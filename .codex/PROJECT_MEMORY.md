# Codex Project Memory

Project: `LeanFpAnalysis`, a Lean 4 library for floating-point arithmetic and
automatic stability analysis. The model is axiomatic and intentionally not tied
to IEEE 754. All core results should be stated over `FPModel` and `Real`.

Last review by Codex: 2026-05-28.
Current RandNLA work is on branch `RandNLA_Kimon`.  Current `main` is for the
stable core library, and benchmark work lives on branch `benchmark`.  The main
commit before the
end-to-end stability rebuild is tagged as
`main-stable-before-end-to-end-20260527` at
`d5c0fa90c69c36f794f176c96f2dd4d293bb5aa3`.

## Current Chapter 13 Work

- On 2026-06-19, split-3 Chapter 13 formalization was started from
  `References/1.9780898718027.ch13.pdf`.
- The governing skill is `.codex/skills/higham-chapter-formalization/SKILL.md`.
- Source inventory: `docs/chapter13/CHAPTER13_SOURCE_INVENTORY.md`.
- Working report: `docs/chapter13/CHAPTER13_FORMALIZATION_REPORT.md`.
- Primary Lean module: `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.
- 2026-07-05 sync/checkpoint: local `main` fast-forwarded to `origin/main`
  commit `183253e3`; direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` passed with no
  output after the sync.  For Theorem 13.6, the exact cited [326] paper has
  been identified as J. W. Demmel, N. J. Higham, and R. S. Schreiber,
  "Stability of block LU factorization", *Numerical Linear Algebra with
  Applications* 2 (1995), pp. 173--190, doi:10.1002/nla.1680020208.  The later
  Lindquist--Luszczek--Dongarra arXiv:2509.07305 paper gives an advisory
  Section 2.2 route split into factorization, triangular-solve, and combined
  solve backward-error theorems.  This supports the existing
  `DemmelHighamSchreiber13_6Estimates` target design but does not close the
  theorem; the [326]-level implementation estimates remain open.
- 2026-07-05 matrix-`∞` source-norm positive-dimension paired endpoints:
  extended the source-norm upper/history positive-block-size cleanup with
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table_of_pos_dim`,
  `..._of_continuousLinearMap_source_table_of_pivot_right_inverse_of_pos_dim`,
  `..._of_initial_diag_right_inverse_of_pivot_right_inverse_of_pos_dim`,
  `..._of_reciprocal_diag_right_inverse_of_pivot_right_inverse_of_pos_dim`,
  `..._of_nonsingInv_diag_of_pivot_right_inverse_of_pos_dim`, and the earlier
  canonical active-pivot
  `..._of_nonsingInv_diag_of_pivotInv_eq_nonsingInv_of_pos_dim` in
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These package the raw,
  pivot-right-inverse, initial-diagonal, reciprocal, canonical-initial, and
  canonical active-pivot source-norm upper/history pairs from the source-shaped
  assumptions plus `0 < r`, discharging the artificial finite unit-sphere
  witness.  Direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` passed before
  lookup refresh; import-materializing
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU` passed (`2982/2982`,
  252s), and ignored scratch
  `scratch/chapter13/ScratchCh13PosDimAxioms.lean` confirmed all six
  positive-dimension paired endpoints and reported only standard Lean/Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`.  A redirected full
  `examples/LibraryLookup.lean` rerun printed all six new Ch13 declarations
  successfully, but the file as a whole now fails at unrelated non-Ch13
  `#check`s around lines 15311--15342; the new Ch13 checks are covered by the
  focused scratch check.
  This remains a matrix-`∞` dependency endpoint; it does not close the
  source-strength entrywise Eq.13.21, Eq.13.23 `rho <= 2`, Problem 13.4
  all-tail comparison, or Theorem 13.6 cited-estimate rows.
- 2026-07-05 post-merge verification for the same endpoint: local milestone
  commit `0b483444` was merged with incoming `origin/main` commit `de29bd7c`
  by merge commit `f101dfba`.  At that merge tip,
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `git diff --check`,
  and the touched Lean placeholder scan passed; ignored scratch
  `scratch/chapter13/ScratchCh13PosDimAxioms.lean` again printed the theorem
  and only standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
  A redirected `examples/LibraryLookup.lean` run printed the new Ch13
  declaration but still exited nonzero on unrelated non-Ch13 lookup rows
  beginning around line 13063 and later Split-3B placeholder/foundation rows
  around 15306--15337.
- 2026-07-04 plain inverse-comparison canonical active-pivot wrappers: added
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivotInv_eq_nonsingInv`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivotInv_eq_nonsingInv`,
  their determinant-nonzero companions, and the Eq.13.23 product-update/
  dimension-aware companions in `BlockLU.lean`.  These derive the active pivot
  right-inverse table from active pivot determinant nonzero plus
  `pivotInv k = nonsingInv r pivot_k`, removing a proof-artifact premise from
  the plain inverse-comparison route.  This is dependency cleanup only: the
  Schur-tail inverse comparison, source-strength Eq.13.23 BDD `rho <= 2` data,
  all-tail source comparisons, and Theorem 13.6 cited estimates remain open.
- 2026-07-04 BDD generic source-norm CLM paired endpoints: added
  `higham13_algorithm13_3_upperFromNormedStages_and_normedStageHistoryBound_le_two_of_column_bdd_diag_lower`,
  `higham13_algorithm13_3_clm_upperFromNormedStages_and_normedStageHistoryBound_le_two_of_continuousLinearMap_source_table`,
  and
  `higham13_algorithm13_3_clm_upperFromNormedStages_and_normedStageHistoryBound_le_two_of_initial_diag_inverse_of_pivot_inverse`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These package the
  one-sided diagonal-lower certificate into the paired source-norm upper-factor
  and finite Schur-stage history endpoint, then instantiate it for actual CLM
  Algorithm 13.3 stages and for diagonal-inverse/active-pivot inverse data.
  This is source-norm Theorem 13.8/Eq.13.21 dependency progress only: it does
  not close the scalar entrywise `rho <= 2` route, the concrete BDD
  source-table construction, Problem 13.4 all-tail comparisons, or Theorem 13.6
  implementation estimates.
- 2026-07-02 Problem 13.4 raw canonical-parent determinant product packaging:
  added
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_canonical_parent_inverse_entry_of_det_ne_zero`
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_canonical_parent_inverse_entry_of_det_ne_zero`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These compose the raw
  Eq.13.22/Eq.13.23 active-suffix product witnesses with the canonical parent
  inverse-entry handoff and derive the ambient canonical `nonsingInv`
  right-inverse from `det(blockMatrixFirstSplitFlat A) != 0`.  This removes the
  caller-supplied `hRight` proof artifact at the raw canonical-parent product
  surface while keeping the genuine active-suffix invertibility/source
  obligations and, for Eq.13.23, the source `rho <= 2` theorem explicit.  The
  all-tail parent/source comparisons, source-strength BDD table construction,
  dimension-free max-entry product estimate, and Theorem 13.6 cited
  implementation estimates remain open.
- 2026-07-01 BDD generic source-norm upper endpoint: added
  `higham13_blockNormSup` and basic supremum lemmas, the normed-block assembled
  upper factor `higham13_algorithm13_3_upperFromNormedStages`, and
  `higham13_algorithm13_3_upperFromNormedStages_blockNormSup_bound_of_column_bdd_diag_lower`
  plus the reciprocal source-table corollary.  The new endpoint proves the
  source-norm upper-factor bound
  `higham13_blockNormSup U <= 2 * higham13_blockNormSup A` for any
  `SeminormedRing` block algebra from column BDD, a one-sided/reciprocal
  diagonal certificate, and the Eq.13.18 active diagonal-update predicate.
  Direct `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` passed
  before documentation wiring.  This is dependency progress only: the
  source-strength entrywise max-growth route, concrete BDD source-table
  construction, Problem 13.4 source comparisons, and Theorem 13.6 cited
  implementation estimates remain open.
- 2026-07-01 BDD generic source-norm finite-history endpoint: added
  `higham13_algorithm13_3_normedStageHistoryBound` and containment/nonnegativity
  helpers, the active-stage-to-history bound
  `higham13_algorithm13_3_normedStageHistoryBound_le_of_active_bound`, the
  one-sided and reciprocal source-table endpoints
  `higham13_algorithm13_3_normedStageHistoryBound_le_two_of_column_bdd_diag_lower`
  and
  `higham13_algorithm13_3_normedStageHistoryBound_le_two_of_column_bdd_source_table_reciprocal`,
  and the paired theorem
  `higham13_algorithm13_3_upperFromNormedStages_and_normedStageHistoryBound_le_two_of_column_bdd_source_table_reciprocal`.
  These prove the finite source-norm history bound over stages `0, ..., m` in
  any `SeminormedRing` block algebra and pair it with the assembled
  source-norm upper-factor Eq.13.21 bound.  This is clean Theorem 13.8
  source-norm dependency progress only: scalar entrywise `growthFactorEntry <= 2`,
  the concrete BDD source-table/nonsingularity construction, Problem 13.4 source
  comparisons, and Theorem 13.6 cited implementation estimates remain open.
- 2026-07-01 Problem 13.4 canonical all-tail global-tableau source-chain
  constructor: added `higham13_algorithm13_3_activeSuffixTail`,
  `higham13_algorithm13_3_activeSuffixStageTailBlock`, the stage-zero/stage-one
  bridges `higham13_algorithm13_3_activeSuffixStageTailBlock_zero_eq` and
  `higham13_algorithm13_3_activeSuffixStageTailBlock_one_eq_blockSchur`, and
  `Higham13Eq1322GlobalTableauSourceChain.activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa`.
  The new theorem builds the fixed-ambient global-tableau source chain for any
  canonical Algorithm 13.3 active suffix from per-stage source obligations
  (current-tail full invertibility and inverse-entry comparison, nonterminal
  first-split/Schur invertibility, pivot identity, dimension budget, and global
  tableau containment).  It uses the derived-tail handoff internally, so callers
  no longer need to pass a prebuilt recursive `hTail` at every suffix level.
	  A follow-up theorem,
	  `Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa`,
	  identifies the canonical stage-one suffix with `blockSchur A (pivotInv 0)`,
	  giving first-split Eq.13.22/Eq.13.23 wrappers a direct replacement for a raw
	  recursive tail-chain premise once the first Schur-tail inverse-entry
	  comparison is supplied.  The Eq.13.22 product witness
	  `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa`
	  and Eq.13.23 product witness
	  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa`
	  now consume that first-Schur-tail active-suffix certificate directly,
	  replacing the old raw `hTail` premise by source-shaped active-suffix
	  obligations.  This closes the general all-tail packaging dependency and
	  wires the raw first-split Eq.13.22/Eq.13.23 product-witness layer; follow-up
	  work should continue the source-strength BDD/product-update and Theorem 13.6
	  rows.
- 2026-07-01 Problem 13.4 active-suffix dimension-budget cleanup: added
  `higham13_activeSuffix_dimension_budget_of_global_bound`,
  `Higham13Eq1322GlobalTableauSourceChain.activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound`,
  and
  `Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound`.
  These derive the per-tail `(m+1)*r <= n` budget table for canonical
  active-suffix source chains from one ambient bound `M*r <= n` (or the
  first-split specialization `((m+1)+1)*r <= n`).  This removes a bookkeeping
  proof artifact from the all-tail route; the active pivot/Schur invertibility
  data, inverse-entry/source comparisons, source-strength BDD product-update
  data, and Theorem 13.6 estimates remain open.
- 2026-07-01 Problem 13.4 active-suffix determinant-table cleanup: added
  `Higham13Eq1322GlobalTableauSourceChain.activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound_of_det_tables`
  and
  `Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound_of_det_tables`.
  These derive the current-tail, pivot-block, and Schur-complement
  invertibility instances for the canonical active-suffix global-tableau chain
  from determinant-nonzero tables plus the existing global dimension bound.
  This removes another proof-artifact layer from the Problem 13.4 route; the
  all-tail inverse-entry/source comparisons, source-strength BDD
  product-update data, and Theorem 13.6 estimates remain open.
- 2026-07-01 Problem 13.4 active-suffix determinant-table product witnesses:
  added
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_det_tables`
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_det_tables`.
  These feed the determinant-table first-Schur-tail active-suffix constructor
  directly into the Eq.13.22/Eq.13.23 first-split product-witness APIs.  They
  remove caller-supplied active-suffix invertibility instances from the product
  surface while still keeping the source inverse-entry comparison table, ambient
  right-inverse certificate, and Eq.13.23 `rho <= 2` theorem explicit.
- 2026-07-01 Problem 13.4 active-suffix determinant-table product-update
  witnesses: added
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_tables`
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_tables`.
  These combine the source product-bound/diagonal-update `rho <= 2` route with
  the determinant-table active-suffix Eq.13.23 product wrapper.  The active
  suffix invertibility instances are now internal at this product-update
  surface too; the source product/update data, inverse-entry comparison table,
  and ambient right-inverse certificate remain explicit obligations.
- 2026-07-01 Problem 13.4 first-split active-suffix Eq.13.23 product-update
  wrappers: added
  `higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update`,
  `higham13_algorithm13_3_firstSplitStageHistoryGrowthFactor_le_two_of_product_bound_diag_update_reciprocal`,
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update`,
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal`.
  These transport the source product-bound/diagonal-update `rho <= 2` theorem to
  the first-split flat representation and then feed it into the active-suffix
  Eq.13.23 product witness, so the source-strength first-split Eq.13.23 route no
  longer needs raw `hTail` or raw `rho <= 2` premises once the active-suffix
  source chain and BDD tables are supplied.  The source-compatible structured
  product estimate, source table data, and Theorem 13.6 estimates remain open.
- 2026-07-01 Problem 13.4 global-tableau Eq.13.23 product-update
  source-chain method: added
  `Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update`
  and
  `Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update_reciprocal`,
  plus determinant variants
  `Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_of_det_ne_zero`
  and
  `Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero`.
  It is the fixed-ambient source-chain-level wrapper for the full flat
  Algorithm 13.3 matrix: from any completed
  `Higham13Eq1322GlobalTableauSourceChain`, an ambient right inverse or
  `det(blockMatrixFlatFin A) != 0`, and the product-bound/diagonal-update BDD
  data, it derives `rho <= 2` internally and returns the Eq.13.23
  `BlockLUFactSpec` product witness; the reciprocal variants accept the
  Theorem 13.7-style reciprocal pivot table, and the determinant variants
  derive the canonical ambient `nonsingInv` right-inverse.  This removes the
  raw growth-factor and ambient-right-inverse plumbing at the global-tableau
  source-chain boundary, but it does not construct the all-tail source chain or
  prove the inverse-entry/source comparison.
- 2026-07-01 Problem 13.4 global-tableau source-chain pivot tables: added
  `Higham13Eq1322GlobalTableauSourceChain.nonterminal_pivot_right_inverse`,
  `Higham13Eq1322GlobalTableauSourceChain.nonterminal_pivot_det_ne_zero`,
  `Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final`,
  `Higham13Eq1322GlobalTableauSourceChain.pivot_det_ne_zero_of_final`,
  `Higham13Eq1322GlobalTableauSourceChain.pivot_det_ne_zero_of_final_right_inverse`,
  `Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final_nonsingInv`,
  and
  `Higham13Eq1322GlobalTableauSourceChain.pivot_det_ne_zero_of_final_nonsingInv`.
  These expose the pivot identity stored at each nonterminal step of the
  fixed-ambient global-tableau source certificate and add the terminal-pivot
  wrappers needed to satisfy all-pivot right-inverse/determinant APIs.  This
  removes an all-pivot proof-artifact table from the global-tableau route, but
  the all-tail source comparison/nonsingularity data, source-strength BDD
  product/update data, and Theorem 13.6 cited estimates remain open.
- 2026-07-01 Problem 13.4 global-tableau determinant variants: added
  `Higham13Eq1322GlobalTableauSourceChain.to_blockLUBudgetChain_of_det_ne_zero`,
  `Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa_of_det_ne_zero`,
  and
  `Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_det_ne_zero`.
  These specialize the generic fixed-ambient global-tableau source-chain
  surfaces to the canonical ambient inverse `nonsingInv N Aglob` under
  `det Aglob != 0`, deriving the ambient right-inverse certificate internally.
  This removes the raw ambient right-inverse proof artifact from the reusable
  source-chain boundary; Eq.13.23 still keeps the source-side `rho <= 2` theorem
  explicit, and the all-tail source comparisons, source-strength BDD data, and
  Theorem 13.6 estimates remain open.
- 2026-07-01 Problem 13.4 derived active-tail Eq.13.23 product-update
  wrappers: added
  `higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_product_bound_diag_update`,
  `higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_product_bound_diag_update_reciprocal`,
  `higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_product_bound_diag_update_of_det_ne_zero`,
  and
  `higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero`.
  These specialize the generic derived-tail active Eq.13.23 witness to the
  full flat Algorithm 13.3 source matrix, derive `rho <= 2` from the existing
  BDD product-bound/diagonal-update route, accept reciprocal-table pivot data,
  and optionally derive the ambient `nonsingInv` right-inverse from
  `det(blockMatrixFlatFin A) != 0`.  The successor-tail source-chain
  constructor and derived tail inverse-entry comparison remain explicit; the
  all-tail source certificate, Schur-complement/source-chain invertibility
  data, source BDD product/update data, and Theorem 13.6 cited estimates remain
  open.
- 2026-07-01 Problem 13.4 three-block active-tail Eq.13.23
  product-update wrappers: added
  `higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update`,
  `higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal`,
  `higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero`,
  and
  `higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero`.
  These specialize the length-three active-tail Eq.13.23 product witness to
  the full flat Algorithm 13.3 source matrix, derive the `rho <= 2` side
  condition from existing BDD product-bound/diagonal-update data, accept the
  source-style active reciprocal table, and optionally derive the ambient
  canonical `nonsingInv` right-inverse from `det(blockMatrixFlatFin A) != 0`.
  This is dependency/plumbing progress only: the all-tail source certificate,
  Schur-complement/source-chain invertibility data, source BDD product/update
  data, and Theorem 13.6 cited estimates remain open.
- 2026-07-01 Problem 13.4 tail invertibility representation bridges:
  added `blockMatrixFirstSplitFlat_invertible_of_blockMatrixFlatFin`,
  `blockMatrixFirstSplit_fromBlocks_invertible_of_blockMatrixFirstSplitFlat`,
  `blockMatrixFirstSplit_fromBlocks_invertible_of_blockMatrixFlatFin`, and
  `higham13_problem13_4_schurTail_fromBlocks_invertible_of_schur_invertible`.
  These transport invertibility from the uniform flat block matrix through the
  first-split scalar flattening and `Matrix.fromBlocks` view, then specialize
  that transport to Schur tails.  The derived active-tail successor and its
  Eq.13.22/Eq.13.23 product wrappers now derive the tail representation
  instance locally instead of requiring it from callers; the finite
  three-block active-tail constructor/product wrappers use the same bridge to
  remove their explicit recursive tail `Matrix.fromBlocks` instance.  The
  all-tail constructor, Schur-complement/source-chain invertibility data,
  Eq.13.23 `rho <= 2`/BDD data, and Theorem 13.6 cited estimates remain open.
- 2026-07-01 Problem 13.4 derived-tail active product witnesses:
  added
  `higham13_eq13_22_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa`
  and
  `higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa`.
  They feed the derived-tail active successor into the fixed-ambient
  Eq.13.22/Eq.13.23 `BlockLUFactSpec` product APIs, so a recursive tail
  builder only has to consume the derived tail inverse-entry certificate under
  the locally derived tail representation instance.  The all-tail constructor,
  Schur-complement/source-chain invertibility data, Eq.13.23 `rho <= 2`/BDD
  data, and Theorem 13.6 cited estimates remain open.
- 2026-07-01 Problem 13.4 derived-tail active successor handoff:
  added
  `Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_active_tail_with_derived_tail_inverse_entry_exact_kappa`.
  It derives the recursive Schur-tail inverse-entry certificate from the
  parent active-tail inverse-entry certificate via
  `higham13_problem13_4_firstSplit_schurTail_inverse_entry_bound_from_block_inverse`,
  then invokes the recorded active-tail successor for any tail builder that
  only needs that derived certificate.  This is reusable all-tail
  infrastructure; the actual all-tail constructor, Schur-complement/source-chain
  invertibility data, Eq.13.23 `rho <= 2`/BDD data, and Theorem 13.6 cited
  estimates remain open.
- 2026-07-01 Problem 13.4 three-block active-tail product witnesses: added
  `higham13_eq13_22_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa`
  and
  `higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa`.
  They route the closed three-block global-tableau active-tail source chain
  through the Eq.13.22/Eq.13.23 `BlockLUFactSpec` product APIs, removing a
  finite recursive-tail product plumbing gap.  The all-tail source certificate,
  Schur-complement/source-chain invertibility data, Eq.13.23 `rho <= 2`/BDD
  data, and Theorem 13.6 cited estimates remain open; after the tail
  representation-bridge cleanup these wrappers no longer require the recursive
  tail `Matrix.fromBlocks` invertibility instance from callers.
- 2026-07-01 Problem 13.4 three-block global-tableau active-tail constructor:
  added
  `Higham13Eq1322GlobalTableauSourceChain.three_from_matrix_stage_history_active_tail_exact_kappa`.
  It composes the active-tail successor with the two-block active-tail
  constructor and uses
  `higham13_problem13_4_firstSplit_schurTail_inverse_entry_bound_from_block_inverse`
  to derive the first recursive tail inverse-entry certificate from the parent
  active-tail inverse-entry certificate, and it now derives the recursive tail
  `Matrix.fromBlocks` invertibility instance locally from the Schur-tail bridge.
  This removes explicit recursive inverse-entry and representation proof
  artifacts for the three-block active-tail case; the all-tail source
  certificate, Schur-complement/source-chain invertibility data, Eq.13.23
  `rho <= 2`/BDD data, and Theorem 13.6 cited estimates remain open.
- 2026-07-01 Problem 13.4 recursive Schur-tail inverse-entry handoff:
  added `invOf_entry_bound_of_reindex_eq` and
  `higham13_problem13_4_firstSplit_schurTail_inverse_entry_bound_from_block_inverse`.
  The generic helper transports entrywise inverse bounds across an equivalence
  reindexing, and the Chapter 13 theorem uses the first-split Schur
  inverse-entry bridge to propagate a parent block inverse-entry certificate to
  the first-split inverse of the Schur tail.  This is direct dependency
  progress on the all-tail ambient inverse-entry/source comparison in
  Problem 13.4; it still assumes the parent inverse-entry certificate and the
  tail first-split invertibility needed to form the next inverse, and does not
  close the full recursive source certificate, Eq.13.23 `rho <= 2`/BDD data,
  or Theorem 13.6 cited estimates.
- 2026-07-01 Problem 13.4 Schur inverse-entry bridge checkpoint: added
  `higham13_problem13_4_Sinv_entry_bound_from_block_inverse` and
  `higham13_problem13_4_Sinv_maxEntryNormRect_from_block_inverse`.  These use
  the Problem 13.8 lower-right block-inverse identity to show that entries, and
  hence the max-entry norm, of the displayed Schur-complement inverse inherit a
  supplied entrywise max bound on the parent block inverse.  This removes a
  lower-right-block identity proof artifact from recursive max-entry
  source-comparison routes.  It does not prove the all-tail ambient
  inverse-entry/source comparison, Eq.13.23 `rho <= 2`/BDD product-update data,
  or Theorem 13.6 cited implementation estimates.  Verification passed with
  direct `BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet public lookup with empty
  stderr and both names present, `git diff --check`, touched Lean placeholder
  scan, anchored conflict-marker scan, and focused `#print axioms` reporting
  only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-01 Problem 13.4 first-split Schur inverse-entry bridge: added
  `higham13_problem13_4_firstSplit_Sinv_entry_bound_from_block_inverse` and
  `higham13_problem13_4_firstSplit_Sinv_maxEntryNormRect_from_block_inverse`.
  These specialize the preceding Problem 13.8 lower-right-block bridge to the
  `blockMatrixFirstSplitA..` objects used by recursive block-LU source routes,
  so downstream wrappers can consume the Schur inverse-entry inheritance in
  source-shaped notation.  This is dependency progress only; the all-tail
  ambient inverse-entry/source comparison and Eq.13.23 source-strength BDD data
  remain open.  Verification passed with direct `BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet public lookup
  with empty stderr and both names present, `git diff --check`, touched Lean
  placeholder scan, anchored conflict-marker scan, and focused `#print axioms`
  reporting only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-01 full-flat two-block active-tail product-update checkpoint:
  added
  `higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update`,
  `higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal`,
  `higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero`,
  and
  `higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero`.
  These specialize the two-block active-tail global-tableau Eq.13.23 witness
  to the actual flat Algorithm 13.3 source matrix, so the product-bound/
  diagonal-update BDD route supplies `rho <= 2` internally.  The reciprocal
  variants accept the source-style active reciprocal table; the determinant
  variants derive the canonical ambient `nonsingInv` right-inverse from
  `det(blockMatrixFlatFin A) != 0`.  This removes one proof-artifact surface
  but still leaves the current two-block inverse-entry comparison, all-tail
  source-table/product-update data, and Theorem 13.6 estimates open.
- 2026-07-01 first-split global-tableau product-update checkpoint:
  added
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_product_bound_diag_update`
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal`.
  These remove the raw first-split Eq.13.23 `rho <= 2` hypothesis from the
  fixed-ambient global-tableau product-witness surface by transporting the
  uniform-flat matrix-stage BDD product/update theorem across the
  first-split/uniform representation bridge.  The reciprocal wrapper accepts
  the Theorem 13.7 source reciprocal table instead of the scalar pivot-product
  bound.  This is dependency progress only: all-tail ambient inverse-entry
  comparison, global all-tail source-table BDD data, and Theorem 13.6 cited
  implementation estimates remain open.
- 2026-07-01 first-split global-tableau product-update determinant checkpoint:
  added
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero`
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero`.
  These combine the preceding first-split product-update and reciprocal
  wrappers with
  `higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero`,
  so callers can supply `det(blockMatrixFirstSplitFlat Ablk) != 0` instead of
  an explicit canonical ambient right-inverse certificate.  This is still
  dependency progress only and leaves the all-tail ambient inverse-entry
  comparison, global all-tail source-table BDD data, and Theorem 13.6 cited
  implementation estimates open.
- 2026-07-01 two-block active-tail product-witness checkpoint:
  added
  `higham13_eq13_22_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa`
  and
  `higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa`.
  These route the closed two-block active-tail global-tableau chain through the
  concrete Eq.13.22/Eq.13.23 `BlockLUFactSpec` product-witness APIs.  They
  still leave the ambient inverse-entry/source comparison explicit, and the
  Eq.13.23 wrapper still requires the source `rho <= 2` theorem.
- 2026-07-01 two-block active-tail global-tableau checkpoint:
  added
  `Higham13Eq1322GlobalTableauSourceChain.two_from_matrix_stage_history_active_tail_exact_kappa`.
  This composes the active-tail successor constructor with the terminal
  one-block matrix-stage constructor, so a recorded active tail of length two
  now builds a complete fixed-ambient global-tableau source chain without a
  separate terminal `hTail` hypothesis.  The theorem still leaves the ambient
  inverse-entry/source comparison explicit; all-tail inverse-entry comparison,
  Eq.13.23 `rho <= 2`/BDD product-update data, and Theorem 13.6 estimates
  remain open.  Verification passed with direct `lake env lean -s 65536
  LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup with empty stderr and
  the new theorem present, `git diff --check`, Lean-only placeholder/conflict
  scans, and focused `#print axioms` reporting only standard Mathlib axioms.
- 2026-06-30 active-tail global-tableau successor checkpoint:
  added
  `Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_active_tail_exact_kappa`.
  This is the all-tail successor constructor for the fixed-ambient Problem
  13.4 global-tableau source chain: a recorded active stage-`k` tail gets its
  first-row upper budget and Schur-tableau containment from the global
  matrix-stage history, while
  `higham13_algorithm13_3_schurStageMatrixTailBlock_succ_active_eq_blockSchur`
  identifies the local `blockSchur` tail with the recorded stage-`k+1`
  successor tail.  It leaves the ambient inverse-entry/source comparison
  explicit, because that remains the genuine open source obligation.
  Verification passed with focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, executable lookup with empty stderr
  and the new name present, `git diff --check`, touched Lean placeholder scan,
  conflict-marker scan, and focused `#print axioms` reporting only `propext`,
  `Classical.choice`, and `Quot.sound`; temporary scratch files were removed.
- 2026-06-30 active recorded-tail Schur bridge checkpoint:
  added
  `higham13_algorithm13_3_schurStageMatrixTailBlock_succ_active_eq_blockSchur`.
  This proves the all-tail Algorithm 13.3 algebra bridge: if a recorded
  stage-`k` active tail starts with the active pivot index and `tailSucc` is
  the successor tail, then the local first Schur complement of the recorded
  stage-`k` tail is exactly the recorded stage-`k+1` tail.  This should feed
  the recursive Problem 13.4 global-tableau source certificate by aligning
  `blockSchur` tails with recorded matrix-stage-history tails.  It does not
  prove the all-tail inverse subblock/source comparison, Eq.13.23 `rho <= 2`,
  or Theorem 13.6 cited implementation estimates.  Verification passed with
  focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, executable
  lookup with empty stderr and the new name present, `git diff --check`,
  touched Lean placeholder scan, conflict-marker scan, and focused
  `#print axioms` reporting only `propext`, `Classical.choice`, and
  `Quot.sound`; temporary scratch files were removed.
- 2026-06-30 fixed-ambient global-tableau terminal-tail checkpoint:
  added
  `Higham13Eq1322GlobalTableauSourceChain.one_of_blockMaxNorm_le_global_tableau`
  and
  `Higham13Eq1322GlobalTableauSourceChain.one_from_matrix_stage_history_tail_exact_kappa`.
  These expose the one-block base case of the Problem 13.4 global-tableau
  source chain: ambient tableau containment gives the exact Eq.13.22 upper
  budget, and any one-block Schur tail recorded by the Algorithm 13.3
  matrix-stage history supplies that containment.  This is dependency progress
  only.  Recursive all-tail tableau/source-inverse data, Eq.13.23 `rho <= 2`/
  BDD product-update data, and Theorem 13.6 cited implementation estimates
  remain open.  Verification passed with direct `BlockLU.lean` compile,
  focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, executable
  lookup with empty stderr and both new names present, `git diff --check`,
  touched Lean placeholder scan, conflict-marker scan, and focused
  `#print axioms` reporting only `propext`, `Classical.choice`, and
  `Quot.sound`; the temporary scratch audit file was removed.
- 2026-06-30 fixed-ambient global-tableau first-split determinant wrappers:
  added
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero`
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero`.
  These specialize the first-split global-tableau Eq.13.22/Eq.13.23 concrete
  product witnesses to the canonical ambient `nonsingInv` inverse by deriving
  the required right-inverse certificate from determinant nonsingularity.  They
  do not prove the recursive all-tail source certificate, Eq.13.23 `rho <= 2`,
  or Theorem 13.6 implementation estimates.  Verification passed with direct
  `BlockLU.lean` compile, focused LU build, executable lookup, `git diff
  --check`, touched Lean placeholder scan, conflict-marker scan, and focused
  `#print axioms` reporting only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-06-30 fixed-ambient global-tableau first-split constructor checkpoint:
  added
  `Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_first_split_exact_kappa`,
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa`,
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_tail_chain_matrix_stage_history_exact_kappa`.
  These instantiate the first successor of the fixed-ambient Problem 13.4
  global-tableau certificate from the concrete Algorithm 13.3 matrix-stage
  history, discharging the first-split tableau containment, Schur-tail
  containment, canonical `nonsingInv` inverse-entry comparison, and first-row
  upper-budget obligations before routing to the Eq.13.22/Eq.13.23 concrete
  product-witness APIs.  This is dependency progress only: recursive all-tail
  tableau/source-inverse data, Eq.13.23 `rho <= 2`/BDD product-update data, and
  Theorem 13.6 cited implementation estimates remain open.  Verification
  passed with direct `lake env lean -s 65536
  LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, executable
  `examples/LibraryLookup.lean`, `git diff --check`, touched Lean placeholder
  scan, anchored conflict-marker scan, and focused `#print axioms` reporting
  only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-06-30 fixed-ambient global-tableau source-chain checkpoint:
  added `Higham13Eq1322GlobalTableauSourceChain` plus
  `to_blockLUBudgetChain`, `to_blockLUBudgetChain_of_right_inverse`, and the
  Eq.13.22/Eq.13.23 concrete product witness wrappers
  `exists_blockLUFact_eq13_22_product_exact_kappa_of_right_inverse` and
  `exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse`.  This
  packages the Oracle-advised Problem 13.4 route as a recursive fixed-ambient
  certificate using one global GE-tableau growth factor and exact ambient
  `kappa` denominator; each successor stores the ambient initial/Schur
  containment, ambient inverse-entry certificate, first-row upper budget,
  pivot identity, and recursive tail certificate.  It is dependency progress
  only: all-tail tableau/source-inverse data, Eq.13.23 `rho <= 2`/BDD
  product-update data, and Theorem 13.6 cited implementation estimates remain
  open.  Verification passed by direct `BlockLU.lean` compile, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, executable
  `examples/LibraryLookup.lean`, `git diff --check`, placeholder and anchored
  conflict-marker scans, and focused `#print axioms` reporting only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-06-30 Eq.13.23 reciprocal source-chain product/update checkpoint:
  added
  `higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update_reciprocal`,
  `Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal`,
  `Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal`,
  and
  `Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal`.
  These wrappers accept the source reciprocal active-pivot table
  `SchurStageActivePivotInvReciprocal13_7` and internally derive the raw
  pivot-product bound used by the existing product-bound/diagonal-update
  Eq.13.23 routes.  This removes a source-surface mismatch only; structured
  product/update data, recursive Problem 13.4 comparisons, and Theorem 13.6
  cited estimates remain open.  Verification passed by direct `BlockLU.lean`
  compile, focused LU build, quiet `examples/LibraryLookup.lean` with empty
  stderr and all four new names present, `git diff --check`, placeholder and
  conflict-marker scans, and focused `#print axioms` reporting only `propext`,
  `Classical.choice`, and `Quot.sound`.  Committed as
  `2b76f93 Split 3A: add Ch13 reciprocal product-update wrappers`, merged
  incoming shared-main work through `e49a0ac`, reran the relevant merged-tree
  builds/lookups/scans, pushed to `origin/main`, and confirmed ahead/behind
  `0 0`.
- 2026-06-30 base/inverse route-audit checkpoint:
  `higham13_base_inverse_principal_tail_base_comparison_counterexample` shows
  that the stronger base comparison `||A_full||_max <= ||A_tail||_max` needed
  by the optional base/inverse recursive tail-transport route is not automatic
  even for a concrete full/right-inverse principal-tail witness.  The proof
  reuses `higham13_inverse_ratio_principal_tail_counterexample`: if the base
  comparison held together with the already-present inverse comparison, then
  `maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le` would contradict
  the rejected inverse-ratio comparison.  This is route-rejection evidence for
  Problem 13.4/Eq.13.22--13.23 only; the per-tail direct lower-budget
  comparison, Eq.13.23 `rho <= 2`, and Theorem 13.6 cited estimates remain
  open.  Verification: direct `lake env lean -s 65536
  LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, refreshed `lake build
  LeanFpAnalysis.FP.Algorithms.HighamChapter9`, quiet
  `examples/LibraryLookup.lean` with empty stderr and the new Ch13 name in
  stdout, `git diff --check`, and focused `#print axioms`; the axiom output was
  only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-06-30 recursive Schur-tail base/inverse bridge checkpoint:
  `maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le` and
  `growthFactorEntry_sq_kappa_budget_le_of_growth_le_base_inverse` derive the
  optional inverse-ratio/lower-budget scalar transport from the stronger
  explicit pair `||A_full||_max <= ||A_tail||_max` and
  `||A_tail^{-1}||_max <= ||A_full^{-1}||_max`.
  `higham13_eq13_22_tail_lower_budget_le_full_from_base_inverse_matrix_stage_history_exact_kappa`
  and
  `higham13_eq13_22_tail_chain_to_full_budget_from_base_inverse_matrix_stage_history_exact_kappa`
  feed that pair into the recursive Schur-tail Eq.13.22 transport.  This is
  dependency progress only: the strong base comparison and inverse comparison
  remain explicit source obligations, and the direct Problem 13.4
  lower-budget/condition comparison plus Eq.13.23 `rho <= 2` source theorem
  remain open.  Verification used direct `BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, public `examples/LibraryLookup.lean`
  with empty quiet stderr, `git diff --check`, marker/conflict scans, and
  focused `#print axioms`; the axiom output was only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-06-29 matrix-`∞` finite-unit-sphere cleanup:
  `higham13_fin_fun_unit_sphere_nonempty` constructs the nonempty unit sphere
  in `Fin r -> ℝ` from `0 < r`.  New `_of_pos_dim` wrappers for the
  reciprocal diagonal right-inverse and canonical `nonsingInv` matrix-`∞`
  packages remove the caller-supplied `hunit` proof artifact while preserving
  the existing constants and conclusions.  This is hidden-hypothesis cleanup
  only; the BDD source table, active pivot determinant/equality table,
  structured dimension-free max-entry product/update proof, Problem 13.4
  comparisons, and Theorem 13.6 cited estimates remain open.
- 2026-06-29 source-lower-block canonical active-pivot checkpoint:
  the Eq.13.22/Eq.13.23 source local lower-block witness route now has
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivotInv_eq_nonsingInv`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivotInv_eq_nonsingInv`,
  their determinant/canonical-full-inverse variants, and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero_of_product_bound_diag_update`.
  These derive the pivot right-inverse certificate from active pivot determinant
  nonzero plus `pivotInv = nonsingInv`, removing another proof-artifact premise
  from the Problem 13.4 source-shaped Eq.13.22/Eq.13.23 route.  The local
  lower-block estimates, scalar comparison table, active BDD product/update
  data, and Theorem 13.6 cited implementation estimates remain open.
- 2026-06-29 base-comparison canonical active-pivot checkpoint:
  added
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_of_pivotInv_eq_nonsingInv`.
  These route the stage-local-growth base-comparison witness layer through
  active pivot determinant nonzero plus `pivotInv = nonsingInv`, removing
  explicit active pivot right-inverse certificates from that Problem 13.4
  proof surface.  Verification used direct `BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet `examples/LibraryLookup.lean`
  with empty stderr, `git diff --check`, touched-file marker scan, and
  focused `#print axioms`; the axiom output was only `propext`,
  `Classical.choice`, and `Quot.sound`.  The base comparison, condition
  comparison table, active BDD product/update data, and Theorem 13.6 cited
  implementation estimates remain open.
- 2026-06-29 base-comparison determinant/full-inverse checkpoint:
  added
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero_of_product_bound_diag_update`.
  These specialize the base-comparison witness route to the source-facing full
  inverse `nonsingInv (m*r) (blockMatrixFlatFin Ablk)` and derive the full
  positive denominator/right-inverse certificate from
  `det(blockMatrixFlatFin Ablk) ≠ 0`, while keeping the base comparison,
  condition comparison, active BDD product/update data, and Theorem 13.6 cited
  implementation estimates open.  Verification used direct `BlockLU.lean`,
  focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet
  `examples/LibraryLookup.lean` with empty stderr, `git diff --check`, touched
  Lean marker scan, and focused `#print axioms`; the axiom output was only
  `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-06-29 plain inverse-comparison budget checkpoint:
  added `higham13_stage_local_source_lblock_budget_le_of_growth_plain_inverse_bound`,
  `higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_plain_inverse_bound_exact_kappa`,
  `higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa`,
  and `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa`.
  These refine the direct inverse route by replacing the previous source
  obligation `||A_local^{-1}||_max <= rhoFull * ||A^{-1}||_max` with the
  sharper Schur-tail inverse comparison
  `||A_local^{-1}||_max <= ||A^{-1}||_max`; the extra `rhoFull` factor is
  derived from `rhoFull >= 1` because the matrix-stage history contains the
  input.  Product-level determinant companions
  `higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_det_ne_zero`
  and
  `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_det_ne_zero`
  specialize the raw Eq.13.22/Eq.13.23 surfaces to
  `nonsingInv (m*r) (blockMatrixFlatFin Ablk)` and derive the full positive
  denominator/right-inverse certificate from `det(blockMatrixFlatFin Ablk) != 0`.
  The matching concrete factor witnesses
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse`,
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`
  package this sharper route as `BlockLUFactSpec` witnesses and specialize the
  determinant variants to the source-facing full inverse `nonsingInv (m*r)
  (blockMatrixFlatFin Ablk)`.  The Eq.13.23 companions
  `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update`,
  `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse`
  compose the same plain-inverse route with the active BDD product/update
  `rho <= 2` layer and with the dimension-aware diagonal-update layer.  The
  determinant/canonical-inverse companions
  `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_det_ne_zero`,
  `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_det_ne_zero`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse_of_det_ne_zero`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_plain_inverse_bound_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse_of_det_ne_zero`
  specialize those diagonal-update surfaces to
  `nonsingInv (m*r) (blockMatrixFlatFin Ablk)` and derive the full positive
  denominator/right-inverse certificate from `det(blockMatrixFlatFin Ablk) != 0`.
  The
  Schur-tail inverse comparison itself, source-strength active BDD product/update
  data, active pivot determinant/equality table, and Theorem 13.6 cited
  implementation estimates remain open.  Verified by focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet public lookup with empty
  stderr, `git diff --check`, marker/conflict-marker scans, and focused
  `#print axioms` reporting only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-06-29 Algorithm 13.3 max-entry product-bound audit:
  added `higham13_algorithm13_3_product_bound_not_generic`, proving that the
  source-conditional `hProduct` surface used by
  `higham13_algorithm13_3_matrix_active_local_schur_bound_of_product_bound`
  is false as a generic Algorithm 13.3 stage-table theorem.  The all-ones
  `2 x 2` block table at the initial active stage would force the max-entry
  triple-product estimate `4 <= 1`.  This rules out the ordinary
  dimension-free max-entry multiplication shortcut for the Eq.13.21/Eq.13.23
  branch; it is route-rejection evidence only and leaves the structured
  source product/update theorem, source BDD reciprocal data, Problem 13.4
  comparisons, and Theorem 13.6 cited estimates open.
- 2026-06-29 matrix-`∞` source-norm upper endpoint checkpoint:
  `blockInfNorm` is the blockwise maximum of matrix-`∞` operator norms, with
  helpers `block_le_blockInfNorm`, `blockInfNorm_nonneg`,
  `blockInfNorm_le_of_block_le`, `infNorm_zeroBlock`, and
  `infNorm_le_zero_of_eq_zeroBlock`.  The new Algorithm 13.3 wrappers
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_active_stage_bound`,
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_continuousLinearMap_source_table`,
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_continuousLinearMap_source_table_of_pivot_right_inverse`,
  and
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockInfNorm_bound_of_initial_diag_right_inverse_of_pivot_right_inverse`
  prove `blockInfNorm (upperFromMatrixStages ...) <= 2 * blockInfNorm A`.
  This closes the source-norm upper-factor packaging gap without introducing
  the old max-entry comparison loss; the entrywise max-norm Eq.13.21 endpoint
  and `growthFactorEntry <= 2` remain open.  Verification before commit:
  direct `BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet `examples/LibraryLookup.lean`
  with empty stderr, `git diff --check`, marker scan, and focused
  `#print axioms` all passed; axiom output was only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-06-29 matrix-`∞` source-norm to max-entry upper bridge:
  `blockMaxNorm_le_blockInfNorm` and the
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_by_blockInfNorm_*`
  wrappers prove
  `blockMaxNorm (upperFromMatrixStages ...) <= 2 * blockInfNorm A` from the
  same active/source-table/pivot-right-inverse/initial-diagonal data.  This
  gives the existing entrywise upper-factor API without the old input-side
  `r * blockMaxNorm A` comparison loss when the source norm is the blockwise
  matrix-`∞` maximum; the entrywise-input Eq.13.21 and finite-history
  `growthFactorEntry <= 2` rows remain open.  Verification before commit:
  direct `BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet `examples/LibraryLookup.lean`
  with empty stderr, `git diff --check`, marker scan, and focused
  `#print axioms` all passed with only standard Mathlib axioms.
- 2026-06-29 matrix-`∞` source-norm finite-history bridge:
  `higham13_algorithm13_3_matrixStageHistoryInfBound` records the finite
  matrix-product stage history using the blockwise matrix-`∞` maximum.  The
  containment lemmas
  `higham13_algorithm13_3_matrixStageHistoryInfBound_contains_stage`,
  `higham13_algorithm13_3_matrixStageHistoryInfBound_contains_initial`, and
  `higham13_algorithm13_3_matrixStageHistoryInfBound_contains_upperFromMatrixStages`
  parallel the existing max-entry history object.  The active-stage induction
  layer
  `higham13_algorithm13_3_matrixStageBlock_infNorm_bound_of_active_bound`,
  `higham13_algorithm13_3_matrixStage_blockInfNorm_bound_of_active_bound`,
  `higham13_algorithm13_3_matrixStageHistoryInfBound_le_of_stage_bound`,
  `higham13_algorithm13_3_matrixStageHistoryInfBound_le_of_active_bound`, and
  `higham13_algorithm13_3_matrixStageHistoryInfBound_le_two_of_active_stage_bound`
  proves inactive carry-forward stages are also controlled.  Source-table,
  pivot-right-inverse, and initial-diagonal/right-inverse wrappers prove
  `matrixStageHistoryInfBound <= 2 * blockInfNorm A`; the companion
  `higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthMatrix_bound_by_blockInfNorm_*`
  wrappers prove the existing max-entry growth matrix is bounded by
  `2 * blockInfNorm A`.  This is source-norm finite-history progress, not yet
  the chapter's entrywise-denominator `growthFactorEntry <= 2`.
- 2026-06-29 Problem 13.4 stage-local inverse-bound scalar bridge:
  `higham13_stage_local_source_lblock_budget_le_of_growth_inverse_bound`
  exposes the scalar step used by the direct inverse-bound route.  From the
  already-proved local growth numerator budget
  `rhoLocal * ||A_local|| <= rhoFull * ||A||` and the remaining source inverse
  comparison `||A_local^{-1}|| <= rhoFull * ||A^{-1}||`, it proves the full
  `rhoFull^2 * kappaFull` budget.  The matrix-stage theorem
  `higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_inverse_bound_exact_kappa`
  now uses this bridge directly.  This is proof-chain/dependency cleanup; the
  source inverse estimate and Eq.13.23 `rho <= 2` branch remain open.
- 2026-06-29 matrix-`∞` source-table max-entry composition checkpoint:
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_blockMaxNorm_bound_with_card_of_continuousLinearMap_source_table`,
  `higham13_algorithm13_3_matrix_infNorm_matrixStageHistoryGrowthFactor_le_card_of_continuousLinearMap_source_table`,
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table`,
  and the corresponding `_of_pivot_right_inverse` variants now compose the
  matrix-`∞` continuous-linear source-table route directly into the max-entry
  upper-factor and finite-history growth APIs.  The endpoint remains
  dimension-aware (`2*r*blockMaxNorm(A)` and `growthFactorEntry <= 2*r`), so
  the source-strength Eq.13.21/`rho <= 2` branch remains open.  The
  `_of_det_ne_zero` paired variants, including the initial-diagonal/right-inverse
  specialization, derive the positive growth-factor denominator from
  `det(blockMatrixFlatFin A) != 0` while keeping the same dimension-aware
  endpoint.
- 2026-06-30 matrix-`∞` raw source-table positive-dimension cleanup:
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_growthFactor_le_card_of_continuousLinearMap_source_table_of_pos_dim`,
  its determinant-denominator variant, and the two pivot-right-inverse variants
  remove the explicit finite unit-sphere witness from the raw source-table
  max-entry packages by using `higham13_fin_fun_unit_sphere_nonempty hr`.
  This is hidden-hypothesis cleanup for the BDD route; the endpoint remains
  dimension-aware (`growthFactorEntry <= 2*r`), so the printed Eq.13.21 /
  Eq.13.23 `rho <= 2` source-strength row remains open.
- 2026-06-29 matrix-`∞` max-entry transfer checkpoint:
  `higham13_algorithm13_3_matrix_infNorm_block_le_card_mul_blockMaxNorm`,
  `higham13_algorithm13_3_matrix_infNorm_active_stage_maxEntry_bound`, and the
  `higham13_algorithm13_3_matrix_infNorm_*upperFromMatrixStages*` /
  `*matrixStageHistoryGrowth*` wrappers now route matrix-`∞` active-stage
  bounds into the Chapter 13 max-entry upper-factor and finite-history growth
  APIs. The resulting endpoint is dimension-aware
  `upperFromMatrixStages <= 2*r*blockMaxNorm(A)` and
  `growthFactorEntry <= 2*r`; the source-strength Eq.13.21/`rho <= 2`
  branch remains open.
- Existing `BlockLU.lean` was already Chapter-13-shaped but mislabeled as
  Chapter 12. Its labels were corrected to Higham Chapter 13, and it now exposes
  source-facing first-order bound vocabulary for equations (13.4)--(13.6) and
  (13.14)--(13.15), gamma forms and the row/transpose bridge for equation
  (13.17), block-count recurrences for Theorem 13.5, exact Matrix adapters for
  equations (13.1)--(13.3), the Algorithm 13.1 Schur-complement prose form,
  the §13.1 block-LU-to-standard-LU product bridge
  `higham13_block_lu_to_standard_lu_product`, exact output-check theorems for
  Algorithms 13.1/13.3/13.4, exact partition-display wrappers
  `higham13_eq13_20_partition` and `higham13_eq13_26_partition`, scalar
  consequences for equations (13.22) and (13.25), the Eq.13.19 norm-comparison
  package `BlockNormComparison13_19`, the Eq.13.18 one-step Schur-column
  proof-chain declarations `higham13_eq13_18_min_lower_bound`,
  `higham13_eq13_18_scalar_column_chain`, and
  `higham13_eq13_18_schur_column_dominance`, the row one-step inheritance theorem
  `block_diag_dom_schur_inherit_row`, the Theorem 13.8 one-step `2 * max`
  block-bound corollary `higham13_theorem13_8_one_step_block_bound`, the
  Theorem 13.8 active-stage induction layer
  `SchurStageActiveColumnStep13_8` /
  `higham13_theorem13_8_active_column_bound_of_steps` /
  `higham13_theorem13_8_active_stage_block_bound` /
  `higham13_theorem13_8_active_stage_block_bound_of_steps`, the staged Theorem
  13.8 column-invariant wrapper `SchurStageColumnBound13_8` /
  `higham13_theorem13_8_stage_block_bound`, the SPD-section symmetric partition
  wrapper `higham13_spd_symmetric_partition_isSymm`, the SPD Schur
  positive-definiteness dependencies `higham13_spd_leadingBlock_posDef` /
  `higham13_spd_schurComplement_posDef` /
  `higham13_spd_schurComplement_posDef_of_full` /
  `higham13_spd_schurComplement_source_posDef`, the
  flat-SPD block-LU existence route `blockMatrixFlat` /
  `leadingBlockPrefix13_2_posDef_flat_of_posDef_flat` /
  `LeadingPrincipalBlockNonsingular13_2.of_posDef_flat` /
  `BlockLUFactSpec.existsUnique_of_posDef_flat`, the row block diagonal
  dominance large-`L` scalar-block family
  `higham13_rowdom_largeL_arbitrarily_large`, the Problem 13.1 block-tridiagonal
  local norm-bound theorems `higham13_problem13_1_column_step_bounds` and
  `higham13_problem13_1_row_step_bounds`, the exact scalar-block Problem 13.2
  incomparability witnesses `higham13_problem13_2_incomparability`, the
  exact scalar-block Problem 13.3 counterexample
  `higham13_problem13_3_counterexample`, the Problem 13.5 point-column
  inverse-action theorem `higham13_problem13_5_oneNormRect_bound`, and exact
  Matrix/Schur-complement adapters for Problems 13.7--13.9.
- Theorem 13.7 leading-prefix dominance inheritance is now closed as a genuine
  dependency: `leadingBlockPrefixIndex13_7`, `leadingBlockPrefixNorm13_7`,
  `leadingBlockPrefixInvDiagBound13_7`,
  `isBlockDiagDomCol_leadingBlockPrefix13_7`, and
  `isBlockDiagDomRow_leadingBlockPrefix13_7` prove that row/column block
  diagonal dominance restricts to every leading block prefix under nonnegative
  block norms.  This supports the eventual Theorem 13.2 nonsingularity route
  but does not close full Theorem 13.7; the concrete one-sided active
  diagonal-lower certificate or equivalent pivot product bound, diagonal-update
  equality facts, and the BDD-to-nonsingularity theorem remain open.
- Theorem 13.5 has scalar recurrence infrastructure:
  `partitioned_lu_backward_error_step` proves the one-step max aggregation from
  per-block source inequalities, while `higham13_theorem13_5_recurrence_step`
  instantiates that aggregation with the actual `blockErrorDelta`/`blockErrorTheta`
  recurrences. `higham13_theorem13_5_recurrence_step_firstOrder` lifts the same
  recurrence step to explicit `FirstOrderLe`/`+ O(u^2)` witnesses.
  `blockErrorTheta_le_cubic_of_quadratic_constants`,
  `higham13_theta_isBigO_cubic_of_quadratic_constants`, and
  `higham13_theta_conventional_isBigO_cubic` close the p.250 recurrence-only
  conventional `θ(n,r)=O(n^3)` consequence using Mathlib `IsBigO` with the
  shifted cubic `(n+1)^3`. This still does not close the full computed-matrix
  theorem or instantiate the individual matrix proof-step equations
  (13.8)--(13.13).
- Theorem 13.5 model specs now include exact matrix residual fields:
  `MatMulFirstOrderSpec` for (13.4), `TriangularSolveFirstOrderSpec` for the
  left-solve form of (13.5), `RightTriangularSolveFirstOrderSpec` for the
  right/transpose solve orientation used in (13.9), `LocalLUFirstOrderSpec` for
  (13.6), `SubtractionFirstOrderSpec` for (13.10), and
  `PartitionedLUFirstOrderSpec` for the recursive induction hypothesis
  (13.12a)--(13.12b). Source-facing wrappers
  `higham13_eq13_4_from_matmul_spec`, `higham13_eq13_5_from_triangular_solve_spec`,
  `higham13_eq13_6_from_local_lu_spec`, `higham13_eq13_8_from_triangular_solve_spec`,
  `higham13_eq13_9_from_right_triangular_solve_spec`, and
  `higham13_eq13_10_from_subtraction_spec`, and
  `higham13_eq13_12_from_induction_spec` unpack the exact residual equations and
  first-order bounds. They are model/spec wrappers, not concrete BLAS proofs.
- The p.248 conventional constants row is now closed at the concrete kernel
  scope in `BlockLU.lean`. `higham13_conventional_matmul_spec_c1_maxEntry`
  uses `fl_matMul`, the existing componentwise `gamma fp n` error bound, the
  rectangular entrywise norm `maxEntryNormRect`, and
  `gamma_eq_linear_plus_quadratic_remainder` to prove the source constant
  `c1(m,n,p) = n^2` for Eq.13.4. For Eq.13.5,
  `higham13_conventional_backSub_spec_c2_maxEntry` and
  `higham13_conventional_forwardSub_spec_c2_maxEntry` instantiate the generic
  bridge `higham13_triangular_solve_c2_maxEntry_from_componentwise_backward`
  with the existing `backSub_backward_error` and `forwardSub_backward_error`
  kernels to prove `c2(m,p) = m^2` for columnwise upper/lower triangular
  substitution in the left-solve residual form `T Xhat = B + DeltaB`.
- The Eq.13.11 trailing Schur proof step now has local infrastructure:
  `higham13_eq13_11a_subtraction_error` proves the exact additive identity from
  the computed product/subtraction equations, and
  `higham13_eq13_11b_trailing_schur_error_firstOrder` proves the scalar
  first-order norm bound with an explicit second-order witness.
  `higham13_eq13_11_from_matmul_subtraction_specs` now combines those two
  pieces directly from the product model (13.4) and subtraction model (13.10),
  retaining the explicit norm aggregation hypotheses for `ΔS` and `Ĉ`.
  `higham13_eq13_13_trailing_block_identity` proves the exact additive trailing
  block identity, and `higham13_eq13_13_trailing_block_error_firstOrder` combines
  the local `ΔS` and expanded recursive `ΔŜ` bounds into the displayed
  trailing-block scalar first-order bound.
  `higham13_eq13_13_from_matmul_subtraction_induction_specs` now combines the
  Eq.13.11 product/subtraction spec bridge with the recursive induction spec to
  produce the exact trailing-block residual and scalar first-order bound under
  the still-explicit norm aggregation and expanded induction-bound hypotheses.
  These are still proof-step lemmas, not a closure of the full Theorem 13.5
  computed-matrix path.
- `higham13_theorem13_5_block_residual_identity` proves the exact assembled
  block residual identity `Lhat * Uhat = A + DeltaA` from the four block residual
  equations (13.6), (13.8), (13.9), and (13.13). It is exact algebra; the global
  norm bound and recursive computed-factor theorem remain separate obligations.
  `higham13_theorem13_5_block_residual_identity_from_specs` instantiates the
  first three residual equations directly from `LocalLUFirstOrderSpec`,
  `TriangularSolveFirstOrderSpec`, and `RightTriangularSolveFirstOrderSpec`.
- `higham13_theorem13_5_residual_and_recurrence_from_specs` packages the two
  currently formalized Theorem 13.5 proof-step halves: it proves both the exact
  assembled block residual identity and the scalar `FirstOrderLe` recurrence
  conclusion from global-norm-majorant local specs plus an explicit
  trailing-block first-order premise. It remains an integration proof step, not
  the full computed partitioned-LU theorem.
- `higham13_theorem13_5_partitioned_step_spec_from_specs` repackages the same
  proof as the next `PartitionedLUFirstOrderSpec` over the assembled
  `Matrix.fromBlocks` factors. It is the spec-shaped induction step and still
  leaves the actual computed factor sequence/global norm instantiation open.
- Theorem 13.6 model specs now include exact residual fields for the two source
  assumptions: `BlockSolveFirstOrderSpec` for (13.14) and
  `DiagonalBlockSolveFirstOrderSpec` for (13.15). Wrappers
  `higham13_eq13_14_from_block_solve_spec` and
  `higham13_eq13_15_from_diagonal_block_solve_spec` unpack the residual equations
  and first-order bounds. They are model/spec wrappers; the cited
  Demmel--Higham--Schreiber theorem remains open.
- Algorithm 13.3 implementation paths now have local source-facing specs:
  `Algorithm13_3Implementation1LocalSpec` packages the Implementation 1 path
  through Eq.13.14 and Eq.13.15, with
  `higham13_algorithm13_3_implementation1_eq13_14_15_from_spec` unpacking both
  source equations. `Algorithm13_3Implementation2ExplicitInverseSpec` and
  `higham13_algorithm13_3_implementation2_explicit_inverse_equations` record
  the explicit-inverse multiplication path. The p.251 scalar condition-number
  multiplier consequence is
  `higham13_algorithm13_3_implementation2_eq13_16_firstOrder_multiplier`: from
  supplied factorization/solve `FirstOrderLe` bounds whose first-order terms
  are already multiplied by a common `kappaMax` corresponding to
  `max_i kappa(Uhat_ii)`, it derives the combined (13.16) bound with that same
  multiplier. It does not prove the concrete exact-inverse local conditioned
  bounds from an inverse computation.
- `block_lu_solve_backward_error_firstOrder` is the explicit `FirstOrderLe`
  version of the existing Theorem 13.6 scalar max-bound adapter. It aggregates
  supplied factorization and solve first-order bounds, but it is not the omitted
  implementation-facing Theorem 13.6 proof.
- Problem 13.6 has an exact single-right-hand-side perturbation construction:
  `higham13_problem13_6_residualRankOneDelta` defines the rank-one matrix
  that maps a nonzero component of `xhat` to a supplied solve residual,
  `higham13_problem13_6_residualRankOneDelta_mulVec` proves that action, and
  `higham13_problem13_6_single_rhs_backward_error_identity` /
  `higham13_problem13_6_single_rhs_backward_error_exists` assemble
  `(A + DeltaA) *ᵥ xhat = b` from `Lhat * Uhat = A + DeltaFact` and
  `(Lhat * Uhat) *ᵥ xhat = b + rsolve`, under the necessary condition that
  `xhat` has a nonzero component. The Frobenius-norm route reuses
  `residualRankOnePerturbation`: `higham13_problem13_6_residualRankOnePerturbation_frobNorm`,
  `higham13_problem13_6_single_rhs_backward_error_frobenius_identity`,
  `higham13_problem13_6_residualRankOnePerturbation_frobNorm_firstOrder`, and
  `higham13_problem13_6_single_rhs_backward_error_frobenius_firstOrder` prove
  the exact single-RHS backward equation and first-order Frobenius aggregation
  from supplied factorization and triangular-solve residual budgets.
  `higham13_problem13_6_residualRankOnePerturbation_opNorm2Le` and
  `higham13_problem13_6_residualRankOnePerturbation_opNorm2Le_firstOrder` give
  the corresponding operator 2-norm certificate and first-order operator-bound
  bridge for the same residual correction. The fully implementation-facing
  triangular-solve residual proof remains open.
- Validation note for the Problem 13.6 single-RHS operator-norm bridge: focused
  Lean, focused `BlockLU` build, and lookup with `lake env lean -s 65536
  examples/LibraryLookup.lean` passed after adding
  `higham13_problem13_6_residualRankOnePerturbation_opNorm2Le` and
  `higham13_problem13_6_residualRankOnePerturbation_opNorm2Le_firstOrder`.
  The first axiom-audit attempt raced the rebuild and failed on a temporarily
  missing `BlockLU.olean`; rerunning after the build passed. `#print axioms`
  for both declarations reports only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`; `/tmp/Ch13Problem136OpNormAxioms.lean`
  was removed, `git diff --check` passed, and the placeholder scan over
  `BlockLU.lean`/`LibraryLookup.lean` returned no matches.
- Problem 13.6 has a multiple-right-hand-side residual proof step:
  `higham13_problem13_6_multiple_rhs_residual_identity` proves
  `A * Xhat - B = Rsolve - DeltaA * Xhat` from `Lhat * Uhat = A + DeltaA`
  and `(Lhat * Uhat) * Xhat = B + Rsolve`, and
  `higham13_problem13_6_multiple_rhs_residual_firstOrder` derives the displayed
  scalar `FirstOrderLe` residual bound from factorization and multiple-RHS
  triangular-solve residual budgets.
- The block-LU-to-standard-LU bridge proves the exact product identity after
  factoring each diagonal block of the block upper factor. It intentionally does
  not close Theorem 13.2 or prove the lower/upper triangular shape of the refined
  factors.
- Theorem 13.2 is now closed for the uniform-block model by
  `BlockLUFactSpec.existsUnique_iff_leadingPrincipalBlockNonsingular13_2`.
  The forward direction is
  `BlockLUFactSpec.existsUnique_of_leadingPrincipalBlockNonsingular13_2`.
  The converse uses `first_block_inverse_of_isUnit_det` to turn determinant
  nonsingularity into explicit inverse data,
  `BlockLUFactSpec.first_block_inverse_of_existsUnique` to prove first-pivot
  nonsingularity from exists-unique block LU by a left-kernel shear
  contradiction, `BlockLUFactSpec.schurTail_existsUnique_of_existsUnique_of_first_block_inverse`
  to pass uniqueness to the Schur tail, and
  `LeadingPrincipalBlockNonsingular13_2.of_existsUnique` for the induction.
  Supporting source adapters include `LeadingPrincipalBlockNonsingular13_2`,
  `leadingBlockPrefix13_2`, `BlockMatrixNonsingular`,
  `BlockMatrixTwoSidedInverse`,
  `LeadingPrincipalBlockNonsingular13_2.first_block_inverse`,
  `leadingBlockPrefix13_2_blockSchur`,
  `blockSchur_nonsingular_of_nonsingular_of_first_block_inverse`,
  `blockMatrixNonsingular_of_first_block_inverse_of_blockSchur_nonsingular`,
  `LeadingPrincipalBlockNonsingular13_2.schur`,
  `BlockLUFactSpec.existsUnique_one`, `blockLUOneStepL`, `blockLUOneStepU`,
  `block_lu_one_step_explicit`, `block_lu_one_step`,
  `BlockLUFactSpec.firstRow_eq`,
  `BlockLUFactSpec.firstColumnBelow_eq_of_right_inverse`,
  `BlockLUFactSpec.of_leadingBlockPrefix13_2`,
  `BlockLUFactSpec.schurTailFactSpec_of_right_inverse`,
  `BlockLUFactSpec.eq_of_schurTail_unique_of_right_inverse`, and
  `BlockLUFactSpec.existsUnique_step_of_schurTail_existsUnique`.
- The Chapter 13 norm convention row is closed at the current block API level by
  `higham13_norm_convention_blockMaxNorm_eq_entrywise_sup`,
  `block_entry_abs_le_blockMaxNorm`, `blockMaxNorm_le_of_entry_abs_le`, and
  `higham13_block_norm_eq_maxEntryNorm`. These prove the exact
  block-index/within-block entrywise max-norm convention and identify the
  ambient Pi norm on each `Fin r -> Fin r -> R` block with the same max-entry
  norm used by the concrete Algorithm 13.3 stage tables; no quotient-based flat
  `Fin (m*r)` API has been introduced.
- The Eq.13.20/Eq.13.26 wrappers close only the source partition displays via
  `Matrix.fromBlocks`; the Problem 13.4 norm and condition-number inequalities
  remain open.
- The Eq.13.19 declarations record the source norm-comparison assumption
  `max_ij ||Aij|| <= ||A|| <= sum_ij ||Aij||`; they do not claim that an
  arbitrary chosen norm satisfies it.
- The Eq.13.18 declarations close the source one-step column proof chain under
  explicit subordinate-norm/min hypotheses: `higham13_eq13_18_scalar_column_chain`
  proves the displayed scalar inequalities from (13.17),
  `higham13_eq13_18_min_lower_bound` proves the reverse-triangle min step, and
  `higham13_eq13_18_schur_column_dominance` combines them. They do not close
  the row case, Schur-stage induction, nonsingularity argument, or full
  Theorem 13.7.
- `block_diag_dom_schur_inherit_row` proves the row-wise one-step analogue of
  `block_diag_dom_schur_inherit` by applying the column theorem to transposed
  block-norm and Schur-norm tables. The active-stage induction layer is now
  represented by `SchurStageActiveColumnDom13_7`,
  `SchurStageActiveColumnDomStep13_7`,
  `higham13_theorem13_7_active_column_dominance_of_steps`,
  `SchurStageActiveRowDom13_7`, `SchurStageActiveRowDomStep13_7`, and
  `higham13_theorem13_7_active_row_dominance_of_steps`: from initial
  row/column BDD and a one-step active inheritance rule, all active stages
  inherit the same dominance form. The actual instantiation of the one-step
  active premises from Algorithm 13.3's Schur-complement relation and the
  nonsingularity/block-LU existence part remain open.
- The Theorem 13.8 declaration
  `higham13_theorem13_8_one_step_block_bound` proves the one-step Schur
  complement `2 * max` block bound from the existing one-step column-sum theorem
  and diagonal-dominance column-sum lemma. The active-stage induction layer
  `activeBlockIndices13_8`, `SchurStageActiveColumnStep13_8`,
  `SchurStageActiveColumnBound13_8`,
  `higham13_theorem13_8_active_column_bound_of_steps`, and
  `higham13_theorem13_8_active_stage_block_bound` proves the source-shaped
  induction from one-step active-column inequalities to the active block
  `2 * max` bound for `k <= i,j`; the wrapper
  `higham13_theorem13_8_active_stage_block_bound_of_steps` combines those two
  steps directly from `hInit` and `hStep`. The active-column-only layer
  `SchurStageActiveColumnStepOnActive13_8`,
  `SchurStageActiveColumnBoundOnActive13_8`,
  `higham13_theorem13_8_active_column_bound_on_active_of_steps`,
  `higham13_theorem13_8_active_stage_block_bound_on_active`,
  `higham13_theorem13_8_active_stage_block_bound_on_active_of_steps`,
  `SchurStageActiveLocalSchurBound13_8`,
  `higham13_theorem13_8_active_tail_pivot_sum_le_of_column_dominance`,
  `higham13_theorem13_8_active_column_step_on_active_of_local_schur_bound`, and
  `higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound` proves
  the source-relevant active-column step from local Schur norm estimates plus
  active column dominance, so the direct `hStep` obligation is no longer needed
  for active columns. The exact-update layer
  `SchurStageActiveExactUpdate13_8`,
  `SchurStageActivePivotInvReciprocal13_7`,
  `SchurStageActivePivotInvReciprocal13_7.of_mul_eq_one`,
  `SchurStageActiveDiagLowerUpdate13_7`,
  `SchurStageActiveDiagLowerUpdate13_7.of_eq`,
  `higham13_theorem13_7_pivot_inverse_bound_of_reciprocal`,
  `higham13_theorem13_8_active_local_schur_bound_of_exact_update`,
  `higham13_theorem13_7_active_column_dom_step_of_exact_update`,
  `higham13_theorem13_7_active_column_dom_step_of_exact_update_reciprocal`,
  `higham13_theorem13_7_active_column_dominance_of_exact_update`,
  `higham13_theorem13_7_active_column_dominance_of_exact_update_reciprocal`,
  `higham13_theorem13_8_active_stage_block_bound_of_exact_update`, and
  `higham13_theorem13_8_active_stage_block_bound_of_exact_update_reciprocal`
  derives the local Schur norm estimate and active column-dominance induction
  from the exact Schur update relation plus the named diagonal Schur
  lower-bound update predicate; `SchurStageActiveDiagLowerUpdate13_7.of_eq`
  converts an exact diagonal-certificate equality into that inequality. The
  concrete active Algorithm 13.3 stage sequence is now supplied by
  `higham13_algorithm13_3_schurStageBlock`, whose exact update relation is
  `higham13_algorithm13_3_schurStageBlock_exact_update`; the associated norm
  tables `higham13_algorithm13_3_schurStageNorm` and
  `higham13_algorithm13_3_pivotInvNorm` instantiate the local Schur estimate in
  `higham13_algorithm13_3_schurStage_local_schur_bound`.
  `higham13_algorithm13_3_active_column_dom_step_of_reciprocal`,
  `higham13_algorithm13_3_active_column_dominance_of_reciprocal`,
  `higham13_algorithm13_3_active_stage_block_bound_of_reciprocal`, and
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_reciprocal_zero_lower`
  thread that concrete stage sequence through the Theorem 13.7 dominance,
  Theorem 13.8 active growth, and Eq.13.21 zero-lower max-norm bridges while
  keeping diagonal update, reciprocal pivot data, upper-`U` stage equality, and
  growth-factor premises visible. The source-shaped adapters
  `higham13_algorithm13_3_pivot_reciprocal_of_mul_eq_one`,
  `higham13_algorithm13_3_active_diag_lower_update_of_eq`,
  `higham13_algorithm13_3_active_column_dom_step_of_pivot_mul_diag_eq`,
  `higham13_algorithm13_3_active_column_dominance_of_pivot_mul_diag_eq`,
  `higham13_algorithm13_3_active_stage_block_bound_of_pivot_mul_diag_eq`, and
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq`
  turn those remaining predicate obligations into concrete pivot-product and
  diagonal-update equality facts. The upper-`U`/stage bridge
  `higham13_algorithm13_3_upper_block_bound_of_eq_stage` derives the named
  `SchurStageUpperBlockBound13_21` predicate from exact upper-block stage
  equality, using `higham13_block_norm_eq_maxEntryNorm` to align the ambient Pi
  norm with the chapter max-entry norm, and
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_upper_eq`
  threads that bridge into the concrete Eq.13.21 source-shaped wrapper. The
  source-assembled upper factor is now represented by
  `higham13_algorithm13_3_upperFromStages`: its proofs
  `higham13_algorithm13_3_upperFromStages_eq_stage`,
  `higham13_algorithm13_3_upperFromStages_lower_zero`, and
  `higham13_algorithm13_3_upperFromStages_upper_block_bound` close the exact
  upper-stage equality, strict-lower zero shape, and upper-stage norm predicate
  for this concrete `U`; the wrapper
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq`
  specializes Eq.13.21 to that assembled upper factor. The concrete diagonal
  lower-bound certificate `higham13_algorithm13_3_diagLowerCert`, with
  `higham13_algorithm13_3_diagLowerCert_zero`,
  `higham13_algorithm13_3_diagLowerCert_eq`, and
  `higham13_algorithm13_3_diagLowerCert_update`, follows the source recurrence
  and discharges the diagonal-update equality path; the wrapper
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert`
  specializes Eq.13.21 to both the assembled upper factor and this certificate.
  The column-BDD specialization
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd`
  instantiates the input max-norm majorant with `blockMaxNorm hm hr A` and the
  initial block-norm table with `maxEntryNorm hr (A i j)`. The reciprocal
  variant
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_reciprocal`
  is now the preferred source-facing route because it assumes the pivot
  condition as `SchurStageActivePivotInvReciprocal13_7` directly. The
  product-form route remains available:
  `SchurStageActivePivotInvReciprocal13_7.of_mul_eq_one` derives the reciprocal
  certificate from nonzero product-form pivot data, and
  `SchurStageActivePivotInvReciprocal13_7.of_active_mul_eq_one` derives the
  same certificate from the active product identity alone, with nonzero active
  pivot-inverse norms following from that identity. The source-shaped concrete
  wrappers
  `higham13_algorithm13_3_active_column_dom_step_of_pivot_mul_diag_eq_active_mul_eq_one`,
  `higham13_algorithm13_3_active_column_dominance_of_pivot_mul_diag_eq_active_mul_eq_one`,
  `higham13_algorithm13_3_active_stage_block_bound_of_pivot_mul_diag_eq_active_mul_eq_one`,
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_active_mul_eq_one`,
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_upper_eq_active_mul_eq_one`,
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_active_mul_eq_one`
  thread that active-product route through the concrete Theorem 13.7,
  Theorem 13.8, and Eq.13.21 pivot-product/diagonal-equality wrappers without a
  separate nonzero pivot-inverse norm premise. The same active-product fact now
  also feeds the weaker certificate interfaces through
  `SchurStageActivePivotInvDiagLower13_7.of_active_mul_eq_one`,
  `higham13_algorithm13_3_diagLowerCert_diag_lower_of_active_mul_eq_one`, and
  `higham13_algorithm13_3_diagLowerCert_pivot_bound_of_active_mul_eq_one`.
  Conversely, `SchurStageActivePivotInvDiagLower13_7.of_pivot_bound` and
  `higham13_algorithm13_3_diagLowerCert_diag_lower_of_pivot_bound` convert a
  positive direct product bound into the one-sided certificate, so future
  progress on either pivot route can feed the other interface.
  The direct-bound wrappers
  `higham13_algorithm13_3_active_column_dom_step_of_pivot_bound`,
  `higham13_algorithm13_3_active_column_dominance_of_pivot_bound`,
  `higham13_algorithm13_3_active_stage_block_bound_of_pivot_bound`,
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_bound`,
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_bound_upper_eq`,
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_bound`,
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_pivot_bound`,
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_pivot_bound`
  give the weaker source-shaped route from the scalar bound
  `||pivotInv_k|| * gamma_k <= 1`. The one-sided diagonal-lower bridge
  `SchurStageActivePivotInvDiagLower13_7`,
  `higham13_theorem13_7_pivot_inverse_bound_of_diag_lower`,
  `higham13_algorithm13_3_diagLowerCert_pivot_bound_of_diag_lower`,
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_diag_lower`,
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_diag_lower`
  derives that scalar product bound from the source-shaped certificate
  `gamma_k <= ||pivotInv_k||^-1`; `SchurStageActivePivotInvDiagLower13_7.of_reciprocal`
  records that a reciprocal certificate is sufficient for this weaker
  one-sided route. The staged wrapper
  `higham13_theorem13_8_stage_block_bound` proves the final `2 * max` conclusion
  from `SchurStageColumnBound13_8`; for the column-BDD `2*||A||` Eq.13.21
  route, only that concrete one-sided active diagonal-lower certificate, or an
  equivalent active pivot product bound, remains open for
  `higham13_algorithm13_3_diagLowerCert`. The broader general growth-factor/
  Problem 13.4 route remains open separately.
- Validation note for the Algorithm 13.3 Implementation 2 scalar multiplier:
  focused Lean, focused `BlockLU` build, and logged lookup with
  `lake env lean -s 65536 examples/LibraryLookup.lean` passed after adding
  `higham13_algorithm13_3_implementation2_eq13_16_firstOrder_multiplier`.
  The first lookup attempt raced the rebuild and failed because `BlockLU.olean`
  did not yet exist; rerunning after the focused build passed. `#print axioms`
  for the new declaration reports only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`; temporary scratch file
  `ScratchCh13Implementation2MultiplierAxioms.lean` was removed.
- Validation note for the Table 13.1 generic bridge: focused Lean, focused
  `BlockLU` build, and logged lookup with
  `lake env lean -s 65536 examples/LibraryLookup.lean` passed after adding
  `higham13_table13_1_backward_error_from_product_bound`. `#print axioms` for
  the new declaration reports only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`; temporary scratch file
  `ScratchCh13TableAxioms.lean` was removed.
- Validation note for the Table 13.1 row corollaries: focused Lean, focused
  `BlockLU` build, and `lake env lean -s 65536 examples/LibraryLookup.lean`
  passed after adding `higham13_table13_1_col_bdd_backward_error`,
  `higham13_table13_1_point_col_bdd_backward_error`,
  `higham13_table13_1_point_row_backward_error_from_growth`, and
  `higham13_table13_1_spd_backward_error`. `#print axioms` for the four
  declarations reports only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`; `/tmp/Ch13TableRowsAxioms.lean` was
  removed, `git diff --check` passed, and the placeholder scan over `BlockLU`
  plus `LibraryLookup.lean` returned no matches.
- Validation note for the SPD block-LU existence route: focused Lean, focused
  `BlockLU` build, and logged lookup with
  `lake env lean -s 65536 examples/LibraryLookup.lean` passed after adding the
  flat determinant/SPD block-nonsingularity bridges and
  `BlockLUFactSpec.existsUnique_of_posDef_flat`. `#print axioms` for
  `blockMatrixNonsingular_of_flat_inverse`,
  `blockMatrixNonsingular_of_isUnit_det_flat`,
  `blockMatrixNonsingular_of_posDef_flat`,
  `matrix_posDef_submatrix_of_injective`,
  `leadingBlockPrefix13_2_posDef_flat_of_posDef_flat`,
  `LeadingPrincipalBlockNonsingular13_2.of_posDef_flat`, and
  `BlockLUFactSpec.existsUnique_of_posDef_flat` reports only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`; temporary scratch
  file `ScratchCh13SpdExistenceAxioms.lean` was removed.
- Validation note for the SPD Schur positive-definiteness dependency: focused
  Lean, focused `BlockLU` build, and `lake env lean -s 65536
  examples/LibraryLookup.lean` passed after adding
  `higham13_spd_leadingBlock_posDef`, `higham13_spd_schurComplement_posDef`,
  `higham13_spd_schurComplement_posDef_of_full`, and
  `higham13_spd_schurComplement_source_posDef`. The first lookup attempt raced
  an earlier rebuild and failed only because the `BlockLU.olean` file was not
  present yet; rerunning after the build passed. `#print axioms` for the four
  declarations
  reports only standard Mathlib axioms `propext`, `Classical.choice`, and
  `Quot.sound`; temporary scratch files `ScratchCh13SchurPosDef.lean` and
  `ScratchCh13SchurPosDefAxioms.lean`, then `ScratchCh13LeadingSpd.lean` and
  `ScratchCh13LeadingSpdAxioms.lean`, then
  `ScratchCh13SpdSourceDisplay.lean` and
  `ScratchCh13SpdSourceDisplayAxioms.lean`, were removed.
- Validation note for the concrete Algorithm 13.3 active stage sequence:
  focused Lean, focused `BlockLU` build, and `lake env lean -s 65536
  examples/LibraryLookup.lean` passed after adding the stage block table,
  norm tables, exact-update theorem, and local Schur estimate. Axiom audits for
  the new public stage declarations report only standard Mathlib axioms
  (`propext`, `Classical.choice`, `Quot.sound`; exact update only needs
  `propext`), and the temporary `ScratchCh13Stage*` files were removed.
- Validation note for the concrete Algorithm 13.3 active bridge wrappers:
  focused Lean, focused `BlockLU` build, and `lake env lean -s 65536
  examples/LibraryLookup.lean` passed after adding the four
  `higham13_algorithm13_3_*_of_reciprocal`/Eq.13.21 wrappers. `#print axioms`
  for all four reports only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- Validation note for the concrete Algorithm 13.3 source-shaped pivot/diagonal
  certificate wrappers: focused Lean, focused `BlockLU` build, and logged
  lookup with `lake env lean -s 65536 examples/LibraryLookup.lean` passed.
  `#print axioms` for the six new wrappers reports only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`.
- Validation note for the concrete Algorithm 13.3 upper-`U`/stage equality
  bridge: focused Lean, focused `BlockLU` build, and logged lookup with
  `lake env lean -s 65536 examples/LibraryLookup.lean` passed after adding
  `higham13_block_norm_eq_maxEntryNorm`,
  `higham13_algorithm13_3_upper_block_bound_of_eq_stage`, and
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_upper_eq`.
  `#print axioms` for those three declarations reports only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`; temporary scratch
  files from this pass were removed.
- Validation note for the concrete Algorithm 13.3 assembled upper factor:
  focused Lean, focused `BlockLU` build, and logged lookup with
  `lake env lean -s 65536 examples/LibraryLookup.lean` passed after adding
  `higham13_algorithm13_3_upperFromStages`,
  `higham13_algorithm13_3_upperFromStages_eq_stage`,
  `higham13_algorithm13_3_upperFromStages_lower_zero`,
  `higham13_algorithm13_3_upperFromStages_upper_block_bound`, and
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq`.
  `#print axioms` for the four public proof declarations reports only standard
  Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`; temporary
  scratch file `ScratchCh13UpperFromStagesAxioms.lean` was removed.
- Validation note for the concrete Algorithm 13.3 diagonal certificate:
  focused Lean, focused `BlockLU` build, and logged lookup with
  `lake env lean -s 65536 examples/LibraryLookup.lean` passed after adding
  `higham13_algorithm13_3_diagLowerCert`,
  `higham13_algorithm13_3_diagLowerCert_zero`,
  `higham13_algorithm13_3_diagLowerCert_eq`,
  `higham13_algorithm13_3_diagLowerCert_update`, and
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert`.
  `#print axioms` for the four public proof declarations reports only standard
  Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`; temporary
  scratch file `ScratchCh13DiagCertAxioms.lean` was removed.
- Validation note for the concrete Algorithm 13.3 column-BDD max-norm
  specialization: focused Lean, focused `BlockLU` build, and logged lookup with
  `lake env lean -s 65536 examples/LibraryLookup.lean` passed after adding
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd`.
  `#print axioms` for that declaration reports only standard Mathlib axioms
  `propext`, `Classical.choice`, and `Quot.sound`; temporary scratch file
  `ScratchCh13ColumnBddAxioms.lean` was removed.
- Validation note for the concrete Algorithm 13.3 column-BDD reciprocal
  specialization: focused Lean, focused `BlockLU` build, and logged lookup with
  `lake env lean -s 65536 examples/LibraryLookup.lean` passed after adding
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_reciprocal`.
  `#print axioms` for that declaration reports only standard Mathlib axioms
  `propext`, `Classical.choice`, and `Quot.sound`; temporary scratch file
  `ScratchCh13ColumnBddRecipAxioms.lean` was removed.
- Validation note for the concrete Algorithm 13.3 active-product pivot route:
  focused Lean, focused `BlockLU` build, and lookup with
  `lake env lean -s 65536 examples/LibraryLookup.lean` passed after adding
  `SchurStageActivePivotInvReciprocal13_7.of_active_mul_eq_one`,
  `higham13_algorithm13_3_pivot_reciprocal_of_active_mul_eq_one`,
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_active_mul_eq_one`,
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_active_mul_eq_one`.
  `#print axioms` for those four declarations reports only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`; temporary scratch
  file `ScratchCh13ActiveMulPivotAxioms.lean` was removed, `git diff --check`
  passed, and the placeholder scan over `BlockLU.lean`/`LibraryLookup.lean`
  returned no matches.
- Validation note for the active-product no-separate-nonzero wrappers: focused
  Lean, focused `BlockLU` build, and lookup with
  `lake env lean -s 65536 examples/LibraryLookup.lean` passed after adding
  `higham13_algorithm13_3_active_column_dom_step_of_pivot_mul_diag_eq_active_mul_eq_one`,
  `higham13_algorithm13_3_active_column_dominance_of_pivot_mul_diag_eq_active_mul_eq_one`,
  `higham13_algorithm13_3_active_stage_block_bound_of_pivot_mul_diag_eq_active_mul_eq_one`,
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_active_mul_eq_one`,
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_upper_eq_active_mul_eq_one`,
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_active_mul_eq_one`.
  `#print axioms` for those six declarations reports only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`; temporary file
  `/tmp/Ch13ActiveProductWrapperAxioms.lean` was removed, `git diff --check`
  passed, and the placeholder scan over `BlockLU.lean`/`LibraryLookup.lean`
  returned no matches.
- Validation note for the direct pivot-bound wrappers: focused `BlockLU` build
  and lookup with `lake env lean -s 65536 examples/LibraryLookup.lean` passed
  from the current tree after adding
  `higham13_algorithm13_3_active_column_dom_step_of_pivot_bound`,
  `higham13_algorithm13_3_active_column_dominance_of_pivot_bound`,
  `higham13_algorithm13_3_active_stage_block_bound_of_pivot_bound`,
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_bound`,
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_bound_upper_eq`,
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_pivot_bound`,
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_pivot_bound`,
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_pivot_bound`.
  `#print axioms` for those eight declarations reports only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`; temporary file
  `/tmp/Ch13PivotBoundAxioms.lean` was removed, `git diff --check` passed, and
  the placeholder scan over `BlockLU.lean`/`LibraryLookup.lean` returned no
  matches.
- Validation note for the one-sided diagonal-lower route: focused Lean,
  focused `BlockLU` build, and lookup with
  `lake env lean -s 65536 examples/LibraryLookup.lean` passed after adding
  `SchurStageActivePivotInvDiagLower13_7`,
  `higham13_theorem13_7_pivot_inverse_bound_of_diag_lower`,
  `higham13_algorithm13_3_diagLowerCert_pivot_bound_of_diag_lower`,
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_diagLowerCert_diag_lower`,
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_diag_lower`.
  `#print axioms` for the four theorem declarations reports only standard
  Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`; temporary file
  `/tmp/Ch13DiagLowerAxioms.lean` was removed, `git diff --check` passed, and
  the placeholder scan over `BlockLU.lean`/`LibraryLookup.lean` returned no
  matches.
- Current continuation note for the concrete `diagLowerCert` active route:
  `higham13_algorithm13_3_active_column_dominance_of_diagLowerCert_pivot_bound`,
  `higham13_algorithm13_3_active_column_dominance_of_diagLowerCert_diag_lower`,
  `higham13_algorithm13_3_active_stage_block_bound_of_diagLowerCert_pivot_bound`,
  `higham13_algorithm13_3_active_stage_block_bound_of_diagLowerCert_diag_lower`,
  `higham13_algorithm13_3_active_column_dominance_of_column_bdd_diag_lower`,
  and
  `higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_diag_lower`
  discharge the concrete initial-certificate and diagonal-update recurrence
  plumbing and feed the direct or one-sided pivot certificate into Algorithm
  13.3 active dominance and Theorem 13.8 active-stage growth. They do not prove
  the still-open concrete one-sided pivot certificate/product fact.
  Validation for this route: `lake env lean
  LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, and `lake env lean -s 65536
  examples/LibraryLookup.lean` passed. `#print axioms` for the six route
  declarations reports only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`; `/tmp/Ch13DiagLowerActiveRouteAxioms.lean`
  was removed, `git diff --check` passed, and the placeholder scan over
  `MatrixAlgebra.lean`, `BlockLU.lean`, and `LibraryLookup.lean` returned no
  matches.
- The p.253--254 column block diagonal-dominance stability consequences are
  represented by exact scalar product theorems:
  `higham13_col_bdd_stability_bound` proves `||L||||U|| <= m^3 ||A||` from
  `||L|| <= m` and `||U|| <= m^2 ||A||`,
  `higham13_col_bdd_oneNorm_stability_bound` proves the `2m ||A||_1`
  refinement from the corresponding source-derived one-norm premises, and
  `higham13_col_bdd_infNorm_stability_bound` proves the `2m^2 ||A||_inf`
  refinement. These close only the scalar consequences; deriving the premises
  from the full Theorem 13.7/13.8 Schur-stage machinery remains open.
- Eq.13.23 now has the exact scalar bridge
  `higham13_eq13_23_point_row_from_growth`: from the Eq.13.22 source premises
  `||L|| <= n rho_n^2 kappa(A)`, `||U|| <= rho_n ||A||`, nonnegative
  `||A||`, and `rho_n <= 2`, it proves
  `||L||||U|| <= 8 n kappa(A) ||A||`. It does not close the Problem 13.4 or
  Eq.13.21 premises needed to derive those inequalities from point row
  dominance.
- Table 13.1 has the generic scalar bridge
  `higham13_table13_1_backward_error_from_product_bound`: from a Theorem 13.6
  style first-order backward-error premise
  `FirstOrderLe u (c_n*u*(||A|| + ||L||||U||)) err` and a product bound
  `||L||||U|| <= tableValue*||A||`, it derives the exact visible leading term
  `FirstOrderLe u (c_n*u*((1+tableValue)*||A||)) err`. The row corollaries
  `higham13_table13_1_col_bdd_backward_error`,
  `higham13_table13_1_point_col_bdd_backward_error`,
  `higham13_table13_1_point_row_backward_error_from_growth`, and
  `higham13_table13_1_spd_backward_error` instantiate this for column
  block-BDD, point column-BDD, point row-BDD via Eq.13.23, and SPD/Eq.13.24
  from their displayed product premises. Full class-specific premise derivation
  and the implementation-facing Theorem 13.6 path remain separate obligations.
- Eq.13.21 has the finite max-norm theorem
  `higham13_eq13_21_blockMaxNorm_bound`: if every block of `U` satisfies
  `maxEntryNorm U_ij <= rho_n ||A||`, then the chapter's `blockMaxNorm` of
  `U` satisfies `||U|| <= rho_n ||A||`. The upper-`U`/Schur-stage premise is
  now named by `SchurStageUpperBlockBound13_21`, and
  `SchurStageUpperBlockBound13_21.of_eq_stageBlock` derives it when each upper
  block `U_ij` is exactly the corresponding Schur-stage block and `stageNorm`
  is the chapter entrywise max norm. The bridge
  `higham13_eq13_21_blockMaxNorm_bound_of_active_stage` derives the `rho_n = 2`
  column-BDD max-norm conclusion from the active Theorem 13.8 wrapper, assuming
  `SchurStageUpperBlockBound13_21` and strict lower blocks are zero at the norm
  level. The bridge
  `higham13_eq13_21_blockMaxNorm_bound_of_local_schur_bound` uses the new local
  Schur/active-dominance route instead of a direct active-step premise.
  `higham13_eq13_21_blockMaxNorm_bound_of_exact_update` goes one level closer
  to the source by deriving those local/dominance inputs from exact Schur update
  plus named diagonal-update/pivot premises, and
  `higham13_eq13_21_blockMaxNorm_bound_of_exact_update_reciprocal` derives the
  pivot product premise from the reciprocal pivot certificate.
  `higham13_eq13_21_blockMaxNorm_bound_of_exact_update_reciprocal_zero_lower`
  additionally discharges the strict lower-`U` norm premise from actual
  `zeroBlock` equalities using `maxEntryNorm_zeroBlock` and
  `maxEntryNorm_le_zero_of_eq_zeroBlock`. The concrete active Schur-stage
  update sequence is now available, and
  `higham13_algorithm13_3_upper_block_bound_of_eq_stage` plus
  `higham13_algorithm13_3_eq13_21_blockMaxNorm_bound_of_pivot_mul_diag_eq_upper_eq`
  convert exact upper-block stage equality into the concrete Eq.13.21 wrapper.
  `higham13_algorithm13_3_upperFromStages` now supplies the assembled upper
  factor whose upper-stage equality and strict-lower zero shape are proved by
  construction, and its Eq.13.21 wrapper removes those obligations for that
  source object. `higham13_algorithm13_3_diagLowerCert` supplies the concrete
  source-recurrence diagonal lower-bound certificate and removes the diagonal
  update equality premise from the assembled-upper Eq.13.21 route. The
  column-BDD specialization now also removes the generic max-norm majorant
  premise for the `2*||A||` route, and the reciprocal variant exposes the
  pivot condition in the source-facing form. The active-product variant removes
  the separate nonzero pivot-inverse norm premise by deriving it from the active
  product identity. The direct pivot-bound variant now avoids requiring that
  equality and leaves only the scalar product bound for this diagonal
  certificate open for the `2*||A||` route; reciprocal pivot data and the
  general growth-factor definition remain open for the broader Eq.13.21/Problem
  13.4 route.
- The p.254 row block diagonal dominance example is closed in scalar-block form:
  `higham13_rowdom_largeL_A eps = [[eps,0],[1/2,1]]`,
  `higham13_rowdom_largeL_reconstructs` proves the displayed `LU` identity for
  `eps ≠ 0`, and `higham13_rowdom_largeL_arbitrarily_large` proves the
  subdiagonal `L` entry can exceed any nonnegative threshold.
- Problem 13.1's displayed local norm inequalities are represented by
  `higham13_problem13_1_column_step_bounds` and
  `higham13_problem13_1_row_step_bounds`. These are scalar norm-level
  consequences of bidiagonal block-LU subordinate-norm estimates plus inherited
  column/row block diagonal dominance. They do not close the final qualitative
  stability deduction, which still depends on the full Theorem 13.6 path.
- Problem 13.2 is closed by explicit 4-by-4 scalar witnesses grouped into
  2-by-2 blocks. `higham13_problem13_2_incomparability` packages the four
  directions: column/1-norm point diagonal dominance does not imply
  block-column dominance, block-column dominance does not imply point column
  dominance, row/infinity-norm point diagonal dominance does not imply
  block-row dominance, and block-row dominance does not imply point row
  dominance.
- The SPD partition wrapper closes the symmetric `Matrix.fromBlocks` display
  `[[A11,A21ᵀ],[A21,A22]]`. The SPD block-LU existence prose is also closed at
  the uniform-block model level: `Matrix.PosDef (blockMatrixFlat A)` implies
  every leading block prefix is flat positive definite by
  `leadingBlockPrefix13_2_posDef_flat_of_posDef_flat`, hence block-nonsingular
  by `LeadingPrincipalBlockNonsingular13_2.of_posDef_flat`, and
  `BlockLUFactSpec.existsUnique_of_posDef_flat` applies Theorem 13.2 to produce
  a unique block LU factorization. `higham13_spd_leadingBlock_posDef` and
  `higham13_spd_schurComplement_source_posDef` close the leading-block and
  Schur-complement positive-definiteness dependencies for the Hermitian block
  form and the book's real source display used in Lemma 13.10. Lemma 13.9 is
  closed by the exact source-facing 2-norm/canonical-inverse theorem, and
  Lemma 13.10 is now closed by
  `higham13_lemma13_10_schur_kappa_bound_of_spd`.
- Problem 13.3 is closed by the scalar-block witness `[[1,-1],[-1,1]]`: it is
  symmetric, has positive diagonal, satisfies `IsBlockDiagDomRow` for block-norm
  table `|Aᵢⱼ|` and diagonal inverse reciprocal `1`, and is not `IsSymPosDef`
  because `(1,1)` has quadratic form zero.
- Problem 13.5 is closed in local block-partition form by
  `higham13_problem13_5_oneNormRect_bound`: point column diagonal dominance on
  the leading block columns, encoded by `higham13_problem13_5_columnOff` plus
  `higham13_problem13_5_trailingCol`, and an explicit right inverse
  `A11 * A11_inv = I` imply `oneNormRect (rectMatMul A21 A11_inv) <= 1`.
- Do not treat the conditional adapters
  `higham13_lemma13_9_conditional_bound` and
  `higham13_lemma13_10_conditional_bound` as the completed proofs of Lemmas
  13.9 and 13.10. The inventory points to the exact closure theorems instead.
- Lemma 13.9 now also has a genuine Cholesky product-route foundation:
  `higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le` proves the
  operator-2 certificate for `R12^T R11^{-T}` from operator-2 certificates for
  `R12` and `R11^{-1}` plus the product majorant
  `||R12||_2 ||R11^{-1}||_2 <= sqrt(kappa_2(A))`, and
  `higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_of_eq` transfers
  it across the source identity `A21 A11^{-1} = R12^T R11^{-T}`. The source
  identity itself is now closed by `higham13_lemma13_9_cholesky_block_identity`
  from the Cholesky block equations, `A11^{-1} = R11^{-1} R11^{-T}`, and
  `R11 * R11^{-1} = I`; the needed generic algebra is
  `rectMatMul_assoc`, `rectMatMul_id_right`, and `rectMatMul_id_left` in
  `MatrixAlgebra.lean`. The scalar product majorant is now reduced by
  `higham13_lemma13_9_product_majorant_from_square_bounds` to squared
  Cholesky norm bounds and `||A||_2 ||A^{-1}||_2 <= kappa_2(A)`, with
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_block_eqs` combining
  that scalar bridge with the exact block equations.
  `vecNorm2_finiteBasisVec`, `rectOpNorm2Le_radius_nonneg`, and
  `higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_of_rect_operator_bounds`
  remove the separate `0 <= ||R12||_2` and `0 <= ||R11^{-1}||_2`
  assumptions from the product route on nonempty rectangular domains.
  `higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_from_square_bounds_of_rect_operator_bounds`
  and
  `higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_of_eq_from_square_bounds_of_rect_operator_bounds`
  push that cleanup through the squared-bound and equality-instantiated
  squared-bound routes.
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_block_eqs_of_rect_operator_bounds`
  applies the cleaned equality route after the exact Cholesky block identity,
  so the source block-equation certificate no longer exposes the two
  rectangular radius nonnegativity assumptions on nonempty dimensions.
  `rectOpNorm2Le_sqrt_of_vecNorm2Sq_le` now converts a quadratic square-action
  inequality into a rectangular operator-2 certificate, and
  `higham13_lemma13_9_R12_rectOpNorm2Le_of_A22_cholesky_block` proves the
  `R12` Cholesky square-bound certificate from
  `A22 = R12^T R12 + R22^T R22` plus an `opNorm2Le A22 ||A||_2` premise.
  The principal-block inheritance side is now closed by
  `finiteOpNorm2Le_sumInr_principal`, `opNorm2Le_of_finiteOpNorm2Le`,
  `higham13_lemma13_9_A22_opNorm2Le_of_full_block`,
  `higham13_lemma13_9_A22_opNorm2Le_of_full_block_eq`, and
  `higham13_lemma13_9_R12_rectOpNorm2Le_of_full_cholesky_block`, which feed a
  full block operator-2 certificate into the `R12` Cholesky square-bound route.
  The matching inverse-principal branch is now closed by
  `finiteOpNorm2Le_sumInl_principal`,
  `higham13_lemma13_9_A11inv_opNorm2Le_of_full_inverse_block`,
  `higham13_lemma13_9_A11inv_opNorm2Le_of_full_inverse_block_eq`,
  `higham13_lemma13_9_R11inv_rectOpNorm2Le_of_A11inv_cholesky_block`, and
  `higham13_lemma13_9_R11inv_rectOpNorm2Le_of_full_inverse_cholesky_block`.
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_full_operator_bounds`
  assembles the exact Cholesky block identity, both square-bound branches, and
  `||A||_2 ||A^{-1}||_2 <= kappa_2(A)` into the desired operator certificate.
  `finiteVecNorm2_finiteBasisVec` and `finiteOpNorm2Le_radius_nonneg` now
  prove nonnegativity of any finite vector-action operator radius on a
  nonempty index type, and
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_nonempty_full_operator_bounds`
  uses them to remove the separate `0 <= ||A||_2` and
  `0 <= ||A^{-1}||_2` assumptions from the full-operator route when the block
  dimension is nonempty.
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_nonempty_full_operator_bounds_kappa_product`
  removes the separate condition-number majorant when `kappa_2(A)` is
  represented directly by `||A||_2 ||A^{-1}||_2`.
  The source row is still not fully closed because the bare SPD hypothesis has
  not yet been connected to all of those Cholesky/final norm-condition
  certificates. Focused
  Lean/build/lookup, placeholder scan, `git diff --check`, and `#print axioms`
  for the route theorems, rectangular product lemmas, block identity,
  square-bound route wrappers, `R12` bridge, `A22` principal-block bridge,
  `R11inv` inverse-principal bridge, full-operator assembly theorem, and the
  nonempty full-operator wrapper and product wrapper were clean with only
  standard Mathlib axioms.
- Eq.13.24 now has the source-shaped scalar product theorem
  `higham13_eq13_24_spd_scalar_bound`, proving
  `||L||_2 ||U||_2 <= sqrt(m) * (1 + m * sqrt(kappa_2(A))) * ||A||_2`
  from explicit `||L||_2 <= 1 + m * sqrt(kappa_2(A))` and
  `||U||_2 <= sqrt(m) * ||A||_2` premises. Lemmas 13.9 and 13.10 now supply
  the SPD condition-number ingredients; the proof of the remaining source
  product premises, especially the `U` norm bound and the full Theorem 13.6
  implementation-facing path, remains open.
- SPD Eq.13.24/Eq.13.25 scalar surfaces were tightened after audit:
  `spd_backward_error_bound` no longer carries the former vacuous
  backward-error hypothesis, and the SPD scalar wrappers no longer carry unused
  nonnegativity hypotheses. Focused Lean, focused `BlockLU` build,
  `lake env lean -s 65536 examples/LibraryLookup.lean`, `git diff --check`,
  placeholder scan, and `#print axioms` for `block_lu_stability_spd`,
  `higham13_eq13_24_spd_scalar_bound`, `spd_backward_error_bound`, and
  `spd_backward_error_bound_higham_13_25` were clean; only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound` appear.

## Build State

- `lake build` succeeds with Lean toolchain `leanprover/lean4:v4.29.0-rc3`.
- No real `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` declarations were
  found in `LeanFpAnalysis` during the 2026-05-23 health check.
- Current build warnings are cleanup warnings concentrated in QR/least-squares:
  unused simp arguments in `QR/GivensSpec.lean`, unused variables in
  `QR/HouseholderQR.lean`, `QR/GivensQR.lean`, `QR/QRSolve.lean`,
  `LeastSquares/LSQRSolve.lean`, `LeastSquares/LSNormalEquations.lean`, and
  `FastMatMul.lean`.
- After the 2026-04-26 fix pass, `main` was fast-forward merged to
  `015d6c4`.  Later benchmark work was split onto branch `benchmark`.
- `.vscode/` remains unrelated untracked local editor state.

## Earlier Context Found

- Old in-repo agent settings and benchmark prompt files were removed so the
  repository no longer carries tool-specific benchmark guidance.
- Earlier project notes framed the project as a VSCL/Thrust A thesis library
  for compositional stability-carrying foundations, not as a goal to formalize
  all of Higham.
- Durable user/project preferences: formalize only reusable stepping stones for
  future stability proofs; always search the existing codebase before claiming
  a theorem or definition is missing; put proof sketches in docstrings; keep
  Higham constants exact.

## Top-Level Structure

- `LeanFpAnalysis.lean` imports `LeanFpAnalysis.FP`.
- `LeanFpAnalysis/FP.lean` imports `Model`, `Analysis`, and `Algorithms`.
- `LeanFpAnalysis/FP/Analysis.lean` re-exports:
  `Error`, `Rounding`, `Summation`, `SubtractionFold`, `Stability`,
  `ForwardError`, `FiniteProbability`, `MatrixAlgebra`, `PerturbationTheory`.
- `LeanFpAnalysis/FP/Algorithms.lean` re-exports the algorithm families:
  summation, dot/matvec/matmul, triangular solves and bounds, LU, Cholesky,
  QR, least squares, Sylvester, iterative refinement, matrix inversion,
  stationary iteration, matrix powers, underdetermined systems, fast matmul.

## Foundation Modules

- `Model.lean`: `FPModel` with `u`, `u_nonneg`, `fl_add/sub/mul/div/sqrt`,
  exact `fl_add_zero`, and standard relative-error axioms for each operation.
  The square-root axiom is stated for nonnegative inputs.
- `Analysis/Error.lean`: `absError`, `relError`, `compRelErrorBounded`.
- `Analysis/Stability.lean`: scalar/vector backward-error predicates,
  componentwise relative backward stability, scalar `condNumber`, and
  `forward_from_backward`.
- `Analysis/Rounding.lean`: `gamma`, `gammaValid`, gamma monotonicity and
  arithmetic, `prod_error_bound`, `gamma_mul`, `gamma_inv`, `gamma_div`,
  `gamma_inv_mul_roundoff`, and absorption lemmas such as
  `three_gamma_plus_sq_le_gamma`.
- `Analysis/Summation.lean`: `fl_sum_error`, `fl_sum_error_init`,
  `fl_sum_error_tight`.
- `Analysis/SubtractionFold.lean`: subtraction-fold and inverse-product
  error lemmas used by triangular substitution proofs.
- `Analysis/FiniteProbability.lean`: lightweight finite probability spaces,
  finite Markov, Chebyshev, exponential Markov, and Chernoff kernels.
- `Analysis/MatrixAlgebra.lean`: exact matrix operations, inverses, norms,
  transpose, Frobenius algebra, vector 2-norm/operator-2 predicate bounds,
  orthogonal matrices, Neumann-series style bounds. This is foundational but
  very large and could eventually be split.
- `Analysis/PerturbationTheory.lean`: residual, normwise/componentwise
  perturbation, Oettli-Prager, Rigal-Gaches, Skeel condition definitions.

## Strong Reuse Chain

- `Rounding` supports `Summation` and `SubtractionFold`.
- `Summation` supports `DotProduct`.
- Exact algebraic operations should be separated from rounded algorithms.
  For dot product, Mathlib's `x ⬝ᵥ y = ∑ i, x i * y i` is the exact
  specification, while local `fl_dotProduct` is the rounded left-to-right
  recurrence using `fp.fl_mul` and `fp.fl_add`.  Stability theorems should
  compare the rounded algorithm to the exact Mathlib specification; they should
  not pretend the whole dot product always has a single global relative error,
  because cancellation can make that false.
- `DotProduct` supports `MatVec`.
- `MatVec` supports `MatMul` and matrix inversion residual results.
- `DotProduct` supports `Norm2`, which gives the reusable `fl_norm2Sq` and
  `fl_norm2` kernels needed by later Householder reflector construction.
  `Norm2` states exact facts directly over Mathlib's `x ⬝ᵥ x` and
  `‖WithLp.toLp 2 x‖`; it should not reintroduce exact vector-norm aliases.
  Premature Householder construction/application modules were removed from
  `end-to-end-rebuild` so the branch can proceed bottom-up from foundations
  before returning to QR-specific kernels.
- `TriangularSolve` and `ForwardSub` use `SubtractionFold`/`Rounding` and feed
  `TriangularSolveCombined`, `ForwardError`, `MMatrix`, LU solve, Cholesky
  solve, matrix inversion, and underdetermined systems.
- `ForwardError` combines triangular backward error with exact inverse
  predicates from `MatrixAlgebra`.
- LU modules build from Gaussian elimination specs into solve and growth-factor
  results; Cholesky solve reuses triangular solves and Cholesky specs.
- RandNLA Algorithm 1 now builds as:
  `ElementwiseSampling` for squared-magnitude probabilities, deterministic
  sampled-entry updates, traces, hit counts, and entrywise stability events;
  `Analysis/FiniteProbability` for generic probability kernels; and
  `HitCountConcentration` for Markov, pairwise-Chebyshev, and canonical
  product-law Chernoff concentration plus high-probability stability.
  `ElementwiseSpectral` adds the deterministic equation (2) transfer layer:
  exact rectangular `rectOpNorm2Le` spectral residual events transfer to
  floating-point residual events by adding the Frobenius norm of a proved
  entrywise FP perturbation budget. This does not prove the missing exact
  matrix concentration theorem.
  It also contains `algorithm1ExactFrobEvent` and the bridge theorems
  `probability_algorithm1_exact_spectral_of_frob` and
  `probability_algorithm1_fl_spectral_of_exact_frob`, which transfer a proved
  exact Frobenius residual event to exact/FP rectangular operator events.
  The canonical product trace law now also proves the weaker nonconditional
  Frobenius/Markov route:
  `sqMagTraceProbability_expectationReal_elementwiseTraceResidual_frob_sq_le`,
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_frob`,
  and
  `sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_ge_one_sub_frob`.
  Do not cite these as CACM equation (2); they carry an `m*n` Frobenius factor
  and do not replace matrix Bernstein/Khintchine.
  The scalar entrywise route now also uses the generic finite-intersection
  union bound
  `FiniteProbability.eventProb_forall_ge_one_sub_sum` to prove
  `sqMagTraceProbability_eventProb_algorithm1ExactEntrywiseEvent_ge_one_sub`,
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_entrywise`,
  and
  `sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_ge_one_sub_entrywise`.
  This is a real high-probability support theorem, but it is still only
  Markov-plus-union-bound over entries and must not be cited as CACM equation
  (2)'s Bernstein/Khintchine spectral concentration theorem.
  `MatrixAlgebra` now provides vector-norm homogeneity and
  `rectUnitBallCover`/`rectOpNorm2Le_of_unit_ball_cover`.  Algorithm 1 composes
  this deterministic cover geometry with finite-test-set Markov tails and a
  Frobenius residual event in
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_cover`
  and
  `sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_ge_one_sub_cover`.
  These theorems assume a supplied finite unit-ball cover and are still support
  infrastructure, not a construction of an optimal net or a replacement for
  matrix Bernstein/Khintchine.
  The matrix-concentration route now also has self-adjoint dilation
  infrastructure in `MatrixAlgebra`: `finiteVecNorm2`, `finiteMatVec`,
  `finiteFrobNormSq`, `finiteMatMul`, `finiteIdMatrix`, `finiteTranspose`,
  `finiteTrace`,
  `finiteTrace_add`, `finiteTrace_smul`, `finiteTrace_finiteMatMul_comm`,
  `finiteMatVec_finiteMatMul`, `finiteMatVec_finiteIdMatrix`,
  `finiteVecNorm2Sq_finiteMatVec_le_finiteFrobNormSq_mul`,
  `finiteOpNorm2Le`, `finiteQuadraticForm`, `finitePSD`,
  `finiteLoewnerLe`,
  `abs_finiteVecInnerProduct_finiteMatVec_le_of_finiteOpNorm2Le`,
  `finiteQuadraticForm_add`, `finiteQuadraticForm_neg`,
  `finiteQuadraticForm_sub`,
  `finiteQuadraticForm_finset_sum`,
  `finiteQuadraticForm_finset_sum_smul`,
  `finiteQuadraticForm_fintype_sum`,
  `finiteQuadraticForm_fintype_sum_smul`,
  `finitePSD_fintype_sum_of_finitePSD`,
  `finitePSD_fintype_sum_smul_of_nonneg`,
  `abs_finiteQuadraticForm_le_of_loewnerLe_neg`,
  `finiteQuadraticForm_finiteMatMul_self_of_symmetric`,
  `finitePSD_finiteMatMul_self_of_symmetric`,
  `finiteQuadraticForm_finiteMatMul_self_le_finiteFrobNormSq_mul_of_symmetric`,
  `finiteMatMul_self_loewnerLe_scalar_id_of_finiteOpNorm2Le`,
  `finiteOpNorm2Le_of_finiteMatMul_self_loewnerLe_scalar_id`,
  `rectSelfAdjointDilation`,
  `finitePSD_rectSelfAdjointDilation_square`,
  `rectSelfAdjointDilation_square_loewnerLe_scalar_id_of_finiteOpNorm2Le`,
  `rectSelfAdjointDilation_opNorm2Le_of_square_loewnerLe_scalar_id`,
  `rectOpNorm2Le_of_selfAdjointDilation_square_loewnerLe_scalar_id`,
  `finiteFrobNormSq_rectSelfAdjointDilation`,
  `finiteTrace_finiteMatMul_rectSelfAdjointDilation_self`, and
  `rectOpNorm2Le_of_selfAdjointDilation`.  `ElementwiseSpectral` connects this
  to Algorithm 1 with `algorithm1ExactDilationEvent`,
  `algorithm1ExactDilationSquareEvent`,
  `algorithm1ExactDilationSquareEvent_subset_exactDilationEvent`,
  `algorithm1ExactDilationSquareEvent_subset_exactSpectralEvent`,
  `rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement`,
  `sqMagProb_sum_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_eq_zero`,
  `sqMagProb_sum_finiteFrobNormSq_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_le`,
  `sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le`,
  `sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le`,
  `sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id`,
  `sqMagProb_sum_rectSelfAdjointDilation_square_psd`,
  `sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id`,
  `sqMagProb_sum_steps_rectSelfAdjointDilation_square_psd`,
  `sqMagProb_sum_finiteTrace_rectSelfAdjointDilation_square_le`,
  `sqMagProb_sum_steps_finiteTrace_rectSelfAdjointDilation_square_le`,
  `probability_algorithm1_exact_spectral_of_dilation`, and
  `probability_algorithm1_fl_spectral_of_exact_dilation`, plus
  `probability_algorithm1_exact_spectral_of_dilation_square` and
  `probability_algorithm1_fl_spectral_of_exact_dilation_square`.  These remain
  bridge and quadratic-form/Loewner/PSD/trace variance-proxy theorems, plus
  deterministic trace/order algebra, trace monotonicity, scalar-identity trace
  bounds, symmetric operator-square trace bounds, and trace-of-square
  identities for the dilation; they do not prove Bernstein/Khintchine.
  The matrix algebra layer also bridges local finite symmetry to mathlib's
  matrix API through `IsSymmetricFiniteMatrix.to_matrix_isSymm` and
  `Matrix_isSymm.to_IsSymmetricFiniteMatrix`, plus the Hermitian bridge
  `IsSymmetricFiniteMatrix.to_matrix_isHermitian` and
  `Matrix_isHermitian.to_IsSymmetricFiniteMatrix`, so a future
  largest-eigenvalue or trace-exponential proof can use mathlib symmetry and
  Hermitian facts without changing the RandNLA algorithm definitions.  The same layer now bridges
  local `finitePSD`/`finiteLoewnerLe` facts to mathlib `Matrix.PosSemidef`
  through `finitePSD.to_matrix_posSemidef`,
  `Matrix_posSemidef.to_finitePSD`,
  `finitePSD_iff_matrix_posSemidef_of_symmetric`,
  `finiteLoewnerLe.to_matrix_posSemidef_sub`, and
  `Matrix_posSemidef_sub.to_finiteLoewnerLe`, plus the iff theorem
  `finiteLoewnerLe_iff_matrix_posSemidef_sub_of_symmetric`.
  `Analysis/MatrixSpectral.lean` now adds `finiteHermitianEigenvalues`,
  `finiteHermitianEigenvalues_mem_spectrum_real`, and
  `finiteTrace_eq_sum_finiteHermitianEigenvalues`, a mathlib-backed spectral
  hook for finite real symmetric matrices.  It also has
  `finitePSD_iff_finiteHermitianEigenvalues_nonneg`,
  `finiteLoewnerLe_iff_sub_finiteHermitianEigenvalues_nonneg`, and
  `finiteLoewnerLe_smul_id_iff_sub_finiteHermitianEigenvalues_nonneg`, so
  local PSD and scalar-identity Loewner upper events can be read as
  nonnegativity of Hermitian eigenvalues of difference matrices.  This is still foundation only; the
  matrix Bernstein/Khintchine tail is not proved.
  `FiniteProbability` now has real-valued exponential Markov in
  `eventProb_real_ge_le_exp_mul_mgf` and
  `eventProb_real_le_ge_one_sub_exp_mul_mgf`.
  External literature search recorded Tropp, "User-friendly tail bounds for
  sums of random matrices" (Found. Comput. Math. 12 (2012), arXiv:1004.4389)
  as advisory guidance for the next source-chain targets: Theorem 3.6,
  Corollary 3.7, Theorem 1.4, and Theorem 1.6. These are not formalized or
  used as hidden hypotheses.
- RandNLA Algorithm 2 row sampling builds in `Algorithms/RandNLA/RowSampling.lean`
  and `Algorithms/RandNLA/RowSamplingGram.lean`: equation (4) norm-squared row
  probabilities, literal sampled rows, local one-division FP stability,
  elementwise unbiasedness of `Atildeᵀ Atilde`, the iid variance calculation,
  high-probability equation (5), the probability-one support theorem for
  positive-probability row traces, and explicit FP perturbation/bias theorems
  for the Gram matrix.
  Do not cite any grouped row-hit or Chernoff-count theorem for Algorithm 2;
  Algorithm 2 does not accumulate repeated sampled rows.
- RandNLA Algorithm 2 leverage-score row sampling builds in
  `Algorithms/RandNLA/RowSamplingLeverage.lean`: equation (6) is formalized as
  the existing row-norm-squared distribution applied to an orthonormal-column
  matrix `U`, proving `p_i = ||U_i*||_2^2 / n`, `rowGram U = I`, and equation
  (7) in vector-action operator-2 form. The fully floating-point equation (7)
  corollary reuses `rowSampleGramFullFpPerturbBudget` and `dotProduct_error_bound`.
- RandNLA equation (8) least-squares work now includes
  `Algorithms/RandNLA/LeastSquaresSketch.lean`: `lsObjective`,
  `PreservesLSObjective`, and deterministic sketched-minimizer residual
  objective theorems. It also has the coordinate quadratic-error bridge
  `preservesLSObjective_of_coordinate_quadratic_error` and finite-probability
  transfer `eventProb_preservesLSObjective_of_coordinate_quadratic_error`,
  which turn an already proved operator-2 Gram-error event into
  `PreservesLSObjective`. The high-probability theorem that a concrete random
  sketch supplies the residual coordinates and operator event with the survey
  sample complexity remains open.
- The Section 7 open backlog is tracked in
  `docs/RANDNLA_CACM_NOT_PROVED_LEDGER.md`. Open paper-level items remain:
  Algorithm 1 equation (2) exact matrix concentration, matrix
  Bernstein/Khintchine, randomized LS embedding for equation (8), low-rank
  equation (9), and matrix completion equations (10)--(11).

## Known Weak Spots

These compile, but should not be treated as fully derived stability results:

- `Algorithms/MatrixInversion.lean` no longer has `True` placeholder fields in
  `BlockMethod1BSpec`.  The block-indexing details remain abstract, but the
  spec now exposes the concrete per-column backward-error contract used to
  prove `triInv_method1B_right_residual_from_spec`.
- Several high-level theorems are wrappers around a hypothesis that is already
  essentially the conclusion:
  `GaussJordan.lean` recurrence/forward/backward/SPD residual wrappers;
  `MatrixInversion.lean` method 2, method 2C, method D, and SPD method D
  wrappers; `CholeskyDemmel.lean` scaled forward-error wrapper;
  `CholeskyIndefinite.lean` Bunch-Parlett/Bunch-Kaufman wrappers;
  `CholeskyNonsym.lean` nonsymmetric PD growth and Mathias success wrappers;
  `CholeskyPSD.lean` Schur perturbation, W-norm, complete-pivoting, and
  termination wrappers; `CholeskyPerturbation.lean` normwise perturbation
  wrapper; `SylvesterPerturbation.lean` first-order linearized wrapper.
- These wrappers are acceptable as named interfaces only if the supplied
  hypothesis is intentionally an abstract external theorem. They should not be
  advertised as internally proved from the FP model.  These wrappers were
  redocumented as abstract interfaces in the 2026-04-26 fix pass.

## Organization Notes

- The core library organization is coherent: model -> analysis infrastructure
  -> low-level algorithms -> higher-level algorithms.
- `MatrixAlgebra.lean` is over 1200 lines and mixes general algebra, norms,
  orthogonality, and Neumann theory. A future split into matrix basics, norms,
  orthogonal/Frobenius, and Neumann/resolvent infrastructure would improve
  maintainability.
- `HitCountConcentration.lean` is large but now logically narrower after moving
  generic finite-probability kernels to `Analysis/FiniteProbability.lean`. It
  remains internally sectioned; future growth could justify splitting hit-count
  moments, budgets, and the squared-magnitude product trace law.
- Triangular inverse infrastructure is split across
  `TriangularForwardBound.lean` and `InverseBounds.lean`. This works, but a
  neutral `Analysis/TriangularAlgebra.lean` or `Algorithms/TriangularInverse`
  module would make the dependency story cleaner.
- `MMatrix.lean` proves the Corollary 8.10 relative-error statement in μ-form
  via `mmatrix_forwardSub_relative_error`.  It does not separately formalize
  the asymptotic simplification `μ_i ≤ (n²+n+1)u + O(u²)` as a Big-O theorem.
## Branch Notes

- Benchmark artifacts and benchmark-specific decision notes were moved to
  branch `benchmark` on 2026-04-28.
- RandNLA Algorithm 1 deterministic and randomized stability work lives on
  branch `RandNLA_Kimon`. The public entry point is
  `LeanFpAnalysis.FP.Algorithms.RandNLA`.
- Algorithm 2 row sampling is also on `RandNLA_Kimon`; cite
  `fl_rowSampleSketch_error_bound` for the local sampled-entry FP division
  bound, `rowSqNormTraceProbability_expectationReal_rowSampleGram_entry` for
  unbiasedness of `Atildeᵀ Atilde`,
  `rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon`
  for the exact high-probability equation (5) bound, and
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget`
  for the fully floating-point Gram corollary; it reuses `fl_dotProduct` /
  `dotProduct_error_bound` and has an explicit budget with `δτ = 0`.
- For Algorithm 2 equation (6)/(7), cite
  `leverageTraceProbability_eventProb_rowSampleGram_opNorm2_error_le_epsilon`
  for the exact leverage-score subspace-embedding theorem and
  `leverageTraceProbability_eventProb_fl_rowSampleGramDot_opNorm2_error_le_epsilon_add_budget`
  for the fully floating-point theorem. These use `opNorm2Le`, the vector-action
  form of an operator-2-norm bound, rather than a supremum-valued spectral norm.
- For Algorithm 1 equation (2)-style floating-point transfer, cite
  `fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact`,
  `fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact_and_hitCount_le`, and
  `probability_algorithm1_fl_spectral_of_exact_spectral`. Do not cite these as
  the exact equation (2) concentration theorem; they require an exact spectral
  event as input.
- For the weaker Frobenius-to-operator route, cite
  `algorithm1ExactFrobEvent_subset_exactSpectralEvent`,
  `probability_algorithm1_exact_spectral_of_frob`, and
  `probability_algorithm1_fl_spectral_of_exact_frob`. These require a proved
  exact Frobenius residual event as input and do not close equation (2).
- For equation (8) deterministic least-squares sketching, cite
  `lsObjective_le_of_sketch_preserves` and
  `lsObjective_le_one_add_eta_of_sketch_preserves`. Do not cite these as a
  randomized sampling/sample-complexity theorem.
- Keep benchmark task files, stubs, generated-workspace scripts, run protocols,
  and task-selection rationale off `main` unless the user explicitly decides to
  merge them back.
- Library implementation work after the benchmark audit lives on
  `end-to-end-rebuild`, renamed from the earlier QR-specific branch.
  The branch should proceed bottom-up: stabilize the general foundations first,
  then add concrete rounded kernels, then prove bridge theorems showing those
  kernels satisfy the existing contracts.

## 2026-05 End-To-End Rebuild Work

- End goal for this branch: each important high-level stability contract should
  eventually be backed by a concrete rounded `fl_*` algorithm and a theorem
  proving that algorithm satisfies the contract from `FPModel`, rather than
  only assuming the contract.
- Step 1 foundation audit began with `FPModel`, `Rounding`, `Summation`,
  `SubtractionFold`, `Stability`, and `MatrixAlgebra`.  The scan found no
  `sorry`, `admit`, `axiom`, or `opaque` in these files.  The main immediate
  gap was documentation precision: distinguish the Higham standard model from
  extra exactness assumptions, and mark `MatrixAlgebra` as exact algebra rather
  than floating-point algorithm code.
- Foundation cleanup replaced the old locally-defined `infNorm hn A` API with
  Mathlib-backed compatibility wrappers: `infNormVec v := ‖v‖` and
  `infNorm A := ‖Matrix.of A‖` with a local Mathlib `linfty` operator-norm
  instance.  `infNormBound n M c` is now the clean norm inequality
  `infNorm M ≤ c`, with row-wise bridge lemmas `row_sum_le_infNorm`,
  `infNorm_le_of_row_sum_le`, and `row_sum_le_of_infNormBound` for
  Neumann proofs.
- Exact norm policy: use Mathlib norm/dot-product infrastructure directly for
  exact algebra and avoid duplicate local aliases when practical.  Exact vector
  aliases `exactNorm2Sq`, `exactNorm2`, `norm2Sq`, and `norm2Vec` were removed;
  `Norm2` now states exact facts over `x ⬝ᵥ x` and `‖WithLp.toLp 2 x‖`
  directly.  Floating-point kernels such as `fl_dotProduct`, `fl_norm2Sq`, and
  `fl_norm2` remain local because they encode rounded operation order.
- Matrix shape aliases were added in `MatrixAlgebra`: `RVec n := Fin n → ℝ`,
  `RMat m n := Matrix (Fin m) (Fin n) ℝ`, `RSqMat n := RMat n n`, and
  `RMatFn m n := Fin m → Fin n → ℝ`.  New exact matrix-facing APIs should
  prefer `RMat` when possible, while existing algorithm code may keep using
  `RMatFn` during gradual migration.
- Current exact Frobenius policy: keep `frobNorm` as a readable rectangular
  compatibility wrapper over Mathlib, not as an independent norm definition:
  `frobNorm A := ‖(Matrix.of A : RMat m n)‖`.  The source of truth is
  Mathlib's Frobenius norm, while public statements over legacy function-shaped
  matrices stay readable.  Keep `frobNormSq` only as a squared convenience for
  existing sum-of-squares algebra and sep/Sylvester proofs until a separate
  squared-norm migration is planned.
- Matrix-shape policy for the rebuild: rectangular real matrices are needed
  before full QR/least-squares implementation-backed proofs.  Avoid adding new
  square-only exact infrastructure unless the algorithm is inherently square.
  Prefer APIs that can move toward `Matrix (Fin m) (Fin n) ℝ` or compatible
  `Fin m → Fin n → ℝ` wrappers.  Do not attempt a silent global migration to
  complex matrices: complex floating-point arithmetic needs an explicit later
  model, probably built from real rounded operations on real and imaginary
  parts rather than by treating `ℂ` operations as primitive.
- Corrected the QR implementation plan to start with missing low-level
  primitives rather than treating reflector construction as permanently out of
  scope.
- Extended `FPModel` with `fl_sqrt` and `model_sqrt` for nonnegative real
  inputs.
- Added `Algorithms/Norm2.lean` with floating 2-norm kernels `fl_norm2Sq` and
  `fl_norm2`, plus exact Mathlib facts over `x ⬝ᵥ x` and
  `‖WithLp.toLp 2 x‖`: `norm_toLp_two_eq_sqrt_dotProduct`,
  `dotProduct_self_nonneg_real`, `dotProduct_self_eq_zero_iff_real`,
  `dotProduct_self_ne_zero_iff_real`, `dotProduct_self_pos_iff_real`, and
  `norm_toLp_two_nonneg`.
- Removed premature `HouseholderReflector` and `HouseholderApply` additions from
  the active branch.  They were useful prototypes, but the user decided the
  rebuild should not move into Householder-specific kernels before auditing the
  lower-level foundation chain.
- Historical early-rebuild next step was the bottom-up audit/cleanup beginning
  with `DotProduct` and its exact-specification bridge to Mathlib
  `dotProduct`; that phase has since been used as the template for the QR
  rebuild.
- Rebuild standard clarified with the dot-product/QR contrast.  `DotProduct.lean`
  is the positive template: it defines a concrete rounded algorithm
  `fl_dotProduct` from `FPModel` primitives and proves
  `dotProduct_backward_error` from that definition using summation and gamma
  lemmas.  At the start of the rebuild, QR was not at that standard:
  `householder_qr_backward` consumed an assumed
  `OrthogonalSequenceBackwardError`, and `HouseholderAppError` was only a
  specification.  The current Householder QR safe `R`, safe RHS, safe solve,
  and computed `(Q_hat, R_hat)` layers now have concrete implementation-backed
  bridge theorems; the old sequence-level theorem remains as a reusable
  transfer theorem, not the main implementation-backed result.
- Whole-library repass aim: keep contracts/specification structures as useful
  modular interfaces, but add implementation-backed bridge theorems wherever a
  public algorithmic stability result currently depends only on a supplied
  contract.  The desired chain is `FPModel` primitives -> concrete `fl_*`
  algorithm -> theorem that the algorithm satisfies its contract -> final
  stability theorem.  Avoid claiming end-to-end stability for modules that stop
  before the bridge theorem.
- A local Codex skill for this workflow was created at
  `~/.codex/skills/lean-fp-stability-audit/SKILL.md`.  Use it when auditing or
  rebuilding modules for implementation-backed stability proofs.
- Skill/source policy: always compare the proof boundary against the original
  source, not just the current Lean file.  If Higham or another source proves a
  lower-level bound, the rebuild should formalize that bound rather than treating
  it as a permanent assumption in a higher-level theorem.  QR/Householder in
  Higham Chapter 18 is the motivating example.
- Internal rebuild planning files were created under ignored `thesis/`:
  `thesis/IMPLEMENTATION_BACKED_AUDIT.md` records the current module-by-module
  classification, and `thesis/REPASS_LEDGER.md` records the phased checklist for
  the repass.  Future work should use these with the
  `lean-fp-stability-audit` skill.
- Treat `thesis/REPASS_LEDGER.md` as living documentation.  Update it whenever
  a higher-level proof reveals a missing lower-level rounded operation, bridge
  theorem, source reference, or dependency not visible in the initial audit.
- Phase 1 foundation audit completed on 2026-06-01.  Targeted `lake env lean`
  passed for `FP/Model.lean`, `Analysis/Rounding.lean`, `Analysis/Error.lean`,
  `Analysis/Summation.lean`, `Analysis/SubtractionFold.lean`,
  `Analysis/Stability.lean`, and `Analysis/MatrixAlgebra.lean`.  Only narrow
  documentation edits were made: `fl_add_zero` is explicitly an extra exactness
  hypothesis, and `gammaValid` is described as model-parametric rather than
  IEEE-specific.
- Phase 2 scalar/vector audit completed on 2026-06-01.  Targeted `lake env lean`
  passed for `RecursiveSum.lean`, `PairwiseSum.lean`, `SumTree.lean`,
  `DotProduct.lean`, `OuterProduct.lean`, and `Norm2.lean`.  `DotProduct` is the
  positive implementation-backed template.  `OuterProduct` documentation was
  corrected to stress that its perturbation theorem is row-wise and not a global
  backward-stability result, matching Higham's discussion after equation (3.6).
  `Norm2` is implementation-backed as a kernel.  Later Phase 5 work added the
  Householder-specific norm bridges needed for Chapter 18 reflector
  construction.
- Phase 3 basic matrix-kernel audit completed on 2026-06-01.  Targeted
  `lake env lean` passed for `MatVec.lean`, `MatMul.lean`, and
  `LeastSquares/LSNormalEquations.lean`.  Added concrete bridge theorems
  `gramProductError_from_fl_matMul` and `gramVecError_from_fl_matVec`, so the
  normal-equations Gram product/vector contracts can now be proved from
  `fl_matMul` and `fl_matVec`.  Cholesky remains the contract-level dependency
  in normal equations.
- Phase 4 triangular-solve audit completed on 2026-06-01.  `TriangularSolve` and
  `ForwardSub` are implementation-backed: the concrete recursive rounded
  algorithms prove `fl_backSub_satisfies_spec` and
  `fl_forwardSub_satisfies_spec`, then the backward-error theorems consume those
  proved row-spec bridges.  `TriangularSolveCombined` only composes those proved
  results.  The derived forward-error/comparison/M-matrix theorems take exact
  inverse, exact-solution, diagonal-dominance, M-matrix, and `gammaValid`
  hypotheses; these are mathematical problem assumptions, not missing rounded
  algorithm contracts.  `TriangularForwardComparison` was relabelled so the
  backward-error-derived comparison bound is not confused with Higham's direct
  Theorem 8.9 μ-bound (`forwardSub_forward_error_mu_bound`).
- Phase 5 low-level QR rebuild started on 2026-06-01.  Added
  `Algorithms/QR/HouseholderReflector.lean` with concrete rounded kernels
  `fl_householderScale`, `fl_householderVector`, and `fl_householderBeta`.
  Source alignment matters here: Higham Lemma 18.1 computes
  `s = sign(x_0)||x||_2`, `v_0 = fl_add x_0 s_hat`, and
  `beta_hat = fl_div 1 (fl_mul s_hat v_hat_0)`.  The dot-product beta path
  `2/fl_dotProduct(v,v)` is an alternate algorithm and should not be used to
  claim Higham's `γ_{4n+8}` bound.  Applying `sign(x_0)` is exact in Higham's
  operation count, so `fl_householderScale` is an exact sign change of
  `fl_norm2`, not a rounded multiplication.  The current kernels follow the source order.
  Their unroll lemmas reduce the construction to existing `fl_norm2`,
  `fp.model_add`, `fp.model_mul`, and `fp.model_div` layers.
  Added `Algorithms/QR/HouseholderApply.lean` with concrete rounded
  `fl_householderApply`, modeling `b - beta * v * (v^T b)` and unrolling it into
  dot-product, multiplication, and subtraction errors.  Lemma 18.1 is now
  implementation-backed by later bridge theorems; Lemma 18.2 application
  stability remains the next missing bridge.
- Phase 5 source boundary update on 2026-06-02: inspecting `References/Chapter18.pdf`
  page images confirmed that Higham Lemma 18.2 assumes the normalized reflector
  perturbation model from equation (18.3) before deriving the application error
  `y_hat = (P + ΔP)b`.  Added `HouseholderVectorError` to
  `HouseholderSpec.lean` to represent that intermediate contract explicitly, and
  added `householder_matMulVec_eq` in `HouseholderApply.lean` to connect the
  exact reflector matrix with the closed-form expression
  `b - beta * v * (v^T b)`.  Do not add a vacuous theorem that proves
  `HouseholderAppError` by manufacturing an arbitrary post-hoc `ΔP`; the real
  bridge is `fl_householderVector -> HouseholderVectorError`, followed by
  `fl_householderApply + HouseholderVectorError -> HouseholderAppError`.
- Phase 5 exact-form update on 2026-06-02: added exact Householder construction
  definitions `householderScale`, `householderAlpha`, `householderVector`,
  `householderBeta`, and `householderBetaFromScale`, plus
  `householderBeta_mul_norm_sq`.  Added normalized-form support
  `householderNormalizedVector`, `householder_normalizedVector_eq`, and
  `householderNormalizedVector_norm_sq`.  This proves the algebraic bridge
  between the library's unnormalized `I - beta v v^T` reflector and Higham's
  normalized `I - v v^T` equation (18.3) form.  Later bridge theorems prove the
  rounded construction satisfies the normalized-vector perturbation model.
- Also added `householder_exact_orthogonal`: exact `householderVector` together
  with exact `householderBeta` produces an orthogonal reflector whenever
  `v^T v` is nonzero.  Later rounded proofs should compare the computed
  construction against this exact reflector rather than re-proving exact
  orthogonality algebra.
- Added `fl_householderVector_tail_eq_householderVector`, proving the
  implementation-backed exact-copy part of Higham Lemma 18.1: all non-first
  components of the rounded Householder vector agree with the exact vector.
- Added `HouseholderConstructionError`, the explicit Higham Lemma 18.1 contract:
  tail equality, first-component relative error bounded by `γ_{n+2}`, and beta
  relative error bounded by `γ_{4n+8}`.  Also added exact source-alignment
  lemmas `householderScale_mul_self`,
  `householderVector_norm_sq_eq_two_scale_mul`, and
  `householderBetaFromScale_eq_householderBeta`, connecting the source beta
  formula `1/(s*v_0)` with the reflector beta formula `2/(v^T v)`.
- Added Householder-facing norm bridges in `Norm2.lean`:
  `weighted_sum_relative_error_nonneg`, `fl_norm2Sq_relative_error`, and
  `fl_norm2_relative_error_sqrt_factor`.  These prove the source step
  `fl(x^T x) = (1+θ_n)x^T x` and expose
  `fl(||x||_2) = sqrt(x^T x) * sqrt(1+θ_n) * (1+δ)`.
  Added the exact square-root perturbation lemma
  `sqrt_one_add_sub_one_abs_le_abs`, the gamma bridge
  `sqrt_one_add_mul_roundoff_gamma`, and the source-style norm theorem
  `fl_norm2_relative_error`, so the rounded norm now has
  `fl_norm2 x = ||x||_2 * (1+θ_{n+1})` from the concrete `fl_norm2`
  implementation.
- Added `householderVector_zero_abs_eq`, proving the exact no-cancellation fact
  `|x_0+s| = |x_0| + |s|`, and
  `fl_householderScale_relative_error_sqrt_factor`, which composes the new
  `fl_norm2` bridge with exact sign application.  Added
  `fl_householderScale_relative_error` and
  `fl_householderVector_zero_relative_error`, proving the
  first-component `γ_{n+2}` part of Higham Lemma 18.1 for nonzero inputs from
  the concrete rounded Householder vector implementation.
- Added `gamma_inv_mul_roundoff` in `Rounding.lean` so a reciprocal of a
  `γ_k`-perturbed denominator plus the final division rounding can be bounded
  by `γ_{2k}`.  This preserves Higham's beta constant rather than weakening it
  by one extra gamma index.
- Added `fl_householderBeta_denominator_relative_error`,
  `fl_householderBeta_relative_error`, and `fl_householderConstructionError`.
  For nonzero inputs, the concrete rounded Householder construction now
  satisfies the full `HouseholderConstructionError` contract matching Higham
  Lemma 18.1: exact tail copy, first-component `γ_{n+2}` perturbation, and
  beta `γ_{4n+8}` perturbation.
- Added `sqrt_one_add_mul_relative_gamma` in `Norm2.lean` and the normalized
  Householder construction bridges `householderVectorError_from_construction`
  and `fl_householderVectorError`.  For nonzero inputs and a stronger
  `gammaValid fp (8*n+16)` side condition, the concrete rounded construction
  now satisfies Higham equation (18.3) after algebraic normalization, with
  explicit bound `γ_{5n+10}` as a concrete instance of Higham's generic
  `γ_{cm}`.
- Added `householderApplyRoundedMatrix`,
  `householderApplyDeltaMatrix`, `fl_householderApply_matrix_unroll`, and
  `fl_householderApply_appError_of_matrix_bound`.  These prove that the
  concrete rounded Householder application is multiplication by a matrix
  determined by the primitive rounding errors, and they isolate the exact
  remaining Lemma 18.2 obligation: prove a Frobenius norm bound for that
  concrete delta matrix from `HouseholderVectorError` and the primitive error
  bounds.  This is not yet the full Lemma 18.2 stability theorem.
- Added exact norm helpers in `MatrixAlgebra.lean` turning entrywise absolute
  bounds into Frobenius bounds, plus `HouseholderVectorError` consequences in
  `HouseholderSpec.lean`: sum-of-squares for the normalized vector, a
  componentwise magnitude bound for the computed vector, and relative factors
  `v_hat_i = v_i(1+alpha_i)`.  Added `HouseholderApply` factorization and
  entrywise gamma theorems for the normalized application delta.  The current
  next gap is now the final Frobenius summation estimate that turns these
  entrywise gamma facts into a concrete `HouseholderAppError` bound.
- Completed the normalized one-reflector Householder application bridge:
  `householderApply_sub_error_frob_bound`,
  `householderApply_outer_gamma_frob_bound`,
  `householderApplyDeltaMatrix_normalized_frob_bound`, and
  `fl_householderApply_normalized_appError`.  This proves that if equation
  (18.3) is supplied for a normalized computed vector, then the concrete
  rounded `fl_householderApply fp n v_hat 1 b` satisfies `HouseholderAppError`.
  The bound is currently the raw expression
  `sqrt(n*u^2) + 2*gamma(2a+n+3)`, not yet collapsed into Higham's generic
  `gamma_cm` notation.
- Added `Algorithms/QR/HouseholderOneStep.lean` with
  `fl_householderConstructApply_appError`, combining the concrete construction
  bridge `fl_householderVectorError` with
  `fl_householderApply_normalized_appError`.  For nonzero input vectors and
  `gammaValid fp (11*n+23)`, concrete construction plus concrete application
  now satisfies `HouseholderAppError` for one reflector, again with the raw
  bound `sqrt(n*u^2) + 2*gamma(11*n+23)`.
- Added `Algorithms/QR/HouseholderMatrixStep.lean` with
  `fl_householderApplyMatrix`, `ColumnwiseHouseholderStepError`, and
  `fl_householderConstructApply_matrix_step_error`.  This lifts the concrete
  one-vector reflector result to a concrete matrix-column step: each output
  column of `fl_householderApplyMatrix` satisfies `HouseholderAppError` with a
  column-dependent perturbation matrix.  This is intentionally weaker than the
  existing `orthogonal_sequence_one_step` hypothesis, which uses one global
  `ΔP` for the whole matrix step; Higham's Lemma 18.3 proof is columnwise, so
  the next QR bridge must aggregate column-dependent perturbations rather than
  silently forcing them into a global perturbation.
- Added exact columnwise Frobenius aggregation lemmas in `MatrixAlgebra.lean`:
  `matMulVec_sum_sq_le_frobNormSq_mul_sum_sq`,
  `frobNormSq_columnwise_matMulVec_le`, and
  `frobNorm_columnwise_matMulVec_le`.  `HouseholderMatrixStep.lean` now exposes
  `ColumnwiseHouseholderStepError.exists_residual_matrix_bound`, proving that a
  columnwise Householder step has a single residual matrix `E` with
  `A_hat = P*A + E` and `‖E‖_F ≤ c*‖A‖_F`.  The next gap is turning repeated
  residual steps into the final `Qᵀ(A+ΔA)`/QR backward-error statement.
- Added residual-form sequence one-step theorems in `HouseholderQR.lean`:
  `orthogonal_sequence_one_step_of_residual` and
  `orthogonal_sequence_one_step_of_columnwise_error`.  These advance the
  sequence invariant from `A_hat = Qᵀ(A+ΔA)` through a step
  `A_next = P*A_hat + E` with `‖E‖_F ≤ c‖A_hat‖_F`, and the columnwise version
  consumes `ColumnwiseHouseholderStepError` directly.  This avoids the stronger
  old assumption that one global `ΔP` explains a whole matrix step.  The
  remaining QR gap is the repeated-step induction/loop model and the final
  connection to `HouseholderQRBackwardError`.
- Added `idMatrix_orthogonal` in `MatrixAlgebra.lean` and the conservative
  repeated residual theorem `residual_orthogonal_sequence_backward_error` in
  `HouseholderQR.lean`.  If each step has
  `A_{k+1} = P_k*A_k + E_k`, each `P_k` is orthogonal, and
  `‖E_k‖_F ≤ c‖A_k‖_F`, the theorem proves
  `A_r = Qᵀ(A_0+ΔA)` with
  `‖ΔA‖_F ≤ residualAccumBound c r * ‖A_0‖_F`.  This keeps higher-order terms
  via a recurrence instead of forcing the first-order `r*c` simplification.
  The next QR gap is a concrete Householder QR loop/sequence feeding these
  hypotheses, plus a sourced gamma-collapse lemma if the public theorem should
  recover Higham's `r*c`/`γ_cm` style bound.
- Added `columnwise_householder_sequence_backward_error`,
  `householderConstructApplyBound`, `householderConstructApplyBound_nonneg`,
  and `fl_householder_sequence_backward_error`.  The last theorem proves that
  any matrix sequence updated by repeated concrete
  `fl_householderApplyMatrix` steps, with reflectors concretely constructed
  from nonzero `xseq k`, satisfies the residual orthogonal-sequence
  backward-error theorem.  This is still not full QR factorization because the
  theorem does not yet define/select the QR trailing-column vectors or prove
  triangularization; it is the implementation-backed repeated-reflector bridge
  needed before that final QR loop theorem.
- Added rectangular panel infrastructure for Householder QR trailing updates:
  `matMulRect` in `MatrixAlgebra.lean`,
  `frobNormSq_columnwise_matMulVec_le_rect`,
  `frobNorm_columnwise_matMulVec_le_rect`,
  `fl_householderApplyMatrixRect`,
  `ColumnwiseHouseholderStepErrorRect`, and
  `fl_householderConstructApply_matrix_step_error_rect`.  A square
  Householder reflector can now be applied to an `m × p` panel, and the
  concrete rounded panel update has a columnwise backward-error contract plus a
  single residual matrix bound `‖E‖_F ≤ c‖A‖_F`.  This is needed before the
  real QR loop can operate on trailing rectangular panels instead of only
  square full matrices.
- Added exact rectangular orthogonal algebra:
  `matMulRect_id_left`, `matMulRect_add_right`,
  `matMulRect_assoc_square_left`, `frobNormSq_orthogonal_left_rect`, and
  `frobNorm_orthogonal_left_rect`.  Added rectangular residual sequence
  theorems in `HouseholderQR.lean`:
  `orthogonal_sequence_one_step_of_residual_rect`,
  `residual_orthogonal_sequence_backward_error_rect`,
  `columnwise_householder_panel_sequence_backward_error`, and
  `fl_householder_panel_sequence_backward_error`.  Repeated concrete
  Householder panel updates now satisfy a rectangular backward-error sequence
  theorem.  Remaining QR work: define the actual trailing-panel loop and prove
  it supplies these panel update hypotheses and triangularization.
- Added `panelFirstColumn` and
  `fl_householder_first_column_panel_step_error`.  This specializes the
  rectangular panel bridge to the first-column choice used by a Householder QR
  panel step.  It is the first link from arbitrary supplied construction
  vectors toward an actual QR loop, but it still does not define recursive
  trailing panels or prove triangularization.
- Added `fl_householder_first_column_panel_sequence_backward_error`, which
  repeats the first-column panel choice over a fixed rectangular panel shape.
  This removes the arbitrary `xseq` layer for fixed panels.  Remaining QR work
  is still the dependent trailing-panel loop with shrinking dimensions and the
  triangularization/package proof.
- Added exact trailing-panel indexing infrastructure in `HouseholderQR.lean`:
  `panelDropFirstRow`, `panelDropFirstCol`, and `trailingPanel`, plus the
  concrete rounded shrinking step `fl_householderTrailingPanelStep`.  This
  models one QR move from an `(m+1) × (p+1)` panel to its updated trailing
  `m × p` panel.  This is still an indexing/algorithm-definition layer; the
  next proof gap is an induction over these dependent shrinking panel shapes
  and the exact triangularization property.
- Added `frobNormSq_trailingPanel_le`, `frobNorm_trailingPanel_le`, and
  `fl_householderTrailingPanelStep_residual`.  The concrete one-step shrinking
  QR panel update now has a residual representation inherited from the full
  first-column Householder panel step.  Remaining QR work: dependent induction
  across changing dimensions, exact zeroing/triangularization, and packaging
  into the final `HouseholderQRBackwardError`.
- Added exact Householder zeroing lemmas in `HouseholderOneStep.lean`:
  `householderVector_dot_original_eq_scale_mul_zero`,
  `householder_constructed_matMulVec_first`, and
  `householder_constructed_matMulVec_tail_zero`.  These prove the exact
  triangularization kernel for one constructed reflector:
  the source column is mapped to `-s e_0`, so all tail components are zero.
  This is exact algebra, not yet a rounded triangularization theorem for the
  full QR loop.
- Added panel-level exact triangularization bridges in `HouseholderQR.lean`:
  `householder_first_column_panel_exact_first` and
  `householder_first_column_panel_exact_tail_zero`.  These lift the exact
  one-vector zeroing theorem to the first column of a rectangular panel after
  applying the constructed exact reflector.  The next QR gap is to combine this
  exact zeroing fact with the rounded residual theorem in the shrinking-panel
  induction.
- Added panel decomposition infrastructure in `HouseholderQR.lean`:
  `panelTopLeft`, `panelTopRowTail`, `panelFirstColumnTail`, and
  `panelFirstColumnTailZero`.  Added exact bridges
  `householder_panel_exact_topLeft` and
  `householder_panel_exact_firstColumnTailZero`, so the one-step exact
  triangularization result is now stated in the panel shape that the future QR
  loop will consume.
- Added `fl_householder_first_column_panel_step_residual_and_shape`, which
  packages one concrete rounded first-column Householder panel update with:
  a residual matrix bound for the computed full-panel update, the exact
  top-left value of the underlying reflector step, and exact first-column tail
  zeroing.  This is the one-step implementation-backed panel bridge; remaining
  QR work is the dependent induction over shrinking panels and final packaging.
- Added `IsUpperTriangular` and
  `StructuredHouseholderQRBackwardError` in `HouseholderQR.lean`.  The original
  `HouseholderQRBackwardError` remains the normwise backward-error contract
  only; the structured contract explicitly includes the `R_hat` upper-triangular
  shape requirement.  `structured_householder_qr_backward` is only a packaging
  theorem from the old backward-error theorem plus a supplied triangularity
  proof; the rebuild still has to prove triangularity from the concrete rounded
  QR loop.
- Added `HouseholderPanelState`, `householderPanelStateStep`, and
  `householderPanelStateIterate` as the first dependent-loop substrate for
  Householder QR.  The state tracks the active trailing panel and the concrete
  step shrinks nonempty panels using `fl_householderTrailingPanelStep`.  It does
  not yet store the accumulated `Q` or completed `R` rows, so it is not a full
  QR algorithm definition yet.
- Added `householderPanelStateStep_nonempty_residual_and_shape`, the state-level
  one-step bridge.  For a nonempty active panel, the concrete state transition
  has a residual representation for the next active panel and reuses the exact
  top-left/first-column-tail-zero facts for the underlying reflector step.
  Remaining QR work: induction over `householderPanelStateIterate`, plus a
  richer state that records accumulated `Q` and completed `R` structure.
- Added `HouseholderPanelStepReady` and `HouseholderPanelRunReady`, plus
  `householderPanelRunReady_head` and `householderPanelRunReady_tail`.  These
  predicates record the per-step nonzero-column and gamma-validity hypotheses
  needed to use the implementation-backed one-step panel bridge during an
  induction over `householderPanelStateIterate`.
- Added `householderPanelStateStep_nonempty_residual_and_shape_of_ready`, so the
  state-level one-step bridge can consume `HouseholderPanelStepReady` directly
  instead of unpacking nonzero-column and gamma-validity hypotheses at every
  future induction site.
- Added `householderPanelRunReady_succ_iff`, splitting a ready run of length
  `r+1` into a ready current step and a ready tail after
  `householderPanelStateStep`.  This is the intended induction shape for future
  repeated active-panel proofs.
- Added `householderPanelStepReady_nonempty_of_global_gammaValid`, allowing a
  global `gammaValid fp (11*N+23)` assumption for an original row dimension to
  satisfy the current active panel's smaller per-step gamma condition.
- Added `embedTrailingOne` in `HouseholderQR.lean`, embedding an active-panel
  square matrix as the lower-right block of a matrix with leading scalar
  identity.  This is the exact algebraic bridge needed before a trailing-panel
  Householder reflector can be composed as a full-size QR transformation.
- Added exact embedding algebra for `embedTrailingOne`: transpose commutation,
  multiplication commutation, identity preservation, and orthogonality
  preservation.  This means an orthogonal active-panel reflector can now be
  lifted to a full-size orthogonal transformation.
- Added rectangular panel action lemmas for `embedTrailingOne`: left
  multiplication leaves the top row unchanged and the trailing panel becomes
  the smaller `matMulRect` action on the old trailing panel.  These lemmas
  connect full-size embedded transformations with active-panel updates.
- Added `panelFromTopAndTrailing`, exact QR bookkeeping that reconstructs a
  nonempty panel from the computed top row and trailing panel while setting the
  first-column tail to zero.  This supports an implementation-backed `R_hat`
  algorithm whose upper-triangular shape is by construction, not by assuming
  rounded operations produce exact zeros.  A recursive triangularity lemma for
  this constructor is also available.
- Added `fl_householderQRPanel_R` and square alias `fl_householderQR_R`, the
  first recursive rounded Householder QR loop that returns an `R` panel.  It
  applies the concrete rounded first-column reflector, stores the computed top
  row, zeroes the completed first-column tail by construction, and recurses on
  the computed trailing panel.  Proved `fl_householderQR_R_upper`; backward
  error for this recursive loop is still pending.
- Added projection lemmas for `fl_householderQRPanel_R`: the top-left entry
  and top-row tail are the values computed by the current rounded panel step,
  the completed first-column tail is structurally zero, and the trailing panel
  is exactly the recursive output on `fl_householderTrailingPanelStep`.
- Added the stored first-column panel residual bridge:
  `fl_householder_first_column_panel_stored_residual_and_shape`.  It proves
  that after the rounded first-column panel step, replacing the completed
  first-column tail by structural zeros preserves the same residual bound,
  because the exact Householder application has zero tail there and the
  Frobenius norm cannot increase when that residual slice is zeroed.
- Added `panelTrailingPerturbation` and its Frobenius norm equality, plus
  `panelFromTopAndTrailing_lift_trailing_rep`.  These exact algebra lemmas
  lift a tail backward representation into the full panel using
  `embedTrailingOne`, which is the block-composition step needed for the
  recursive QR backward-error induction.
- Added `HouseholderQRPanelReady`, a recursive readiness predicate for the
  concrete `fl_householderQRPanel_R` loop.  Each nonempty panel requires a
  nonzero current first column, the matching gamma-validity condition, and
  readiness of the concrete trailing-panel step.
- Added `householderQRPanelBackwardCoeff` and square alias
  `householderQRBackwardCoeff`, the recursive coefficient intended for the
  future implementation-backed QR backward-error induction.
- Added `HouseholderQRPanelBackwardError`, the rectangular induction target for
  the recursive QR implementation, plus trivial empty-row and empty-column base
  cases.  This target records `R_hat = Qᵀ(A + ΔA)` for rectangular panels; the
  square wrapper still needs to convert it to the existing
  `HouseholderQRBackwardError` form.
- Proved `householder_qr_panel_backward_cons`, the generic recursive cons
  theorem: a stored one-step residual bound for the current panel plus a
  rectangular QR backward-error proof for the trailing panel yields a full-panel
  backward-error proof.  This composes the tail proof with `embedTrailingOne`
  and uses the coefficient update `c + α*(1+c)`.
- Proved `fl_householderQRPanel_R_backward_error`, the implementation-backed
  recursive backward-error theorem for the concrete rounded
  `fl_householderQRPanel_R` loop under `HouseholderQRPanelReady`.  This closes
  the rectangular/panel-level bridge from concrete QR recursion to
  `HouseholderQRPanelBackwardError`; the remaining QR work is the square wrapper
  into `HouseholderQRBackwardError`/`StructuredHouseholderQRBackwardError`.
- Proved the square wrappers:
  `householder_qr_panel_backward_to_square`,
  `fl_householderQR_R_backward_error`, and
  `fl_householderQR_R_structured_backward_error`.  The concrete recursive
  Householder QR `R` algorithm now satisfies the existing structured QR
  backward-error contract, with the explicit `HouseholderQRPanelReady`
  assumptions and recursive coefficient `householderQRBackwardCoeff`.
- In `QR/QRSolve.lean`, added `qr_solve_backward_error_from_components`, which
  packages the existing QR-factorization, `Qᵀb`, and back-substitution component
  equations plus perturbation bounds into `QRSolveBackwardError`.  This fixes
  the algebraic packaging gap for Higham Theorem 18.5, but it is still not a
  concrete `fl_qr_solve` implementation-backed theorem.
- Added concrete QR-solve objects in `QR/QRSolve.lean`:
  `fl_householderQRPanel_rhs`, square alias `fl_householderQR_rhs`, and
  `fl_householderQR_solve`.  The RHS recursion applies the same rounded
  Householder reflectors chosen from the active `A` panel to `b`, then the solve
  definition calls `fl_backSub` on `fl_householderQR_R` and the transformed RHS.
- Added RHS one-step residual bridge in `QR/QRSolve.lean`:
  `HouseholderAppError.exists_residual_vector`,
  `fl_householder_first_column_rhs_step_error`, and
  `fl_householder_first_column_rhs_step_residual`.  These expose the computed
  RHS update as `P*b + e` with `e = ΔP*b`, using the same panel-selected
  Householder reflector as the QR factorization step.
- Added exact componentwise support in `MatrixAlgebra.lean`:
  `abs_entry_le_frobNorm`, `abs_matMulVec_le_card_frobNorm_infNormVec`,
  `abs_matMulVec_le_card_bound_infNormVec`, and orthogonal transport bounds
  `IsOrthogonal.abs_entry_le_one`,
  `IsOrthogonal.abs_matMulVec_le_card_infNormVec`, and
  `IsOrthogonal.infNormVec_matMulVec_le_card`.  These are crude but proved
  exact bounds needed to track QR-solve residual vectors without introducing
  a new assumption.
- Added `HouseholderAppError.exists_residual_vector_bound` and
  `fl_householder_first_column_rhs_step_residual_bound` in `QR/QRSolve.lean`.
  The concrete first-column RHS Householder step now has an explicit
  componentwise residual bound
  `(m+1) * householderConstructApplyBound fp (m+1) * infNormVec b`.
  Added `HouseholderQRRhsPanelBackwardError`,
  `householderQRRhsPanelBackwardBound`,
  `householder_qr_rhs_panel_backward_cons`,
  `fl_householderQRPanel_rhs_backward_error`, and
  `fl_householderQR_rhs_backward_error`.  The concrete RHS reflector recursion
  is now implementation-backed under `HouseholderQRPanelReady`, with a
  recursive componentwise perturbation bound.
- Added the simultaneous shared-orthogonal-factor bridge
  `HouseholderQRPanelSolveBackwardError`,
  `householder_qr_panel_solve_backward_cons`,
  `fl_householderQRPanel_solve_components_backward_error`, and
  `fl_householderQR_solve_components_backward_error`.  This closes the
  common-`Q` gap between the concrete `R` proof and concrete RHS proof.
- Added `fl_householderQR_solve_backward_error`, the implementation-backed
  theorem for the concrete Householder QR solve.  It combines the shared-`Q`
  QR/RHS component theorem with `backSub_backward_error`.  Side assumptions are
  explicit: `HouseholderQRPanelReady`, nonzero diagonal of the computed
  `fl_householderQR_R`, `0 < n`, and `gammaValid fp n`.  The matrix bound is
  `householderQRBackwardCoeff fp n * ‖A‖_F +
  gamma fp n * ‖fl_householderQR_R fp n A‖_F`; the RHS bound is
  `householderQRRhsBackwardBound fp n A b`.
- Began the Givens rebuild in `QR/GivensSpec.lean`.  Added concrete
  `fl_givensApply`, which applies supplied exact `c,s` parameters by two
  rounded multiplications plus rounded add/sub on the affected components and
  copies all other components exactly.  Added exact unroll lemmas for the
  computed and exact `p`, `q`, and unaffected components.  Added
  `fl_givensApply_supplied_app_error`, proving the concrete supplied-parameter
  kernel satisfies `GivensAppError` with the conservative bound
  `gamma fp 2 * ‖givensRotation n p q c s‖_F`.  This is implementation-backed
  for exact supplied `c,s`; rounded rotation-parameter construction and the
  full `fl_givens_qr` loop are still pending.
- Added exact Givens coefficient construction from Higham (18.14):
  `givensDenom`, `givensC`, and `givensS`, plus exact facts
  `givensCoeff_norm_sq`, `givensCoeff_zero_second`,
  `givensCoeff_first_component`, and `givensRotation_constructed_orthogonal`.
  Added rounded coefficient kernels `fl_givensDenom`, `fl_givensC`, and
  `fl_givensS`, with the denominator deliberately routed through the existing
  `fl_norm2` kernel.  Added conservative implementation-backed coefficient
  bridges `fl_givensC_relative_error_conservative` and
  `fl_givensS_relative_error_conservative`, proving `gamma fp 6` relative
  error bounds from `fl_norm2` plus rounded division.  Added the
  `GivensCoeffError` wrapper and `fl_givensCoeffError_conservative` so later
  Givens application/sequence proofs can consume coefficient contracts without
  unpacking both scalar theorems manually.  The sharper Higham Lemma 18.6
  target `ĉ = c(1+θ₄)` and `ŝ = s(1+θ'₄)` is still pending.
- Added `fl_givensApply_coeffError_app_error` and
  `fl_givensApply_computed_app_error_conservative`.  These close the concrete
  Givens coefficient-plus-application path: coefficients are computed by
  `fl_givensC`/`fl_givensS` and then used by `fl_givensApply`, producing a
  `GivensAppError` for the exact constructed rotation.  The bound is the
  conservative `gamma fp 8 * ‖G‖_F`, obtained by combining the current
  `gamma fp 6` coefficient bridge with two rounded operations in the
  application.  This is implementation-backed but not the sharp Higham Lemma
  18.7 constant `sqrt 2 * gamma_6`.
- Added `QR/GivensMatrixStep.lean`, defining `fl_givensApplyMatrix` and
  `fl_givensApplyMatrixRect` plus square/rectangular `ColumnwiseGivensStepError`
  contracts.  Proved `fl_givensApply_computed_matrix_step_error` and its
  rectangular version from the concrete computed-coefficient vector bridge, then
  proved residual matrix aggregation lemmas.  Added
  `fl_givens_sequence_backward_error` and
  `fl_givens_panel_sequence_backward_error` in `GivensQR.lean`, which accumulate
  any supplied concrete sequence of computed Givens updates via the existing
  residual orthogonal sequence theorem under an explicit uniform per-step bound.
  The remaining gap for full Givens QR is choosing/formalizing the annihilation
  schedule and proving the produced sequence has the QR triangular shape and a
  source-clean uniform bound.
- Added exact Frobenius facts in `MatrixAlgebra.lean`:
  `frobNormSq_idMatrix`, `IsOrthogonal.frobNormSq_eq_card`, and
  `IsOrthogonal.frobNorm_eq_sqrt_card`.  These reuse existing exact Frobenius
  invariance under orthogonal multiplication and show `‖U‖_F = sqrt n` for
  orthogonal `n × n` matrices.  Added uniform Givens sequence corollaries
  `fl_givens_sequence_backward_error_uniform` and
  `fl_givens_panel_sequence_backward_error_uniform`, discharging the earlier
  explicit per-step norm-bound assumption with `gamma fp 8 * sqrt n`.
- Added concrete current-matrix Givens column steps:
  `fl_givensColumnStepMatrix` and `fl_givensColumnStepMatrixRect`, with bridge
  theorems `fl_givensColumnStep_matrix_step_error` and the rectangular variant.
  Added sequence corollaries
  `fl_givens_column_sequence_backward_error_uniform` and
  `fl_givens_column_panel_sequence_backward_error_uniform`, where each rotation
  coefficient is computed from the evolving matrix entries
  `(Aseq k (pseq k) (colseq k), Aseq k (qseq k) (colseq k))`.  The remaining
  full-Givens-QR gap is now specifically the annihilation schedule, nonzero
  guards for the selected pivots, and the final upper-triangular shape proof.
- Added exact vector embedding algebra for the QR RHS recursion:
  `vectorTrailingPerturbation`, `embedTrailingOne_matMulVec_top`,
  `vectorTail_embedTrailingOne_matMulVec`, and
  `vectorFromTopTail_lift_trailing_rep`.  These are the vector analogues of the
  panel block-lift lemmas and prepare the recursive RHS backward-error proof.
- Returned to Householder QR before continuing Givens.  Added the zero-column
  skip infrastructure in `QR/HouseholderQR.lean`:
  `panelFirstColumnTailZero_of_panelFirstColumn_eq_zero`,
  `panelFromTopAndTrailing_of_panelFirstColumn_eq_zero`, and
  `householder_qr_panel_backward_skip_zero_column`.  These prove that if an
  active panel's first column is already zero, the QR loop can skip the
  reflector exactly and lift the recursive trailing-panel backward-error proof
  to the full panel with an embedded leading identity.
- Added zero-aware Householder QR `R` definitions:
  `fl_householderTrailingPanelStepSafe`, `fl_householderQRPanel_R_safe`, and
  square alias `fl_householderQR_R_safe`.  Added
  `HouseholderQRPanelSafeReady`, which removes the old "all active first
  columns are nonzero" requirement; gamma validity is required only on
  nonzero branches where a rounded reflector is actually computed.
- Added branch-dependent coefficient
  `householderQRPanelBackwardCoeffSafe` and proved
  `fl_householderQRPanel_R_safe_backward_error`,
  `fl_householderQR_R_safe_backward_error`, and
  `fl_householderQR_R_safe_structured_backward_error`.  The preferred
  Householder QR `R` theorem is now implementation-backed for zero and nonzero
  active columns.  Remaining QR-solve work: propagate the safe QR/RHS recursion
  through `QRSolve.lean`; the current solve theorem still uses the older
  nonzero-panel `fl_householderQR_R` path and requires nonzero diagonal of the
  computed `R`.
- Propagated the zero-aware Householder recursion through `QR/QRSolve.lean`.
  Added `fl_householderQRPanel_rhs_safe`, `fl_householderQR_rhs_safe`, and
  `fl_householderQR_solve_safe`, plus the branch-dependent RHS bound
  `householderQRRhsPanelBackwardBoundSafe`.  Added exact RHS and shared-`Q`
  skip theorems:
  `householder_qr_rhs_panel_backward_skip_zero_column` and
  `householder_qr_panel_solve_backward_skip_zero_column`.
- Proved the safe RHS and solve bridge theorems:
  `fl_householderQRPanel_rhs_safe_backward_error`,
  `fl_householderQR_rhs_safe_backward_error`,
  `fl_householderQRPanel_solve_components_safe_backward_error`,
  `fl_householderQR_solve_components_safe_backward_error`, and
  `fl_householderQR_solve_safe_backward_error`.  Householder QR solve now has
  an implementation-backed zero-aware path.  Remaining assumptions are the
  inherent back-substitution side conditions: `0 < n`, nonzero diagonal of the
  computed `fl_householderQR_R_safe fp n A`, and `gammaValid fp n`.
- Simplified the public safe Householder QR API by deriving recursive
  `HouseholderQRPanelSafeReady` from a single global gamma assumption.  Added
  `HouseholderQRPanelSafeReady_of_global_gammaValid`,
  `HouseholderQRPanelSafeReady_square_of_global_gammaValid`, and global-gamma
  wrappers for safe `R`, structured `R`, RHS, shared QR/RHS components, and
  solve:
  `fl_householderQR_R_safe_backward_error_of_global_gammaValid`,
  `fl_householderQR_R_safe_structured_backward_error_of_global_gammaValid`,
  `fl_householderQR_rhs_safe_backward_error_of_global_gammaValid`,
  `fl_householderQR_solve_components_safe_backward_error_of_global_gammaValid`,
  and `fl_householderQR_solve_safe_backward_error_of_global_gammaValid`.  The
  preferred safe solve theorem now asks for `0 < n`, global
  `gammaValid fp (11*n+23)`, and nonzero diagonal of computed `R_safe`; the
  back-substitution `gammaValid fp n` condition is derived internally.
- Supersession note: older historical bullets in this memory file that describe
  Householder QR `R` or Householder QR solve as pending are now superseded by
  the zero-aware implementation-backed theorems above.  The remaining
  Householder QR limitations are narrower: the safe solve still assumes
  nonsingularity via a nonzero diagonal condition for the computed `R_safe`, and
  it does not yet build or return an explicit accumulated `Q` matrix as part of
  the algorithm output.
- Interpretation note: an existential exact orthogonal `Q` in
  `HouseholderQRBackwardError` is acceptable for the Higham-style QR
  backward-error theorem.  The implementation-backed part is the concrete
  rounded `R_safe` algorithm and its bridge to the backward-error contract.
  Returning a separately computed floating-point `Q` would be a distinct future
  API, not a prerequisite for the current `R` or QR-solve stability claims.
- Started the explicit `Q` layer for Householder QR without claiming a rounded
  accumulated `Q_hat`.  Added `fl_householderQRPanel_Q_safe`,
  `fl_householderQR_Q_safe`, and `HouseholderQRWitness` /
  `fl_householderQR_safe_witness`.  These expose the exact orthogonal witness
  generated from the same safe branch choices and rounded trailing panels as
  `fl_householderQR_R_safe`.  Proved
  `fl_householderQRPanel_Q_safe_orthogonal`,
  `fl_householderQR_Q_safe_orthogonal_of_global_gammaValid`, and witness
  wrappers for `Q` orthogonality, `R` upper-triangularity, and the existing
  structured `R` backward-error theorem.
- Completed the next explicit-`Q` milestone.  Added
  `HouseholderQRPanelExplicitBackwardError` and
  `HouseholderQRExplicitBackwardError`, plus explicit skip/cons algebra,
  `fl_householderQRPanel_R_safe_explicit_backward_error`, and
  `fl_householderQR_safe_witness_explicit_backward_error_of_global_gammaValid`.
  The public safe witness now satisfies a fixed-`Q` perturbation equation:
  its `Q` field is the orthogonal factor used in `Q * R = A + ΔA`, with the
  same branch-dependent `householderQRBackwardCoeffSafe` bound.  This is still
  an exact `Q` witness, not a rounded accumulated `Q_hat`.
- Started the concrete rounded `Q_hat` API for Householder QR.  Added
  `fl_householderQRPanel_Qhat_safe`, `fl_householderQR_Qhat_safe`,
  `HouseholderQRComputedFactors`, and `fl_householderQR_computed_safe`.
  The nonzero recursive branch applies the same rounded Householder reflector
  used for the panel update to the embedded trailing `Q_hat` accumulator via
  `fl_householderApplyMatrixRect`; zero branches embed the trailing accumulator
  exactly.  No orthogonality or backward-error theorem is claimed for `Q_hat`
  yet.  The next proof layer is a rounded-accumulation bridge relating this
  computed `Q_hat` to the exact witness or to an explicit perturbation model.
- Added the first `Q_hat` bridge theorem:
  `fl_householderQRPanel_Qhat_safe_succ_succ_nonzero_step_error`.  For each
  nonzero active panel, the rounded `Q_hat` accumulator update satisfies the
  existing implementation-backed rectangular Householder matrix-step error via
  `fl_householderConstructApply_matrix_step_error_rect`.  This is still a
  one-step theorem; the accumulated recursive `Q_hat` stability theorem is not
  proved yet.
- Added `fl_householderQRPanel_Qhat_safe_succ_succ_nonzero_residual_bound`,
  the residual-matrix form of one nonzero rounded `Q_hat` update.  It exposes
  `Qhat_next = P * embedTrailingOne(Qtail_hat) + E` with
  `‖E‖_F ≤ householderConstructApplyBound fp (m+1) *
  ‖embedTrailingOne Qtail_hat‖_F`, using the existing rectangular residual
  aggregation theorem.
- Added `fl_householderQRPanel_Qhat_safe_succ_succ_zero_residual_bound`, which
  records the safe zero-column skip branch as an identity transformation on the
  embedded trailing `Q_hat` accumulator with zero residual.  Future recursive
  `Q_hat` accumulation proofs now have residual lemmas for both branch cases.
- Added computed-factor `R_hat` wrappers:
  `fl_householderQR_computed_safe_R_hat_upper` and
  `fl_householderQR_computed_safe_R_hat_structured_backward_error_of_global_gammaValid`.
  These reuse the proved `R_safe` facts through the `HouseholderQRComputedFactors`
  API and deliberately do not assert any full stability property of `Q_hat`.
- Added
  `fl_householderQR_computed_safe_R_hat_explicit_backward_error_of_global_gammaValid`,
  which gives the computed-factor `R_hat` field the explicit exact-witness
  perturbation equation already proved for `fl_householderQR_safe_witness`.
  The witness `Q` remains exact; this is not a theorem about the rounded
  accumulated `Q_hat`.
- Added a branch-combined safe-step interface for future recursive `Q_hat`
  proofs: `householderQRPanel_Qhat_stepP_safe`,
  `fl_householderQRPanel_Qhat_tail_safe`,
  `householderQRPanel_Qhat_stepCoeff_safe`,
  `householderQRPanel_Qhat_stepP_safe_orthogonal`, and
  `fl_householderQRPanel_Qhat_safe_succ_succ_residual_bound`.  This packages
  zero and nonzero safe branches into one residual theorem of the form
  `Qhat_current = P_step * embedTrailingOne(Qhat_tail) + E` with the
  branch-appropriate coefficient.
- Added `householderQRPanel_Qhat_stepCoeff_safe_nonneg` and the bundled
  `fl_householderQRPanel_Qhat_safe_succ_succ_step_interface`, which packages
  exact-step orthogonality, coefficient nonnegativity, and residual form for
  one safe `Q_hat` step.  Future recursive proofs should use this theorem as
  the local step interface.
- Added exact embedding norm facts for the next accumulated-`Q_hat` proof:
  `frobNormSq_embedTrailingOne`, `frobNorm_embedTrailingOne`, and
  `frobNorm_embedTrailingOne_of_orthogonal`.  These make explicit that
  embedding a trailing block adds exactly the leading identity contribution to
  the Frobenius square.
- Added the first recursive accumulated `Q_hat` perturbation theorem.  The raw
  recursive bound is `householderQRPanel_QhatAccumBound`, the contract shape is
  `HouseholderQRPanelQhatAccumError`, and the algebraic one-step extension is
  `HouseholderQRPanelQhatAccumError.cons`.  The main panel theorem
  `fl_householderQRPanel_Qhat_safe_accum_error` and its square/global wrappers
  `fl_householderQR_Qhat_safe_accum_error_of_global_gammaValid` and
  `fl_householderQR_computed_safe_Q_hat_accum_error_of_global_gammaValid` prove
  that the concrete rounded accumulated `Q_hat` is an exact orthogonal matrix
  plus a bounded perturbation.  This closed the raw recursive perturbation
  layer; later bullets record the closed-form simplification and comparison
  with `fl_householderQR_Q_safe`.
- Added a cleaner recursive accumulated `Q_hat` bound,
  `householderQRPanel_QhatClosedBound`.  The helper
  `HouseholderQRPanelQhatAccumError.embedTrailingOne_norm_le` bounds the
  embedded tail accumulator norm by `sqrt (m + 1) + ηtail`, and
  `HouseholderQRPanelQhatAccumError.cons_closed` threads this through one
  Householder step.  The panel theorem
  `fl_householderQRPanel_Qhat_safe_closed_accum_error` and global wrappers
  `fl_householderQR_Qhat_safe_closed_accum_error_of_global_gammaValid` and
  `fl_householderQR_computed_safe_Q_hat_closed_accum_error_of_global_gammaValid`
  expose the resulting computed-`Q_hat` perturbation theorem.  This is still
  recursive and branch-sensitive; the next polishing steps were a compact
  closed-form growth estimate and comparison with the exact `Q_safe` witness.
- Fixed the exact reference factor in the computed-`Q_hat` perturbation theorem
  to the existing `Q_safe` witness.  The step-orientation lemma
  `fl_householderQRPanel_Q_safe_succ_succ_as_stepP_safe` uses Householder
  symmetry to show that `Q_safe` follows the same `P * embed(Qtail)` orientation
  as the rounded `Q_hat` residual recurrence.  The new fixed-reference contract
  `HouseholderQRPanelQhatFixedAccumError` and the recursive theorem
  `fl_householderQRPanel_Qhat_safe_fixed_Q_safe_closed_accum_error` prove that
  `fl_householderQRPanel_Qhat_safe = fl_householderQRPanel_Q_safe + ΔQ` with the
  closed recursive bound.  The public wrapper
  `fl_householderQR_computed_safe_Q_hat_fixed_Q_safe_closed_accum_error_of_global_gammaValid`
  states this for `(fl_householderQR_computed_safe fp n A).Q_hat` against the
  `Q` field of `fl_householderQR_safe_witness`.  Later bullets record the
  compact closed-form growth estimate and its coarser citation-friendly bound.
- Added the dimension-only uniform recursive computed-`Q_hat` bound
  `householderQR_QhatUniformClosedBound`.  Supporting lemmas prove
  `householderConstructApplyBound_mono`,
  `householderQRPanel_Qhat_stepCoeff_safe_le_global`,
  nonnegativity of the branch-sensitive closed bound, and
  `householderQRPanel_QhatClosedBound_le_uniform`.  The public theorem
  `fl_householderQR_computed_safe_Q_hat_fixed_Q_safe_uniform_accum_error_of_global_gammaValid`
  now states that the computed `Q_hat` differs from the exact safe witness `Q`
  by a perturbation bounded by a dimension-only recurrence using
  `householderConstructApplyBound fp n` and `sqrt n`.  The next step is to
  solve or upper-bound this recurrence by a compact closed-form expression.
- Solved the uniform computed-`Q_hat` recurrence exactly.  The local derived
  bound `householderQR_QhatClosedFormBound fp n k` is
  `((1 + householderConstructApplyBound fp n)^k - 1) * sqrt n`, and
  `householderQR_QhatUniformClosedBound_eq_closedForm` proves the recursive and
  closed forms are equal.  The public theorem
  `fl_householderQR_computed_safe_Q_hat_fixed_Q_safe_closed_form_accum_error_of_global_gammaValid`
  now states `Q_hat = Q_safe + ΔQ` with this closed-form bound.  Remaining
  QR-side polish is optional coefficient simplification/weakening into a more
  conventional printed Higham-style constant, not the recurrence solution.
- Added `HouseholderQRComputedFactorsExplicitError` and the public theorem
  `fl_householderQR_computed_safe_explicit_error_of_global_gammaValid`, which
  packages the current computed `(Q_hat, R_hat)` API honestly: `R_hat` satisfies
  the explicit exact-witness backward-error theorem, and `Q_hat` is the same
  exact witness plus a perturbation bounded by `householderQR_QhatClosedFormBound`.
  This is the main theorem to cite for the current computed Householder QR
  factor pair.
- Tightened the QR-solve component layer with fixed exact witnesses.  In
  `QR/QRSolve.lean`, added `HouseholderQRRhsPanelExplicitBackwardError`,
  `HouseholderQRPanelSolveFixedBackwardError`, explicit RHS base/cons/skip
  lemmas, and
  `fl_householderQR_rhs_safe_explicit_backward_error_of_global_gammaValid`.
  The theorem
  `fl_householderQR_solve_components_safe_fixed_Q_safe_backward_error_of_global_gammaValid`
  now packages the concrete safe `R` panel and safe RHS transform with the same
  explicit `fl_householderQR_Q_safe` witness.  The final
  `QRSolveBackwardError` remains existential in `Q` because its public solved
  system statement does not expose the factor.
- The proof of `fl_householderQR_solve_safe_backward_error` now consumes
  `fl_householderQR_solve_components_safe_fixed_Q_safe_backward_error`
  directly, so the final safe solve theorem is proved through the fixed
  `Q_safe` component bridge even though its public statement hides `Q`.
- Added a simpler growth corollary for the computed `Q_hat` perturbation
  theorem.  `householderQR_QhatClosedFormBound_le_growth` proves
  `((1+c)^k - 1) sqrt(N) ≤ k*c*(1+c)^k*sqrt(N)` for
  `c = householderConstructApplyBound fp N`, and the public wrappers
  `fl_householderQR_Qhat_safe_fixed_Q_safe_growth_accum_error_of_global_gammaValid`
  and
  `fl_householderQR_computed_safe_Q_hat_fixed_Q_safe_growth_accum_error_of_global_gammaValid`
  expose that coarser but easier-to-cite bound.  The sharper closed-form theorem
  remains the canonical result.
- Added source-facing growth wrappers for the implementation-backed
  Householder QR `R_hat` theorem:
  `householderQRBackwardCoeffSafe_le_highamGrowth`,
  `fl_householderQR_R_safe_backward_error_highamGrowth_of_global_gammaValid`,
  `fl_householderQR_safe_witness_explicit_backward_error_highamGrowth_of_global_gammaValid`,
  and
  `fl_householderQR_computed_safe_R_hat_explicit_backward_error_highamGrowth_of_global_gammaValid`.
  These prove the concrete safe rounded `R` algorithm satisfies a
  dimension-only bound `n*c*(1+c)^n*‖A‖_F`, with
  `c = householderConstructApplyBound fp n`, by first bounding the
  branch-sensitive implementation coefficient by `residualAccumBound` and then
  solving/bounding that recurrence.
- Added `HouseholderQRComputedFactorsResidualError` and
  `fl_householderQR_computed_safe_residual_error_highamGrowth_of_global_gammaValid`.
  This is the theorem that directly uses the concrete product
  `Q_hat * R_hat`: it proves a residual bound for the rounded factors by
  combining the exact-witness `R_hat` backward error with the bounded
  perturbation `Q_hat = Q_safe + ΔQ`.  It deliberately does not assert that
  `Q_hat` is orthogonal.  Higham Theorem 18.4 uses an exact orthogonal product
  of Householder reflectors; a separately rounded accumulated `Q_hat` is only
  near that exact factor under the general `FPModel`.
- Added single-`gamma` Householder QR wrappers.  `Rounding.lean` now has
  `n_mul_u_le_gamma`, and `HouseholderQR.lean` has
  `residualAccumBound_mono`,
  `residualAccumBound_gamma_le_gamma_mul`,
  `householderConstructApplyGammaIndex`,
  `householderConstructApplyBound_le_gamma`, and
  `householderQRBackwardCoeffSafe_le_gamma_higham`.  The public theorem
  `fl_householderQR_computed_safe_R_hat_explicit_backward_error_gammaHigham_of_global_gammaValid`
  states the implementation-backed computed `R_hat` theorem with bound
  `gamma fp (n * householderConstructApplyGammaIndex n) * ‖A‖_F`.  The paired
  computed-factor and residual wrappers are
  `fl_householderQR_computed_safe_explicit_error_gammaHigham_of_global_gammaValid`
  and
  `fl_householderQR_computed_safe_residual_error_gammaHigham_of_global_gammaValid`.
  This is the closest formal counterpart to Higham Theorem 18.4's hidden
  `n γ_cm` notation while keeping the operation count explicit.
- Added rectangular single-`gamma` Householder QR panel wrappers.  The sharper
  bound `householderQRPanelBackwardCoeffSafe_le_residualAccumBound_min_global`
  counts at most `min m p` recursive panel stages, and
  `householderQRPanelBackwardCoeffSafe_le_gamma_higham_rect` absorbs that
  rectangular recurrence into one gamma term.  The public theorem
  `fl_householderQRPanel_R_safe_explicit_backward_error_gammaHigham_of_global_gammaValid`
  states that the concrete zero-aware rounded rectangular `R_safe` panel and
  exact orthogonal `Q_safe` witness satisfy
  `‖ΔA‖_F ≤ gamma fp (min m p * householderConstructApplyGammaIndex m) * ‖A‖_F`.
  The tall specialization
  `fl_householderQRPanel_R_safe_explicit_backward_error_tall_gammaHigham_of_global_gammaValid`
  rewrites the stage count to the number of columns when `p ≤ m` and `0 < p`.
  This aligns the implementation-backed panel theorem more closely with
  Higham's rectangular Householder QR statement.
- Added rectangular `R_safe` shape packaging for Householder QR.  The predicate
  `IsUpperTrapezoidal m p R` generalizes the square `IsUpperTriangular`
  condition, and `fl_householderQRPanel_R_safe_upper_trapezoidal` proves that
  the concrete zero-aware recursive panel algorithm returns an upper
  trapezoidal `R` panel by construction.  The structured theorem
  `fl_householderQRPanel_R_safe_structured_explicit_backward_error_tall_gammaHigham_of_global_gammaValid`
  packages this shape fact with the tall rectangular explicit-`Q_safe`
  single-gamma backward-error theorem.
- Added rectangular computed-factor packaging.  `HouseholderQRPanelComputedFactors`
  and `fl_householderQRPanel_computed_safe` expose the panel-level concrete
  `(Q_hat, R_hat)` object.  The theorem
  `fl_householderQRPanel_computed_safe_explicit_error_tall_gammaHigham_of_global_gammaValid`
  packages the structured tall rectangular `R_hat` theorem with the
  fixed-reference `Q_hat = Q_safe + ΔQ` perturbation theorem.  As in the square
  computed-factor API, it deliberately does not claim that rounded `Q_hat` is
  exactly orthogonal.
- Added exact rectangular matrix algebra needed for computed-factor residuals:
  `matMulRect_add_left` and `frobNorm_matMulRect_le`.  The theorem
  `fl_householderQRPanel_computed_safe_residual_error_tall_gammaHigham_of_global_gammaValid`
  now directly states a residual bound for the concrete tall rectangular
  product `Q_hat * R_hat`, derived from the rectangular computed-factor
  explicit-error package.
- Added a source-facing single-gamma wrapper for the safe concrete Householder
  QR solve.  `QRSolveBackwardError.mono` supports bound weakening, and
  `fl_householderQR_solve_safe_backward_error_gammaHigham_of_global_gammaValid`
  replaces the recursive QR coefficient in the final solve theorem by
  `gamma fp (n * householderConstructApplyGammaIndex n) * ‖A‖_F`.  The
  back-substitution contribution `gamma fp n * ‖R_safe‖_F` remains separate
  because it belongs to the triangular solve stage.
- Added the first closed-form bridge for the safe Householder QR RHS bound in
  `QR/QRSolve.lean`.  `vectorTail_infNormVec_le` is exact indexing algebra;
  `fl_householder_first_column_rhs_step_infNormVec_le` and
  `vectorTail_fl_householder_first_column_rhs_step_infNormVec_le` derive
  one-step RHS norm growth from the concrete `fl_householderApply` bridge.
  The dimension-only coefficient `householderQRRhsGrowthCoeff` then controls
  the raw recursive RHS perturbation bound via
  `householderQRRhsBackwardBoundSafe_le_growthCoeff_of_global_gammaValid`.
  The final wrapper
  `fl_householderQR_solve_safe_backward_error_gammaHigham_rhsGrowth_of_global_gammaValid`
  now presents the matrix perturbation bound with the single-gamma QR
  factorization coefficient plus the separate triangular-solve term, and the
  RHS perturbation bound as `householderQRRhsGrowthCoeff fp n * ‖b‖∞`.
  The theorem `householderQRRhsGrowthCoeff_le_closedGrowth` gives a conservative
  nonrecursive growth bound for that RHS coefficient, and
  `fl_householderQR_solve_safe_backward_error_gammaHigham_rhsClosedGrowth_of_global_gammaValid`
  packages it into the final solve contract.  This closed RHS expression is a
  local derived citation bound, not a sharp Higham constant.
- Added `HouseholderQRExplicitBackwardError.frobNorm_R_hat_le` and
  `fl_householderQR_R_safe_frobNorm_le_gammaHigham_of_global_gammaValid` in
  `QR/HouseholderQR.lean`, proving that the computed safe `R` factor satisfies
  `‖R_safe‖_F ≤ (1 + gamma_K) ‖A‖_F` from the explicit QR backward-error
  theorem.  The solve wrapper
  `fl_householderQR_solve_safe_backward_error_gammaHigham_closedInputBounds_of_global_gammaValid`
  now presents both final solve bounds in terms of the original inputs `A` and
  `b`, while keeping QR factorization and back-substitution contributions
  visibly separated in the matrix coefficient.

## 2026-05-22 RandNLA Algorithm 1 Work

- Added `Algorithms/RandNLA/ElementwiseSampling.lean` and
  `Algorithms/RandNLA/HitCountConcentration.lean`, re-exported through
  `Algorithms/RandNLA.lean` and `Algorithms.lean`.
- Formalized squared-magnitude sampling probabilities
  `p_ij = A_ij^2 / ‖A‖_F^2`, deterministic Algorithm 1 sampled-entry updates,
  trace hit counts, and entrywise floating-point stability budgets.
- Proved high-probability stability routes using Markov, pairwise-Chebyshev,
  and Chernoff concentration for the hit counter.
- Closed the Chernoff gap for the canonical independent Algorithm 1 sampler:
  `sqMagTraceProbability` is the finite product trace law, and
  `sqMagTraceProbability_chernoff_mgf_bound` proves the Bernoulli-sum MGF bound
  from that product law rather than assuming it.
- The final canonical high-probability stability APIs are
  `highProbability_sqMagTraceStability_of_independent_chernoff_budget` and
  `highProbability_sqMagTraceStability_of_independent_chernoff_optimized_tail_budget`.
- Generic `*_of_mgf_bound` lemmas remain only as reusable probability bridges;
  they are not the final theorem to cite for Algorithm 1.
- `docs/LIBRARY_LOOKUP.md`, `examples/LibraryLookup.lean`,
  `docs/RANDNLA_ALGORITHM1_STABILITY_LEDGER.md`, and
  `docs/Algorithm1_Stability_Proof_Summary.pdf` document the current theorem
  map.

## 2026-05-23 RandNLA Algorithm 2 Work

- Added `Algorithms/RandNLA/RowSampling.lean` for Algorithm 2 from the CACM
  RandNLA paper, using equation (4)
  `p_i = ||A_i*||_2^2 / ||A||_F^2`, and
  `Algorithms/RandNLA/RowSamplingGram.lean` for the Gram-matrix analysis.
- Formalized row norms, row probabilities, literal sampled sketches
  (`rowSampleSketch`, `fl_rowSampleSketch`), the canonical independent product
  row-trace law, `rowGram`, `rowSampleGram`, and `fl_rowSampleGram`.
- Correction: the earlier grouped row-hit/count material and the sampled-sketch
  probability-one event were removed from the Algorithm 2 API because Algorithm
  2 returns an `s × n` sampled matrix and does not sum repeated row samples.
  The later 2026-05-23 health pass also removed the unused `rowSampleHits`
  helper to keep the row-sampling API away from hit-count terminology.
- Closed the later FP-premise gap: `rowTracePositiveProb` and
  `rowSqNormTraceProbability_eventProb_rowTracePositiveProb` prove the product
  law has probability-one support on positive-probability sampled rows, and
  `rowSampleGramFpPerturbBudget` /
  `rowSampleGram_perturb_budget_le_explicit` give an explicit deterministic
  Gram perturbation budget.
- Added the fully floating-point Gram path `fl_rowSampleGramDot`, which reuses
  the repository's `fl_dotProduct` and `dotProduct_error_bound` instead of
  re-proving dot-product rounding inside RandNLA. Its final closed corollary is
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget`.
- Main APIs:
  `fl_rowSampleSketch_error_bound`,
  `rowSqNormTraceProbability_eventProb_rowTracePositiveProb`,
  `rowSqNormTraceProbability_expectationReal_rowSampleGram_entry`,
  `rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_sq_le`,
  `rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon`,
  `rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon_of_budget`,
  `rowSampleGram_entry_error_bound_of_entrywise`,
  `rowSampleGram_frob_error_bound_of_entrywise`,
  `rowSampleGramFpPerturbBudget`,
  `rowSampleGramDotProductBudget`,
  `rowSampleGramFullFpPerturbBudget`,
  `rowSampleGram_perturb_budget_le_explicit`,
  `rowSampleGram_dot_product_budget_le_explicit`,
  `rowSqNormTraceProbability_expectationReal_fl_rowSampleGram_entry_bias_bound_of_entrywise`,
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau`,
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_forall`,
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_entrywise_budget`,
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_explicit_budget`,
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget`.
- Important distinction: `..._epsilon_add_tau` is a generic union-bound
  transfer theorem with a separate perturbation failure `δτ`. The final
  theorem to cite is now `..._add_explicit_budget`; it proves the support,
  entrywise FP stability, explicit budget, and `δτ = 0` internally.
- Natural-language theorem/corollary summary:
  `docs/Algorithm2_RowSampling_Stability_Proof_Summary.pdf`.

## 2026-05-24 RandNLA Algorithm 2 Leverage Work

- Added `vecNorm2Sq`, `vecNorm2`, `opNorm2Le`, and
  `opNorm2Le_of_frobNorm_le` to `Analysis/MatrixAlgebra.lean`. This provides a
  formally proved bridge from Frobenius bounds to vector-action operator-2
  bounds without adding a new spectral-norm supremum object. Later added
  `frobNorm_const` to expose closed forms for constant Gram-budget matrices.
- Added `Algorithms/RandNLA/RowSamplingLeverage.lean` and re-exported it
  through `Algorithms/RandNLA.lean`.
- Formalized the equation (6) leverage-score row probabilities for an
  orthonormal-column matrix `U`:
  `HasOrthonormalColumns`, `leverageScore`, `leverageScoreProb`,
  `rowSqNormProbDen_eq_nat_of_orthonormal_columns`, and
  `leverageScoreProb_eq_rowNormSq_div_nat`.
- Proved equation (7) in exact arithmetic as
  `leverageTraceProbability_eventProb_rowSampleGram_opNorm2_error_le_epsilon`.
  It reuses the existing equation (5) Frobenius high-probability theorem applied
  to `U`, then transfers Frobenius control to `opNorm2Le`.
- Proved the fully floating-point equation (7) corollary
  `leverageTraceProbability_eventProb_fl_rowSampleGramDot_opNorm2_error_le_epsilon_add_budget`.
  The added FP term is exactly `rowSampleGramFullFpPerturbBudget fp s U`.
- Added `rowSampleGramFpPerturbBudget_eq_nat_mul` and
  `rowSampleGramDotProductBudget_eq_nat_mul` in `RowSamplingGram.lean`, making
  explicit that the row-scaling and dot-product FP budgets include the Gram
  dimension factor `n` hidden in the type `A : Fin m → Fin n → ℝ`.

## 2026-05-25 RandNLA Algorithm 3 Preconditioning Work

- Added `Algorithms/RandNLA/Preconditioning.lean` and re-exported it through
  `Algorithms/RandNLA.lean`.
- Formalized the three explicit branches of Algorithm 3 from the CACM RandNLA
  paper: `preconditionRows` for `PiL * A`, `preconditionColumns` for
  `A * PiR`, and `preconditionElements` for `PiL * A * PiR`.
- Reused existing matrix multiplication infrastructure rather than proving a
  new local product theorem: the floating-point definitions
  `fl_preconditionRows`, `fl_preconditionColumns`, and
  `fl_preconditionElements` are built from `fl_matMul`.
- Main exact results:
  `preconditionRows_frobNorm_orthogonal`,
  `preconditionColumns_frobNorm_orthogonal`, and
  `preconditionElements_frobNorm_orthogonal`.
- Deterministic leverage-basis results added on 2026-05-31:
  `preconditionRows_hasOrthonormalColumns_of_orthogonal`,
  `preconditionColumns_hasOrthonormalColumns_of_orthogonal`,
  `preconditionElements_hasOrthonormalColumns_of_orthogonal`,
  `rowSqNormProbDen_preconditionRows_eq_nat_of_orthogonal`,
  `rowSqNormProbDen_preconditionColumns_eq_nat_of_orthogonal`, and
  `rowSqNormProbDen_preconditionElements_eq_nat_of_orthogonal`. These reuse
  the local equation (6) leverage-score basis and denominator theorem; they do
  not prove distribution-specific random-projection uniformization.
- SRHT deterministic route results added on 2026-05-31:
  `IsOrthogonal.diagMatrix_of_sq_eq_one`,
  `signedOrthogonalPreconditioner_isOrthogonal`,
  `signedOrthogonalPreconditionRows_hasOrthonormalColumns`, and
  `rowSqNormProbDen_signedOrthogonalPreconditionRows_eq_nat`.  These close the
  signed-diagonal/orthogonal prerequisite in the proof-source route through
  Tropp's 2011 SRHT row-norm lemma; the Rademacher/Hadamard row-norm
  concentration and finite union bound remain open.
- SRHT Rademacher sign-law route results added on 2026-05-31:
  `RademacherTrace`, `rademacherSign`, `rademacherSignVector`,
  `rademacherTraceProbability`, and
  `rademacherTraceProbability_eventProb_signedOrthogonalPreconditionRows_eq_one`.
  These define the uniform finite sign-vector law and prove the signed
  orthogonal preprocessing support event with probability one.  They do not
  prove Hadamard flatness, row-norm concentration, or maximum-leverage
  uniformization.
- SRHT Rademacher moment and flat-Hadamard expectation results added on
  2026-05-31: `rademacherTraceProbability_expectationReal_sign_eq_zero`,
  `rademacherTraceProbability_expectationReal_sign_mul_eq_ite`,
  `rademacherTraceProbability_expectationReal_sq_sum_mul_sign_eq_sum_sq`,
  `HadamardFlat`, `signedHadamardPreconditionRows_entry`, and
  `rademacherTraceProbability_expectationReal_rowNormSq_signedHadamard_eq`.
  These prove the finite sign moment algebra and the expectation identity
  `E ||(H D_omega U)_{i,*}||_2^2 = n/m` under `HadamardFlat H` and
  `UᵀU = I`.  This is still not the high-probability Tropp row-norm tail or
  maximum-leverage uniformization theorem.
- SRHT weak Markov/union row-norm auxiliary added on 2026-05-31:
  `rademacherTraceProbability_eventProb_rowNormSq_signedHadamard_le_ge_one_sub`,
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_sum`,
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub`,
  and
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_delta`.
  These reuse the local finite Markov inequality and finite union bound to
  prove an all-row high-probability threshold theorem from the expectation
  identity.  This is weaker than Tropp's SRHT row-norm concentration and does
  not close source-level Algorithm 3 random-projection uniformization.
- Main FP results:
  `fl_preconditionRows_error_bound`,
  `fl_preconditionColumns_error_bound`,
  `preconditionColumns_entry_error_bound_of_entrywise`, and
  `fl_preconditionElements_error_bound`.
- Scope note: the paper's random-projection uniformization discussion is
  distribution-specific and descriptive in the CACM survey. The formalized
  Algorithm 3 results are deterministic after the preprocessing matrices are
  drawn; no random-projection concentration theorem is claimed.

## 2026-05-25 Full RandNLA CACM Paper Audit

- Updated `docs/RANDNLA_CACM_NOT_PROVED_LEDGER.md` from a Section-7-only
  backlog into a full-paper algorithm/application inventory.
- Explicit algorithms in the CACM paper are Algorithm 1 element-wise sampling,
  Algorithm 2 row sampling, and Algorithm 3 random-projection preconditioning.
  Later sections also describe application-level algorithmic claims for least
  squares, low-rank approximation, matrix completion, and Laplacian solvers.
- Do not claim the full-paper final gate passes. Open paper-level foundations
  still include Algorithm 1 spectral concentration, matrix Bernstein/Khintchine,
  randomized LS embedding,
  Algorithm 3 distribution-specific uniformization, low-rank equation (9),
  matrix completion equations (10)--(11), and Laplacian/effective-resistance
  sparsification.
- New exact Algorithm 1 subtheorems from the full-paper audit:
  `sqMagTraceProbability_expectationReal_elementwiseTraceSketch_nonzero_entry`,
  `sqMagTraceProbability_expectationReal_elementwiseTraceSketch_zero_entry`,
  `sqMagTraceProbability_expectationReal_elementwiseTraceSketch_entry`, and
  `sqMagTraceProbability_expectationReal_elementwiseTraceSketch_matrix`
  prove support-inclusive unbiasedness under the canonical independent
  squared-magnitude trace law when `steps = s` and `(s : ℝ) ≠ 0`.
- Existing deterministic/probabilistic subtheorems remain valid but must stay
  separated from those open paper-level rows in PDFs, README, lookup docs, and
  final reports.
- 2026-05-25 full-paper gate rerun with the updated automation prompt searched
  local library and bundled mathlib for the remaining foundations. No matrix
  Bernstein/Khintchine, rectangular spectral random-matrix concentration,
  randomized LS embedding theorem, rectangular low-rank/SVD/pseudoinverse
  package, nuclear-norm matrix-completion machinery, or effective-resistance
  sparsification theorem was available to close an open paper-level row. Keep
  reporting the full-paper gate as FAIL while those ledger rows remain open.
- 2026-05-25 ledger-structure pass added
  `docs/RANDNLA_CACM_THEOREM_LEDGER.md` so the full-paper loop has a live
  theorem ledger separate from the not-proved backlog. It records extracted
  algorithms/equations, random variables, events, classifications, Lean theorem
  names, hypothesis classes, current status, and next proof step for each CACM
  RandNLA claim. The not-proved ledger remains the authoritative FAIL/PASS
  gate for open paper-level results.
- 2026-05-25 continuation-rule update: for full-paper or "prove every
  not-proved item" requests, a failed final gate is a checkpoint, not a stopping
  condition. If any requested paper-level row remains open, select the
  highest-leverage open row and continue with the next concrete Lean theorem or
  reusable foundation proof. Only return a "still open" report when the user
  asks for status/pause, a mathematical choice is genuinely required, or an
  external blocker prevents further local proof work.
- 2026-05-25 Algorithm 1 equation (2) continuation: added the residual
  increment foundation. `elementwiseTraceResidual_eq_sum_sampleResidualIncrement`
  proves the exact residual is a sum of one-sample increments when `steps = s`;
  `sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero`,
  `sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_eq_zero`,
  and the vector-action variants
  `sqMagProb_sum_rectMatMulVec_elementwiseSampleResidualIncrement_eq_zero` and
  `sqMagTraceProbability_expectationReal_rectMatMulVec_elementwiseTraceResidual_eq_zero`
  prove the corresponding mean-zero facts. This is not a spectral tail theorem;
  A1.5 now has self-adjoint dilation, trace-of-square, finite PSD/Loewner,
  trace monotonicity, squared-Loewner-to-operator adapters, and
  quadratic-form/Loewner/PSD/trace variance-proxy prerequisites, but still
  needs largest-eigenvalue/trace-exponential or Bernstein/Khintchine-style
  concentration.
- 2026-05-25 Algorithm 1 equation (2) continuation: added the variance-proxy
  layer for those increments. New proved support theorems include
  `sqMagProb_sum_elementwiseSampleContribution_entry_sq_le`,
  `sqMagProb_sum_elementwiseSampleResidualIncrement_entry_sq_le`,
  `sqMagProb_sum_elementwiseSampleResidualIncrement_frob_sq_le`,
  `sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le`,
  `sqMagTraceProbability_expectationReal_vecNorm2Sq_rectMatMulVec_elementwiseTraceResidual_le`,
  and
  `sqMagTraceProbability_eventProb_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub`.
  Also added the FP fixed-vector transfer
  `fl_elementwiseTraceResidual_vecNorm2_le_of_exact_fixed_vector` and
  probability corollary
  `sqMagTraceProbability_eventProb_fl_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub`.
  The finite-test-set support layer is
  `sqMagTraceProbability_eventProb_forall_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub_sum`
  and
  `sqMagTraceProbability_eventProb_forall_fl_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub_sum`.
  These are one-step/fixed-vector/finite-test second-moment and Markov support
  results, not the CACM equation (2) uniform spectral concentration theorem.
- 2026-05-26 Algorithm 1 source-alignment continuation: formalized the
  Drineas--Zouzias hard-thresholding layer instead of treating the truncated
  source theorem as if it proved the untruncated `A_ij^2 / ||A||_F^2` law. New
  public theorems include `elementwiseTruncate`,
  `elementwiseTruncate_square_error_frobNormRect_le_half`,
  `elementwiseTruncate_square_error_rectOpNorm2Le_half`,
  `elementwiseTruncatedTraceResidual_square_rectOpNorm2Le_of_half`,
  `probability_algorithm1_exact_truncated_spectral_of_sampled_half`,
  `fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated`, and
  `probability_algorithm1_fl_truncated_spectral_of_sampled_half`. These prove
  deterministic truncation cost and exact/FP transfer from a future half-budget
  theorem for sampling `\hat A`; they still do not prove the matrix-Bernstein
  half-budget event or close the untruncated equation (2) target.
- 2026-05-26 Algorithm 1 matrix-Bernstein prerequisite continuation: added
  product-law support and bounded-increment infrastructure for the truncated
  route. New public theorems include `entry_ne_zero_of_sqMagProb_pos`,
  `elementwiseTracePositiveProb`,
  `sqMagTraceProbability_eventProb_elementwiseTracePositiveProb`,
  `frobNormRect_elementwiseTruncate_le`,
  `frobNormRect_elementwiseSampleContribution_truncated_le`,
  `frobNormRect_elementwiseSampleResidualIncrement_truncated_le`,
  `rectOpNorm2Le_elementwiseSampleResidualIncrement_truncated`,
  `sqMagTraceProbability_eventProb_truncatedResidualIncrementsBoundedEvent_eq_one`,
  `finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated`,
  and
  `sqMagTraceProbability_eventProb_truncatedDilationIncrementsBoundedEvent_eq_one`,
  plus the squared-Loewner versions
  `finiteLoewnerLe_rectSelfAdjointDilation_square_elementwiseSampleResidualIncrement_truncated`
  and
  `sqMagTraceProbability_eventProb_truncatedDilationIncrementSquaresBoundedEvent_eq_one`.
  These discharge support, bounded-matrix, and bounded-square side conditions
  only; the trace-exponential/largest-eigenvalue Bernstein tail remains open.
- 2026-05-26 tightened the same truncated Bernstein side-condition layer with
  two-sided Loewner boundedness.  Generic matrix algebra now includes
  `finiteLoewnerLe_smul_id_of_finiteOpNorm2Le` and
  `finiteLoewnerLe_neg_smul_id_of_finiteOpNorm2Le`; the truncated Algorithm 1
  route now exposes
  `finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated`,
  `finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated`,
  `truncatedDilationIncrementLoewnerBoundedEvent`, and
  `sqMagTraceProbability_eventProb_truncatedDilationIncrementLoewnerBoundedEvent_eq_one`.
  The simultaneous `truncatedDilationBernsteinBoundedEvent` now packages
  bounded-operator, two-sided Loewner, and squared-Loewner side conditions with
  probability one.  This is still prerequisite infrastructure, not the
  trace-MGF domination theorem.
- 2026-05-26 added the deterministic scalar-CGF-to-trace-exponential step for
  the trace-MGF route.  `MatrixSpectral.lean` now proves
  `finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq`,
  `finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one`,
  `finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id`,
  `finiteTrace_finiteMatrixExp_le_card_mul_exp_of_finiteLoewnerLe_smul_id`,
  and
  `finiteTrace_finiteMatrixExp_neg_le_card_mul_exp_of_neg_finiteLoewnerLe_smul_id`.
  These turn a future scalar-identity Loewner matrix-CGF estimate into
  `tr(exp(M)) <= d exp(c)` and `tr(exp(-M)) <= d exp(c)`.  They still do not
  prove Golden-Thompson/Lieb trace domination or matrix Bernstein.

- 2026-05-26 continued the Algorithm 1 equation (2) concentration queue by
  adding the product-law expectation bridge.  `HitCountConcentration.lean` now
  has `sqMagTraceProbability_expectationReal_step_eq`, a generic adapter from
  one-step `sqMagProb` sums to expectations of a fixed coordinate in the
  independent trace law.  `ElementwiseSpectral.lean` uses it to prove
  trace-law zero mean for one-step dilation increments and the full dilation
  residual, plus product-law expected quadratic-form, Loewner, and PSD variance
  bounds:
  `sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_elementwiseTraceResidual_eq_zero`,
  `sqMagTraceProbability_expectationReal_sum_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le`,
  `sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_loewnerLe_scalar_id`,
  and
  `sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_psd`.
  These close the expectation/variance packaging gap but not the
  trace-exponential/largest-eigenvalue Bernstein tail.
- 2026-05-26 also added
  `FiniteProbability.eventProb_inter_eq_one_of_eq_one` and the truncated
  simultaneous Bernstein side-condition package
  `truncatedDilationBernsteinBoundedEvent` with probability-one theorem
  `sqMagTraceProbability_eventProb_truncatedDilationBernsteinBoundedEvent_eq_one`.
  This now combines the bounded-dilation, two-sided Loewner, and bounded-square
  events; it remains prerequisite infrastructure only.

## 2026-04-26 Fix Pass

- Created and used branch `codex/library-integrity-fixes`.
- Replaced the explicit Method 1B block-inversion placeholders with a meaningful
  `BlockMethod1BSpec` containing `block_count_le_dim`,
  `lower_triangular_inverse`, and `column_backward_error`.
- Added `triInv_method1B_right_residual_from_spec`, which derives the Method 1B
  residual from the new spec using the existing per-column residual proof.
- Redocumented abstract high-level interfaces in `MatrixInversion`,
  `GaussJordan`, Cholesky chapter modules, and Sylvester perturbation so their
  hypothesis status is explicit.
- Corrected the `MMatrix` Corollary 8.10 documentation and README theorem name
  (`mmatrix_forwardSub_relative_error`, not `corollary_8_10`).
- Removed a misleading prose false-positive for `admit` in the SPD docstring of
  `LU/GaussianElimination.lean`.
- Validation after edits: `lake build` completed successfully; scans found no
  Lean `sorry`/`admit`/`axiom`/`opaque` tokens and no explicit `True`
  placeholder block specs or stale “full Corollary 8.10 future work” claims.
  The remaining build warnings are the pre-existing linter warnings in
  QR/least-squares/fast-matmul modules.

## 2026-05-26 RandNLA Full-Paper Continuation Note

- Continued the Algorithm 1 equation (2) concentration queue by adding generic
  product-law scalar MGF infrastructure in
  `HitCountConcentration.lean`: `exp_sum_stepFunction_eq_prod`,
  `sqMagTraceProbMass_exp_sum_stepFunction_eq`,
  `sqMagTraceProbability_expectationReal_exp_sum_stepFunction_eq`,
  `sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_mul_mgf`, and
  `sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_mul_mgf`,
  plus the one-step-MGF-bound variants
  `sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_of_one_step_mgf_bound`
  and
  `sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_of_one_step_mgf_bound`.
- These theorems factor the MGF of `sum_t f(X_t)` under the independent
  squared-magnitude trace law and provide scalar exponential-Markov tails.
  They are support infrastructure only: they do not prove trace-exponential
  domination, largest-eigenvalue tails, matrix Bernstein/Khintchine, or CACM
  equation (2).
- The same continuation added finite-family scalar MGF support and specialized
  it to self-adjoint-dilation quadratic forms:
  `sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_one_step_mgf_bound`,
  `finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement`,
  and
  `sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_one_step_mgf_bound`.
  These are finite-test support theorems only and still leave matrix
  Bernstein/equation (2) open.
- Added pointwise-bound variants
  `sqMagProb_sum_exp_stepFunction_le_exp_of_forall_le`,
  `sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_pointwise_bound`,
  and
  `sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_pointwise_bound`.
  These remove explicit one-step MGF hypotheses when a pointwise statistic
  bound is available, but they are still weak finite-test support and not
  matrix Bernstein.
- Added support-aware pointwise variants
  `sqMagProb_sum_exp_stepFunction_le_exp_of_support_forall_le`,
  `sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_support_pointwise_bound`,
  and
  `sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_support_pointwise_bound`.
  These only require the one-step pointwise bound on positive-probability
  samples, which avoids hidden retained-entry hypotheses for truncated
  sampling laws.
- Added matrix-algebra adapters
  `abs_finiteQuadraticForm_le_of_finiteOpNorm2Le` and
  `finiteQuadraticForm_le_of_finiteOpNorm2Le`, exposing the existing
  operator-to-inner-product control directly in `finiteQuadraticForm`
  notation for future pointwise MGF bounds.
- Specialized the support-aware MGF support to the Drineas--Zouzias truncated
  Algorithm 1 route with
  `finiteQuadraticForm_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_le`
  and
  `sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_truncatedTraceResidual_le_ge_one_sub_sum_exp_of_support_bound`.
  This closes the zero-mass support bookkeeping for finite test vectors, but
  still does not prove trace-exponential/largest-eigenvalue or matrix
  Bernstein concentration.
- Added a one-sided self-adjoint-dilation Loewner adapter:
  `rectOpNorm2Le_of_selfAdjointDilation_loewnerLe_scalar_id`,
  `algorithm1ExactDilationUpperEvent_subset_exactSpectralEvent`,
  `probability_algorithm1_exact_spectral_of_dilation_upper`, and
  `probability_algorithm1_fl_spectral_of_exact_dilation_upper`.
  This lets a future largest-eigenvalue theorem proving `D(R) <= eps I`
  transfer to exact/FP rectangular residual events, but it is still only a
  deterministic/probability bridge and does not prove equation (2).
- Added a named eigenvalue form of that dilation upper event:
  `finiteScalarUpperDiffEigenvalues`,
  `finiteLoewnerLe_smul_id_iff_finiteScalarUpperDiffEigenvalues_nonneg`,
  `algorithm1ExactDilationEigenUpperEvent`,
  `algorithm1ExactDilationEigenUpperEvent_subset_exactDilationUpperEvent`,
  `algorithm1ExactDilationEigenUpperEvent_subset_exactSpectralEvent`,
  `probability_algorithm1_exact_spectral_of_dilation_eigen_upper`, and
  `probability_algorithm1_fl_spectral_of_exact_dilation_eigen_upper`.
  This exposes the future largest-eigenvalue tail target as nonnegativity of
  all eigenvalues of `eps I - D(R)`, but still does not prove that event with
  high probability.
- Added a finite union-bound adapter for supplied scalar eigenvalue events:
  `algorithm1ExactDilationEigenUpperIndexEvent`,
  `probability_algorithm1_exact_dilation_eigen_upper_of_index_bounds`,
  `probability_algorithm1_exact_spectral_of_dilation_eigen_upper_index_bounds`,
  and
  `probability_algorithm1_fl_spectral_of_exact_dilation_eigen_upper_index_bounds`.
  This is only a probability combiner for per-eigenvalue bounds; it still does
  not prove those bounds or a trace-exponential/largest-eigenvalue theorem.
- Added the matrix-exponential scalar-normalization bridge in
  `LeanFpAnalysis/FP/Analysis/MatrixSpectral.lean`:
  `finiteMatrixExp`, `finiteMatrixExp_smul_finiteIdMatrix`, and
  `finiteTrace_finiteMatrixExp_smul_finiteIdMatrix`, plus symmetry
  preservation `finiteMatrixExp_symmetric`. `MatrixAlgebra.lean` now has
  `finiteDiagonal`, and `MatrixSpectral.lean` proves
  `finiteMatrixExp_finiteDiagonal` and
  `finiteTrace_finiteMatrixExp_finiteDiagonal`.
  These provide the `tr(exp(L I)) = d exp(L)` and diagonal trace-exponential
  normalizations needed by a future trace-MGF proof, but they do not prove
  trace-exponential domination, matrix Bernstein/Khintchine, or CACM
  equation (2).
- Added the Hermitian spectral-calculus trace bridge in
  `LeanFpAnalysis/FP/Analysis/MatrixSpectral.lean`: `finiteHermitianCfcExp`
  and `finiteTrace_finiteHermitianCfcExp_eq_sum_exp_finiteHermitianEigenvalues`.
  This proves `tr(E_cfc(M)) = sum_i exp(lambda_i(M))` for local finite real
  symmetric matrices. The same file now also proves
  `finiteTrace_finiteMatrixExp_eq_sum_exp_finiteHermitianEigenvalues`, the
  repository-native power-series matrix-exponential trace identity
  `tr(exp(M)) = sum_i exp(lambda_i(M))` for local finite real symmetric
  matrices. This closes the trace-diagonalization dependency, but
  trace-exponential domination, largest-eigenvalue tails,
  matrix Bernstein/Khintchine, and CACM equation (2) remain open.
- Added `LeanFpAnalysis/FP/Analysis/MatrixConcentration.lean` with
  `exp_le_finiteTrace_finiteMatrixExp_of_finiteHermitianEigenvalue_ge`,
  `finiteTrace_finiteMatrixExp_nonneg`, and
  `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_expected_trace_exp`.
  This closes the MGF-to-eigenvalue Markov interface for a supplied random
  symmetric matrix family. It still requires a trace-MGF domination theorem for
  independent self-adjoint sums before matrix Bernstein/Khintchine or CACM
  equation (2) can close.
- Extended `MatrixConcentration.lean` with scalar-bound and high-probability
  complement forms:
  `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_trace_bound`,
  `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp`,
  and
  `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound`.
  These make a future trace-MGF bound immediately usable as an eigenvalue
  tail or all-eigenvalues-below-threshold probability statement, but they still
  do not prove trace-MGF domination, matrix Bernstein/Khintchine, or CACM
  equation (2).
- Added the lower-tail companion for the trace-exponential/eigenvalue layer:
  `finiteTrace_finiteMatrixExp_neg_eq_sum_exp_neg_finiteHermitianEigenvalues`,
  `exp_neg_le_finiteTrace_finiteMatrixExp_neg_of_finiteHermitianEigenvalue_le`,
  `finiteTrace_finiteMatrixExp_neg_nonneg`,
  `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_expected_trace_exp_neg`,
  `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_trace_bound`,
  `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_expected_trace_exp_neg`,
  and
  `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_trace_bound`.
  These close the negative one-sided Markov interface for future two-sided
  self-adjoint concentration, but still leave trace-MGF domination,
  matrix Bernstein/Khintchine, and CACM equation (2) open.
- Added the two-sided trace-exponential/eigenvalue combiner
  `FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp_add`
  and
  `FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound_add`.
  These combine positive and negative trace-MGF controls into an
  all-absolute-eigenvalues-below-threshold event, using existing finite
  probability intersection infrastructure. They still do not prove the
  trace-MGF controls themselves, matrix Bernstein/Khintchine, or CACM
  equation (2).
- Added the weak accumulated bounded-increment theorem for the truncated
  Algorithm 1 route:
  `truncatedDilationIncrementLoewnerBoundedEvent_subset_exactDilationUpperEvent_sum_bound`,
  `sqMagTraceProbability_eventProb_algorithm1ExactDilationUpperEvent_truncated_sum_bound_eq_one`,
  and
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncated_sum_bound_eq_one`.
  This proves the probability-one two-sided Loewner bounded-increment event
  composes to a probability-one exact truncated spectral event at scale `sL`.
  It is an audit/side-condition theorem only: it ignores zero mean and
  variance, so it does not prove the CACM equation (2) Bernstein rate.
- Added `Analysis/OperatorLog.lean` with `cstarMatrix_log_le_log`, a local
  wrapper around mathlib operator-log monotonicity for complex `CStarMatrix`.
  This closes one Tropp/Lieb functional-calculus prerequisite for the
  trace-MGF route, but it does not bridge finite real self-adjoint matrices to
  complex C-star matrix order and does not prove trace-MGF domination.
- Added `Analysis/CStarMatrixBridge.lean` with `finiteComplexCStarMatrix` and
  preservation lemmas for entries, subtraction, the finite identity, scalar
  identities, self-adjointness of symmetric finite real matrices, local PSD,
  and local finite Loewner inequalities into complex C-star spectral order.
  It now also proves strict positivity after positive scalar identity
  regularization and preservation of Loewner inequalities under the same
  regularization. `OperatorLog.lean` composes these with
  `cstarMatrix_log_le_log` as
  `finiteComplexCStarMatrix_regularized_log_le_log_of_finiteLoewnerLe`.
  This closes the algebraic/order/strict-positive-regularization part of the
  finite-real-to-complex-C-star bridge; Lieb/Tropp trace-MGF domination remains
  open.
- Added `Analysis/CStarMatrixTrace.lean` with `cstarMatrixTrace`, elementary
  additivity/scaling/subtraction/identity rules, cyclicity
  `cstarMatrixTrace_mul_comm`, real-part trace positivity/monotonicity for the
  C-star spectral order via `cstarMatrixTrace_re_nonneg_of_nonneg` and
  `cstarMatrixTrace_re_mono`, agreement with repository-native `finiteTrace`
  after embedding finite real matrices, and embedded real PSD/Loewner trace
  transfer lemmas.  It also proves scalar CFC-exponential trace
  normalization for complex and real scalar identities via
  `cstarMatrixTrace_cfc_exp_algebraMap` and
  `cstarMatrixTrace_cfc_exp_real_smul_one`.  This closes trace vocabulary for
  the Tropp/Lieb route, but it does not prove Lieb trace concavity, trace-MGF
  domination, matrix Bernstein/Khintchine, or CACM equation (2).
- Added `Analysis/CStarMatrixExpectation.lean` with
  `FiniteProbability.expectationComplex`,
  `FiniteProbability.expectationCStarMatrix`, complex linearity lemmas,
  `FiniteProbability.cstarMatrixTrace_expectationCStarMatrix`, and
  `FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix`.  It
  now also proves `FiniteProbability.expectationCStarMatrix_eq_sum_smul`,
  `FiniteProbability.expectationCStarMatrix_eq_sum_real_smul`,
  `FiniteProbability.expectationComplex_re`,
  `FiniteProbability.expectationCStarMatrix_nonneg`,
  `FiniteProbability.expectationCStarMatrix_mono`, and
  `FiniteProbability.expectationCStarMatrix_add_pos_smul_one_isStrictlyPositive`.
  Together with the finite probability Jensen wrapper
  `FiniteProbability.expectationReal_le_of_concaveOn` and its C-star
  specialization
  `FiniteProbability.expectationReal_le_of_concaveOn_expectationCStarMatrix`,
  plus the conditional trace-exponential shape
  `FiniteProbability.expectationReal_trace_cfc_exp_add_log_le_of_concaveOn`,
  this closes the finite Jensen/expectation adapter needed after a future proof
  of Lieb trace concavity. The concavity hypothesis remains explicit and
  unproved locally. It is not trace-MGF domination, matrix Bernstein/Khintchine,
  or CACM equation (2).
  A follow-up locality pass confirmed that mathlib currently has
  `CFC.log_monotoneOn`, but `ExpLog.Order` still lists operator-log concavity
  as TODO and `Rpow.Order` lists operator concavity of `rpow` as TODO. The next
  proof frontier is therefore a genuine Lieb trace-concavity theorem or a
  deliberate route switch, not another local wrapper.
- Continued the Algorithm 1 equation (2) bottleneck by closing a covering-route
  dependency in `MatrixAlgebra.lean`: `abs_coord_le_vecNorm2`,
  `realUnitIntervalCover`, `rectUnitBallCover_product_grid`, and
  `fintype_card_product_grid_index`.  A one-dimensional interval grid for
  `[-1,1]` now induces an `n`-dimensional Euclidean unit-ball cover with radius
  loss `sqrt n`, and the product index type has cardinality `|grid|^n`.  This
  is deterministic cover geometry only; it does not prove sharp finite-net
  tails, matrix Bernstein/Khintchine, Lieb trace-MGF domination, or CACM
  equation (2).
- Updated the formalization automation workflow and the installed
  `lean-stability-formalizer` skill so incomplete paper proofs trigger a
  front-loaded proof-source acquisition phase before hard Lean proof work.
  Future runs must classify source proofs, search primary literature and
  citation chains, create a proof-source ledger with exact theorem/page/equation
  references and Lean targets, choose a route, and only then formalize. The
  exported Vershynin chapter skill was updated the same way and its archive was
  regenerated.
- Started the updated proof-source workflow for the CACM RandNLA paper by
  adding `docs/RANDNLA_CACM_PROOF_SOURCE_LEDGER.md`. The active Algorithm 1
  equation (2) bottleneck is now explicitly sourced through CACM ->
  Drineas--Zouzias Algorithm 1/Theorem 1/Lemmas 1--4 -> matrix-valued
  Bernstein -> Tropp Lieb/trace-MGF/matrix-Bernstein. Other open paper-level
  rows now have source queues before new infrastructure should be added.
- Added `LeanFpAnalysis/FP/Analysis/LiebTrace.lean` for the Algorithm 1
  equation (2) Tropp/Lieb route. It defines the strictly-positive complex
  `CStarMatrix` cone, proves positive/nonnegative real-scalar preservation and
  `strictPositiveCStarMatrixCone_convex`, and names `liebTraceFunctional` plus
  `liebTraceConcavityTarget`. This closes the domain-convexity/target-vocabulary
  dependency only; Lieb trace concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, and CACM equation (2) remain open.
- Continued the active A1.5-B1 red-bottleneck pass by closing the local
  trace-exponential real-valuedness/positivity bridge: `cstarMatrixTrace_im_eq_zero_of_isSelfAdjoint`,
  `liebTraceCfcExp_nonneg`, `liebTraceFunctional_trace_im_eq_zero`, and
  `liebTraceFunctional_nonneg`. These are listed dependencies for the
  Tropp/Lieb route. They do not prove finite-dimensional Lieb concavity,
  trace-MGF domination, matrix Bernstein/Khintchine, or CACM equation (2).
- Tightened the automation workflow and installed `lean-stability-formalizer`
  skill after the Algorithm 1 equation (2) bottleneck exposed a process failure.
  Future runs must run a foundation feasibility gate before downstream theorem
  work. If a paper-level theorem depends on an unproved foundation, that
  foundation becomes the active Lean target. If the same row survives two
  focused passes with the same missing foundation, it becomes a red bottleneck:
  downstream adapters, transfer corollaries, PDF polish, and lookup prose no
  longer count as progress unless they close a listed dependency, rule out a
  listed route, or correct the theorem statement. The repository prompt playbook
  and exported Vershynin chapter skill now include this rule.
- Continued the active A1.5-B1 red-bottleneck pass by closing the
  log-exponential analytic bridge in `OperatorLog.lean`:
  `cstarMatrix_normedSpaceExp_isTopologicalRing`,
  `cstarMatrix_normedRingExp_isTopologicalRing`,
  `cstarMatrix_realContinuousFunctionalCalculus`,
  `cstarMatrix_log_normedSpace_exp_of_isSelfAdjoint`,
  `cstarMatrix_log_cfc_complex_exp_of_isSelfAdjoint`, and
  `cstarMatrix_log_cfc_real_exp_of_isSelfAdjoint`. These are deterministic
  C-star functional-calculus dependencies for the Tropp/Lieb route. They do not
  prove finite-dimensional Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Continued the active A1.5-B1 red-bottleneck pass by closing the matching
  strictly-positive exponential-logarithm analytic bridge in `OperatorLog.lean`:
  `cstarMatrix_normedRingExp_nonnegSpectrumClass`,
  `cstarMatrix_normedSpace_exp_log_of_isStrictlyPositive`,
  `cstarMatrix_cfc_complex_exp_log_of_isStrictlyPositive`, and
  `cstarMatrix_cfc_real_exp_log_of_isStrictlyPositive`. These are
  deterministic C-star functional-calculus inverse dependencies for the
  Tropp/Lieb route. They do not prove finite-dimensional Lieb concavity,
  trace-MGF domination, matrix Bernstein/Khintchine, or CACM equation (2).
- Continued the active A1.5-B1 red-bottleneck pass by closing the local
  Lieb-functional normalization bridge in `LiebTrace.lean`:
  `liebTraceFunctional_eq_normedSpace_exp` identifies the CFC form of the local
  Lieb functional with the standard normed-algebra exponential
  `Re tr(exp(H + log A))`, and `liebTraceFunctional_zero_eq_trace` normalizes
  the `H = 0` case to `Re tr(A)` on the strictly positive cone. These are
  deterministic C-star functional-calculus/trace dependencies only. They do
  not prove finite-dimensional Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Closed one sanity-check subcase of the Lieb target with
  `liebTraceConcavityTarget_zero`: for `H = 0`, the local Lieb functional is
  affine on the strictly positive cone, hence concave. This reduces the red
  bottleneck but does not prove the arbitrary self-adjoint-`H` Lieb theorem,
  trace-MGF domination, matrix Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing a finite-support
  strict-positivity domain dependency:
  `FiniteProbability.exists_prob_pos` and
  `FiniteProbability.expectationCStarMatrix_isStrictlyPositive`. This shows
  that finite C-star expectations preserve strict positivity when every sampled
  matrix is strictly positive, which is needed before future `log(E[exp X])`
  statements. It does not by itself prove strict positivity of matrix
  exponentials; that separate domain bridge is closed in the next bullet. It
  does not prove Lieb trace concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the self-adjoint
  matrix-exponential strict-positivity bridge:
  `cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint`,
  `cstarMatrix_cfc_complex_exp_isStrictlyPositive_of_isSelfAdjoint`,
  `cstarMatrix_cfc_real_exp_isStrictlyPositive_of_isSelfAdjoint`, and
  `liebTraceCfcExp_isStrictlyPositive`. This combines self-adjoint exponential
  nonnegativity with invertibility of the normed-algebra exponential and
  transfers the result to the CFC exponentials. It does not prove arbitrary
  self-adjoint-`H` Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the conditional
  one-step Tropp/Jensen trace-MGF adapter:
  `FiniteProbability.expectationReal_trace_normed_exp_add_le_of_liebTraceConcavityTarget`.
  It proves `E Re tr exp(H + X) <= Re tr exp(H + log(E exp X))` for finite
  self-adjoint C-star matrix random variables from the explicit hypothesis
  `liebTraceConcavityTarget H`, using the local finite Jensen adapter plus
  `log(exp X)=X` and CFC-to-normed-exponential normalization. It does not prove
  arbitrary self-adjoint-`H` Lieb concavity, nonconditional trace-MGF
  domination, matrix Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the first
  relative-entropy route dependency for the chosen Tropp monograph path:
  `cstarMatrixRelativeEntropy` and `cstarMatrixRelativeEntropy_self`.
  This names the finite complex C-star relative-entropy expression and proves
  the diagonal normalization `D(A;A)=0`. It does not prove matrix
  relative-entropy nonnegativity, joint convexity, the variational principle,
  arbitrary self-adjoint-`H` Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the commutative
  relative-entropy nonnegativity dependency:
  `realRelativeEntropy_nonneg` proves
  `a * (log a - log b) - (a - b) >= 0` for positive real scalars, and
  `finiteRealRelativeEntropy_nonneg` sums it over coordinatewise-positive
  finite vectors. This does not prove matrix relative-entropy nonnegativity,
  joint convexity, the variational principle, arbitrary self-adjoint-`H` Lieb
  concavity, trace-MGF domination, matrix Bernstein/Khintchine, or CACM
  equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the real
  scalar-identity matrix relative-entropy case:
  `cstarMatrixRelativeEntropy_algebraMap_real` proves
  `D(aI;bI) = dim * d(a;b)`, and
  `cstarMatrixRelativeEntropy_algebraMap_real_nonneg` proves nonnegativity for
  positive real scalars. This is a C-star matrix vocabulary sanity theorem
  only; it does not prove general matrix relative-entropy nonnegativity, joint
  convexity, the variational principle, arbitrary self-adjoint-`H` Lieb
  concavity, trace-MGF domination, matrix Bernstein/Khintchine, or CACM
  equation (2).
- A 2026-05-27 route-elimination pass for A1.5-B1 searched the repository,
  lookup files, and mathlib for Klein inequality, quantum/matrix
  relative-entropy joint convexity, arbitrary-`H` Lieb trace concavity, and
  matrix Bernstein. No reusable local theorem was found. Mathlib has scalar
  `convexOn_mul_log`, but its CFC order files still list operator-log
  concavity and operator convexity of `x * log x` as TODOs.
- Continued the A1.5-B1 red-bottleneck pass by closing the real diagonal
  matrix relative-entropy case:
  `cstarMatrixDiagonalStarAlgHom`,
  `cstarMatrixDiagonalStarAlgHom_continuous`, `cstarMatrixRealDiagonal`,
  `cstarMatrixTrace_realDiagonal`, `cstarMatrix_log_realDiagonal`,
  `cstarMatrixRelativeEntropy_realDiagonal`, and
  `cstarMatrixRelativeEntropy_realDiagonal_nonneg`. This proves that the
  diagonal C-star embedding is continuous, that nonzero real diagonal matrices
  have coordinatewise operator logarithms, and that C-star matrix relative
  entropy on real diagonal matrices reduces to finite-vector relative entropy.
  It does not prove general noncommutative matrix relative-entropy
  nonnegativity, joint convexity, the variational principle, arbitrary
  self-adjoint-`H` Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the conditional
  Tropp relative-entropy route reduction:
  `cstarMatrixEntropyVariationalObjective`,
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`,
  `cstarMatrixEntropyVariationalFormula`, and
  `liebTraceConcavityTarget_of_relativeEntropy_route`. A follow-up statement
  correction fixed the variational objective to include the `Re tr A` constant
  required by the local normalization
  `D(X;A)=Re tr(X(log X-log A)-(X-A))`. The same pass closed
  `cstarMatrixEntropyVariationalObjective_liebOptimizer`, the equality
  \(\Psi_H(\exp(H+\log A),A)=\Phi_H(A)\) for the normalized objective, and
  `cstarMatrixEntropyVariationalFormula_of_relativeEntropy_nonneg`, which
  reduces the normalized variational formula to
  `cstarMatrixRelativeEntropyNonnegOnStrictPositive`. This proves that joint
  convexity of local C-star matrix relative entropy on the strictly positive
  cone plus the normalized entropy variational formula imply the local Lieb
  trace-concavity target. It does not prove noncommutative relative-entropy
  nonnegativity or joint convexity, nonconditional trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2); those are the next named
  foundations for this route.
- Continued the A1.5-B1 red-bottleneck pass by splitting the nonnegativity
  foundation further using the proof-source chain from Tropp's matrix
  concentration notes and 2012 relative-entropy/Lieb note.
  `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive` now names the
  generalized Klein first-order trace inequality for
  `Phi(X)=Re tr(X log X - X)`, and
  `cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder`
  proves that this first-order trace inequality implies local C-star matrix
  relative-entropy nonnegativity. This is a source-aligned conditional
  reduction only: the generalized Klein first-order trace inequality and
  matrix relative-entropy joint convexity remain open, followed by
  nonconditional trace-MGF domination, matrix Bernstein/Khintchine, and CACM
  equation (2).
- Continued the same bottleneck with two source-aligned dependencies from
  Tropp Proposition 8.3.5. First,
  `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_relativeEntropy_nonneg`
  and
  `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_iff_relativeEntropy_nonneg`
  show that local generalized Klein first-order convexity and local
  relative-entropy nonnegativity are equivalent in the repository
  normalization. Second, the Hermitian spectral-overlap route is now local:
  `matrixTrace_diagonal_mul_mul_diagonal_mul_star`,
  `matrixTrace_sum_diagonal_mul_mul_diagonal_mul_star_re`,
  `matrixTrace_sum_hermitianCfc_mul_cfc_re`,
  `matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_kernel_nonneg`,
  `matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_eigen_kernel_nonneg`,
  `matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg`,
  `matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg_of_eigen`,
  `realEntropy_firstOrderKernel_nonneg`, and
  `matrixTrace_hermitianCfc_entropy_firstOrder_sum_nonneg` close the
  squared-overlap algebra and the positive-spectrum scalar entropy
  first-order specialization. The compact complex `CStarMatrix` logarithm
  bridge, relative-entropy joint convexity, Lieb concavity, trace-MGF
  domination, matrix Bernstein/Khintchine, and CACM equation (2) remain open.
- Continued A1.5-B1 by closing the compact Hermitian/C-star generalized Klein
  bridge. `matrixTrace_hermitianCfc_entropy_firstOrder_compact_nonneg`,
  `cstarMatrix_nonneg_to_matrix_posSemidef`,
  `cstarMatrix_isStrictlyPositive_to_matrix_posDef`,
  `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_hermitianCfc`,
  `cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_hermitianCfc`,
  `cstarMatrixEntropyVariationalFormula_of_hermitianCfc`, and
  `liebTraceConcavityTarget_of_relativeEntropy_jointConvex` now close
  generalized Klein, local relative-entropy nonnegativity, the normalized
  variational formula, and the reduction from joint convexity alone to the
  local Lieb target. The current A1.5-B1 frontier is
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, followed by
  nonconditional trace-MGF domination, matrix Bernstein/Khintchine, and CACM
  equation (2).
- Front-loaded source search for the next A1.5-B1 frontier identified
  Effros 2009 (matrix perspectives of operator convex functions) and Lindblad
  1975 (relative-entropy convexity/monotonicity lineage) as advisory primary
  sources for `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, in
  addition to Tropp's monograph Sections 8.6--8.8 and Tropp's 2012 note. These
  sources are recorded in the proof-source/theorem ledgers and are not used as
  Lean hypotheses.
- Continued A1.5-B1 by closing the commutative joint-convexity layer on the
  same Tropp/Effros route. `finite_log_sum_inequality` is now proved from
  mathlib's scalar convexity of `x * log x`; it feeds
  `realRelativeEntropy_jointConvex_of_pos_weights`,
  `realRelativeEntropy_jointConvex`, and
  `finiteRealRelativeEntropy_jointConvex`. The diagonal C-star bridge
  `cstarMatrixRealDiagonal_smul_add`, `positive_weighted_sum_pos`, and
  `cstarMatrixRelativeEntropy_realDiagonal_jointConvex` close the real
  diagonal subalgebra case. This is a route dependency/sanity subcase only:
  the current A1.5-B1 frontier remains the noncommutative theorem
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, followed by
  trace-MGF domination, matrix Bernstein/Khintchine, and CACM equation (2).
- 2026-05-27: A1.5-B1 Effros/Tropp perspective substrate advanced again.
  `LiebTrace.lean` now defines `cstarMatrixLeftMul` and
  `cstarMatrixRightMul`, proves their real weighted-sum affine laws, proves
  `cstarMatrixLeftRightMul_commute`, and proves left/right multiplication is
  a unit when the underlying matrix is a unit or strictly positive. This
  closes the algebraic \(L_A\), \(R_A\) layer needed before constructing
  \(L_X R_A^{-1}\); it still does not prove operator convexity, the perspective
  theorem, `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, Lieb
  concavity, trace-MGF domination, matrix Bernstein/Khintchine, or equation
  (2).
- 2026-05-27: A1.5-B1 Effros/Tropp perspective substrate advanced one step
  further. `LiebTrace.lean` now defines `cstarMatrixLeftRightRatio` for
  \(L_XR_A^{-1}\), proves its action formula, and proves the base-point
  normalization \((L_XR_A^{-1})(A)=X\) for unit and strictly positive `A`.
  This closes the explicit ratio-endomorphism layer only; the open frontier
  remains the finite operator-perspective theorem or relative-entropy trace
  representation, then `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.
- 2026-05-27: A1.5-B1 Effros/Tropp perspective substrate added the
  product/power algebra for the left/right multiplication endomorphisms:
  `cstarMatrixLeftMul_mul`, `cstarMatrixRightMul_mul`,
  `cstarMatrixLeftMul_pow`, and `cstarMatrixRightMul_pow`. This supports the
  future functional-calculus/trace-representation step for \(L_XR_A^{-1}\);
  it still does not prove the Effros perspective theorem or joint convexity.
- 2026-05-27: A1.5-B1 Effros/Tropp perspective substrate added the finite
  Kronecker lift layer: `matrix_kronecker_left_identity_real_smul_add`,
  `matrix_kronecker_right_identity_real_smul_add`,
  `matrix_kronecker_left_identity_mul_right_identity`,
  `matrix_kronecker_right_identity_mul_left_identity`,
  `matrix_kronecker_left_right_commute`,
  `matrix_kronecker_posDef_left_identity`, and
  `matrix_kronecker_posDef_right_identity`. This closes the affine,
  commutation, product, and positive-definiteness facts for \(A\otimes I\)
  and \(I\otimes H\); it still does not prove operator convexity, the Effros
  perspective theorem, relative-entropy joint convexity, Lieb concavity, or
  equation (2).
- 2026-05-27: A1.5-B1 Effros/Tropp perspective substrate added the finite
  Kronecker trace layer: `matrix_trace_kronecker`,
  `matrix_trace_kronecker_left_identity`, and
  `matrix_trace_kronecker_right_identity`. This closes
  \(\operatorname{tr}(A\otimes H)=\operatorname{tr}(A)\operatorname{tr}(H)\)
  plus identity-lift trace normalizations for the future trace-representation
  proof; it still does not prove operator convexity, the Effros perspective
  theorem, the representation itself, relative-entropy joint convexity, Lieb
  concavity, or equation (2).
- 2026-05-27: A1.5-B1 Hansen-Pedersen/Effros source route now has explicit
  Lean target names: `cstarMatrixHansenPedersenJensenTwoPointTarget`,
  `cstarMatrixHansenPedersenJensenTwoPointTarget_id`, and
  `cstarMatrixXLogXHansenPedersenJensenTarget`. The identity-function Jensen
  sanity case is proved; the nonlinear \(x\log x\) operator-Jensen theorem,
  Effros perspective theorem, relative-entropy trace representation, and
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive` remain open.
- 2026-05-27: The Hansen-Pedersen/Effros source route is now split more
  faithfully: `cstarMatrixPositiveOperatorConvexTarget`,
  `cstarMatrixPositiveOperatorConvexTarget_id`,
  `cstarMatrixPositiveHansenPedersenTransferTarget`,
  `cstarMatrixXLogXPositiveOperatorConvexTarget`, and
  `cstarMatrixXLogXHansenPedersenTransferTarget` distinguish ordinary
  positive-cone operator convexity from Hansen-Pedersen transfer before the
  assembled `cstarMatrixXLogXHansenPedersenJensenTarget`. Only the
  identity-function ordinary-convexity sanity theorem was proved in that pass;
  the later 2026-05-28 direct-kernel route closes nonlinear \(x\log x\)
  operator convexity, while the transfer theorem remains open.
- 2026-05-27: A1.5-B1 now has the assembly adapter
  `cstarMatrixXLogXHansenPedersenJensenTarget_of_positiveOperatorConvex_of_transfer`.
  It proves that the concrete \(x\log x\) Hansen-Pedersen Jensen target follows
  once the concrete operator-convexity target and concrete transfer target are
  locally proved. This is dependency wiring only; it does not prove either
  nonlinear input.
- 2026-05-28: Since ordinary positive-cone operator convexity of \(x\log x\)
  is now closed locally, A1.5-B1 also has the transfer-only bridge
  `cstarMatrixXLogXHansenPedersenJensenTarget_of_transfer`. That pass left the
  fixed-size transfer target as the visible blocker; the later all-finite
  correction below refines this to
  `cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget` or a finite
  Effros perspective route that bypasses it, followed by relative-entropy joint
  convexity, Lieb trace concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, and CACM equation (2).
- 2026-05-28: Corrected the Hansen-Pedersen source target to expose the
  all-finite-size hypothesis required by the standard block-matrix proof:
  `cstarMatrixPositiveOperatorConvexAllFiniteTarget`,
  `cstarMatrixPositiveHansenPedersenTransferAllFiniteTarget`,
  `cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget`, and
  `cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget`. Also proved
  `cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`
  and the adapter
  `cstarMatrixXLogXHansenPedersenJensenTarget_of_allFiniteTransfer`. The active
  red bottleneck is now the all-finite transfer theorem or a finite Effros
  perspective route that bypasses it.
- 2026-05-27: A Bendat-Sherman-route subdependency for A1.5-B1 is now closed:
  `cstarMatrix_cfc_one_add_log_eq_one_add_log`,
  `cstarMatrixXLogXDerivativeMonotoneTarget`, and
  `cstarMatrixXLogXDerivativeMonotoneTarget_of_log_monotone` prove operator
  monotonicity of the formal derivative `1 + log x` on the strictly positive
  finite C-star-matrix cone by reusing local `cstarMatrix_log_le_log`. This
  does not prove the Bendat-Sherman bridge or
  `cstarMatrixXLogXPositiveOperatorConvexTarget`.
- 2026-05-27: The same Bendat-Sherman route now has the exact missing bridge
  named as `cstarMatrixBendatShermanDerivativeBridgeTarget`.  The adapter
  `cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDerivativeBridge`
  shows that this bridge, together with the closed derivative-monotonicity
  theorem, would close the concrete `x log x` operator-convexity target.  The
  bridge itself remains open.
- 2026-05-27: The Bendat-Sherman route was corrected to the source-faithful
  first-divided-difference formulation.  New local names are
  `realXLogXDividedDifference`,
  `cstarMatrixXLogXDividedDifferenceMonotoneTarget`,
  `cstarMatrixBendatShermanDividedDifferenceBridgeTarget`, and
  `cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDividedDifferenceBridge`.
  The derivative-monotonicity theorem remains a closed sanity subdependency,
  not the full Bendat-Sherman bridge.
- 2026-05-27: The divided-difference route now has scalar normalization lemmas:
  `realXLogXDividedDifference_self`,
  `realXLogXDividedDifference_eq_log_add_ratio`, and
  `realXLogXDividedDifference_eq_log_add_normalized`.  These identify the
  off-diagonal kernel as `log c + (x / c) * log (x / c) / (x / c - 1)`;
  proving operator monotonicity of that normalized logarithmic kernel remains
  the next real Bendat-Sherman-route dependency.
- 2026-05-28: The logarithmic-kernel route now has a finite C-star spectrum
  wrapper and the first unital inverse-kernel monotonicity dependency:
  `cstarMatrix_spectrum_nonneg_of_nonneg`,
  `cstarMatrix_cfc_one_sub_one_add_inv_monotone`, and
  `cstarMatrix_cfc_pos_over_one_add_monotone`.  These prove operator
  monotonicity of `x ↦ 1 - (1 + x)⁻¹` and `x ↦ x/(1+x)` on the nonnegative
  cone in the same unital CFC vocabulary as the Lieb route.  They do not yet
  prove the integral lift to `x log x/(x-1)`, full divided-difference
  monotonicity, Bendat-Sherman, Lieb, matrix Bernstein, or equation (2).
- 2026-05-27: Local/mathlib reuse for the next nonlinear Hansen-Pedersen target
  was ruled out with evidence. Mathlib currently has operator-log monotonicity
  but its CFC exp/log order file lists operator-log concavity and operator
  convexity of `x => x * log x` as TODOs. The next real proof target remains
  `cstarMatrixXLogXHansenPedersenJensenTarget`, unless the source route changes.
- 2026-05-28: The Bendat-Sherman logarithmic-kernel route now also has the
  scaled fractional-kernel theorem
  `cstarMatrix_cfc_pos_over_pos_add_monotone`: for every `s > 0`,
  `x => x / (s + x)` is operator-monotone on the nonnegative finite complex
  C-star cone. This closes the scaling dependency after the unital
  `x/(1+x)` theorem, but the integral lift to the normalized logarithmic
  kernel, full divided-difference monotonicity, and the Bendat-Sherman bridge
  remain open.
- 2026-05-28: The same route now has the finite nonnegative-combination
  closure `cstarMatrix_cfc_finset_sum_nonneg_mul_pos_over_pos_add_monotone`
  for finite sums of scaled kernels `x => x / (sigma + x)` with nonnegative
  weights and positive `sigma`. This is a finite-sum precursor only; the
  Bochner/Riemann integral lift to the normalized logarithmic kernel remains
  open.
- 2026-05-28: The Bendat-Sherman route now has the generic CFC Bochner-integral
  order theorem `cfc_integral_mono_of_forall_of_bound`: pointwise CFC Loewner
  inequalities integrate to Loewner inequalities for the integrated kernel
  under the joint-continuity and finite-integral-bound hypotheses of
  `cfc_integral`. The scalar/logarithmic integral identity and concrete
  continuity/boundedness side conditions were handled by later route rows; the
  scalar-integral-to-CFC equality remains open.
- 2026-05-28: The scalar/logarithmic identity side of that route is now partly
  closed: `realNormalizedLogKernel` names the diagonal-normalized kernel,
  `realXLogXDividedDifference_eq_log_add_normalizedKernel` rewrites the scalar
  divided difference as `log c + realNormalizedLogKernel (x / c)`, and
  `real_normalizedLogKernel_offdiag_intervalIntegral` proves
  `∫ u in 0..1, t / (u + (1 - u) * t) = t * log t / (t - 1)` for
  `t > 0`, `t != 1`. The continuity and boundedness side conditions are now
  closed separately; scalar-integral-to-CFC equality and full
  divided-difference monotonicity remain open.
- 2026-05-28: The same scalar-integral route now has the interior pointwise
  operator-monotonicity theorem
  `cstarMatrix_cfc_unit_interval_fractional_kernel_monotone` for
  `x => x / (u + (1 - u) * x)` when `0 < u < 1`, proved by reducing to the
  scaled `x/(s+x)` theorem with `s = u/(1-u)`. The endpoint-inclusive theorem
  `cstarMatrix_cfc_unit_interval_fractional_kernel_monotone_of_mem_Icc` now
  handles all `u ∈ [0,1]` on the strictly positive cone (`u=0` is constant
  one, `u=1` is identity). The concrete `cfc_integral` side-condition
  discharge and scalar-integral-to-CFC equality remain the next frontier.
- 2026-05-28: The route now also closes the explicit boundedness side
  conditions for the unit-interval integrand. The scalar theorem
  `real_unit_interval_fractional_kernel_abs_le_max_of_le` proves
  `|z / (u + (1 - u) * z)| <= max 1 M` for `u ∈ [0,1]` and `0 < z <= M`;
  `real_unit_interval_fractional_kernel_spectrum_norm_le_max` specializes this
  to strictly positive C-star spectra. The a.e./finite-integral adapters
  `ae_unit_interval_fractional_kernel_spectrum_norm_le_max`,
  `hasFiniteIntegral_const_max_one_spectrum_bound`,
  `continuousOn_uncurry_unit_interval_subtype_fractional_kernel_spectrum`,
  `ae_unit_interval_subtype_fractional_kernel_spectrum_norm_le_max`, and
  `hasFiniteIntegral_unit_interval_subtype_const_max_one_spectrum_bound` give
  the interval-subtype shape expected by the future `cfc_integral` assembly.
  The scalar-integral-to-CFC equality for `realNormalizedLogKernel` and full
  divided-difference monotonicity remain open.
- 2026-05-28: The normalized logarithmic-kernel route now closes the
  scalar-integral-to-CFC equality and the normalized-kernel CFC monotonicity
  theorem. New names are `realNormalizedLogKernel_setIntegral`,
  `cstarMatrix_cfc_realNormalizedLogKernel_eq_unit_interval_integral`,
  `cstarMatrix_setIntegral_mono_on`,
  `cstarMatrix_cfc_realNormalizedLogKernel_monotone_of_spectrum_bound`, and
  `cstarMatrix_cfc_realNormalizedLogKernel_monotone`. The remaining
  Bendat-Sherman-route gap is no longer the scalar-integral-to-CFC equality;
  it is lifting normalized-kernel monotonicity through the base-point
  scaling/constant-shift CFC normalization for each
  `realXLogXDividedDifference c`, followed by the finite
  Bendat-Sherman divided-difference bridge.
- 2026-05-28: The Bendat-Sherman divided-difference route now closes that
  base-point normalization and the full divided-difference monotonicity target.
  New names are `realNormalizedLogKernel_eq_mul_dslope_log`,
  `continuousOn_realNormalizedLogKernel_Ioi`,
  `cstarMatrix_cfc_realXLogXDividedDifference_eq_log_add_scaled_normalizedKernel`,
  and `cstarMatrixXLogXDividedDifferenceMonotoneTarget_of_normalizedLogKernel`.
  The remaining Bendat-Sherman-route gap is the finite bridge
  `cstarMatrixBendatShermanDividedDifferenceBridgeTarget`; A1.5-B1 still does
  not prove operator convexity, Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- 2026-05-28: A direct integral-route dependency is now closed in
  `LiebTrace.lean`: `matrix_posDef_inverse_schur_block`,
  `matrix_weighted_inverse_schur_block`, `matrix_posDef_weighted_sum`, and
  `matrix_inv_convex_posDef` prove finite complex matrix inverse convexity on
  the positive-definite cone by a Schur-complement/arithmetic-harmonic mean
  argument. This is useful substrate for shifted inverse kernels, but at this
  stage A1.5-B1 still lacked the C-star/CFC inverse-kernel bridge, the
  integral representation of `x log x`, operator convexity, Lieb trace-MGF domination,
  matrix Bernstein/Khintchine, and CACM equation (2).
- 2026-05-28: The direct inverse-convexity route now also has the finite
  C-star/CFC bridge: `cstarMatrix_nonneg_of_matrix_posSemidef` and
  `cstarMatrix_le_of_matrix_le` lift ordinary matrix PSD/Loewner facts back to
  C-star order, and `cstarMatrix_cfc_inv_convex_isStrictlyPositive` states the
  inverse-kernel convexity theorem in the real CFC vocabulary on the strictly
  positive cone. At this stage it still did not prove the shifted-positive inverse-kernel
  family, the `x log x` integral representation, Bendat-Sherman, Lieb
  concavity, matrix Bernstein, or CACM equation (2).
- 2026-05-28: The direct inverse-convexity route now also closes the shifted
  inverse-kernel family: `cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one`
  reduces `x ↦ (s + x)⁻¹` to ordinary inverse CFC after adding `sI`, and
  `cstarMatrix_cfc_shifted_inv_convex_nonneg` proves shifted inverse-kernel
  convexity on the nonnegative finite C-star cone for every `s > 0`. The next
  direct-route target is the scalar/operator integral representation turning
  these kernels into operator convexity of `x log x`; A1.5-B1 still does not
  prove Lieb concavity, matrix Bernstein, or CACM equation (2).
- 2026-05-28: The scalar normalization layer for the direct `x log x` route is
  now closed: `real_xlog_eq_sub_one_mul_realNormalizedLogKernel` proves
  `(x - 1) * realNormalizedLogKernel x = x * Real.log x`, and
  `real_xlog_eq_sub_one_mul_normalizedKernel_setIntegral` combines this with
  the existing unit-interval integral for the normalized kernel. This is still
  scalar only; the open direct-route target is the operator integral assembly
  turning the scalar representation plus shifted inverse-kernel convexity into
  operator convexity of `x ↦ x log x`.
- 2026-05-28: A further scalar direct-route dependency is closed:
  `real_unit_interval_xlog_integrand_eq_affine_add_shifted_inv` rewrites the
  unit-interval integrand `(x - 1)^2 / (u + (1 - u) * x)` for `x > 0` and
  `0 <= u < 1` as an affine term plus a positive multiple of the shifted
  inverse kernel `(x + u / (1 - u))⁻¹`. The remaining direct-route target is
  the C-star/CFC fixed-`u` operator decomposition and then the operator
  integral assembly.
- 2026-05-28: The direct `x log x` route was corrected and the ordinary
  positive-cone operator-convexity dependency is now closed. The auxiliary
  `(x - 1)^2 / (u + (1 - u) * x)` integrand is true but is not the scalar
  reconstruction kernel; the correct source-aligned kernel is
  `x * (x - 1) / (u + (1 - u) * x)`. New closed names include
  `real_xlog_eq_unit_interval_xlog_kernel_integral`,
  `real_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`,
  `cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`,
  `continuousOn_uncurry_unit_interval_xlog_kernel_spectrum`,
  `real_unit_interval_xlog_kernel_spectrum_norm_le_max_sq`,
  `ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq`,
  `hasFiniteIntegral_const_max_one_spectrum_bound_sq`,
  `cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral`,
  `cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_convex_of_pos_lt_one`,
  and `cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel`.
  A1.5-B1 still does not prove Hansen-Pedersen transfer, Effros perspective or
  relative-entropy joint convexity, Lieb trace concavity, trace-MGF domination,
  matrix Bernstein/Khintchine, or CACM equation (2).
- 2026-05-28: The Hansen-Pedersen red bottleneck gained a real block-algebra
  dependency closure in `CStarMatrixBridge.lean`.  New definitions/theorems
  `cstarMatrixBlockDiagonal`, `cstarMatrixColumnPair`,
  `cstarMatrixColumnPair_conjTranspose_mul_columnPair`,
  `cstarMatrixColumnPair_conjTranspose_mul_self`,
  `cstarMatrixBlockDiagonal_mul_columnPair`,
  `cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair`, and
  `cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum` formalize
  \(V=[A;B]\), \(D=\operatorname{diag}(T_1,T_2)\), \(V^*V=A^*A+B^*B\), and
  \(V^*DV=A^*T_1A+B^*T_2B\).  This closes the entrywise block-compression
  substrate for the standard proof; the active red bottleneck remains the
  nonlinear CFC/Jensen transfer theorem
  `cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget` or a finite Effros
  perspective theorem.
- 2026-05-28: The same red bottleneck gained the next block-diagonal substrate
  closure.  `CStarMatrixBridge.lean` now proves that
  `cstarMatrixBlockDiagonal` preserves zero, one, addition, negation,
  subtraction, star, multiplication, units, nonnegativity, and strict
  positivity through theorems including `cstarMatrixBlockDiagonal_star`,
  `cstarMatrixBlockDiagonal_mul`, `cstarMatrixBlockDiagonal_isUnit`,
  `cstarMatrixBlockDiagonal_nonneg`, and
  `cstarMatrixBlockDiagonal_isStrictlyPositive`.  This closes the
  star-algebra/order bookkeeping for \(D=\operatorname{diag}(T_1,T_2)\); the
  active red bottleneck remains the nonlinear CFC/Jensen transfer theorem
  `cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget` or a finite Effros
  perspective theorem.
- 2026-05-28: The Hansen-Pedersen route now also has the block-diagonal CFC
  decomposition.  `CStarMatrixBridge.lean` provides the continuous star-algebra
  homomorphism `cstarMatrixBlockDiagonalStarAlgHom_continuous`, and
  `LiebTrace.lean` proves `cstarMatrixBlockDiagonal_cfc`:
  \(f(\operatorname{diag}(T_1,T_2))=\operatorname{diag}(f(T_1),f(T_2))\) for
  self-adjoint blocks and \(f\) continuous on the union of spectra.  This closes
  another listed red-bottleneck dependency; the active blocker is now the
  block-isometry compression/Jensen inequality or an Effros perspective theorem,
  not block-diagonal CFC.
- 2026-05-28: The next Hansen-Pedersen block-isometry dependency is closed:
  `CStarMatrixBridge.lean` now has rectangular multiplication helpers
  `cstarMatrix_mul_assoc_rect`, `cstarMatrix_mul_one_rect`, and
  `cstarMatrix_one_mul_rect`, plus the range projection
  `cstarMatrixColumnPairRangeProjection`.  Under \(V^*V=I\), it proves
  \(P=VV^*\) is self-adjoint/idempotent and absorbs \(V\) and \(V^*\) via
  `cstarMatrixColumnPairRangeProjection_mul_self_of_sum`,
  `cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum`, and
  `cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum`.  The
  associated reflection \(R=2P-I\) is also formalized via
  `cstarMatrixProjectionReflection` and `cstarMatrixColumnPairRangeReflection`;
  it is self-adjoint, squares to identity, is a unitary unit, and fixes \(V\) through
  `cstarMatrixColumnPairRangeReflection_mul_self_of_sum`,
  `cstarMatrixColumnPairRangeReflection_isUnit_of_sum`,
  `cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum`, and
  `cstarMatrixColumnPairRangeReflection_mul_columnPair_of_sum`.  The active
  CFC-conjugation substrate is also closed by `cstarMatrix_cfc_unitary_conj`,
  proving \(f(UTU^*)=Uf(T)U^*\) for unitary \(U\).  The strict-positive domain
  side condition for the same conjugation/reflection route is closed by
  `cstarMatrix_unitary_conj_isStrictlyPositive` and
  `cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum`.  The
  block-compression domain side condition is closed too:
  `cstarMatrixColumnPair_mulVec_injective_of_sum`,
  `cstarMatrixColumnPair_compress_blockDiagonal_isStrictlyPositive_of_sum`, and
  `cstarMatrixHansenPedersenCompression_isStrictlyPositive_of_sum` prove
  \(V^*\operatorname{diag}(T_1,T_2)V=A^*T_1A+B^*T_2B\) is strictly positive
  when \(V^*V=I\) and \(T_1,T_2\) are.  The algebraic pinching-average
  compression identity is also closed by
  `cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum` and
  `cstarMatrixColumnPair_reflectionAverage_compression_of_sum`, proving
  \(V^*R=V^*\) and \(V^*((D+RDR)/2)V=V^*DV\) for \(R=2VV^*-I\).  It also proves
  `cstarMatrixColumnPair_reflectionAverage_conj_rangeReflection_of_sum` and
  `cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum`, so
  the averaged block is invariant under and commutes with the reflection; and
  `cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum`, so
  it commutes with \(VV^*\).  Finally,
  `cstarMatrixColumnPair_reflectionAverage_mul_columnPair_of_sum` and
  `cstarMatrixColumnPair_conjTranspose_mul_reflectionAverage_of_sum` show the
  averaged block acts on \(V\) and \(V^*\) through the same compressed corner
  \(V^*DV\).  The active blocker is now the nonlinear CFC pinching/Jensen step
  or a finite Effros perspective theorem, not projection/reflection algebra,
  algebraic pinching-average compression/invariance/projection-commutation or
  range-reduction, unitary CFC conjugation, or strict-positive domain
  preservation.
- 2026-05-28: The reflection-average CFC pinching inequality is now closed.
  `LiebTrace.lean` proves `cstarMatrix_compression_nonneg` and
  `cstarMatrix_compression_mono`, showing rectangular C-star compression
  preserves nonnegativity and order.  It also proves
  `cstarMatrixColumnPair_reflectionAverage_cfc_le_average_of_sum` and
  `cstarMatrixColumnPair_reflectionAverage_compressed_cfc_le_compressed_of_sum`:
  ordinary all-finite operator convexity applied to \(D\) and \(RDR\), plus
  unitary CFC conjugation and compression by \(V=[A;B]\), yields
  \(V^*f((D+RDR)/2)V\le V^*f(D)V\).  The active red blocker has narrowed to the
  nonlinear corner functional-calculus identity
  \(V^*f((D+RDR)/2)V=f(V^*DV)\), or a source-faithful Effros/perspective route
  that bypasses that identity.  The full-paper gate is still FAIL.
- 2026-05-28: The Hansen-Pedersen red bottleneck now has the shifted-inverse
  nonlinear corner subcase closed.  `CStarMatrixBridge.lean` proves
  `cstarMatrix_units_inv_mul_rect_eq_mul_units_inv_of_mul_eq`, the rectangular
  unit-inverse adapter \(UV=VW \Rightarrow U^{-1}V=VW^{-1}\).  `LiebTrace.lean`
  proves `cstarMatrix_cfc_shifted_inv_mul_rect_eq_mul_cfc_shifted_inv_of_mul_eq`
  and `cstarMatrixColumnPair_reflectionAverage_shifted_inv_corner_of_sum`,
  giving \(V^*(sI+(D+RDR)/2)^{-1}V=(sI+V^*DV)^{-1}\) for \(s>0\).  This was
  an intermediate queue item; the following entry supersedes it by closing the
  full concrete \(x\log x\) corner/Jensen step.
- 2026-05-28: The concrete Hansen-Pedersen `x log x` corner/Jensen dependency is
  now closed.  `CStarMatrixBridge.lean` adds the finite-dimensional C-star
  instance and compression linearity/continuous-linear-map lemmas
  (`cstarMatrix_complex_finiteDimensional`, `cstarMatrixCompressionCLM`, and
  related add/sub/smul helpers).  `LiebTrace.lean` proves
  `cstarMatrix_compression_setIntegral`,
  `cstarMatrixColumnPair_reflectionAverage_xlog_kernel_corner_of_sum`,
  `cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum`, and the concrete
  two-point Jensen theorem
  `cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel`.  The
  affine-corrected normalized entropy-kernel dependency is also closed by
  `realEntropyKernel`, `cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one`,
  `cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_unit_interval_kernel`,
  `cstarMatrixEntropyKernelPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`,
  and `cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_unit_interval_kernel`.
  The finite perspective square-root substrate is now closed too:
  `cstarMatrixPositiveSqrt`, `cstarMatrixPositiveInvSqrt`,
  `cstarMatrixPositiveSqrt_mul_self`,
  `cstarMatrixPositiveInvSqrt_mul_sqrt`,
  `cstarMatrixPositiveSqrt_mul_invSqrt`,
  `cstarMatrixPositiveInvSqrt_isUnit`,
  `cstarMatrixPositiveInvSqrt_mul_self_mul`, and
  `cstarMatrixPositiveInvSqrt_conj_isStrictlyPositive` remove hidden
  \(A^{1/2}\)/\(A^{-1/2}\) algebraic side conditions from the next perspective
  statement.
  The
  full-paper gate is still FAIL, but the red blocker has advanced: the active
  foundation is now the source-faithful finite Effros superoperator
  perspective / Umegaki matrix relative-entropy trace representation, then
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`,
  followed by arbitrary-\(H\) Lieb concavity, trace-MGF domination, and matrix
  Bernstein/Khintchine for CACM equation (2).
- 2026-05-28: The ordinary finite perspective theorem for the normalized
  entropy kernel is now closed.  `LiebTrace.lean` defines
  `cstarMatrixPerspective` and `cstarMatrixPerspectiveWeight`, proves the
  weight normalization/compression/uncompression lemmas, and closes
  `cstarMatrixEntropyKernelPerspective_jointConvex` for
  \(P_f(X,A)=A^{1/2}f(A^{-1/2}XA^{-1/2})A^{1/2}\) with
  \(f(x)=x\log x-(x-1)\).  This is a listed Effros-route dependency, but the
  full-paper gate remains FAIL: the still-open theorem is the source-faithful
  finite superoperator perspective/trace representation for Umegaki relative
  entropy and then `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.
- 2026-05-28: The superoperator trace-representation route now has finite
  vectorization and the vectorized-identity trace pairing closed.
  `LiebTrace.lean` defines `matrixVecId`, `matrixVec`, and
  `matrixComplexQuadraticForm`, proves `finset_sum_product_diagonal`, and
  closes `matrix_kronecker_transpose_mulVec_matrixVec` plus
  `matrixComplexQuadraticForm_vecId_kronecker_transpose`, i.e.
  \(A\otimes B^{\mathsf T}\) represents \(M\mapsto AMB\) and
  \(v_I^*(A\otimes B^{\mathsf T})v_I=\operatorname{tr}(AB)\).  These are real
  dependencies for translating Kronecker/superoperator perspective inequalities
  into trace formulas, but the red bottleneck remains the CFC/log
  superoperator ratio behavior and the full Umegaki relative-entropy trace
  representation.
- 2026-05-28: The same superoperator route now also has the polynomial
  vectorization/trace-pairing layer closed.  `LiebTrace.lean` proves
  `matrix_kronecker_transpose_pow`,
  `matrix_kronecker_transpose_pow_mulVec_matrixVec`, `matrixVec_one`, and
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_pow`, giving
  \((A\otimes B^{\mathsf T})^k=A^k\otimes(B^k)^{\mathsf T}\),
  \((A\otimes B^{\mathsf T})^k\operatorname{vec}(M)=\operatorname{vec}(A^kMB^k)\),
  and \(v_I^*(A\otimes B^{\mathsf T})^k v_I=\operatorname{tr}(A^kB^k)\).
  The remaining red-bottleneck dependency is the CFC/log passage from these
  polynomial identities to the finite superoperator ratio and the full
  Umegaki relative-entropy trace formula.
- 2026-05-28: The finite-polynomial packaging of the superoperator
  trace-pairing layer is also closed.  `LiebTrace.lean` proves
  `matrixComplexQuadraticForm_sum`, `matrixComplexQuadraticForm_smul`, and
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial`, giving
  \(v_I^*(\sum_{k\in S} c_k(A\otimes B^{\mathsf T})^k)v_I
    =\sum_{k\in S}c_k\operatorname{tr}(A^kB^k)\).  The active bottleneck is now
  the analytic CFC/log transfer to the finite superoperator ratio, then the
  Umegaki relative-entropy trace formula.
- 2026-05-28: The finite-polynomial trace identity is now also available in
  standard Lean polynomial-evaluation form via
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval`.  This closes an
  API bridge into `Polynomial.aeval`; the remaining active bottleneck is still
  the analytic CFC/log transfer for the finite superoperator ratio.
- 2026-05-28: The first analytic transfer hook for that route is closed:
  `continuous_matrixComplexQuadraticForm` proves continuity of
  \(M\mapsto v^*Mv\) for fixed finite \(v\).  This supports a later
  polynomial-to-CFC/log limit argument but does not yet prove the log transfer
  or Umegaki relative-entropy trace representation.
- 2026-05-28: Polynomial evaluation continuity on finite complex matrices is
  also closed by `continuous_matrix_polynomial_aeval`.  This removes another
  finite-dimensional continuity side condition before the actual CFC/log
  transfer theorem.
- 2026-05-29: The source-faithful superoperator polynomial perspective layer is
  now closed for the Effros/Umegaki route.  `LiebTrace.lean` proves the
  domain/CFC/approximation facts
  `matrixVecId_inner_matrixVec`,
  `matrix_transpose_conjTranspose_eq_self_of_isSelfAdjoint`,
  `matrix_kronecker_transpose_isSelfAdjoint_of_isSelfAdjoint`,
  `matrix_kronecker_transpose_posSemidef`,
  `matrix_kronecker_transpose_posDef`,
  `matrix_kronecker_inv_transpose_posDef`, `matrixSelfAdjointCfc`,
  `matrixSelfAdjointCfc_polynomial`,
  `exists_realPolynomial_near_log_on_Icc`,
  `exists_realPolynomial_near_xlog_on_Icc`, and
  `exists_realPolynomial_near_realEntropyKernel_on_Icc`, plus the right
  multiplication trace formulas
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_pow_right`,
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial_right`,
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval_right`,
  `matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_transpose_realPolynomial`,
  and
  `matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_inv_transpose_realPolynomial_right`.
  This proves the finite-polynomial identity for
  \(v_I^*p(L_XR_A^{-1})R_Av_I\).  The full-paper gate remains FAIL: the active
  red bottleneck is now the analytic logarithmic/entropy-kernel CFC transfer
  from these polynomial formulas and then the Umegaki relative-entropy trace
  representation.
- 2026-05-29: The analytic uniform-approximation transfer for the
  source-faithful Effros/Umegaki route is now closed by
  `tendsto_matrixComplexQuadraticForm_matrixSelfAdjointCfc_mul` and
  `tendsto_superoperator_entropyKernel_of_realPolynomial_uniform_approx`.
  These theorems prove that a supplied uniform real-polynomial approximation to
  \(x\log x-(x-1)\) on the spectrum of
  \(X\otimes(A^{-1})^{\mathsf T}\) transfers the finite-polynomial trace
  formula for \(p(L_XR_A^{-1})R_A\) to the entropy-kernel CFC trace term.  The
  full-paper gate remains FAIL: the active red bottleneck is reduced to the
  source-faithful Umegaki trace representation and noncommutative
  relative-entropy joint convexity.
- 2026-05-29: The supplied-approximation input in the previous item is now
  removed.  `matrix_posDef_spectrum_real_pos`,
  `matrix_posDef_spectrum_real_subset_Icc`,
  `exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_on_subset_Icc`,
  `exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_spectrum_of_posDef`,
  and `exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_of_posDef`
  construct a real-polynomial approximating sequence on positive-definite
  spectra and specialize the convergence theorem to
  \(X\otimes(A^{-1})^{\mathsf T}\).  The full-paper gate remains FAIL because
  the source-faithful Umegaki trace representation and
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive` are still open.
- 2026-05-29: The remaining joint-convexity step is now corrected to the
  source-faithful superoperator target
  `cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator`, stated in
  terms of \(L_XR_A^{-1}\) via \(X\otimes(A^{-1})^{\mathsf T}\) and right
  multiplication by \(A\).  The ordinary source-matrix perspective bridge was
  rejected as not source-faithful for Umegaki relative entropy.  The
  full-paper gate remains FAIL: this target and
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive` remain open.
- 2026-05-29: The compact relative-entropy trace side of the Umegaki route is
  now closed by `matrix_isHermitian_cfc_id`, `matrix_isHermitian_cfc_xlog`, and
  `matrixTrace_hermitianCfc_relativeEntropy_re_eq_sum`.  The active red
  bottleneck is now the matching spectral-overlap expansion for the
  superoperator CFC term \(v_I^*f(L_XR_A^{-1})R_Av_I\), then the transport to
  `cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator`.
- 2026-05-29: The remaining superoperator-side theorem is now named as
  `matrixSuperoperatorEntropyKernelOverlapExpansion`, with
  `matrixSuperoperatorEntropyKernelTrace` packaging the finite Kronecker trace
  expression and `matrixRelativeEntropyTraceRepresentation_of_superoperator_overlap`
  proving that the overlap expansion would match the compact relative-entropy
  trace.  Do not reopen the ordinary source-matrix perspective route for this
  bottleneck; the next counted progress is proving this overlap expansion or a
  source-equivalent theorem.
- 2026-05-29: The finite-polynomial part of
  `matrixSuperoperatorEntropyKernelOverlapExpansion` is now closed.
  `matrix_isHermitian_cfc_congr_eigen`, `matrix_isHermitian_cfc_mul`,
  `matrix_isHermitian_cfc_fun_pow_nat`,
  `matrix_isHermitian_cfc_inv_of_posDef`,
  `matrix_posDef_mul_inv_pow_eq_cfc`,
  `matrixTrace_pow_mul_inv_pow_re_eq_sum`, and
  `matrixPolynomialTraceRatio_re_eq_sum` prove that
  \(\operatorname{tr}(X^kA(A^{-1})^k)\) and real-polynomial sums have the same
  eigenbasis-overlap weights as the compact relative-entropy trace.  The active
  bottleneck remains the limiting entropy-kernel CFC overlap expansion.
- 2026-05-29: The limiting entropy-kernel overlap expansion and the
  source-faithful Umegaki trace representation are now closed.  New theorem
  names: `realRelativeEntropy_eq_mul_realEntropyKernel_mul_inv`,
  `tendsto_matrixPolynomialTraceRatio_overlap_sum_of_uniform_approx`,
  `exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_and_overlap_of_posDef`,
  `matrixSuperoperatorEntropyKernelOverlapExpansion_of_nonempty`,
  `matrixSuperoperatorEntropyKernelOverlapExpansion_of_isEmpty`,
  `matrixSuperoperatorEntropyKernelOverlapExpansion_all`, and
  `cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator_all`.  The
  full-paper gate remains FAIL because the active A1.5-B1 red bottleneck is now
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, followed by
  arbitrary-\(H\) Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, CACM equation (2), and downstream FP concentration.
- 2026-05-29: The joint-convexity bottleneck gained the product-index lift and
  scalar-extraction layer.  New theorem names:
  `matrix_kronecker_right_identity_transpose_real_smul_add`,
  `cstarMatrixSuperoperatorLeftLift`, `cstarMatrixSuperoperatorRightLift`,
  `cstarMatrixSuperoperatorLeftLift_real_smul_add`,
  `cstarMatrixSuperoperatorRightLift_real_smul_add`,
  `cstarMatrixSuperoperatorLeftLift_isStrictlyPositive`,
  `cstarMatrixSuperoperatorRightLift_isStrictlyPositive`,
  `matrixComplexQuadraticForm_re_nonneg_of_posSemidef`,
  `matrixComplexQuadraticForm_re_mono_of_posSemidef_sub`, and
  `matrixComplexQuadraticForm_re_mono_of_cstarMatrix_le`.  These are counted
  dependencies for `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, but
  the red bottleneck remains open at the finite superoperator perspective
  bridge \(v_I^*P_f(L_X,R_A)v_I = v_I^*f(L_XR_A^{-1})R_Av_I\).
- 2026-05-29: The same bottleneck gained the product-index ordinary
  perspective trace theorem.  New theorem names:
  `matrixComplexQuadraticForm_add`,
  `cstarMatrixSuperoperatorPerspectiveTrace`,
  `cstarMatrixSuperoperatorPerspectiveTrace_jointConvex`,
  `cstarMatrixRelativeEntropyPerspectiveTraceRepresentation`, and
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive_of_perspectiveTraceRepresentation`.
  This proves joint convexity of \(v_I^*P_f(L_X,R_A)v_I\) and reduces the red
  bottleneck to the exact equality bridge identifying that quantity with local
  relative entropy.  It does not yet prove
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.
- 2026-05-29: The equality bridge gained its first CFC commutation/reorder
  dependency.  New theorem names:
  `cstarMatrixSuperoperatorLeftLift_rightLift_commute`,
  `cstarMatrixSuperoperatorPositiveInvSqrtRightLift_commute_leftLift`, and
  `cstarMatrixSuperoperatorPerspective_normalizedArgument_reorder`.  The next
  dependency is the product-index right-lift identity
  \(R_A^{-1/2}R_A^{-1/2}=R_A^{-1}\) and the CFC transport that identifies the
  ordinary product-index perspective trace with
  `matrixSuperoperatorEntropyKernelTrace`.
- 2026-05-29: The right-lift inverse-square-root square dependency is closed.
  New theorem names: `cstarMatrixPositiveInvSqrt_mul_self_eq_unit_inv` and
  `cstarMatrixSuperoperatorPerspective_normalizedArgument_eq_leftLift_mul_rightLift_unit_inv`.
  The remaining equality-bridge target is now the outer CFC/square-root trace
  transport from \(R_A^{1/2}f(L_XR_A^{-1})R_A^{1/2}\) to
  \(f(L_XR_A^{-1})R_A\), then matching that expression with
  `matrixSuperoperatorEntropyKernelTrace`.
- 2026-05-29: The ratio/square-root commutation dependency is closed.  New
  theorem names: `cstarMatrixPositiveSqrt_commute_unit_inv`,
  `cstarMatrixSuperoperatorPositiveSqrtRightLift_commute_leftLift`, and
  `cstarMatrixSuperoperatorLeftLift_mul_rightLift_unit_inv_commute_positiveSqrtRightLift`.
  The next equality-bridge dependency is the CFC transport showing
  \(f(L_XR_A^{-1})\) commutes with \(R_A^{1/2}\), followed by the
  vectorized-identity quadratic-form product equality.
- 2026-05-29: The finite-dimensional relative-entropy/Lieb bottleneck is now
  closed.  New theorem names:
  `cstarMatrixSuperoperatorEntropyKernelCfc_ratio_commute_positiveSqrtRightLift`,
  `cstarMatrixSuperoperatorPerspective_outerSqrt_cfc_ratio_mul_outerSqrt`,
  `cstarMatrixSuperoperatorPerspective_eq_cfc_ratio_mul_rightLift`,
  `cstarMatrix_unit_inv_to_matrix`,
  `cstarMatrixSuperoperatorRightLift_unit_inv_to_matrix`,
  `cstarMatrixSuperoperatorPerspectiveTrace_eq_matrixSuperoperatorEntropyKernelTrace`,
  `cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all`,
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all`,
  `liebTraceConcavityTarget_all`, and
  `FiniteProbability.expectationReal_trace_normed_exp_add_le`.  The active
  A1.5-B1 red bottleneck has moved to Tropp's iterated independent-sum
  trace-MGF domination theorem and matrix Bernstein/Khintchine for CACM
  Algorithm 1 equation (2).
- 2026-05-29: The first Algorithm 1 product-law adapter for the new trace-MGF
  bottleneck is closed in `ElementwiseTraceMGF.lean`.  New theorem names:
  `sqMagSampleProbability`,
  `sqMagTraceProbability_expectationComplex_step_eq`,
  `sqMagTraceProbability_expectationCStarMatrix_step_eq`,
  `sqMagTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation`, and
  `sqMagTraceProbability_expectationReal_trace_normed_exp_add_step_le`.  These
  specialize the no-hidden-Lieb one-step trace-MGF theorem to one coordinate of
  the canonical squared-magnitude Algorithm 1 product trace law; the remaining
  target is the independent-sum trace-MGF iteration and Bernstein/Khintchine
  instantiation.
- 2026-05-29: The Algorithm 1 iid trace-MGF iteration is now closed locally.
  New theorem names: `sqMagTraceProbMass_snoc`,
  `sqMagTraceProbability_expectationReal_succ_last_eq`,
  `cstarMatrix_finset_sum_isSelfAdjoint`, and
  `sqMagTraceProbability_expectationReal_trace_normed_exp_add_sum_le`.  The
  active red bottleneck has moved from product-law trace-MGF iteration to the
  matrix Bernstein/Khintchine tail conversion and downstream FP spectral
  concentration transfer for CACM equation (2).
- 2026-05-29: The finite-real trace-exponential adapter for the Algorithm 1
  trace-MGF route is now closed locally.  New theorem names:
  `finiteComplexCStarMatrix_zero`, `finiteComplexCStarMatrix_add`,
  `finiteComplexCStarMatrix_finset_sum`, `finiteComplexCStarMatrixRingHom`,
  `finiteComplexCStarMatrixRingHom_continuous`,
  `finiteComplexCStarMatrix_finiteMatrixExp`,
  `cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix`,
  `cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix_re`, and
  `sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le`.
  The active red bottleneck is now the scalar matrix-CGF/log-MGF bound for the
  Algorithm 1 self-adjoint dilation increments, followed by the final
  Bernstein/Khintchine largest-eigenvalue tail conversion and FP spectral
  transfer.
- 2026-05-29: The Algorithm 1 self-adjoint dilation trace-MGF instantiation is
  now closed locally.  New theorem names:
  `sqMagTraceProbabilityFiniteRealTraceMGFLogBound`,
  `rectSelfAdjointDilation_elementwiseSampleResidualIncrement_smul_symmetric`,
  `sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_sum_rectSelfAdjointDilation_sampleResidualIncrement_le`,
  and
  `sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le`.
  The left side is now the exact finite-real trace exponential of
  \(\theta D(A-\widetilde A)\).  The next red-bottleneck dependency is the
  scalar matrix-CGF/log-MGF estimate for the one-sample logarithmic mean
  increment.
- 2026-05-29: The Algorithm 1 trace-exponential/eigenvalue Markov step is now
  specialized to the actual scaled self-adjoint dilation residual.  New theorem
  names:
  `sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_ge_le`
  and
  `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge`.
  The remaining red bottleneck is the scalar matrix-CGF/log-MGF estimate and
  explicit Bernstein/Khintchine constants for CACM equation (2), not the
  Markov/eigenvalue conversion itself.
- 2026-05-29: The A1.5-B1 scalar-to-operator CFC Bernstein-parabola lift is
  closed in `LiebTrace.lean`.  New theorem names:
  `cstarMatrix_cfc_quadratic_eq` and
  `cstarMatrix_cfc_real_exp_mul_le_quadratic_of_spectrum`.  These lift a
  scalar pointwise bound \(e^{\theta x}\le 1+\theta x+\beta x^2\) on
  \(\sigma_{\mathbb R}(X)\) to
  \(\exp_{\mathrm{cfc},\mathbb R}(\theta X)\preceq I+\theta X+\beta X^2\).
  This left the scalar Bernstein parabola constants and one-sample
  matrix-CGF/log-MGF variance-proxy use open at that checkpoint; the scalar
  constants are closed in the next memory entry.
- 2026-05-29: The A1.5-B1 scalar Bernstein parabola with constants is now
  closed in `LiebTrace.lean`.  New theorem names:
  `real_exp_quadratic_remainder_monotone`,
  `real_exp_sub_self_sub_one_nonneg`,
  `real_sq_div_two_le_exp_sub_self_sub_one_of_nonneg`,
  `real_exp_le_one_add_self_add_sq_div_two_of_nonpos`,
  `real_exp_tail_two_hasSum`,
  `real_exp_mul_le_quadratic_of_nonneg_of_nonneg_of_le_one`,
  `real_exp_mul_le_quadratic_of_nonneg_of_le_one`,
  `real_exp_mul_le_quadratic_scaled_of_nonneg_of_pos_of_le`, and
  `cstarMatrix_cfc_real_exp_mul_le_bernstein_quadratic_of_spectrum_le`.  The
  remaining red bottleneck is the one-sample matrix-CGF/log-MGF variance-proxy
  instantiation and final Bernstein/Khintchine tail constants for CACM
  equation (2).
- 2026-05-29: The generic A1.5-B1 one-sample matrix-CGF/log-MGF variance
  proxy is now closed in `LiebTrace.lean`, with one real-scalar expectation
  helper in `CStarMatrixExpectation.lean`.  New theorem names:
  `FiniteProbability.expectationCStarMatrix_real_smul`,
  `cstarMatrix_real_smul_isSelfAdjoint`,
  `cstarMatrix_cfc_real_exp_mul_eq_normedSpace_exp_real_smul`,
  `cstarMatrix_selfAdjoint_mul_self_nonneg`,
  `cstarMatrix_one_add_le_normedSpace_exp_of_nonneg`,
  `cstarMatrix_log_one_add_le_self_of_nonneg`,
  `FiniteProbability.expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy`,
  `FiniteProbability.cstarMatrix_log_expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy`,
  and
  `FiniteProbability.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy`.
  The remaining red bottleneck is now Algorithm 1 dilation-increment
  instantiation of that generic theorem, plus the final Bernstein/Khintchine
  tail constants and downstream FP spectral concentration.

- 2026-05-29: Closed the Algorithm 1 truncated one-sample log-CGF
  instantiation.  New shared support-aware wrappers:
  `FiniteProbability.expectationCStarMatrix_nonneg_of_prob_pos`,
  `FiniteProbability.expectationCStarMatrix_mono_of_prob_pos`, and
  `cstarMatrix_spectrum_le_of_le_real_smul_one`.  New Algorithm 1 theorems:
  `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero`,
  `sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le`,
  and
  `sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`.
  The red bottleneck is now the Bernstein/Khintchine trace-MGF-to-tail
  constant optimization and downstream FP spectral concentration, not the
  one-sample Algorithm 1 CGF instantiation.

- 2026-05-29: Closed the Algorithm 1 parameterized two-sided Bernstein tail
  skeleton for the truncated self-adjoint dilation.  New theorem names:
  `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le`,
  `sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le`,
  `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`,
  `sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_ge_le_exp`,
  `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`,
  and
  `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp`.
  The red bottleneck is now theta optimization/final CACM equation (2)
  constants plus downstream floating-point spectral concentration transfer.

- 2026-05-29: Added the explicit `1-\delta` high-probability corollary for the
  Algorithm 1 truncated two-sided dilation eigenvalue theorem.  New theorem
  names: `real_exp_neg_log_two_mul_div_mul_self_add` and
  `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta`.
  This chooses `T = log (2B/delta)` and proves the failure terms sum to
  `delta` locally.  The red bottleneck remains theta optimization, conversion
  from scaled eigenvalues to the final CACM equation (2) spectral-norm
  constants, and downstream FP transfer.

- 2026-05-29: Closed the deterministic scaled-eigenvalue to rectangular
  spectral-event conversion for Algorithm 1.  New shared theorems:
  `finiteLoewnerLe_of_smul_left_le_smul_id` and
  `finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le`.  New Algorithm
  1 event/corollaries:
  `algorithm1ScaledDilationAbsEigenvalueEvent`,
  `algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent`, and
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius`.
  The high-probability spectral radius is still
  `log (2B/delta) / theta`; the red bottleneck is now theta optimization and
  source-constant simplification to CACM equation (2), then downstream FP
  spectral transfer.

- 2026-05-29: Closed the scalar theta-optimization dependency for the
  truncated exact Algorithm 1 spectral route.  New shared theorem:
  `real_bernstein_exact_radius_le_of_log_le`.  New monotonicity helpers:
  `rectOpNorm2Le_mono` and `algorithm1ExactSpectralEvent_mono`.  New
  Algorithm 1 theorem:
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius`.
  This chooses `theta = log (1 + L*r/W) / L` and proves the spectral event at
  radius `r` under an explicit Bennett budget.  The remaining red bottleneck
  is source sample-complexity/final-constant simplification, truncation
  transfer at those constants, and downstream FP spectral transfer.

- 2026-05-29: Closed the source-sharp square variance dependency for the
  Drineas--Zouzias Algorithm 1 route.  New sharp vector/transpose-vector
  moment theorems feed
  `sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_square`,
  `sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_square`,
  and
  `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square`.
  The truncated square trace-MGF/tail skeleton now has
  `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square`,
  `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square`,
  and
  `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_square`.
  Remaining red bottleneck: source sample-complexity/final-constant
  simplification, final truncation transfer, and downstream FP spectral
  transfer.

- 2026-05-29: Closed the source-sharp square scaled-radius and Bennett-radius
  spectral conversion dependency for Algorithm 1.  New theorems:
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_square`
  and
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square`.
  These use the source-aligned `V = n*||Ahat||_F^2/s^2` route and no-`sqrt 2`
  support radius.  Remaining red bottleneck: simplify the explicit Bennett
  budget to the Drineas--Zouzias/CACM sample-complexity constants, then
  perform truncation and FP spectral transfer at those constants.

- 2026-05-29: Closed a conservative denominator fallback for the Algorithm 1
  source-sharp Bennett route.  New scalar theorems:
  `real_bennett_transform_lower_bound_two_add` and
  `real_bennett_budget_of_quadratic_denominator_two_add`; new Algorithm 1
  corollary:
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_sharp_square`.
  This proves the fully local `q <= r^2/(2W+L*r)` route.  It is weaker than
  the Drineas--Zouzias denominator `2W+(2/3)L*r`, so the final source-constant
  bottleneck remains open.

- 2026-05-29: Closed the sharper Algorithm 1 source denominator and sample
  budget route.  New scalar theorems:
  `real_bennett_transform_lower_bound_two_add_two_thirds` and
  `real_bennett_budget_of_quadratic_denominator_two_add_two_thirds`; new
  source sample/truncation/FP theorem family:
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square`,
  `sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square`, and
  `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square`.
  The exact source-budget Algorithm 1 equation (2) route is now closed through
  deterministic truncation.

- 2026-05-29: Closed the Algorithm 1 source-budget floating-point gamma-budget
  row.  New sampling support lemmas:
  `hitCount_le_steps`, `hitCount_eq_zero_of_forall_not_hit`,
  `fl_elementwiseTraceSketch_zero_init_eq_zero_of_forall_not_hit`, and
  `sqMagTraceErrorBudget_nonneg`; new support-aware spectral theorem:
  `fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb`; new
  final FP source-budget theorem:
  `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_square`.
  The theorem intersects the exact source-budget event with the sampler's
  probability-one positive-support event, derives the entrywise `gamma` budget
  locally with `Q=s`, and therefore no longer assumes an all-traces `hPoint`
  perturbation hypothesis.  The remaining Algorithm 1 gap is only the
  untruncated/general-rectangular CACM-prose variant, not the cited
  source-aligned square theorem.

- 2026-05-29: Advanced the equation (8) least-squares row after the Algorithm 1
  closure.  New bridge theorems:
  `rowSampleGramFullFpPerturbBudget_nonneg`,
  `eventProb_lsObjective_le_of_preserves`,
  `eventProb_lsObjective_le_one_add_eta_of_preserves`,
  `eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error`,
  `leverageTraceProbability_eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error`,
  and
  `leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_coordinate_quadratic_error`.
  These transfer the exact and fully floating-point leverage-score equation (7)
  operator events to the equation (8) sketched-minimizer objective guarantee,
  conditional on the residual-coordinate representation.  The paper-level
  equation (8) row remains open at the concrete sampled augmented-residual
  representation, sharper survey sample-complexity theorem, and downstream
  solver/preconditioner FP pipeline.

- 2026-05-29: Closed the concrete sampled-row algebra subrow for equation (8).
  New exact algebra/LS theorems:
  `vecNorm2Sq_add_quadraticForm_sub_id_eq_quadraticForm`,
  `vecNorm2Sq_rowSketch_linearCombination_eq_quadratic_rowSketchGram`,
  `vecNorm2Sq_rowSampleSketch_linearCombination_eq_quadratic_rowSampleGram`,
  `rowSampleLSMatrixWithBasisScale`, `rowSampleLSVectorWithBasisScale`,
  `rowSampleLSResidualWithBasisScale_eq_coord`,
  `rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error`, and
  `leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residual_coordinates`.
  These prove that the concrete Algorithm 2 sampled rows of `A` and `b`, scaled
  by leverage probabilities from `U`, have the expected coordinate quadratic
  objective whenever original residuals are represented in the rows of `U`.
  The equation (8) paper-level row remains open at constructing that
  residual-coordinate map from rectangular augmented-basis/rank/SVD/QR
  foundations, sharper survey sample complexity, and the FP solver pipeline.

- 2026-05-29: Advanced the equation (8) LS row one step further by replacing
  the arbitrary residual-coordinate map with canonical coordinates
  `U^T(Ax-b)` under an explicit column-space predicate.  New theorem names:
  `quadraticForm_idMatrix_eq_vecNorm2Sq`, `residualCoordinates`,
  `ResidualsInColumnSpace`,
  `lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace`,
  and
  `leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residualsInColumnSpace`.
  This closes the objective identity from canonical residual coordinates.  The
  remaining LS foundation is now sharper and more honest: prove an orthonormal
  augmented residual basis that satisfies `ResidualsInColumnSpace`, then prove
  the sharper subspace-embedding/sample-complexity theorem and integrate the
  downstream FP solver/preconditioner pipeline.

- 2026-05-29: Closed the identity-basis fallback for equation (8).  New names:
  `hasOrthonormalColumns_idMatrix`, `residualCoordinates_idMatrix`,
  `residualsInColumnSpace_idMatrix`, and
  `leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_idBasis`.
  This gives a concrete equation (6) theorem with `U = I_m`, uniform row
  probabilities, and dimension parameter `d = m`.  It is a valid fallback and
  a regression guard against hidden residual-coordinate assumptions, but it is
  not the survey's sharp low-dimensional augmented residual basis.

- 2026-05-29: Closed the column/RHS representation adapter for equation (8).
  New names: `ColumnsAndRhsInColumnSpace`, `residualCoordinatesFromColumns`,
  `residualsInColumnSpace_of_residual_representation`,
  `lsResidual_eq_basis_sum_of_columnsAndRhsInColumnSpace`, and
  `residualsInColumnSpace_of_columnsAndRhsInColumnSpace`.  This reduces the
  remaining LS basis foundation to a precise linear-algebra target: construct
  a sharp low-dimensional orthonormal `U` and coordinates for the augmented
  data matrix `[A b]`.

- 2026-05-29: Closed the augmented-span basis dependency for equation (8) by
  reusing Mathlib's finite-dimensional orthonormal-basis API.  New names:
  `euclideanVec`, `augmentedDataVector`, `augmentedDataSpan`,
  `augmentedDataVector_mem_span`, `augmentedSpanBasisMatrix`,
  `augmentedSpanColumnCoords`, `augmentedSpanRhsCoords`,
  `hasOrthonormalColumns_augmentedSpanBasisMatrix`,
  `columnsAndRhsInColumnSpace_augmentedSpanBasisMatrix`,
  `residualsInColumnSpace_augmentedSpanBasisMatrix`, and
  `leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan`.
  The concrete leverage-score sampled LS theorem now uses dimension
  `finrank ℝ (augmentedDataSpan A b)` with the expected positive-dimension
  hypothesis. Remaining LS paper-level work: sharper survey
  subspace-embedding/sample-complexity constants and downstream FP
  solver/preconditioner composition.

- 2026-05-29: Added the fully floating-point rounded-Gram objective-transfer
  corollaries for equation (8) after the augmented-span closure.  New names:
  `leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan`
  and `leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_idBasis`.
  These discharge the canonical residual-coordinate/original-objective side
  for the augmented-span and identity bases while keeping the rounded sketched
  objective representation explicit.  They do not close the sharper
  sample-complexity theorem or the implementation-backed FP solver pipeline.

- 2026-05-29: Advanced the source-sharp leverage-score equation (7) route by
  proving the one-step rank-one ingredients needed for an Oliveira/Tropp
  covariance concentration theorem.  New generic row-sampling names:
  `rowOuterGramSample_eq_zero_of_prob_zero`,
  `finiteQuadraticForm_rowOuterGramSample_eq_sq_div`, and
  `finitePSD_rowOuterGramSample`.  New leverage names:
  `leverage_rowOuterGramSample_finitePSD`,
  `leverage_rowOuterGramSample_mean_eq_id`, and
  `leverage_rowOuterGramSample_finiteLoewnerLe_nat`.  The sharp product-law
  concentration/sample-complexity theorem is still open and is the next
  leverage frontier.

- 2026-05-29: Added `RowSamplingTraceMGF.lean` for Algorithm 2 row-sampling
  product-law trace-MGF infrastructure.  New names include
  `rowSqNormSampleProbability`,
  `rowSqNormTraceProbability_expectationReal_trace_normed_exp_add_sum_le`,
  `rowSqNormTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le`,
  `rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound`, and
  `rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one`.
  This closes the row-trace independence/MGF/scalarization dependency for the
  sharper leverage equation (7) route; the centered leverage covariance
  one-sample log-CGF and final rank-one concentration theorem remain open.

- 2026-05-29: Added `RowSamplingLeverageMGF.lean` to instantiate the local
  generic centered C-star Bernstein log-CGF theorem for Algorithm 2 leverage
  covariance increments `rowOuterGramSample U i - I`.  New names include
  `rowOuterGramSample_centered_symmetric`,
  `leverage_rowOuterGramSample_centered_expectationCStarMatrix_eq_zero`,
  `leverage_rowOuterGramSample_centered_spectrum_le_nat`, and
  `leverage_rowOuterGramSample_centered_log_cgf_le`.  This closes the
  centered one-sample log-CGF dependency without assuming concentration.  The
  active leverage frontier is now the product-law rank-one tail theorem and
  source sample-size simplification.

- 2026-05-29: Continued `RowSamplingLeverageMGF.lean` through the exact
  variance, two-sided row-trace tail, Bennett sample-budget, and sharper
  floating-point finite-Loewner transfer layer.  New public names include
  `rowSampleGram_sub_finiteIdMatrix_eq_centered_rowOuterGramSample_average`,
  `leverage_rowOuterGramSample_centered_square_expectationCStarMatrix_eq`,
  `leverage_rowOuterGramSample_neg_centered_log_cgf_le`,
  `leverage_rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_centered_le`,
  `leverage_rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_neg_centered_le`,
  `leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_upper_lt_ge_one_sub_exp`,
  `leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_lower_lt_ge_one_sub_exp`,
  `leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_exp`,
  and
  `leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget`,
  `real_bernstein_tail_le_half_delta_of_quadratic_budget`,
  `leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_upper_ge_one_sub_delta_half_of_sample_budget`,
  `leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_lower_ge_one_sub_delta_half_of_sample_budget`,
  `leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`.
  The rank-one row-trace tail dependency, scalar Bennett sample-budget
  simplification, and sharper FP transfer are closed in finite-Loewner form.

- 2026-05-29: Continued equation (8) least-squares formalization by composing
  the new Algorithm 2 finite-Loewner Bennett sample-budget theorem with the
  sketched-minimizer objective bridge.  New public names include
  `preservesLSObjective_of_coordinate_finiteLoewner_error`,
  `eventProb_preservesLSObjective_of_coordinate_finiteLoewner_error`,
  `eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error`,
  `leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget`,
  and
  `leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan_sample_budget`.
  The exact Algorithm 2 leverage row-sampled LS theorem is closed in the
  source-aligned Bennett finite-Loewner sample-budget form; the FP theorem is a
  rounded-Gram transfer with an explicit `rowSampleGramFullFpPerturbBudget`
  radius and still requires a rounded sketched-objective representation.

- 2026-05-29: Added the first literal rounded sampled-row implementation
  foundation for equation (8) in `LeastSquaresSketch.lean`.  New public names
  include `fl_rowSampleLSMatrixWithBasisScale`,
  `fl_rowSampleLSVectorWithBasisScale`,
  `fl_rowSampleLSMatrixWithBasisScale_error_bound`,
  `fl_rowSampleLSVectorWithBasisScale_error_bound`,
  `fl_rowSampleLSResidualWithBasisScale_error_bound`, and
  `fl_rowSampleLSResidualWithBasisScale_error_bound_of_positiveProb`.  These
  model rounding the sampled/scaled entries of `A` and `b` by the local
  division FP primitive and prove the rowwise residual perturbation bound.

- 2026-05-29: Closed the deterministic objective-level lift for that literal
  rounded equation (8) construction.  New public names include shared vector
  lemmas `vecNorm2Sq_le_of_abs_le`, `vecNorm2_le_of_abs_le`, and
  `abs_vecNorm2Sq_add_sub_le`, plus LS bridges
  `lsObjective_residual_difference_bound`,
  `lsObjective_residual_budget_bound`, `rowSampleLSResidualFpBudget`,
  `rowSampleLSResidualFpBudget_nonneg`, and
  `fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb`.
  This was later closed under explicit objective-budget slack; the important
  guardrail remains that the concrete rounded `A,b` implementation is not
  claimed to automatically satisfy the older rounded-Gram representation.

- 2026-05-29: Closed the high-probability rounded-minimizer composition for
  the literal rounded sampled/scaled equation (8) construction under an
  explicit objective-budget slack condition.  New public names include
  `rowSampleLSObjectiveFpBudget`, `rowSampleLSObjectiveFpBudget_nonneg`,
  `fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget`,
  `lsObjective_le_of_sketch_preserves_with_objective_error`,
  `lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error`,
  `eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error`,
  `eventProb_lsObjective_le_one_add_eta_of_preserves_with_pointwise_objective_error`,
  `eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error_on_event`,
  `eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_on_event`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error`.
  This theorem reuses the exact finite-Loewner equation (7) concentration and
  the probability-one positive-support event; it still exposes the FP
  objective-budget slack as a hypothesis.  The remaining equation (8) work is
  downstream solver/preconditioner FP integration and random-projection
  variants.

- 2026-05-29: Closed the additive solver-objective-gap bridge for the same
  literal rounded sampled/scaled equation (8) construction.  New public names
  include `IsLeastSquaresApproxMinimizer`,
  `isLeastSquaresApproxMinimizer_of_minimizer`,
  `lsObjective_le_of_sketch_preserves_with_objective_error_and_solver_gap`,
  `lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error_and_solver_gap`,
  `eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error_and_solver_gap_on_event`,
  `eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_and_solver_gap_on_event`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_solver_gap`.
  This closes the composition theorem needed for approximate rounded solvers,
  but it deliberately keeps the solver objective gap explicit.  The next
  equation (8) frontier is deriving such a gap from a concrete QR,
  preconditioner, or iterative-solver FP theorem.

- 2026-05-29: Added the componentwise solver forward-error certificate bridge
  for the literal rounded sampled/scaled equation (8) construction.  New public
  names include `lsSolutionForwardResidualBudget`,
  `lsSolutionForwardObjectiveGap`,
  `lsResidual_difference_bound_of_solution_abs_le`,
  `lsObjective_solution_forward_error_bound`,
  `isLeastSquaresApproxMinimizer_of_solution_abs_le`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error`.
  A nonnegative componentwise certificate
  `|xHat samples j - xStar samples j| <= solverDx samples j` now induces an
  explicit additive rounded-objective gap and composes with the high-probability
  literal rounded sampled-row theorem.  The remaining equation (8) frontier is
  deriving that certificate, or an equivalent objective gap, from a concrete QR,
  preconditioner, or iterative-solver FP theorem.

- 2026-05-29: Added a perturbed-Gram-system solver certificate bridge for the
  same literal rounded sampled/scaled equation (8) construction.  New public
  names include `lsNormalMatrix`, `lsNormalRhs`, `gramForwardSolverDx`,
  `gramForwardSolverDx_nonneg`,
  `gram_forward_error_certificate_of_perturbed_gram_system`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_perturbed_gram_solver`.
  This reuses the local `gram_forward_error_normwise` theorem to turn explicit
  perturbations of the rounded normal equations into the `solverDx` certificate
  consumed by the high-probability theorem.  The remaining solver frontier is
  now specifically to derive those perturbed Gram equations and radii from a
  concrete QR, preconditioner, or iterative solver implementation.

- 2026-05-29: Added the QR least-squares backward-error-spec adapter for the
  same equation (8) solver frontier.  New public names include
  `abs_entry_le_frobNorm`, `lsQRSolveBackwardSolverDx`,
  `lsQRSolveBackwardSolverDx_nonneg`,
  `gram_forward_error_certificate_of_ls_qr_solve_backward_error`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver`.
  This consumes the existing local `LSQRSolveBackwardError` structure, converts
  its Frobenius `ΔG` radius to entrywise control, and feeds the already proved
  solver-certificate transfer.  It is still a spec adapter, not a proof that a
  concrete QR/preconditioner implementation satisfies the spec.

- 2026-05-30: Added a concrete normal-equations/Cholesky solver route for the
  literal rounded sampled/scaled equation (8) construction.  New public names
  include `normalEqCholeskyXHat`, `normalEqCholeskyGramBound`,
  `normalEqCholeskyRhsBound`, `normalEqCholeskySolverDx`,
  `normalEqCholeskySolverDx_nonneg`,
  `normal_equations_cholesky_forward_error_certificate`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_normal_eq_cholesky_solver`.
  This reuses the local `ls_normal_equations_backward` and
  `ls_normal_equations_forward_error` theorems to produce the solver
  certificate.  It closes a concrete solver path, but not the separate
  rectangular QR/preconditioner implementation theorem.

- 2026-05-30: Recorded the remaining equation (8) solver item as red
  bottleneck `LS.8-rectangular-QR`.  Local search confirms that
  `LSQRSolveBackwardError` is a specification because the repository does not
  yet have a rectangular QR/Householder least-squares backward-error theorem.
  External proof-source acquisition points to Higham, *Accuracy and Stability
  of Numerical Algorithms*, chapters 19--20, and Cox--Higham's weighted least
  squares Householder QR analysis as the right mathematical route; these are
  sources to formalize from, not assumptions that close the theorem.

- 2026-05-30: Closed one dependency of `LS.8-rectangular-QR`:
  `rectLSNormalEquations_perturbed_to_gram_system` and
  `LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations` now turn
  perturbed rectangular normal equations plus induced Gram/RHS radii into the
  local `LSQRSolveBackwardError` spec.  The remaining red dependency is the
  concrete rectangular Householder QR/preconditioner FP theorem itself.

- 2026-05-30: Closed another listed dependency of
  `LS.8-rectangular-QR`: `rectLSGramPerturbation_eq_sum`,
  `rectLSRhsPerturbation_eq_sum`,
  `rectLSGramPerturbation_abs_le_entryBudget`,
  `rectLSRhsPerturbation_abs_le_entryBudget`,
  `rectLSGramPerturbation_frobNorm_le_entryBudget`,
  `rectLSGramPerturbation_abs_le_normBudget`,
  `rectLSRhsPerturbation_abs_le_normBudget`, and
  `rectLSGramPerturbation_frobNorm_le_normBudget` expand the induced
  rectangular Gram/RHS perturbations and bound them from exact entry budgets
  or coarse data perturbation radii.  The red blocker is now specifically the
  concrete rectangular QR/preconditioner theorem supplying perturbed
  rectangular normal equations and rectangular data perturbation bounds.

- 2026-05-30: Added the norm-budget handoff theorem
  `LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations_normBudget`.
  It packages perturbed rectangular normal equations, normwise data
  perturbation radii, and the induced Gram/RHS budget bounds into the local
  `LSQRSolveBackwardError` specification.  This closes the adapter layer; the
  remaining red dependency is still the concrete rectangular QR/preconditioner
  implementation theorem itself.

- 2026-05-30: Closed small route-A algebra dependencies for the rectangular
  QR bottleneck: `matMulRectLeft`, `matMulRectRight`,
  `frobNormSqRect_orthogonal_left`, `frobNormRect_orthogonal_left`,
  `frobNormSqRect_orthogonal_right`, and
  `frobNormRect_orthogonal_right` now prove that compatible orthogonal square
  left and right factors preserve the rectangular Frobenius norm.  The concrete
  rectangular Householder QR/preconditioner theorem is still open.

- 2026-05-30: Closed the companion rectangular Frobenius norm-growth
  dependency: `frobNormRect_eq_frobNormFn`,
  `frobNormRect_matMulRectLeft_le`, and
  `frobNormRect_matMulRectRight_le` reuse Mathlib's Frobenius
  submultiplicativity for compatible square left/right factors.  This is
  route-A substrate for a rectangular one-step Householder/orthogonal
  perturbation-accumulation proof, not the concrete QR theorem itself.

- 2026-05-30: Closed the rectangular square-left-action algebra dependency:
  `matMulRectLeft_id`, `matMulRectLeft_assoc`,
  `matMulRectLeft_add_left`, and `matMulRectLeft_add_right`.  These are the
  exact identity/associativity/additivity facts needed by the rectangular
  one-step orthogonal-transformation accumulation proof.

- 2026-05-30: Closed the rectangular one-step orthogonal-transformation
  accumulation theorem `rect_orthogonal_sequence_one_step` in
  `Algorithms/QR/HouseholderQR.lean`.  It generalizes the square
  Householder one-step proof to `m × n` data and gives the rectangular
  Frobenius growth bound.  The remaining red QR bottleneck is the multi-step
  rectangular Householder/preconditioner theorem and solve handoff, not this
  one-step algebra.

- 2026-05-30: Closed the supplied-transformation multi-step rectangular
  accumulation theorem `rect_orthogonal_sequence_geometric`.  It iterates the
  one-step theorem and proves the rigorous geometric radius
  `((1+c)^r - 1) ||A||_F`.  This is not yet a concrete `fl_householder_qr`
  implementation or rectangular solve theorem.

- 2026-05-30: Closed the orthogonal least-squares handoff:
  `rectLSGram_matMulRectLeft_orthogonal`,
  `rectLSRhs_matMulRectLeft_orthogonal`, and
  `RectLSNormalEquations.of_orthogonal_left`.  Orthogonal row transformations
  preserve the rectangular Gram matrix, RHS, and normal equations, so a future
  rectangular QR theorem can feed the existing `RectLSNormalEquations` bridge.

- 2026-05-30: Closed the vector/right-hand-side companion to the rectangular
  QR accumulation route.  `vecNorm2Sq_orthogonal`, `vecNorm2_orthogonal`,
  `matMulVec_id`, `matMulVec_add_left`, and `matMulVec_add_right` provide the
  shared vector algebra; `orthogonal_vector_sequence_one_step` and
  `orthogonal_vector_sequence_geometric` prove the supplied-transformation
  perturbation accumulation for `b` with radius
  `((1+c)^r - 1) ||b||_2`.  This closes the transformed-RHS dependency, but
  not the concrete rectangular `fl_householder_qr` / triangular solve theorem.

- 2026-05-30: Closed the exact top-block QR solve handoff:
  `RectLSNormalEquations.of_rowwise_normal` and
  `RectLSNormalEquations.of_top_solve_zero_bottom`.  If transformed QR data has
  top block `R`, zero lower matrix block, and the computed vector solves
  `R x = c`, then it satisfies the rectangular normal equations for the
  transformed problem; the lower transformed RHS is unrestricted.  This still
  leaves the concrete floating-point rectangular Householder/preconditioner
  implementation and rounded triangular solve theorem open.

- 2026-05-30: Closed the rounded top-block triangular solve handoff using the
  existing `backSub_backward_error` theorem.  `rectTopBlock` embeds an `n x n`
  top block into an `m x n` zero-lower matrix, and
  `RectLSNormalEquations.exists_topBlock_of_fl_backSub` proves that
  `fl_backSub fp n R c` satisfies rectangular normal equations for the
  perturbed top block `R + Delta R` with
  `|Delta R_ij| <= gamma fp n * |R_ij|`.  The red QR bottleneck is now the
  concrete rectangular Householder/preconditioner implementation and
  transformed-RHS/top-block shape theorem.

- 2026-05-30: Closed the common-orthogonal-factor accumulation substrate for
  the red rectangular QR bottleneck.  The new
  `rect_orthogonal_matrix_vector_sequence_one_step` and
  `rect_orthogonal_matrix_vector_sequence_geometric` theorems apply the same
  supplied perturbed orthogonal transformations to an `m x n` matrix and an
  `m`-vector, producing one shared orthogonal factor `Q` plus perturbations
  `Delta A`, `Delta b` with geometric radii.  This avoids combining unrelated
  existential `Q`s from separate matrix/vector accumulation theorems.  The
  remaining red dependency is the pulled-back top-block/triangular-solve QR
  theorem and then a concrete `fl_householder_qr`/preconditioner
  implementation.

- 2026-05-30: Closed the pulled-back top-block triangular-solve dependency.
  `RectLSNormalEquations.exists_original_perturbation_of_commonQ_topBlock_fl_backSub`
  combines common-`Q` transformed data, `[R;0]` top-block shape,
  `fl_backSub`, and the orthogonal normal-equation handoff.  It produces
  `Delta A_total = Delta A + Q [Delta R;0]`, proves rectangular normal
  equations for `(A+Delta A_total,b+Delta b)`, and bounds
  `||Delta A_total||_F` by `||Delta A||_F + ||[Delta R;0]||_F`.  The
  concrete rectangular Householder/preconditioner implementation remains open.

- 2026-05-30: Closed the embedded top-block norm-budget dependency.  Added
  `frobNormSqRect_abs` and `frobNormRect_abs` in `MatrixAlgebra.lean`, plus
  `rectTopBlock_frobNorm_perturb_bound`,
  `rectTopBlock_frobNorm_perturb_bound_of_gamma`, and
  `RectLSNormalEquations.exists_original_perturbation_of_commonQ_topBlock_fl_backSub_gamma_bound`
  in `LSQRSolve.lean`.  The strengthened pullback theorem now bounds
  `||Delta A_total||_F <= ||Delta A||_F + gamma fp n ||[R;0]||_F`, so the
  red QR bottleneck is narrowed to the concrete rectangular
  Householder/preconditioner implementation theorem.

- 2026-05-30: Closed the supplied-transform route into the local QR
  least-squares solver specification.  Added
  `LSQRSolveBackwardError.of_commonQ_topBlock_fl_backSub_gamma_bound_normBudget`
  and
  `LSQRSolveBackwardError.of_rect_orthogonal_sequence_topBlock_fl_backSub_gamma_bound_normBudget`.
  These compose the common-`Q` top-block pullback, rounded `fl_backSub`,
  gamma top-block norm budget, and rectangular induced Gram/RHS norm-budget
  adapter into `LSQRSolveBackwardError`.  This is still a supplied-transform
  theorem; a concrete `fl_householder_qr`/preconditioner implementation
  theorem remains the active red bottleneck.

- 2026-05-30: Closed the first exact embedded-reflector substrate for the
  concrete rectangular Householder QR route.  Added
  `householder_row_eq_id_of_zero_prefix`,
  `householder_col_eq_id_of_zero_prefix`,
  `matMulVec_householder_eq_self_of_zero_prefix`,
  `matMul_householder_eq_self_row_of_zero_prefix`, and
  `matMulRectLeft_householder_eq_self_row_of_zero_prefix` in
  `HouseholderSpec.lean`.  These prove that a full-size Householder reflector
  whose vector vanishes on a prefix acts as the identity on that prefix for
  rows, columns, vectors, and square/rectangular matrix rows.  Remaining
  route-A foundations are active-column zeroing for the constructed reflector
  and a common rounded panel/update theorem for applying the same reflector to
  both `A` and `b`.
- 2026-05-30: Closed the exact active-column Householder substrate for the
  concrete rectangular QR route.  Added `householderActiveVector`,
  `householderBeta`, `householderActiveVector_inner_x`,
  `householderActiveVector_inner_self`,
  `householderActiveVector_inner_self_eq_two_inner_x`,
  `householderBeta_mul_activeVector_inner_x`,
  `matMulVec_householder_activeVector_eq_alpha_basis`, and
  `matMulVec_householder_activeVector_eq_zero_of_ne`.  These prove that the
  exact reflector built from `v = x - alpha e_p` maps `x` to `alpha e_p`, and
  hence zeros off-pivot active-column entries, under explicit
  `alpha^2 = ||x||_2^2` and `v^T v != 0`.  The remaining route-A foundation is
  the common rounded panel/update theorem for applying the same reflector to
  both `A` and `b`, followed by concrete rectangular implementation assembly.
- 2026-05-30: Corrected and narrowed the common rounded panel/update interface
  for the rectangular QR route.  Added `HouseholderPanelAppError`, a stronger
  contract than vector-only `HouseholderAppError`, requiring one shared
  perturbation matrix `Delta P` for both the rectangular matrix-panel update
  and the right-hand-side update.  Added
  `householderPanelAppError_rect_orthogonal_matrix_vector_sequence_geometric`,
  which feeds a sequence of these contracts into the existing common-`Q`
  accumulation theorem.  The remaining red-bottleneck dependency is now the
  low-level floating-point Householder panel implementation proof that
  discharges `HouseholderPanelAppError`, then the final rectangular QR assembly.
- 2026-05-30: Corrected the active rectangular QR route after checking
  Higham's columnwise Householder QR proof source.  The shared-`Delta P`
  contract remains as a strong optional interface, but the source-faithful
  theorem permits a different perturbation matrix for each panel column.
  Added `HouseholderColumnwisePanelAppError`,
  `HouseholderColumnwisePanelAppError.of_vector_applications`,
  `orthogonal_vector_sequence_one_step_fixedQ`,
  `rect_orthogonal_columnwise_vector_sequence_geometric`, and
  `householderColumnwisePanelAppError_rect_orthogonal_columnwise_vector_sequence_geometric`.
  The active red-bottleneck dependency is now the low-level rounded
  Householder vector-application theorem proving `HouseholderAppError` for an
  actual `fl_householder_apply` primitive, then the final rectangular QR
  assembly.
- 2026-05-30: Closed the exact algebraic adapter dependency for the active
  rectangular QR bottleneck.  Added rank-one norm bridges
  `frobNormSq_rankOne`, `frobNorm_rankOne`, `frobNorm_rankOne_smul`, and
  `frobNorm_rankOne_div_vecNorm2Sq` in `MatrixAlgebra.lean`, plus
  `HouseholderAppError.of_forward_error` and
  `HouseholderColumnwisePanelAppError.of_forward_errors` in
  `HouseholderSpec.lean`.  This converts a future rounded Householder
  primitive forward-error theorem into the local backward-error contracts
  without a hidden nonzero-input hypothesis.  The active remaining dependency
  is now the actual rounded dot/scale/subtract primitive forward-error theorem,
  then final rectangular QR/preconditioner assembly.
- 2026-05-30: Closed a concrete explicit-matrix rounded Householder
  application route.  Added `vecNorm2Sq_abs` and `vecNorm2_abs` in
  `MatrixAlgebra.lean`, and created `Algorithms/QR/HouseholderApply.lean`
  with `fl_householderApplyExplicit`, `fl_householderApplyExplicitPanel`,
  `fl_householderApplyExplicit_forward_error_bound`,
  `fl_householderApplyExplicit_HouseholderAppError`, and
  `fl_householderApplyExplicitPanel_HouseholderColumnwisePanelAppError`.
  This route reuses `fl_matVec`/`matVec_error_bound` for an already formed
  reflector matrix and instantiates the vector and columnwise contracts.  The
  compact dot/scale/subtract Householder primitive and final rectangular QR
  assembly remain open.
- 2026-05-30: Closed the compact rounded Householder dot/scale/subtract vector
  primitive dependency.  `Algorithms/QR/HouseholderApply.lean` now contains
  `householderDot`, `householderAbsDotBudget`,
  `fl_householderApplyCompact`, `fl_householderApplyCompactPanel`,
  `householderCompactComponentBudget`, `matMulVec_householder_eq_compact`,
  `fl_householderApplyCompact_componentwise_error_bound`,
  `fl_householderApplyCompact_forward_error_bound`,
  `fl_householderApplyCompact_HouseholderAppError_of_budget`, and
  `fl_householderApplyCompactPanel_HouseholderColumnwisePanelAppError_of_budget`.
  The budget is explicit and deterministic; the relative contract uses a
  visible budget-domination condition, not a hidden concentration/stability
  hypothesis.  The active red bottleneck is now only the final rectangular
  Householder QR/preconditioner assembly: instantiate compact applications
  across the panel/RHS, prove transformed `[R;0]` and top-RHS linkage, and
  compose the pulled-back perturbation/triangular-solve handoff.
- 2026-05-30: Closed the compact sequence-glue dependency for the rectangular
  QR bottleneck.  `HouseholderQR.lean` now imports `HouseholderApply.lean` and
  proves
  `fl_householderApplyCompactPanel_rect_orthogonal_columnwise_vector_sequence_geometric`:
  any supplied sequence of compact rounded panel/RHS Householder updates whose
  explicit budgets are dominated by `c` feeds the existing source-faithful
  columnwise geometric accumulation theorem.  This supplies a common
  accumulated orthogonal factor and column/RHS perturbation radii, but still
  assumes the QR loop's concrete reflector sequence and transformed `[R;0]`
  shape/top-RHS invariants.
- 2026-05-30: Closed the compact sequence-to-solver-spec handoff dependency.
  `MatrixAlgebra.lean` now has
  `frobNormSqRect_eq_sum_vecNorm2Sq_cols` and
  `frobNormRect_le_of_col_vecNorm2_le`, converting columnwise Euclidean
  perturbation bounds into a rectangular Frobenius bound.  `LSQRSolve.lean`
  now proves
  `LSQRSolveBackwardError.of_compact_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`,
  composing the compact Householder sequence theorem with the existing
  top-block `fl_backSub` pullback into the local `LSQRSolveBackwardError`
  interface.  The active red bottleneck is now narrowed to the concrete loop
  invariants that prove the final `[R;0]` shape, top-RHS linkage, and
  triangular/nonzero-diagonal facts for the actual rectangular Householder or
  preconditioner implementation.
- 2026-05-30: Closed the exact trailing Householder shape dependency for the
  rectangular QR bottleneck.  `HouseholderSpec.lean` now has
  `householderPrefixPart`, `householderTrailingPart`,
  `householderTrailingNorm2Sq`, `householderTrailingActiveVector`,
  support/split lemmas,
  `matMulVec_householder_eq_self_of_zero_prefix_support`,
  `matMulVec_householder_trailingActiveVector_eq_prefix_alpha_zero`, and
  `matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt`.
  `HouseholderQR.lean` now proves
  `exact_trailing_householder_sequence_lower_zero` and
  `rectangular_topBlock_shape_facts_of_lower_zero`.  This corrects the exact
  QR shape route: the reflector vector is built from the trailing pivot
  segment with a zero prefix, preserving entries above the pivot and zeroing
  entries below it.  The remaining red dependency is the rounded stored-`R`/RHS
  compact loop assembly plus a formal nonzero-diagonal/rank or nonbreakdown
  condition.
- 2026-05-30: Closed the stored rounded QR shape dependency with
  `fl_householderStoredPanelStep`, `fl_householderStoredRhsStep`,
  `fl_householderStoredPanel_sequence_lower_zero`, and
  `fl_householderStoredPanel_sequence_topBlock_shape_facts`.  The stored panel
  step preserves completed columns and explicitly writes zeros below each pivot,
  so final `[R;0]`, `cTop`, and upper-triangular facts are now available for
  the rounded loop shape.  The remaining red dependency is the stored-step
  `HouseholderColumnwisePanelAppError` perturbation theorem plus
  nonzero-diagonal/rank or nonbreakdown.
- 2026-05-30: Closed the stored-step perturbation contract dependency with
  `householderCompactComponentBudget_nonneg`,
  `fl_householderStoredRhsStep_componentwise_error_bound`,
  `fl_householderStoredRhsStep_forward_error_bound`,
  `fl_householderStoredPanelStep_column_componentwise_error_bound`,
  `fl_householderStoredPanelStep_column_forward_error_bound`, and
  `fl_householderStoredPanelStep_HouseholderColumnwisePanelAppError_of_budget`.
  The theorem proves that the stored panel/RHS step satisfies the
  source-faithful columnwise Householder contract under explicit
  preservation, pivot-zeroing, RHS-prefix, and budget-domination hypotheses.
  The remaining red dependency is the concrete trailing-reflector loop theorem
  that discharges those hypotheses for each step, plus the nonzero
  diagonal/rank or nonbreakdown condition.
- 2026-05-30: Closed the one-step concrete trailing-reflector discharge
  dependency with
  `fl_householderStoredTrailingPanelStep_HouseholderColumnwisePanelAppError_of_budget`.
  The theorem uses the pre-step lower-zero invariant and the exact trailing
  Householder algebra to discharge completed-column preservation, RHS-prefix
  preservation, and pivot-column zeroing for one stored rounded QR step.  The
  remaining red dependency is the multi-step stored trailing loop theorem that
  invokes this step theorem at every pivot and the nonzero diagonal/rank or
  nonbreakdown condition.
- 2026-05-30: Closed the multi-step stored trailing Householder perturbation
  dependency with
  `fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric`.
  The theorem maintains the stored lower-zero invariant, invokes the one-step
  trailing-reflector theorem at each pivot, and feeds the resulting
  columnwise contracts into the common-`Q` geometric accumulation theorem.  It
  yields one orthogonal factor, columnwise data perturbation radii
  `((1+c)^n-1)||A(:,j)||_2`, and RHS radius `((1+c)^n-1)||b||_2`.  The active
  red dependency is now the stored-loop solver-spec handoff into
  `LSQRSolveBackwardError`, plus the nonzero diagonal/rank or nonbreakdown
  condition.
- 2026-05-30: Closed the stored trailing Householder loop solver-spec handoff
  with
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`.
  The theorem reads the final `R` and `cTop` from `A_hat n` and `b_hat n`,
  reuses `fl_householderStoredPanel_sequence_topBlock_shape_facts` and
  `fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric`,
  converts the columnwise data radii to Frobenius form, and invokes the
  existing common-`Q`/top-block `fl_backSub` pullback into
  `LSQRSolveBackwardError`.  The active red dependency is now exactly the
  nonzero diagonal/rank or nonbreakdown proof for the computed top block.
- 2026-05-30: Reduced the stored QR nonzero-diagonal bottleneck to a concrete
  per-pivot FP nonbreakdown condition with
  `fl_householderStoredTrailingPanelStep_diag_nonzero_of_budget_lt_abs_alpha`,
  `fl_householderStoredPanel_sequence_diag_nonzero_of_step_diag_nonzero`,
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_budget_lt_abs_alpha`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_error_lt_abs_alpha`.
  The new route proves final top-block diagonal nonzeroness whenever each
  stored diagonal component budget is strictly smaller than `|alpha_k|`.  The
  active red dependency is now deriving those inequalities from a formal
  rank/conditioning/nonbreakdown invariant.
- 2026-05-30: Reduced the stored QR Householder denominator side condition
  `v^T v != 0` to the scalar pivot condition `A_hat[k,k] != alpha_k`.
  The new theorem
  `householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha`
  proves denominator nonzeroness for the trailing active vector; the stored QR
  theorem `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_pivot_ne_alpha`
  and the LSQRSolve wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_ne_alpha_and_pivot_error_lt_abs_alpha`
  compose it with the existing pivot-budget nonbreakdown bridge.  This is not
  a rank theorem; deriving `A_hat[k,k] != alpha_k` and
  `budget_k < |alpha_k|` from rank/conditioning remains open.
- 2026-05-30: Reduced the scalar stored QR pivot condition
  `A_hat[k,k] != alpha_k` to the standard Householder sign-choice facts.  New
  theorems
  `householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos` and
  `householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos`
  prove denominator nonzeroness from
  `alpha_k^2 = ||A_hat_k(k:m,k)||_2^2`, positive trailing norm, and
  `alpha_k * A_hat[k,k] <= 0`; the stored QR theorem
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_trailingNorm_pos_mul_nonpos`
  and the LSQRSolve wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_trailingNorm_pos_mul_nonpos_and_pivot_error_lt_abs_alpha`
  compose this with the existing pivot-budget nonbreakdown bridge.  The active
  red dependency is now deriving positive trailing-column norms and
  `budget_k < |alpha_k|` from rank/conditioning/nonbreakdown.
- 2026-05-30: Added scalar lower-bound bridges for the remaining stored QR
  nonbreakdown route.  `householderTrailingNorm2Sq_pos_of_exists_ne` and
  `householderTrailingNorm2Sq_pos_of_pivot_ne_zero` reduce positive active
  trailing norm to a concrete nonzero trailing entry; `abs_alpha_eq_sqrt_trailingNorm2Sq`
  and `budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq` convert square-root
  trailing-norm lower bounds into the stored-loop condition
  `budget_k < |alpha_k|`.  The red dependency is now specifically a
  rank/conditioning/nonbreakdown invariant that supplies those two scalar
  facts for the computed loop.
- 2026-05-30: Added the first prefix-span bridge for the stored QR rank route.
  `qrColumnNotInPreviousSpan` plus
  `qrPrefixSupportSpannedByPreviousColumns` imply a nonzero active trailing
  entry by `exists_active_trailing_entry_ne_of_column_notInPreviousSpan`, hence
  positive trailing norm by
  `householderTrailingNorm2Sq_pos_of_column_notInPreviousSpan`.  The stored QR
  wrapper
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_sqrt_budget`
  combines prefix-span/column-independence, sign choice, and square-root budget
  into final nonzero diagonal entries.  Remaining QR rank work: prove the
  prefix-span and column-independence invariants, and budget lower bounds, from
  an invertible triangular/full-rank/nonbreakdown assumption.
- 2026-05-30: Added a prefix-span coefficient bridge for the stored QR rank
  route.  `qrPrefixBasisCoefficientMatrix` records concrete leading-block
  coefficients reproducing the prefix coordinate basis vectors, and
  `qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix`
  proves that this witness plus the QR lower-zero shape supplies
  `qrPrefixSupportSpannedByPreviousColumns`.  The remaining rank bottleneck is
  now producing those coefficient witnesses from a nonsingular/right-invertible
  leading block, proving current-column independence, and obtaining budget
  lower bounds.
- 2026-05-30: Added a leading-column left-inverse bridge for the same QR route.
  `qrLeadingColumnLeftInverse` records a dual coefficient family selecting the
  first `k+1` columns, and
  `qrColumnNotInPreviousSpan_of_leadingColumnLeftInverse` proves
  `qrColumnNotInPreviousSpan`.  Remaining QR rank work is producing the
  basis/left-inverse witnesses from a full-rank or triangular nonbreakdown
  invariant, plus quantitative budget lower bounds.
- 2026-05-30: Composed the QR coefficient and left-inverse witness bridges.
  `exists_active_trailing_entry_ne_of_leading_witnesses`,
  `householderTrailingNorm2Sq_pos_of_leading_witnesses`, and
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_witnesses_sqrt_budget`
  prove active trailing nonbreakdown and stored-loop diagonal nonbreakdown from
  concrete leading witnesses plus the visible square-root budget.  This removes
  the abstract prefix-span/column-independence hypotheses from that stored-loop
  theorem but still does not derive the witnesses or the quantitative budget
  lower bound from full rank alone.
- 2026-05-30: Added the QR leading-block inverse orientation adapter.
  `qrPreviousLeadingBlockTranspose` names the transposed leading block and
  `qrPrefixBasisCoefficientMatrix_of_leftInverse_previousLeadingBlockTranspose`
  reuses the repository's `IsLeftInverse` predicate to produce the prefix
  coefficient witness.  This closes the coefficient-witness-from-inverse
  adapter but still does not prove existence of that inverse from rank or
  triangular nonbreakdown.
- 2026-05-30: Added the QR leading-block inverse padding adapter.
  `qrLeadingBlock` names the actual leading `(k+1) x (k+1)` block and
  `qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock` pads a local
  `IsLeftInverse` witness by zeros outside the first `k+1` rows to produce
  the ambient `qrLeadingColumnLeftInverse` witness.  This closes the finite
  ambient-row bookkeeping for column independence, but still does not prove
  that the local leading block inverse exists from a rank/triangular invariant.
- 2026-05-30: Added the QR local-inverse composition bridge.
  `exists_active_trailing_entry_ne_of_leading_block_leftInverses`,
  `householderTrailingNorm2Sq_pos_of_leading_block_leftInverses`, and
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_leftInverses_sqrt_budget`
  let the stored QR nonbreakdown route consume local `IsLeftInverse` witnesses
  for the previous and current leading blocks directly.  Remaining open
  dependencies are existence of those local inverses from a formal rank or
  triangular invariant and a square-root trailing-norm budget lower bound.
- 2026-05-30: Added the determinant/rank bridge for those QR local inverse
  witnesses.  `nonsingInv`, `isLeftInverse_nonsingInv_of_det_isUnit`, and
  `exists_isLeftInverse_of_det_ne_zero` wrap Mathlib's nonsingular inverse and
  convert nonzero determinants into the repository's `IsLeftInverse`
  predicate.  The QR wrappers
  `qrPrefixBasisCoefficientMatrix_of_det_ne_zero_previousLeadingBlockTranspose`,
  `qrLeadingColumnLeftInverse_of_det_ne_zero_leadingBlock`,
  `exists_active_trailing_entry_ne_of_leading_block_det_ne_zero`,
  `householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero`, and
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_det_ne_zero_sqrt_budget`
  replace raw inverse-witness assumptions by nonzero determinants of the local
  leading blocks.  Remaining open dependencies are determinant/rank
  preservation for the computed leading blocks and the square-root
  trailing-norm budget lower bound.  The determinant/rank bridge itself has
  two weak-component passes.
- 2026-05-30: Added the triangular determinant route for QR local leading
  blocks.  `det_ne_zero_of_upper_triangular_diag_ne_zero` and
  `det_ne_zero_of_lower_triangular_diag_ne_zero` are shared MatrixAlgebra
  lemmas; `qrPreviousLeadingBlockTranspose_det_ne_zero_of_upper_triangular_diag_ne_zero`
  and `qrLeadingBlock_det_ne_zero_of_upper_triangular_diag_ne_zero` instantiate
  them for the QR blocks.  This is a visible principal-minor/nonzero-diagonal
  route, not a generic full-rank theorem.  It has two clean weak-component
  passes; the red QR bottleneck now needs either an explicit route choice to
  keep these local assumptions visible or a source-faithful prefix-span/full-rank
  invariant plus a square-root trailing-norm budget lower bound.
- 2026-05-30: Added a solver-facing nonsingular-leading-block QR wrapper:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_block_det_ne_zero_sqrt_budget`.
  It feeds nonzero local leading-block determinants, QR lower-zero shape, sign
  choice, square-root pivot budgets, compact panel/RHS budget domination, and
  final Gram/RHS norm budgets into the local `LSQRSolveBackwardError`
  certificate.  This dependency has two clean weak-component passes;
  determinant/rank facts and the square-root budget lower bound remain the
  active red bottleneck.
- 2026-05-30: Added and two-pass validated the triangular-leading-block QR solver wrapper:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_sqrt_budget`.
  It composes the triangular determinant adapters with the solver-facing
  nonsingular-leading-block certificate, so visible upper-triangular local
  shape plus nonzero previous/current leading diagonals can feed
  `LSQRSolveBackwardError` directly.  This is a domain theorem, not a generic
  full-rank result; the source-faithful rank/conditioning route and
  square-root budget lower bound remain open.  The second PDF validation used
  a Ghostscript-repaired exact-path PDF artifact because the raw pdfTeX output
  triggered Poppler page-tree warnings after page 79.
- 2026-05-30: Added and two-pass validated the active-entry square-root budget bridge in
  `HouseholderSpec.lean`: `abs_entry_le_sqrt_householderTrailingNorm2Sq_of_pivot_le`
  and `budget_lt_sqrt_householderTrailingNorm2Sq_of_lt_abs_active_entry`.
  These reuse the local coordinate-to-vector norm bound to show that
  `budget < |x_i|` for an active trailing entry implies the square-root
  trailing-norm budget.  This is progress on the QR red bottleneck, but it
  still leaves the source-faithful lower-bound derivation from rank,
  nonbreakdown, or conditioning open.
- 2026-05-30: Added the stored-loop active-entry-budget QR nonbreakdown wrapper
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_active_entry_budget`
  in `HouseholderQR.lean`.  It uses the active-entry scalar bridge to remove the
  square-root expression from the prefix-span stored-loop wrapper, while keeping
  the active-entry magnitude lower bound visible as a domain/nonbreakdown
  condition.  It now has two clean weak-component passes.
- 2026-05-30: Added the solver-facing active-entry-budget QR wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_active_entry_budget`
  in `LSQRSolve.lean`.  It feeds prefix-span nonbreakdown, sign choice,
  Householder normalization, compact panel/RHS budget domination, a visible
  active-entry magnitude budget, and final Gram/RHS budgets into the local
  `LSQRSolveBackwardError` certificate.  It now has two clean weak-component
  validation passes.  The remaining red bottleneck is the source-faithful
  derivation of the active-entry lower bound from rank, nonbreakdown, or
  conditioning, or an explicit route choice to keep that lower bound visible.
- 2026-05-30: Added and two-pass validated the dimensioned norm-square-budget
  bridge for the same QR bottleneck.  The lemma
  `exists_active_entry_budget_lt_abs_of_dim_mul_budget_sq_lt_trailingNorm2Sq`
  proves that `m * budget^2 < trailingNorm2Sq` gives an active entry with
  `budget < |x_i|`.  The stored-loop wrapper
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget`
  and solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_trailingNorm2Sq_budget`
  use this to replace the raw active-entry witness by a dimensioned per-pivot
  norm-square margin.  This is not a conditioning theorem; the next red
  dependency is deriving that margin from a formal conditioning/nonbreakdown
  invariant, or explicitly keeping it as a domain assumption.
- 2026-05-30: Added and two-pass validated the leading-dual norm lower-bound
  route.  The lemma
  `householderTrailingNorm2Sq_ge_inv_leading_dual_norm_budget` proves that a
  prefix-span invariant plus a pivot-selecting leading dual row with
  `||L_last||_2^2 <= K` yields `1 / K <= trailingNorm2Sq`.  The stored-loop
  and solver wrappers
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leading_dual_norm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leading_dual_norm_budget`
  feed this into QR diagonal nonbreakdown and the local least-squares
  `LSQRSolveBackwardError` certificate under `m * budget_k^2 < 1 / K_k`.  This
  narrows the quantitative red bottleneck to constructing/bounding that dual
  from a concrete inverse/conditioning theorem, or keeping the dual-norm budget
  visible.
- 2026-05-30: Added and two-pass validated the local leading-block inverse
  row-norm route.  The new padding lemmas
  `vecNorm2Sq_qrLeadingRow_padded_eq` and
  `qrLeadingColumnLeftInverse_padded_row_norm_sq_eq` convert the last row of a
  local left inverse for `qrLeadingBlock` into the ambient dual row without
  changing squared norm.  The stored-loop wrapper
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
  and solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
  now feed the local inverse row budget into QR nonbreakdown and
  `LSQRSolveBackwardError`.  This still leaves deriving the inverse-row norm
  budget from determinant margins, SVD, condition number, or inverse-norm
  hypotheses as the active red-bottleneck dependency.
- 2026-05-30: Added and two-pass validated the local leading-block inverse
  Frobenius-norm route.  Shared matrix algebra now has
  `vecNorm2Sq_row_le_frobNormSq` and `vecNorm2Sq_row_le_frobNorm_sq`; QR/LS
  wrappers
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`
  use the local inverse Frobenius budget `||C_k||_F^2 <= K_k` plus
  `m * budget_k^2 < 1 / K_k`.  Validation used a targeted `LSQRSolve` build
  followed by full `lake build`, executable lookup, placeholder scan,
  `git diff --check`, axiom audit, and PDF compile/repair/text/render
  inspection.  This still does not derive the inverse Frobenius budget from
  determinant margin/SVD/condition number.
- 2026-05-30: Added and two-pass validated the local leading-block inverse
  infinity-norm route.  Shared matrix algebra now has
  `abs_coord_le_sum_abs`, `vecNorm2Sq_le_sum_abs_sq`,
  `frobNormSq_le_nat_mul_infNorm_sq`, and
  `frobNorm_sq_le_nat_mul_infNorm_sq`, proving
  `||C_k||_F^2 <= (k+1)||C_k||_\infty^2`.  QR/LS wrappers
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`
  use the visible local inverse infinity-norm budget
  `(k+1)||C_k||_\infty^2 <= K_k` plus `m * budget_k^2 < 1 / K_k`.
  Validation used a targeted `LSQRSolve` build followed by full `lake build`,
  executable lookup, placeholder scan, `git diff --check`, axiom audit, and
  PDF compile/repair/text/render inspection.  The next red-bottleneck
  dependency is deriving the inverse infinity-norm budget from triangular
  inverse estimates, determinant margin, SVD, condition number, or keeping that
  budget explicitly visible.
- 2026-05-30: Implemented the diagonal-dominant triangular inverse route for
  the QR local inverse budget.  `InverseBounds.lean` now has
  `triInv_infNorm_upperBound` and
  `triInv_infNorm_sq_budget_of_diagDominantUpper`, and `LSQRSolve.lean` has
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_invNorm_budget`.
  Targeted builds for `InverseBounds` and `LSQRSolve` passed, followed by full
  `lake build`.  Two weak-component passes are now clean: lookup, placeholder
  scan, `git diff --check`, axiom audit, PDF compile/repair/text extraction,
  and rendered page inspection all succeeded.  This closes the
  diagonal-dominant triangular inverse route as a visible-domain theorem family;
  the remaining red-bottleneck work is to derive or choose the domain
  assumptions for computed QR leading blocks.
- 2026-05-30: Implemented the determinant-facing diagonal-dominant QR route.
  `MatrixAlgebra.lean` now proves determinant-to-`IsInverse` adapters for
  `nonsingInv`; `InverseBounds.lean` has
  `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero`; and
  `LSQRSolve.lean` has
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_det_ne_zero_invNorm_budget`.
  Two weak-component validation passes passed.  This closes the explicit
  inverse-witness dependency for the diagonal-dominant branch, while leaving
  diagonal dominance, determinant nonzero, and the diagonal-minimum budget as
  visible assumptions for the next red-bottleneck step.
- 2026-05-30: Implemented the determinant-facing inverse-norm QR route.
  `LSQRSolve.lean` now has
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_infNorm_budget`,
  which uses `det S_k != 0` to instantiate the inverse-\(\infty\) route with
  `C_k = nonsingInv S_k` while keeping the inverse-norm budget visible.
  Targeted build and full-build validation now have two clean
  weak-component passes: executable lookup, placeholder scan,
  `git diff --check`, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection all succeeded.  The remaining red QR bottleneck is
  to derive the inverse-\(\infty\) budget from SVD, condition-number,
  determinant-margin, or computed-loop assumptions, or to keep that budget
  explicitly visible.
- 2026-05-30: Implemented the condition-number route for the local QR inverse
  budget.  `PerturbationTheory.lean` now proves
  `infNorm_eq_sup_row_sum`, `kappaInf_eq_infNorm_mul_infNorm`,
  `infNorm_inv_le_of_kappaInf_le_and_norm_lower`, and
  `infNorm_sq_budget_of_kappaInf_le_and_norm_lower`, and `LSQRSolve.lean` has
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_budget`.
  The route derives `(k+1)||nonsingInv S_k||_\infty^2 <= K_k` from
  `0 < rho_k <= ||S_k||_\infty`, a visible
  `kappaInf S_k (nonsingInv S_k) <= kappa_k` bound, and
  `(k+1)(kappa_k/rho_k)^2 <= K_k`.  Two weak-component passes passed:
  targeted/full builds, executable lookup, placeholder scan, `git diff
  --check`, axiom audit, PDF compile/repair/text extraction, and rendered page
  inspection were clean.  This closes the condition-number route as a visible
  dependency; the remaining red-bottleneck work is deriving local `rho_k`,
  `kappa_k`, determinant, and QR-loop assumptions from SVD/determinant-margin
  or computed-loop invariants, or keeping them explicit.
- 2026-05-30: Implemented the self-norm specialization of the local QR
  condition-number route.  `MatrixAlgebra.lean` now proves
  `infNorm_pos_of_det_ne_zero`; `PerturbationTheory.lean` proves
  `infNorm_inv_le_of_kappaInf_le_and_det_ne_zero` and
  `infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero`; and `LSQRSolve.lean`
  proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget`.
  This removes the separate `rho_k` lower-bound hypothesis by taking
  `rho_k = ||S_k||_infty`.  Two weak-component passes passed: targeted/full
  builds, lookup, placeholder scan, `git diff --check`, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection were clean. This
  dependency is closed as a visible-domain route; the remaining red QR
  bottleneck is deriving the local determinant and `kappaInf` assumptions,
  plus prefix-span/compact-update/sign-choice/final solver budgets, from SVD,
  determinant-margin, or a computed-loop invariant, or keeping them explicit.
- 2026-05-30: Added the determinant-facing prefix-span bridge for the QR
  condition-number route.  `HouseholderQR.lean` now proves
  `qrPrefixSupportSpannedByPreviousColumns_of_det_ne_zero_previousLeadingBlockTranspose`,
  and `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_blocks_det_ne_zero_kappaInf_selfNorm_budget`.
  This removes the abstract prefix-span hypothesis from the self-norm `κ∞`
  solver route under visible previous-leading-block determinant and lower-zero
  shape assumptions.  Two weak-component passes passed: targeted/full builds,
  lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection were clean.  This
  dependency is closed as a visible-domain route; the remaining red QR
  bottleneck is deriving previous/current determinant assumptions, local
  `kappaInf` bounds, sign choice, compact-update budgets, final solver budgets,
  and computed-loop lower-zero shape from SVD, determinant-margin, or a
  source-faithful computed-loop invariant, or keeping them explicit.
- 2026-05-30: Added the triangular-principal-minor self-norm condition-number
  route for stored QR least squares.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_kappaInf_selfNorm_budget`,
  deriving the previous/current determinant hypotheses and completed-column
  lower-zero shape from visible upper-triangular local shape plus nonzero
  previous/current leading diagonals, then applying the determinant-facing
  prefix-span self-norm route.  Two weak-component passes passed: targeted/full
  builds, lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection were clean.
  This closes the triangular self-norm dependency as a visible-domain route.
  The remaining red QR bottleneck is deriving the triangular/nonzero-diagonal
  computed-loop invariant, local `kappaInf` bounds, sign choice,
  compact-update budgets, and final solver budgets from source-faithful
  foundations, or explicitly keeping them visible.
- 2026-05-30: Added the computed-prefix-zero triangular self-norm
  condition-number route for stored QR least squares.  `HouseholderQR.lean` now
  exposes `fl_householderStoredPanel_sequence_prefix_lower_zero` and local
  leading-block determinant adapters; `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget`.
  This removes the over-strong whole-panel triangular-shape assumption by
  deriving the needed leading-block triangular entries and completed-column
  lower-zero shape from the stored panel recurrence itself.  Two
  weak-component validation passes passed: targeted/full builds, lookup,
  placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
  extraction, and rendered page inspection were clean.  This dependency is
  closed as a computed-loop shape route.  Remaining visible assumptions are
  nonzero local diagonals, local `kappaInf` bounds, sign choice,
  compact-update budgets, and final solver budgets.
- 2026-05-30: Added the concrete signed-alpha specialization for the stored QR
  route.  `HouseholderSpec.lean` now defines `signedHouseholderAlpha` and
  proves the scalar square/sign lemmas; `HouseholderQR.lean` proves
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`;
  `LSQRSolve.lean` proves both
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_trailingNorm_pos_and_sqrt_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget`.
  This removes the independent sign-choice hypothesis whenever the loop states
  the standard signed trailing-norm alpha rule.  Remaining red QR dependencies:
  nonzero local diagonals/nonbreakdown, local `kappaInf` bounds,
  compact-update budgets, and final solver budgets.  Two weak-component
  validation passes passed: targeted/full builds, executable lookup,
  placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
  extraction, and rendered page inspection were clean.
- 2026-05-30: Added the prefix-local previous-diagonal nonbreakdown route for
  the stored QR bottleneck.  `HouseholderQR.lean` now proves
  `fl_householderStoredPanel_sequence_prefix_diag_nonzero_of_step_diag_nonzero`
  and
  `fl_householderStoredTrailingPanel_sequence_prefix_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`;
  `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`.
  This derives all previous local diagonal nonzeros from the stored signed-alpha
  loop and leaves the current leading pivot nonzero condition visible.  Two-pass
  validation passed: targeted/full builds, executable lookup, placeholder scan,
  whitespace check, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection were clean, with one lookup rerun after a transient
  concurrent-build race.  Remaining red QR dependencies: current-pivot
  nonzero/nonbreakdown, local `kappaInf` bounds, compact-update budgets, and
  final solver budgets.
- 2026-05-30: Added explicit final Gram/RHS radii for the prefix-local stored QR
  route.  `LSQRSolve.lean` now defines
  `qrSolveFinalDataPerturbationBudget`, `qrSolveFinalRhsPerturbationBudget`,
  `qrSolveFinalGramBudget`, and `qrSolveFinalRhsBudget`, proves the required
  nonnegativity/RHS-sum adapters, and closes the solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`.
  Two-pass validation passed: targeted/full builds, executable lookup,
  placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
  extraction, and rendered page inspection were clean.  The final Gram/RHS
  listed dependency of the red QR bottleneck is closed; remaining dependencies
  are current-pivot nonzero/nonbreakdown, local `kappaInf` bounds,
  compact-update budgets, and square-root/compact pivot-budget derivations.
- 2026-05-31: Added explicit compact-update budgets for the prefix-local stored
  QR route.  `HouseholderApply.lean` now defines one-vector and one-panel
  relative compact budgets, `HouseholderQR.lean` sums them into
  `storedQRCompactSequenceRelativeBudget`, and `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`.
  This removes the separate compact-update domination constant from the
  prefix-local signed-alpha route by choosing a displayed repository budget and
  reusing the explicit final Gram/RHS radii.  Two-pass validation passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page inspection
  were clean.  The red QR bottleneck is now narrowed to current-pivot
  nonzero/nonbreakdown, local `kappaInf` bounds, and square-root/compact
  pivot-budget derivations.
- 2026-05-31: Added the scalar positive-trailing-norm bridge for the
  prefix-local stored QR route.  `HouseholderSpec.lean` now proves
  `householderTrailingNorm2Sq_pos_of_nonneg_budget_lt_sqrt`, and the explicit
  final-budget and explicit compact-budget LSQRSolve wrappers derive their
  positive-trailing-norm obligations internally from the square-root budget
  hypotheses.  Two-pass validation passed: targeted/full builds, executable
  lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection were clean.
  The red QR bottleneck is now narrowed to current-pivot nonzero/nonbreakdown,
  local `kappaInf` bounds, and square-root/compact pivot-budget derivations.
- 2026-05-31: Added the direct norm-square-to-square-root pivot-budget bridge
  for the stored QR route.  `HouseholderSpec.lean` now proves
  `budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq`,
  and `HouseholderQR.lean` uses it directly in
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget`
  instead of detouring through an active-entry witness.  Two-pass validation
  passed: targeted/full builds, executable lookup, placeholder scan, whitespace
  check, axiom audit, PDF compile/repair/text extraction, and rendered page
  inspection were clean.  The red QR bottleneck is now narrowed to
  current-pivot nonzero/nonbreakdown, local `kappaInf` bounds, and
  conditioning-to-norm-square compact pivot-budget derivations.
- 2026-05-31: Added the solver-facing explicit compact QR certificate with
  norm-square pivot margins.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_normSqBudget`,
  which composes the direct scalar bridge with the explicit compact-update and
  final-radius QR solver wrapper.  The theorem accepts the dimensioned margin
  `m * budget_k^2 < ||A_k(k:m,k)||_2^2` directly rather than exposing a
  square-root pivot-budget hypothesis.  Two-pass validation passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page inspection
  were clean.  The red QR bottleneck is now narrowed to current-pivot
  nonzero/nonbreakdown, local `kappaInf` bounds, and deriving the norm-square
  margins from conditioning or a computed-loop invariant.
- 2026-05-31: Added a route-elimination counterexample for the rectangular QR
  bottleneck.  `HouseholderQR.lean` now defines the real `2 x 2` column-swap
  matrix `qrPivotCounterexample2` and proves
  `qrPivotCounterexample2_first_pivot_zero`,
  `qrPivotCounterexample2_det_ne_zero`, and
  `not_forall_det_ne_zero_implies_first_pivot_ne_zero`.  This formally rules
  out using ordinary nonsingularity/full rank alone to justify the first
  unpivoted Householder pivot.  Two-pass validation passed: targeted/full
  builds, executable lookup, placeholder scan, whitespace check, axiom audit,
  PDF compile/repair/text extraction, and rendered page inspection were clean.
  The red QR bottleneck is now narrowed to source-faithful pivoting,
  no-breakdown or structured current-pivot invariants, local `kappaInf` bounds,
  and deriving norm-square margins from conditioning or a computed-loop
  invariant.
- 2026-05-31: Closed the structured current-pivot route for the rectangular QR
  bottleneck.  `MatrixAlgebra.lean` now proves
  `diag_ne_zero_of_upper_triangular_det_ne_zero`; `HouseholderQR.lean` proves
  `qrLeadingBlock_current_pivot_ne_zero_of_local_upper_triangular_det_ne_zero`
  and
  `fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero`;
  `LSQRSolve.lean` exposes the compact solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_normSqBudget`.
  Two-pass validation passed: targeted/full builds, executable lookup,
  placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
  extraction, and rendered page inspection were clean.  The current-pivot
  dependency is now closed under the source-faithful structured local-leading
  determinant assumption; the red QR bottleneck remains local `kappaInf`
  bounds and conditioning-to-norm-square/dual compact pivot-budget derivations.
- 2026-05-31: Closed the structured norm-square margin route from local leading
  blocks and `kappaInf`/dual budgets.  `HouseholderQR.lean` now proves
  `qrPrefixSupportSpannedByPreviousColumns_of_leadingBlock_upper_det_ne_zero`,
  deriving prefix-span from stored lower-zero shape and nonsingular local
  leading blocks.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`,
  which derives the dimensioned norm-square compact pivot margin internally
  from local `kappaInf`/`K_k` and dual compact-budget assumptions.  Two-pass
  validation passed: targeted/full builds, executable lookup, placeholder
  scan, whitespace check, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection were clean.  The red QR bottleneck is now narrowed
  to deriving or justifying local `kappaInf`, `K_k`, and dual compact-budget
  assumptions from conditioning or a computed-loop invariant.
- 2026-05-31: Closed the structured direct inverse-∞ budget route for the
  latest explicit compact QR certificate.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_invNorm_dualBudget`,
  which removes the local `kappaInf` and self-norm hypotheses when the direct
  budget `(k+1)||nonsingInv(S_k)||_∞^2 <= K_k` is available.  The theorem
  still keeps local leading-block determinants and the dual compact-budget
  inequality visible.  Two-pass validation passed: targeted/full builds,
  executable lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection were clean.  The
  red QR bottleneck is now narrowed to deriving direct inverse-∞ and dual
  compact-budget assumptions from diagonal dominance, conditioning, or a
  computed-loop invariant, or keeping them as explicit triangular-solve domain
  assumptions.
- 2026-05-31: Closed the diagonal-dominant structured direct inverse-∞ route
  for the latest explicit compact QR certificate.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_dualBudget`,
  which composes `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero`
  with the direct inverse-budget wrapper.  Local diagonal dominance, nonzero
  leading-block determinant, and Higham's diagonal-minimum budget now derive
  `(k+1)||nonsingInv(S_k)||_∞^2 <= K_k` internally.  Two-pass validation
  passed: targeted/full builds, executable lookup, placeholder scan,
  whitespace check, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection were clean.  The red QR bottleneck is now narrowed
  to deriving local diagonal dominance and the dual compact-budget inequality
  from conditioning or a computed-loop invariant, or keeping them as visible
  source/domain assumptions.
- 2026-05-31: Closed a route-elimination dependency for the rectangular QR
  bottleneck: `TriangularForwardBound.lean` now proves
  `not_forall_upper_tri_diag_nonzero_implies_diagDominant` using the concrete
  `2 x 2` matrix `[[1,2],[0,1]]`.  It is upper triangular and has nonzero
  diagonal entries, but it is not diagonally dominant.  Two-pass validation
  passed: targeted/full builds, executable lookup, placeholder scan,
  whitespace check, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection were clean.  The red QR bottleneck is now narrowed
  to deriving local diagonal dominance from a stronger computed-loop or
  conditioning invariant, deriving the dual compact-budget inequality, or
  keeping those assumptions visible as source/domain hypotheses.
- 2026-05-31: Closed the concrete-dual diagonal-dominant compact QR dependency:
  `diagDominantUpperInvBudgetExpr`,
  `diagDominantUpperInvBudgetExpr_pos`,
  `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero_twice_budget`, and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualBudget`
  remove the arbitrary auxiliary `K_k` from the latest diagonal-dominant
  certificate by choosing `K_k = 2D_k`.  Two-pass validation passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page
  inspection were clean.  The remaining red QR choice is to prove local
  diagonal dominance and the direct compact smallness condition from a stronger
  conditioning/computed-loop invariant, or keep them visible as domain
  assumptions.
- 2026-05-31: Closed the product-form concrete-dual compact QR dependency:
  `mul_sq_lt_inv_two_mul_of_two_mul_mul_sq_lt_one` and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductBudget`
  convert the concrete-dual smallness assumption from
  `m * budget_k^2 < 1/(2D_k)` to `2D_k * (m * budget_k^2) < 1`, with `D_k > 0`
  derived from the existing diagonal-dominance budget positivity theorem.
  Two-pass validation passed: targeted/full builds, executable lookup,
  placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
  extraction, and rendered page inspection were clean.  The red QR bottleneck
  now has the product-shaped compact-smallness statement, but still requires
  deriving local diagonal dominance and product smallness from a stronger
  conditioning/computed-loop invariant, ruling out that route, or keeping the
  assumptions visible.
- 2026-05-31: Closed a route-elimination dependency for the product-form
  compact QR bottleneck: `InverseBounds.lean` now proves
  `not_forall_pos_implies_two_mul_mul_sq_lt_one`, showing with the scalar
  counterexample `D = 1`, `B = 1`, and `m = 1` that positivity of the inverse
  budget alone cannot imply `2D * (m * B^2) < 1`.  Two-pass validation passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page inspection
  were clean.  The active QR bottleneck is now narrowed to proving a genuine
  compact-update product bound from a computed-loop/conditioning invariant or
  keeping the product-smallness assumption visible.
- 2026-05-31: Strengthened the diagonal-dominance route elimination for the
  rectangular QR bottleneck.  `TriangularForwardBound.lean` now proves
  `diagDominanceCounterexample2_det_ne_zero` and
  `not_forall_upper_tri_det_ne_zero_implies_diagDominant`, showing that the
  concrete upper-triangular matrix `[[1,2],[0,1]]` has nonzero determinant but
  still is not diagonally dominant.  Two-pass validation passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page inspection
  were clean.  The active QR bottleneck can no longer use triangular
  determinant nonzeroness as a hidden diagonal-dominance proof; a positive
  route must derive diagonal dominance from a stronger computed-loop or
  conditioning invariant, or keep it visible.

- 2026-05-31: Added the conditioning-facing companion route elimination for
  the same QR bottleneck.  `TriangularForwardBound.lean` now proves
  `exists_upper_tri_det_ne_zero_kappaInf_bound_not_diagDominant` and
  `not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_diagDominant`.
  The same `[[1,2],[0,1]]` matrix has upper-triangular shape, nonzero
  determinant, and a finite local `kappaInf` certificate, but is not
  diagonally dominant.  This rules out using a generic finite condition-number
  certificate as the missing diagonal-dominance invariant; a positive route
  needs a stronger computed-loop/off-diagonal-control invariant or an explicit
  domain assumption.  Two weak-component passes completed: targeted/full
  builds, lookup, touched-Lean placeholder scan, whitespace check, axiom audit,
  PDF compile/text extraction, and rendered page inspection.

- 2026-05-31: Added source-faithful leading-dual budget instantiation wrappers
  for the rectangular QR bottleneck.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leading_dual_norm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leading_dual_norm_budget`.
  These wrappers choose the repository final Gram/RHS budgets and, in the
  compact version, `storedQRCompactSequenceRelativeBudget` for the
  prefix-span plus leading-dual solver certificate.  They close a real
  budget-instantiation dependency while keeping the remaining obligations
  visible: construct the leading dual, prove prefix-span, and derive the dual
  compact-smallness condition from a computed-loop/conditioning invariant or
  keep them as explicit domain assumptions.  Two weak-component passes
  completed: targeted/full builds, lookup, touched-Lean placeholder scan,
  whitespace check, axiom audit, PDF compile/text extraction, and rendered
  page inspection.

- 2026-05-31: Added source-faithful local inverse row-budget wrappers with
  repository final and compact budgets.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`.
  These construct the leading dual from a local leading-block left inverse,
  choose `qrSolveFinalGramBudget`/`qrSolveFinalRhsBudget`, and then choose
  `storedQRCompactSequenceRelativeBudget`.  This closes the local-dual
  construction plus budget-instantiation dependency under visible prefix-span,
  local row-norm, sign-choice, and compact-smallness hypotheses.  Two
  weak-component passes completed: targeted/full builds, lookup, touched-Lean
  placeholder scan, whitespace check, axiom audit, PDF compile/text extraction,
  and rendered page inspection.

- 2026-05-31: Added source-faithful local inverse Frobenius/infinity wrappers
  with repository final and compact budgets.  `LSQRSolve.lean` now proves the
  explicit norm-budget and explicit compact-budget variants ending in
  `leadingBlock_leftInverse_frobNorm_budget` and
  `leadingBlock_leftInverse_infNorm_budget`.  These compose the existing
  row-versus-Frobenius and infinity-versus-Frobenius bridges with
  `qrSolveFinalGramBudget`, `qrSolveFinalRhsBudget`, and
  `storedQRCompactSequenceRelativeBudget`.  Two weak-component passes
  completed: targeted/full builds, lookup, touched-Lean placeholder scan,
  whitespace check, axiom audit, PDF compile/text extraction, and rendered
  page inspection.

- 2026-05-31: Added the stored-prefix-span local-inverse row wrapper for the
  source-faithful rectangular QR route.  `HouseholderQR.lean` now proves
  `qrPrefixSupportSpannedByPreviousColumns_of_leftInverse_previousLeadingBlockTranspose`
  and
  `fl_householderStoredPanel_sequence_prefixSpan_of_leftInverse_previousLeadingBlockTranspose`,
  deriving prefix-span from the actual stored panel recurrence plus local
  left inverses for the previous transposed leading blocks.  `LSQRSolve.lean`
  now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget`,
  which feeds that derived prefix-span fact into the row-norm local-inverse
  compact-budget certificate.  This closes the separate prefix-span assumption
  for the row branch under visible previous/current local left inverses; local
  inverse existence, row-norm budget, sign choice, and compact-smallness remain
  explicit.  Two weak-component passes passed: targeted/full builds, lookup,
  placeholder scans, whitespace checks, repeated axiom audit, PDF text
  extraction, and rendered page inspection.
- 2026-05-31: Extended the stored-prefix-span source-faithful QR route to the
  Frobenius and infinity inverse-norm compact-budget branches.  `LSQRSolve.lean`
  now proves the `...previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget`
  and `...previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget`
  wrappers, which derive prefix-span from the stored recurrence plus previous
  local left inverses and feed it into the repository-budgeted inverse-norm
  certificates.  Two weak-component passes passed: targeted/full builds,
  lookup, placeholder scans, whitespace checks, repeated axiom audit, PDF text
  extraction, and rendered page inspection.
- 2026-05-31: Added the signed-alpha stored-prefix-span local-inverse row
  wrapper for the source-faithful rectangular QR route.  `LSQRSolve.lean` now
  proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget`,
  which derives the squared-alpha trailing-norm identity and sign-choice
  inequality from the repository `signedHouseholderAlpha` definition before
  applying the stored-prefix-span row certificate.  Two weak-component passes
  passed: targeted/full builds, lookup, placeholder scans, whitespace checks,
  repeated axiom audit, PDF text extraction, and rendered page inspection.
- 2026-05-31: Extended the signed-alpha stored-prefix-span local-inverse route
  to the Frobenius and infinity inverse-norm branches.  `LSQRSolve.lean` now
  proves the `...signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget`
  and `...signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget`
  wrappers, which derive the squared-alpha identity and sign-choice inequality
  from `signedHouseholderAlpha` before applying the stored-prefix-span
  Frobenius/infinity certificates.  Two weak-component passes passed:
  targeted/full builds, lookup, placeholder scans, whitespace checks, repeated
  axiom audit, PDF text extraction, and rendered page inspection.
- 2026-05-31: Added the determinant-facing signed-alpha stored-prefix-span
  local-inverse wrappers.  `LSQRSolve.lean` now proves the
  `...signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_norm_budget`,
  `...frobNorm_budget`, and `...infNorm_budget` certificates, instantiating
  previous/current local left inverses with `nonsingInv` from nonzero
  determinants while keeping the inverse-budget and compact-smallness
  inequalities visible.  Two weak-component passes passed: targeted/full
  builds, lookup, placeholder scans, whitespace checks, repeated axiom audit,
  PDF page-local text extraction, and rendered page inspection.
- 2026-05-31: Added the source-faithful signed-alpha determinant `κ∞`
  self-norm wrapper
  `...signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget`.
  It derives the direct inverse-∞ budget from visible determinant, local
  `κ∞`, and self-norm squared-budget hypotheses using the repository
  `infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero` bridge.  Two
  weak-component passes passed: targeted/full builds, lookup, placeholder
  scans, whitespace checks, repeated axiom audit, PDF page-local text
  extraction, and rendered page inspection.
- 2026-05-31: Added the source-faithful signed-alpha triangular leading-block
  `κ∞` wrapper
  `...signed_alpha_upperTriangular_leadingDiag_ne_zero_kappaInf_selfNorm_budget`.
  It derives the previous/current determinant facts from visible
  upper-triangular leading-block shape and nonzero displayed leading diagonal
  entries using the QR determinant bridges, then applies the signed-alpha
  determinant `κ∞` route.  Two weak-component passes passed: targeted/full
  builds, lookup, placeholder scans, whitespace checks, repeated axiom audit,
  PDF page-local text extraction, and rendered page inspection after replacing
  an overflowing inline Lean-name proof-idea sentence by math-level prose.
- 2026-05-31: Ruled out the false current-pivot route "positive active trailing
  norm implies current unpivoted pivot nonzero."  `HouseholderSpec.lean` now has
  the concrete `x = (0,1)` counterexample
  `householderTrailingPivotCounterexample2` with positive active trailing
  squared norm and zero pivot entry, plus
  `not_forall_trailingNorm2Sq_pos_implies_pivot_ne_zero`.  Two weak-component
  passes passed: targeted/full builds, lookup, placeholder scans, whitespace
  checks, repeated axiom audit, PDF page-local text extraction, and rendered
  page inspection.  This is route elimination only; the QR bottleneck must
  continue through pivoting, structured leading-block invariants, or visible
  domain assumptions for current-pivot nonzero.
- 2026-05-31: Ruled out the false product-smallness route "diagonal dominance
  and the displayed Higham inverse budget imply product compact smallness."
  `InverseBounds.lean` now has
  `not_forall_diagDominantUpper_implies_two_mul_budget_expr_mul_sq_lt_one`,
  using the scalar `1 x 1` identity block with compact budget `B = 1` and
  `m = 1`.  Two weak-component passes passed: targeted/full builds, lookup,
  placeholder scans, whitespace checks, repeated axiom audit, PDF page-local
  text extraction, and rendered page inspection.  This is route elimination
  only; the product compact-smallness inequality still needs a genuine
  computed-loop/conditioning invariant or must stay visible as a domain
  assumption.
- 2026-05-31: Re-audited the rectangular QR proof-source route after the
  product-smallness shortcut was ruled out.  The remaining QR work is now a
  genuine theorem-family choice: continue Higham's columnwise/normwise
  Householder QR Theorem 4.5 route, switch to Cox--Higham row-wise weighted-LS
  stability with pivoting/sorting/sign-choice hypotheses, or keep the remaining
  nonbreakdown/conditioning/product-smallness hypotheses visible.  Do not loop
  back into diagonal dominance/product smallness unless a real compact-update
  budget theorem is added.
- 2026-05-31: Chose the Higham columnwise route and closed the final stored QR
  factorization assembly.  `HouseholderQR.lean` now has
  `fl_householderStoredTrailingPanel_higham_columnwise_factorization`, combining
  the stored trailing columnwise perturbation theorem with the stored top-block
  shape theorem.  It yields one orthogonal `Q`, perturbations `DeltaA` and
  `Deltab`, columnwise/RHS geometric perturbation bounds, final `[R;0]` shape,
  top transformed RHS, and upper-triangular `R`.  This is not the final
  solver/preconditioner theorem: nonzero diagonal, conditioning/inverse-budget,
  and compact-smallness/product-budget obligations remain separate.
- 2026-05-31: Refactored the stored-loop LSQRSolve handoff
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`
  so it reuses
  `fl_householderStoredTrailingPanel_higham_columnwise_factorization` directly
  instead of rebuilding the sequence perturbation and shape facts internally.
  The cleanup has two weak-component passes (targeted/full builds, lookup,
  placeholder scan, diff check, axiom audit, PDF compile/text extraction, and
  rendered page inspection); this is a library-health/modularity improvement,
  not a new discharge of nonzero diagonal, conditioning, or compact-smallness.
- 2026-05-31: Strengthened the no-pivot QR route elimination:
  `qrPivotCounterexample2_first_leadingBlock_det_zero` and
  `not_forall_det_ne_zero_implies_all_leading_blocks_det_ne_zero` show that the
  nonsingular `2 x 2` column-swap matrix has zero determinant in its first
  unpivoted `1 x 1` leading QR block.  This rules out deriving the per-pivot
  leading-block determinant hypotheses from whole-matrix nonsingularity/full
  rank alone.  It is a theorem-statement correction/route elimination, not a
  positive nonbreakdown theorem.  Two weak-component passes validated the Lean
  facts, lookup references, axiom audit, PDF text extraction, and rendered PDF
  pages 120--121.
- 2026-05-31: Added the QR bottleneck cross-route elimination
  `not_forall_upper_tri_det_ne_zero_product_budget_implies_diagDominant`.
  The nonsingular upper-triangular block `[[1,2],[0,1]]` satisfies the displayed
  product compact-smallness inequality for a small budget `B = 1/8`, but still
  is not diagonally dominant.  This prevents collapsing the remaining
  diagonal-dominance and product-smallness assumptions into each other; both
  need a genuine invariant or must stay visible as domain assumptions.  Two
  weak-component passes validated the Lean theorem, lookup reference, axiom
  audit, PDF text extraction, and rendered PDF pages 124--125.
- 2026-05-31: Added the QR bottleneck stored-sequence compact-budget bridge:
  `storedQRCompactPivotBudget_le_sequence_column_norm`,
  `two_mul_mul_sq_lt_one_of_nonneg_le`, and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductSequenceBudget`.
  The raw pivot compact component is now bounded by the deterministic stored
  QR sequence budget times the current pivot-column norm before feeding the
  concrete-dual product certificate.  Two weak-component passes validated the
  Lean facts, lookup reference, axiom audit, PDF text extraction, and rendered
  PDF page 124.
- 2026-05-31: Added a QR bottleneck route elimination:
  `not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_two_mul_budget_expr_mul_sq_lt_one`.
  It shows that upper-triangular nonsingularity plus a finite local `κ∞` budget
  does not imply product compact-smallness; the compact-update budget still
  needs a genuine computed-loop/conditioning invariant or must stay visible.
  Two weak-component passes validated the Lean fact, lookup reference, axiom
  audit, PDF text extraction, and rendered PDF pages 125--126.
- 2026-05-31: Marked `LS.8-rectangular-QR` as an explicit route-choice
  checkpoint after the shortcut eliminations.  The generic implementation-backed
  equation (8) QR/preconditioner theorem remains open; the next valid progress
  must choose a stronger computed-loop/off-diagonal-control invariant, switch to
  a Cox--Higham pivoted/sorted row-wise theorem family, or keep the remaining
  nonbreakdown/conditioning/product-smallness assumptions visible as domain
  assumptions.  New adjacent adapters are frozen unless they close or rule out
  one of those listed routes.
- 2026-05-31: Narrowed the Cox--Higham option for `LS.8-rectangular-QR`.
  Source review confirmed it is not a drop-in closure for the current unpivoted
  stored-QR solver/preconditioner theorem: Cox--Higham requires column pivoting
  plus row pivoting or row sorting and the specified sign convention.  Treat it
  as a separate future theorem family.  For the current unpivoted theorem, the
  remaining honest choices are a stronger computed-loop/off-diagonal-control
  invariant or visible domain hypotheses.
- 2026-05-31: Added a Lean route elimination for the remaining unpivoted QR
  diagonal-dominance route.  The theorem
  `not_forall_orthogonal_upper_factorization_implies_diagDominant` shows that
  exact QR-shaped data `A = Q * R` with `Q` orthogonal, `R` upper triangular,
  and nonzero diagonal still does not imply diagonal dominance; the witness is
  `Q = I`, `R = [[1,2],[0,1]]`.  A positive unpivoted route must therefore use
  a genuine computed-loop/off-diagonal-control invariant, or keep diagonal
  dominance visible as a domain hypothesis.
- 2026-05-31: Strengthened the same route elimination with the actual exact
  no-pivot trailing Householder recurrence.  The theorem
  `not_forall_exact_trailing_householder_sequence_implies_diagDominant` proves
  that a valid two-step exact Householder sequence can start from
  `[[1,2],[0,1]]` and end at `[[-1,-2],[0,-1]]`, which is not diagonally
  dominant.  Do not try to close the QR/preconditioner bottleneck by claiming
  diagonal dominance is a generic consequence of the unpivoted Householder
  loop; it must be an explicit off-diagonal-control/pivoting hypothesis or a
  visible domain assumption.
- 2026-05-31: After the exact no-pivot recurrence route elimination, the
  equation (8) QR/preconditioner bottleneck is a theorem-scope choice rather
  than a local-adapter gap.  The next valid progress must choose one of:
  prove a stronger computed-loop/off-diagonal-control invariant, switch to a
  pivoted/sorted row-wise theorem family, or keep the remaining nonbreakdown,
  conditioning, diagonal-dominance, and compact-product assumptions visible as
  domain hypotheses.  Adjacent QR adapters are frozen until that choice is made.
- 2026-05-31: User chose the stronger computed-loop/off-diagonal-control route.
  `LSQRSolve.lean` now defines `StoredQROffDiagonalControlInvariant`, bundling
  local leading-block nonsingularity, local diagonal dominance, and product
  smallness for `storedQRCompactSequenceRelativeBudget * ||A_hat_k(:,k)||_2`.
  The wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl`
  proves this invariant feeds the existing diagonal-dominant stored-sequence
  QR certificate and yields `LSQRSolveBackwardError` with the repository final
  Gram/RHS budgets.  This packages and consumes route 1; it does not prove the
  invariant from ordinary no-pivot QR.
- 2026-05-31: Reduced the route-1 invariant to source-shaped local fields.
  `StoredQRSourceOffDiagonalControl` assumes upper-triangular local leading
  blocks, nonzero local leading diagonals, row-wise off-diagonal domination,
  and the stored-sequence compact-product inequality.
  `StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl` derives the
  packaged invariant using `det_ne_zero_of_upper_triangular_diag_ne_zero`, and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl`
  feeds those source-shaped assumptions to the existing solver certificate.
  The next QR bottleneck target is to prove `StoredQRSourceOffDiagonalControl`
  from a real pivoting/order/off-diagonal-growth theorem, or keep it visible as
  the theorem's domain condition.

## Maintenance Rules For Future Work

- Preserve the axiomatic `FPModel`; do not add IEEE-specific assumptions unless
  they are in a separate optional module.
- Prefer deriving new algorithm bounds from existing foundation theorems rather
  than restating a bound as a hypothesis.
- When adding high-level theorem wrappers around external assumptions, label
  them as abstract/specification transfer theorems, not as full internal error
  analyses.
- Keep public constants exact when Higham gives exact gamma constants. Avoid
  weakening constants unless the theorem name and docs say so.
- Before saying something is absent, search with `rg`/`rg --files`; this
  library is large enough that memory alone is unreliable.
- Prioritize fixes and new formalizations that improve compositional reuse for
  stability proofs, especially kernel contracts useful in larger algorithms.
- Run `lake build` after edits and check for new warnings.

## 2026-05-31 RandNLA CACM QR Bottleneck Frontier

- Route 1 for the rectangular QR/preconditioner bottleneck is reduced to
  `StoredQRSourceOffDiagonalControl`.  The source-shaped wrapper has two clean
  weak-component passes: full build, lookup, diff check, placeholder scan,
  axiom audit, PDF compile/text extraction, and rendered pages 128--129.  The
  remaining red dependency is not another adapter; it is proving the
  source-shaped local control data from source-specific pivoting, ordering, or
  off-diagonal-growth assumptions, or keeping those fields visible as domain
  hypotheses.
- The stored recurrence itself now supplies the triangular leading-block field:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diag_offdiag_product`
  derives it from `fl_householderStoredPanel_sequence_prefix_lower_zero`, and
  the solver theorem
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diag_offdiag_product`
  leaves only nonzero displayed diagonals, row-wise off-diagonal domination,
  and compact-product smallness as the active red-bottleneck obligations.  This
  triangular-source reduction has two clean weak-component passes.
- The nonzero displayed diagonal obligation is now reduced using existing local
  QR infrastructure: `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_pivot_sqrtBudget_offdiag_product`
  derives previously written diagonal entries from the signed-alpha stored
  prefix-diagonal theorem and square-root budget, while its solver wrapper
  keeps current pivot nonzero, square-root budget, row-wise off-diagonal
  domination, and compact-product smallness visible.  This reduction has two
  clean weak-component passes.
- The raw current pivot nonzero field is now reduced further to a structured
  local leading-block determinant hypothesis:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_sqrtBudget_offdiag_product`
  reuses
  `fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero`,
  and the solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_sqrtBudget_offdiag_product`
  feeds the reduced source-shaped data into `LSQRSolveBackwardError`.  This
  reduction has two clean weak-component passes.
- The square-root nonbreakdown budget in the same determinant-shaped
  source route is now reduced to the dimensioned norm-square margin:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_offdiag_product`
  applies
  `budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq`,
  and the solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_offdiag_product`
  feeds the result into the final QR certificate.  This reduction has two
  clean weak-component passes.
- The current QR red bottleneck is a genuine theorem-family route choice, not
  an API problem.  Existing local counterexamples rule out deriving the
  residual route-1 fields from ordinary unpivoted stored Householder QR, full
  rank, whole-matrix determinant nonzero, positive trailing norm, exact QR
  shape, finite conditioning, diagonal dominance alone, or product smallness
  alone.  Further progress needs one choice: keep the remaining fields as visible source/domain
  assumptions, switch to pivoted/sorted/off-diagonal-controlled QR, or provide
  an application-specific source theorem proving them.
- Current scoping choice: keep local leading-block nonsingularity, norm-square
  nonbreakdown margin, row-wise off-diagonal domination, and compact-product
  smallness visible for the existing
  unpivoted theorem family.  This closes the route-choice bookkeeping but not
  the generic paper-level QR/preconditioner claim.  Do not add adjacent
  unpivoted QR wrappers unless they close a listed dependency or the theorem
  family changes.
- 2026-05-31: Algorithm 3 SRHT route now has scalar signed-linear-form MGF
  infrastructure in `Preconditioning.lean`.
  `rademacherTraceProbability_expectationReal_exp_sum_mul_sign_eq_prod`
  factors the finite Rademacher MGF exactly, and
  `rademacherTraceProbability_eventProb_sum_mul_sign_le_ge_one_sub_exp_mul_prod`
  composes that factorization with the local exponential-Markov kernel.  The
  same file now also closes the scalar Hoeffding/two-sided-tail dependency and
  a weaker coordinate-Hoeffding all-row row-norm theorem
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_sum_exp_sq_bound`.
  It also closes the scoped equation-(6) leverage-probability lift
  `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_ge_one_sub_delta`.
  `UniformRowSampling.lean` now defines `uniformRowOuterGramSample` and proves
  the PSD, mean-identity, quadratic-form, and leverage-to-Loewner one-step
  facts for uniform row sampling after preconditioning.  `Preconditioning.lean`
  composes the coordinate-Hoeffding leverage event into
  `rademacherTraceProbability_eventProb_forall_uniformRowOuterGramSample_signedHadamard_finiteLoewnerLe_ge_one_sub_delta`.
  `UniformRowSamplingMGF.lean` now closes the deterministic-after-preconditioning
  iid uniform sample-average concentration route in tail-budget finite-Loewner
  form, ending with
  `uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget`.
  `UniformRowSamplingComposition.lean` now composes the closed
  coordinate-Hoeffding preprocessing event with the closed uniform
  sample-average theorem on the product probability law, ending with
  `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta`.
  `UniformRowSamplingFP.lean` now closes the scoped floating-point uniform
  sketch transfer by proving `rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram`,
  `fl_uniformRowSampleGramDot_perturb_bound`, and
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta`.
  This is a real high-probability auxiliary but not Tropp Lemma 3.3; remaining
  source-sharp work is Tropp row-norm/leverage uniformization.
- 2026-05-31: The scoped Algorithm 3 coordinate-Hoeffding route also has a
  deterministic FP-radius refinement in `UniformRowSamplingFP.lean`.
  `uniformRowSampleGramFullFpConstBudget` names a fixed row-scaling plus
  dot-product perturbation budget; the closed-form lemmas expose the Gram
  dimension factor; `uniformRowSampleGramFullFpPerturbBudget_le_const_of_sample_rowNormSq_le`
  proves that sampled-row norm caps bound the sample-dependent FP budget by
  the fixed budget with `C = m * R`; and
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget`
  gives the same joint probability lower bound with radius `epsilon + tau`
  whenever `tau` dominates the sample-dependent FP budget over all joint
  outcomes.  This closes the optional deterministic-radius refinement for the
  scoped route; it now has two clean weak-component passes.  It still does not
  prove Tropp's source-sharp SRHT row-norm theorem.
- 2026-05-31: The active Algorithm 3 source-sharp SRHT bottleneck has been
  narrowed by proof-source acquisition.  Tropp Lemma 3.3 depends on the
  Ledoux/Talagrand convex-Lipschitz Rademacher concentration theorem
  (Tropp Proposition 2.1), not on the scalar coordinate-Hoeffding theorem
  already formalized.  `Preconditioning.lean` now closes the expected
  Euclidean row-norm prelude step with
  `rademacherTraceProbability_expectationReal_sqrt_rowNormSq_signedHadamard_le`.
  `RowSamplingLeverage.lean`, `MatrixAlgebra.lean`, and `Preconditioning.lean`
  now also close the deterministic Lipschitz side with
  `hasOrthonormalColumns_vecNorm2Sq_mul_vec_eq`,
  `hasOrthonormalColumns_transpose_mul_vecNorm2Sq_le`,
  `abs_vecNorm2_sub_le_vecNorm2_sub`, and
  `signedHadamard_row_vecNorm2_lipschitz`.  `MatrixAlgebra.lean` and
  `Preconditioning.lean` now close the deterministic convexity side with
  `FiniteVecConvex`, `vecNorm2_linear_combination_convex`, and
  `signedHadamard_row_vecNorm2_convex`.  `MatrixAlgebra.lean` also records
  the deterministic Ledoux-to-Tropp affine scaling constants with
  `FiniteVecLipschitzWith`, `unitCubeToRademacherVec`,
  `finiteVecConvex_scaled_unitCubeToRademacher`, and
  `finiteVecLipschitzWith_scaled_unitCubeToRademacher`.  Ledoux's source
  statement is Corollary 1.3 from the log-Sobolev route: the \([0,1]^m\)
  upper tail has exponent `exp(-t^2/2)`, and Tropp's Rademacher
  `exp(-t^2/8)` follows from the factor-two affine map.  `FiniteProbability.lean` also
  closes the finite MGF/Herbst/Laplace algebraic substrate with
  `FiniteProbability.expectationReal_exp_pos`,
  `FiniteProbability.hasDerivAt_expectationReal_exp_mul`,
  `FiniteProbability.hasDerivAt_log_expectationReal_exp_mul`,
  `FiniteProbability.entropyReal`,
  `FiniteProbability.entropyReal_exp_mul_eq`,
  `FiniteProbability.boolUniformProbability`,
  `FiniteProbability.boolUniformProbability_prob`,
  `FiniteProbability.boolUniformProbability_expectationReal`,
  `FiniteProbability.entropyReal_boolUniformProbability_eq`,
  `FiniteProbability.twoPointEntropy_le_sq_sub_div_of_pos`,
  `FiniteProbability.entropyReal_boolUniformProbability_sq_le_sq_sub_of_pos`,
  `FiniteProbability.expectationReal_sq_nonneg`,
  `FiniteProbability.abs_expectationReal_mul_le_sqrt_mul_sqrt`,
  `FiniteProbability.sqrt_expectationReal_sq_add_le`,
  `FiniteProbability.abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq`,
  `FiniteProbability.boolUniformProbability_abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq`,
  `FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_coordinate_add_entropy`,
  `FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_lifted_diff_sum_add`,
  `FiniteProbability.prod_expectationReal_eq`,
  `FiniteProbability.prod_expectationReal_fst_eq`,
  `FiniteProbability.entropyReal_prod_eq_expectation_entropyReal_add_entropyReal_expectation`,
  `FiniteProbability.log_mgf_differential_le_of_entropyReal_exp_mul_le`,
  `FiniteProbability.log_mgf_div_sub_quadratic_antitoneOn_of_differential_le`,
  `FiniteProbability.tendsto_log_mgf_div_nhdsGT_zero`,
  `FiniteProbability.log_mgf_le_mean_add_quadratic_of_differential_le`,
  `FiniteProbability.log_mgf_le_mean_add_quadratic_of_entropyReal_exp_mul_le`,
  `FiniteProbability.expectationReal_exp_centered_le_exp_of_log_mgf_le`, and
  `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_log_mgf_bound`,
  `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_entropyReal_exp_mul_le`,
  and closes the generic Chernoff optimizer with
  `FiniteProbability.eventProb_real_le_ge_one_sub_exp_of_mgf_bound` and
  `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_subgaussian_mgf`,
  turning a centered subgaussian MGF bound into the one-sided
  `exp(-t^2/(2*sigma^2))` tail.  The unbiased Bernoulli coordinate law,
  coordinate expectation/entropy formulas, fair-Bernoulli coordinate
  log-Sobolev inequality, finite `L2` section-norm reverse-triangle bridge, the
  one-coordinate product peel-off, the abstract Bernoulli-product induction
  lift, the concrete `RademacherTrace m` cube entropy-gradient theorem
  `rademacherTraceProbability_entropyReal_sq_le_sum_flip`, the conditional
  exponential-tilt reduction
  `rademacherTraceProbability_entropyReal_exp_mul_le_of_flip_tilt_sq_sum_bound`,
  the conditional finite-cube Chernoff wrapper
  `rademacherTraceProbability_eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_flip_tilt_sq_sum_bound`,
  product-law expectation Fubini, entropy chain-rule/tensorization algebra,
  scalar tilt inequalities `real_exp_sub_one_le_mul_exp`,
  `real_abs_exp_sub_exp_le_abs_sub_mul_exp_add_exp`,
  `real_exp_half_sub_sq_le_two_mul_half_diff_sq`, uniform Rademacher
  flip-invariance (`rademacherTraceFlip_involutive`,
  `rademacherTraceProbability_expectationReal_flip`), and the non-sharp
  finite-cube symmetrization bridges
  `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_halfdiff_sq_le`
  and
  `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_absdiff_le`
  are now closed locally.  `MatrixAlgebra.lean` also closes the unit-support
  lemmas `vecNorm2_inv_smul_self_of_pos`,
  `vecInnerProduct_inv_smul_self_eq_norm`, and
  `vecNorm2_sub_le_inner_unit_diff`; `Preconditioning.lean` closes the
  sign-flip algebra, `signedHadamard_row_vec_sub_flip`,
  `signedHadamard_row_inner_sq_sum_eq_inv_mul`, and the concrete
  signed-Hadamard row-norm positive-flip self-bound
  `signedHadamard_row_vecNorm2_positive_flip_sq_sum_le`.  The former
  exponential-tilt bottleneck is now closed in the specialized row-norm route:
  `real_exp_half_sub_sq_le_quarter_mul_sq_mul_exp_of_le`,
  `real_exp_half_sub_sq_le_lam_sq_quarter_pair_pos`,
  `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_posdiff_sq_sum_le`,
  and
  `rademacherTraceProbability_flip_tilt_sq_sum_bound_signedHadamard_row_vecNorm2`
  feed the finite-cube Herbst wrapper to prove the one-row
  `exp(-m*t^2/8)` tail and the all-row SRHT row-norm/leverage caps in
  `Preconditioning.lean`.  `UniformRowSamplingComposition.lean` also closes the
  exact source-sharp product-law composition
  `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht`.
  The logarithmic preprocessing choice is also closed:
  `real_sqrt_eight_log_div_pos_of_pos_lt`,
  `real_mul_exp_neg_mul_sqrt_eight_log_div_sq_div_eight_eq`,
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_log_delta_ge_one_sub_delta`,
  `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_log_delta_ge_one_sub_delta`,
  and
  `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`.
  The matching source-sharp floating-point constant-budget transfer is also
  closed by
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht`
  and
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess`.
  The SRHT branch has two consecutive clean weak-component passes recorded in
  the not-proved ledger; non-SRHT Algorithm 3 distributions should use separate
  proof-source/bottleneck rows.
- 2026-05-31: Advanced the rectangular QR/preconditioner red bottleneck along
  the Cox--Higham pivoted/sorted weighted least-squares route.  The first local
  dependency, the signed Householder denominator bound
  `householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos`
  and
  `householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_signed`, is
  now proved in `HouseholderSpec.lean` and has two weak-component passes.  It
  formalizes `2 ||x_tail||_2^2 <= v^T v`, the algebraic core of Cox--Higham
  Lemma 2.1 / equation (2.5).  The column-pivoting comparison also has two
  weak-component passes by `householderTrailingColumnNorm2Sq`,
  `exists_householderTrailingColumnNorm2Sq_active_max`,
  `abs_inner_householderTrailingActiveVector_trailingPart_le_vecNorm2_mul_sqrt`,
  and
  `abs_inner_householderTrailingActiveVector_column_le_vecNorm2_mul_sqrt_of_pivot_max`.
  The Cox--Higham scalar endpoint and first row-growth step are now proved by
  `abs_householderBeta_mul_inner_column_le_sqrt_two_of_signed_pivot_max` and
  `abs_householder_signed_pivot_update_entry_le_one_add_sqrt_two_mul_row_bound`;
  two weak-component passes for these theorems are clean.
  The row-sorting stage accumulation is now formalized by
  `scalar_growth_iterate_bound`,
  `coxHigham_rowSorting_active_entry_bound_of_prior_growth`, and
  `coxHigham_rowSorting_active_entry_bound_of_stage_growth`; two
  weak-component passes for these theorems are clean.
  The pivot-row active-tail norm step from Cox--Higham equations (4.4)--(4.5)
  is now formalized in ambient-dimension form by
  `vecNorm2_le_sqrt_card_mul_of_abs_le`,
  `coxHigham_pivot_row_entry_bound_of_active_tail_entry_bound`, and
  `coxHigham_pivot_row_entry_bound_of_stage_entry_bound`; two weak-component
  passes are clean for this dependency.
  The scalar row-wise accumulated perturbation dependency is now formalized by
  `scalarAffineGrowthBudget`, `scalar_affine_growth_iterate_bound`,
  `coxHigham_rowwise_error_accumulation_bound`, and
  `coxHigham_rowSorting_active_entry_bound_with_accumulated_error`; two
  weak-component passes for these theorems are clean.
  The concrete stored rounded panel per-step FP budget is now represented by
  `fl_householderStoredPanelStep_active_entry_componentwise_error_bound`,
  `coxHigham_storedPanelStep_row_error_recurrence_of_exact_lipschitz`, and
  `coxHigham_storedPanel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz`;
  two weak-component passes for these theorems are clean.  A direct
  row-magnitude adapter has also been added:
  `coxHigham_storedPanelStep_active_entry_bound_of_exact_growth` and
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth`;
  two weak-component passes validate this route-shape correction as a scoped
  dependency, not as the final row-wise QR theorem.
  The non-pivot active-row exact same-reflector bridge is now formalized by
  `matMulVec_householder_signed_pivot_update_entry_eq` and
  `coxHigham_exact_same_reflector_row_growth_of_signed_pivot_row_bound`; two
  weak-component passes validate this one-step bridge as a scoped route
  dependency, not as the final row-wise QR theorem.
  The exact signed pivot-row same-reflector bridge is also now formalized by
  `householderBeta_mul_inner_self_eq_two`,
  `abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal`,
  `coxHigham_signed_pivot_row_update_abs_le_trailing_vecNorm2`, and
  `coxHigham_exact_signed_pivot_row_entry_bound_of_stage_entry_bound`; two
  weak-component passes validate this one-step pivot-row bridge as a scoped
  route dependency, not as the final row-wise QR theorem.
  The one-step active-row case split is now formalized by
  `coxHigham_exact_signed_pivot_active_row_entry_bound_of_stage_bounds`; two
  weak-component passes validate this combined one-step bridge as a scoped
  route dependency, not as the final row-wise QR theorem.
  The exact multi-stage loop bridge is now represented by the concrete
  `exactSignedPivotHouseholderPanelStep` and the sequence theorems
  `coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_stage_budgets`
  and
  `coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_geometric_stage_budgets`;
  two weak-component passes validate this stage-budget propagation dependency as
  a scoped exact loop theorem, not as the final row-wise QR theorem.  The
  exact-to-FP handoff for this honest active-row factor is now represented by
  `coxHigham_storedPanelStep_active_entry_bound_of_exact_growth_factor`,
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth_factor`,
  and
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_growth`;
  two weak-component passes validate this handoff dependency as a scoped
  exact-to-FP bridge, not as the final row-wise QR theorem.
  The source-shaped handoff has also been corrected to explicit stage budgets:
  `coxHigham_storedPanelStep_active_entry_bound_of_exact_stage_budget_factor`,
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_stage_budgets_factor`,
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_stage_budgets`,
  and
  `coxHigham_storedPanelStep_active_entry_bound_of_signed_pivot_stage_bounds`;
  two weak-component passes validate this stage-budget dependency as a scoped
  exact-to-FP bridge, not as the sorting-policy proof or final row-wise QR
  theorem.
  The one-step active-block sorting-field adapter
  `coxHigham_exactSignedPivotPanelStep_active_block_bound_of_stage_bound` has
  been added; two weak-component passes validate it as a scoped dependency. It
  closes only the conversion from one active-block bound to the row/column
  fields of the signed-pivot step, not multi-stage sorting-policy propagation.
  The exact sequence active-block wrappers
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_stage_budgets`
  and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_geometric_stage_budgets`
  have been added; two weak-component passes validate them as scoped
  dependencies. They close only source-shaped field packaging for a visible
  active-block budget family.
  The exact active-block propagation theorem
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound`
  has been added and now has two weak-component passes clean. It derives the
  active-block family from an initial entrywise bound and monotone active
  windows, while leaving positive active norm and pivot-max fields visible.
  The positive active-norm field is now reduced to pivot maximality plus a
  nonzero remaining-active-block witness via
  `householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_active_entry_ne`
  and the sequence wrapper
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_nonzero`.
  Two weak-component passes validate this reduction as a scoped dependency.
  The raw pivot-max inequality is now supplied by the finite active max-pivot
  selector `householderActiveMaxPivotColumn` and the sequence wrapper
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_max_pivot`,
  replacing it by a visible pivot-policy equation. Two weak-component passes
  validate this finite-selector reduction as a scoped dependency.
  The active-nonzero witness is now reduced further to positive active-block
  mass via `householderActiveBlockNorm2Sq`,
  `exists_active_entry_ne_of_householderActiveBlockNorm2Sq_pos`, and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_norm_pos`.
  Two weak-component passes validate this positive-mass bridge as a scoped
  dependency. The active max-pivot policy for displayed sorted stages is now
  supplied by `householderSwapColumns_activeMaxPivotColumn_pivot_max` and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot`;
  two weak-component passes validate this swapped-policy bridge as a scoped
  dependency.
  The raw-to-swapped active-block mass bridge is now validated:
  `householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne`,
  `householderActiveBlockNorm2Sq_swapColumns_pos_of_pos`, and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot_of_raw_active_block_norm_pos`
  move the positive active-block mass assumption back to the raw pre-swap
  stage. Two weak-component passes validate this bridge as a scoped dependency.
  The rounded stored active-block budget recurrence has now been added:
  `signedPivotHouseholderVector`, `signedPivotHouseholderBeta`, and
  `coxHigham_storedPanel_sequence_active_block_bound_of_signed_pivot_stage_bounds`
  propagate rounded active-block budgets through the signed-pivot stored panel
  under visible nonbreakdown, pivot-maximality, storage, monotone active-window,
  and compact-budget recurrence fields. Two weak-component passes validate this
  theorem as a scoped dependency.  The QR-side raw-stage active-block
  nonbreakdown bridge is now added: the previous-span, leading-witness,
  local-left-inverse, and determinant routes each imply positive active-block
  mass, and `householderActiveBlockNorm2Sq_pos_sequence_of_leading_block_det_ne_zero`
  packages the determinant route for stored QR stages.  Two weak-component
  passes validate this as a scoped dependency.  The generic rectangular
  QR/preconditioner theorem remains open.  The new route-elimination theorem
  `not_forall_leadingBlock_upper_det_activeBlockPos_implies_offdiag_le_diag`
  shows that upper-triangular nonsingular leading blocks plus positive
  active-block mass still do not imply the row-wise off-diagonal domination
  field required by `StoredQRSourceOffDiagonalControl`.  The row-sorting
  invariance foundation is now added too: `vecPermute`, `rectPermuteRows`,
  `rectPermuteCols`, `vecNorm2Sq_permute`, `frobNormSqRect_permuteRows`,
  `frobNormSqRect_permuteCols`, `frobNormRect_permuteRows`,
  `frobNormRect_permuteCols`, `rectMatMulVec_permuteRows`,
  `rectLSGram_permuteRows`, `rectLSRhs_permuteRows`,
  `lsResidual_permuteRows`, and `lsObjective_permuteRows` prove that finite
  row sorting preserves rectangular least-squares objectives and
  normal-equation data.  The column-pivoting relabeling foundation is now added
  as well: `vecPermute_symm_vecPermute`, `vecPermute_vecPermute_symm`,
  `rectMatMulVec_permuteCols`, `rectLSGram_permuteCols`,
  `rectLSRhs_permuteCols`, `RectLSNormalEquations.of_permuteCols`,
  `lsResidual_permuteCols`, `lsObjective_permuteCols`, and
  `IsLeastSquaresMinimizer.of_permuteCols`; this foundation has two clean
  weak-component passes and is recorded as `LS.2g-dt`.  The unpivoted
  source-controlled solver handoff is now also composed into the Algorithm 2
  high-probability rounded objective theorem: `storedQRFinalR`,
  `storedQRFinalTopRhs`, `storedQRBackSubSolution`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver`
  close the equation (8) handoff once `StoredQRSourceOffDiagonalControl` is
  supplied.  The row-budget decomposition is now added:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product`
  split the off-diagonal-control field into row-growth upper budgets and
  diagonal lower-bound obligations.  Two weak-component passes validate this
  row-budget decomposition as a scoped dependency.  Next progress must prove
  those fields for the concrete raw stages and connect the rounded sequence
  result to the QR/preconditioner solve theorem.  The next row-growth
  propagation bridge is now added in `HouseholderQR.lean`:
  `qrLeadingOffdiagStop`,
  `fl_householderStoredPanel_sequence_completed_column_eq_pivot_succ`, and
  `fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_exact_stage_budgets_factor`
  convert Cox--Higham stage budgets into displayed leading-block upper
  off-diagonal row budgets.  Two weak-component passes validate this bridge:
  focused `lake build LeanFpAnalysis.FP.Algorithms.QR.HouseholderQR`, executable
  lookup, `git diff --check`, touched-file marker scan, axiom audit, PDF
  compile/repair/text extraction, and rendered pages 172 and 203 all pass with
  only the pre-existing unused-variable warnings and standard axiom footprint.
  The least-squares stage-budget handoff is now added:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product`
  compose stage budgets plus diagonal lower bounds into the local source-control
  and QR solve certificates.  Two weak-component passes validate this handoff:
  focused `lake build LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve`,
  executable lookup, `git diff --check`, touched-file marker scan, axiom audit,
  PDF compile/repair/text extraction, and rendered pages 173 and 203 all pass
  with only the pre-existing unused-variable warnings and standard axiom
  footprint.  Next progress must prove the diagonal lower-bound/nonbreakdown
  field or instantiate the remaining concrete stage-budget/pivot-zeroing
  fields.  The next scoped dependency has started: `HouseholderQR.lean` now
  defines `storedQRSignedStageVector`, `storedQRSignedStageBeta`, and proves
  `fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_signed_stage_budgets_factor`,
  specializing the displayed off-diagonal row-growth bridge to the actual
  signed stored-QR stages.  Focused build and two weak-component passes validate
  this specialization.  The least-squares layer now also proves the signed-stage
  source-control and solver handoff theorems
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product`.
  Focused build and two weak-component passes validate this handoff.  The exact
  pivot-column zeroing field is now formalized by
  `storedQRSignedStage_pivot_column_zero_below_of_trailingNorm_pos` and
  `storedQRSignedStage_pivot_zeroing_field_of_trailingNorm_pos`.  Focused build
  and two weak-component passes validate this field.  The norm-square-budget
  adapter `storedQRSignedStage_pivot_zeroing_field_of_normSqBudget`, together
  with
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget`,
  now removes the independent `hpivot` hypothesis from the signed-stage
  solver-facing route; focused build and two weak-component passes validate
  this adapter.  The uniform-stage-budget handoff
  `qrLeadingOffdiagStop_le`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget`
  now validates with two weak-component passes that monotone stage budgets
  remove the terminal row-budget-domination field.  The local exact
  same-reflector row split
  `storedQRSignedStage_exact_same_reflector_bound_of_prefix_or_active_stage_bounds`
  now has two clean weak-component passes: prefix rows use the zero-prefix
  Householder identity and active rows use the Cox--Higham signed-pivot
  active-row theorem.  The least-squares wrappers
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds`
  now remove the abstract `hexact` field from the uniform-stage-budget route by
  deriving it from concrete stage row/column entry bounds, pivot maximality,
  and norm-square nonbreakdown; focused build and two weak-component passes
  validate this scoped handoff.  The next proof target is the diagonal
  lower-bound/nonbreakdown field or remaining concrete stage-entry recurrence.
  The row-budget diagonal-bound handoff now has the offdiag-row-only correction
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows`,
  which require `rowBudget k i <= |S_k ii|` only for `i.val < k`.  Focused
  build and two weak-component passes validate this statement correction.
  The correction is now propagated through the stage-budget, signed-stage,
  norm-square-derived pivot-zeroing, uniform-stage-budget, and concrete
  stage-entry-bound LSQRSolve handoffs via the corresponding `_offdiag_rows`
  source-control and solver theorem families.  Focused LSQRSolve build passes
  with only the pre-existing HouseholderQR unused-variable warnings; two weak
  passes now close this checkpoint.  Next bottleneck progress should target
  either diagonal lower-bound/nonbreakdown for rows `i < k` or the remaining
  concrete stage-entry recurrence.
  The active/prefix stage-entry split was added next:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows`
  replace all-row stage-entry hypotheses by an active-suffix block budget plus a
  prefix displayed-row budget.  Focused LSQRSolve build passes, and two weak
  passes now validate this checkpoint.  The active-suffix recurrence handoff has
  since been added too:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows`
  instantiate the existing signed-pivot Cox--Higham active-block theorem for the
  stored QR pivot map.  Focused LSQRSolve build passes, and two weak-component
  passes now validate this checkpoint.  The prefix-row recurrence has now been
  added too: `storedQRSignedStage_active_block_bound_of_signed_stage_budget`
  exposes the active block as a reusable theorem,
  `storedQRSignedStage_prefix_row_bound_of_active_block_and_prefix_budget`
  proves displayed prefix-row bounds from a one-step prefix budget, and the
  source-control/solver wrappers with suffix
  `_activePrefix_activeBlockRecurrence_prefixRowRecurrence_offdiag_rows` remove
  the raw prefix-row-bound hypothesis.  Focused LSQRSolve build passes, and two
  weak-component passes now validate this checkpoint.  If resuming, target
  diagonal lower-bound/nonbreakdown, compact-product smallness, or concrete
  one-step active/prefix budget dependencies.
  The one-step budget dependency is now further packaged by a finite global
  compact-step budget: `storedQRSignedStageGlobalCompactBudget`,
  `storedQRSignedStage_compact_component_le_globalBudget`,
  `storedQRSignedStage_active_prefix_budgets_of_globalCompactBudget`, and the
  `_activePrefix_activeBlockRecurrence_globalCompactBudget_offdiag_rows`
  source-control/solver wrappers reduce displayed off-diagonal, active-block,
  and prefix-row one-step fields to one scalar recurrence.  Focused LSQRSolve
  build passes; two weak-component passes now validate this latest checkpoint.
  The completed-column preservation field has now been closed by
  `storedQRSignedStage_completed_column_preservation`, which derives old-column
  exact-reflector preservation from the stored prefix-lower-zero invariant and
  the zero-prefix Householder support lemma.  The completed-column global-budget
  source-control/solver wrappers build, and two weak-component passes are
  clean.  The per-pivot compact-product field is now packaged by
  `storedQRCompactSequenceProductBudget` and the
  `_globalCompactBudget_completedColumns_globalProduct_offdiag_rows`
  source-control/solver wrappers; two weak-component passes are clean.  The
  current RandNLA assembly theorem
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver`
  has two clean weak-component passes.  If resuming, target diagonal
  lower-bound/nonbreakdown and global compact-product smallness from a concrete
  pivoted/sorted/off-diagonal-controlled loop.
  The global-product smallness bookkeeping now also has the converse finite
  maximum adapters:
  `storedQRCompactSequenceProductBudget_lt_one_of_forall_expr_lt` and
  `storedQRCompactSequenceProductBudget_lt_one_of_forall_pivot_product`.  These
  prove that `storedQRCompactSequenceProductBudget < 1` follows from the
  finite per-pivot product inequalities.  Two weak-component passes are clean.
  The active/prefix global-product route now also reuses the local
  leading-block inverse-budget infrastructure:
  `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`
  derives the raw norm-square nonbreakdown margin from local determinant,
  `κ∞`/self-norm, and dual compact-budget data.  The corresponding
  `kappaInf_dualBudget` source-control, solver, and equation (8) wrappers
  build and remove `hbudgetNormSq` from the newest route when those structured
  assumptions are supplied.  Two weak-component passes are clean for this
  checkpoint: focused build, executable lookup, `git diff --check`, marker
  scan, qualified axiom audit, PDF compile, text extraction, and rendered-page
  inspection.  Resume by targeting per-pivot product inequalities,
  offdiag-row diagonal lower bounds, and concrete-loop local
  determinant/conditioning budgets.
- 2026-06-01: Added the diagonal-dominant global-product branch for equation
  (8).  New theorem names:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_diagDominant_globalProduct`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_globalProduct_kappaInf_dualBudget_solver`.
  These reuse `IsDiagDominantUpper`, the finite global-product budget, and the
  `κ∞`/dual-budget norm-square adapter to close the offdiag-row diagonal
  lower-bound field under explicit diagonal-dominance assumptions.  This is a
  scoped dependency closure only; diagonal dominance, local
  determinant/conditioning budgets, and product smallness still need to be
  proved for a concrete QR loop or kept visible.  Two weak-component passes are
  clean: focused build, executable lookup, `git diff --check`, marker scan,
  qualified axiom audit, PDF compile, text extraction, and rendered page
  inspection.
- 2026-06-01: Added
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_factor_norm_bounds`.
  It proves `storedQRCompactSequenceProductBudget < 1` from global bounds
  `D_k <= Dmax`, `||A_k(:,k)||_2 <= Nmax`, local diagonal dominance, and the
  scalar inequality `2 * Dmax * (m * (c_seq * Nmax)^2) < 1`.  This reduces the
  red product-smallness dependency to concrete-loop proofs of those global
  factor/norm bounds plus the scalar inequality.  Two weak-component passes are
  clean: focused build, executable lookup, `git diff --check`, marker scan,
  qualified axiom audit, PDF compile, text extraction, and rendered page
  inspection.
- 2026-06-01: Added the canonical finite-max product-smallness adapter
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness`
  plus `storedQRDiagDominantInvFactorBudget`,
  `storedQRDiagDominantInvFactor_le_budget`,
  `storedQRDiagDominantInvFactorBudget_nonneg`,
  `storedQRPivotColumnNormBudget`, `storedQRPivotColumnNorm_le_budget`, and
  `storedQRPivotColumnNormBudget_nonneg`.  These choose finite maxima for the
  diagonal-dominant inverse factor and pivot-column norm, remove separate
  `Dmax`/`Nmax` bound hypotheses, and leave only the scalar smallness
  inequality for the canonical maxima.  Two weak-component passes are clean:
  focused build, executable lookup, `git diff --check`, marker scan, qualified
  axiom audit, PDF compile, text extraction, and rendered page inspection.
- 2026-06-01: Threaded the canonical finite-max product-smallness scalar into
  the diagonal-dominant equation (8) QR handoff.  New theorem names:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_diagDominant_finiteMaxSmallness`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_kappaInf_dualBudget_solver`.
  This removes the raw `storedQRCompactSequenceProductBudget < 1` field from
  that theorem surface when the scalar inequality over
  `storedQRDiagDominantInvFactorBudget` and `storedQRPivotColumnNormBudget` is
  supplied.  Focused LSQRSolve and LeastSquaresSketch builds pass, and two
  weak-component passes are clean: `git diff --check`, marker scan, focused
  LeastSquaresSketch build, executable lookup, qualified axiom audit, PDF
  compile, text extraction, and rendered page inspection.  The axiom audit
  reports only standard `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-06-01: Added the concrete-dual finite-max diagonal-dominant equation (8)
  handoff.  New theorem names:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual`
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver`.
  These reuse the local concrete diagonal-dominant inverse-budget theorem and
  the canonical finite-max product-smallness adapter, removing auxiliary `κ`,
  `K`, and dual compact-budget fields from the finite-max diagonal-dominant
  QR/equation (8) surface.  First weak-component validation is clean: focused
  build, executable lookup, `git diff --check`, marker scan, qualified axiom
  audit, PDF compile, text extraction, and rendered-page inspection all passed.
  The axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  The repeated pass is also clean, and the temporary axiom-audit
  file was deleted.  This checkpoint now has two consecutive clean passes.
- 2026-06-01: Added the determinant-free concrete-dual finite-max
  diagonal-dominant equation (8) handoff.  New theorem names:
  `det_ne_zero_of_diagDominantUpper`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSmallness_concreteDual`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver_of_diagDominant`.
  The local determinant field is now derived from `IsDiagDominantUpper`; the
  finite-max concrete-dual branch no longer exposes local determinant,
  auxiliary `κ`, auxiliary `K`, or dual compact-budget hypotheses.  Two
  weak-component validation passes are clean: focused build, executable lookup,
  `git diff --check`, marker scan, qualified axiom audit, PDF compile, text
  extraction, and rendered-page inspection all passed twice.  The repeated
  axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`, and the temporary axiom-audit file was deleted.
- 2026-06-01: Added the direct packaged off-diagonal-control RandNLA equation
  (8) handoff.  New theorem name:
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver`.
  It consumes samplewise `StoredQROffDiagonalControlInvariant` and composes the
  local stored-QR backward-error certificate with the already proved
  high-probability finite-Loewner sampled-row objective theorem.  The existing
  source-shaped theorem
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver`
  now derives the packaged invariant via
  `StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl` and reuses
  the direct theorem.  Two weak-component validation passes are clean: focused
  build, executable lookup, `git diff --check`, marker scan, qualified axiom
  audit, PDF compile, text extraction, and rendered-page inspection all passed
  twice.  The repeated axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  This closes the route-1
  solver-to-RandNLA handoff for the packaged invariant, not the proof that a
  concrete arbitrary no-pivot QR loop satisfies that invariant.
- 2026-06-01: Added the finite-max diagonal-dominant constructor for the
  packaged route-1 invariant.  New theorem name:
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness`.
  It derives `StoredQROffDiagonalControlInvariant` from local
  `IsDiagDominantUpper` leading blocks and the canonical scalar finite-max
  smallness inequality by reusing `det_ne_zero_of_diagDominantUpper` and
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness`.
  First weak-component validation is clean: focused LSQRSolve build,
  executable lookup, `git diff --check`, marker scan, qualified axiom audit,
  PDF compile, text extraction, and rendered page inspection all passed.  The
  axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  The remaining route-1 red dependencies are proving or
  classifying local diagonal dominance and the scalar finite-max smallness
  inequality for a concrete no-pivot stored QR loop.
  The repeated validation pass is also clean: focused LSQRSolve build,
  executable lookup, `git diff --check`, marker scan, qualified axiom audit,
  PDF compile, text extraction, and rendered page inspection passed again.
  This checkpoint now has two consecutive clean passes.
- 2026-06-01: Added the Cox--Higham row-budget diagonal-lower-bound route
  elimination.  New theorem name:
  `not_forall_leadingBlock_upper_det_activeBlockPos_offdiagBudget_implies_rowBudget_diag`.
  It uses the local `[[1,2],[0,1]]` witness with row budget `2` to show that
  upper-triangular nonsingular leading blocks, positive active-block mass, and
  a valid strict-upper-entry row budget do not imply the matching diagonal
  lower-bound field; the first displayed diagonal has magnitude `1`.  Two
  weak-component validation passes are clean: focused LSQRSolve build,
  executable lookup, `git diff --check`, touched Lean marker scan, qualified
  axiom audit, PDF compile, text extraction, and rendered page inspection
  passed twice.  This is route elimination only.  The next red-bottleneck
  progress must target a genuine diagonal lower-bound/nonbreakdown invariant,
  a stronger source theorem that supplies it, or a final solver-facing theorem
  that keeps the field explicit.
- 2026-06-01: Added the explicit-domain row-budget certificate
  `StoredQRDisplayedRowBudgetControl` and the wrapper theorems
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product`.
  This packages the Cox--Higham displayed strict-upper row-budget field and
  the matching offdiag-row diagonal lower-bound/nonbreakdown field as a visible
  source/domain assumption.  Two weak-component validations are clean:
  focused LSQRSolve build, executable lookup, `git diff --check`, marker scan,
  qualified axiom audit, PDF compile, text extraction, and rendered-page
  inspection all passed twice; the axiom audit reports only standard
  `propext`, `Classical.choice`, and `Quot.sound`, and the temporary audit file
  was deleted after validation.  This is a theorem-statement correction, not a
  proof of the diagonal lower-bound invariant.
- 2026-06-01: Added the equation (8) probability-level row-budget-control
  handoff
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver`.
  It consumes samplewise `StoredQRDisplayedRowBudgetControl`, derives the
  source-shaped stored-QR certificate, and reuses the high-probability rounded
  sampled-row objective theorem.  Focused RandNLA least-squares build passed
  with only the pre-existing `HouseholderQR.lean` unused-variable warnings.
  Two weak-component validations are clean: executable lookup, `git
  diff --check`, marker scan, qualified axiom audit, PDF compile, text
  extraction, and rendered page inspection all passed twice; the axiom audit
  reports only standard `propext`, `Classical.choice`, and `Quot.sound`, and
  the temporary audit file was deleted after validation.
  This is a scoped theorem under visible domain assumptions, not a proof of
  the packaged row-budget certificate from a concrete loop.
- 2026-06-01: Added the `κ∞`/dual-budget equation (8) row-budget-control
  probability handoff
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_kappaInf_dualBudget_solver`.
  It reuses
  `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`
  to derive the norm-square nonbreakdown margin, then calls the existing
  row-budget-control solver theorem.  First weak-component validation is clean:
  focused RandNLA least-squares build, executable lookup, `git diff --check`,
  marker scan, qualified axiom audit, PDF compile, text extraction, and rendered
  page inspection passed; the repeated pass is also clean with the same standard
  axiom audit result.  This removes the raw norm-square
  nonbreakdown hypothesis from the row-budget probability handoff but leaves
  `StoredQRDisplayedRowBudgetControl`, local determinant/`κ∞`/dual-budget data,
  and compact-product smallness visible.
- 2026-06-01: Added
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_budgets_factor_of_normSqBudget`
  in `LSQRSolve.lean`.  This builds the named row-budget control certificate
  from signed-stage Cox--Higham row-growth budgets, deriving pivot-column
  zeroing from the norm-square nonbreakdown budget and keeping the offdiag-row
  diagonal lower-bound field visible.  First weak-component validation is clean:
  focused LSQRSolve build, executable lookup, `git diff --check`, marker scan,
  qualified axiom audit, PDF compile/text/render checks all passed; the axiom
  audit reports only standard `propext`, `Classical.choice`, and `Quot.sound`.
  The repeated pass is also clean with the same standard axiom audit result and
  readable PDF pages 174--175.  The remaining package-producing dependencies are
  the offdiag-row diagonal lower-bound/nonbreakdown invariant and concrete
  stage-budget recurrence.
- 2026-06-01: Added
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_factor_of_normSqBudget`
  in `LSQRSolve.lean`.  This uniform-stage constructor sets
  `rowBudget k i = stageBudget k` and uses `qrLeadingOffdiagStop_le` plus
  monotonicity to discharge terminal row-budget domination.  First
  weak-component validation is clean: focused LSQRSolve build, executable
  lookup, `git diff --check`, marker scan, qualified axiom audit, PDF
  compile/text/render checks all passed; the axiom audit reports only standard
  `propext`, `Classical.choice`, and `Quot.sound`.  The repeated pass is also
  clean with the same standard axiom audit result and readable PDF pages
  174--175.
- 2026-06-01: Added
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_of_normSqBudget`
  and
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_kappaInf_dualBudget`
  in `LSQRSolve.lean`.  These constructors package the selected
  `κ∞`/dual-budget route: the norm-square version derives
  `StoredQRDisplayedRowBudgetControl` from monotone stage budgets,
  completed-column preservation, active-block recurrence, prefix-row
  recurrence, pivot maximality, finite global compact-step recurrence, and the
  norm-square nonbreakdown budget; the `κ∞`/dual-budget version derives that
  norm-square budget from the existing leading-block inverse-budget adapter.
  First weak-component validation is clean: `git diff --check`, touched Lean
  marker scan, focused LSQRSolve build, executable lookup, qualified axiom
  audit, PDF compile/text checks, and rendered page 175 passed; the axiom audit
  reports only standard `propext`, `Classical.choice`, and `Quot.sound`.  The
  repeated weak-component pass is also clean with the same standard axiom audit
  result and readable page 175.  This is a dependency closure, not a proof of
  the offdiag-row diagonal lower-bound/nonbreakdown invariant or final generic
  QR/preconditioner theorem.
- 2026-06-01: Added the canonical row-max row-budget bridge in
  `LSQRSolve.lean`: `qrLeadingStrictUpperRowMaxBudget`,
  `qrLeadingStrictUpperRowMaxBudget_entry_le`,
  `qrLeadingStrictUpperRowMaxBudget_le_diag_of_offdiag`, and
  `StoredQRDisplayedRowBudgetControl.of_sourceOffDiagonalControl_rowMaxBudget`.
  This packages an existing `StoredQRSourceOffDiagonalControl` field into
  `StoredQRDisplayedRowBudgetControl` by taking each row budget to be the finite
  maximum of strict-upper absolute values in the displayed row.  Focused build
  passed with only the pre-existing HouseholderQR warnings; first
  weak-component validation is clean: whitespace, marker, focused build,
  executable lookup, qualified axiom audit, PDF compile/text, and rendered page
  175 passed.  This is a safe-direction bridge, not a proof of source
  off-diagonal domination or generic QR/preconditioner closure.  The repeated
  weak-component pass is also clean with the same standard axiom audit result,
  executable lookup exposure, PDF text extraction, and readable rendered page
  175.
- 2026-06-01: Added the direct finite-max diagonal-dominant RandNLA equation
  (8) wrapper for the packaged route-1 invariant.  New theorem name:
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxSmallness`.
  It applies
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness`
  samplewise, then reuses the direct packaged off-diagonal-control theorem
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver`.
  This removes the packaged-invariant hypothesis from the diagonal-dominant
  finite-max probability surface, while leaving local diagonal dominance and
  the canonical scalar finite-max smallness inequality visible.  First
  weak-component validation is clean: focused build, executable lookup, `git
  diff --check`, marker scan, qualified axiom audit, PDF compile/text, and
  rendered-page inspection passed; the axiom audit reports only standard
  `propext`, `Classical.choice`, and `Quot.sound`.
  The repeated weak-component pass is also clean with the same standard axiom
  audit result and readable rendered pages 115 and 186.  This checkpoint now
  has two consecutive clean passes.
- 2026-06-01: Added the stronger exact-no-pivot route-elimination theorem
  `not_forall_exact_trailing_householder_sequence_implies_diagDominant_and_property`
  in `LSQRSolve.lean`.  It reuses the existing exact two-step Householder
  counterexample to show that the standard no-pivot recurrence cannot
  universally imply diagonal dominance together with any final-block property
  `P`.  This directly rules out a hidden proof of the finite-max
  diagonal-dominant route from the exact recurrence alone; focused LSQRSolve
  build passed and first weak-component validation is clean (`git diff
  --check`, marker scan, focused build, executable lookup, qualified axiom
  audit, PDF compile/text extraction, and rendered page 168).  Repeated
  validation is also clean with the same standard axiom audit result and
  readable rendered page 168.  This closes the route-elimination dependency;
  positive completion still needs a stronger invariant, a pivoted/sorted
  theorem family, or visible scoped assumptions.
- 2026-06-01: Added active-max-pivot variants of the packaged global
  compact-step row-budget constructors in `LSQRSolve.lean`:
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_of_normSqBudget`
  and
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_kappaInf_dualBudget`.
  They derive the raw pivot-maximality field from
  `householderActiveMaxPivotColumn_pivot_max`, letting the row-budget package
  expose the algorithmic finite active max-pivot policy instead of a bare
  pivot inequality.  Focused LSQRSolve build passed; first weak-component
  validation is clean (`git diff --check`, marker scan, focused build,
  executable lookup, qualified axiom audit, PDF compile/text extraction, and
  rendered pages 175--176).  The repeated validation pass is also clean with
  the same standard axiom audit result and readable rendered pages 175--176.
  This checkpoint now has two consecutive clean passes.  It closes only the
  pivot-max field for the packaged row-budget route, not diagonal lower
  bounds/nonbreakdown, determinant/conditioning data, compact-product
  smallness, or final QR/preconditioner assembly.
- 2026-06-01: Added the probability-level active-max-pivot wrapper
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`
  in `LeastSquaresSketch.lean`.  It replaces the raw samplewise pivot-max
  inequality in the active/prefix global-product `κ∞` equation (8) theorem
  surface by the policy equation choosing `householderActiveMaxPivotColumn` as
  the displayed pivot column, derives the raw field with
  `householderActiveMaxPivotColumn_pivot_max`, then applies the existing
  probability theorem.  First weak-component validation is clean: `git diff
  --check`, marker scan, focused RandNLA least-squares build, executable
  lookup, qualified axiom audit with only standard axioms, PDF compile/text
  extraction, and rendered page 185 passed.  Repeated validation is also clean
  with the same standard axiom audit result and readable rendered page 185.
  This checkpoint now has two consecutive clean passes.  It closes only the
  probability-layer pivot-max surface field; diagonal lower bounds,
  determinant/conditioning data, compact-product smallness, and the final
  generic QR/preconditioner theorem remain open or visible assumptions.
- 2026-06-01: Added the probability-level active-max-pivot row-budget
  global-product wrapper
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`
  in `LeastSquaresSketch.lean`.  It constructs samplewise
  `StoredQRDisplayedRowBudgetControl` from the active-max-pivot global
  compact-step constructor and then applies the finite global-product
  row-budget equation (8) theorem.  First weak-component validation is clean:
  `git diff --check`, marker scan, focused RandNLA least-squares build,
  executable lookup, qualified axiom audit with only standard axioms, PDF
  compile/text extraction, and rendered page 185 passed.  The repeated pass is
  also clean with the same standard axiom audit result and readable rendered
  page 185.  This checkpoint now has two consecutive clean passes.  It closes
  only a packaging/assembly edge; diagonal lower bounds, determinant or
  conditioning data, compact-product smallness, and the final generic
  QR/preconditioner theorem remain open or visible assumptions.
- 2026-06-01: Added the active-max-pivot row-budget diagonal route-elimination
  theorem in `LSQRSolve.lean`.  The new local witnesses
  `activeMaxPivotRowBudgetDiagCounterexampleA0` and
  `activeMaxPivotRowBudgetDiagCounterexampleSeq` show that a first stage with
  an active max-pivot column can be followed by the same row-budget diagonal
  failure stage `[[1,2],[0,1]]`.  The theorem
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_offdiagBudget_implies_rowBudget_diag`
  therefore rules out deriving the diagonal lower-bound/nonbreakdown field
  from active-block mass, active max-pivot selection, and row-growth upper
  budgets alone.  First weak-component validation is clean: `git diff
  --check`, touched Lean marker scan, focused LSQRSolve build, executable
  lookup, qualified axiom audit, PDF compile/text extraction, and rendered page
  169 passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  The repeated weak-component pass is
  also clean with the same standard axiom audit result and readable rendered
  page 169.  This checkpoint now has two consecutive clean passes.  This is
  route elimination, not a positive diagonal lower-bound invariant.
- 2026-06-01: Added the active-block-budget strengthening
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowBudget_diag`
  in `LSQRSolve.lean`.  It reuses the two-stage active max-pivot witness and
  additionally assumes that the same nonnegative row budget bounds every active
  trailing-block entry at each displayed stage.  The witness satisfies that
  active-block magnitude budget with row budget `2`, but the second displayed
  stage still violates the diagonal lower-bound field because the relevant
  diagonal magnitude is `1`.  This red-bottleneck route-elimination dependency
  now has two clean weak-component passes: repeated `git diff --check`, touched
  Lean marker scan, focused `LSQRSolve` build, executable lookup, qualified
  axiom audit, PDF compile/text extraction, and rendered-page inspection passed.
  The axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  It is route elimination, not a positive diagonal lower-bound
  invariant.
- 2026-06-01: Added the meta-property strengthening
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_property_implies_rowBudget_diag`
  in `LSQRSolve.lean`.  It shows that adding an arbitrary auxiliary side
  property `P A_hat rowBudget` to the active-block-budget row-budget route
  still cannot imply the diagonal lower-bound field; the proof chooses
  `P := True` and reuses the active-block-budget route-elimination theorem.
  This is a guardrail for the red bottleneck: unrelated scalar/product
  hypotheses cannot be treated as hidden diagonal nonbreakdown.  Two
  weak-component validation passes are clean: repeated `git diff --check`,
  touched Lean marker scan, focused `LSQRSolve` build, executable lookup,
  qualified axiom audit, PDF compile/text extraction, and rendered-page
  inspection passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  The remaining valid progress routes
  are a genuine diagonal lower-bound/nonbreakdown invariant, determinant or
  conditioning field closure, compact-product smallness, or an explicit
  visible-assumption theorem surface.
- 2026-06-01: Added the solver-facing active-max-pivot wrapper for the
  active/prefix global-product `κ∞` QR route:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_offdiag_rows`.
  It derives the raw pivot-maximality inequality from the finite active pivot
  selector using `householderActiveMaxPivotColumn_pivot_max` and applies the
  existing raw-pivot solver theorem.  This closes only the local solver-layer
  pivot-policy dependency.  The remaining QR/preconditioner red-bottleneck
  dependencies are still the diagonal lower-bound/nonbreakdown invariant,
  local determinant/conditioning data, dual compact-budget assumptions,
  compact-product smallness, and final generic assembly.  Two weak-component
  passes are clean: whitespace, touched-source marker scan, focused LSQRSolve
  build, executable lookup, qualified axiom audit, PDF compile/text extraction,
  and rendered-page inspection of pages 184--185 passed, with only standard
  `propext`, `Classical.choice`, and `Quot.sound` in the axiom audit.
- 2026-06-01: Added the solver-facing row-budget-control finite-global-product
  wrappers:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_globalProduct`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_rowBudgetControl_globalProduct`.
  These close the local solver-layer per-pivot compact-product family for the
  packaged row-budget route by reusing the existing source-control
  global-product certificate and the `κ∞`/dual-budget norm-square adapter.
  Two weak-component passes are clean: whitespace, touched-source marker scan,
  focused LSQRSolve build, executable lookup, qualified axiom audit, PDF
  compile/text extraction, and rendered-page inspection of pages 184--185
  passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  Remaining QR/preconditioner
  red-bottleneck dependencies are still `StoredQRDisplayedRowBudgetControl`,
  local determinant/conditioning or dual-budget data, scalar compact-product
  smallness, and final generic assembly.
- 2026-06-01: Added the route-1 row-max contraction handoff for the
  rectangular QR/preconditioner bottleneck.  `LSQRSolve.lean` now proves
  `StoredQRDisplayedRowBudgetControl.of_rowMaxBudget_le_diag_factor`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowMaxBudgetFactor_globalProduct`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxBudgetFactor_globalProduct`.
  These theorem surfaces say that if a computed-loop invariant supplies a
  scalar `ρ <= 1` with every canonical displayed strict-upper row maximum below
  `ρ * |diag|`, then the packaged row-budget certificate and local solver
  handoff follow under the usual stored recurrence, determinant, norm-square,
  and global compact-product hypotheses.  This is a positive route-1 handoff,
  not a proof of the contraction invariant from generic no-pivot QR.
- 2026-06-01: Added the scalar row-max/diagonal defect handoff for the same
  rectangular QR/preconditioner route.  `LSQRSolve.lean` now defines
  `storedQRRowMaxDiagDefectBudget`, proves
  `storedQRRowMaxDiagDefect_le_budget`, and exposes
  `StoredQRDisplayedRowBudgetControl.of_rowMaxDiagDefectBudget_nonpos`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct`.
  The scalar condition `storedQRRowMaxDiagDefectBudget hmn A_hat <= 0`
  packages the `ρ = 1` row-max contraction branch as a finite maximum over
  displayed defects `rowMax - |diag|`.  Two weak-component validation passes
  are clean: repeated whitespace checks, touched-source marker scans, focused
  LSQRSolve builds, executable lookup, qualified axiom audits, PDF
  compile/text extraction, and rendered-page inspections passed; the axiom
  audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  This reduces the shape of the
  row-budget dependency but does not prove the scalar defect condition,
  determinant/conditioning data, norm-square nonbreakdown, product smallness,
  or the final generic QR/preconditioner theorem from ordinary no-pivot QR.
- 2026-06-01: Added the scalar row-max defect route-elimination theorem pair
  for the rectangular QR/preconditioner bottleneck.  `LSQRSolve.lean` now
  proves
  `exactHouseholderQRDiagDominanceCounterexample_rowMaxDiagDefectBudget_pos`
  and
  `not_forall_exact_trailing_householder_sequence_implies_rowMaxDiagDefectBudget_nonpos`.
  The exact two-stage no-pivot Householder counterexample has positive
  `storedQRRowMaxDiagDefectBudget`, so exact recurrence plus valid squared-norm
  identities and nonzero denominators cannot universally imply the
  nonpositive scalar defect condition.  First weak-component validation is
  clean: whitespace, touched-source marker scan, focused LSQRSolve build,
  executable lookup, qualified axiom audit, PDF compile/text extraction, and
  rendered-page inspection of pages 177--179 passed; the axiom audit reports
  only standard `propext`, `Classical.choice`, and `Quot.sound`.  The repeated
  pass is also clean with the same standard axiom audit result, executable
  lookup exposure, PDF text extraction, and readable rendered pages 177--179.
  This is route elimination only, not a positive scalar defect invariant.
- 2026-06-01: Added the probability-level scalar row-max-defect global-product
  equation (8) wrapper
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver`
  in `LeastSquaresSketch.lean`.  It builds the samplewise row-budget
  certificate from `storedQRRowMaxDiagDefectBudget <= 0`, derives per-pivot
  compact-product smallness from `storedQRCompactSequenceProductBudget < 1`,
  and reuses the row-budget-control high-probability objective theorem.  First
  weak-component validation is clean: whitespace, touched-source marker scan,
  focused LeastSquaresSketch build, executable lookup, qualified axiom audit,
  PDF compile/text extraction, and rendered-page inspection of pages 114--118
  passed; the axiom audit reports only standard `propext`, `Classical.choice`,
  and `Quot.sound`.  This is an assembly closure only; the scalar defect
  invariant and concrete-loop determinant/nonbreakdown/product-smallness fields
  remain open or visible.  Repeated validation is also clean with the same
  standard axiom audit result, executable lookup exposure, PDF text extraction,
  and readable rendered pages 114--118, giving this dependency two consecutive
  clean passes.
- 2026-06-01: Added the probability-level primitive
  norm-square/off-diagonal-product equation (8) wrapper
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_leadingBlock_det_ne_zero_normSqBudget_offdiag_product_solver`
  in `LeastSquaresSketch.lean`.  It constructs
  `StoredQRSourceOffDiagonalControl` samplewise from leading-block determinant
  nonzeroness, dimensioned norm-square nonbreakdown, row-wise off-diagonal
  domination, and per-pivot compact-product smallness before applying the
  source-shaped high-probability objective theorem.  First weak-component
  validation is clean: whitespace, touched-source marker scan, focused
  LeastSquaresSketch build, executable lookup, qualified axiom audit, PDF
  compile/text extraction, and rendered-page inspection of pages 114--119
  passed; the axiom audit reports only standard `propext`, `Classical.choice`,
  and `Quot.sound`.  This is an assembly closure only; determinant/nonbreakdown,
  off-diagonal domination, product smallness, and the final generic QR theorem
  remain open or visible.  Repeated validation is also clean with the same
  standard axiom audit result, executable lookup exposure, PDF text extraction,
  and readable rendered pages 114--119, giving this dependency two consecutive
  clean passes.
- 2026-06-01: Added the diagonal-dominance to scalar row-max-defect bridge
  `storedQRRowMaxDiagDefectBudget_nonpos_of_diagDominant` and
  `StoredQRDisplayedRowBudgetControl.of_diagDominant` in `LSQRSolve.lean`.
  Local `IsDiagDominantUpper` displayed leading blocks now imply
  `storedQRRowMaxDiagDefectBudget <= 0`, and hence the packaged row-budget
  certificate, by taking the finite maximum of the row-wise strict-upper
  diagonal-dominance inequalities.  First weak-component validation is clean:
  whitespace, touched-source marker scan, focused LSQRSolve build, executable
  lookup, qualified axiom audit, PDF compile/text extraction, and rendered-page
  inspection of pages 177--179 passed; the axiom audit reports only standard
  `propext`, `Classical.choice`, and `Quot.sound`.  This is a bridge between
  visible route surfaces, not a proof that generic no-pivot QR is diagonally
  dominant.  Repeated validation is also clean with the same standard axiom
  audit result, executable lookup exposure, PDF text extraction, and readable
  rendered pages 177--179, giving this dependency two consecutive clean passes.
- 2026-06-02: Added the exact/zero-compact compact-product endpoint
  `storedQRCompactSequenceProductBudget_lt_one_of_relativeBudget_eq_zero` in
  `LSQRSolve.lean`.  If
  `storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha = 0`, then
  the stored compact-product budget is automatically below one.  This closes
  only the exact/zero-compact product-smallness dependency for the
  rectangular QR/preconditioner bottleneck; positive floating-point
  compact-product smallness, local diagonal dominance/off-diagonal control,
  determinant/conditioning fields, norm-square nonbreakdown, and the final
  generic equation (8) QR/preconditioner theorem remain open.  Two
  weak-component passes are clean: focused LSQRSolve build, executable lookup,
  `git diff --check`, touched Lean marker scan, qualified axiom audit, PDF
  compile/text extraction, and rendered-page inspection of page 186 passed.
  The axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-06-02: Added the positive relative-budget cap theorem
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_relativeBudget_le`
  in `LSQRSolve.lean`.  Under local diagonal dominance, if the stored compact
  sequence relative budget is bounded by a nonnegative scalar `cmax`, then the
  canonical finite-max product smallness condition may be checked with `cmax`
  in place of the exact relative budget.  This reduces the positive-budget
  compact-product blocker to proving the cap and scalar inequality; it does not
  prove local diagonal dominance/off-diagonal control, determinant/conditioning
  fields, norm-square nonbreakdown, or the final generic equation (8)
  QR/preconditioner theorem.  First weak-component validation is clean:
  focused LSQRSolve build, executable lookup, `git diff --check`, touched Lean
  marker scan, qualified axiom audit, PDF compile/text extraction, and
  rendered-page inspection of pages 187--188 passed.  The axiom audit reports
  only standard `propext`, `Classical.choice`, and `Quot.sound`.  Repeated
  weak-component validation is also clean with the same standard axiom audit
  result, executable lookup exposure, PDF text extraction, and readable
  rendered pages 187--188, giving this dependency two consecutive clean passes.
- 2026-06-02: Added the uniform per-step compact-panel cap reduction for the
  positive-budget compact-product route.  `HouseholderQR.lean` now proves
  `storedQRCompactSequenceRelativeBudget_le_mul_of_step_le`, and
  `LSQRSolve.lean` now proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_stepBudget_le`.
  A uniform one-step relative budget cap `cStep` gives the sequence cap
  `n * cStep`, which is then fed into the canonical finite-max product
  threshold.  This reduces the route-1 blocker to proving the one-step cap and
  scalar inequality, while local diagonal dominance/off-diagonal control,
  determinant/conditioning/nonbreakdown, and the final generic equation (8)
  QR/preconditioner theorem remain open.  Two weak-component passes are clean:
  focused LSQRSolve build, executable lookup, `git diff --check`, touched Lean
  marker scan, qualified axiom audit, PDF compile/text extraction, and
  rendered-page inspection of pages 187--188 passed.  The axiom audit reports
  only standard `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-06-02: Added the vector-level compact column/RHS cap reduction for the
  same route.  `HouseholderApply.lean` proves
  `householderCompactPanelRelativeBudget_le_mul_add_of_column_rhs_le`;
  `HouseholderQR.lean` proves
  `storedQRCompactStepRelativeBudget_le_mul_add_of_column_rhs_le`; and
  `LSQRSolve.lean` proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsBudget_le`.
  The product-smallness chain now has an explicit local reduction
  `cCol,cRhs -> n * cCol + cRhs -> n * (n * cCol + cRhs)`.  This still leaves
  vector-level compact caps, the scalar smallness inequality, local diagonal
  dominance/off-diagonal control, determinant/conditioning/nonbreakdown, and
  the final generic equation (8) QR/preconditioner theorem as open
  red-bottleneck dependencies.  Two weak-component passes were clean, with only
  pre-existing HouseholderQR unused-variable warnings and standard axioms in
  the audit.
- 2026-06-02: Added the primitive norm-budget compact column/RHS cap reduction.
  `HouseholderApply.lean` proves
  `householderCompactRelativeBudget_le_of_normBudget_le_mul` and
  `householderCompactPanelRelativeBudget_le_mul_add_of_normBudget_le_mul`;
  `HouseholderQR.lean` proves
  `storedQRCompactStepRelativeBudget_le_mul_add_of_normBudget_le_mul`; and
  `LSQRSolve.lean` proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsNormBudget_le`.
  The positive-budget compact-product chain can now start from primitive
  `householderCompactNormBudget <= c * vecNorm2` hypotheses and still uses
  the cap chain `cCol,cRhs -> n * cCol + cRhs -> n * (n * cCol + cRhs)`.
  This narrows the next route-1 target to deriving those primitive norm-budget
  inequalities from the local FP dot/scale/subtract model, or to scalar
  smallness/local off-diagonal-control work.  Two weak-component passes are
  clean: repeated whitespace checks, touched Lean marker scans, focused
  HouseholderApply/HouseholderQR/LSQRSolve builds, executable lookup, qualified
  axiom audits, theorem PDF compile/text extraction, and rendered inspection of
  pages 187--190 all passed with only pre-existing HouseholderQR unused-variable
  warnings and standard axioms.
- 2026-06-02: Added the componentwise compact column/RHS cap reduction below
  the primitive norm-budget bridge.  `HouseholderApply.lean` proves
  `householderCompactNormBudget_le_mul_of_componentBudget_le_mul_abs`,
  `householderCompactRelativeBudget_le_of_componentBudget_le_mul_abs`, and
  `householderCompactPanelRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs`;
  `HouseholderQR.lean` proves
  `storedQRCompactStepRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs`;
  and `LSQRSolve.lean` proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsComponentBudget_le`.
  This lowers the positive-budget compact-product chain to entrywise
  `householderCompactComponentBudget_i <= c * |input_i|` hypotheses, then
  reuses the same `cCol,cRhs -> n * cCol + cRhs -> n * (n * cCol + cRhs)` cap
  chain.  Two weak-component validations are clean: repeated whitespace
  checks, touched Lean marker scans, focused LSQRSolve builds, executable
  lookup, qualified axiom audits, theorem PDF compile/text extraction, and
  rendered inspection of pages 188--190 passed with only pre-existing
  HouseholderQR unused-variable warnings and standard axioms.  The next route-1
  targets are proving those entrywise FP inequalities, scalar smallness, or
  local off-diagonal-control/diagonal dominance fields.
- 2026-06-02: Added the explicit compact Householder norm-coefficient route for
  the equation (8) QR/preconditioner compact-product bottleneck.  The local
  Householder file now proves `householderAbsDotBudget_le_vecNorm2_mul`,
  defines `householderCompactUpdateCoeff` and
  `householderCompactNormBudgetCoeff`, proves
  `householderCompactComponentBudget_le_updateCoeff_mul_norm`,
  `householderCompactNormBudget_le_normBudgetCoeff_mul`,
  `householderCompactRelativeBudget_le_normBudgetCoeff`, and
  `householderCompactPanelRelativeBudget_le_mul_add_normBudgetCoeff`.  The QR
  file adds `storedQRCompactStepNormBudgetCoeff` and
  `storedQRCompactStepRelativeBudget_le_mul_add_normBudgetCoeff`; the LS file
  adds
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeff_le`.
  This is the valid primitive FP reduction: it charges the nonlocal compact
  update to `||input||_2 * |v_i|` and the final subtraction to `|input_i|`,
  rather than requiring the generally false cap `budget_i <= c * |input_i|`.
  Two weak-component validation passes are clean: focused builds, repeated
  `git diff --check`, touched-file marker scan, executable lookup, qualified
  axiom audit, PDF compile, targeted `pdftotext`, and rendered pages 188--192
  all passed.
- 2026-06-02: Added the canonical finite maximum for the compact Householder
  norm-coefficient route.  `HouseholderQR.lean` proves
  `storedQRCompactStepNormBudgetCoeff_nonneg`; `LSQRSolve.lean` defines
  `storedQRCompactStepNormBudgetCoeffBudget`, proves
  `storedQRCompactStepNormBudgetCoeff_le_budget` and
  `storedQRCompactStepNormBudgetCoeffBudget_nonneg`, and proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget`.
  This removes the arbitrary `cHH` field from the product theorem by choosing
  the finite max of the actual stored-stage coefficients.  Two
  weak-component validation passes are clean: repeated `git diff --check`,
  touched-file marker scans, focused LSQRSolve build, executable lookup,
  qualified axiom audits, PDF compile/text extraction, and rendered pages
  188--193 all passed.  Scalar smallness for the displayed max and local
  diagonal/off-diagonal or determinant/conditioning fields remain.
- 2026-06-02: Added the coefficient-maximum equation (8) handoff.  The
  least-squares layer proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffSmallness`,
  deriving the route-1 package from local diagonal dominance and the canonical
  `storedQRCompactStepNormBudgetCoeffBudget` scalar inequality.  The RandNLA
  layer proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxNormBudgetCoeffSmallness`,
  composing that package into the high-probability sampled least-squares
  objective theorem.  Two weak-component validation passes are clean (repeated
  `git diff --check`, touched-file marker scans, focused RandNLA build,
  executable lookup, qualified axiom audits, PDF compile/text extraction, and
  rendered pages 190--192); scalar smallness for the displayed max and local
  diagonal/off-diagonal or determinant/conditioning fields remain.
- 2026-06-02: Added the bounded scalar-smallness certificate for the
  coefficient-maximum route.  `LSQRSolve.lean` proves
  `storedQRCompactNormBudgetCoeffSmallness_of_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget_bounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffBoundedSmallness`.
  These reduce the exact canonical scalar condition to route constants
  `Dmax`, `Cmax`, and `Nmax` that dominate the canonical diagonal-dominant
  inverse budget, compact Householder coefficient maximum, and pivot-column
  norm budget; nonnegativity of those constants is derived from domination.
  Two weak-component validation passes are clean (`git diff --check`, touched
  Lean marker scans, focused LSQRSolve builds, executable lookup, qualified
  axiom audits, PDF compile/text extraction, and rendered pages 190--193).
- 2026-06-02: Added pointwise route-bound certificates for the
  coefficient-maximum scalar route.  `LSQRSolve.lean` proves
  `storedQRDiagDominantInvFactorBudget_le_of_forall_le`,
  `storedQRPivotColumnNormBudget_le_of_forall_le`,
  `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_le`,
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget_pointwise_bounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds`.
  These reduce the displayed-upper-bound obligations to per-pivot route
  estimates plus nonnegativity of the displayed constants in the zero-pivot
  case.  Two weak-component validation passes are clean: repeated touched Lean
  marker scans, focused LSQRSolve builds, executable lookup, qualified axiom
  audits, PDF compile/text extraction, and rendered pages 190--194 passed.
- 2026-06-02: Added the solver-facing pointwise coefficient-maximum handoff.
  `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual`.
  These wrappers compose the pointwise product-budget route into the
  concrete-dual QR solve certificate; the second derives leading-block
  determinant nonzeroness from local diagonal dominance.  Two weak-component
  validation passes are clean: repeated `git diff --check`, touched Lean marker
  scans, focused LSQRSolve builds, executable lookup, qualified axiom audits,
  PDF compile/text extraction, and rendered pages 191--195 passed.  This remains a solver-surface composition step only:
  the pointwise estimates, scalar inequality, local diagonal/off-diagonal
  control, and final generic equation (8) QR/preconditioner theorem remain open.
- 2026-06-02: Added the per-pivot beta-norm coefficient reduction for the
  compact Householder route.  `HouseholderApply.lean` proves
  `householderCompactNormBudgetCoeff_eq_u_add_abs_beta_norm_sq_mul_factor`,
  `householderCompactNormBudgetCoeffFactor_nonneg`, and
  `householderCompactNormBudgetCoeff_le_of_abs_beta_norm_sq_le`; `HouseholderQR.lean`
  proves `storedQRCompactStepNormBudgetCoeff_le_of_abs_beta_norm_sq_le` and
  `storedQRCompactStepNormBudgetCoeff_le_of_forall_abs_beta_norm_sq_le`;
  `LSQRSolve.lean` proves
  `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_abs_beta_norm_sq_le`,
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_absBetaNormSq_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_absBetaNormSqPointwiseBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxAbsBetaNormSqPointwiseBounds`.
  This specializes the coefficient-max route to
  `Cmax = u + Bmax * householderCompactNormBudgetCoeffFactor fp m` when each
  signed stage has `|beta_k| * ||v_k||_2^2 <= Bmax`.  Focused LSQRSolve build
  passes; two weak-component validation passes are clean (`git diff --check`,
  touched-source marker scans, focused LSQRSolve builds, executable lookup,
  qualified axiom audits, PDF compile/text extraction, and rendered page
  inspections).  The `Bmax` estimate, scalar inequality, local
  diagonal/off-diagonal control, and final generic equation (8)
  QR/preconditioner theorem remain open.
- 2026-06-02: Added the exact Householder-normalization coefficient branch.
  `HouseholderSpec.lean` proves `abs_householderBeta_mul_vecNorm2_sq_eq_two`
  and `abs_householderBeta_mul_vecNorm2_sq_le_two`, reusing
  `householderBeta_mul_inner_self_eq_two` to show
  `|beta| * ||v||_2^2 = 2` from a nonzero denominator.  `HouseholderQR.lean`
  lifts this to stored signed stages and the source-shaped QR-loop
  nonbreakdown hypothesis; `LSQRSolve.lean` proves
  `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_source_den_ne_zero`,
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenPointwiseBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenPointwiseBounds`.
  This closes the coefficient-route `Bmax` estimate with concrete `Bmax = 2`
  under visible source nonbreakdown.  Focused LSQRSolve build passes, and two
  weak-component passes are clean: repeated `git diff --check`, touched Lean
  marker scans, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve`, executable
  lookup, qualified axiom audit for the eleven new theorem names, theorem PDF
  compile, targeted `pdftotext`, and rendered pages 190--193 passed.  The axiom
  audit reported only standard `propext`, `Classical.choice`, and
  `Quot.sound`, and the temporary axiom-audit file was deleted.

- 2026-06-02: Added the LS.2g-fi source-facing scalar-smallness normalization.
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_simple_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenSimpleBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenSimpleBounds`.
  These siblings rewrite the expanded exact-normalization condition with
  `Cmax = fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m` into the
  compact route certificate
  `2 * Dmax * (m * ((n * (n + 1) * Cmax * Nmax)^2)) < 1`, then reuse the
  source-denominator `Bmax = 2` branch.  Focused LSQRSolve build passes, and
  two weak-component passes are clean: repeated `git diff --check`, touched
  Lean marker scans, focused LSQRSolve builds, executable lookup, qualified
  axiom audit for the three new theorem names, theorem PDF compile, targeted
  `pdftotext`, and rendered pages 192--193 passed.  The axiom audit reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`, and the
  temporary axiom-audit file was deleted.

- 2026-06-02: Added the LS.2g-fj source-denominator scalar cap bridge.
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_cap_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenCapBounds`.
  These theorems reduce the source-facing scalar condition with
  `fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m` to visible caps
  `fp.u <= Ucap` and
  `householderCompactNormBudgetCoeffFactor fp m <= Fcap`, plus the displayed
  inequality with `Ucap + 2 * Fcap`.  This is a scalar-smallness dependency
  reduction only: cap estimates, local diagonal dominance/off-diagonal control,
  inverse-factor and pivot-column pointwise bounds, source nonbreakdown,
  determinant/conditioning fields, and the final generic equation (8)
  QR/preconditioner theorem remain open or visible.  Focused LSQRSolve build
  passed, and two weak-component passes are clean: repeated `git diff --check`,
  production Lean marker scans, focused LSQRSolve builds, executable lookup,
  qualified axiom audits, theorem PDF compile, targeted `pdftotext`, and
  rendered pages 192--195 passed.  The axiom audit reported only standard
  `propext`, `Classical.choice`, and `Quot.sound`, and the temporary audit file
  was deleted.

- 2026-06-02: Added the LS.2g-fk Householder coefficient-factor cap.
  `HouseholderApply.lean` now proves
  `householderCompactNormBudgetCoeffFactor_le_of_u_gamma_le`, bounding
  `householderCompactNormBudgetCoeffFactor fp m` by the explicit polynomial in
  caps `Ucap` and `Gcap` whenever `fp.u <= Ucap`,
  `gamma fp m <= Gcap`, and the caps are nonnegative.  This is a cap-estimate
  dependency for the LS.2g-fj scalar cap bridge only: primitive `u`/`gamma`
  caps, scalar cap smallness, local diagonal dominance/off-diagonal control,
  inverse-factor and pivot-column pointwise bounds, source nonbreakdown,
  determinant/conditioning fields, and the final generic equation (8)
  QR/preconditioner theorem remain open.  Two weak-component passes are clean:
  repeated `git diff --check`, production Lean marker scans, focused
  HouseholderApply and LSQRSolve builds, executable lookup, qualified axiom
  audit, theorem PDF compile, targeted `pdftotext`, and rendered pages 192--193
  passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fl gamma cap from a unit-roundoff cap.
  `Rounding.lean` now proves `gamma_le_of_u_le_cap` and
  `gamma_le_Gcap_of_u_le_cap`, bounding `gamma fp m` by
  `m*Ucap/(1-m*Ucap)` from `fp.u <= Ucap` and `(m : ℝ) * Ucap < 1`, and then
  by any displayed `Gcap` dominating that expression.  This is a primitive
  cap-estimate dependency for the LS.2g-fk factor cap only: the actual
  unit-roundoff cap, scalar cap smallness, local diagonal dominance/off-diagonal
  control, inverse-factor and pivot-column pointwise bounds, source
  nonbreakdown, determinant/conditioning fields, and final generic equation (8)
  QR/preconditioner theorem remain open.  Two weak-component passes are clean:
  repeated `git diff --check`, production marker scans, focused
  Rounding/HouseholderApply/LSQRSolve builds, executable lookup, qualified
  axiom audit, theorem PDF compile, targeted `pdftotext`, and rendered pages
  193--194 passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fm composed coefficient-factor cap from a
  unit-roundoff cap.  `HouseholderApply.lean` now proves
  `householderCompactNormBudgetCoeffFactor_le_of_u_cap_gamma_cap`, composing
  the LS.2g-fk factor cap with the LS.2g-fl gamma cap so the route derives
  `householderCompactNormBudgetCoeffFactor fp m <= polynomial(Ucap,Gcap)`
  from `fp.u <= Ucap`, `(m : ℝ) * Ucap < 1`, and the rational domination by
  `Gcap`, without a separate `gamma fp m <= Gcap` field.  Two weak-component
  passes are clean: repeated `git diff --check`, production marker scans,
  focused HouseholderApply/LSQRSolve builds, executable lookup, qualified axiom
  audit, theorem PDF compile, targeted `pdftotext`, and rendered pages 193--194
  passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fn source-denominator cap route from
  unit-roundoff/gamma caps.  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_uGammaCapBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenUGammaCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenUGammaCapBounds`,
  composing the LS.2g-fm displayed Householder factor cap into the
  scalar-smallness, compact-product, and packaged invariant surfaces.  Two
  weak-component passes are clean: repeated `git diff --check`, production Lean
  marker scans, focused LSQRSolve builds, executable lookup, qualified axiom
  audits, theorem PDF compile, targeted `pdftotext`, and rendered pages 193--195
  passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`; the temporary audit file was deleted.

- 2026-06-02: Added the LS.2g-fo unit-roundoff-cap route elimination.
  `Model.lean` now defines `FPModel.exactWithUnitRoundoff` and proves
  `FPModel.not_forall_u_le_cap`, showing that no fixed cap `fp.u <= Ucap`
  follows from the abstract `FPModel` alone.  This is a theorem-statement
  correction for the LS.2g cap route: primitive unit-roundoff caps must remain
  visible domain assumptions unless a concrete machine model is formalized.
  Two weak-component passes are clean: repeated `git diff --check`, production
  Lean marker scans, focused Model builds, executable lookup, qualified axiom
  audits, theorem PDF compile, targeted `pdftotext`, and rendered page 194
  passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fp rational gamma cap specialization.
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_uRationalGammaCapBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenURationalGammaCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCapBounds`,
  specializing `Gcap` to `(m * Ucap)/(1 - m * Ucap)` so the separate
  rational-domination proof field closes by reflexivity.  Two weak-component
  passes are clean: repeated `git diff --check`, production Lean marker scans,
  focused LSQRSolve builds, executable lookup, qualified axiom audits, theorem
  PDF compile, targeted `pdftotext`, and rendered pages 194--195 passed.  The
  axiom audit reported only standard `propext`, `Classical.choice`, and
  `Quot.sound`.

- 2026-06-02: Added the LS.2g-fq canonical finite-max rational gamma cap route.
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_source_den_ne_zero_uRationalGammaCanonicalBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenURationalGammaCanonicalBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  choosing `Dcap` and `Ncap` as the repository's canonical finite maxima and
  removing the separate pointwise inverse-factor and pivot-column domination
  proof fields from the rational-gamma source-denominator route.  Two
  weak-component passes are clean: repeated `git diff --check`, production
  Lean marker scans, focused LSQRSolve builds, executable lookup, qualified
  axiom audits, theorem PDF compile, targeted `pdftotext`, and rendered pages
  194--196 passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fr solver/probability handoff for the canonical
  finite-max rational gamma cap route.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  and `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  Two weak-component passes are clean: repeated `git diff --check`, production
  Lean marker scans, focused LSQRSolve and LeastSquaresSketch builds,
  executable lookup, qualified axiom audits, theorem PDF compile, targeted
  `pdftotext`, and rendered pages 195--201 passed.  The axiom audit reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fs canonical scalar-smallness route-elimination
  theorem.  `LSQRSolve.lean` now proves
  `not_forall_diagDominant_sourceDen_uCap_implies_uRationalGammaCanonicalSmallness`,
  a `1 x 1` exact-with-unit-roundoff witness showing that local diagonal
  dominance, source denominator nonbreakdown, `fp.u <= Ucap`, and
  `(m : ℝ) * Ucap < 1` do not imply the displayed canonical finite-max scalar
  smallness inequality.  Two weak-component passes are clean: repeated
  `git diff --check`, production Lean marker scans, focused LSQRSolve builds,
  executable lookup, qualified axiom audits, theorem PDF compile, targeted
  `pdftotext`, and rendered pages 198--199 passed.  The axiom audit reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the actual-unit-roundoff companion to the LS.2g-fs
  scalar-smallness route elimination.  `LSQRSolve.lean` now proves
  `not_forall_diagDominant_sourceDen_actualU_implies_uRationalGammaCanonicalSmallness`,
  showing that even substituting the actual `fp.u` into the rational-gamma
  expression does not make the canonical finite-max scalar smallness inequality
  automatic from diagonal dominance, source nonbreakdown, and `m * fp.u < 1`.
  This rules out the `Ucap = fp.u` shortcut and keeps scalar smallness as a
  genuine positive proof obligation.

- 2026-06-02: Added the LS.2g-ft source nonbreakdown reduction for the
  canonical rational-gamma route.  `LSQRSolve.lean` now proves
  `storedQRSourceDenominator_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos`,
  `StoredQROffDiagonalControlInvariant.of_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds`;
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These derive raw source denominator nonbreakdown from signed-alpha source
  facts and positive trailing norm squares, then reuse the existing canonical
  route.  Two weak-component passes are now clean: focused LSQRSolve and
  LeastSquaresSketch builds, executable lookup, `git diff --check`, touched
  marker scan, qualified axiom audit, theorem PDF compile, `pdftotext`
  inspection, and rendered page inspection passed.  The temporary axiom-audit
  file was deleted.

- 2026-06-02: Added the Algorithm 1 explicit FP scalar-radius correction after
  PDF review.  `ElementwiseSpectral.lean` now proves
  `sqMagTraceErrorBudget_zero_init_truncated_le_const`,
  `frobNormRect_sqMagTraceErrorBudget_zero_init_truncated_le_const_square`,
  `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_square`,
  and
  `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_square`.
  The user-facing Algorithm 1 equation (2) FP corollary should now advertise
  the displayed radius
  `eps + (2*n^2*||A||_F^2/eps)*gamma fp (s+1)` for `tau=eps/(2n)`, not only
  the internal budget-matrix theorem `eps + ||B||_F`.  Two weak-component
  passes are clean for this correction: repeated diff checks, marker scans,
  focused ElementwiseSpectral builds, executable lookup, axiom audit, PDF
  compile/text inspection, and rendered page checks.

- 2026-06-02: Fixed the follow-up Algorithm 1 PDF presentation regression.
  Theorem 142 in `docs/RandNLA_CACM_Formalization_Summary.tex` is now
  exact-only and explicitly labelled as an entrywise union-bound fallback, not
  equation (2).  The final end-of-Algorithm-1 corollary immediately before
  Algorithm 2 is the equation (2) citation target; it states the rounded
  source-aligned square truncated result with the explicit radius
  `eps + (2*n^2*||A||_F^2/eps)*gamma fp (s+1)` and no hidden budget matrix.
  Older fallback Markov/net/Frobenius prose was also rewritten so generic
  perturbation matrices do not look like advertised Algorithm 1 endpoints.

- 2026-06-02: Made the final Algorithm 1 equation (2) PDF corollary
  self-contained.  Corollary 143 now restates the hard-thresholding definition
  of `trunc_tau(A)` entrywise and explains why `tau = eps/(2*n)` is used:
  deterministic truncation costs at most `eps/2` in Frobenius/operator norm for
  an `n x n` matrix, while retained sampled entries have magnitude at least
  `tau`, giving the denominator lower bound behind the explicit FP
  `gamma fp (s+1)` radius.

- 2026-06-02: Corrected the Algorithm 1 theorem-scope mistake after user
  review.  Hard-thresholding is not part of the literal CACM Algorithm 1
  sampler with `p_ij = A_ij^2 / ||A||_F^2`; it is a modified/truncated
  element-wise sampler.  The theorem PDF now retitles the former final
  Algorithm 1 corollary as a truncated element-wise sampler theorem and states
  explicitly that the sharp literal untruncated equation (2) matrix-Bernstein
  theorem remains open.
  Do not cite the truncated theorem as closing CACM Algorithm 1.

- 2026-06-02: Added the faithful nontruncated Algorithm 1 FP corollary after
  the truncation correction.  `ElementwiseSpectral.lean` proves
  `sqMagTraceErrorBudget_zero_init_le_const_of_entry_abs_ge`,
  `frobNormRect_sqMagTraceErrorBudget_zero_init_le_const_square_of_entry_abs_ge`,
  and
  `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_frob_explicit_gamma_square`.
  This result uses the literal law `p_ij = A_ij^2 / ||A||_F^2`, no
  `trunc_tau(A)`, and a visible nonzero-entry floor `alpha <= |A_ij|` to expand
  the rounded radius to `eps + n*(||A||_F^2/alpha)*gamma fp (s+1)`.  It is a
  weaker Frobenius/Markov corollary, not the sharp CACM equation (2)
  matrix-Bernstein/Khintchine theorem.

- 2026-06-02: Added the literal Algorithm 1 source-rate specialization under a
  visible no-small-entry condition.  `ElementwiseSpectral.lean` proves
  `elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge`,
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_square`,
  and
  `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_source_sample_budget_no_small_entries_square`.
  These use the literal law `p_ij = A_ij^2 / ||A||_F^2` and the source-rate
  sample budget `14*n*||A||_F^2*log(2(2n)/delta) <= s*eps^2`, but require
  `eps/(2n) <= |A_ij|` for every nonzero entry so the source truncation is the
  identity.  The FP radius is
  `eps + (2*n^2*||A||_F^2/eps)*gamma fp (s+1)`.  This is not the fully
  unconditional literal CACM equation (2) theorem for arbitrarily small
  nonzero entries.

- 2026-06-02: Clarified Algorithm 2 equation (5) FP scope.  The theorem
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_scaling_budget`
  is the scaling-only model: sampled/scaled rows are rounded, then the Gram
  matrix is formed as a mathematical object.  Its radius is
  `eps * D(A) + n*(2*u+u^2)*D(A)` and it has no `tau_dot` and no `gammaValid`
  hypothesis.  Use the `fl_rowSampleGramDot` theorem only for implementations
  that actually compute Gram entries by rounded dot products.

- 2026-06-02: Added the LS.2g-fu determinant-facing source-nonbreakdown
  reduction for the canonical rational-gamma QR route.  `LSQRSolve.lean` now
  proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`;
  `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  This replaces the positive trailing-norm hypothesis in the LS.2g-ft branch
  by nonzero previous/current leading-block determinants plus the stored
  lower-zero shape, then reuses the signed-alpha source-nonbreakdown route.
  Two weak-component passes are clean: focused LSQRSolve and
  LeastSquaresSketch builds, executable lookup, `git diff --check`, production
  marker scans, qualified axiom audits, theorem PDF compile, targeted
  `pdftotext`, and rendered pages 203--204 passed.  The axiom audits reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`, and the
  temporary audit file was deleted.  The final generic rectangular
  QR/preconditioner theorem remains open on determinant/nonzero fields, local
  diagonal-dominance/off-diagonal control, scalar smallness, primitive
  unit-roundoff caps, and conditioning assumptions.

- 2026-06-02: Added the LS.2g-fv signed-alpha-definition invariant-surface
  reduction for the determinant-facing canonical rational-gamma QR route.
  `LSQRSolve.lean` proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  which derives the squared-alpha identity and sign-choice inequality directly
  from the concrete `signedHouseholderAlpha` definition before reusing the
  determinant-facing source-nonbreakdown route.  This is a theorem-surface
  reduction only; determinant nonzeroness, local diagonal dominance/off-diagonal
  control, scalar smallness, primitive unit-roundoff caps, conditioning fields,
  and the final rectangular QR/preconditioner theorem remain open or visible.
  The determinant-facing solver theorem now syntactically consumes this
  packaged invariant through the generic off-diagonal-control handoff.  Two
  focused weak-component passes after this proof rewrite are clean: repeated
  focused LSQRSolve builds, executable lookup, `git diff --check`, production
  marker scans, qualified axiom audits for both the invariant and consuming
  solver theorem, theorem PDF compiles, targeted `pdftotext`, and rendered pages
  203--204 passed.  The axiom audits reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`, and the temporary axiom-audit file was
  deleted after the second pass.

- 2026-06-02: Added the LS.2g-fw current-determinant reduction for the
  determinant-facing canonical rational-gamma QR route.  `LSQRSolve.lean`
  proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`;
  `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These wrappers derive the current leading-block determinant from
  `IsDiagDominantUpper` via `det_ne_zero_of_diagDominantUpper`.  The previous
  transposed leading-block determinant, local diagonal dominance/off-diagonal
  control, scalar smallness, primitive unit-roundoff caps, conditioning fields,
  and final rectangular QR/preconditioner theorem remain open or visible.
  Two focused weak-component passes are clean: focused LSQRSolve and
  LeastSquaresSketch builds, executable lookup, `git diff --check`, production
  marker scans, qualified axiom audits, theorem PDF compile, targeted
  `pdftotext`, and rendered page 204 passed.  The axiom audits reported only
  standard `propext`, `Classical.choice`, and `Quot.sound`, and the temporary
  audit file was deleted.

- 2026-06-02: Added the LS.2g-fx previous-determinant reduction for the
  determinant-facing canonical rational-gamma QR route.  `LSQRSolve.lean`
  proves `qrPreviousLeadingBlockTranspose_det_ne_zero_of_diagDominant_leadingBlock`,
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds`;
  `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These wrappers derive the previous transposed leading-block determinant from
  the same `IsDiagDominantUpper` leading-block hypothesis, leaving the previous
  lower-zero shape, diagonal dominance/off-diagonal control, scalar smallness,
  primitive unit-roundoff caps, conditioning fields, and final rectangular
  QR/preconditioner theorem open or visible.  Two focused weak-component passes
  are clean: repeated LSQRSolve and LeastSquaresSketch builds, executable
  lookup, `git diff --check`, production marker scans, qualified axiom audits,
  theorem PDF compile, targeted `pdftotext`, and rendered pages 205--206
  passed.  The axiom audits reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`, and the temporary audit file was deleted
  after validation.

- 2026-06-02: Added the LS.2g-fy stored-lower-zero reduction for the
  determinant-facing canonical rational-gamma QR route.  `LSQRSolve.lean`
  proves `storedQRPreviousColumnLowerZero_of_stored_trailing_householder_sequence`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds`;
  `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These wrappers derive the previous-column lower-zero field from the stored
  Householder panel recurrence via
  `fl_householderStoredPanel_sequence_prefix_lower_zero`, leaving diagonal
  dominance/off-diagonal control, scalar smallness, primitive unit-roundoff
  caps, conditioning fields, and the final rectangular QR/preconditioner theorem
  open or visible.  Two focused weak-component passes are clean: focused
  LSQRSolve and LeastSquaresSketch builds, executable lookup, `git diff --check`,
  production marker scans, qualified axiom audits, theorem PDF compile,
  targeted `pdftotext`, and rendered pages 205--206 passed.  The axiom audits
  reported only standard `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fz unit-roundoff-cap nonnegativity reduction for
  the stored-lower canonical rational-gamma QR route.  `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap`;
  `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap`.
  These wrappers derive the former explicit `0 <= Ucap` hypothesis from
  `FPModel.u_nonneg` and `fp.u <= Ucap`, leaving the primitive unit-roundoff cap
  itself, scalar smallness, local diagonal dominance/off-diagonal control,
  conditioning fields, and the final QR/preconditioner theorem open or visible.
  Two focused weak-component passes are clean: focused LSQRSolve and
  LeastSquaresSketch builds, executable lookup, `git diff --check`, production
  marker scans, qualified axiom audit, theorem PDF compile, targeted
  `pdftotext`, and rendered pages 205--207 passed.  The axiom audit reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-ga cap-derived gamma-validity reduction for the
  stored-lower canonical rational-gamma QR route.  `Rounding.lean` proves
  `gammaValid_of_u_le_cap`.  `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap_no_gammaValid`,
  and `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap_no_gammaValid`.
  These wrappers derive the former `gammaValid fp m`/`gammaValid fp s` guard
  from `fp.u <= Ucap` and the displayed cap smallness, then derive the
  triangular-dimension guard with `gammaValid_mono`.  This removes a redundant
  FP validity field from the cap-based QR/probability surface; it does not
  prove the primitive cap itself, scalar smallness, local diagonal
  dominance/off-diagonal control, conditioning fields, or the final generic
  QR/preconditioner theorem.  Two focused weak-component passes are clean:
  Rounding, LSQRSolve, and LeastSquaresSketch builds; executable lookup;
  `git diff --check`; touched-source marker scan; qualified axiom audit;
  theorem PDF compile; targeted `pdftotext`; and rendered pages 206--207
  passed.  The only Lean warnings were the pre-existing `HouseholderQR`
  unused-variable warnings, and the axiom audit reported only standard
  `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-gb actual-unit-roundoff stored-lower
  specialization.  `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_actualUnitRoundoff`,
  and `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_actualUnitRoundoff`.
  These wrappers choose `Ucap = fp.u`, discharge `fp.u <= Ucap` by
  reflexivity, and write the canonical finite-max scalar smallness condition
  directly with the actual unit roundoff.  The ordinary `gammaValid fp m` or
  `gammaValid fp s` guard remains visible.  This removes a primitive cap
  parameter and cap notation from the stored-lower solver/probability surface;
  it does not prove scalar smallness, local diagonal dominance/off-diagonal
  control, conditioning fields, or the final generic QR/preconditioner theorem.
  Two weak-component passes are clean: focused LSQRSolve and
  LeastSquaresSketch builds; executable lookup; `git diff --check`;
  touched Lean-source marker scan; qualified axiom audit; theorem PDF compile;
  targeted `pdftotext` over pages 206--208; and rendered pages 206--208
  passed.  The only Lean warnings were the pre-existing `HouseholderQR`
  unused-variable warnings, and the axiom audit reported only standard
  `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-05: Added LR.1ds for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` proves
  `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos`,
  composing the constructed ordered replacement-tail block certificate with the
  exact block-certificate rank/residual surface.  The theorem exposes exact
  `det(V_ord^T Z) != 0` and cross-term hypotheses and gives rank at most `k`
  plus residual radius `2 * sqrt(1 + eps^2) * ||Sigma_tail||_F`; sampling
  probabilities and laws remain exact mathematical inputs.  It does not prove
  the relative/Eckart--Young conclusion, randomness-derived cross-term
  certificates, or computed non-probability SVD/singular-vector/projector/Gram/
  inverse/sketch/product routines.  Focused Lean, focused Lake build after one
  stale-artifact rerun, lookup, aggregate RandNLA build, full Lake build,
  marker scan, axiom audit, PDF compile/text/render checks, and root/docs PDF
  sync passed; the axiom audit reported only `propext`, `Classical.choice`, and
  `Quot.sound`.

- 2026-06-05: Added and fully validated LR.1dt for the RandNLA CACM
  equation-(9) low-rank bottleneck.  `LowRankApprox.lean` proves
  `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos`,
  composing the same constructed ordered replacement-tail block certificate
  with the exact block-certificate sigma-tail relative surface.  The theorem
  exposes exact `det(V_ord^T Z) != 0`, exact cross-term, exact tail-optimality
  for every rank-at-most-`k` competitor, and scalar comparison hypotheses, then
  returns the best-rank certificate for the constructed ordered source head and
  the relative residual bound for the exact Gram-inverse column-sketch
  projector.  Focused Lean, focused Lake build, lookup, aggregate RandNLA
  build, full Lake build, `git diff --check`, marker scan, axiom audit, PDF
  compile/text/render checks, and root/docs PDF sync passed; the axiom audit
  reported only `propext`, `Classical.choice`, and `Quot.sound`.  Remaining
  obligations are the Eckart--Young tail-optimality proof for the constructed
  ordered source split, randomness-derived cross-term certificates, and
  computed non-probability SVD/singular-vector/projector/Gram/inverse/sketch/
  product routine certificates.  Sampling probabilities and laws remain exact
  mathematical inputs.

- 2026-06-05: Added and fully validated LR.1du for the RandNLA CACM
  equation-(9) low-rank bottleneck.  `LowRankApprox.lean` now proves the
  generic exact diagonal identities `frobNormSq_diagonal_eq_sum` and
  `frobNorm_diagonal_eq_sqrt_sum`, plus the constructed ordered-tail
  specializations `frobNormSq_rectRightGramOrderedTailSingularDiagonal_eq_sum`
  and `frobNorm_rectRightGramOrderedTailSingularDiagonal_eq_sqrt_sum`.  The
  result rewrites `||rectRightGramOrderedTailSingularDiagonal A hk||_F` as the
  square root of the complement singular-square sum needed for the LR.1dt
  tail-optimality discharge.  Focused Lean, lookup, aggregate RandNLA build,
  full Lake build, `git diff --check`, marker scan, axiom audit, PDF
  compile/text/render checks, and root/docs PDF sync passed; the axiom audit
  reported only `propext`, `Classical.choice`, and `Quot.sound`.  Remaining
  obligations are the residual lower-bound transport, randomness-derived
  cross-term certificates, and computed non-probability SVD/singular-vector/
  projector/Gram/inverse/sketch/product routine certificates.  Sampling
  probabilities and laws remain exact mathematical inputs.

- 2026-06-05: Added and fully validated LR.1dv for the RandNLA CACM
  equation-(9) low-rank bottleneck.  `LowRankApprox.lean` now proves
  `rectRightGramSelectedIndexSet_card_add_compl_card` and
  `rectRightGramOrderedTailIndex_card_add`, giving the exact finite-cardinality
  bridge `k + |S^c| = n` and its constructed ordered-tail specialization
  `k + q = n`.  Focused Lean, focused LowRankApprox build, lookup, full Lake
  build, `git diff --check`, marker scan, axiom audit, PDF compile/text/render
  checks, and root/docs PDF sync passed; the axiom audit reported only
  `propext`, `Classical.choice`, and `Quot.sound`.  Remaining obligations are
  column-reindexing/equivalence transport, the residual lower-bound discharge
  for LR.1dt's tail-optimality hypothesis, randomness-derived cross-term
  certificates, and computed non-probability SVD/singular-vector/projector/
  Gram/inverse/sketch/product routine certificates.  Sampling probabilities
  and laws remain exact mathematical inputs.

- 2026-06-06: Added LR.1dw for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` now proves
  `sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_gap`,
  `rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_gap`,
  and `sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_gap`.
  The route transports the diagonal head-tail gap theorem through exact
  `U diag(sigma) V^T` and composes it with the q-dimensional residual-side
  right-kernel theorem.  This avoids assuming that a constructed complement-tail
  enumeration is sorted: it only needs a visible separator `eta` with head
  squares above and tail squares below.  Focused Lean, focused LowRankApprox
  build, lookup, full Lake build, `git diff --check`, marker scan, axiom audit,
  PDF compile/text/render checks, and root/docs PDF sync passed; the axiom
  audit reported only `propext`, `Classical.choice`, and `Quot.sound`.  The
  summary PDF now contains Corollary 605, "Source-factor gap lower-bound bridge
  for equation (9)", with the three LR.1dw theorem names.  The remaining
  low-rank proof still needs the constructed gap instantiation, original-column
  reindexing/equivalence transport, LR.1dt tail-optimality discharge,
  randomness-derived cross-term certificates, and computed non-probability
  SVD/singular-vector/projector/Gram/inverse/sketch/product routine
  certificates.  Sampling probabilities and laws remain exact mathematical
  inputs.

- 2026-06-06: Added LR.1dx for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` now proves
  `rectRightGramOrdered_head_tail_square_gap`: for `0 < k`, the last selected
  top singular square is a separator `eta` such that every constructed selected
  head square is at least `eta` and every constructed complement-tail singular
  square is at most `eta`.  The proof uses selected-square equality plus
  antitonicity of ordered right-Gram singular-value squares for the head side,
  and the complement-versus-selected comparison plus nonnegativity and
  `sq_le_sq` for the tail side.  Focused Lean, focused LowRankApprox build,
  lookup, full Lake build, `git diff --check`, marker scan, axiom audit, PDF
  compile/text/render checks, and root/docs PDF sync passed; the axiom audit
  reported only `propext`, `Classical.choice`, and `Quot.sound`.  The summary
  PDF now contains Corollary 588, "Constructed ordered head-tail square gap",
  with the LR.1dx theorem name and the displayed separator inequalities.  The
  remaining low-rank proof still needs original-column reindexing/equivalence
  transport, the LR.1dt tail-optimality discharge, randomness-derived cross-term
  certificates, and computed non-probability SVD/singular-vector/projector/Gram/
  inverse/sketch/product routine certificates.  Sampling probabilities and laws
  remain exact mathematical inputs.

- 2026-06-06: Added LR.1dy for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` now defines
  `RectRankFactorization.permuteCols` and proves
  `RectRankAtMost.permuteCols`, `RectRankAtMost.of_permuteCols`, and
  `lowRankResidualFrob_permuteCols`.  This gives the exact generic
  column-reindexing transport: explicit rank factorizations transport by
  composing the right factor with the column equivalence, rank-at-most
  certificates transport both directions, and Frobenius residuals are invariant
  when source and competitor are permuted together.  Focused Lean, focused
  LowRankApprox build, lookup, full Lake build, marker scan, axiom audit, PDF
  compile/text/render checks, and root/docs PDF sync passed.  The PDF records
  this as Corollary 589 on pages 394--395.  This clears the LowRank parse
  blocker noted in not-proved ledger row 1451.  The next low-rank target is the
  constructed head-plus-complement-tail equivalence
  `Fin (k+q) ≃ Fin n`, followed by the LR.1dt tail-optimality discharge.
  Sampling probabilities and laws remain exact mathematical inputs.

- 2026-06-06: Added LR.1dz for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` now defines
  `rectRightGramOrderedHeadTailColumnMap`, proves its injectivity and
  surjectivity, packages `rectRightGramOrderedHeadTailColumnSumEquiv`, and
  composes with `finSumFinEquiv` to obtain
  `rectRightGramOrderedHeadTailColumnEquiv : Fin (k+q) ≃ Fin n` for the
  constructed ordered top block plus complement-tail enumeration.  Focused
  Lean, focused LowRankApprox build, lookup, full Lake build, marker scan,
  axiom audit, PDF compile/text/render checks, and root/docs PDF sync passed.
  The PDF records this as Corollary 590 on pages 396--397.  The next low-rank
  target is the LR.1dt tail-optimality discharge using the constructed gap,
  diagonal-tail norm, and column-equivalence transport.  Sampling probabilities
  and laws remain exact mathematical inputs.

- 2026-06-06: Added LR.1ea for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` now defines `rectReindexCols` for exact
  cross-domain column equivalences `Fin p ≃ Fin n`, transports explicit rank
  factorizations and rank-at-most certificates through the equivalence, proves
  `frobNormSqRect_reindexCols`, `frobNormRect_reindexCols`, and
  `lowRankResidualFrob_reindexCols`, and specializes the result to
  `rectRightGramOrderedHeadTailColumnEquiv hk`.  Focused Lean, focused
  LowRankApprox build, lookup, full Lake build, marker scan, axiom audit, PDF
  compile/text/render, and root/docs PDF sync passed.  The PDF records this as
  Corollary 591 on pages 397--398.  The next low-rank target remains the
  LR.1dt tail-optimality discharge.  Sampling probabilities and laws remain
  exact mathematical inputs.

- 2026-06-06: Added and fully validated LR.1eb for the RandNLA CACM
  equation-(9) low-rank bottleneck.  `LowRankApprox.lean` now assembles the
  constructed ordered head-plus-tail `Fin(k+q)` source blocks, proves the left
  block and pulled-back right block orthonormal/orthogonal facts, proves the
  source factor equals `rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A`,
  and discharges the constructed tail-optimality inequality
  `frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) <=
  lowRankResidualFrob A B` for every exact rank-at-most-`k` competitor.  The
  wrapper
  `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal`
  feeds this into LR.1dt without a supplied `hopt`.  Focused Lean, focused
  LowRankApprox build, lookup, full Lake build, marker scan, axiom audit, PDF
  compile/text/render, and root/docs PDF sync passed.  The PDF records this as
  Corollary 592 on pages 399--400.  The next low-rank targets are
  randomness-derived cross-term certificates, scalar relative comparison, and
  computed non-probability SVD/singular-vector/projector/Gram/inverse/sketch/
  product routine certificates.  Sampling probabilities and laws remain exact
  mathematical inputs.

- 2026-06-06: Added and fully validated LR.1ec for the RandNLA CACM
  equation-(9) low-rank bottleneck.  `LowRankApprox.lean` now proves
  `two_sqrt_one_add_sq_mul_tail_le_of_scalar` and the wrapper
  `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal_of_scalarRelative`.
  The theorem surface now accepts the coefficient condition
  `2 * sqrt (1 + eps^2) <= rho`; Lean derives the product-form scalar
  comparison by multiplying by the nonnegative constructed tail Frobenius norm.
  During validation a local proof-focus issue in
  `rademacherTraceProbability_expectationReal_eq_zero_of_flip_neg` was made
  robust by proving the function equality explicitly.  Focused Lean, focused
  Preconditioning build, focused LowRankApprox build, lookup, full Lake build,
  marker scan, axiom audit, PDF compile/text/render, and root/docs PDF sync
  passed.  The PDF records this as Corollary 593 on page 401.  Remaining
  low-rank targets are randomness-derived cross-term certificates and computed
  non-probability SVD/singular-vector/projector/Gram/inverse/sketch/product
  routine certificates.  Sampling probabilities and laws remain exact
  mathematical inputs.

- 2026-06-21: Chapter 13 Problem 13.4 now has two validated certificate
  bridges in `BlockLU.lean`:
  `higham13_problem13_4_A21A11inv_rectOpNorm2Le_from_growth_certificates`
  proves the lower-left solve product bound from growth-factor,
  principal-inverse, and condition-product operator certificates, and
  `higham13_problem13_4_schur_kappa_bound_from_operator_certificates` proves
  the Schur condition-product scalar bound from `S`, `S^{-1}`, and
  `A`/`A^{-1}` operator certificates.  Focused Lean, focused BlockLU build,
  lookup, axiom audit, `git diff --check`, placeholder scan, and temp cleanup
  passed.  These are non-vacuous product-propagation dependencies, not a full
  closure of Problem 13.4: deriving the source operator certificates from
  growth-factor/Schur-complement hypotheses remains open, and Lemma 13.10 plus
  Eq.13.22/Eq.13.23 premise derivations still depend on that source route.

- 2026-06-21: Extended the Chapter 13 Problem 13.4 foundation with genuine
  off-diagonal block operator inheritance.  `MatrixAlgebra.lean` now has
  `finiteOpNorm2Le_sumInl_sumInr_rect`,
  `finiteOpNorm2Le_sumInr_sumInl_rect`,
  `rectOpNorm2Le_of_finiteOpNorm2Le`, and the two Fin-specialized
  rectangular wrappers.  `BlockLU.lean` now proves
  `higham13_problem13_4_A21_rectOpNorm2Le_of_full_operator_bound` and
  `higham13_problem13_4_A21A11inv_rectOpNorm2Le_from_full_A_certificate`,
  so the `A21` side of Problem 13.4 is derived from a full `A` operator
  certificate plus `rho >= 1` while the inverse-principal-block obligation
  remains visible.  It also has a special full-inverse-block route
  `higham13_problem13_4_A21A11inv_rectOpNorm2Le_from_full_block_certificates`
  when the supplied `A11inv` is explicitly the upper-left block of a full
  inverse certificate; this is not the general source proof of
  `A11^{-1}`.  Focused MatrixAlgebra Lean/build, focused BlockLU Lean/build,
  lookup, axiom audit, `git diff --check`, placeholder scan, and temp cleanup
  passed.  Remaining Problem 13.4 source work: derive the general
  inverse-principal-block and Schur-complement operator certificates, then
  feed Lemma 13.10 and Eq.13.22/Eq.13.23 premise derivations.

- 2026-06-21: Audited the Chapter 13 PDF text for Problem 13.4 with
  Ghostscript extraction.  The exercise on p.258 explicitly defines
  `||A|| := max_ij |a_ij|`.  The existing operator-certificate declarations
  were therefore recorded as auxiliary infrastructure, not exact source
  closure.  The source-aligned route must use max-entry-norm proof steps or a
  constant-preserving bridge from the source max-entry growth/condition
  hypotheses to the operator-certificate surface.

- 2026-06-21: Added the source-aligned max-entry product-propagation step for
  Chapter 13 Problem 13.4.  `BlockLU.lean` now has
  `maxEntryNormRect_rectMatMul_le`,
  `higham13_problem13_4_A21A11inv_maxEntryNormRect_from_growth_certificates`,
  and
  `higham13_problem13_4_A21A11inv_maxEntryNormRect_from_entrywise_A21_bound`.
  These prove `||A21 A11^{-1}||_max <= n rho_n kappa(A)` once the growth,
  inverse-principal-block, dimension, and condition-product certificates are
  supplied.  The selected source row remains open because those certificates
  and the Schur condition bound are not yet derived from the source
  growth-factor/Schur hypotheses.

- 2026-06-21: Added the max-entry `A21` inheritance bridge for Chapter 13
  Problem 13.4.  `higham13_problem13_4_A21_maxEntryNormRect_of_full_entry_bound`
  derives `||A21||_max <= rho ||A||` from a full partitioned-matrix entrywise
  bound and `rho >= 1`, and
  `higham13_problem13_4_A21A11inv_maxEntryNormRect_from_full_entry_bound`
  feeds that into the source max-entry product bridge.  Remaining exact source
  work for Problem 13.4: derive the max-entry inverse-principal-block
  certificate for `A11^{-1}` and the Schur-complement norm/inverse
  certificates from the growth-factor/Schur hypotheses.

- 2026-06-21: Added the source-aligned max-entry Schur condition bridge for
  Chapter 13 Problem 13.4.  `BlockLU.lean` now has
  `higham13_problem13_4_schur_kappa_maxEntryNormRect_from_certificates` and
  `higham13_problem13_4_schur_kappa_maxEntryNormRect_from_entrywise_schur_bound`,
  proving `kappa(S) <= rho_n kappa(A)` at the source max-entry norm once the
  Schur entrywise-growth, Schur-inverse, and condition-product certificates
  are supplied.  The exact source row remains open because the max-entry
  inverse-principal-block certificate for `A11^{-1}` and the Schur-inverse
  certificate `||S^{-1}|| <= ||A^{-1}||` still need to be connected to the
  source growth-factor/Schur hypotheses.

- 2026-06-21: Added the Problem 13.4 lower-right full-inverse inheritance
  bridge for the Schur condition route.  `BlockLU.lean` now has
  `higham13_problem13_4_Sinv_maxEntryNormRect_of_full_inverse_entry_bound`
  and
  `higham13_problem13_4_schur_kappa_maxEntryNormRect_from_full_inverse_entry_bound`,
  so the max-entry `S^{-1}` certificate follows once `S^{-1}` is identified
  with the lower-right block of a full inverse and the full inverse has the
  source entrywise `||A^{-1}||` bound.

- 2026-06-21: Added the Problem 13.4 block-inverse Schur certificate bridge.
  `BlockLU.lean` now has
  `higham13_problem13_4_Sinv_eq_full_inverse_lower_right_of_block_inverse`
  and
  `higham13_problem13_4_schur_kappa_maxEntryNormRect_from_block_inverse`,
  reusing `higham13_problem13_8_block_inverse` to identify `S^{-1}` with the
  lower-right block of the full inverse and then feeding that identity into the
  source max-entry Schur condition-product theorem.  Remaining exact Problem
  13.4 work: derive the max-entry inverse-principal-block certificate for
  `A11^{-1}` from the source hypotheses.

- 2026-06-21: Added the Problem 13.4 max-entry upper-left full-inverse-block
  certificate branch.  `BlockLU.lean` now has
  `higham13_problem13_4_A11inv_maxEntryNormRect_of_full_inverse_entry_bound`
  and
  `higham13_problem13_4_A21A11inv_maxEntryNormRect_from_full_block_entry_bound`.
  These prove the lower-left max-entry solve bridge when a supplied `A11inv`
  is explicitly the upper-left block of a supplied full inverse certificate.
  This is a genuine proved inheritance branch but not the general source proof
  for the displayed `A11^{-1}`.  Focused `BlockLU` Lean/build, lookup rerun,
  axiom audit, `git diff --check`, placeholder scan, and temp cleanup passed.
  Remaining exact Problem 13.4 work: derive the max-entry inverse-principal
  certificate for the displayed `A11^{-1}` from the GE/growth-factor source
  hypotheses or prove the lower-left solve bound by a direct GE route.

- 2026-06-21: Added the missing scalar Table 13.1 arbitrary-matrix and block
  row-BDD row wrappers.  `BlockLU.lean` now has
  `higham13_table13_1_arbitrary_backward_error_from_growth` and
  `higham13_table13_1_block_row_bdd_backward_error_from_growth`, both deriving
  the table-style first-order backward-error bound from explicit Eq.13.22
  product premises and a Theorem 13.6-style first-order error premise.  The
  wrappers keep the Eq.13.22 dimension factor visible instead of absorbing it
  into `c_n`; they do not close the Problem 13.4/Eq.13.21 premise derivations.
  Focused `BlockLU` Lean/build, lookup, axiom audit, `git diff --check`,
  placeholder scan, and temp cleanup passed.

- 2026-06-21: Created `docs/chapter13/CHAPTER13_BOTTLENECK_LEDGER.md` for the repeated
  selected-scope Chapter 13 blockers required by the Higham skill's red
  bottleneck protocol.  The ledger records exact next Lean dependencies for
  the Algorithm 13.3 active pivot product/certificate route, Problem 13.4's
  max-entry inverse-principal-block certificate, Theorem 13.6's cited
  Implementation 1 proof, Lemma 13.9's SPD-to-Cholesky/operator certificate
  instantiation, and Lemma 13.10's SPD Schur condition-number comparison.
  The report and human library lookup now point to this ledger.

- 2026-06-21: Advanced the Lemma 13.9 Cholesky/SPD bottleneck by proving the
  sum-indexed Cholesky block-equation extraction.  `BlockLU.lean` now has
  `higham13_lemma13_9_cholesky_block_equations_of_sum_product`, deriving the
  source `A22 = R12^T R12 + R22^T R22` and `A21 = R12^T R11` equations from
  a full `A = R^T R` product certificate and the block form of `R`, plus
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_sum_cholesky_product`,
  which feeds those extracted equations into the existing full-operator
  Lemma 13.9 route.  A follow-up in the same pass added
  `higham13_lemma13_9_sum_product_of_equiv_product`,
  `higham13_lemma13_9_cholesky_block_equations_of_equiv_product`, and
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_equiv_cholesky_product`,
  so a finite Cholesky product certificate indexed on another finite type can
  be pulled back through an equivalence to the block partition.  This closes a
  proof-artifact assumption but not the bare SPD source theorem; the remaining
  route is to derive the Cholesky block-form data and pulled-back full/full
  inverse operator certificates from the repository SPD/Cholesky surface.

- 2026-06-21: Advanced the Lemma 13.9 SPD/Cholesky bottleneck again by
  importing `LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec` into
  `BlockLU.lean` and adding a `CholeskyFactSpec` bridge:
  `higham13_lemma13_9_cholesky_lower_left_zero_of_order_equiv`,
  `higham13_lemma13_9_cholesky_block_equations_of_cholesky_fact_equiv`,
  `higham13_lemma13_9_cholesky_block_equations_exists_of_spd_equiv`, and
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_equiv`.
  These prove that an order-compatible block equivalence turns repository
  Cholesky upper-triangularity plus `A = R^T R` into the source lower-left zero
  block and the `A22`/`A21` equations; SPD existence supplies such a Cholesky
  factor.  Lemma 13.9 remains open only at the certificate-instantiation level:
  derive/select the full `A`/`A^{-1}` operator certificates and the
  `A11^{-1} = R11^{-1} R11^{-T}` certificate from the SPD/inverse surface, then
  instantiate `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_equiv`.

- 2026-06-21: Specialized the Lemma 13.9 `CholeskyFactSpec` bridge to the
  standard source block ordering `finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r+s)`.
  New declarations:
  `higham13_lemma13_9_finSumFinEquiv_leading_lt_trailing`,
  `higham13_lemma13_9_cholesky_block_equations_of_cholesky_fact_fin_sum`,
  `higham13_lemma13_9_cholesky_block_equations_exists_of_spd_fin_sum`, and
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum`.
  These discharge the arbitrary order side condition for the source-shaped
  `Fin (r+s)` partition.  The remaining Lemma 13.9 blocker is now only the
  full `A`/`A^{-1}` and `A11^{-1}` operator-certificate instantiation needed
  by the standard route.

- 2026-06-21: Closed the Lemma 13.9 pulled-back operator-certificate
  reindexing dependency.  `MatrixAlgebra.lean` now has
  `finiteVecNorm2_reindex_equiv`, `finiteMatVec_reindex_equiv`, and
  `finiteOpNorm2Le_reindex_equiv`, proving finite Euclidean norms,
  matrix-vector products, and vector-action operator-2 certificates are
  invariant under simultaneous row/column equivalence reindexing.  `BlockLU.lean`
  now imports `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` directly and has
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_full_operator`,
  which feeds ordinary full `Fin (r+s)` certificates for `A` and `A^{-1}` into
  the standard `finSumFinEquiv` Cholesky route.  Verification passed:
  direct Lean checks for `MatrixAlgebra.lean` and `BlockLU.lean`, focused builds
  for both modules, `lake env lean -s 65536 examples/LibraryLookup.lean`, axiom
  audit with only standard Mathlib axioms, `git diff --check`, placeholder scan,
  and scratch cleanup.  Lemma 13.9 remains open at the true source certificate
  surface: derive/select the full `A`/`A^{-1}` operator certificates and prove
  the `A11^{-1} = R11^{-1} R11^{-T}` Cholesky-principal-inverse certificate
  from SPD/inverse data.

- 2026-06-21: Closed the follow-on Lemma 13.9 repository-operator predicate
  adapter.  `MatrixAlgebra.lean` now has `finiteOpNorm2Le_of_opNorm2Le`, the
  converse bridge to the earlier `opNorm2Le_of_finiteOpNorm2Le`, and
  `BlockLU.lean` now has
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_opNorm2`.
  The standard source-order Cholesky route can now consume ordinary full
  `opNorm2Le` certificates for `A` and `A^{-1}` directly.  Verification passed:
  direct Lean checks for `MatrixAlgebra.lean` and `BlockLU.lean`, focused builds
  for `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` and
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536
  examples/LibraryLookup.lean`, axiom audit with only standard Mathlib axioms,
  `git diff --check`, placeholder scan, and scratch cleanup.  Lemma 13.9 is
  still open at the mathematical source certificate surface: derive/select the
  full `A`/`A^{-1}` operator-norm certificates and prove the `A11^{-1}`
  Cholesky-principal-inverse certificate from SPD/inverse data.

- 2026-06-21: Closed the source-aligned Lemma 13.9 principal-inverse route
  adapter.  `MatrixAlgebra.lean` now has `opNorm2Le_radius_nonneg`, the
  ordinary square-operator analogue of the earlier finite-radius helper, and
  `BlockLU.lean` now has
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_principal_inverse`.
  This wrapper feeds the standard `Fin (r+s)` Cholesky route with an
  operator-2 certificate for the actual leading-principal inverse `A11^{-1}`
  and the source identity `A11^{-1} = R11^{-1} R11^{-T}`; it deliberately does
  not treat `A11^{-1}` as the upper-left block of the full inverse.  Verification
  passed: direct Lean checks for `MatrixAlgebra.lean` and `BlockLU.lean`,
  focused builds for `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` and
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536
  examples/LibraryLookup.lean`, axiom audit with only standard Mathlib axioms,
  `git diff --check`, placeholder scan, and scratch cleanup.  Lemma 13.9
  remains open at deriving the full `A` and actual leading-principal inverse
  operator certificates from the bare SPD source surface.

- 2026-06-21: Closed the Lemma 13.9 `R11 =` leading Cholesky block
  nonsingular-inverse bridge.  `BlockLU.lean` now has
  `higham13_lemma13_9_R11_nonsingInv_right_inverse_of_cholesky_fact_fin_sum`,
  which derives `IsRightInverse r R11 (nonsingInv r R11)` from
  `CholeskyFactSpec` upper-triangularity and positive diagonal, and
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_principal_inverse_nonsingInv`,
  which instantiates the principal-inverse route with `R11inv = nonsingInv r
  R11`.  Verification passed: `lake env lean
  LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536
  examples/LibraryLookup.lean`, axiom audit with only standard Mathlib axioms,
  `git diff --check`, placeholder scan, and scratch cleanup.  Lemma 13.9
  remains open only at deriving/selecting the full `A` operator certificate and
  actual leading-principal inverse operator certificate from the bare SPD
  source surface.

- 2026-06-21: Closed the Lemma 13.9 PSD/Loewner-to-operator bridge for the
  actual leading-principal inverse route.  `MatrixAlgebra.lean` now has
  `finitePSD_cauchy_schwarz`,
  `finiteVecNorm2Sq_finiteMatVec_le_of_finitePSD_of_finiteLoewnerLe_smul_id`,
  and `finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_smul_id`, proving that
  a symmetric PSD finite matrix bounded by `c I` in Loewner order has
  operator-2 norm at most `c`.  `BlockLU.lean` now has
  `higham13_lemma13_9_principal_inverse_operator_certificate_from_loewner` and
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_principal_inverse_loewner`,
  which feed that certificate into the existing `nonsingInv` Cholesky route.
  Verification passed: direct Lean checks for `MatrixAlgebra.lean` and
  `BlockLU.lean`, focused builds for `LeanFpAnalysis.FP.Analysis.MatrixAlgebra`
  and `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536
  examples/LibraryLookup.lean`, axiom audit with only standard Mathlib axioms,
  `git diff --check`, placeholder scan, and scratch cleanup.  Lemma 13.9
  remains open at deriving/selecting the full `A` operator certificate and the
  actual leading-principal inverse PSD/Loewner upper certificate from the bare
  SPD source surface.

- 2026-06-21: Closed the Lemma 13.9 full-SPD side of the Loewner certificate
  route.  `MatrixAlgebra.lean` now has `finiteQuadraticForm_eq_sum_sum`;
  `BlockLU.lean` now has `isSymPosDef_to_IsSymmetricFiniteMatrix`,
  `finitePSD_of_isSymPosDef`,
  `higham13_lemma13_9_full_operator_certificate_from_spd_loewner`, and
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_and_principal_inverse_loewner`.
  These discharge the full-matrix symmetry/PSD hypotheses from the repository
  `IsSymPosDef` predicate and feed the full `A` side into the existing
  Cholesky route from a scalar-identity Loewner upper certificate.  Verification
  passed: direct Lean checks for `MatrixAlgebra.lean` and `BlockLU.lean`,
  focused builds for `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` and
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536
  examples/LibraryLookup.lean`, axiom audit with only standard Mathlib axioms,
  `git diff --check`, placeholder scan, and scratch cleanup.  Lemma 13.9
  remains open at deriving the scalar-identity Loewner upper certificates,
  especially for the actual leading-principal inverse, from the bare SPD source
  surface.

- 2026-06-21: Closed the Lemma 13.9 principal-inverse Gram certificate side of
  the Loewner route.  `MatrixAlgebra.lean` now has
  `rectMatMul_self_transpose_symmetric`,
  `finiteQuadraticForm_rectMatMul_self_transpose_eq_sum_sq`,
  `finitePSD_rectMatMul_self_transpose`,
  `IsSymmetricFiniteMatrix_of_eq_rectMatMul_self_transpose`, and
  `finitePSD_of_eq_rectMatMul_self_transpose`, proving that a rectangular Gram
  product `M M^T` is symmetric PSD and transporting those facts across an
  equality.  `BlockLU.lean` now has
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_and_principal_inverse_loewner_upper`,
  which uses the identity `A11inv = R11inv R11inv^T` to discharge the actual
  leading-principal inverse symmetry/PSD obligations.  Verification passed:
  direct Lean checks for `MatrixAlgebra.lean` and `BlockLU.lean`, focused build
  for `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536
  examples/LibraryLookup.lean`, and axiom audit with only standard Mathlib
  axioms.  Lemma 13.9 remains open at deriving the scalar-identity Loewner
  upper certificates for full `A` and the actual leading-principal inverse from
  the bare SPD source surface.

- 2026-06-21: Advanced the Lemma 13.9 certificate route from raw Loewner upper
  hypotheses to spectral upper certificates.  `MatrixSpectral.lean` now has
  `finiteOpNorm2Le_of_finitePSD_of_finiteHermitianEigenvalues_le` and
  `opNorm2Le_of_finitePSD_of_finiteHermitianEigenvalues_le`, packaging
  symmetric PSD plus pointwise Hermitian eigenvalue upper bounds into operator-2
  certificates.  `BlockLU.lean` now imports `MatrixSpectral` and has
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_and_principal_inverse_eigenvalue_upper`,
  which feeds full-`A` and actual-principal-inverse eigenvalue upper bounds into
  the standard source-order Cholesky route.  Verification passed: direct Lean
  checks for `MatrixSpectral.lean` and `BlockLU.lean`, focused builds for
  `LeanFpAnalysis.FP.Analysis.MatrixSpectral` and
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536
  examples/LibraryLookup.lean`, and axiom audit with only standard Mathlib
  axioms.  Lemma 13.9 remains open at proving the source norm/eigenvalue upper
  certificates for full `A` and the actual leading-principal inverse, matching
  the book's `||.||_2`/`κ_2(A)` surface.

- 2026-06-21: Advanced Lemma 13.9 again by proving the lower/upper Loewner
  route for the actual leading-principal inverse.  `MatrixAlgebra.lean` now has
  finite Loewner/quadratic-form reindexing, principal-block inheritance for
  Loewner bounds and scalar identities, a right-inverse Loewner upper theorem
  `finiteLoewnerLe_right_inverse_upper_of_smul_id_le`, and
  `IsRightInverse_rectMatMul_transpose_self_of_IsInverse`.  `BlockLU.lean` now
  has the leading-block Cholesky extraction lemmas,
  `higham13_lemma13_9_R11_nonsingInv_inverse_of_cholesky_fact_fin_sum`,
  `higham13_lemma13_9_principal_inverse_loewner_upper_of_full_lower`, and
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_lower_upper`.
  These derive `A11^{-1} <= alpha^{-1} I` from the full lower bound
  `alpha I <= A` and feed full bounds `alpha I <= A <= normA I` to the
  Cholesky route with radius `sqrt(normA * alpha^{-1})`.  Verification passed:
  direct Lean checks/builds for `MatrixAlgebra.lean` and `BlockLU.lean`,
  `lake env lean -s 65536 examples/LibraryLookup.lean`, focused placeholder
  scan, `git diff --check`, and axiom audit with only standard Mathlib axioms.
  Lemma 13.9 remains open at source-identifying/proving the full certificates
  `A <= ||A||_2 I` and `(1 / ||A^{-1}||_2) I <= A`, plus the final
  condition-number presentation.

- 2026-06-21: Narrowed the Lemma 13.9 lower/upper route by eliminating the
  explicit full upper Loewner hypothesis when an ordinary repository
  `opNorm2Le A normA` certificate is available.  `MatrixAlgebra.lean` now has
  `finiteLoewnerLe_smul_id_of_opNorm2Le`; `BlockLU.lean` now has
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_lower_opNorm2_upper`.
  Verification passed: direct Lean checks for `MatrixAlgebra.lean` and
  `BlockLU.lean` after rebuilding `MatrixAlgebra`, focused build for
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536
  examples/LibraryLookup.lean`, placeholder scan, `git diff --check`, and
  axiom audit with only standard Mathlib axioms.  At this checkpoint Lemma 13.9
  still awaited the lower certificate `(1 / ||A^{-1}||_2) I <= A` and the final
  `sqrt(kappa_2(A))` presentation.

- 2026-06-21: Closed the Lemma 13.9 lower-certificate dependency in
  certificate form.  `MatrixAlgebra.lean` now has
  `finiteLoewnerLe_smul_id_le_of_right_inverse_finiteOpNorm2Le` and
  `finiteLoewnerLe_smul_id_le_of_right_inverse_opNorm2Le`, proving
  `(normAinv)^{-1} I <= A` from SPD symmetry/PSD, `A * Ainv = I`, and
  `opNorm2Le Ainv normAinv`.  `BlockLU.lean` now has
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_opNorm2_inverse`,
  combining `opNorm2Le A normA`, `opNorm2Le Ainv normAinv`, and the standard
  Cholesky route to prove the radius `sqrt(normA * normAinv)`.  Verification
  passed: direct Lean checks for `MatrixAlgebra.lean` and `BlockLU.lean`,
  focused builds for `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` and
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536
  examples/LibraryLookup.lean`, placeholder scan, `git diff --check`, and
  axiom audit with only standard Mathlib axioms.  At this checkpoint Lemma 13.9
  still awaited the exact source 2-norm/condition-number presentation
  `sqrt(kappa_2(A))`, not the inverse-norm lower Loewner certificate.

- 2026-06-21: Closed the Lemma 13.9 exact norm/condition-number surface.
  `MatrixAlgebra.lean` now has exact `opNorm2` pinned to Mathlib's finite l2
  operator norm, `opNorm2_nonneg`, `opNorm2Le_opNorm2`,
  `opNorm2_pos_of_right_inverse_at`, `opNorm2_pos_of_right_inverse`, and
  `kappa2`.  `BlockLU.lean` now has
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2`
  and the stronger
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2_of_right_inverse`,
  which proves the Lemma 13.9 Cholesky-route radius `sqrt(kappa2 A Ainv)` and
  derives `0 < opNorm2 Ainv` from the right-inverse certificate.  Verification
  passed: direct Lean checks for `MatrixAlgebra.lean` and `BlockLU.lean`,
  focused builds for `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` and
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536
  examples/LibraryLookup.lean`, placeholder scan, `git diff --check`, scratch
  cleanup, and axiom audit with only standard Mathlib axioms.  At this checkpoint
  Lemma 13.9 still awaited bare-source instantiation: choosing/proving the
  canonical inverse/right-inverse and Cholesky certificate from SPD, or keeping
  those assumptions explicit without claiming full source closure.  The later
  source-facing closure checkpoint below supersedes this open status.

- 2026-06-21: Closed the Lemma 13.9 canonical inverse dependency.  `BlockLU.lean`
  now has `isSymPosDef_to_matrix_posDef`, `isSymPosDef_det_ne_zero`, and
  `isRightInverse_nonsingInv_of_isSymPosDef`, deriving the canonical repository
  `nonsingInv` right-inverse certificate from the source SPD predicate via
  Mathlib positive-definite determinant positivity.  The new wrapper
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2_nonsingInv`
  proves the Lemma 13.9 route with radius
  `sqrt(kappa2 A (nonsingInv (r+s) A))`, removing the arbitrary `Ainv` and
  right-inverse hypotheses.  Verification passed: direct Lean check and focused
  build for `BlockLU.lean`, `lake env lean -s 65536 examples/LibraryLookup.lean`,
  placeholder scan, `git diff --check`, scratch cleanup, and axiom audit with
  only standard Mathlib axioms.  At this checkpoint Lemma 13.9 still awaited
  packaging the Cholesky factor/block identity and displayed
  `A11inv = R11^{-1}R11^{-T}` from the bare SPD source surface.  The later
  source-facing closure checkpoint below supersedes this open status.

- 2026-06-21: Closed Lemma 13.9 in the source-facing exact
  2-norm/canonical-inverse form.  `MatrixAlgebra.lean` now has
  `nonsingInv_eq_of_isRightInverse` and
  `nonsingInv_rectMatMul_transpose_self_of_IsInverse`; `BlockLU.lean` now has
  `higham13_lemma13_9_exists_cholesky_route_rectOpNorm2Le_from_spd_kappa2_nonsingInv`,
  `higham13_lemma13_9_leading_nonsingInv_eq_cholesky_fact_fin_sum`, and
  `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_spd_leading_nonsingInv_kappa2`.
  The final theorem chooses a Cholesky factor from SPD, identifies the leading
  principal inverse with `R11^{-1} R11^{-T}`, uses the canonical full inverse
  `nonsingInv (r+s) A`, and proves the Lemma 13.9 bound with radius
  `sqrt (kappa2 A (nonsingInv _ A))`.  Verification passed: direct Lean checks
  and focused builds for `MatrixAlgebra.lean` and `BlockLU.lean`,
  `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan,
  `git diff --check`, scratch cleanup, and axiom audit with only standard
  Mathlib axioms.  The Lemma 13.9 bottleneck is closed; the active SPD-section
  blocker is now Lemma 13.10.

- 2026-06-21: Advanced the Lemma 13.10 SPD Schur-complement route without
  closing the final source theorem.  `MatrixAlgebra.lean` now has the exact
  norm converse bridges `opNorm2_le_of_opNorm2Le` and
  `opNorm2_le_of_finiteOpNorm2Le`, the product bridge
  `kappa2_le_of_opNorm2Le_bounds`, and the reusable Loewner/operator adapter
  `finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_of_finiteOpNorm2Le`.
  `BlockLU.lean` now has
  `higham13_spd_schurComplement_source_loewnerLe_A22`,
  `higham13_spd_schurComplement_source_loewnerLe_A22_of_full`,
  `higham13_lemma13_10_schur_opNorm2Le_of_full_operator_bound`, and
  `higham13_problem13_4_Sinv_finiteOpNorm2Le_from_block_inverse`.  These prove
  the source Loewner bound `S <= A22`, the finite operator certificate
  `||S||_2 <= ||A||_2`, and the block-inverse finite operator certificate
  `||S^{-1}||_2 <= ||A^{-1}||_2`.  Verification passed: direct Lean checks for
  `MatrixAlgebra.lean` and `BlockLU.lean`, focused builds for both modules,
  `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan over
  `MatrixAlgebra.lean`, `BlockLU.lean`, and `LibraryLookup.lean`,
  `git diff --check`, and axiom audit with only standard Mathlib axioms.

- 2026-06-21: Threaded the Algorithm 13.3 right-inverse/reciprocal bridge into
  the concrete column-BDD active route.  New `BlockLU.lean` wrappers:
  `higham13_algorithm13_3_diagLowerCert_pivot_bound_of_pivot_right_inverse_reciprocal`,
  `higham13_algorithm13_3_active_column_dominance_of_column_bdd_pivot_right_inverse_reciprocal`,
  `higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_pivot_right_inverse_reciprocal`,
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_pivot_right_inverse_reciprocal`.
  These derive the direct pivot product bound, active column dominance,
  active-stage `2*max` growth, and Eq.13.21 assembled-upper bound from actual
  active pivot right-inverse data plus the concrete reciprocal certificate.
  At that checkpoint the concrete reciprocal certificate for `diagLowerCert`
  remained the open active-pivot source obligation; the later source-table
  bridge narrows this to instantiating the source inverse-bound table or proving
  the direct active product bound.  Verification passed: direct `BlockLU.lean`
  check, focused `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build,
  `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan over
  `MatrixAlgebra.lean`, `BlockLU.lean`, and `LibraryLookup.lean`,
  `git diff --check`, and axiom audit with only standard Mathlib axioms.
  At that pass, the next Lemma 13.10 target was the exact source theorem
  `higham13_lemma13_10_schur_kappa_bound_of_spd`, aligning these finite
  certificates with the `Fin (r+s)` source block extraction, canonical
  `nonsingInv` choices, and exact `kappa2` surface without a target-equivalent
  hypothesis.

- 2026-06-21: Advanced the Lemma 13.10 inverse-certificate route one step
  closer to the exact source surface.  `MatrixAlgebra.lean` now has
  `finiteOpNorm2Le_invOf_reindex_equiv_nonsingInv`, which turns a Mathlib
  `⅟` inverse of an equivalently reindexed source matrix into a finite
  operator certificate bounded by `opNorm2 (nonsingInv n A)`.  `BlockLU.lean`
  now has
  `higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_block_inverse`,
  which applies that bridge to the Schur complement lower-right inverse block
  after `finSumFinEquiv` source block identification.  Verification passed:
  direct Lean checks for `MatrixAlgebra.lean` and `BlockLU.lean`, focused
  builds for `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` and
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`,
  `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan over
  `MatrixAlgebra.lean`, `BlockLU.lean`, and `LibraryLookup.lean`,
  `git diff --check`, and axiom audit with only standard Mathlib axioms.
  Remaining
  Lemma 13.10 work: discharge SPD-derived constructive invertibility of the
  leading block/Schur complement/full reindexed block, identify `⅟S` with the
  Schur `nonsingInv`, and compose the exact `kappa2` product.

- 2026-06-21: Closed the Chapter 13 Lemma 13.10 SPD Schur-complement
  condition-number theorem.  `MatrixAlgebra.lean` now has
  `kappa2_le_of_opNorm2Le_bounds_general`, the mixed-dimension exact
  `kappa2` monotonicity bridge.  `BlockLU.lean` now has
  `higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_posDef_block_inverse`,
  `higham13_lemma13_10_schur_kappa_bound_of_source_posDef_block`, and the
  source-facing final theorem
  `higham13_lemma13_10_schur_kappa_bound_of_spd`.  The final theorem assumes
  only `IsSymPosDef (r+s) A` plus `[Nonempty (Fin s)]` as the nonempty trailing
  Schur-complement domain condition, forms the standard `finSumFinEquiv`
  source blocks, and proves
  `kappa2 S (nonsingInv s S) <= kappa2 A (nonsingInv (r+s) A)`.  Verification
  passed: direct Lean checks for `MatrixAlgebra.lean` and `BlockLU.lean`,
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`,
  `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan over
  `MatrixAlgebra.lean`, `BlockLU.lean`, and `LibraryLookup.lean`,
  `git diff --check`, and `#print axioms` for the closure chain with only
  standard Mathlib axioms.  The SPD-section Lemma 13.10 bottleneck is closed;
  Problem 13.4 remains open separately in the source max-entry norm.

- 2026-06-21: Advanced the Algorithm 13.3 active pivot route by closing the
  nonzero-norm/product step from actual inverse data.  `MatrixAlgebra.lean` now
  has `norm_ne_zero_of_isRightInverse`, proving that a right inverse on a
  nonempty square block is nonzero in the ambient function norm.  `BlockLU.lean`
  now has
  `higham13_algorithm13_3_diagLowerCert_active_mul_eq_one_of_pivot_right_inverse_reciprocal`,
  which turns active Schur-stage pivot right-inverse data plus the concrete
  reciprocal diagonal certificate for `diagLowerCert` into the active product
  identity `gamma_k * ||pivotInv_k|| = 1`.  This does not close Theorem 13.7,
  Theorem 13.8, or Eq.13.21 by itself: the reciprocal/direct certificate for
  the concrete `diagLowerCert` remains the active Algorithm 13.3 bottleneck.
  Verification passed: direct Lean checks for `MatrixAlgebra.lean` and
  `BlockLU.lean`, focused build for
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`,
  `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan over
  `MatrixAlgebra.lean`, `BlockLU.lean`, and `LibraryLookup.lean`,
  `git diff --check`, and axiom audit with only standard Mathlib axioms.

- 2026-06-21: Continued the Chapter 13 red-bottleneck pass after the context
  handoff.  The Algorithm 13.3 active-pivot route was sharpened by inspecting
  the existing Theorem 13.2/leading-prefix nonsingularity declarations
  (`BlockLUFactSpec.existsUnique_of_leadingPrincipalBlockNonsingular13_2`,
  `LeadingPrincipalBlockNonsingular13_2.first_block_inverse`,
  `LeadingPrincipalBlockNonsingular13_2.schur`) against the concrete
  `higham13_algorithm13_3_schurStageBlock`; the missing theorem remains a
  link from the arbitrary active `pivotInv` sequence to the recursive first
  block inverses or a direct product bound for
  `higham13_algorithm13_3_diagLowerCert`.  Problem 13.4 now has four
  source-object max-entry bridges:
  `higham13_problem13_4_A11inv_maxEntryNormRect_from_entrywise_bound`,
  `higham13_problem13_4_A21A11inv_maxEntryNormRect_from_displayed_inverse_entry_bound`,
  `higham13_problem13_4_Sinv_maxEntryNormRect_from_entrywise_bound`, and
  `higham13_problem13_4_schur_kappa_maxEntryNormRect_from_entrywise_inverse_bound`.
  These let displayed entrywise certificates for the actual `A11^{-1}` and
  `S^{-1}` feed the lower-left solve and Schur condition-product bounds
  without routing through full-inverse block equalities.  The full source
  Problem 13.4 row remains open until those displayed entrywise inverse
  certificates are derived from the source growth/condition hypotheses.
  Verification passed for this pass: direct `BlockLU.lean`, focused
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build,
  `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan over
  `BlockLU.lean` and `LibraryLookup.lean`, `git diff --check`, scratch-file
  cleanup, and `#print axioms` for the four new declarations with only
  standard Mathlib axioms.

- 2026-06-21: Advanced the Chapter 13 Problem 13.4 source max-entry route past
  the old displayed-inverse-entry certificate blocker.  `BlockLU.lean` now has
  `higham13_problem13_4_A21A11inv_maxEntryNormRect_from_block_inverse_growth`,
  proving the first displayed Problem 13.4 inequality from the block-inverse
  identity `A21 A11^{-1} = -S (A^{-1})21`, Schur-growth entries, full-inverse
  max-entry entries, the dimension bound `s <= n`, and the condition-product
  certificate.  It also has
  `higham13_problem13_4_maxEntry_bounds_from_block_inverse_growth`, pairing
  that lower-left bound with the existing Schur lower-right block-inverse
  condition-product theorem.  Verification passed: direct `BlockLU.lean`,
  focused `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build,
  `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan over
  `BlockLU.lean`, `LibraryLookup.lean`, and the temporary axiom file,
  `git diff --check`, scratch-file cleanup, and `#print axioms` for the two new
  declarations with only standard Mathlib axioms.  The selected Problem 13.4
  row remained open at that checkpoint for instantiating the explicit
  Schur-growth, full-inverse max-entry, dimension, and condition-product
  certificates from the formal GE growth-factor/max-entry condition-number
  surfaces and then threading the result into Eq.13.22/Eq.13.23.  A later
  checkpoint instantiates the full-inverse max-entry certificate from source
  block identification and `nonsingInv`.

- 2026-06-21: Narrowed the Chapter 13 Problem 13.4 source bridge further by
  instantiating the full-inverse max-entry certificate from source block
  identification.  `BlockLU.lean` now has
  `maxEntryNormRect_invOf_reindex_equiv_nonsingInv_entry_bound`, the max-entry
  analogue of the existing operator-2 inverse/reindex bridge, and
  `higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth`,
  which feeds `nonsingInv (r+s) A` into the paired block-inverse Problem 13.4
  theorem.  Verification passed: direct `BlockLU.lean`, focused
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build,
  `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan over
  `BlockLU.lean`, `LibraryLookup.lean`, and the temporary axiom file,
  `git diff --check`, scratch-file cleanup, and `#print axioms` for the two new
  declarations with only standard Mathlib axioms.  Remaining Problem 13.4 work
  is now Schur-growth and condition-product instantiation from the formal GE
  growth-factor/max-entry condition-number surfaces, followed by
  Eq.13.22/Eq.13.23 integration.

- 2026-06-21: Narrowed the same Problem 13.4 route again by adding
  `higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth_exact_kappa`
  to `BlockLU.lean`.  This wrapper chooses the source max-entry condition
  number as the exact product
  `||A||_max * ||nonsingInv (r+s) A||_max`, so the paired Problem 13.4
  source-indexed bounds now require only the Schur-growth entry certificate
  (plus block identifications, dimensions, and invertibility).  Lookup,
  inventory, bottleneck, and proof-source docs were updated accordingly; the
  focused `BlockLU.lean` check, focused `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`
  build, fresh executable lookup, production Lean-file placeholder scan,
  `git diff --check`, scratch-file cleanup, and `#print axioms` all passed
  (only standard Mathlib axioms).  The first axiom/lookup attempts raced the
  rebuild and saw stale object files, then passed after the rebuild.  The
  remaining Problem 13.4 work is Schur-growth instantiation from the formal GE
  growth-factor surface and Eq.13.22/Eq.13.23 integration.

- 2026-06-21: Added the norm-level Schur-growth surface
  `higham13_problem13_4_maxEntry_bounds_from_source_schur_growth_exact_kappa`
  to `BlockLU.lean`.  It takes the book-shaped premise
  `||S||_max <= rho * ||A||_max`, derives the entrywise Schur-growth
  certificate using `entry_le_maxEntryNormRect`, and feeds the exact-κ
  source block-inverse route.  This closes the entrywise/norm-level mismatch
  in the active Problem 13.4 row; what remains is proving that norm-level
  Schur-growth premise from formal GE growth-factor data and then threading
  the resulting bounds into Eq.13.22/Eq.13.23.  Lookup/report/inventory/
  bottleneck/proof-source docs were updated.  Verification passed: direct
  `BlockLU.lean`, focused `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build,
  fresh executable lookup, production Lean-file placeholder scan,
  `git diff --check`, scratch-file cleanup, and `#print axioms` with only
  standard Mathlib axioms.  The first axiom/lookup attempts raced the rebuild
  and then passed after the rebuild.

- 2026-06-21: Added and audited the formal `growthFactorEntry` specialization
  of the active Problem 13.4 max-entry route.  `BlockLU.lean` now has
  `maxEntryNormRect_eq_maxEntryNorm`,
  `maxEntryNormRect_le_growthFactorEntry_mul_of_le_maxEntryNorm`, and
  `higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa`.
  This instantiates `rho` as `growthFactorEntry hN A U hApos` and leaves the
  source row narrowed to the concrete GE/stage inclusion `||S||_max <=
  ||U||_max`, followed by Eq.13.22/Eq.13.23 integration.  Verification passed:
  focused `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build, fresh executable
  lookup, placeholder scan over `BlockLU.lean`, `LibraryLookup.lean`, and the
  temporary axiom file, `git diff --check`, scratch-file cleanup, and
  `#print axioms` for the three declarations with only standard Mathlib axioms.

- 2026-06-21: Added the Schur-submatrix growth-factor bridge for Problem 13.4.
  `BlockLU.lean` now has `maxEntryNormRect_le_maxEntryNorm_of_reindex_eq` and
  `higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa_of_schur_submatrix`.
  This replaces the remaining direct `||S||_max <= ||U||_max` premise by the
  concrete entrywise equality saying the displayed Schur complement is the
  lower-right block of the formal growth-factor matrix/stage.  That local
  equality is now closed by the subsequent one-step Schur-stage matrix theorem;
  the selected row remains open for global/recursive growth-factor and
  Eq.13.22/Eq.13.23 integration.  Verification passed: direct `BlockLU.lean`, focused
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build, fresh executable lookup,
  placeholder scan over `BlockLU.lean`, `LibraryLookup.lean`, and the temporary
  axiom file, `git diff --check`, scratch-file cleanup, and `#print axioms`
  for the two declarations with only standard Mathlib axioms.  The first
  axiom/lookup attempts raced the rebuild and then passed after the rebuild.

- 2026-06-21: Added the concrete local Schur-stage growth-matrix closure for
  Problem 13.4.  `BlockLU.lean` now has
  `higham13_problem13_4_schurStageMatrix`,
  `higham13_problem13_4_schurStageMatrix_lower_right`, and
  `higham13_problem13_4_maxEntry_bounds_from_source_schurStageMatrix_exact_kappa`.
  This instantiates the lower-right Schur/growth-block equality by construction
  for the one-step Schur-stage matrix and proves both Problem 13.4 inequalities
  with `rho = growthFactorEntry` for that local stage.  The selected row remains
  open only for connecting this local stage object to the recursive/global GE
  growth-factor surface and threading the result into Eq.13.22/Eq.13.23.
  Verification passed: direct `BlockLU.lean`, focused
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build, fresh executable lookup,
  placeholder scan over `BlockLU.lean`, `LibraryLookup.lean`, and the temporary
  axiom file, `git diff --check`, scratch-file cleanup, and `#print axioms` for
  the two theorem declarations with only standard Mathlib axioms.

- 2026-06-21: Added the Algorithm 13.3 source-table diagonal-lower bridge.
  `BlockLU.lean` now has
  `higham13_algorithm13_3_diagLowerCert_active_le_of_diag_update` and
  `higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table`.  These
  close the bookkeeping from any source inverse-bound table satisfying the
  Eq.13.18 active diagonal update inequality, initial lower bound, and active
  reciprocal upper bounds to the concrete `diagLowerCert` one-sided pivot
  certificate.  The Algorithm 13.3 red row is now narrowed to instantiating that
  source inverse-bound table from actual nonsingular Schur-stage pivots, or
  proving the direct active product bound for the concrete pivots.  Verification
  passed before this checkpoint: direct `BlockLU.lean`, focused
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build, fresh executable lookup,
  placeholder scan over `BlockLU.lean`, `LibraryLookup.lean`, and the temporary
  scratch/axiom files, `git diff --check`, scratch-file cleanup, and
  `#print axioms` for both theorem declarations with only standard Mathlib
  axioms.

- 2026-06-22: Added the local Problem 13.4 -> Eq.13.22 lower-factor premise
  bridge.  `GrowthFactor.lean` now has `growthFactorEntry_nonneg` and
  `growthFactorEntry_ge_one_of_maxEntryNorm_le`; `BlockLU.lean` now has
  `higham13_problem13_4_L21_eq13_22_premise_from_source_schurStageMatrix_exact_kappa`.
  The bridge reuses the local one-step Schur-stage Problem 13.4 theorem and
  proves the scalar promotion from `n rho kappa(A)` to `n rho^2 kappa(A)` once
  the chosen stage growth matrix also contains the initial max-entry norm.
  This closes the local algebraic Eq.13.22 lower-factor premise step; it does
  not close the global recursive GE growth-factor inclusion, the Eq.13.21
  upper-factor premise, or the full Eq.13.22/Eq.13.23 source integration.
  Verification passed: direct `GrowthFactor.lean`, focused
  `LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor` build, direct `BlockLU.lean`,
  focused `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build, fresh executable
  lookup, placeholder scan over `GrowthFactor.lean`, `BlockLU.lean`, and
  `LibraryLookup.lean`, `git diff --check`, scratch-file cleanup, and
  `#print axioms` for all three declarations with only standard Mathlib axioms.

- 2026-06-22: Generalized the local Problem 13.4 -> Eq.13.22 lower-factor
  bridge to an arbitrary source growth matrix.  `BlockLU.lean` now has
  `higham13_problem13_4_L21_eq13_22_premise_from_source_growthFactorEntry_exact_kappa`,
  and the previous local Schur-stage theorem
  `higham13_problem13_4_L21_eq13_22_premise_from_source_schurStageMatrix_exact_kappa`
  now reuses it.  The general theorem proves the `n rho^2 kappa(A)` lower-left
  Eq.13.22 premise from two explicit growth-object containments:
  `maxEntryNorm A <= maxEntryNorm U` and `maxEntryNormRect S <= maxEntryNorm U`.
  This is the source-facing shape needed for a recursive GE growth object; the
  remaining Problem 13.4/Eq.13.22 work is to instantiate those containments
  from that object and combine with the Eq.13.21 upper-factor premise.
  Verification passed: direct `BlockLU.lean`, focused
  `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build, fresh executable lookup,
  placeholder scan over `GrowthFactor.lean`, `BlockLU.lean`, and
  `LibraryLookup.lean`, `git diff --check`, scratch-file cleanup, and
  `#print axioms` for the general/local bridge pair with only standard Mathlib
  axioms.

- 2026-06-22: Added the local Eq.13.22/Eq.13.23 common-growth product bridge for
  Problem 13.4.  `BlockLU.lean` now has
  `maxEntryNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm`,
  `higham13_eq13_22_local_product_from_source_growthFactorEntry_exact_kappa`,
  and `higham13_eq13_23_local_product_from_source_growthFactorEntry_exact_kappa`.
  These combine the source lower-left bound with an Eq.13.21-style upper-factor
  containment under one explicit max-entry growth object; the Eq.13.23 version
  additionally uses the source-side hypothesis `rho_n <= 2`.  The row remains
  open for instantiating the recursive GE growth object and lifting the local
  product to the full recursive `L`/`U` factors; the containment work was later
  narrowed first to a finite local history envelope and then to the dominated
  history-envelope checkpoint below.
  Verification passed:
  direct `BlockLU.lean`, focused `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`
  build, fresh executable lookup after rebuilding the module, placeholder scan
  over touched Lean files and temporary axiom file, `git diff --check`,
  scratch-file cleanup, and `#print axioms` for all three new declarations with
  only standard Mathlib axioms.

- 2026-06-22: Added the block-upper version of the local Eq.13.22/Eq.13.23
  common-growth product bridge for Problem 13.4.  `BlockLU.lean` now has
  `blockMaxNorm_le_maxEntryNorm_of_reindex_eq`,
  `blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm`,
  `higham13_eq13_22_local_block_product_from_source_growthFactorEntry_exact_kappa`,
  and
  `higham13_eq13_23_local_block_product_from_source_growthFactorEntry_exact_kappa`.
  These convert an entrywise embedding of a block upper factor into the common
  max-entry growth-object containment and then combine it with the already
  proved local Problem 13.4 lower-block premise.  The row remains open for a
  genuine recursive/global GE growth object containing the initial matrix, the
  Schur complement, and the block upper factor, followed by a lift from the
  local product to full recursive `L`/`U` factors.  Verification passed: direct
  `BlockLU.lean`, focused `LeanFpAnalysis.FP.Algorithms.LU.BlockLU` build,
  fresh executable lookup, scratch-file cleanup, and `#print axioms` for all
  four new declarations with only standard Mathlib axioms.

- 2026-06-22: Added the finite local growth-history envelope for Chapter 13
  Problem 13.4.  `BlockLU.lean` now has `maxEntryNorm_const_nonneg`,
  `higham13_problem13_4_localGrowthEnvelope`, containment theorems for the
  initial matrix, current Schur complement, and block upper factor, and the
  wrappers
  `higham13_eq13_22_local_block_product_from_history_envelope_exact_kappa` /
  `higham13_eq13_23_local_block_product_from_history_envelope_exact_kappa`.
  This removes the explicit local common-containment hypotheses by using an
  honest finite max-entry history object; it does not claim the recursive GE
  history theorem.  Remaining Problem 13.4 work is to identify or dominate this
  local envelope by the recursive/global GE growth surface and then lift the
  local product to the full recursive `L`/`U` factors.  Verification passed:
  direct `BlockLU.lean`, focused `LeanFpAnalysis.FP.Algorithms.LU.BlockLU`
  build, executable lookup, scratch-file cleanup, and `#print axioms` for the
  new theorem layer with only standard Mathlib axioms.

- 2026-06-22: Added the dominated history-envelope adapters for Chapter 13
  Problem 13.4.  `BlockLU.lean` now has
  `higham13_eq13_22_local_block_product_from_dominated_history_envelope_exact_kappa`
  and
  `higham13_eq13_23_local_block_product_from_dominated_history_envelope_exact_kappa`.
  These wrap the finite local history envelope under one domination hypothesis
  `maxEntryNorm localGrowthEnvelope <= maxEntryNorm G` for the chosen growth
  matrix, so the next real selected-scope theorem is the recursive GE history
  domination result, followed by the full recursive `L`/`U` lift.  Verification
  passed for direct `BlockLU.lean`, the focused BlockLU build, executable
  lookup, scratch-file cleanup, and `#print axioms` for the two dominated
  adapters with only standard Mathlib axioms.

- 2026-06-22: Added a finite Algorithm 13.3 stage-history growth object for
  the Chapter 13 Problem 13.4 route.  `BlockLU.lean` now has
  `higham13_algorithm13_3_stageHistoryBound`,
  `higham13_algorithm13_3_stageHistoryGrowthMatrix`, and containment lemmas for
  the input block table, each recorded Schur stage, and
  `higham13_algorithm13_3_upperFromStages`.  This gives the recursive growth
  route a genuine finite block-stage history object, packaged as a constant
  max-entry growth matrix.  It does not yet prove the flattened/tail
  identification needed to show that `higham13_problem13_4_localGrowthEnvelope`
  is dominated by this history; that is the next meaningful Problem 13.4
  dependency before the full-factor lift.  Verification passed for direct
  `BlockLU.lean`, the focused BlockLU build, executable lookup, scratch-file
  cleanup, and `#print axioms` for the stage-history theorem layer with only
  standard Mathlib axioms.

- 2026-06-22: Added the Problem 13.4 local-envelope domination bridge to the
  Algorithm 13.3 stage-history route.  `BlockLU.lean` now has
  `higham13_problem13_4_localGrowthEnvelope_le_of_bounds`, the universal
  max-entry domination property of the finite local envelope, and
  `higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_initial_schur`,
  which specializes that property to `higham13_algorithm13_3_stageHistoryGrowthMatrix`.
  The specialization discharges the assembled-upper-factor containment via
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_upperFromStages`;
  the remaining local Problem 13.4 dependency is exactly the flattened
  initial-matrix and flattened Schur-complement containment facts for the
  relevant stage/tail, before composing the dominated-envelope product adapters
  and lifting to the full recursive factors.  Verification passed for direct
  `BlockLU.lean`, the focused BlockLU build, executable lookup, scratch-file
  cleanup, and `#print axioms` for the two bridge declarations with only
  standard Mathlib axioms.

- 2026-06-22: Added the Problem 13.4 flat/stage-history containment bridge.
  `BlockLU.lean` now has `blockMatrixFlatFin`, which reindexes a uniform block
  matrix through `finProdFinEquiv` to a standard `Fin (m*r)` square matrix, plus
  `maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm`, proving that this
  reindexing preserves the Chapter 13 max-entry norm.  The stage-history route
  now also has
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_flat_initial`,
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_stage_submatrix`,
  and
  `higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_flat_initial_stage_submatrix`.
  These close the flat-initial max-norm side and the generic recorded-stage
  scalar-submatrix side of the local-envelope domination step.  The remaining
  local Problem 13.4 dependency is the concrete tail-index equality identifying
  the local Schur complement with the relevant Algorithm 13.3 recorded stage
  submatrix, before composing the dominated-envelope Eq.13.22/Eq.13.23 adapters
  and lifting to full recursive factors.  Verification passed for direct
  `BlockLU.lean`, the focused BlockLU build, executable lookup, scratch-file
  cleanup, `git diff --check`, marker scan, and `#print axioms` for the new
  theorem layer with only standard Mathlib axioms.

- 2026-06-22: Added the packaged flat stage-tail containment layer for Chapter
  13 Problem 13.4.  `BlockLU.lean` now has
  `higham13_algorithm13_3_schurStageTailBlock`,
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_flat_stage_tail`,
  and
  `higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_flat_initial_flat_stage_tail`.
  These specialize the flat/stage-history containment machinery to a named
  flattened block tail of a recorded Algorithm 13.3 Schur stage, so the next
  source-specific obligation is the equality between the recursive local Schur
  complement and that packaged stage tail, followed by the global/full-factor
  Eq.13.22/Eq.13.23 lift.  Verification passed for direct `BlockLU.lean`, the
  focused BlockLU build, executable lookup, scratch-file cleanup,
  `git diff --check`, marker scan, and `#print axioms` for the two exported
  bridge declarations with only standard Mathlib axioms.

- 2026-06-22: Added a source-faithful matrix-product Schur-stage tail bridge
  for Chapter 13 Problem 13.4.  `BlockLU.lean` now has
  `higham13_algorithm13_3_schurStageMatrixBlock` and
  `higham13_algorithm13_3_schurStageMatrixBlock_one_tail_eq_blockSchur`; the
  latter proves that the first active tail of the matrix-product Algorithm
  13.3 stage table is exactly `blockSchur A A11_inv` when `pivotInv 0 =
  A11_inv`.  This avoids treating the source block Schur complement as a
  pointwise function-product update.  Remaining Problem 13.4 growth work is to
  put this matrix-product stage tail under the finite stage-history/local
  envelope domination route, then perform the recursive/full-factor
  Eq.13.22/Eq.13.23 lift.  Verification passed for direct `BlockLU.lean`, the
  focused BlockLU build, executable lookup after rebuild, scratch-file cleanup,
  `git diff --check`, marker scan, and `#print axioms` for both declarations
  with only standard Mathlib axioms.

- 2026-06-22: Added the source-faithful matrix-product stage-history/local
  envelope bridge for Chapter 13 Problem 13.4.  `BlockLU.lean` now has
  `higham13_algorithm13_3_upperFromMatrixStages`,
  `higham13_algorithm13_3_matrixStageHistoryBound`,
  `higham13_algorithm13_3_matrixStageHistoryGrowthMatrix`,
  `higham13_algorithm13_3_schurStageMatrixTailBlock`,
  `higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_stage_tail`,
  `higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_flat_initial_flat_stage_tail`,
  and
  `higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_blockSchur_first_tail`.
  This closes the local source Schur-complement domination route using genuine
  matrix multiplication: `blockMatrixFlatFin (blockSchur A A11_inv)` is now
  contained in a matrix-product finite stage-history growth matrix when
  `pivotInv 0 = A11_inv`.  Remaining Problem 13.4/Eq.13.22/Eq.13.23 work is
  the recursive/global lift from the local envelope/product bridges to full
  recursive `L` and `U` factors.  Verification passed for direct
  `BlockLU.lean`, focused BlockLU build, quiet executable lookup after rebuild,
  scratch-file cleanup, `git diff --check`, marker scan, and `#print axioms`
  for the matrix-history theorem layer with only standard Mathlib axioms.

- 2026-06-22: Added the first-split matrix-stage local Eq.13.22/Eq.13.23
  product bridge for Chapter 13 Problem 13.4.  `BlockLU.lean` now has
  `blockMatrixFirstSplitFlat`, `blockMatrixFirstSplitA11`,
  `blockMatrixFirstSplitA12`, `blockMatrixFirstSplitA21`,
  `blockMatrixFirstSplitA22`,
  `blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur`,
  `higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_blockSchur_first_split`,
  `higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_blockSchur_first_split_of_hN`,
  `higham13_eq13_22_local_block_product_from_matrix_stage_history_first_split_exact_kappa`,
  and
  `higham13_eq13_23_local_block_product_from_matrix_stage_history_first_split_exact_kappa`.
  This aligns the source first pivot block with the local `r + m*r` split,
  proves the scalar Schur complement is the flattened `blockSchur`, and
  instantiates the local Eq.13.22/Eq.13.23 block-product bounds against the
  matrix-product Algorithm 13.3 history.  Remaining Problem
  13.4/Eq.13.22/Eq.13.23 work is the recursive/global full-factor lift.
  Verification passed for direct `BlockLU.lean`, focused BlockLU build,
  executable lookup after rebuild, scratch-file cleanup, `git diff --check`,
  marker scan, and `#print axioms` for the first-split theorem layer with only
  standard Mathlib axioms.

- 2026-06-22: Added the first recursive/full-factor norm-lift dependencies for
  Chapter 13 Problem 13.4:
  `blockLUOneStepL_blockMaxNorm_le_of_firstSplit_tail`,
  `blockLUOneStepU_blockMaxNorm_le_of_firstRow_tail`, and
  `blockLUOneStep_blockMaxNorm_product_le_of_firstSplit_tail`.  They prove
  that the explicit one-step lower/upper factors, and then their product, are
  bounded in block max norm by common constants when the first-split lower-left
  block / first block row and recursive Schur-tail factors are bounded.  These
  are real dependencies for the full recursive Eq.13.22/Eq.13.23 lift; the
  recursive induction theorem remains open.  Verification passed for direct
  `BlockLU.lean`, focused BlockLU build, quiet executable lookup,
  scratch-file cleanup, and `#print axioms` for the one-step norm-lift
  theorems with only standard Mathlib axioms.

- 2026-06-22: Added the Algorithm 13.3 matrix-stage lower-factor surface for
  the Chapter 13 Problem 13.4 full-factor route:
  `higham13_algorithm13_3_lowerFromMatrixStages` and
  `higham13_algorithm13_3_lowerFromMatrixStages_blockMaxNorm_bound`, then added
  the full assembled product wrapper
  `higham13_algorithm13_3_matrixStages_LU_product_bound`.  The lower factor
  uses identity diagonal blocks, zero strict upper blocks, and below the
  diagonal uses the source multiplier block `A_ij^(j) * pivotInv j` from the
  matrix-product Schur-stage table.  The norm theorem lifts per-stage
  multiplier bounds plus `1 <= C` to a block max-norm bound for the assembled
  lower factor; the product theorem combines that with any assembled-upper
  bound.  Verification passed for direct `BlockLU.lean`, focused BlockLU build,
  quiet executable lookup, scratch-file cleanup, and `#print axioms` with only
  standard Mathlib axioms.

- 2026-06-22: Added conditional full assembled matrix-stage Eq.13.22/Eq.13.23
  wrappers for the Chapter 13 Problem 13.4 route:
  `higham13_eq13_22_matrix_stage_product_from_multiplier_bounds` and
  `higham13_eq13_23_matrix_stage_product_from_multiplier_bounds`.  These use
  `higham13_algorithm13_3_lowerFromMatrixStages` and
  `higham13_algorithm13_3_upperFromMatrixStages` as the full factor surfaces,
  combine per-stage lower multiplier bounds with the assembled-upper
  `growthFactorEntry` containment, and produce the source-shaped
  `nρ^3κ(A)||A||` / `8nκ(A)||A||` products.  They intentionally keep the
  per-stage multiplier bounds, `1 <= nρ^2κ(A)`, and `ρ <= 2` (for Eq.13.23)
  explicit.  Verification passed for direct `BlockLU.lean`, focused BlockLU
  build, quiet executable lookup, scratch-file cleanup, and `#print axioms`
  with only standard Mathlib axioms.

- 2026-06-22: Added matrix-stage-history specializations of the assembled
  Chapter 13 Problem 13.4 Eq.13.22/Eq.13.23 wrappers:
  `higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds` and
  `higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds`.
  These choose `higham13_algorithm13_3_matrixStageHistoryGrowthMatrix` as the
  growth object and discharge the assembled-upper containment using
  `higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_upperFromMatrixStages`.
  Remaining obligations are now the per-stage lower multiplier bounds, the
  lower-diagonal nonvacuity inequality `1 <= nρ^2κ(A)`, and the point-row
  `ρ <= 2` hypothesis for Eq.13.23.  Verification passed for direct
  `BlockLU.lean`, focused BlockLU build, quiet executable lookup,
  scratch-file cleanup, and `#print axioms` with only standard Mathlib axioms.

- 2026-06-22: Closed the Eq.13.22 lower diagonal nonvacuity side condition for
  the Chapter 13 matrix-stage route.  `BlockLU.lean` now has
  `one_le_dim_mul_maxEntryNormRect_mul_of_isRightInverse`, proving
  `1 <= N ||A||_max ||Ainv||_max` from a right inverse by comparing `A*Ainv`
  with the identity, and
  `higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth`, promoting
  this to `1 <= nρ^2κ(A)` when the finite growth object contains the initial
  matrix and `(N : ℝ) <= n`.  Focused BlockLU build, quiet executable lookup,
  scratch-file cleanup, and `#print axioms` passed with only standard Mathlib
  axioms.  Remaining matrix-stage Eq.13.22/Eq.13.23 work is the per-stage lower
  multiplier bounds, plus the source point-row `ρ <= 2` hypothesis for
  Eq.13.23.

- 2026-06-22: Added exact-κ matrix-stage-history wrappers
  `higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds_exact_kappa`
  and
  `higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa`.
  They specialize the assembled Algorithm 13.3 stage-history product bounds to
  `A0 = blockMatrixFlatFin Ablk`, use exact max-entry
  `κ(A) = ||A||_max ||A^{-1}||_max`, and discharge the lower diagonal budget
  with the new right-inverse nonvacuity theorem plus finite history containment
  of the flattened input.  Direct `BlockLU.lean`, focused BlockLU build, quiet
  lookup, scratch-file cleanup, and `#print axioms` passed with only standard
  Mathlib axioms.  The remaining exact-κ matrix-stage obligation is now the
  per-stage lower multiplier bound; Eq.13.23 additionally still needs the
  source point-row `ρ <= 2` hypothesis.

- 2026-06-22: Added
  `higham13_problem13_4_single_block_multiplier_bound_from_local_growth_budget`.
  It views an individual stage multiplier as the lower-left `A21*A11^{-1}`
  product of a local `2 × 2` block partition, applies the existing source
  Problem 13.4 max-entry lower-left bridge, and compares the local `ρ²κ` budget
  with an explicit ambient budget `C`.  Direct BlockLU check, focused BlockLU
  build, quiet lookup, scratch cleanup, and `#print axioms` passed with only
  standard Mathlib axioms.  This closes the multiplier extraction adapter but
  leaves the recursive Schur-condition/stage-budget comparison as the next
  concrete theorem.

- 2026-06-22: Added
  `higham13_algorithm13_3_stage_multiplier_bound_from_local_growth_budget`,
  the Algorithm 13.3 specialization of the single-block multiplier adapter for
  one active pair `j < i`.  It uses the concrete stage blocks `(j,j)`, `(j,i)`,
  `(i,j)`, `(i,i)` and the supplied `pivotInv j`.  Direct BlockLU check,
  focused BlockLU build, quiet lookup, scratch cleanup, and `#print axioms`
  passed with only standard Mathlib axioms.  Next concrete theorem remains the
  uniform recursive/stage-local budget comparison that feeds this adapter for
  every active lower multiplier.

- 2026-06-22: Added `matrix_invOf_eq_of_isRightInverse`, converting
  `IsRightInverse r A P` for a square real matrix into `P = ⅟A`.  Focused
  BlockLU build, quiet lookup, scratch cleanup, and `#print axioms` passed with
  only standard Mathlib axioms.  This removes a bookkeeping side condition in
  the stage multiplier route when exact pivot right-inverse data is available.

- 2026-06-22: Added the Eq.13.23 matrix-stage `rho <= 2` bridge for the
  Chapter 13 matrix-stage route.  `GrowthFactor.lean` now has
  `growthFactorEntry_le_of_maxEntryNorm_le_mul`, and `BlockLU.lean` now has
  `higham13_algorithm13_3_matrixStageBlock_bound_of_active_bound`,
  `higham13_algorithm13_3_matrixStage_blockMaxNorm_bound_of_active_bound`,
  `higham13_algorithm13_3_matrixStageHistoryBound_le_of_stage_bound`,
  `higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_le_of_active_bound`,
  `higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_le_two_of_active_stage_bound`,
  and
  `higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_active_stage_bound`.
  These prove that active-stage max-entry bounds
  `||stage_ij||_max <= 2 ||A||_max` for every active matrix-product Schur-stage
  block imply the formal finite-history `growthFactorEntry <= 2` hypothesis
  needed by the exact-kappa Eq.13.23 wrapper.  Verification passed for direct
  GrowthFactor and BlockLU checks, focused GrowthFactor and BlockLU builds,
  quiet executable lookup, `git diff --check`, touched-file marker scan, and
  `#print axioms` with only standard Mathlib axioms.  Remaining matrix-stage
  work is proving the active-stage max-entry theorem and the per-stage lower
  multiplier budget comparison.

- 2026-06-22: Composed the Eq.13.23 matrix-stage `rho <= 2` bridge with the
  exact-kappa assembled product theorem.  `BlockLU.lean` now has
  `higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_active_stage_bound`,
  which proves the exact-kappa matrix-stage Eq.13.23 product bound from the
  per-stage multiplier budget hypothesis and active-stage max-entry
  `2 ||A||` bounds, without a separate public `rho <= 2` argument.  Direct
  BlockLU check, focused BlockLU build, quiet executable lookup, scratch-file
  cleanup, `git diff --check`, touched-file marker scan, and `#print axioms`
  passed with only standard Mathlib axioms.  Remaining work is still the
  active-stage max-entry proof itself and the per-stage lower multiplier
  budget comparison.

- 2026-06-22: Added the stage-local budget composition layer for the Chapter 13
  Eq.13.23 matrix-stage route.  `BlockLU.lean` now has
  `higham13_algorithm13_3_stageLocalBlockMatrix`,
  `higham13_algorithm13_3_stageLocalFlatMatrix`,
  `higham13_algorithm13_3_stageLocalSchurOfInv`, and
  `higham13_eq13_23_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound`.
  The wrapper applies the existing single-stage Problem 13.4 multiplier
  adapter at every active pair and feeds the resulting lower-factor bounds,
  together with active-stage `rho <= 2`, into the exact-kappa Eq.13.23
  matrix-stage product theorem.  Direct BlockLU check, focused BlockLU build,
  quiet executable lookup, scratch cleanup, `git diff --check`, touched-file
  marker scan, and `#print axioms` passed with only standard Mathlib axioms.
  Remaining work is proving the active-stage max-entry theorem and the
  local-to-global budget comparisons for those active `2 x 2` stage partitions.

- 2026-06-22: Added the Eq.13.22 companion to the Chapter 13 stage-local budget
  composition layer.  `BlockLU.lean` now has
  `higham13_eq13_22_matrix_stage_history_product_from_stage_local_budgets_exact_kappa`,
  which feeds the same active-pair local Problem 13.4 budget data into the
  exact-kappa Eq.13.22 matrix-stage product theorem, without the Eq.13.23
  active-stage `rho <= 2` side condition.  Quiet executable lookup, scratch
  cleanup, `git diff --check`, touched-file marker scan, and `#print axioms`
  passed with only standard Mathlib axioms.  Remaining work is the local-to-global
  budget comparison for active `2 x 2` stage partitions, plus the Eq.13.23
  active-stage max-entry proof and recursive/global factor lift.

- 2026-06-22: Added the canonical stage-local growth layer for the Chapter 13
  matrix-stage Eq.13.22/Eq.13.23 route.  `BlockLU.lean` now has
  `higham13_algorithm13_3_stageLocalSchurOfPivot`,
  `higham13_algorithm13_3_stageLocalSchurOfPivot_eq_stageLocalSchurOfInv`,
  `higham13_algorithm13_3_stageLocalGrowthMatrix`, its initial/Schur containment
  lemmas, and
  `higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa`,
  `higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound`.
  Direct BlockLU check, focused BlockLU build, quiet executable lookup, scratch
  cleanup, `git diff --check`, touched-file marker scan, and `#print axioms`
  passed with only standard Mathlib axioms.  This removes local containment
  hypotheses from the stage-local wrappers; the remaining budget blocker is the
  local-to-global comparison for this canonical local growth matrix.  Important
  guardrail: do not reuse the older pointwise column-BDD active-stage theorem
  for the matrix-product stage route; Lean exposed that bridge as mixing
  pointwise block multiplication with true `Matrix` multiplication.

- 2026-06-22: Added the stage-local growth domination layer for the Chapter 13
  matrix-stage budget route.  `BlockLU.lean` now has
  `higham13_algorithm13_3_stageLocalSchurOfPivot_eq_next_diag`,
  `higham13_algorithm13_3_stageLocalFlatMatrix_le_matrixStageHistoryGrowthMatrix`,
  `higham13_algorithm13_3_stageLocalSchurOfPivot_le_matrixStageHistoryGrowthMatrix`,
  `higham13_algorithm13_3_stageLocalGrowthMatrix_maxEntryNorm`, and
  `higham13_algorithm13_3_stageLocalGrowthMatrix_le_matrixStageHistoryGrowthMatrix`.
  Direct BlockLU check, focused BlockLU build, quiet executable lookup, scratch
  cleanup, `git diff --check`, touched-file marker scan, and `#print axioms`
  passed with only standard Mathlib axioms.  This closes the max-entry
  stage-history containment part of the active-pair local-to-global budget
  comparison.  Remaining budget work is the inverse/condition-number comparison
  between the local `2 x 2` stage flat matrix and the ambient flattened source
  matrix, plus the Eq.13.23 active-stage max-entry theorem and recursive/global
  factor lift.

- 2026-06-22: Added the stage-local inverse-ratio budget adapter for the
  Chapter 13 matrix-stage Eq.13.22/Eq.13.23 route.  `BlockLU.lean` now has
  `growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio`,
  `higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa`,
  and
  `higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound`.
  These derive the per-active-pair local `rho^2 kappa` budget from the already
  proved local-growth domination plus an explicit cross-multiplied inverse-norm
  ratio between the local `2 x 2` stage flat matrix and the ambient flattened
  source matrix.  Direct BlockLU check, focused BlockLU build, executable lookup,
  scratch cleanup, `git diff --check`, touched-file marker scan, and
  `#print axioms` passed with only standard Mathlib axioms.  Remaining work is
  proving that inverse/condition-number ratio, the Eq.13.23 active-stage
  max-entry theorem, and the recursive/global full-factor lift.

- 2026-06-22: Added the first-split lower-left matrix-stage bridge for Chapter
  13 Problem 13.4 / Eq.13.22:
  `higham13_problem13_4_L21_eq13_22_premise_from_matrix_stage_history_first_split_exact_kappa`.
  It instantiates the existing source `growthFactorEntry` lower-left bridge
  with `blockMatrixFirstSplitFlat Ablk` and the matrix-product Algorithm 13.3
  stage-history growth matrix, proving the first-split
  `||A21*A11^{-1}||_max <= n rho^2 kappa(A)` premise from already proved
  initial/stage-tail containment and the first-split Schur flattening equality.
  Verification passed for direct `BlockLU.lean`, focused BlockLU build, quiet
  executable lookup after rebuilding the module cache, scratch-file cleanup,
  and `#print axioms` with only standard Mathlib axioms.

  Two important guardrails were recorded during this pass.  Do not instantiate
  the older abstract active-stage theorem with true `Matrix` blocks to close
  the matrix-product active-stage max-entry row: the elementwise matrix norm
  matches the source max-entry norm but lacks a true matrix-multiplication
  `SeminormedRing`, while the operator-norm matrix ring has the wrong norm for
  the source theorem.  Also, the inverse-ratio hypothesis in the stage-local
  budget adapter is still open; it compares local/global inverse-to-input norm
  ratios and is stronger than a plain local inverse-norm containment.  The next
  concrete target should be the recursive/full-factor lift, likely starting
  from `blockLUOneStep_blockMaxNorm_product_le_of_firstSplit_tail` plus a
  first-row/source-growth containment bridge.

- 2026-06-22: Added the source-facing one-step Eq.13.22 product lift
  `higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa`.
  The theorem uses `pivotInv 0` on the one-step lower factor, with `hpivot`
  tying it to the first block inverse.  It derives the first-split lower-left
  budget from
  `higham13_problem13_4_L21_eq13_22_premise_from_matrix_stage_history_first_split_exact_kappa`,
  derives the first block-row upper budget from matrix-stage initial-history
  containment, and packages these with recursive Schur-tail `L_S`/`U_S`
  hypotheses through `blockLUOneStep_blockMaxNorm_product_le_of_firstSplit_tail`.
  Direct `BlockLU.lean`, focused BlockLU build, quiet executable lookup, and
  `#print axioms` passed with only standard Mathlib axioms.  The next concrete
  Eq.13.22 target is the recursive induction theorem that supplies the tail
  hypotheses at every Schur level and identifies the final recursive factors;
  Eq.13.23 still needs either an analogous one-step point-row specialization or
  composition from the eventual Eq.13.22 recursive theorem plus the `rho <= 2`
  bridge.

- 2026-06-22: Added the source-facing one-step Eq.13.22 witness lift
  `higham13_eq13_22_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa`.
  It combines the one-step product bound with `block_lu_one_step_explicit`:
  from a Schur-tail `BlockLUFactSpec` and the recursive tail norm hypotheses,
  it constructs explicit full one-step `L` and `U` factors, proves
  `BlockLUFactSpec (m+1) r Ablk L U`, and proves the same
  `n*rho^3*kappa(A)*||A||` product bound.  The first-pivot left-inverse
  identity is derived locally from `invOf_mul_self` and `hpivot`, not assumed.
  Direct `BlockLU.lean`, focused BlockLU build, quiet executable lookup, scratch
  cleanup, and `#print axioms` passed with only standard Mathlib axioms.  The
  first axiom-audit attempt used an unqualified name outside the
  `LeanFpAnalysis.FP` namespace; the qualified rerun passed.  Next Eq.13.22
  target remains the recursive induction theorem over Schur tails, now using
  the witness theorem rather than only the product-only theorem.

- 2026-06-22: Added the source-facing one-step Eq.13.23 product and witness
  lifts
  `higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa`
  and
  `higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa`.
  The product theorem composes the one-step Eq.13.22 product bound with the
  source-side `rho <= 2` hypothesis to get the explicit
  `8*n*kappa(A)*||A||` bound for `blockLUOneStepL/U`.  The witness theorem
  combines this product bound with `block_lu_one_step_explicit`, producing
  concrete full one-step factors and a `BlockLUFactSpec` under the same
  Schur-tail factorization and norm hypotheses.  Direct `BlockLU.lean`,
  focused BlockLU build, quiet executable lookup, scratch cleanup, and
  `#print axioms` passed with only standard Mathlib axioms.  This closes the
  one-step Eq.13.23 analogue; the remaining selected-scope work is still the
  recursive induction over Schur tails plus the source proof of final
  `rho <= 2` where Eq.13.23 uses it.

- 2026-06-22: Added the source-facing one-step Eq.13.22 separate-budget and
  separate-budget witness lifts
  `higham13_eq13_22_blockLUOneStep_norms_from_matrix_stage_history_first_split_tail_exact_kappa`
  and
  `higham13_eq13_22_exists_blockLUOneStep_fact_norms_from_matrix_stage_history_first_split_tail_exact_kappa`.
  These preserve the two recursive budgets separately for the explicit
  `blockLUOneStepL/U` factors:
  `||L|| <= n*rho^2*kappa(A)` and `||U|| <= rho*||A||`.  The witness theorem
  combines those bounds with `block_lu_one_step_explicit` and a Schur-tail
  `BlockLUFactSpec`, so it is the intended induction-strength hook for the
  full recursive Eq.13.22 theorem.  Direct `BlockLU.lean`, focused BlockLU
  build, quiet executable lookup, scratch cleanup, and `#print axioms` passed
  with only standard Mathlib axioms.  Next target: a recursive theorem that
  supplies the Schur-tail `BlockLUFactSpec` plus separate tail bounds at every
  level and identifies the final recursive `L`/`U` factors.

- 2026-06-22: Added the one-block base cases for the Problem 13.4 /
  Eq.13.22-Eq.13.23 recursive full-factor route:
  `higham13_eq13_22_exists_blockLUFact_one_norms_from_matrix_stage_history_exact_kappa`,
  `higham13_eq13_22_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa`,
  and
  `higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa`.
  These construct the base factors `L = I`, `U = A`, prove `BlockLUFactSpec`,
  preserve the separate Eq.13.22 lower/upper budgets, and derive the
  Eq.13.22/Eq.13.23 product bounds from the matrix-stage history growth object
  plus the exact right-inverse nonvacuity lemma.  Direct `BlockLU.lean`,
  focused BlockLU build, standalone quiet lookup rerun, scratch cleanup, and
  `#print axioms` passed with only standard Mathlib axioms.  Next target:
  combine this base with
  `higham13_eq13_22_exists_blockLUOneStep_fact_norms_from_matrix_stage_history_first_split_tail_exact_kappa`
  in a recursive theorem over Schur tails.

- 2026-06-22: Added the existential-tail successor wrapper
  `higham13_eq13_22_exists_blockLUFact_succ_norms_from_tail_witness_matrix_stage_history_exact_kappa`.
  It turns an existential strict-Schur-tail `BlockLUFactSpec` with separate
  Eq.13.22 lower/upper budgets into a successor-size full-factor witness by
  applying the separate-budget one-step theorem.  Direct `BlockLU.lean`,
  focused BlockLU build, standalone quiet lookup, scratch cleanup, and
  `#print axioms` passed with only standard Mathlib axioms.  The next target is
  no longer the abstract successor surface; it is the genuinely recursive
  theorem that supplies compatible strict-tail witnesses from the one-block
  base case across all Schur tails.

- 2026-06-23: Added the Eq.13.22 existential-tail product successor wrapper
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa`.
  It packages the Eq.13.22 one-step product witness behind the same existential
  strict-Schur-tail separate-budget witness, yielding the source
  `n*rho^3*kappa(A)*||A||` product bound for successor factors.  Direct
  `BlockLU.lean`, focused BlockLU build, standalone quiet lookup, scratch
  cleanup, and `#print axioms` passed with only standard Mathlib axioms.  The
  remaining Eq.13.22 target is the genuine recursive theorem that supplies
  compatible strict-tail witnesses from the one-block base case.

- 2026-06-23: Added the Eq.13.23 existential-tail successor wrapper
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa`.
  It packages the Eq.13.23 one-step witness behind the same existential
  strict-Schur-tail separate-budget witness used by the Eq.13.22 successor
  theorem, while keeping the source-side `rho <= 2` assumption explicit.
  Direct `BlockLU.lean`, focused BlockLU build, standalone quiet lookup, scratch
  cleanup, and `#print axioms` passed with only standard Mathlib axioms.  The
  remaining recursive/full-factor target is unchanged: supply compatible
  strict-tail witnesses from the one-block base case, and for Eq.13.23 prove
  the source `rho <= 2` premise at the final surface.

- 2026-06-23: Added the Chapter 13 ambient-budget recursive chain
  `Higham13BlockLUBudgetChain`,
  `Higham13BlockLUBudgetChain.exists_blockLUFact_norms`,
  `Higham13BlockLUBudgetChain.lowerBudget_nonneg`, and
  `Higham13BlockLUBudgetChain.exists_blockLUFact_product`.  The chain records
  the base case and successor Schur-step budget obligations under fixed ambient
  lower/upper budgets `C_L` and `C_U`; the norm theorem proves concrete
  `BlockLUFactSpec` factors satisfying those budgets from such a chain, and the
  product theorem packages the `C_L*C_U` product bound without adding a separate
  lower-budget nonnegativity hypothesis.  A follow-up pass added
  `Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product` and
  `Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product`, specializing
  the chain to the displayed Eq.13.22 source budgets and, with `rho <= 2`, the
  Eq.13.23 point-row bound.  Direct `BlockLU.lean`, focused BlockLU build,
  standalone lookup, scratch cleanup, and `#print axioms` passed with only
  standard Mathlib axioms.  This closes the structural recursion, product
  packaging, and source-shaped product wrappers from compatible budgets to
  factors, but does not instantiate the source Eq.13.22/Eq.13.23 budget chain;
  next work is proving the chain from Problem 13.4/growth/condition data and
  adding the final Eq.13.23 `rho <= 2` source surface.

- 2026-06-23: Added assembled Algorithm 13.3 matrix-stage shape and witness
  adapters:
  `higham13_algorithm13_3_upperFromMatrixStages_eq_of_le`,
  `higham13_algorithm13_3_upperFromMatrixStages_lower_zero`,
  `higham13_algorithm13_3_upperFromMatrixStages_first_row`,
  `higham13_algorithm13_3_lowerFromMatrixStages_eq_of_lt`,
  `higham13_algorithm13_3_lowerFromMatrixStages_diag`,
  `higham13_algorithm13_3_lowerFromMatrixStages_upper_zero`,
  `higham13_algorithm13_3_lowerFromMatrixStages_first_column`,
  `higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_product_eq`,
  `higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound`,
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds`,
  plus exact-κ history companions
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa`
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa`.
  The shape lemmas discharge the concrete lower/upper triangular obligations
  and record the first-row/first-column source entries for
  `higham13_algorithm13_3_lowerFromMatrixStages` and
  `higham13_algorithm13_3_upperFromMatrixStages`; the witness adapters add
  `BlockLUFactSpec` to the existing product bounds once the actual assembled
  product equality is supplied.  Direct `BlockLU.lean`, focused BlockLU build,
  quiet lookup, scratch cleanup, and `#print axioms` passed with only standard
  Mathlib axioms.  This does not prove assembled Algorithm 13.3 reconstruction;
  that product equality is now the explicit remaining matrix-stage
  reconstruction obligation, alongside the per-stage multiplier-budget and
  Eq.13.23 `rho <= 2` obligations.

- 2026-06-23: Added the matrix-stage pivot right-inverse bridge for Algorithm
  13.3.  `MatrixAlgebra.lean` now has the generic finite-square theorem
  `isLeftInverse_of_isRightInverse`, and `BlockLU.lean` now has
  `higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse`,
  `higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse`,
  `higham13_algorithm13_3_matrixStages_product_eq_of_pivot_right_inverse`,
  `higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_pivot_right_inverse`,
  the general Eq.13.22/Eq.13.23 pivot-right witness wrappers, and exact-κ
  stage-history pivot-right witness wrappers.  Direct `MatrixAlgebra.lean`,
  focused `MatrixAlgebra` build, direct `BlockLU.lean`, focused BlockLU build,
  quiet lookup, scratch cleanup, and `#print axioms` passed with only standard
  Mathlib axioms.  This removes the orientation mismatch for source pivot
  certificates: exact right-inverse data now feeds both `pivotInv = ⅟pivot` and
  the matrix-stage reconstruction/product witness route.  Remaining source
  obligations are still the per-stage multiplier budgets, the local
  inverse/condition-number comparison, and the Eq.13.23 active-stage
  `rho <= 2` theorem.

- 2026-06-23: Added the converse `⅟` pivot bridge and inverse-ratio witness
  packaging.  `MatrixAlgebra.lean` now has `isRightInverse_of_eq_invOf`, and
  `BlockLU.lean` now has
  `higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_invOf`,
  `higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivotInv_eq_invOf`,
  `higham13_algorithm13_3_matrixStages_product_eq_of_pivotInv_eq_invOf`,
  `higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_pivotInv_eq_invOf`,
  plus the Eq.13.22/Eq.13.23 inverse-ratio witness wrappers
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_pivot_right_inverse`
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound_of_pivot_right_inverse`.
  Direct `MatrixAlgebra.lean`, focused `MatrixAlgebra` build, direct
  `BlockLU.lean`, focused BlockLU build, quiet lookup, scratch cleanup, and
  `#print axioms` passed with only standard Mathlib axioms.  This packages
  existing inverse-ratio product bounds as existential `BlockLUFactSpec`
  witnesses under a pivot-right table and lets `pivotInv = ⅟pivot` data feed
  that table; the inverse-ratio theorem and active-stage proof remain open.

- 2026-06-23: Added the matrix-product active-stage local-Schur bridge for
  Eq.13.23.  `BlockLU.lean` now has
  `higham13_algorithm13_3_matrix_active_stage_bound_of_local_schur_bound` and
  `higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_local_schur_bound`.
  Direct `BlockLU.lean`, focused BlockLU build, quiet lookup, scratch cleanup,
  and `#print axioms` passed with only standard Mathlib axioms.  This avoids
  the rejected normed-ring shortcut for true matrix products by using the
  explicit max-entry stage table: active column dominance plus a local Schur
  max-entry estimate now imply the active-stage `2‖A‖` bound and the
  matrix-stage `rho <= 2` bridge.  The active dominance/local-Schur
  instantiation, inverse-ratio comparison, and per-stage multiplier budgets
  remain open.

- 2026-06-23: Reduced the matrix-product local-Schur estimate itself to an
  explicit product-bound obligation.  `BlockLU.lean` now has
  `maxEntryNorm_sub_le` and
  `higham13_algorithm13_3_matrix_active_local_schur_bound_of_product_bound`.
  Quiet lookup and `#print axioms` passed with only standard Mathlib axioms,
  and `ScratchCh13MatrixLocalSchur.lean` /
  `ScratchCh13MatrixLocalSchurAxioms.lean` were removed.  The Eq.13.23
  `rho <= 2` route now needs active column dominance plus the concrete
  triple-product max-entry bound for true matrix products, rather than an
  opaque local-Schur hypothesis.

- 2026-06-23: Closed the local positive-denominator side condition for the
  matrix-stage inverse-ratio route.  `BlockLU.lean` now has
  `maxEntryNorm_pos_of_invertible`,
  `higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible`, and
  `higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table`.
  The witness wrappers
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_pivot_right_inverse_of_local_invertible`
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound_of_pivot_right_inverse_of_local_invertible`
  expose that reduction at the `BlockLUFactSpec` surface.
  Direct `BlockLU.lean`, focused BlockLU build, quiet lookup, scratch cleanup,
  and `#print axioms` passed with only standard Mathlib axioms after rebuilding
  a stale import cache.  The inverse/condition-number ratio remains the real
  local-to-global budget blocker.

- 2026-06-23: Added the true matrix-product max-entry dimension-factor
  boundary for the Chapter 13 active-stage local-Schur route.  `BlockLU.lean`
  now has `maxEntryNorm_matrix_mul_le_dim`,
  `maxEntryNorm_matrix_mul_mul_le_dim_sq`, and
  `higham13_algorithm13_3_matrix_active_local_schur_bound_with_dim_factor`.
  Direct `BlockLU.lean`, focused BlockLU build, quiet lookup after rebuilding a
  stale import cache, scratch cleanup, and `#print axioms` passed with only
  standard Mathlib axioms.  This proves the exact matrix-product local-Schur
  estimate in the entrywise max norm with the explicit `(r : ℝ)^2` factor; it
  does not close the source-strength `rho <= 2` theorem, which still needs an
  active-column/source-compatible structured local-Schur argument.

- 2026-06-23: Composed the Chapter 13 matrix-product dimension-factor local
  Schur estimate through the active-stage and finite-history growth-factor
  layers.  `BlockLU.lean` now has
  `higham13_algorithm13_3_matrix_active_stage_bound_with_dim_factor` and
  `higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_with_dim_factor`.
  Direct `BlockLU.lean`, focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_dim_comp.err` empty, output contains both names),
  `git diff --check`, touched-file marker scan, scratch cleanup, and
  `#print axioms` passed with only standard Mathlib axioms.  This proves the
  finite-history `rho <= 2` consequence under the strengthened
  `((r : ℝ)^2 * ||pivotInv k||_max) * stageInvDiagBound k k <= 1` pivot budget;
  it still is not the source-strength dimension-free route.

- 2026-06-23: Added
  `higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_with_dim_factor`.
  This composes the dimension-aware `rho <= 2` bridge with the exact-κ
  matrix-stage Eq.13.23 product theorem under the same strengthened
  `(r : ℝ)^2` pivot budget and the existing per-stage lower-multiplier
  hypotheses.  Direct `BlockLU.lean`, focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_dim_product.err` empty, output contains the name),
  `git diff --check`, touched-file marker scan, scratch cleanup, and
  `#print axioms` passed with only standard Mathlib axioms.  Source-strength
  dimension-free active-stage and per-stage multiplier budget obligations remain
  open.

- 2026-06-23: Added the matrix-product diagonal-update composition layer for
  the dimension-aware active-stage route.  `BlockLU.lean` now has
  `higham13_algorithm13_3_matrix_active_column_dominance_of_local_schur_bound`,
  `higham13_algorithm13_3_matrix_active_column_dominance_of_product_bound`,
  `higham13_algorithm13_3_matrix_active_column_dominance_with_dim_factor`,
  `higham13_algorithm13_3_matrix_active_stage_bound_of_local_schur_diag_update`,
  `higham13_algorithm13_3_matrix_active_stage_bound_with_dim_factor_of_diag_update`,
  `higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_with_dim_factor_of_diag_update`,
  and
  `higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_with_dim_factor_of_diag_update`.
  These reduce the raw matrix-stage active-dominance premise to the source
  Theorem 13.7-style `SchurStageActiveDiagLowerUpdate13_7` certificate plus
  the strengthened `((r : ℝ)^2 * ||pivotInv k||_max) * stageInvDiagBound k k <= 1`
  pivot budget, then thread it through active-stage, finite-history `rho <= 2`,
  and exact-κ Eq.13.23 product wrappers.  Direct `BlockLU.lean`, focused
  BlockLU build, quiet lookup (`/tmp/ch13_lookup_diag_update.err` empty and
  output contains the new names), `git diff --check`, touched-file marker scan,
  scratch cleanup, and `#print axioms` passed with only standard Mathlib
  axioms.  The source-strength dimension-free structured product/local-Schur
  proof, the stage-local inverse/condition-number ratio, and per-stage
  multiplier budgets remain open.

- 2026-06-23: Added the source-strength conditional product-bound composition
  layer for the matrix-stage Eq.13.23 route.  `BlockLU.lean` now has
  `higham13_algorithm13_3_matrix_active_stage_bound_of_product_bound_diag_update`,
  `higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update`,
  and
  `higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_product_bound_diag_update`.
  These compose an explicit dimension-free triple-product max-entry hypothesis
  plus the Theorem 13.7-style diagonal lower-update certificate through the
  active-stage, finite-history `rho <= 2`, and exact-κ Eq.13.23 product
  wrappers, without using the `(r : ℝ)^2` generic matrix-product fallback.
  Direct `BlockLU.lean`, focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_product_diag.err` empty and output contains all three
  names), `git diff --check`, touched-file marker scan, scratch cleanup, and
  `#print axioms` passed with only standard Mathlib axioms.  The structured
  source proof of that dimension-free triple-product premise, the
  stage-local inverse/condition-number ratio, and the per-stage multiplier
  budgets remain open.

- 2026-06-23: Added the stage-local inverse-ratio diagonal-update composition
  layer for Eq.13.23.  `BlockLU.lean` now has
  `higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update`,
  `higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_with_dim_factor_of_diag_update`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse`.
  These compose the explicit inverse-ratio route with the source-conditional
  product-bound/diagonal-update active-stage theorem and the dimension-aware
  diagonal-update theorem, then package both as concrete `BlockLUFactSpec`
  witnesses under exact pivot right-inverse data.  Direct `BlockLU.lean`,
  focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_inverse_ratio_diag.err` empty and output contains all four
  names), `git diff --check`, touched-file marker scan, scratch cleanup, and
  `#print axioms` passed with only standard Mathlib axioms.  The
  inverse/condition-number ratio, structured dimension-free triple-product
  estimate, and per-stage multiplier budgets remain open.

- 2026-06-23: Added the stage-local budget witness-packaging pair
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_pivot_right_inverse`
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse`.
  These package the local Problem 13.4 budget product wrappers as concrete
  `BlockLUFactSpec` witnesses under exact pivot right-inverse data; Eq.13.23
  still keeps active-stage `rho <= 2` data explicit.  Direct `BlockLU.lean`,
  focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_stage_local_budget_witness.err` empty and output contains
  both names), `git diff --check`, touched-file marker scan, scratch cleanup,
  and `#print axioms` passed with only standard Mathlib axioms.  The first
  lookup/axiom attempt raced the old compiled module before the focused build;
  reruns passed after rebuild.  The local budget table and Eq.13.23 active-stage
  theorem remain open.

- 2026-06-23: Added local-invertible cleanup variants for the stage-local
  budget witnesses:
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_pivot_right_inverse_of_local_invertible`
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse_of_local_invertible`.
  They derive the local `growthFactorEntry` positive denominator from
  `higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table`, so
  the witness surface no longer needs a separate local positivity table.
  Direct `BlockLU.lean`, focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_stage_local_budget_local_inv.err` empty and output
  contains both names), `git diff --check`, touched-file marker scan, scratch
  cleanup, and `#print axioms` passed with only standard Mathlib axioms.  The
  first lookup/axiom attempt raced the old compiled module before the focused
  build; reruns passed after rebuild.  The local budget inequalities and
  Eq.13.23 active-stage theorem remain open.

- 2026-06-23: Added exact-κ source specializations of the ambient-budget
  recursive chain:
  `Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa`
  and
  `Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa`.
  They package the already-proved chain-to-product route with
  `rho = growthFactorEntry hN A0 G hApos`,
  `kappa(A) = ||A0||_max * ||Ainv||_max`, and
  `normA = ||A0||_max`; Eq.13.23 still requires `rho <= 2`.
  Direct `BlockLU.lean`, focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_budget_chain_exact_kappa.err` empty and output contains
  both names), `git diff --check`, touched-file marker scan, scratch cleanup,
  and `#print axioms` passed with only standard Mathlib axioms.  The source
  chain instantiation from Problem 13.4/growth/condition data remains open.

- 2026-06-23: Added exact-κ constructor instantiations for the
  ambient-budget recursive chain:
  `higham13_eq13_22_blockLUBudgetChain_one_from_matrix_stage_history_exact_kappa`
  and
  `higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa`.
  The first proves the base `Higham13BlockLUBudgetChain` case from the
  matrix-stage source input, and the second proves the first-split successor
  constructor from the source lower-left/first-row matrix-stage history data
  plus a supplied recursive tail chain.  Direct `BlockLU.lean`, focused
  BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_budget_chain_constructors.err` empty and output contains
  both names), `git diff --check`, touched-file marker scan, scratch cleanup,
  and `#print axioms` passed with only standard Mathlib axioms.  The recursive
  tail-chain instantiation from Problem 13.4/growth/condition data, and the
  Eq.13.23 `rho <= 2` source surface, remain open.

- 2026-06-23: Added tail-chain successor product witnesses for the exact-κ
  ambient-budget route:
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_chain_matrix_stage_history_exact_kappa`
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_chain_matrix_stage_history_exact_kappa`.
  These compose the first-split exact-κ chain constructor with the
  chain-to-product packagers to produce concrete `BlockLUFactSpec` witnesses
  from a supplied recursive Schur-tail chain; Eq.13.23 additionally requires
  the full first-split `rho <= 2` hypothesis.  Direct `BlockLU.lean`, focused
  BlockLU build, quiet lookup (`/tmp/ch13_lookup_tail_chain_witness.err`
  empty and output contains both names), `git diff --check`, touched-file
  marker scan, scratch cleanup, and `#print axioms` passed with only standard
  Mathlib axioms.  The recursive tail-chain source proof and Eq.13.23
  source-strength `rho <= 2` theorem remain open.

- 2026-06-23: Added `Higham13BlockLUBudgetChain.mono`, the monotonicity
  theorem for the Chapter 13 ambient-budget recursive chain.  It transports a
  compiled Schur-tail chain from smaller lower/upper budgets to larger ambient
  budgets, which is the structural bridge needed before tail-local Problem
  13.4 budgets can feed the full Eq.13.22/Eq.13.23 constants.  Direct
  `BlockLU.lean` passed immediately after the edit.  Lookup/report/source
  inventory/bottleneck docs were updated.  The remaining source work is still
  proving the recursive tail chain from Problem 13.4/growth/condition scalar
  comparisons and, for Eq.13.23, the source-strength `rho <= 2` theorem.

- 2026-06-23: Added the shifted Schur-tail matrix-stage history comparison
  lemmas
  `higham13_algorithm13_3_matrixStageHistoryBound_tail_le` and
  `higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_tail_le`.  They prove
  that the recursive tail's finite matrix-stage history/growth object is
  max-entry dominated by the full matrix-stage history, closing the
  upper-growth comparison needed when transporting a tail-local recursive
  budget chain to the full ambient source budgets.  Direct `BlockLU.lean`,
  focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_tail_history.err` empty and output contains both names),
  `git diff --check`, touched-file marker scan, scratch cleanup, and
  `#print axioms` passed with only standard Mathlib axioms.  The recursive
  tail-chain construction still needs the source scalar lower/condition
  comparisons and, for Eq.13.23, the source-strength `rho <= 2` theorem.

- 2026-06-23: Added `growthFactorEntry_mul_maxEntryNormRect_eq_maxEntryNorm`
  and
  `higham13_eq13_22_tail_upper_budget_le_full_matrix_stage_history_exact_kappa`.
  The first rewrites the exact source upper budget
  `growthFactorEntry * ||A||_max` as the max-entry norm of the chosen growth
  matrix; the second combines that identity with the shifted Schur-tail
  history comparison to prove the exact upper-budget inequality
  `rho_tail * ||S||_max <= rho_full * ||A||_max` for the recursive tail versus
  the full matrix-stage history.  Direct `BlockLU.lean` passed immediately
  after the edit.  Focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_tail_upper_budget.err` empty and output contains both
  names), `git diff --check`, touched-file marker scan, scratch cleanup, and
  `#print axioms` passed with only standard Mathlib axioms.  The remaining
  recursive-chain work is the source scalar lower/condition comparison and,
  for Eq.13.23, the source-strength `rho <= 2` theorem.

- 2026-06-23: Added
  `higham13_eq13_22_tail_chain_to_full_budget_from_lower_comparison_matrix_stage_history_exact_kappa`.
  It transports a recursive Schur-tail `Higham13BlockLUBudgetChain` proved
  under the tail's exact matrix-stage constants to the full ambient exact-κ
  constants by applying `Higham13BlockLUBudgetChain.mono`; the upper comparison
  is discharged internally by
  `higham13_eq13_22_tail_upper_budget_le_full_matrix_stage_history_exact_kappa`,
  so the theorem exposes only the lower/condition scalar comparison as a
  remaining transport hypothesis.  Direct `BlockLU.lean` passed immediately
  after the edit.  Focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_tail_chain_transport.err` empty and output contains the
  theorem name), `git diff --check`, touched-file marker scan, scratch cleanup,
  and `#print axioms` passed with only standard Mathlib axioms.  The lower/
  condition scalar comparison, recursive tail-chain construction, and Eq.13.23
  source-strength `rho <= 2` theorem remain open.

- 2026-06-23: Added
  `higham13_eq13_22_tail_lower_budget_le_full_from_inverse_ratio_matrix_stage_history_exact_kappa`.
  It composes the shifted Schur-tail matrix-stage history domination with
  `growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio`, proving the
  exact tail-to-full lower-budget comparison from a single cross-multiplied
  inverse-ratio/condition hypothesis.  This narrows the recursive tail-chain
  transport work to proving that source inverse-ratio comparison and building
  the recursive local tail chain; the upper comparison is already closed.
  Direct `BlockLU.lean` passed immediately after moving the theorem below its
  scalar dependency.  Focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_tail_lower_budget.err` empty and output contains the
  theorem name), `git diff --check`, touched-file marker scan, scratch cleanup,
  and `#print axioms` passed with only standard Mathlib axioms.  The remaining
  recursive work is proving the source inverse-ratio comparison, building the
  recursive local tail chain, and, for Eq.13.23, proving the source-strength
  `rho <= 2` theorem.

- 2026-06-23: Added
  `higham13_eq13_22_tail_chain_to_full_budget_from_inverse_ratio_matrix_stage_history_exact_kappa`,
  composing the lower-budget inverse-ratio theorem with
  `higham13_eq13_22_tail_chain_to_full_budget_from_lower_comparison_matrix_stage_history_exact_kappa`.
  A recursive proof can now provide a tail-local budget chain plus the explicit
  inverse-ratio/condition comparison and immediately obtain the same tail chain
  under the full ambient exact-κ budgets; the upper-growth comparison is
  internal.  Direct `BlockLU.lean`, focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_tail_chain_inv_ratio_transport.err` empty and output
  contains the theorem name), `git diff --check`, touched-file marker scan,
  scratch cleanup, and `#print axioms` passed with only standard Mathlib
  axioms.  The remaining recursive work is proving the source inverse-ratio
  comparison, building the recursive local tail chain, and, for Eq.13.23,
  proving the source-strength `rho <= 2` theorem.

- 2026-06-23: Added
  `higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa`.
  This composes the tail-local-to-full budget transport from
  `higham13_eq13_22_tail_chain_to_full_budget_from_inverse_ratio_matrix_stage_history_exact_kappa`
  with
  `higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa`,
  so a recursive tail-local chain plus the explicit source inverse-ratio/
  condition comparison now yields the successor full-budget chain directly.
  Direct `BlockLU.lean`, focused BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_succ_tail_local_inv_ratio.err` empty and output contains
  the theorem name), `git diff --check`, touched-file marker scan, scratch
  cleanup, and `#print axioms` passed with only standard Mathlib axioms.
  The remaining recursive work is proving the source inverse-ratio comparison,
  building the recursive local tail chain, and, for Eq.13.23, proving the
  source-strength `rho <= 2` theorem.

- 2026-06-23: Added
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa`
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa`.
  These compose the tail-local inverse-ratio successor-chain theorem with the
  exact-κ Eq.13.22/Eq.13.23 product packagers, producing concrete
  `BlockLUFactSpec` witnesses from a tail-local recursive chain plus the
  explicit inverse-ratio/condition comparison.  Direct `BlockLU.lean`, focused
  BlockLU build, quiet lookup
  (`/tmp/ch13_lookup_succ_tail_local_product_witnesses.err` empty and output
  contains both theorem names), `git diff --check`, touched-file marker scan,
  scratch cleanup, and `#print axioms` passed with only standard Mathlib
  axioms.  The remaining recursive work is proving the source inverse-ratio
  comparison, building the recursive local tail chain, and, for Eq.13.23,
  proving the source-strength `rho <= 2` theorem.

- 2026-06-23: Added
  `higham13_inverse_ratio_one_sided_containment_counterexample` and
  `higham13_inverse_ratio_not_implied_by_one_sided_containment`.  These are
  audit theorems, not source closures: the scalar values `A = 100`, `S = 1`,
  `Ainv = 1`, and `Sinv = 1` satisfy one-sided norm/inverse-norm containment
  but fail the cross-multiplied inverse-ratio comparison required by the
  recursive Eq.13.22/Eq.13.23 budget transport.  Direct `BlockLU.lean`,
  focused BlockLU build, and lookup passed after refreshing the compiled
  `BlockLU` module.  The inverse-ratio route therefore cannot be closed from
  ordinary local inverse containment; any proof must supply a genuinely
  stronger source comparison, or the work should continue through the
  source block-inverse/per-stage multiplier route.

- 2026-06-23: Added the direct lower-comparison recursive wrappers
  `higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa`,
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa`,
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa`.
  These route a supplied lower-budget comparison through the already-proved
  tail upper-budget comparison, first-split successor constructor, and
  Eq.13.22/Eq.13.23 product packagers.  Verification passed: direct
  `BlockLU.lean`, focused BlockLU build, quiet lookup
  `/tmp/ch13_lookup_lower_comparison.{out,err}`, touched-file marker scan,
  `git diff --check`, scratch cleanup, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.  This does not prove the
  source lower-budget comparison, recursive tail-local chain, or Eq.13.23
  `rho <= 2`; it gives the source block-inverse route a direct landing point
  without reusing the rejected ordinary-containment-to-inverse-ratio shortcut.

- 2026-06-23: Added canonical stage-local growth direct-budget witness wrappers
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_pivot_right_inverse`
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse`.
  They package the existing canonical stage-local growth direct-budget product
  theorems as concrete `BlockLUFactSpec` witnesses under exact pivot
  right-inverse data, without passing through the inverse-ratio specialization.
  Verification passed: direct `BlockLU.lean`, focused BlockLU build, quiet
  lookup `/tmp/ch13_lookup_stage_local_growth_direct_witness.{out,err}`,
  touched-file marker scan, `git diff --check`, scratch cleanup, and
  `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.
  The remaining source obligations are the local-to-global budget table and,
  for Eq.13.23, the active-stage max-entry bound.

- 2026-06-23: Added local-invertible variants for the canonical stage-local
  direct-budget witness route:
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_pivot_right_inverse_of_local_invertible`
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse_of_local_invertible`.
  These derive the local `growthFactorEntry` positive denominator from the
  local full-stage invertibility table before packaging the direct-budget
  canonical-growth product route as concrete `BlockLUFactSpec` witnesses.
  Verification passed: focused BlockLU build, quiet lookup
  `/tmp/ch13_lookup_stage_local_growth_direct_localinv.{out,err}`,
  touched-file marker scan, `git diff --check`, scratch cleanup, and
  `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-23: Added Problem 13.4 lower-budget shortcut audit theorems
  `higham13_stage_local_budget_from_problem13_4_scalar_counterexample` and
  `higham13_stage_local_budget_not_implied_by_problem13_4_bound`.  They show
  that even with equal scalar dimensions, `rhoTail <= rho` and the
  Problem13.4-shaped condition comparison `kappaTail <= rho * kappa` do not
  imply the exact `rho^2 kappa` lower-budget transport needed by the recursive
  Eq.13.22/Eq.13.23 adapters.  Verification passed: direct `BlockLU.lean`,
  focused BlockLU build, refreshed quiet lookup
  `/tmp/ch13_lookup_problem134_budget_shortcut.{out,err}`, touched-file marker
  scan, `git diff --check`, scratch cleanup, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.  This is route-rejection
  evidence only; the source lower-budget comparison/direct budget table remains
  open.

- 2026-06-23: The Chapter 13 Theorem 13.6 proof-source ledger now records a
  bibliographic acquisition checkpoint for the cited Demmel--Higham--Schreiber
  source: likely J. W. Demmel, N. J. Higham, and R. S. Schreiber, "Stability of
  block LU factorization", Numerical Linear Algebra with Applications 2 (1995),
  173--190, doi:10.1002/nla.1680020208.  The breadcrumb came from
  Lindquist--Luszczek--Dongarra, arXiv:2509.07305, which cites this as the
  previous Demmel et al. block-LU perturbation analysis.  This is not a Lean
  closure; `H13-Thm13.6`/`H13-Eq13.16` remain open until that primary proof is
  reconstructed or replaced by local first-order factor/solve estimates.

- 2026-06-23: Added Algorithm 13.3 source-table downstream adapters:
  `higham13_algorithm13_3_diagLowerCert_pivot_bound_of_source_table`,
  `higham13_algorithm13_3_active_column_dominance_of_column_bdd_source_table`,
  `higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_source_table`,
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_source_table`.
  These compose a supplied source inverse-bound table/active reciprocal upper
  bound into the direct pivot-product, active column-dominance/growth, and
  Eq.13.21 assembled-upper column-BDD interfaces.  Verification passed: direct
  `BlockLU.lean`, focused BlockLU build, quiet lookup
  `/tmp/ch13_lookup_source_table_wrappers.{out,err}`, touched-file marker
  scan, `git diff --check`, scratch cleanup, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.  This does not close the
  red Algorithm 13.3 blocker; the source table itself or a direct active
  product bound remains to be proved.

- 2026-06-23: Added the Algorithm 13.3 function-block finite stage-history
  `rho <= 2` bridge:
  `higham13_algorithm13_3_stageBlock_bound_of_active_bound`,
  `higham13_algorithm13_3_stage_blockMaxNorm_bound_of_active_bound`,
  `higham13_algorithm13_3_stageHistoryBound_le_of_stage_bound`,
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_le_of_active_bound`,
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_active_stage_bound`,
  `higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_active_stage_bound`,
  and
  `higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table`.
  These transport a supplied active-stage `2 * blockMaxNorm` bound, including
  the source-table column-BDD route, into `growthFactorEntry <= 2` for the
  finite function-block history object.  Verification passed: direct
  `BlockLU.lean`, focused BlockLU build, quiet lookup
  `/tmp/ch13_lookup_function_stage_history.{out,err}`, scratch cleanup, and
  `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.
  This does not construct the source inverse-bound table or prove the true
  matrix-product dimension-free active-stage theorem.

- 2026-06-23: Added source-table package wrappers
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_column_bdd_source_table`
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table`.
  They expose the Algorithm 13.3 source-table route as a single public surface:
  the same supplied source inverse-bound table gives the Eq.13.21 assembled
  upper-factor bound and the finite function-block `rho <= 2` consequence.
  Verification passed: direct `BlockLU.lean`, focused BlockLU build, quiet
  lookup `/tmp/ch13_lookup_source_table_package.{out,err}`, touched-file marker
  scan, `git diff --check`, scratch cleanup, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.  The source inverse-bound
  table itself and the true matrix-product dimension-free active-stage theorem
  remain open.

- 2026-06-23: Added the exact diagonal-update equality entry point
  `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_diag_eq`.
  It feeds initial-table equality and the displayed active diagonal-update
  recurrence into the paired source-table package, leaving only the active
  reciprocal upper bounds/source table as the analytic obligation.
  Verification passed: direct `BlockLU.lean`, focused BlockLU build, quiet
  lookup `/tmp/ch13_lookup_source_table_diag_eq_package.{out,err}`,
  touched-file marker scan, `git diff --check`, scratch cleanup, and
  `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-23: Added right-inverse/reciprocal finite-history package wrappers
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_column_bdd_pivot_right_inverse_reciprocal`,
  `higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_pivot_right_inverse_reciprocal`,
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_pivot_right_inverse_reciprocal`.
  These carry exact active pivot right-inverse data plus the reciprocal
  diagonal certificate through the Eq.13.21 assembled-upper bound and finite
  function-block `rho <= 2` bridge.  Verification passed: direct
  `BlockLU.lean`, focused BlockLU build, quiet lookup
  `/tmp/ch13_lookup_right_inverse_finite_history_package.{out,err}`,
  touched-file marker scan, `git diff --check`, scratch cleanup, and
  `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.
  The reciprocal diagonal certificate itself remains open.

- 2026-06-23: Added the structured Problem 13.4 inverse-ratio route-rejection
  theorem `higham13_inverse_ratio_principal_tail_counterexample`.  It uses the
  diagonal full matrix `diag(100,1,1)`, its diagonal right inverse, and the
  lower-right principal `2 x 2` tail to show that right-inverse certificates,
  actual principal-tail/full-inverse block identities, and one-sided max-entry
  containments still do not imply the cross-multiplied inverse-ratio comparison
  needed by the recursive Eq.13.22/Eq.13.23 lower-budget transport.  This is
  route-rejection evidence only: the source lower-budget comparison still
  requires a direct source proof or a genuinely stronger inverse/condition
  argument.

- 2026-06-23: Added the direct one-sided-certificate finite-history package
  for Algorithm 13.3:
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_column_bdd_diag_lower`,
  `higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_diag_lower`,
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_diag_lower`.
  These carry a concrete `diagLowerCert` one-sided certificate directly through
  Theorem 13.8's finite function-block history norm bound, the
  `growthFactorEntry <= 2` consequence, and the paired Eq.13.21/finite-history
  wrapper.  Verification passed: direct `BlockLU.lean`, focused BlockLU build,
  public lookup, touched-file marker scan, `git diff --check`, scratch cleanup,
  and `#print axioms` with only `propext`, `Classical.choice`, and
  `Quot.sound`.  The wrapper layer is closed; the red Algorithm 13.3 blocker
  remains the source inverse-bound table/active reciprocal upper bound or an
  equivalent direct concrete pivot certificate.

- 2026-06-23: Added determinant-nonzero exact-κ wrappers for the Problem 13.4
  recursive Eq.13.22/Eq.13.23 route.  New public declarations include
  `higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero`,
  `higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa_of_det_ne_zero`,
  tail-local inverse-ratio/lower-comparison successor-chain `_of_det_ne_zero`
  wrappers, and the Eq.13.22/Eq.13.23 tail-chain and tail-local product-witness
  `_of_det_ne_zero` wrappers.  These derive the `nonsingInv` right-inverse
  certificate from `det A != 0`, keeping the exact constants unchanged while
  removing an auxiliary proof-artifact hypothesis from the source-facing
  surface.  Verification passed: direct `BlockLU.lean`, focused BlockLU build,
  rebuilt public lookup, scratch cleanup, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.  The red Problem 13.4
  blocker remains the recursive tail-chain construction, source lower-budget
  comparison, and final Eq.13.23 `rho <= 2` source proof.

- 2026-06-23: Added the base-case determinant interface for the Problem 13.4
  exact-κ chain: `maxEntryNorm_pos_of_det_ne_zero` and
  `higham13_eq13_22_blockLUBudgetChain_one_from_matrix_stage_history_exact_kappa_of_det_ne_zero`.
  Determinant nonsingularity now supplies both the positive
  `growthFactorEntry` denominator and the `nonsingInv` right-inverse
  certificate for the one-block chain base case.  Verification passed: direct
  `BlockLU.lean`, focused BlockLU build, rebuilt public lookup, scratch cleanup,
  and `#print axioms` with only `propext`, `Classical.choice`, and
  `Quot.sound`.

- 2026-06-23: Added first-split/uniform-flat max-entry norm representation
  bridges for Problem 13.4:
  `blockMaxNorm_le_maxEntryNorm_blockMatrixFirstSplitFlat`,
  `maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMaxNorm`, and
  `maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin`.  These prove
  that the source first-split flattening and the uniform block flattening have
  the same Chapter 13 max-entry norm.  Verification passed: direct
  `BlockLU.lean`, focused BlockLU build, rebuilt public lookup, scratch cleanup,
  and `#print axioms` with only `propext`, `Classical.choice`, and
  `Quot.sound`.  The inverse/nonsingInv transport across this reindexing
  remains separate before a fully uniform recursive-chain data predicate can
  replace the current successor-wrapper surface.

- 2026-06-23: Closed the inverse side of the first-split/uniform-flat
  representation bridge for Problem 13.4.  New declarations
  `blockMatrixFirstSplitToFlatProductEquiv`,
  `blockMatrixFirstSplitToFlatFinEquiv`,
  `blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex`,
  `maxEntryNormRect_nonsingInv_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin`,
  `maxEntryNormRect_kappa_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin`, and
  `maxEntryNormRect_kappa_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin_of_det_ne_zero`
  transport the first-split canonical-inverse norm and exact max-entry
  condition product to the uniform flat representation.  This removes the
  representation mismatch only; the recursive Schur-tail lower-budget/source
  comparison remains open.

- 2026-06-23: Added determinant-nonzero canonical-inverse wrappers for the
  Problem 13.4 canonical stage-local growth direct-budget route:
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse_of_det_ne_zero`.
  These specialize the ambient exact-κ object to `nonsingInv (m*r)
  (blockMatrixFlatFin Ablk)` and derive the full-matrix positive denominator
  and right-inverse certificate from `det(blockMatrixFlatFin Ablk) != 0`.
  The local-to-global stage budget table and Eq.13.23 active-stage bound remain
  open.

- 2026-06-24: Extended the Problem 13.4 first-split/uniform-flat
  representation bridge from max-entry/inverse transport to determinant,
  growth-factor, and complete Eq.13.22 budget transport.  New declarations:
  `det_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin`,
  `det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin`,
  `growthFactorEntry_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin`,
  `higham13_eq13_22_firstSplit_lower_budget_le_flat_matrix_stage_history_exact_kappa`,
  and
  `higham13_eq13_22_firstSplit_upper_budget_eq_flat_matrix_stage_history_exact_kappa`.
  These remove the first-split representation artifact from the exact-κ
  Eq.13.22 lower/upper source-budget surface by transporting it to the uniform
  flat source matrix.  Verification passed: direct `BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet public lookup
  rerun after object refresh, touched Lean-file marker scan, `git diff
  --check`, scratch cleanup, and `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.  Remaining red Problem 13.4 blocker:
  source lower-budget/direct budget comparisons for recursive Schur tails,
  recursive chain instantiation for every tail, and the final Eq.13.23
  `rho <= 2` source proof.

- 2026-06-24: Added
  `higham13_eq13_22_blockLUBudgetChain_succ_from_flat_matrix_stage_history_exact_kappa_of_det_ne_zero`.
  This is the uniform-flat determinant-nonzero exact-κ successor constructor for
  the Problem 13.4 recursive chain: from `det(blockMatrixFlatFin Ablk) != 0`
  and a supplied recursive Schur-tail `Higham13BlockLUBudgetChain` already
  stated under the uniform `blockMatrixFlatFin` Eq.13.22 budgets, it builds the
  successor chain under those same uniform budgets.  The proof uses the
  first-split local lower-left theorem internally and then applies the new
  first-split-to-flat lower-budget bridge, so the first-split representation
  artifact is no longer exposed on this successor surface.  Verification passed:
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused `lake
  build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet public lookup
  `/tmp/ch13_lookup_flat_succ.{out,err}` after the focused build, touched
  Lean-file marker scan, `git diff --check`, scratch cleanup, and `#print
  axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.  The first
  unredirected lookup attempt exited nonzero while/noisily around the rebuild;
  the quiet rerun had empty stderr and found the theorem name.  Remaining red
  Problem 13.4 blocker: prove/instantiate the recursive Schur-tail chain from
  source lower-budget/direct condition data, and separately prove the final
  Eq.13.23 `rho <= 2` source surface.

- 2026-06-24: Added uniform-flat concrete successor product witnesses
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_flat_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero`
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_flat_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero`.
  These compose the uniform-flat determinant successor chain with the exact-κ
  chain-to-product packagers, so a supplied recursive Schur-tail chain under
  the same `blockMatrixFlatFin Ablk` budgets now yields concrete
  `BlockLUFactSpec` witnesses and Eq.13.22/Eq.13.23 product bounds without
  exposing the first-split representation.  Verification passed: direct
  `BlockLU.lean`, focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`,
  quiet public lookup `/tmp/ch13_lookup_flat_product.{out,err}` with empty
  stderr and both new names present, touched Lean-file marker scan, `git diff
  --check`, scratch cleanup, and `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.  Remaining red Problem 13.4 blocker:
  prove/instantiate the recursive Schur-tail chain from source lower-budget or
  direct condition data, prove the source lower-budget comparison itself, and
  prove the final Eq.13.23 `rho <= 2` surface.

- 2026-06-24: Added determinant-nonzero one-block witness wrappers
  `higham13_eq13_22_exists_blockLUFact_one_norms_from_matrix_stage_history_exact_kappa_of_det_ne_zero`,
  `higham13_eq13_22_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_det_ne_zero`,
  and
  `higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_det_ne_zero`.
  These are the concrete `BlockLUFactSpec` companions to the determinant
  base-chain wrapper: `det(blockMatrixFlatFin Ablk) != 0` now supplies both the
  positive `growthFactorEntry` denominator and the canonical `nonsingInv`
  right-inverse certificate for the base separate-budget/product witnesses.
  Verification passed: direct `BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet public lookup
  `/tmp/ch13_lookup_det_base_witness.{out,err}` with empty stderr and all three
  names present, touched Lean-file marker scan, `git diff --check`, scratch
  cleanup, and `#print axioms` with only `propext`, `Classical.choice`, and
  `Quot.sound`.  Remaining red Problem 13.4 blocker: recursive Schur-tail chain
  instantiation, the source lower-budget/condition comparison, and the final
  Eq.13.23 `rho <= 2` source proof.

- 2026-06-24 timeout checkpoint: Added
  `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_det_ne_zero`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` and added its
  `#check` to `examples/LibraryLookup.lean`.  This is the determinant-nonzero
  wrapper for the Algorithm 13.3 column-BDD source-table package: it derives
  the positive `growthFactorEntry` denominator from
  `det(blockMatrixFlatFin A) != 0`, while still leaving the source inverse-bound
  table, diagonal-update data, and active reciprocal upper bounds as explicit
  hypotheses.  Direct `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`
  and focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU` both passed.
  Still pending after resume: quiet public lookup rerun, `#print axioms`, marker
  scan, `git diff --check`, scratch cleanup if an axiom scratch is created, and
  updates to `docs/LIBRARY_LOOKUP.md`, `docs/chapter13/CHAPTER13_BOTTLENECK_LEDGER.md`,
  `docs/chapter13/CHAPTER13_SOURCE_INVENTORY.md`, and
  `docs/chapter13/CHAPTER13_FORMALIZATION_REPORT.md`.

- 2026-06-24 resume verification: Completed the pending audit for
  `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_det_ne_zero`.
  Current-state checks passed: focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet public lookup
  `/tmp/ch13_lookup_bdd_det_source_table.{out,err}` with empty stderr and the
  theorem name present, touched Lean-file marker scan with no matches,
  `git diff --check`, scratch cleanup for
  `ScratchCh13BddDetSourceTableAxioms.lean`, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.  Documentation was updated
  in `docs/LIBRARY_LOOKUP.md`, `docs/chapter13/CHAPTER13_BOTTLENECK_LEDGER.md`,
  `docs/chapter13/CHAPTER13_SOURCE_INVENTORY.md`, and
  `docs/chapter13/CHAPTER13_FORMALIZATION_REPORT.md`.  The wrapper removes the separate
  positive-denominator proof artifact for the source-table package but does not
  construct the source inverse-bound table or active reciprocal upper bounds.

- 2026-06-24: Added and verified
  `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_diag_eq_of_det_ne_zero`.
  This is the exact diagonal-update equality companion to the determinant
  source-table package: it derives the positive `growthFactorEntry`
  denominator from `det(blockMatrixFlatFin A) != 0` while keeping the exact
  update recurrence, source inverse-bound table data, and active reciprocal
  upper bounds explicit.  Verification passed: direct `BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet public lookup
  `/tmp/ch13_lookup_diag_eq_det_source_table.{out,err}` rerun after object
  refresh with empty stderr and the theorem name present, touched Lean-file
  marker scan with no matches, `git diff --check`, scratch cleanup for
  `ScratchCh13DiagEqDetSourceTableAxioms.lean`, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.  Remaining red BDD blocker:
  construct/instantiate the source inverse-bound table or prove the direct
  active pivot-product/certificate bound.

- 2026-06-24: Added and verified the Problem 13.4 uniform-flat lower-comparison
  tail transport and product-witness package
  `higham13_eq13_22_tail_chain_to_flat_budget_from_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero`
  and the combined successor chain wrapper
  `higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero`,
  plus concrete witness wrappers
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero`
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero`.
  These compose the existing direct lower-budget comparison route with the
  first-split/uniform-flat budget bridges, so a tail-local exact-κ recursive
  chain now feeds the uniform `blockMatrixFlatFin` determinant successor without
  exposing first-split budgets, and packages concrete Eq.13.22/Eq.13.23
  `BlockLUFactSpec` witnesses.  Verification passed: direct `BlockLU.lean`,
  focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet public
  lookup `/tmp/ch13_lookup_flat_tail_lower_comparison_products.{out,err}` with empty
  stderr and all four names present, touched Lean-file marker scan with no matches,
  `git diff --check`, scratch cleanup for
  `ScratchCh13FlatTailLowerComparisonProductsAxioms.lean`, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.  Remaining red Problem 13.4
  blocker: prove the direct source lower-budget comparison, instantiate the
  recursive source-tail chain at every Schur tail, and prove the Eq.13.23
  `rho <= 2` source surface.

- 2026-06-24 timeout checkpoint: Added the Problem 13.4 Schur-tail positivity
  cleanup `det_ne_zero_blockMatrixFlatFin_blockSchur_of_first_split_invertible`
  and
  `maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible`,
  plus the four `_of_schur_invertible` flat lower-comparison successor/product
  wrappers.  These derive the positive flattened Schur-tail denominator from
  first-split Schur-complement invertibility, removing the separate `hTailPos`
  proof-artifact premise from the flat lower-comparison route.  Verification
  passed: direct `BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, and quiet public lookup
  `/tmp/ch13_lookup_schur_tail_pos.{out,err}` with empty stderr and all six
  public names present.  The touched Lean/lookup marker scan and
  `git diff --check` passed after the checkpoint docs.  On resume, the scratch
  audit `ScratchCh13SchurTailPosAxioms.lean` was run and removed; `#print axioms`
  for all six declarations reported only `propext`, `Classical.choice`, and
  `Quot.sound`.  Remaining red Problem 13.4 blocker: direct source lower-budget
  comparison, recursive source-tail chain instantiation, and final Eq.13.23
  `rho <= 2` source proof.

- 2026-06-24: Completed the urgent handoff target by adding and strengthening
  the non-flat Schur-tail/full-positivity cleanup wrappers
  `higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible`,
  `higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible`,
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible`,
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible`,
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible`,
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible`.
  Each wrapper derives
  `0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
    (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0)))`
  from
  `maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible hr Ablk pivotInv hpivot`
  and derives the full positive denominator from determinant nonsingularity
  before calling the existing non-flat `_of_det_ne_zero` theorem.  Verification
  passed after strengthening: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`,
  focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_nonflat_schur_tail_pos.{out,err}` with empty stderr and all
  six new public names present, touched Lean/lookup marker scan with no
  matches, scratch cleanup for `ScratchCh13NonflatSchurTailPosAxioms.lean`, and
  `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.
  These wrappers remove the proof-artifact Schur-tail and full positive
  denominator premises from the inverse-ratio and lower-comparison non-flat
  determinant routes, but they do not prove the inverse-ratio comparison,
  direct lower-budget comparison, recursive source-tail chain, or Eq.13.23
  `rho <= 2` source theorem.

- 2026-06-24 source-chain savepoint: Added
  `Higham13Eq1322LowerComparisonSourceChain`,
  `Higham13Eq1322LowerComparisonSourceChain.det_ne_zero`,
  `Higham13Eq1322LowerComparisonSourceChain.to_blockLUBudgetChain`,
  `Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa`,
  and
  `Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa`.
  The inductive certificate records the direct lower-budget route recursively:
  the base carries one-block determinant nonsingularity and the successor
  carries pivot identity, full determinant nonsingularity, dimension bounds,
  the direct lower-budget comparison, and the tail certificate.  The lift
  theorem constructs the ambient `Higham13BlockLUBudgetChain`; the product
  wrappers package concrete Eq.13.22/Eq.13.23 `BlockLUFactSpec` witnesses.
  Verification passed: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_source_chain.{out,err}` with empty stderr and all five new
  public names present, `git diff --check`, touched Lean/lookup marker scan,
  scratch cleanup, and `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.  Current modified files intentionally on disk
  are `.codex/PROJECT_MEMORY.md`,
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`,
  `docs/chapter13/CHAPTER13_BOTTLENECK_LEDGER.md`,
  `docs/chapter13/CHAPTER13_FORMALIZATION_REPORT.md`,
  `docs/chapter13/CHAPTER13_SOURCE_INVENTORY.md`, `docs/LIBRARY_LOOKUP.md`, and
  `examples/LibraryLookup.lean`.  On resume, continue from the remaining
  Problem 13.4 per-tail direct lower-budget comparison and Eq.13.23 `rho <= 2`
  source surfaces rather than adding more chain-packaging wrappers.

- 2026-06-24 docs-health savepoint after source-chain lift: corrected stale
  Chapter 13 status language in `docs/chapter13/CHAPTER13_SOURCE_INVENTORY.md`,
  `docs/chapter13/CHAPTER13_FORMALIZATION_REPORT.md`, `docs/chapter13/CHAPTER13_BOTTLENECK_LEDGER.md`,
  and `docs/LIBRARY_LOOKUP.md`.  The docs now consistently say that
  `Higham13Eq1322LowerComparisonSourceChain` handles the recursive source-tail
  lift from supplied determinant/pivot/dimension/direct-lower-comparison data,
  while the active Problem 13.4 blockers are the per-tail direct
  lower-budget/condition comparison and, for Eq.13.23, the final `rho <= 2`
  theorem.  No new Lean declarations were added in this docs-health pass.

- 2026-06-24 pivot-right-inverse route-rejection savepoint: added
  `higham13_algorithm13_3_pivot_right_inverse_not_imply_diagLowerCert_pivot_bound`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  It proves by a one-block
  scalar witness that exact active pivot right-inverse data alone does not
  imply the concrete `diagLowerCert` pivot product bound required by the
  Algorithm 13.3 column-BDD route; the source inverse-bound table/active
  reciprocal upper bound remains a genuine open obligation.  Verification
  passed: direct `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`,
  focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_pivot_right_counterexample.{out,err}` with empty stderr and
  the new public name present, scratch cleanup, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-24 timeout handoff savepoint: no new Lean declaration was started
  after the pivot-right-inverse route-rejection savepoint.  The intentional
  modified files on disk are `.codex/PROJECT_MEMORY.md`,
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`,
  `docs/chapter13/CHAPTER13_BOTTLENECK_LEDGER.md`,
  `docs/chapter13/CHAPTER13_FORMALIZATION_REPORT.md`,
  `docs/chapter13/CHAPTER13_SOURCE_INVENTORY.md`, `docs/LIBRARY_LOOKUP.md`, and
  `examples/LibraryLookup.lean`.  Resume from the selected-scope red
  bottlenecks: Problem 13.4's per-tail direct lower-budget/condition
  comparison feeding `Higham13Eq1322LowerComparisonSourceChain`, Eq.13.23's
  source `rho <= 2`/active-stage theorem for matrix-product stages, Algorithm
  13.3's source inverse-bound table or reciprocal diagonal certificate for
  Theorems 13.7--13.8/Eq.13.21, and Theorem 13.6's cited Implementation 1
  proof.  The next small Lean step identified but not begun was a matrix
  max-entry route audit showing that generic dimension-free max-entry
  submultiplicativity/triple-product estimates are false in general; this
  should only be route-rejection evidence, not a source theorem closure.

- 2026-06-24 matrix max-entry dimension-free shortcut audit: added
  `maxEntryNorm_matrix_mul_dimension_free_counterexample` and
  `maxEntryNorm_matrix_mul_mul_dimension_free_counterexample` in
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  They use the all-ones
  `2 x 2` matrix to prove that generic dimension-free binary and
  triple-product max-entry estimates are false for ordinary matrix
  multiplication.  This is route-rejection evidence for the matrix-product
  Eq.13.23/`rho <= 2` red row: the remaining source-compatible proof must use
  additional structure and cannot be replaced by a generic max-entry
  submultiplicativity shortcut.  Verification passed: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_maxentry_counterexamples.{out,err}` with empty stderr and
  both new public names present, touched Lean/lookup marker scan, scratch
  cleanup, and `#print axioms` with only `propext`, `Classical.choice`, and
  `Quot.sound`.

- 2026-06-24 Theorem 13.6 exact conditional Eq.13.16 wrapper: added
  `higham13_theorem13_6_eq13_16_from_factor_solve_estimates` in
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  It proves the exact scalar
  pair of Eq.13.16-style factorization/solve inequalities and their max
  aggregation from supplied factor/solve estimates whose constants are bounded
  by a common `d_n`.  This is conditional scalar algebra only; it does not
  prove the omitted Demmel--Higham--Schreiber [326] implementation estimates,
  and `H13-Thm13.6` / `H13-Eq13.16` remain open in the source inventory and
  proof-source ledger.  Verification passed: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_eq1316_conditional.{out,err}` with empty stderr and the
  new public name present, scratch cleanup, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-24 07:13 UTC timeout handoff savepoint: no new Lean declaration was
  started after the Theorem 13.6 conditional Eq.13.16 wrapper.  The
  intentional modified files on disk are `.codex/PROJECT_MEMORY.md`,
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`,
  `docs/chapter13/CHAPTER13_BOTTLENECK_LEDGER.md`,
  `docs/chapter13/CHAPTER13_FORMALIZATION_REPORT.md`,
  `docs/chapter13/CHAPTER13_PROOF_SOURCE_LEDGER.md`,
  `docs/chapter13/CHAPTER13_SOURCE_INVENTORY.md`, `docs/LIBRARY_LOOKUP.md`, and
  `examples/LibraryLookup.lean`.  The last inspected next step was a possible
  inverse-ratio-to-`Higham13Eq1322LowerComparisonSourceChain` connector for
  Problem 13.4; because existing inverse-ratio successor-chain/witness wrappers
  already package that route, resume by adding such a connector only if it
  proves a genuinely new source dependency.  Otherwise continue with the real
  red obligations: per-tail direct lower-budget/condition comparison, Eq.13.23
  source `rho <= 2` for matrix-product stages, Algorithm 13.3's source
  inverse-bound/reciprocal certificate, and Theorem 13.6's cited
  implementation estimates.

- 2026-06-24 07:20 UTC timeout handoff savepoint: no Lean declaration or
  library edit was started after the 07:13 UTC savepoint.  The skill file,
  split-primary contract, chapter index, active bottleneck ledger, source
  inventory, lookup index, and extracted Chapter 13 PDF text were rechecked.
  The key source audit is that Eq.13.22 in the book uses a source-shaped
  recursive lower-block budget with one local growth factor, then enlarges to
  the fixed full ambient `n * rho_n^2 * kappa(A)` budget.  The existing
  `Higham13Eq1322LowerComparisonSourceChain` direct-comparison route remains a
  stronger exact-tail transport, not the scalar consequence of Problem 13.4
  alone.  Resume by avoiding redundant inverse-ratio connector wrappers unless
  they discharge a genuinely new source dependency.  A good next small Lean
  step is the positive scalar bridge
  `s * rhoTail * kappaTail <= n * rho^2 * kappa` from `s <= n`,
  `rhoTail <= rho`, and `kappaTail <= rho * kappa`, paired with the existing
  counterexample that rejects the stronger `rhoTail^2 * kappaTail` transport.
  The remaining red obligations are unchanged: direct Problem 13.4
  lower-budget/condition data, Eq.13.23 source `rho <= 2` for matrix-product
  stages, Algorithm 13.3 source inverse-bound/reciprocal certificate, and the
  cited Theorem 13.6 implementation estimates.

- 2026-06-24 Problem 13.4 source-shaped scalar bridge: added
  `higham13_stage_local_source_lblock_budget_le_of_problem13_4_bound` in
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  It proves the positive
  scalar step matching the book's Eq.13.22 derivation: from `s <= n`,
  `rhoTail <= rho`, nonnegativity, and `kappaTail <= rho * kappa`, the
  one-local-growth lower-block budget `s * rhoTail * kappaTail` is bounded by
  the full ambient `n * rho^2 * kappa` budget.  This is deliberately distinct
  from the already-rejected stronger exact-tail `rhoTail^2 * kappaTail`
  transport, so it is a source-shaped dependency and not a full Problem 13.4
  recursive closure.  Verification passed: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_source_lblock_bridge.{out,err}` with empty stderr and the
  new public name present, `git diff --check`, touched Lean/lookup marker scan,
  scratch cleanup, and `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-24 Problem 13.4 source local lower-block product wrappers: added
  `higham13_algorithm13_3_multiplier_bounds_from_source_lblock_budgets_exact_kappa`,
  `higham13_eq13_22_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa`,
  and
  `higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These compose the
  positive source scalar bridge with the exact-κ matrix-stage product wrappers:
  per-active-pair local lower-block estimates `r * rhoLocal * kappaLocal`,
  together with `rhoLocal <= rhoFull` and
  `kappaLocal <= rhoFull * kappaFull`, now produce the per-stage multiplier
  hypotheses and the Eq.13.22/Eq.13.23 assembled product bounds.  They leave
  the actual local lower-block estimate table, scalar comparison table, and
  Eq.13.23 source `rho <= 2` theorem open.  Verification passed: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_source_lblock_products.{out,err}` with empty stderr and all
  three names present, `git diff --check`, touched Lean/lookup marker scan,
  scratch cleanup, and `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-24 Problem 13.4 source local lower-block witness wrappers: added
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse`
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` and added both names to
  `examples/LibraryLookup.lean`.  These package the source-local lower-block
  product route as concrete `BlockLUFactSpec` witnesses under exact pivot
  right-inverse certificates, removing the black-box per-stage
  multiplier-bound hypothesis from the pivot-right witness surface.  They
  still leave the actual local lower-block estimate table, scalar comparison
  table, and Eq.13.23 source `rho <= 2` theorem open.  Verification passed:
  direct `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`,
  focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_source_lblock_witness.{out,err}` with empty stderr and
  both names present, `git diff --check`, touched Lean/lookup marker scan,
  scratch cleanup, and `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-24 Problem 13.4 determinant/canonical-inverse source local
  lower-block witness wrappers: added
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` and added both names to
  `examples/LibraryLookup.lean`.  These specialize the source-local
  lower-block witness route to the canonical full inverse
  `nonsingInv (m*r) (blockMatrixFlatFin Ablk)`, deriving the full positive
  denominator and right-inverse certificate from
  `det(blockMatrixFlatFin Ablk) != 0`.  They still leave the local
  lower-block estimate table, scalar comparison table, and Eq.13.23 source
  `rho <= 2` theorem open.  Verification passed: scratch compile, direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_source_lblock_det_witness.{out,err}` with empty stderr and
  both names present, `git diff --check`, touched Lean/lookup marker scan,
  scratch cleanup, and `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-24 Problem 13.4 determinant/canonical-inverse source local
  lower-block product wrappers: added
  `higham13_eq13_22_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_det_ne_zero`
  and
  `higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_det_ne_zero`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` and added both names to
  `examples/LibraryLookup.lean`.  These are the product-bound analogues of the
  determinant source-local witness wrappers: they use
  `nonsingInv (m*r) (blockMatrixFlatFin Ablk)` and derive the full positive
  denominator and right-inverse certificate from
  `det(blockMatrixFlatFin Ablk) != 0` before applying the source-local
  lower-block product route.  They still leave the local lower-block estimate
  table, scalar comparison table, and Eq.13.23 source `rho <= 2` theorem open.
  Verification passed: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_source_lblock_det_product.{out,err}` with empty stderr and
  both names present, `git diff --check`, touched Lean/lookup marker scan,
  scratch cleanup, and `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-24 Problem 13.4 source local lower-block from canonical local
  growth: added
  `higham13_problem13_4_single_block_source_lblock_bound_from_local_growth`
  and
  `higham13_algorithm13_3_source_lblock_bound_from_stageLocalGrowth_le`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` and added both names to
  `examples/LibraryLookup.lean`.  The generic theorem keeps the direct
  Problem 13.4 lower-left estimate in the one-growth-factor source shape
  `r * rhoLocal * kappaLocal`; the Algorithm 13.3 specialization proves the
  active multiplier estimate from the canonical stage-local growth matrix plus
  local growth/κ budget domination.  This closes the local lower-block
  estimate side of the source-shaped Eq.13.22/Eq.13.23 wrappers.  Remaining
  source obligations are the local-to-full scalar comparisons and Eq.13.23
  source `rho <= 2`.  Verification passed: scratch compile, direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_source_lblock_local_growth.{out,err}` with empty stderr and
  both names present, `git diff --check`, touched Lean/lookup marker scan,
  scratch cleanup, and `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-24 Problem 13.4 stage-local source scalar-comparison multiplier
  adapter: added
  `higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_source_comparisons_exact_kappa`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` and added it to
  `examples/LibraryLookup.lean`.  The theorem chooses the canonical local
  growth/κ values for every active Algorithm 13.3 matrix-stage pair, applies
  the local lower-block estimate, and uses the source scalar comparison table
  (`rhoLocal <= rhoFull`, `kappaLocal <= rhoFull * kappaFull`) to derive the
  exact per-stage multiplier hypothesis consumed by the assembled
  Eq.13.22/Eq.13.23 product wrappers.  Remaining source obligations are the
  scalar comparison table itself and Eq.13.23 source `rho <= 2`.  Verification
  passed: scratch compile, direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_stage_local_source_comparisons.{out,err}` with empty
  stderr and the name present, scratch cleanup, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-24 Problem 13.4 stage-local source-comparison product/witness
  composition: added
  `higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa`,
  `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa`,
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` and added them to
  `examples/LibraryLookup.lean`.  These wrappers feed the canonical
  stage-local-growth multiplier theorem directly into the Eq.13.22/Eq.13.23
  product and concrete `BlockLUFactSpec` witness surfaces, so the canonical
  source-comparison route no longer exposes the local lower-block estimate as
  a separate hypothesis.  Remaining source obligations are still the
  local-to-full scalar comparison table and Eq.13.23 source `rho <= 2`.

- 2026-06-29 Problem 13.4 stage-local base-comparison multiplier reduction:
  added
  `higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_base_comparisons_exact_kappa`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` and a public lookup entry.
  The theorem reuses
  `higham13_algorithm13_3_stageLocalGrowthFactor_le_matrixStageHistoryGrowthFactor_of_base_le`
  to discharge the raw `rhoLocal <= rhoFull` premise of the source-comparison
  multiplier route from the explicit denominator/base comparison
  `||blockMatrixFlatFin Ablk||_max <= ||stageLocalFlatMatrix i j||_max`.
  This narrows the remaining scalar table: the base comparison and
  `kappaLocal <= rhoFull * kappaFull` remain source obligations, and the
  generic base comparison is still known false by
  `higham13_stage_local_base_comparison_counterexample`.  Verification passed:
  direct `lake env lean -s 65536
  LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_stageLocal_baseComparison_lookup.{out,err}` with empty stderr and
  the name present, `git diff --check`, touched public Lean-file marker scan,
  scratch cleanup, and focused `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-29 Problem 13.4 stage-local base-comparison product/witness routing:
  added
  `higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa`,
  `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa`,
  `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update`,
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivot_right_inverse`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_pivot_right_inverse`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_base_comparisons_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse`.
  These thread the base-comparison multiplier route into the Eq.13.22/Eq.13.23
  product wrappers and concrete `BlockLUFactSpec` witness wrappers.  The
  reduced surface now replaces raw `rhoLocal <= rhoFull` by the explicit
  base-denominator comparison, and the Eq.13.23 diagonal-update variants also
  replace raw `rho <= 2` by active BDD product/update data.  The base
  comparison, condition comparison, and active product/update data remain open
  source obligations, not assumed closures.  Verification passed: direct
  `BlockLU.lean`, focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`,
  quiet lookup `/tmp/ch13_stageLocal_baseProducts_lookup.{out,err}` with empty
  stderr and all six names present, `git diff --check`, touched public
  Lean-file marker scan, scratch cleanup, and focused `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-24 Problem 13.4 stage-local source-comparison determinant cleanup:
  added
  `higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_det_ne_zero`,
  `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_det_ne_zero`,
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` and added them to
  `examples/LibraryLookup.lean`.  These determinant variants specialize the
  canonical source-comparison route to
  `nonsingInv (m*r) (blockMatrixFlatFin Ablk)`, derive the full
  positive-denominator/right-inverse certificates from
  `det(blockMatrixFlatFin Ablk) != 0`, and derive the local stage
  positive-denominator table from the existing local invertibility table.
  Verification used direct Lean, focused Lake build, quiet lookup
  `/tmp/ch13_lookup_stageLocalGrowth_source_det_products.{out,err}`, and
  `#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound`
  appeared.  Remaining source obligations are still the local-to-full scalar
  comparison table and Eq.13.23 source `rho <= 2`.
  Verification passed: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_stageLocalGrowth_source_products.{out,err}` with empty
  stderr and all four names present, `git diff --check`, Lean-only marker
  scan, scratch cleanup, and `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-24 Problem 13.4 stage-local growth-factor comparison: added
  `growthFactorEntry_le_of_growth_le_of_base_le` and
  `higham13_algorithm13_3_stageLocalGrowthFactor_le_matrixStageHistoryGrowthFactor_of_base_le`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, plus lookup entries.  The
  generic scalar lemma proves local `growthFactorEntry <=` global
  `growthFactorEntry` from numerator domination and denominator/base
  domination.  The Algorithm 13.3 specialization uses the already-proved
  canonical local-growth domination to reduce the source `rhoLocal <= rhoFull`
  row to the explicit denominator comparison
  `||blockMatrixFlatFin Ablk||_max <= ||stageLocalFlatMatrix i j||_max`.
  Verification passed: scratch compile, direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_growth_factor_comparison.{out,err}` with empty stderr and
  both names present, scratch cleanup, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-24 Problem 13.4 stage-local denominator/base route rejection: added
  `higham13_stage_local_base_comparison_counterexample` in
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, plus a lookup entry.  The
  theorem gives a `3 × 3` scalar-block example where the active local pair has
  positive local denominator `1` but the flattened global input has max-entry
  norm `100` outside that local `2 × 2` stage partition, so the generic
  comparison `||A||_max <= ||A_local||_max` is false.  Verification passed:
  scratch compile, direct `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`,
  focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_stage_local_base_counterexample.{out,err}` with empty
  stderr and the name present, scratch cleanup, and `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-28 Theorem 13.6 cited-estimate surface: added
  `DemmelHighamSchreiber13_6Estimates` and
  `higham13_theorem13_6_eq13_16_firstOrder_from_DHS_estimates` in
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, plus public lookup entries.
  The new predicate names the [326]-level Implementation 1 factorization/solve
  estimates cited by Higham, and the theorem routes that named conditional
  surface through the existing Eq.13.16 first-order scalar aggregation wrapper.
  This is dependency organization only and does not close `H13-Thm13.6` or
  `H13-Eq13.16`; the implementation proof from Demmel--Higham--Schreiber is
  still open. Verification passed: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_dhs_surface.{out,err}` with empty stderr and both names
  present, `git diff --check`, Lean-only placeholder scan, scratch cleanup, and
  `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.
  Public commit pushed to `origin/main` as `00f37b5` with subject
  `Split 3A: name Ch13 DHS estimate surface`.

- 2026-06-28 Algorithm 13.3 reciprocal source-table determinant surface: added
  `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_reciprocal_of_det_ne_zero`.
  This derives the positive finite-history growth denominator from
  `det(blockMatrixFlatFin A) != 0` for the reciprocal source-table package,
  matching the existing determinant surfaces for the non-reciprocal and
  exact-update reciprocal routes. It removes a proof-artifact premise from the
  book-shaped reciprocal interface but does not construct the source
  inverse-bound table or prove its Eq.13.18 diagonal-update data. Verification
  passed: direct `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`,
  focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_recip_det.{out,err}` with empty stderr and the name
  present, `git diff --check`, Lean-only placeholder scan, scratch cleanup, and
  `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-28 Problem 13.4 canonical stage-local Eq.13.23 composition: added
  `higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update`.
  It composes the canonical stage-local-growth source-comparison product route
  with the matrix-stage product-bound/diagonal-update `rho <= 2` layer, removing
  the raw Eq.13.23 `growthFactorEntry <= 2` premise from that route. The
  local-to-full scalar comparison table and active BDD product/update data
  remain explicit source obligations. Verification passed: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_stage_local_product_update.{out,err}` with empty stderr and
  the name present, `git diff --check`, Lean-only placeholder scan, scratch
  cleanup, and `#print axioms` with only `propext`, `Classical.choice`, and
  `Quot.sound`.

- 2026-06-28 Problem 13.4 canonical stage-local Eq.13.23 witness composition:
  added
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse`
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero_of_product_bound_diag_update`.
  These are the concrete `BlockLUFactSpec` witness counterparts of the
  product-only connector above. They package exact Algorithm 13.3 factors under
  exact pivot right-inverse certificates, remove the raw Eq.13.23
  `growthFactorEntry <= 2` premise by using the product-bound/diagonal-update
  route, and in the determinant variant derive the canonical full inverse and
  full positive denominator from `det(blockMatrixFlatFin Ablk) != 0`.
  Remaining source obligations are still the local-to-full scalar comparison
  table and active BDD product/update data. Verification passed: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet lookup
  `/tmp/ch13_lookup_stage_local_witness_product_update.{out,err}` with empty
  stderr and both names present, `git diff --check`, Lean-only placeholder
  scan, scratch cleanup, and `#print axioms` with only `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-28 Algorithm 13.3 BDD lower-norm Eq.13.18 route: Oracle/GPT-5.5 Pro
  confirmed that the source inverse-bound table should be built first as
  `mu(A_jj^(k)) = min_{||x||=1} ||A_jj^(k)x||`, then rewritten as
  `||pivotInv_k||^{-1}` only after active diagonal nonsingularity is derived.
  Added `SchurStageActiveDiagLowerUpdate13_7.of_unit_min_actions`, which
  derives the active diagonal-update predicate from unit-vector lower-bound /
  minimum data and the Schur perturbation estimate, plus
  `higham13_algorithm13_3_diagLowerCert_diag_lower_of_unit_min_source_table`
  and
  `higham13_algorithm13_3_diagLowerCert_pivot_bound_of_unit_min_source_table`,
  which feed that min-action update and reciprocal active table into the
  concrete `diagLowerCert`/pivot-product route.  This is source Eq.13.18
  dependency progress only: Theorems 13.7--13.8/Eq.13.21 still require the
  lower-norm table construction for actual Schur stages, active reciprocal
  equality from nonsingular pivots, and subordinate-norm perturbation estimates.
  Verification passed: direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, public lookup
  `lake env lean -s 65536 examples/LibraryLookup.lean`, `git diff --check`,
  touched public Lean-file marker scan, scratch cleanup, and focused
  `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-28 Algorithm 13.3 BDD Euclidean right-inverse lower-bound route:
  added `opNorm2_inv_recip_le_vecNorm2_matMulVec_of_isRightInverse` in
  `MatrixAlgebra.lean`, proving that a certified right inverse gives
  `||Minv||_2^{-1} <= ||M x||_2` for every Euclidean unit vector.  Chapter 13
  wrappers `higham13_eq13_18_unit_lower_bound_of_right_inverse_opNorm2` and
  `higham13_eq13_18_active_diag_table_unit_lower_bound_of_right_inverse_opNorm2`
  package the individual-block and active-table forms for Eq.13.18.  This
  closes only the right-inverse/unit-lower-bound half for the concrete 2-norm
  route; the selected BDD row still needs the lower-norm table
  construction/minimum-attainment Schur update, active reciprocal equality for
  actual Schur-stage pivots, and the source arbitrary-subordinate-norm
  perturbation estimates.

- 2026-06-28 Algorithm 13.3 BDD abstract inverse-action lower-bound route:
  added `higham13_eq13_18_unit_lower_bound_of_inverse_action_bound`,
  `higham13_eq13_18_active_diag_table_unit_lower_bound_of_inverse_action_bound`,
  and `SchurStageActiveDiagLowerUpdate13_7.of_inverse_action_bounds` in
  `BlockLU.lean`. These prove the arbitrary normed-space lower-bound half:
  a bounded inverse action plus a left-inverse identity gives
  `normInv^{-1} <= ||diag x||` for every unit vector, and the active wrapper
  feeds it into the Eq.13.18 Schur lower-update predicate. This removes the
  Euclidean-only limitation for that dependency but still does not construct
  the actual lower-norm/source table, active reciprocal equality, or concrete
  subordinate-norm perturbation estimates.

- 2026-06-28 Algorithm 13.3 BDD Euclidean lower-norm table construction:
  added `continuous_vecNorm2`, `continuous_vecNorm2_matMulVec`,
  `isCompact_vecNorm2_unit_sphere`,
  `exists_vecNorm2_matMulVec_unit_minimizer`, `matMulVecLowerNorm2`,
  `matMulVecLowerNorm2_attained`, and `matMulVecLowerNorm2_le` in
  `MatrixAlgebra.lean`. These prove that the finite Euclidean unit sphere is
  compact and that every matrix action attains its lower norm on
  `||x||_2 = 1`. Added the Chapter 13 wrappers
  `higham13_eq13_18_vecNorm2_min_lower_bound` and
  `SchurStageActiveDiagLowerUpdate13_7.of_vecNorm2_stage_lower_norm_matrices`
  in `BlockLU.lean`, which use `matMulVecLowerNorm2` as the active Eq.13.18
  diagonal certificate table for concrete finite 2-norm block actions. This is
  genuine source-table progress for the Euclidean route: minimum attainment and
  lower-norm table construction are now proved locally. The selected BDD row
  remains open because active reciprocal equality for actual Schur-stage pivots
  and the concrete subordinate-norm perturbation estimates are still not
  instantiated, and the source theorem is still stated for an arbitrary
  subordinate norm.

- 2026-06-28 Algorithm 13.3 BDD Euclidean Schur perturbation instantiation:
  added `vecNorm2_matMulVec_triple_le_opNorm2` and
  `vecNorm2_matMulVec_triple_le_opNorm2_of_unit` in `MatrixAlgebra.lean`,
  proving the exact 2-norm subordinate triple-product action estimate.  Added
  `higham13_algorithm13_3_vecNorm2_diag_lower_update` in `BlockLU.lean`, which
  instantiates the Eq.13.18 Euclidean lower-norm diagonal update for the actual
  Algorithm 13.3 matrix-product Schur stages.  This closes the concrete Schur
  action identity and 2-norm perturbation-estimate parts of the Euclidean
  lower-norm route.  The selected BDD row still remains open because active
  reciprocal equality for the stage pivots is not proved, and the printed
  theorem remains arbitrary-subordinate-norm unless a Euclidean specialization
  is explicitly chosen.

- 2026-06-28 Algorithm 13.3 BDD Euclidean active reciprocal instantiation:
  added finite-dimensional 2-norm attainment and reciprocal lower-norm
  infrastructure in `MatrixAlgebra.lean`: `matMulVec_const_mul_right`,
  `matMulVec_of_isRightInverse`, `exists_vecNorm2_matMulVec_unit_maximizer`,
  `opNorm2_le_of_unit_vecNorm2_bound`,
  `opNorm2_eq_vecNorm2_matMulVec_of_unit_maximizer`,
  `exists_vecNorm2_matMulVec_unit_opNorm2_attained`,
  `matMulVecLowerNorm2_le_inv_opNorm2_of_isRightInverse`, and
  `matMulVecLowerNorm2_eq_inv_opNorm2_of_isRightInverse`.  Added
  `higham13_algorithm13_3_vecNorm2_active_pivot_reciprocal_of_right_inverse`
  in `BlockLU.lean`, proving that exact active pivot right-inverse data
  identifies the Algorithm 13.3 Euclidean lower-norm table entry with
  `||pivotInv_k||₂⁻¹`.  Together with
  `higham13_algorithm13_3_vecNorm2_diag_lower_update`, this closes the
  concrete Euclidean lower-norm table/update/active-reciprocal route.  It does
  not close the printed arbitrary-subordinate-norm theorem or the separate
  max-entry Eq.13.21 route without a documented Euclidean specialization or
  additional norm-comparison/source-table work.

- 2026-06-28 Algorithm 13.3 BDD generic lower-norm source-table dependency:
  added the continuous-linear-map lower-norm infrastructure in
  `MatrixAlgebra.lean`: `isCompact_norm_unit_sphere`,
  `exists_continuousLinearMap_unit_minimizer`,
  `continuousLinearMapLowerNorm`,
  `continuousLinearMapLowerNorm_attained`,
  `continuousLinearMapLowerNorm_le`,
  `exists_continuousLinearMap_unit_maximizer`,
  `continuousLinearMap_opNorm_eq_norm_of_unit_maximizer`,
  `exists_continuousLinearMap_unit_opNorm_attained`,
  `continuousLinearMap_opNorm_pos_of_right_inverse`,
  `continuousLinearMapLowerNorm_le_inv_opNorm_of_inverse`,
  `inv_opNorm_le_continuousLinearMapLowerNorm_of_inverse`, and
  `continuousLinearMapLowerNorm_eq_inv_opNorm_of_inverse`.  These prove
  minimum/maximum attainment on the unit sphere in a proper normed real vector
  space and identify a two-sided inverse's reciprocal operator norm with the
  lower norm.  Added the Chapter 13 adapters
  `SchurStageActiveDiagLowerUpdate13_7.of_continuousLinearMap_stage_lower_norms`
  and `SchurStageActivePivotInvReciprocal13_7.of_continuousLinearMap_inverse`
  in `BlockLU.lean`, giving the arbitrary-norm analogue of the Eq.13.18 lower
  table and active reciprocal route.  This closes a source-table dependency
  for the printed BDD theorem, but not the theorem itself: the concrete
  subordinate block action, Schur perturbation estimate, max-entry Eq.13.21
  integration, and BDD nonsingularity/block-LU existence surface remain open.

- 2026-06-28 Algorithm 13.3 BDD generic Schur-composition perturbation
  dependency: added `continuousLinearMap_triple_norm_le` and
  `continuousLinearMap_triple_norm_le_of_unit` in `MatrixAlgebra.lean`, plus
  `SchurStageActiveDiagLowerUpdate13_7.of_continuousLinearMap_schur_composition`
  in `BlockLU.lean`.  The new adapter instantiates the Eq.13.18 generic
  lower-norm table's perturbation hypothesis when the Schur correction is the
  composed continuous-linear block action `A_jk A_kk^{-1} A_kj`, with block
  norms interpreted as Mathlib operator norms.  This removes the standalone
  arbitrary-norm Schur perturbation-estimate gap; the printed BDD row still
  needs the concrete active block actions/inverse certificates to be connected
  to Algorithm 13.3, plus the entrywise max-norm Eq.13.21 route and
  BDD nonsingularity/block-LU existence integration.

- 2026-06-28 Algorithm 13.3 BDD CLM source-table integration bridge:
  added
  `higham13_algorithm13_3_diagLowerCert_diag_lower_of_continuousLinearMap_source_table`
  in `BlockLU.lean`.  It packages the generic continuous-linear lower-norm
  table, Schur-composition update, and two-sided active pivot inverse into the
  existing concrete `diagLowerCert` one-sided pivot certificate, assuming the
  CLM operator norms agree with the Algorithm 13.3 stage norm and pivot-inverse
  norm tables and the initial source lower table dominates the initial
  `invDiagBound`.  This narrows the printed BDD row to constructing/aligning
  the actual active block CLMs and inverse certificates, then composing with
  the existing Eq.13.21 and BDD nonsingularity wrappers.

- 2026-06-28 Algorithm 13.3 BDD matrix-infinity CLM instantiation:
  added `matrixMulVecCLM`, `matrixMulVecCLM_apply`, and
  `matrixMulVecCLM_norm_eq_infNorm` in `MatrixAlgebra.lean`, identifying a
  Mathlib square matrix with its continuous-linear `mulVec` action and
  proving its operator norm is the repository `infNorm`/Mathlib matrix
  infinity operator norm.  Added the generic scalar recurrence
  `higham13_algorithm13_3_diagLowerCertGeneric` and bridges
  `higham13_algorithm13_3_diagLowerCertGeneric_diag_lower_of_source_table_reciprocal`,
  `higham13_algorithm13_3_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table`,
  and
  `higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table`
  in `BlockLU.lean`.  The last theorem instantiates the CLM source-table route
  for the actual Algorithm 13.3 matrix-product Schur stages in matrix
  infinity norm, assuming the initial lower table and exact two-sided active
  pivot inverse identities.  The printed BDD row remains open for deriving
  those table/inverse facts from BDD and integrating the result with the
  entrywise max-norm Eq.13.21 and BDD nonsingularity/block-LU existence
  endpoints.

- 2026-06-28 Algorithm 13.3 BDD matrix-infinity CLM downstream wrappers:
  added
  `higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table`,
  `higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_continuousLinearMap_source_table`,
  and
  `higham13_algorithm13_3_matrix_infNorm_active_stage_bound_of_continuousLinearMap_source_table`
  in `BlockLU.lean`.  These carry the matrix-`∞` CLM source-table hypotheses
  through the direct active pivot-product bound, active column dominance, and
  the Theorem 13.8-style `2 * normMax` active-stage bound for the actual
  Algorithm 13.3 matrix Schur stages.  This is downstream packaging only: the
  initial lower table, exact active pivot inverse identities, entrywise
  max-norm Eq.13.21 transfer, and BDD nonsingularity/block-LU existence
  endpoints remain open.

- 2026-06-29 Algorithm 13.3 BDD matrix-infinity CLM right-inverse wrappers:
  added `matrixMulVecCLM_right_inverse_of_isRightInverse` and
  `matrixMulVecCLM_left_inverse_of_isRightInverse` in `MatrixAlgebra.lean`,
  plus the `_of_pivot_right_inverse` matrix-`∞` CLM source-table wrappers for
  `diagLowerCertGeneric` diagonal-lower, direct pivot-product, active column
  dominance, and active-stage `2 * normMax` bounds in `BlockLU.lean`.  These
  derive the exact CLM action identities from the repository's matrix
  `IsRightInverse` pivot certificates.  The BDD source row still remains open
  for the initial source lower table/source reciprocal data, entrywise
  max-norm Eq.13.21 transfer, and BDD nonsingularity/block-LU existence
  endpoint.

- 2026-06-29 Algorithm 13.3 BDD matrix-infinity initial lower-table wrappers:
  added
  `higham13_algorithm13_3_matrix_infNorm_initial_lower_table_of_diag_right_inverse`,
  `higham13_algorithm13_3_matrix_infNorm_initial_diag_bound_of_diag_right_inverse`,
  and downstream `_of_initial_diag_right_inverse_of_pivot_right_inverse`
  wrappers for `diagLowerCertGeneric` diagonal-lower, active pivot-product,
  active column dominance, and active-stage `2 * normMax` bounds in
  `BlockLU.lean`.  These derive the stage-zero lower-norm table and initial
  diagonal comparison from per-diagonal right-inverse certificates plus
  reciprocal norm bounds.  The BDD source row remains open for deriving those
  reciprocal data and the active-pivot/source bridge from the source BDD
  hypotheses, then connecting the matrix-`∞` surface to Eq.13.21/max-entry and
  block-LU existence endpoints.

- 2026-06-29 Algorithm 13.3 BDD actual CLM source-table wrappers:
  added
  `higham13_algorithm13_3_clm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table`,
  `higham13_algorithm13_3_clm_diagLowerCertGeneric_pivot_bound_of_continuousLinearMap_source_table`,
  `higham13_algorithm13_3_clm_initial_lower_table_of_diag_inverse`,
  `higham13_algorithm13_3_clm_initial_diag_bound_of_diag_inverse`, and the
  downstream `_of_initial_diag_inverse_of_pivot_inverse` wrappers in
  `BlockLU.lean`.  These instantiate the generic continuous-linear source-table
  theorem for the actual Algorithm 13.3 Schur-stage recurrence on CLM blocks,
  deriving the Schur update from
  `higham13_algorithm13_3_schurStageBlock_exact_update`, and build the
  stage-zero lower table plus initial diagonal comparison from two-sided
  diagonal inverse data.  This removes one more abstract-table alignment layer
  for arbitrary subordinate CLM norms; the BDD source row remains open for
  deriving the reciprocal/inverse data from block diagonal dominance and for
  the source-strength max-entry Eq.13.21/`rho <= 2` endpoint.

- 2026-06-29 Algorithm 13.3 BDD actual CLM active-stage wrappers:
  added
  `higham13_algorithm13_3_clm_active_column_dominance_of_continuousLinearMap_source_table`,
  `higham13_algorithm13_3_clm_active_stage_bound_of_continuousLinearMap_source_table`,
  `higham13_algorithm13_3_clm_active_column_dominance_of_initial_diag_inverse_of_pivot_inverse`,
  and
  `higham13_algorithm13_3_clm_active_stage_bound_of_initial_diag_inverse_of_pivot_inverse`
  in `BlockLU.lean`.  These route the actual CLM source-table/pivot-product
  certificate through the Theorem 13.7 active-column and Theorem 13.8
  active-stage `2 * normMax` interfaces, with the initial-inverse variants also
  deriving the stage-zero lower table and initial diagonal comparison from
  two-sided diagonal inverse data.  This is source-facing CLM downstream
  packaging; the printed BDD row remains open for deriving the reciprocal data
  from the BDD hypotheses and for the source-strength entrywise max-norm
  Eq.13.21/`rho <= 2` endpoint.

- 2026-06-29 Algorithm 13.3 BDD matrix-infinity reciprocal-table wrappers:
  added the `_of_reciprocal_diag_right_inverse_of_pivot_right_inverse`
  family in `BlockLU.lean`, including active-stage, `blockInfNorm`,
  finite-history, and dimension-aware max-entry/growth-factor packages.
  These specialize the previous initial-diagonal/right-inverse wrappers to
  the exact table `invDiagBound j = (infNorm (diagInv j))^{-1}`, removing the
  separate `hInvBound` proof artifact.  The endpoint remains the
  matrix-`∞` route with explicit comparison loss `r`, proving
  `growthFactorEntry <= 2*r` rather than the printed dimension-free
  Eq.13.23 `rho <= 2` source row.

- 2026-06-29 Algorithm 13.3 BDD canonical diagonal-inverse wrappers:
  added the `_of_nonsingInv_diag_of_pivot_right_inverse` family in
  `BlockLU.lean`, specializing the matrix-`∞` reciprocal-table route further
  to the repository canonical inverse `nonsingInv r (A j j)` under
  per-diagonal determinant nonzero hypotheses.  These remove the explicit
  `diagInv` object and diagonal right-inverse hypothesis from the active-stage,
  `blockInfNorm`, finite-history, and dimension-aware max-entry/growth-factor
  packages.  The active pivot right-inverse data and the explicit comparison
  loss `r` remain; this still does not close the printed dimension-free
  Eq.13.21/Eq.13.23 source endpoint.

- 2026-06-29 Algorithm 13.3 BDD canonical active-pivot wrappers:
  added `higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv`
  plus the `_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv` matrix-`∞` family
  in `BlockLU.lean`.  These derive the active pivot right-inverse certificates
  from `det(pivot_k) != 0` and `pivotInv k = nonsingInv r pivot_k`, then reuse
  the canonical diagonal route for the active-stage, `blockInfNorm`,
  finite-history, and dimension-aware max-entry/growth-factor packages.  This
  removes an active right-inverse proof artifact, while the active pivot
  determinant/equality table and the `2*r` max-entry transfer loss remain open.

- 2026-06-29 Algorithm 13.3 canonical active-pivot reconstruction wrappers:
  added `higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivotInv_eq_nonsingInv`,
  `higham13_algorithm13_3_matrixStages_product_eq_of_pivotInv_eq_nonsingInv`,
  and
  `higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_pivotInv_eq_nonsingInv`.
  These feed the matrix-stage `BlockLUFactSpec`, product-equality, and
  product-bound witness surfaces from active pivot determinant nonzero plus
  `pivotInv k = nonsingInv r pivot_k`, reusing the existing canonical
  right-inverse theorem.  They are proof-surface cleanup for the witness layer;
  multiplier bounds, upper-factor bounds, source lower-budget comparisons, and
  the Eq.13.23 `rho <= 2` endpoint remain open.

- 2026-06-29 Eq.13.22/Eq.13.23 canonical active-pivot product wrappers:
  added
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivotInv_eq_nonsingInv`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivotInv_eq_nonsingInv`,
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivotInv_eq_nonsingInv`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivotInv_eq_nonsingInv`,
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero`.
  These route the canonical active pivot table through the generic, exact-κ,
  and determinant/full-`nonsingInv` Eq.13.22/Eq.13.23 concrete
  `BlockLUFactSpec` product witnesses.  This removes explicit active
  right-inverse certificates from those witness surfaces; the multiplier-bound
  table, source lower-budget comparisons, and Eq.13.23 `rho <= 2` theorem
  remain open.

- 2026-06-29 Eq.13.22/Eq.13.23 canonical active-pivot source-comparison
  witnesses: added
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv`,
  `higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero`,
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_product_bound_diag_update_of_pivotInv_eq_nonsingInv`,
  and
  `higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivotInv_eq_nonsingInv_of_det_ne_zero_of_product_bound_diag_update`.
  These reuse
  `higham13_algorithm13_3_pivot_right_inverse_of_pivotInv_eq_nonsingInv` to
  remove explicit active pivot right-inverse certificates from the
  stage-local-growth source-comparison `BlockLUFactSpec` witness layer,
  including the full canonical inverse and product-bound/diagonal-update
  Eq.13.23 surfaces.  The active pivot determinant/equality table,
  local-to-full source comparison table, and Eq.13.23 BDD product/update data
  remain open.

- 2026-06-29 Eq.13.22/Eq.13.23 source-chain nonterminal pivot extraction:
  added
  `Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_right_inverse`
  and
  `Higham13Eq1322InverseRatioSourceChain.nonterminal_pivot_right_inverse`.
  These extract exact active pivot right-inverse certificates for genuine
  elimination steps `k < m` in an `(m+1)`-block recursive source chain; the
  one-block base case intentionally carries no `pivotInv 0` condition because
  no further elimination step uses it.  This removes another proof-artifact
  premise for the represented pivots, while final one-block/all-pivot data for
  downstream APIs, per-tail source comparisons, product/update source data, and
  the Eq.13.23 `rho <= 2` theorem remain open.

- 2026-06-29 Eq.13.22/Eq.13.23 source-chain all-pivot wrappers: added
  `Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final` and
  `Higham13Eq1322InverseRatioSourceChain.pivot_right_inverse_of_final`.
  These combine the recursive source-chain nonterminal pivot extractor with a
  single terminal-pivot right-inverse certificate, producing the all-pivot table
  `k < m+1` expected by existing matrix-stage witness APIs.  This isolates the
  final one-block pivot datum instead of repeating the whole active pivot table;
  the per-tail source lower-budget/condition comparisons, structured
  product/update source data, and Eq.13.23 `rho <= 2` theorem remain open.

- 2026-06-29 Eq.13.22/Eq.13.23 source-chain canonical final pivots: added
  `Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final_nonsingInv`
  and
  `Higham13Eq1322InverseRatioSourceChain.pivot_right_inverse_of_final_nonsingInv`.
  These specialize the all-pivot wrappers to the common final-stage source data:
  determinant nonsingularity of the terminal Schur block and
  `pivotInv m = nonsingInv r` of that block.  They derive the terminal
  right-inverse proof with `isInverse_nonsingInv_of_det_ne_zero` and reuse the
  recursive source-chain nonterminal extractor, so downstream APIs can consume a
  canonical final pivot without a caller-built all-pivot certificate.

- 2026-06-30 Eq.13.22/Eq.13.23 source-chain pivot determinant extraction:
  added
  `Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_det_ne_zero`,
  `Higham13Eq1322LowerComparisonSourceChain.pivot_det_ne_zero_of_final`,
  `Higham13Eq1322InverseRatioSourceChain.nonterminal_pivot_det_ne_zero`, and
  `Higham13Eq1322InverseRatioSourceChain.pivot_det_ne_zero_of_final`.
  These convert the existing source-chain pivot right-inverse certificates into
  determinant-nonzero tables for genuine elimination pivots and isolate the
  terminal pivot determinant needed by all-pivot APIs.  They are proof-surface
  cleanup for the Problem 13.4 source-chain route; the per-tail direct
  lower-budget comparison, structured product/update data, and Eq.13.23
  `rho <= 2` theorem remain open.

- 2026-06-30 Eq.13.22/Eq.13.23 pivot right-inverse to determinant bridge:
  added
  `higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse_at`,
  `higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse`,
  `Higham13Eq1322LowerComparisonSourceChain.pivot_det_ne_zero_of_final_right_inverse`,
  and
  `Higham13Eq1322InverseRatioSourceChain.pivot_det_ne_zero_of_final_right_inverse`.
  The general Algorithm 13.3 bridge turns exact active pivot right-inverse
  certificates into determinant nonsingularity, and the source-chain wrappers
  use a single terminal right-inverse certificate to build all-pivot determinant
  tables.  This removes another proof-surface conversion artifact; the same
  three Chapter 13 red rows remain open.

- 2026-06-30 BDD CLM source-table paired endpoint: added
  `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_continuousLinearMap_source_table`
  and
  `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_continuousLinearMap_source_table_of_det_ne_zero`.
  These compose the arbitrary-norm continuous-linear lower-norm source-table
  route with the direct one-sided certificate package, yielding both the
  assembled Eq.13.21 upper-factor bound and finite function-block
  `growthFactorEntry <= 2` once the CLM stage norms, Schur update, and
  two-sided active inverse identities are supplied.  This is BDD integration
  progress, but the printed arbitrary-norm/source-table instantiation and
  downstream source-strength max-entry integration remain open.

- 2026-06-30 Eq.13.22/Eq.13.23 canonical final pivot determinant wrappers:
  added
  `Higham13Eq1322LowerComparisonSourceChain.pivot_det_ne_zero_of_final_nonsingInv`
  and
  `Higham13Eq1322InverseRatioSourceChain.pivot_det_ne_zero_of_final_nonsingInv`.
  These compose the existing canonical final-pivot `nonsingInv`
  right-inverse wrappers with the active pivot determinant bridge, so all-pivot
  determinant APIs can consume source chains whose terminal pivot is stored
  canonically.  This removes a final-pivot determinant proof-surface artifact;
  the per-tail lower comparison, structured BDD product/update theorem, and
  Theorem 13.6 implementation estimates remain open.

- 2026-06-30 Eq.13.22/Eq.13.23 recursive base/inverse source chain: added
  `Higham13Eq1322BaseInverseSourceChain`,
  `Higham13Eq1322BaseInverseSourceChain.det_ne_zero`,
  `Higham13Eq1322BaseInverseSourceChain.to_lowerComparisonSourceChain`,
  `Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa`,
  `Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa`,
  and
  `Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update`.
  The chain packages the stronger route where each nonterminal Schur-tail step
  supplies explicit base and inverse max-entry comparisons, then converts to
  the existing direct lower-comparison source chain.  It is dependency
  packaging only: the base/inverse comparisons, Eq.13.23 BDD product/update
  data, and Theorem 13.6 implementation estimates remain open.

- 2026-06-30 Eq.13.22/Eq.13.23 base/inverse source-chain connector cleanup:
  added `Higham13Eq1322BaseInverseSourceChain.to_inverseRatioSourceChain`,
  `Higham13Eq1322BaseInverseSourceChain.nonterminal_pivot_right_inverse`,
  `Higham13Eq1322BaseInverseSourceChain.nonterminal_pivot_det_ne_zero`,
  `Higham13Eq1322BaseInverseSourceChain.pivot_right_inverse_of_final`,
  `Higham13Eq1322BaseInverseSourceChain.pivot_det_ne_zero_of_final`,
  `Higham13Eq1322BaseInverseSourceChain.pivot_det_ne_zero_of_final_right_inverse`,
  `Higham13Eq1322BaseInverseSourceChain.pivot_right_inverse_of_final_nonsingInv`,
  and
  `Higham13Eq1322BaseInverseSourceChain.pivot_det_ne_zero_of_final_nonsingInv`.
  The conversion theorem factors the explicit base/inverse comparisons through
  the inverse-ratio source-chain API using
  `maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le`; the pivot wrappers
  inherit the nonterminal and final-pivot right-inverse/determinant surfaces
  from the lower-comparison chain.  This removes another all-pivot
  proof-surface artifact for the base/inverse route, but the base/inverse
  comparison theorems, Eq.13.23 BDD product/update data, and Theorem 13.6
  implementation estimates remain open.

- 2026-06-30 Eq.13.22/Eq.13.23 base/inverse budget-chain connector:
  added `Higham13Eq1322BaseInverseSourceChain.to_blockLUBudgetChain` and
  routed the base/inverse Eq.13.22 and Eq.13.23 product witnesses through that
  ambient exact-`kappa` chain.  The theorem composes the stronger base/inverse
  source certificate with the existing lower-comparison chain constructor, so
  callers no longer need to mention the lower-comparison certificate or
  prebuilt ambient budget chain on this route.  This is dependency cleanup for
  Problem 13.4; it still leaves the actual base/inverse comparison theorems,
  structured Eq.13.23 BDD product/update data, and Theorem 13.6 cited
  implementation estimates open.

- 2026-06-30 Eq.13.23 base/inverse product/update connector cleanup:
  refactored
  `Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update`
  so it also consumes
  `Higham13Eq1322BaseInverseSourceChain.to_blockLUBudgetChain` directly and
  invokes
  `higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update`
  for the product/update `rho <= 2` layer.  Direct
  `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` passed before
  and after the edit; focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet public lookup,
  `git diff --check`, touched Lean/lookup marker scans, anchored conflict-marker
  scan, and focused `#print axioms` also passed, with the axiom audit reporting
  only `propext`, `Classical.choice`, and `Quot.sound`.  This removes a
  lower-comparison proof-surface detour only; the base/inverse comparisons,
  source-strength product/update data, and Theorem 13.6 cited estimates remain
  open.

- 2026-06-30 BDD matrix-`∞`/max-entry reverse-comparison audit: added
  `higham13_blockInfNorm_not_le_blockMaxNorm_counterexample` in
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  It exhibits a single
  one-block `2 x 2` matrix with first row `[1,1]` where `blockMaxNorm = 1` and
  `blockInfNorm = 2`, formally ruling out a generic dimension-free comparison
  `blockInfNorm <= blockMaxNorm`.  This is route-rejection evidence for the
  BDD red row and explains why the matrix-`∞` to entrywise max-norm transfer
  keeps an explicit dimension factor; the source-strength Eq.13.21/Eq.13.23
  `rho <= 2` branch, active pivot source table, structured product/update data,
  and Theorem 13.6 implementation estimates remain open.  Direct
  `lake env lean -s 65536 LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`
  passed, as did focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`,
  quiet public lookup with empty stderr and the new name present,
  `git diff --check`, conflict-marker and touched Lean marker scans, and
  focused `#print axioms` with only `propext`, `Classical.choice`, and
  `Quot.sound`.

- 2026-06-30 Problem 13.4 global-growth-tableau route correction: Oracle/GPT-5.5
  Pro advised that the recursive source proof uses one ambient GE growth factor
  `rho_n(A)` for the original matrix, not local normalized `rho(T)` factors for
  Schur tails.  Added
  `higham13_problem13_4_L21_eq13_22_premise_from_ambient_block_inverse_growth`
  and
  `higham13_problem13_4_L21_eq13_22_premise_from_global_growth_tableau_exact_kappa`
  to derive the Eq.13.22 lower-block budget from ambient Schur-tableau
  containment, an explicit current-tail inverse-entry certificate, exact
  max-entry `kappa(A)`, and `rho(A) >= 1`.  The open Ch13 red row is now
  sharper: prove recursive tableau-submatrix containment, prove the current-tail
  inverse-entry certificate from the ambient inverse, and finish Eq.13.23
  `rho <= 2`/BDD product-update data plus Theorem 13.6 estimates.  Verification
  passed before sync: direct `BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, quiet `examples/LibraryLookup.lean`
  with empty stderr and both names present, `git diff --check`, touched
  public-Lean marker scan, anchored conflict-marker scan, and focused
  `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-30 Problem 13.4 source global-growth integration: added
  `higham13_problem13_4_L21_eq13_22_premise_from_source_global_growth_tableau_exact_kappa`,
  the `nonsingInv`/`finSumFinEquiv` source specialization of the ambient
  global-growth-tableau theorem.  The existing first-split matrix-stage lower
  budget theorem now routes through this source wrapper, so the first-pivot
  Eq.13.22 premise no longer depends on a separate inverse-entry artifact; its
  remaining assumptions are the ambient matrix-stage history containments.
  This is dependency progress only: recursive all-tail tableau containment,
  all-tail inverse/source comparison data, Eq.13.23 `rho <= 2`/BDD product
  update, and Theorem 13.6 cited estimates remain open.

- 2026-07-01 Problem 13.4 active-suffix determinant packaging: added
  determinant-nonzero wrappers for the active-suffix first-split Eq.13.22 and
  Eq.13.23 product witnesses, including the Eq.13.23 product-update and
  reciprocal product-update surfaces.  The new wrappers derive the canonical
  ambient `nonsingInv` right-inverse from
  `det(blockMatrixFirstSplitFlat A) != 0`, so callers using the canonical
  active-suffix all-tail source chain no longer expose the raw ambient
  right-inverse premise at that layer.  This is proof-surface cleanup for
  Problem 13.4; the source-strength BDD table construction, all-tail source
  comparison data, and Theorem 13.6 cited estimates remain open.

- 2026-07-01 Algorithm 13.3 matrix-stage Eq.13.21/Eq.13.23 paired
  product/update package: added
  `higham13_algorithm13_3_upperFromMatrixStages_blockMaxNorm_bound_of_active_stage_bound`,
  `higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update`,
  and
  `higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update_reciprocal`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These compose the true
  matrix-product active-stage/product-update route into both the Eq.13.21
  assembled upper-factor bound and the finite matrix-stage `growthFactorEntry
  <= 2` endpoint.  The reciprocal wrapper accepts
  `SchurStageActivePivotInvReciprocal13_7` and derives the raw pivot-product
  table internally.  Verification: direct `BlockLU.lean`, focused BlockLU
  build, public lookup, `git diff --check`, touched placeholder scan, and
  focused `#print axioms` passed; the axiom audit reported only `propext`,
  `Classical.choice`, and `Quot.sound`.  This is dependency-strength progress:
  the structured dimension-free triple-product max-entry estimate,
  diagonal-update/source table data, Problem 13.4 source comparisons, and
  Theorem 13.6 cited estimates remain open.

- 2026-07-01 Problem 13.4 parent inverse-entry handoff: added
  `Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_parent_inverse_entry_exact_kappa`,
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_parent_inverse_entry`,
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_parent_inverse_entry`.
  These use the Problem 13.8 block inverse formula, via
  `higham13_problem13_4_firstSplit_schurTail_inverse_entry_bound_from_block_inverse`,
  to derive the first Schur-tail inverse-entry certificate from the parent
  first-split inverse-entry comparison, then reuse the active-suffix source
  chain to propagate through later tails.  This removes the separate
  first-Schur-tail inverse-entry premise from the Eq.13.22/Eq.13.23
  active-suffix product surfaces while keeping the genuine parent inverse-entry
  source comparison and, for Eq.13.23, the source `rho <= 2` theorem explicit.

- 2026-07-02 Problem 13.4 canonical parent inverse-entry packaging: added
  `higham13_problem13_4_firstSplit_parent_inverse_entry_bound_from_nonsingInv`,
  `Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_canonical_parent_inverse_entry_exact_kappa`,
  `higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_canonical_parent_inverse_entry`,
  and
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_canonical_parent_inverse_entry`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  The helper reuses the
  reindexing bridge from the displayed first-split `Matrix.fromBlocks` inverse
  to the canonical ambient `nonsingInv` of `blockMatrixFirstSplitFlat`; the
  source-chain and product wrappers now derive the parent inverse-entry
  comparison internally under the parent `Matrix.fromBlocks` invertibility
  instance.  This removes another proof-artifact hypothesis from the
  Eq.13.22/Eq.13.23 active-suffix product surfaces.  The all-tail
  parent/source comparison theorem, source-strength BDD table construction, and
  Theorem 13.6 cited implementation estimates remain open.
- 2026-07-02 Problem 13.4 canonical-parent Eq.13.23 product-update packaging:
  added
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_canonical_parent_inverse_entry`,
  `higham13_eq13_23_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_canonical_parent_inverse_entry`,
  and determinant-nonzero companions ending in
  `_of_canonical_parent_inverse_entry_of_det_ne_zero`.
  These compose the existing first-split product/update or reciprocal-table
  `rho <= 2` bridge with the canonical parent inverse-entry handoff, so the
  source-strength Eq.13.23 active-suffix product-update surfaces no longer
  expose a first-Schur-tail inverse-entry comparison; the determinant variants
  also derive the ambient `nonsingInv` right-inverse from `det A != 0`.  This is
  dependency/interface cleanup only: the structured max-entry product estimate,
  source table data, all-tail source comparisons, and Theorem 13.6 cited
  implementation estimates remain open.

- 2026-07-04/05 Algorithm 13.3 matrix-infinity source-norm paired endpoints:
  added seven wrappers in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`
  pairing the assembled matrix-stage upper-factor `blockInfNorm` bound with the
  finite matrix-stage history `blockInfNorm` bound:
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table`,
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_continuousLinearMap_source_table_of_pivot_right_inverse`,
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_initial_diag_right_inverse_of_pivot_right_inverse`,
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_reciprocal_diag_right_inverse_of_pivot_right_inverse`,
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivot_right_inverse`,
  and
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv`;
  the positive-block-size canonical active-pivot wrapper
  `higham13_algorithm13_3_matrix_infNorm_upperFromMatrixStages_and_matrixStageHistoryInfBound_le_of_nonsingInv_diag_of_pivotInv_eq_nonsingInv_of_pos_dim`
  removes the finite unit-sphere witness from that paired source-norm route.
  Direct `lake env lean -s 65536 LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`
  passed before documentation/lookup refresh.  These are source-norm
  dependency packages only; the source-strength entrywise max-entry BDD/product
  update route, Problem 13.4 all-tail source comparisons, and Theorem 13.6
  cited implementation estimates remain open.

- 2026-07-05 Algorithm 13.3 arbitrary-norm active lower table: added
  `higham13_algorithm13_3_source_lowerNorm_table_of_active_schur_pivots` in
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  The theorem names the
  source lower-norm table for the actual continuous-linear Algorithm 13.3 Schur
  stages: `continuousLinearMapLowerNorm` of each active Schur diagonal satisfies
  the Eq.13.18 active diagonal-update predicate, and two-sided active pivot
  inverse identities give the active reciprocal table.  The existing downstream
  CLM diagonal-certificate theorem
  `higham13_algorithm13_3_clm_diagLowerCertGeneric_diag_lower_of_continuousLinearMap_source_table`
  now consumes this named table instead of reconstructing it inline.  Direct
  `lake env lean -s 65536 LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`
  passed after the edit.  This closes the listed lower-norm-table dependency in
  the BDD bottleneck ledger, but not the whole BDD row: deriving active
  reciprocal/pivot data from the printed BDD hypotheses, choosing or connecting
  the source-norm versus entrywise max-norm downstream surface, Problem 13.4
  all-tail source comparisons, and Theorem 13.6 cited implementation estimates
  remain open.

- 2026-07-05 Theorem 13.7 BDD zero-offdiagonal scalar step: added
  `higham13_blockDiagDomCol_offdiag_zero_of_diagBound_nonpos` and
  `higham13_blockDiagDomRow_offdiag_zero_of_diagBound_nonpos` in
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These prove that a
  nonpositive active diagonal lower bound in a nonnegative column/row BDD norm
  table forces all off-diagonal block norms in that column/row to vanish,
  matching the source proof sentence after (13.18).  Direct
  `lake env lean -s 65536 LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`
  passed after the edit; focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `git diff --check`,
  touched Lean placeholder scan, and ignored scratch axiom audit passed.  The
  axiom audit reported only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`.  Redirected public lookup printed both
  new Chapter 13 declarations successfully and failed only on unrelated
  pre-existing non-Ch13 lookup rows.  This closes only the scalar
  zero-off-column/row piece of the Schur-diagonal-singularity contradiction;
  the vector-kernel/flat singularity contradiction, BDD-derived active pivot
  inverses, source-norm versus entrywise max-growth integration, Problem 13.4
  all-tail source comparisons, and Theorem 13.6 cited implementation estimates
  remain open.

- 2026-07-05 Theorem 13.7 BDD flat-kernel singularity step: added
  `blockMatrixFlat_det_ne_zero_of_blockMatrixNonsingular`,
  `higham13_blockMatrixFlat_det_eq_zero_of_offdiag_col_zero_of_diag_kernel`,
  and
  `higham13_not_blockMatrixNonsingular_of_offdiag_col_zero_of_diag_kernel` in
  `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These formalize the source
  proof step after (13.18): if BDD has forced a block column's off-diagonal
  blocks to be zero and the diagonal block has a nonzero right-kernel vector,
  the flattened block matrix has a nonzero kernel vector and determinant zero,
  contradicting `BlockMatrixNonsingular`.  Direct
  `lake env lean -s 65536 LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`,
  focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`,
  `git diff --check`, touched Lean placeholder scan, and ignored scratch axiom
  audit all passed.  The axiom audit reported only standard Mathlib axioms
  `propext`, `Classical.choice`, and `Quot.sound`.  Redirected public lookup
  printed all three new Chapter 13 declarations successfully and still failed
  only on unrelated pre-existing non-Ch13 lookup rows.  This closes the
  vector-kernel/flat-singularity piece of the Schur-diagonal-singularity
  contradiction, but not the full BDD block-LU existence route: diagonal-block
  kernel extraction from lower-bound zero, the leading-prefix contradiction
  assembly, active pivot inverses, source-norm versus entrywise max-growth
  integration, Problem 13.4 all-tail source comparisons, and Theorem 13.6 cited
  estimates remain open.

- 2026-07-05 Theorem 13.7 BDD diagonal-singularity contradiction step: added
  `higham13_exists_nonzero_coord_of_vec_ne_zero`,
  `higham13_exists_diag_kernel_coord_of_det_eq_zero`,
  `higham13_blockMatrixFlat_det_eq_zero_of_offdiag_col_zero_of_diag_det_eq_zero`,
  and
  `higham13_not_blockMatrixNonsingular_of_offdiag_col_zero_of_diag_det_eq_zero`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These bridge the previous
  flat-kernel lemma to the source's singular-active-diagonal-block case:
  determinant zero of the active diagonal block yields a nonzero right-kernel
  vector with a named nonzero coordinate, and zero off-diagonal blocks in that
  column then make the whole flattened block matrix singular, contradicting
  `BlockMatrixNonsingular`.  Direct
  `lake env lean -s 65536 LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`
  passed after the edit; focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `git diff --check`,
  touched Lean placeholder scan, and ignored scratch axiom audit passed.  The
  axiom audit reported only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`.  Redirected public lookup printed all
  four new Chapter 13 declarations successfully and still failed only on
  unrelated pre-existing non-Ch13 lookup rows.  This closes the diagonal-block
  singularity-to-flat contradiction dependency, but not the full BDD block-LU
  existence route: deriving active diagonal-block determinant nonzero/pivot
  inverses from the BDD lower-bound alternatives and leading-prefix
  nonsingularity, source-norm versus entrywise max-growth integration, Problem
  13.4 all-tail source comparisons, and Theorem 13.6 cited estimates remain
  open.

- 2026-07-05 Theorem 13.7 BDD actual-block contradiction step: added
  `higham13_block_entries_zero_of_norm_eq_zero`,
  `higham13_blockDiagDomCol_offdiag_entries_zero_of_norm_table_nonpos`,
  `higham13_not_blockMatrixNonsingular_of_blockDiagDomCol_diagBound_nonpos_diag_det_eq_zero`,
  and
  `higham13_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These connect the
  abstract nonnegative BDD norm-table step to the actual block matrix table
  `fun i j => ‖A i j‖`: a nonpositive active diagonal lower bound gives
  zero scalar entries in all off-diagonal blocks of that column, and together
  with determinant zero of the active diagonal block contradicts
  `BlockMatrixNonsingular`.  Direct
  `lake env lean -s 65536 LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`
  passed after the edit; focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `git diff --check`,
  touched Lean placeholder scan, and ignored scratch axiom audit passed.  The
  axiom audit reported only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`.  Redirected public lookup printed all
  four new Chapter 13 declarations successfully and still failed only on
  unrelated pre-existing non-Ch13 lookup rows.  This closes the actual-block
  column-BDD nonpositive-bound/singular-diagonal contradiction dependency, but
  not the full BDD block-LU existence route: deriving positive active diagonal
  determinant/pivot inverse data for all leading prefixes, source-norm versus
  entrywise max-growth integration, Problem 13.4 all-tail source comparisons,
  and Theorem 13.6 cited estimates remain open.

- 2026-07-05 Theorem 13.7 BDD leading-prefix diagonal step: added
  `higham13_leadingBlockPrefix_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos`
  and
  `higham13_leadingBlockPrefix_diag_det_ne_zero_of_leadingPrincipalBlockNonsingular13_2_blockDiagDomCol_diagBound_nonpos`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These combine full
  column BDD inheritance for leading prefixes with the actual-block
  nonsingularity contradiction: a nonsingular leading prefix cannot have a
  singular active diagonal block at any prefix index whose inherited diagonal
  lower bound is nonpositive.  Direct
  `lake env lean -s 65536 LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`
  passed after the edit; focused
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `git diff --check`,
  touched Lean placeholder scan, and ignored scratch axiom audit passed.  The
  axiom audit reported only standard Mathlib axioms `propext`,
  `Classical.choice`, and `Quot.sound`.  Redirected public lookup printed both
  new Chapter 13 declarations successfully and still failed only on unrelated
  pre-existing non-Ch13 lookup rows.  This closes the leading-prefix packaging
  for the nonpositive-bound/singular-diagonal contradiction, but not the final
  BDD block-LU existence route: deriving the positive active
  lower-bound/pivot inverse table for all pivots, source-norm versus entrywise
  max-growth integration, Problem 13.4 all-tail source comparisons, and Theorem
  13.6 cited estimates remain open.

- 2026-07-05 Theorem 13.7 BDD leading-prefix canonical inverse step: added
  `higham13_leadingBlockPrefix_diag_nonsingInv_isInverse_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos`
  and
  `higham13_leadingBlockPrefix_diag_nonsingInv_isInverse_of_leadingPrincipalBlockNonsingular13_2_blockDiagDomCol_diagBound_nonpos`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These wrap the
  leading-prefix determinant-nonzero facts with
  `isInverse_nonsingInv_of_det_ne_zero`, exposing the repository canonical
  `nonsingInv` as a two-sided inverse for every prefix diagonal block whose
  inherited column-BDD lower bound is nonpositive.  Focused
  `lake env lean -s 65536 LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean` and
  `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU` passed; `git diff --check`,
  touched Lean placeholder scan, and the extended ignored scratch
  axiom audit passed.  The new wrappers' axiom audit reports only standard
  Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.  Redirected
  public lookup printed both new Chapter 13 declarations successfully and still
  failed only on unrelated pre-existing non-Ch13 lookup rows.  This closes the
  canonical inverse packaging needed by downstream active-pivot APIs, but not
  the final BDD block-LU existence route: deriving the positive active
  lower-bound/pivot inverse table for all pivots, source-norm versus entrywise
  max-growth integration, Problem 13.4 all-tail source comparisons, and Theorem
  13.6 cited estimates remain open.

- 2026-07-05 Theorem 13.7 BDD all-prefix diagonal inverse table: added
  `higham13_diag_nonsingInv_isInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos`
  and
  `higham13_diag_nonsingInv_isRightInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These specialize the
  leading-prefix canonical inverse theorem to an all-leading-prefix
  nonsingularity table, yielding canonical two-sided and right-inverse
  certificates for every original diagonal block whose column-BDD lower-bound
  entry is nonpositive.  This is dependency packaging for downstream
  diagonal/pivot certificate APIs; it does not close the active Schur-stage
  BDD theorem, because deriving all active pivot certificates from the printed
  BDD hypotheses and connecting them to the source max-growth/product-update
  route remains open.

- 2026-07-05 Theorem 13.7 BDD initial active-pivot bridge: added
  `higham13_algorithm13_3_initial_pivot_nonsingInv_isInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos`,
  `higham13_algorithm13_3_initial_pivot_nonsingInv_isRightInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos`,
  `higham13_algorithm13_3_initial_pivot_det_ne_zero_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos`,
  and
  `higham13_algorithm13_3_initial_pivot_right_inverse_of_pivotInv_eq_nonsingInv_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These specialize the
  BDD all-prefix diagonal inverse table to Algorithm 13.3 stage zero, where
  the active pivot is definitionally the original first diagonal block.  The
  determinant wrapper gives first-pivot nonsingularity directly from the
  canonical BDD inverse, and the equality wrapper turns
  `pivotInv 0 = nonsingInv r (A 0 0)` into the exact first active pivot
  right-inverse certificate consumed by matrix-stage APIs.  This closes only
  the base-pivot bridge; deriving later active Schur-stage pivot certificates
  from the printed BDD hypotheses remains open.

- 2026-07-06 Theorem 13.7 BDD first Schur-tail nonsingularity handoff: added
  `higham13_algorithm13_3_first_schur_tail_blockMatrixNonsingular_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos`
  and
  `higham13_algorithm13_3_first_schur_tail_blockMatrixFlat_det_ne_zero_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These compose the
  BDD all-prefix canonical first-pivot inverse with the existing
  Schur-complement nonsingularity theorem: full leading-prefix nonsingularity
  gives nonsingularity of the original full block matrix, and the BDD-derived
  canonical first pivot supplies the two-sided inverse needed to prove
  `blockSchur A (pivotInv 0)` block-nonsingular.  The determinant corollary
  exposes the product-index flattened determinant certificate.  This closes
  the first recursive nonsingularity handoff after the base pivot bridge, but
  not the later active Schur-stage BDD reciprocal/source table, entrywise
  max-growth product/update route, Problem 13.4 all-tail comparisons, or
  Theorem 13.6 cited implementation estimates.  Direct
  `lake env lean -s 65536 LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`,
  focused `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`,
  `git diff --check`, touched Lean marker scan, scratch proof bench, and
  scratch axiom audit passed; the axiom audit reported only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`.  Redirected public
  lookup printed both new Chapter 13 declarations and still failed only on
  unrelated pre-existing stale lookup rows.

- 2026-07-06 Theorem 13.7 BDD first Schur-tail leading-prefix handoff: added
  `higham13_algorithm13_3_first_schur_tail_leadingPrincipalBlockNonsingular_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  This strengthens the
  first Schur-tail nonsingularity bridge by transferring the full
  `LeadingPrincipalBlockNonsingular13_2` condition to
  `blockSchur A (pivotInv 0)` from the all-leading-prefix table and the
  BDD-derived canonical first pivot inverse.  It is the recursive
  leading-prefix handoff needed before later BDD/source-table work can iterate
  on Schur tails.  Later active Schur-stage reciprocal/source-table data,
  entrywise max-growth product/update routing, Problem 13.4 all-tail
  comparisons, and Theorem 13.6 cited implementation estimates remain open.
  Direct `lake env lean -s 65536
  LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `git diff --check`, touched Lean
  marker scan, scratch proof bench, and scratch axiom audit passed; the axiom
  audit reported only standard Mathlib axioms `propext`, `Classical.choice`,
  and `Quot.sound`.  Redirected public lookup printed the full first-tail
  theorem family and still failed only on unrelated pre-existing stale lookup
  rows.

- 2026-07-06 Theorem 13.7 BDD first Schur-tail all-prefix table:
  added
  `higham13_algorithm13_3_first_schur_tail_all_leadingBlockPrefixes_nonsingular_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  This packages the
  preceding full-tail nonsingularity and leading-principal handoffs for
  `blockSchur A (pivotInv 0)` into the all-leading-prefix table shape
  consumed by the BDD all-prefix diagonal-inverse theorem.  It is a small but
  important recursive dependency: after the first canonical BDD pivot, the
  first Schur tail now has the exact prefix-nonsingularity hypothesis format
  needed by later tail-level diagonal inverse/pivot-certificate steps.  It
  still does not construct the later active Schur-stage reciprocal/source
  table, entrywise max-growth product/update route, Problem 13.4 all-tail
  comparisons, or Theorem 13.6 cited implementation estimates.  Direct
  `lake env lean -s 65536
  LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `git diff --check`, touched Lean
  marker scan, scratch proof bench, and scratch axiom audit passed.  The axiom
  audit reported only standard Mathlib axioms `propext`, `Classical.choice`,
  and `Quot.sound`.  Redirected public lookup printed the four first-tail
  declarations including the new all-prefix table, with empty stderr; it still
  failed only on unrelated pre-existing stale lookup rows later in
  `examples/LibraryLookup.lean`.

- 2026-07-06 Theorem 13.7 BDD first Schur-tail diagonal inverse handoff:
  added
  `higham13_algorithm13_3_first_schur_tail_diag_nonsingInv_isInverse_of_tail_blockDiagDomCol_diagBound_nonpos`,
  `higham13_algorithm13_3_first_schur_tail_diag_nonsingInv_isRightInverse_of_tail_blockDiagDomCol_diagBound_nonpos`,
  and
  `higham13_algorithm13_3_first_schur_tail_diag_det_ne_zero_of_tail_blockDiagDomCol_diagBound_nonpos`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These apply the
  first-Schur-tail all-prefix handoff to the existing BDD all-prefix
  diagonal-inverse theorem: if the first Schur tail has its own column-BDD
  lower-bound table with nonpositive bounds, then every tail diagonal block
  has the canonical `nonsingInv` two-sided/right-inverse certificates and a
  nonzero determinant certificate.  This is recursive pivot-certificate
  packaging only; it does not prove the tail BDD/source reciprocal table,
  entrywise max-growth product/update route, Problem 13.4 all-tail
  comparisons, or Theorem 13.6 cited implementation estimates.  Verification
  passed: direct `lake env lean -s 65536
  LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `git diff --check`, touched Lean
  marker scan, scratch prototype, expanded scratch axiom audit, and redirected
  public lookup presence.  The axiom audit reported only standard Mathlib
  axioms `propext`, `Classical.choice`, and `Quot.sound`; lookup stderr was
  empty and the later nonzero exit was still from unrelated stale
  non-Chapter-13 lookup rows.

- 2026-07-07 Theorem 13.7 BDD stage-1 active-pivot bridge: added
  `higham13_algorithm13_3_stage1_pivot_eq_first_schur_tail_diag`,
  `higham13_algorithm13_3_stage1_pivot_nonsingInv_isInverse_of_first_schur_tail_blockDiagDomCol_diagBound_nonpos`,
  `higham13_algorithm13_3_stage1_pivot_right_inverse_of_pivotInv_eq_nonsingInv_first_schur_tail_blockDiagDomCol_diagBound_nonpos`,
  and
  `higham13_algorithm13_3_stage1_pivot_det_ne_zero_of_first_schur_tail_blockDiagDomCol_diagBound_nonpos`
  in `LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`.  These identify the
  original Algorithm 13.3 stage-1 active pivot with the first diagonal block
  of `blockSchur A (pivotInv 0)` and transport the first Schur-tail BDD
  diagonal inverse handoff back to the original stage-indexed pivot surface.
  The right-inverse wrapper accepts
  `pivotInv 1 = nonsingInv r ((blockSchur A (pivotInv 0)) 0 0)`, giving the
  exact stage-1 pivot certificate consumed by downstream matrix-stage APIs.
  This closes a stage-index bridge only; the source-strength tail BDD/source
  reciprocal table, entrywise max-growth product/update data, Problem 13.4
  all-tail comparisons, and Theorem 13.6 cited implementation estimates
  remain open.  Verification passed: focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, focused `lake build
  LeanFpAnalysis.FP.Algorithms.LU.BlockLU:olean`, `git diff --check`, touched
  Lean marker scan, scratch prototype, expanded scratch axiom audit, and
  redirected public lookup presence.  The axiom audit reported only standard
  Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`; lookup
  stderr was empty and the later nonzero exit was still from unrelated stale
  non-Chapter-13 lookup rows.
