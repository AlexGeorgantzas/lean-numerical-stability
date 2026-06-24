# Higham Chapter 13 Proof-Source Ledger

This ledger records Chapter 13 targets whose source proof is omitted,
citation-only, or delegated to another result. These targets must not be
reported as closed unless the cited proof has been reconstructed in Lean or
replaced by an independently checked proof.

## Theorem 13.6

- Source: `References/1.9780898718027.ch13.pdf`, pp.250--251.
- Statement summary: computed block LU factors and block back substitution in
  Algorithm 13.3, Implementation 1, satisfy the two backward-error inequalities
  displayed in (13.16), up to first order in `u`.
- Book proof status: omitted; the text cites Demmel--Higham--Schreiber [326].
- Current Lean status: `block_lu_solve_backward_error` is a scalar aggregation
  lemma from supplied factorization and solve error bounds. It is not a proof of
  Theorem 13.6 because it assumes the algorithm-specific first-order estimates
  that the source theorem delegates to [326].
- Current decision: keep scalar aggregation support, but leave
  `H13-Thm13.6` and `H13-Eq13.16` open in the inventory.
- Closure requirement: either formalize the missing algorithm-specific proof from
  the cited source, or introduce a source-facing theorem whose hypotheses
  explicitly include the [326]-level assumptions and classify it as conditional.
- Source-acquisition checkpoint, 2026-06-23: an advisory later source,
  Lindquist--Luszczek--Dongarra, *The Stability of Block Eliminations and
  Additive Modifications*, arXiv:2509.07305
  (https://arxiv.org/abs/2509.07305), identifies the relevant previous
  Demmel--Higham--Schreiber work as J. W. Demmel, N. J. Higham, and
  R. S. Schreiber, "Stability of block LU factorization", *Numerical Linear
  Algebra with Applications* 2 (1995), pp. 173--190,
  doi:10.1002/nla.1680020208 (https://doi.org/10.1002/nla.1680020208).
  This is bibliographic acquisition only: the primary paper's proof has not yet
  been reconstructed locally, so `H13-Thm13.6` and `H13-Eq13.16` remain open.

## Lemma 13.10 Dependency Note

- Source: p.255.
- Statement summary: for an SPD block partition, the Schur complement satisfies
  `kappa_2(S) <= kappa_2(A)`.
- Book proof status: a proof sketch is given and refers to Problem 13.4.
- Current Lean status: closed directly by
  `higham13_lemma13_10_schur_kappa_bound_of_spd`, with
  `higham13_lemma13_10_schur_kappa_bound_of_source_posDef_block`,
  `higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_posDef_block_inverse`,
  and `kappa2_le_of_opNorm2Le_bounds_general` as the final bridge layer.
  The older `higham13_lemma13_10_conditional_bound` remains only a conditional
  adapter and is not the closure claim.
- Closure requirement: satisfied for the SPD/operator-2 source Lemma 13.10.
  Problem 13.4 remains separately open in the source max-entry norm.

## Problem 13.4 Source Norm Note

- Source: p.258, Problem 13.4.
- Statement summary: for the partition (13.26), the exercise explicitly sets
  `||A|| := max_ij |a_ij|` and asks for
  `||A21 A11^{-1}|| <= n rho_n kappa(A)` plus
  `kappa(S) <= rho_n kappa(A)`.
- Current Lean status: `higham13_problem13_4_A21A11inv_maxEntryNormRect_from_block_inverse_growth`
  proves the lower-left inequality from the Problem 13.8 block-inverse identity
  `A21 A11^{-1} = -S (A^{-1})21`, Schur growth, full-inverse max-entry,
  dimension, and condition-product certificates.  This route supersedes the
  older displayed-`A11^{-1}` entrywise-certificate bottleneck.  The Schur side
  is closed by
  `higham13_problem13_4_schur_kappa_maxEntryNormRect_from_block_inverse`, which
  identifies `S^{-1}` with the lower-right block of the full inverse.  The paired
  theorem `higham13_problem13_4_maxEntry_bounds_from_block_inverse_growth`
  packages both displayed Problem 13.4 inequalities from those explicit
  certificates.  The follow-up source wrapper
  `higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth`
  instantiates the full-inverse max-entry certificate from the canonical
  source inverse `nonsingInv (r+s) A` once the displayed block matrix is
  identified via `finSumFinEquiv`.  The exact-κ wrapper
  `higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth_exact_kappa`
  then chooses `κ(A) = ||A||_max ||A^{-1}||_max`, removing the separate
  condition-product certificate from the source-shaped surface.  The wrapper
  `higham13_problem13_4_maxEntry_bounds_from_source_schur_growth_exact_kappa`
  further accepts the book's norm-level Schur-growth premise
  `||S||_max <= rho ||A||_max` and derives the entrywise premise internally.
  The growth-factor wrapper
  `higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa`
  instantiates `rho` as the formal max-entry `growthFactorEntry`; at that
  route step it reduces Schur growth to identifying the Schur complement with
  the relevant growth-factor stage block.  The Schur-submatrix wrapper
  `higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa_of_schur_submatrix`
  derives that norm inclusion from an entrywise lower-right equality between
  the displayed Schur complement and the formal growth-factor matrix/stage.
  The concrete local stage declarations `higham13_problem13_4_schurStageMatrix`,
  `higham13_problem13_4_schurStageMatrix_lower_right`, and
  `higham13_problem13_4_maxEntry_bounds_from_source_schurStageMatrix_exact_kappa`
  close that lower-right equality by construction for the one-step Schur-stage
  matrix.  The growth-factor lower-bound lemmas `growthFactorEntry_nonneg` and
  `growthFactorEntry_ge_one_of_maxEntryNorm_le` close the scalar fact `rho >= 1`
  once the chosen growth matrix contains the initial max-entry norm.  The
  general bridge
  `higham13_problem13_4_L21_eq13_22_premise_from_source_growthFactorEntry_exact_kappa`
  uses that fact to promote the lower-left bound to the Eq.13.22 lower-factor
  premise `n rho^2 kappa(A)` for any growth matrix containing both the initial
  matrix and the Schur complement; the local Schur-stage theorem
  `higham13_problem13_4_L21_eq13_22_premise_from_source_schurStageMatrix_exact_kappa`
  is now a specialization of that general bridge.  The square helper
  `maxEntryNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm` and block helper
  `blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm` supply the
  matching Eq.13.21-style upper-factor premise from the same max-entry growth
  object, while `blockMaxNorm_le_maxEntryNorm_of_reindex_eq` converts an
  entrywise block embedding into the needed block containment.  The square local
  product bridges
  `higham13_eq13_22_local_product_from_source_growthFactorEntry_exact_kappa`
  and
  `higham13_eq13_23_local_product_from_source_growthFactorEntry_exact_kappa`
  and the block local product bridges
  `higham13_eq13_22_local_block_product_from_source_growthFactorEntry_exact_kappa`
  and
  `higham13_eq13_23_local_block_product_from_source_growthFactorEntry_exact_kappa`
  combine the source lower-left premise and contained upper factor under one
  common growth object, with the Eq.13.23 versions specializing the scalar
  growth factor by the source condition `rho_n <= 2`.  The finite local
  history-envelope declarations `maxEntryNorm_const_nonneg`,
  `higham13_problem13_4_localGrowthEnvelope`,
  `higham13_problem13_4_localGrowthEnvelope_contains_initial`,
  `higham13_problem13_4_localGrowthEnvelope_contains_schur`, and
  `higham13_problem13_4_localGrowthEnvelope_contains_block_upper` provide an
  honest local growth object containing the initial matrix, current Schur
  complement, and block upper factor.  They feed
  `higham13_eq13_22_local_block_product_from_history_envelope_exact_kappa` and
  `higham13_eq13_23_local_block_product_from_history_envelope_exact_kappa`,
  which remove the three local containment hypotheses without claiming the
  recursive GE history theorem.
- The dominated-envelope adapters
  `higham13_eq13_22_local_block_product_from_dominated_history_envelope_exact_kappa`
  and
  `higham13_eq13_23_local_block_product_from_dominated_history_envelope_exact_kappa`
  further reduce the recursive/global growth work to one explicit domination
  hypothesis:
  `maxEntryNorm localGrowthEnvelope <= maxEntryNorm G`.
- The finite Algorithm 13.3 stage-history layer
  `higham13_algorithm13_3_stageHistoryBound` /
  `higham13_algorithm13_3_stageHistoryGrowthMatrix` proves that a concrete
  block-stage history object dominates the input block table, every recorded
  Schur stage, and `higham13_algorithm13_3_upperFromStages`.  This is retained
  as recursive-growth infrastructure; it still needs a flattened tail
  identification theorem before it can discharge the local two-block
  `higham13_problem13_4_localGrowthEnvelope` domination hypothesis.
- The local-envelope domination bridge
  `higham13_problem13_4_localGrowthEnvelope_le_of_bounds` proves the finite
  envelope's universal property, and
  `higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_initial_schur`
  specializes it to the finite Algorithm 13.3 stage-history object.  The
  stage-history upper-factor containment is now automatic on this route; the
  exact remaining local proof obligations are the flattened initial matrix and
  flattened Schur complement containments in the stage-history growth matrix.
- The flat/stage-history containment layer
  `maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm`,
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_flat_initial`,
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_stage_submatrix`,
  and
  `higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_flat_initial_stage_submatrix`
  closes the norm-preserving flat-initial bridge and the generic
  recorded-stage scalar-submatrix bridge.  The tail-packaged layer
  `higham13_algorithm13_3_schurStageTailBlock`,
  `higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_flat_stage_tail`,
  and
  `higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_flat_initial_flat_stage_tail`
  closes the same containment for a flattened block tail of a recorded stage.
  The source-faithful matrix-product wrapper
  `higham13_algorithm13_3_schurStageMatrixBlock` and
  `higham13_algorithm13_3_schurStageMatrixBlock_one_tail_eq_blockSchur` prove
  the first active tail/block-Schur identity with genuine block matrix
  multiplication.  The matrix-product stage-history/local-envelope bridge
  `higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_stage_tail`,
  `higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_flat_initial_flat_stage_tail`,
  and
  `higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_blockSchur_first_tail`
  now puts that source Schur complement under the same local-growth-envelope
  route.  The first-split reindexing and product wrappers
  `blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur`,
  `higham13_eq13_22_local_block_product_from_matrix_stage_history_first_split_exact_kappa`,
  and
  `higham13_eq13_23_local_block_product_from_matrix_stage_history_first_split_exact_kappa`
  now close the local source-faithful Eq.13.22/Eq.13.23 block-product route.
  The remaining source proof is the recursive/global full-factor lift.
- Closure requirement: instantiate the common recursive/global GE growth object
  by identifying it with, or proving it dominates, the local history envelope
  at each recursive stage, then lift the local product bridge to the full
  recursive `L`/`U` factors in Eq.13.22/Eq.13.23.
  The displayed inverse-entry certificate route is now retained only as an
  adapter, not as the main missing source proof.
