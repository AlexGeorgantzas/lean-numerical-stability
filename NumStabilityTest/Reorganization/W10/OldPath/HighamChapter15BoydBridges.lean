import NumStability.Algorithms.HighamChapter15BoydBridges

/-!
# Old path: `NumStability.Algorithms.HighamChapter15BoydBridges`

Imports only the historical module. Every public declaration the owner
had at C0007 still resolves through the compatibility module, so no
consumer that used this import path can have been broken by the split.
-/

#check @NumStability.Ch15.IsLocalContractionTo
#check @NumStability.Ch15.boydCarrier_fixedPoint_pos
#check @NumStability.Ch15.boydCarrier_maximum_eq_opP
#check @NumStability.Ch15.boydCarrier_ne_zero
#check @NumStability.Ch15.boydNonnegativeUnitCarrier
#check @NumStability.Ch15.boydNonnegativeUnitCarrier_nonempty
#check @NumStability.Ch15.complex_rect_action_le_abs_real_action
#check @NumStability.Ch15.continuousAt_realLpDual
#check @NumStability.Ch15.continuousAt_realLpDualUnit
#check @NumStability.Ch15.continuousAt_realLpGradient
#check @NumStability.Ch15.continuousAt_rect_general_xnext
#check @NumStability.Ch15.continuousAt_rect_general_zof
#check @NumStability.Ch15.continuousOn_rect_general_xnext_boydCarrier
#check @NumStability.Ch15.continuous_realLpGradient_coordFactor
#check @NumStability.Ch15.continuous_realLpPowerSum
#check @NumStability.Ch15.continuous_realLpSignedPower
#check @NumStability.Ch15.continuous_realVecLpNorm
#check @NumStability.Ch15.continuous_rect_general_objective
#check @NumStability.Ch15.continuous_rect_general_yof
#check @NumStability.Ch15.exists_boydCarrier_maximizing_fixedPoint
#check @NumStability.Ch15.exists_boydCarrier_positive_opP_fixedPoint
#check @NumStability.Ch15.exists_isLocalContractionTo_of_hasFDerivAt_norm_lt
#check @NumStability.Ch15.exists_pos_coord_of_mem_boydCarrier
#check @NumStability.Ch15.exists_pos_in_column_of_rectGram_irreducible
#check @NumStability.Ch15.higham15_boyd_global_of_compact_unique_optimal_fixed
#check @NumStability.Ch15.higham15_boyd_local_linear_of_fderiv_norm_lt
#check @NumStability.Ch15.higham15_boyd_local_linear_of_local_contraction
#check @NumStability.Ch15.higham15_boyd_normalized_positive_orbit
#check @NumStability.Ch15.isClosed_boydNonnegativeUnitCarrier
#check @NumStability.Ch15.isCompact_boydNonnegativeUnitCarrier
#check @NumStability.Ch15.iterate_dist_le_geometric_of_isLocalContractionTo
#check @NumStability.Ch15.realLpDualUnit_pos_of_pos
#check @NumStability.Ch15.realLpDual_eq_realLpGradient
#check @NumStability.Ch15.realLpDual_nonneg_of_nonneg
#check @NumStability.Ch15.realLpDual_pos_of_pos
#check @NumStability.Ch15.realLpGradient_coord_eq_signedPower
#check @NumStability.Ch15.realLpGradient_nonneg_of_nonneg_coord
#check @NumStability.Ch15.realLpGradient_pos_of_pos_coord
#check @NumStability.Ch15.realLpNormalizedStart
#check @NumStability.Ch15.realLpNormalizedStart_norm_eq_one
#check @NumStability.Ch15.realLpNormalizedStart_pos
#check @NumStability.Ch15.realLpNormer_eq_dual
#check @NumStability.Ch15.realLpSignedPower
#check @NumStability.Ch15.realVecLpNorm_smul_real
#check @NumStability.Ch15.rectGram
#check @NumStability.Ch15.rectGram_mulVec_eq_transpose_yof
#check @NumStability.Ch15.rectGram_mulVec_zero_at_zero_of_fixed
#check @NumStability.Ch15.rectGram_nonneg
#check @NumStability.Ch15.rectMatVec_pos_of_row_entry
#check @NumStability.Ch15.rectPNormPair_xseq_eq_iterate
#check @NumStability.Ch15.rect_gammaSeq_bddAbove
#check @NumStability.Ch15.rect_gammaSeq_monotone
#check @NumStability.Ch15.rect_gammaSeq_tendsto_ciSup
#check @NumStability.Ch15.rect_general_stopsAt_iff_xnext_eq
#check @NumStability.Ch15.rect_general_xnext_eq_of_objective_not_increased
#check @NumStability.Ch15.rect_general_xnext_mapsTo_boydCarrier
#check @NumStability.Ch15.rect_general_xnext_mem_boydCarrier
#check @NumStability.Ch15.rect_general_xnext_pos_of_nonneg_gram_irreducible
#check @NumStability.Ch15.rect_general_xnext_pos_of_pos_columns
#check @NumStability.Ch15.rect_general_xseq_pos_of_nonneg_gram_irreducible
#check @NumStability.Ch15.rect_general_yof_ne_zero_of_mem_boydCarrier
#check @NumStability.Ch15.rect_general_zof_ne_zero_of_mem_boydCarrier
#check @NumStability.Ch15.rect_general_zof_nonneg_of_mem_boydCarrier
#check @NumStability.Ch15.tendsto_iterate_of_compact_strictLyapunov_unique_fixed
#check @NumStability.Ch15.tendsto_iterate_of_isLocalContractionTo
