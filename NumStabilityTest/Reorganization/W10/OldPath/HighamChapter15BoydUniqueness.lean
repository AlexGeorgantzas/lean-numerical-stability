import NumStability.Algorithms.HighamChapter15BoydUniqueness

/-!
# Old path: `NumStability.Algorithms.HighamChapter15BoydUniqueness`

Imports only the historical module. Every public declaration the owner
had at C0007 still resolves through the compatibility module, so no
consumer that used this import path can have been broken by the split.
-/

#check @NumStability.Ch15.boydCarrier_fixedPoint_isMax_rawPower
#check @NumStability.Ch15.boydCarrier_fixedPoint_unique
#check @NumStability.Ch15.boydRawAdjoint
#check @NumStability.Ch15.boydRawAdjoint_coord_eq_objective_mul_rpow_of_fixed
#check @NumStability.Ch15.boydRawPowerObjective
#check @NumStability.Ch15.boydRawPowerObjective_eq_realLpPowerSum
#check @NumStability.Ch15.boydRawPowerObjective_le_simplex_tangent
#check @NumStability.Ch15.boydSimplexTangentCoeff
#check @NumStability.Ch15.boydSimplexTangentCoeff_eq_mul_boydRawAdjoint
#check @NumStability.Ch15.boydSimplexTangentCoeff_eq_objective_mul_rpow_of_fixed
#check @NumStability.Ch15.boydSimplexTangent_sum_eq_objective_of_fixed
#check @NumStability.Ch15.boyd_row_power_tangent_eq_ratio
#check @NumStability.Ch15.boyd_row_power_tangent_le
#check @NumStability.Ch15.higham15_boyd_global_of_nonnegative_irreducibleGram
#check @NumStability.Ch15.realLpGradient_coord_eq_rpow_sub_one_of_pos_unit
#check @NumStability.Ch15.realLpPowerSum_eq_one_of_unit
#check @NumStability.Ch15.realVecLpNorm_rpow_eq_boydRawPowerObjective
#check @NumStability.Ch15.rect_general_zof_coord_eq_norm_mul_rpow_of_fixed
#check @NumStability.Ch15.rect_general_zof_eq_scale_mul_boydRawAdjoint
#check @NumStability.Ch15.rpow_div_rpow_cancel
#check @NumStability.Ch15.rpow_mul_mul_div_eq
#check @NumStability.Ch15.rpow_one_sub_mul_rpow_sub_one
#check @NumStability.Ch15.rpow_sub_two_mul_self_eq_rpow_sub_one
#check @NumStability.Ch15.rpow_sub_two_mul_self_eq_rpow_sub_one_of_nonneg
