import NumStability.Algorithms.HighamChapter15BoydSourceLocal

/-!
# Old path: `NumStability.Algorithms.HighamChapter15BoydSourceLocal`

Imports only the historical module. Every public declaration the owner
had at C0007 still resolves through the compatibility module, so no
consumer that used this import path can have been broken by the split.
-/

#check @NumStability.Ch15.IsBoydNondegenerateTangentHessian
#check @NumStability.Ch15.boydInvariantRestriction
#check @NumStability.Ch15.boydLemma3B
#check @NumStability.Ch15.boydLemma3B_sub
#check @NumStability.Ch15.boydLemma3B_weighted_psd
#check @NumStability.Ch15.boydLemma3B_weighted_symmetric
#check @NumStability.Ch15.boydProjectedLemma3B
#check @NumStability.Ch15.boydProjectedLemma3B_eq_projection
#check @NumStability.Ch15.boydProjectedLemma3B_is_tangent
#check @NumStability.Ch15.boydProjectedLemma3B_weighted_psd
#check @NumStability.Ch15.boydProjectedLemma3B_weighted_psd_on_tangent
#check @NumStability.Ch15.boydProjectedLemma3B_weighted_symmetric
#check @NumStability.Ch15.boydProjectedLemma3B_weighted_symmetric_on_tangent
#check @NumStability.Ch15.boydRectActionCLM
#check @NumStability.Ch15.boydRectActionCLM_apply
#check @NumStability.Ch15.boydRectTransposeActionCLM
#check @NumStability.Ch15.boydRectTransposeActionCLM_apply
#check @NumStability.Ch15.boydSmoothRectDerivative
#check @NumStability.Ch15.boydSmoothRectDerivative_apply_directional_chain
#check @NumStability.Ch15.boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B
#check @NumStability.Ch15.boydSmoothRectUpdate
#check @NumStability.Ch15.boydSmoothRectUpdate_eq_of_stationarity
#check @NumStability.Ch15.boydSmoothRectUpdate_hasFDerivAt
#check @NumStability.Ch15.boydWeightedPair
#check @NumStability.Ch15.boydWeightedPair_lemma3B
#check @NumStability.Ch15.boydWeightedPair_projection_left_of_tangent
#check @NumStability.Ch15.boydWeightedPair_projection_right_of_tangent
#check @NumStability.Ch15.boydWeightedPair_smul_left
#check @NumStability.Ch15.boydWeightedPair_smul_right
#check @NumStability.Ch15.boydWeightedPair_sub_left
#check @NumStability.Ch15.boydWeightedPair_sub_right
#check @NumStability.Ch15.boydWeightedPair_symm
#check @NumStability.Ch15.boydWeightedPair_x_self_eq_powerSum
#check @NumStability.Ch15.boydWeightedProjection
#check @NumStability.Ch15.boydWeightedProjection_eq_self_of_tangent
#check @NumStability.Ch15.boydWeightedProjection_is_tangent
#check @NumStability.Ch15.boydWeightedProjection_sq
#check @NumStability.Ch15.boydWeightedProjection_sq_le
#check @NumStability.Ch15.boydWeightedTangentDerivative
#check @NumStability.Ch15.boyd_abs_dualCoordinate
#check @NumStability.Ch15.boyd_dualCoordinate_abs_rpow_q
#check @NumStability.Ch15.boyd_dualCoordinate_involution
#check @NumStability.Ch15.boyd_dualCoordinate_ne_zero
#check @NumStability.Ch15.boyd_dualCoordinate_weight
#check @NumStability.Ch15.boyd_holder_sub_one_mul_sub_one
#check @NumStability.Ch15.boyd_holder_sub_one_mul_sub_two
#check @NumStability.Ch15.boyd_inner_directional_eq_weighted_projectedLemma3B
#check @NumStability.Ch15.boyd_outer_directional_weighted_tangent
#check @NumStability.Ch15.boyd_powerSum_scaled_dual
#check @NumStability.Ch15.boyd_scale_coefficient
#check @NumStability.Ch15.boyd_scaled_dualCoordinate_involution
#check @NumStability.Ch15.boyd_scaled_dualCoordinate_weight
#check @NumStability.Ch15.boyd_scaled_gradient_coefficient
#check @NumStability.Ch15.boyd_stationarity_Bx
#check @NumStability.Ch15.boyd_stationarity_inner_vector
#check @NumStability.Ch15.boyd_stationarity_outer_coord_ne
#check @NumStability.Ch15.boyd_tangent_restriction_power_stable_of_nondegenerate_hessian
#check @NumStability.Ch15.boyd_transpose_inner_directional_expansion
#check @NumStability.Ch15.boyd_weight_mul_B
#check @NumStability.Ch15.boyd_weight_mul_inverse_weight
#check @NumStability.Ch15.boyd_weight_mul_self
#check @NumStability.Ch15.boyd_weightedPair_scaled_dual_weighted
#check @NumStability.Ch15.boyd_weighted_tangent_contraction_of_nondegenerate_hessian
#check @NumStability.Ch15.continuousLinearEquiv_conj_pow
#check @NumStability.Ch15.differentiableAt_realLpGradientCoordinateFactor
#check @NumStability.Ch15.differentiableAt_realLpGradient_of_all_ne
#check @NumStability.Ch15.differentiableAt_realLpPowerSum
#check @NumStability.Ch15.exists_pos_power_bound_of_equivalent_contraction
#check @NumStability.Ch15.fderiv_realLpGradient_apply
#check @NumStability.Ch15.hasDerivAt_abs_rpow_sub_two_mul_self
#check @NumStability.Ch15.higham15_boyd_local_corrected_of_actual_derivative_power_stable
#check @NumStability.Ch15.opNorm_le_one_sub_of_symmetric_psd_rayleigh_gap
#check @NumStability.Ch15.realLpGradientDirectional
#check @NumStability.Ch15.realLpGradient_line_hasDerivAt
#check @NumStability.Ch15.realLpGradient_scaled_dual_eq
#check @NumStability.Ch15.rect_general_boyd_tangent_power_stable_of_nondegenerate_hessian
#check @NumStability.Ch15.rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B
#check @NumStability.Ch15.rect_general_fderiv_xnext_eq_boydSmoothRectDerivative
#check @NumStability.Ch15.rect_general_xnext_eq_boydSmoothRectUpdate
#check @NumStability.Ch15.rect_general_xnext_eq_of_stationarity
#check @NumStability.Ch15.rect_general_xnext_hasFDerivAt_boyd
#check @NumStability.Ch15.strictMaximum_does_not_imply_negative_quadratic_term
