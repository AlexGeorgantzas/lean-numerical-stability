import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.CondEstimators
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.PowerBounds.CondEstimators
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.PowerBounds.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Probability.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Probability.DixonProbability
import NumStability.Source.Higham.Chapter15.Equation07.DixonBound.Basic
import NumStability.Source.Higham.Chapter15.Theorem06.Dixon.Basic

/-!
# Dixon

Reusable two-norm Dixon algebra, power bounds and
probability, with the printed Theorem 15.6 and equation (15.7) leaves.
-/

#check @NumStability.Ch15.dixon_left_inequality
#check @NumStability.Ch15.dixon_quadForm_gram_eq
#check @NumStability.Ch15.dixon_sqrt_quadForm_le_opNorm2
#check @NumStability.Ch15.gram_inv_of_isInverse
#check @NumStability.Ch15.quadForm
#check @NumStability.ch15Closure_ch15SphereInner_unitSphereOfFiniteVec
#check @NumStability.ch15Closure_dixon_failure_probability_le
#check @NumStability.ch15Closure_dixon_left_power_inequality
#check @NumStability.ch15Closure_dixon_success_probability_ge
#check @NumStability.ch15Closure_exists_dixon_sphere_direction_power_lower
#check @NumStability.ch15Closure_exists_gram_opNorm2_sq_unit_eigenvector
#check @NumStability.ch15Closure_gram_pow_finitePSD
#check @NumStability.ch15Closure_gram_symmetric
#check @NumStability.ch15Closure_matPow_matrix_eq_pow
#check @NumStability.ch15Closure_matPow_mulVec_eigenvector
#check @NumStability.ch15Closure_matPow_symmetric
#check @NumStability.ch15Closure_opNorm2Le_matPow
#check @NumStability.ch15Closure_quadForm_power_lower_of_unit_eigenvector
#check @NumStability.ch15Closure_sqrt_inv_pow_eq_rpow_neg_half
#check @NumStability.ch15Closure_unitSphereOfFiniteVec
#check @NumStability.ch15SphereFirstCoordinate
#check @NumStability.ch15SphereInner
#check @NumStability.ch15SphereInner_base
#check @NumStability.ch15SphereInner_smul
#check @NumStability.ch15_dixon_strip_coefficient_le
#check @NumStability.ch15_inv_sqrt_two_pi_le
#check @NumStability.ch15_measurable_sphereFirstCoordinate
#check @NumStability.ch15_piFinSuccAbove_norm_sq
#check @NumStability.ch15_ratio_implies_strip
#check @NumStability.ch15_standardGaussianDirection_firstCoordinate_dixon_bound
#check @NumStability.ch15_standardGaussianDirection_firstCoordinate_small
#check @NumStability.ch15_standardGaussianDirection_inner_dixon_bound
#check @NumStability.ch15_standardGaussian_abs_le
#check @NumStability.ch15_standardGaussian_coordinate_sq_integral
#check @NumStability.ch15_standardGaussian_norm_integral_le_sqrt
#check @NumStability.ch15_standardGaussian_norm_sq_integral
#check @NumStability.ch15_standardGaussian_pdf_le
#check @NumStability.ch15_standardGaussian_product_strip_bound
#check @NumStability.higham15_6_dixon_closed
