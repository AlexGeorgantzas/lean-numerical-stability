import NumStability.Algorithms.Ch15CondEstimators

/-!
# Old path: `NumStability.Algorithms.Ch15CondEstimators`

Imports only the historical module. Every public declaration the owner
had at C0007 still resolves through the compatibility module, so no
consumer that used this import path can have been broken by the split.
-/

#check @NumStability.Ch15.IsPlusMinusOne
#check @NumStability.Ch15.IsUpperTriangular
#check @NumStability.Ch15.blockTriangular_id_of_isUpperTriangular
#check @NumStability.Ch15.diag_ne_zero_of_isUpperTriangular_isLeftInverse
#check @NumStability.Ch15.dixon_left_inequality
#check @NumStability.Ch15.dixon_quadForm_gram_eq
#check @NumStability.Ch15.dixon_sqrt_quadForm_le_opNorm2
#check @NumStability.Ch15.gram_inv_of_isInverse
#check @NumStability.Ch15.infNormVec_eq_one_of_plusMinusOne
#check @NumStability.Ch15.linpackD
#check @NumStability.Ch15.linpackD_isPlusMinusOne
#check @NumStability.Ch15.linpackPartial
#check @NumStability.Ch15.linpackSign
#check @NumStability.Ch15.linpackSign_plusMinusOne
#check @NumStability.Ch15.linpackY
#check @NumStability.Ch15.linpackYSteps
#check @NumStability.Ch15.linpackY_infNorm_le_infNorm_inv
#check @NumStability.Ch15.linpackY_infNorm_le_infNorm_inv_nonsingular
#check @NumStability.Ch15.linpackY_solves
#check @NumStability.Ch15.linpack_estimate_le_infNorm_inv
#check @NumStability.Ch15.quadForm
