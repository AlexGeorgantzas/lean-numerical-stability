import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Algorithms.NormEstimation.OneNorm.LAPACK.Basic
import NumStability.Algorithms.NormEstimation.OneNorm.LINPACK.Basic
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.PNormPowerMethod

/-!
# One-norm estimation

The reusable one-norm machinery and the
Chapter 15 one-norm endpoints, built together.
-/

#check @NumStability.Ch15.IsPlusMinusOne
#check @NumStability.Ch15.IsUpperTriangular
#check @NumStability.Ch15.blockTriangular_id_of_isUpperTriangular
#check @NumStability.Ch15.diag_ne_zero_of_isUpperTriangular_isLeftInverse
#check @NumStability.Ch15.dualq_one
#check @NumStability.Ch15.dualq_one_attains
#check @NumStability.Ch15.dualq_one_punit
#check @NumStability.Ch15.holder_one
#check @NumStability.Ch15.infNormVec_eq_one_of_plusMinusOne
#check @NumStability.Ch15.linpackD
#check @NumStability.Ch15.linpackPartial
#check @NumStability.Ch15.linpackY
#check @NumStability.Ch15.linpackYSteps
#check @NumStability.Ch15.linpack_estimate_le_infNorm_inv
#check @NumStability.Ch15.pNormPair_one
#check @NumStability.Ch15.sign_attains_one
#check @NumStability.Ch15.sign_qunit_one
#check @NumStability.OneNormState
#check @NumStability.OneNormState.casesOn
#check @NumStability.OneNormState.ctorIdx
#check @NumStability.OneNormState.mk
#check @NumStability.OneNormState.mk.inj
#check @NumStability.OneNormState.mk.injEq
#check @NumStability.OneNormState.mk.noConfusion
#check @NumStability.OneNormState.mk.sizeOf_spec
#check @NumStability.OneNormState.noConfusion
#check @NumStability.OneNormState.noConfusionType
#check @NumStability.OneNormState.rec
#check @NumStability.OneNormState.recOn
#check @NumStability.OneNormState.x
#check @NumStability.OneNormState.γ
#check @NumStability.abs_signVec
#check @NumStability.argmaxAbs
#check @NumStability.argmaxAbs_spec
#check @NumStability.basisVec
#check @NumStability.initial_vec_oneNorm
#check @NumStability.lapackAltVec
#check @NumStability.lapackNormEstimator
#check @NumStability.mul_signVec_eq_abs
#check @NumStability.oneNormPowerMethod
#check @NumStability.oneNormStep
#check @NumStability.oneNormVec
#check @NumStability.oneNormVec_basisVec
#check @NumStability.oneNormVec_matVec_le
#check @NumStability.oneNormVec_nonneg
#check @NumStability.signVec
