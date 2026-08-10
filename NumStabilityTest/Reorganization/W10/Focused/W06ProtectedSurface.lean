import NumStability.Algorithms.Sylvester.Higham16NormEstimator
import NumStability.Algorithms.CondEstimation

/-!
# W06 protected surface

The accepted `Higham16NormEstimator` relationship is
preserved: it consumes `CondEstimation`, which remains a declaration-bearing
compatibility module.
-/

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
#check @NumStability.cond_norm_identity
#check @NumStability.initial_vec_oneNorm
#check @NumStability.lapackAltVec
#check @NumStability.lapackNormEstimator
#check @NumStability.lapackNormEstimator_lower_bound
#check @NumStability.mul_signVec_eq_abs
#check @NumStability.oneNormPowerMethod
#check @NumStability.oneNormPowerMethod_lower_bound
#check @NumStability.oneNormStep
#check @NumStability.oneNormVec
#check @NumStability.oneNormVec_basisVec
#check @NumStability.oneNormVec_matVec_le
