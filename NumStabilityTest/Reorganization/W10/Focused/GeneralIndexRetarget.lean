import NumStability.Algorithms.NormEstimation.OneNorm.GeneralIndex

/-!
# Proposed integrator retarget

Pins the accepted surface behind integrator
request 3. `GeneralIndex` is imported unchanged; both declarations it uses are
checked at their frozen names, so the proposed retarget can be validated without
editing the accepted consumer.
-/

#check @NumStability.lapackNormEstimator
#check @NumStability.lapackNormEstimator_lower_bound
