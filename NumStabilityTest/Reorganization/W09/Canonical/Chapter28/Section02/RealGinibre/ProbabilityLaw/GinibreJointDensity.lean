import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.GinibreJointDensity

/-!
# GinibreJointDensity canonical-only test (S_GIN_PROB, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28GinibreJointDensity`
during wave W09 and must resolve from S_GIN_PROB alone.
-/
#check @NumStability.integrable_standardGaussianVectorDensity
#check @NumStability.integral_standardGaussianVectorDensity_eq_one
