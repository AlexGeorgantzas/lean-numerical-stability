import NumStability.Analysis.TestMatrices.Gaussian.GaussianDirection

/-!
# GaussianDirection canonical-only test (R_GAUSSIAN, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28GaussianDirection`
during wave W09 and must resolve from R_GAUSSIAN alone.
-/
#check @NumStability.orthogonalSphereBase
#check @NumStability.gaussianUnitDirection
#check @NumStability.gaussianUnitDirectionValue
