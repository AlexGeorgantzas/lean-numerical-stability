import NumStability.Analysis.TestMatrices.Gaussian.GaussianDirection
import NumStability.Analysis.TestMatrices.Gaussian.GaussianOrthogonal

/-!
# Gaussian: reusable test-matrix analysis, standing alone

Imports only the reusable `Gaussian` modules. This is the family boundary the
wave brief asks for: reusable test-matrix analysis that a later wave can use
without importing Chapter 28 source correspondence.
-/
#check @NumStability.orthogonalSphereBase
#check @NumStability.gaussianUnitDirection
#check @NumStability.gaussianUnitDirectionValue
#check @NumStability.standardGaussianVectorMeasure
