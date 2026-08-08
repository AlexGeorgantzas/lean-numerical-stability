import NumStability.Analysis.TestMatrices.Orthogonal.Basic
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalCoordinates
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalFibers
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalHaar
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalSphere

/-!
# Orthogonal: reusable test-matrix analysis, standing alone

Imports only the reusable `Orthogonal` modules. This is the family boundary the
wave brief asks for: reusable test-matrix analysis that a later wave can use
without importing Chapter 28 source correspondence.
-/
#check @NumStability.OrthogonalSphere
#check @NumStability.orthogonalFirstRow
#check @NumStability.RealOrthogonalGroup
#check @NumStability.stewartFirstSection
