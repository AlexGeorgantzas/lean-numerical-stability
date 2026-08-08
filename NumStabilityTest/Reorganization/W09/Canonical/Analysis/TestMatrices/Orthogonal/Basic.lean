import NumStability.Analysis.TestMatrices.Orthogonal.Basic

/-!
# Basic canonical-only test (R_ORTHOGONAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28`
during wave W09 and must resolve from R_ORTHOGONAL alone.
-/
#check @NumStability.matrixListProduct_isOrthogonal
#check @NumStability.higham28_theorem28_1_product_orthogonal
