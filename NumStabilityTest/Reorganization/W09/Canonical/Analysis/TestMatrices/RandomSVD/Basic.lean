import NumStability.Analysis.TestMatrices.RandomSVD.Basic

/-!
# Basic canonical-only test (R_RANDOMSVD, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28`
during wave W09 and must resolve from R_RANDOMSVD alone.
-/
#check @NumStability.randsvdMatrix
#check @NumStability.stewartOrthogonalProduct
