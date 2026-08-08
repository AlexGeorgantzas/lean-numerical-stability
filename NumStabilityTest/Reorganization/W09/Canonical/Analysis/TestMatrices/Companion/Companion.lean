import NumStability.Analysis.TestMatrices.Companion.Companion

/-!
# Companion canonical-only test (R_COMPANION, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Companion`
during wave W09 and must resolve from R_COMPANION alone.
-/
#check @NumStability.companionOfMatrix
#check @NumStability.Matrix.IsSimilar.rank_eq
#check @NumStability.Matrix.IsSimilar.rank_sub_scalar_eq
