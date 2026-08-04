import NumStability.Analysis.TestMatrices.Companion.Basic

/-!
# Basic canonical-only test (R_COMPANION, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28`
during wave W09 and must resolve from R_COMPANION alone.
-/
#check @NumStability.companionMatrix
#check @NumStability.companionEigenvector
#check @NumStability.companionMatrix_mulVec_companionEigenvector
