import NumStability.Analysis.TestMatrices.Companion.Contracts

/-!
# Contracts canonical-only test (R_COMPANION, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Contracts`
during wave W09 and must resolve from R_COMPANION alone.
-/
#check @NumStability.companionRankMinor
#check @NumStability.companionGramFormula
#check @NumStability.companionRankMinor_det
