import NumStability.Analysis.TestMatrices.Cauchy.Contracts

/-!
# Contracts canonical-only test (R_CAUCHY, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Contracts`
during wave W09 and must resolve from R_CAUCHY alone.
-/
#check @NumStability.cauchyLower
#check @NumStability.cauchyUpper
#check @NumStability.IsLeftCyclicFor
