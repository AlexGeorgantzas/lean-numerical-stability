import NumStability.Analysis.TestMatrices.Cauchy.Basic

/-!
# Basic canonical-only test (R_CAUCHY, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28`
during wave W09 and must resolve from R_CAUCHY alone.
-/
#check @NumStability.cauchyMatrix
#check @NumStability.cauchyDetFormula
#check @NumStability.cauchyInverseEntry
