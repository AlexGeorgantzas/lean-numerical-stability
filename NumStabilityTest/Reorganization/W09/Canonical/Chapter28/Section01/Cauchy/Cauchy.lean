import NumStability.Source.Higham.Chapter28.Section01.Cauchy.Cauchy

/-!
# Cauchy canonical-only test (S_S01_CAUCHY, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Cauchy`
during wave W09 and must resolve from S_S01_CAUCHY alone.
-/
#check @NumStability.sum_cauchyInverseFormula
#check @NumStability.cauchyLower_mul_cauchyUpper
