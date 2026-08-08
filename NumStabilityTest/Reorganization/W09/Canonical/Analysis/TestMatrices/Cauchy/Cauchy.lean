import NumStability.Analysis.TestMatrices.Cauchy.Cauchy

/-!
# Cauchy canonical-only test (R_CAUCHY, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Cauchy`
during wave W09 and must resolve from R_CAUCHY alone.
-/
#check @NumStability.cauchyChoTerm
#check @NumStability.headTailEquiv
#check @NumStability.prod_Ioi_succ_fin
