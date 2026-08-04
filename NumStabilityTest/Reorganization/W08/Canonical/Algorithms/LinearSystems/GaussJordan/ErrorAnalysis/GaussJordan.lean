import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan

/-!
# GaussJordan canonical-only test (D01, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.GaussJordan`
during wave W08 and must resolve from D01 alone.
-/
#check @NumStability.gje_c₃
#check @NumStability.GJEStage2Spec
#check @NumStability.gje_c3_nonneg
