import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.MatrixInversion

/-!
# MatrixInversion canonical-only test (D31, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave W08 and must resolve from D31 alone.
-/
#check @NumStability.higham14_absMatrix_matMulVec_mono
#check @NumStability.higham14_method2BBlockUpdateDelta
#check @NumStability.higham14_method2BBlockUpdateExact
