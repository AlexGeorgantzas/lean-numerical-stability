import NumStability.Algorithms.GaussJordan

/-!
# GaussJordan old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W08, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.gje_c₃
#check @NumStability.GJEStage2Spec
#check @NumStability.gje_c3_nonneg
