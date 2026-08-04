import NumStability.Algorithms.MatrixInversion

/-!
# MatrixInversion old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W08, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.Method2Spec
#check @NumStability.MatProdError
#check @NumStability.BlockMethod1BSpec
