import NumStability.Algorithms.TestMatrices.Higham28Companion

/-!
# Higham28Companion old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.companionOfMatrix
#check @NumStability.Matrix.IsSimilar.rank_eq
#check @NumStability.Matrix.IsSimilar.rank_sub_scalar_eq
