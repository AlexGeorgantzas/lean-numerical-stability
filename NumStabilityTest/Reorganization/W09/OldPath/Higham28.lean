import NumStability.Algorithms.TestMatrices.Higham28

/-!
# Higham28 old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.hilbertRNat
#check @NumStability.pascalLower
#check @NumStability.cauchyMatrix
