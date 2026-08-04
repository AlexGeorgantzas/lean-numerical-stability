import NumStability.Algorithms.TestMatrices.Higham28Ginibre

/-!
# Higham28Ginibre old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.realEigenvalueCount_le
#check @NumStability.ginibreHypergeometricTerm
#check @NumStability.ginibreHypergeometricTerm_eq
