import NumStability.Algorithms.TestMatrices.Higham28Cauchy

/-!
# Higham28Cauchy old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.cauchyChoTerm
#check @NumStability.headTailEquiv
#check @NumStability.prod_Ioi_succ_fin
