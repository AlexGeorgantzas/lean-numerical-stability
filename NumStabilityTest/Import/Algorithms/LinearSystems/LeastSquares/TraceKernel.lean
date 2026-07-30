import NumStability.Algorithms.LinearSystems.LeastSquares.TraceKernel

/-!
# TraceKernel canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.Theorem20_7.applyProd_sub
#check @NumStability.Theorem20_7.applyProd_smul
#check @NumStability.Theorem20_7.applyProd_snoc
