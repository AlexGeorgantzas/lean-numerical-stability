import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.KKT

/-!
# Equality.KKT canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.LSEKKTSystem
#check @NumStability.LSEKKTLinearMap
#check @NumStability.LSEKKTSystem.iff_linearMap_eq
