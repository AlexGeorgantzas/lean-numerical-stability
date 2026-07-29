import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem

/-!
# AugmentedSystem canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.LSAugmentedSystem
#check @NumStability.LSAugmentedNormalSystem
#check @NumStability.LSScaledAugmentedSystem
