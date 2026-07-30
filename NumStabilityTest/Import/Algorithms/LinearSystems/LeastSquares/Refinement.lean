import NumStability.Algorithms.LinearSystems.LeastSquares.Refinement

/-!
# Refinement canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.Higham20DirectLSRefinementRun
#check @NumStability.Higham20AugmentedRefinementRun
#check @NumStability.Higham20DirectLSRefinementStep
