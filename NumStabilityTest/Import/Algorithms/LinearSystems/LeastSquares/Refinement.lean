import NumStability.Algorithms.LinearSystems.LeastSquares.Refinement

/-!
# Refinement canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.higham20DirectLSRefinementResidual
#check @NumStability.Higham20AugmentedRefinementStep
#check @NumStability.Higham20SeminormalEquationsSolve
