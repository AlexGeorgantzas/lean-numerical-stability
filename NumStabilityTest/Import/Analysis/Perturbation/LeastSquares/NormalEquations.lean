import NumStability.Analysis.Perturbation.LeastSquares.NormalEquations

/-!
# NormalEquations canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.GramVecError
#check @NumStability.GramProductError
#check @NumStability.GramConditionSquared
