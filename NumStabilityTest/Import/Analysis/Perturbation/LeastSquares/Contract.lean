import NumStability.Analysis.Perturbation.LeastSquares.Contract

/-!
# Contract canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.Theorem20_7.rowScaleCounterA
#check @NumStability.Theorem20_7.rowScaleCounterRowMax
#check @NumStability.Theorem20_7.rowScaleCounter_pivot0
