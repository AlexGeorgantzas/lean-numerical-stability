import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations

/-!
# NormalEquations canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.RectLSNormalEquations
#check @NumStability.lsAplusOfGramNonsingInv
#check @NumStability.RectLSNormalEquations.of_permuteCols
