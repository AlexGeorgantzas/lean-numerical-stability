import NumStability.Analysis.Perturbation.LeastSquares.BackwardError

/-!
# BackwardError canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.LSQRSolveBackwardError
#check @NumStability.LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations
#check @NumStability.LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations_normBudget
