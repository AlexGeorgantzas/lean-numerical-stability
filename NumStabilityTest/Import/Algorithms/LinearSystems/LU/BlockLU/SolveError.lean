import NumStability.Algorithms.LinearSystems.LU.BlockLU.SolveError

/-!
# Block LU solve-error import smoke test

This test imports only the canonical solve-error leaf and checks all three
reviewed declarations.
-/

#check NumStability.dhsBlockForwardConventionalSolution
#check NumStability.dhsBlockForwardConventionalSolution_apply
#check NumStability.dhsBlockForwardConventionalSolution_flat
