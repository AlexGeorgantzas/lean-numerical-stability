import NumStability.Algorithms.LeastSquares.Higham20WeightedLimit

/-!
# Higham20WeightedLimit historical import smoke test

Imports only the historical path, proving the retained compatibility
wrapper still resolves its original declarations.
-/

#check @NumStability.higham20WeightedSolution
#check @NumStability.vecNorm2Sq_lseStackedMatrix_mulVec
#check @NumStability.lseWeightedMinimizer_energy_le_lagrange
