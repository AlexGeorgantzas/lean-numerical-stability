import NumStability.Analysis.Perturbation.LeastSquares.WeightedLimit

/-!
# WeightedLimit canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.higham20WeightedSolution
#check @NumStability.lseWeightedMinimizer_energy_le_lagrange
#check @NumStability.lseWeightedMatrix_injective_of_lseStackedFullColumnRank
