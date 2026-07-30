import NumStability.Source.Higham.Chapter20.Equations.WeightedLimit

/-!
# Equations.WeightedLimit canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.vecNorm2Sq_lseStackedMatrix_mulVec
#check @NumStability.lseWeightedMinimizer_distance_le_sqrt_inv_sq
#check @NumStability.higham20WeightedSolution_isLeastSquaresMinimizer
