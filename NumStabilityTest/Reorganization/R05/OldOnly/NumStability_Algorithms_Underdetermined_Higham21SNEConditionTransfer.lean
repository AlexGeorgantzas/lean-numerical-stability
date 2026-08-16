import NumStability.Algorithms.Underdetermined.Higham21SNEConditionTransfer

/-!
# R05 historical-only test — `Higham21SNEConditionTransfer`

Imports exactly the historical path; checks its preserved public
surface (3 declarations).
-/

#check @NumStability.higham21_sne_cond2_mul_solution_norm_le_direction_radius
#check @NumStability.higham21_sne_dual_solution_difference_vecNorm2_le_direction_radius
#check @NumStability.higham21_sne_primal_solution_difference_vecNorm2_le_direction_radius
