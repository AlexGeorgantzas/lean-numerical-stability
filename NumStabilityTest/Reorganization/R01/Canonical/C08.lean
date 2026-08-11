import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.BlockForm.ProjectorLimit

/-!
# R01 canonical-only import test C08

Imports exactly the frozen canonical leaf `NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.BlockForm.ProjectorLimit` and checks every public declaration routed there.
-/

#check NumStability.G_fixes_oneEigenProjector_apply
#check NumStability.G_mul_oneEigenProjector_eq
#check NumStability.J_mul_topProjector
#check NumStability.conjugate_matMul
#check NumStability.eq_conjugate_of_similarity
#check NumStability.matMul_row_id
#check NumStability.matMul_row_zero
#check NumStability.matPow_G_tendsto_oneEigenProjector
#check NumStability.matPow_J_bottom_row_sum
#check NumStability.matPow_J_top_entry
#check NumStability.matSub_id_semiconvergentE
#check NumStability.oneEigenProjector
#check NumStability.oneEigenProjector_idempotent
#check NumStability.semiconvergentE
#check NumStability.topProjector
#check NumStability.topProjector_apply_bottom
#check NumStability.topProjector_apply_top
#check NumStability.topProjector_idempotent
#check NumStability.topProjector_mul_J
