import NumStability.Algorithms.Underdetermined.Higham21SNEClosure

/-!
# R05 historical-only test — `Higham21SNEClosure`

Imports exactly the historical path; checks its preserved public
surface (5 declarations).
-/

#check @NumStability.higham21_sne_householder_actual_output_source_finite_quadratic_bound
#check @NumStability.higham21_sne_householder_actual_output_source_forward_finite_bound
#check @NumStability.higham21_sne_householder_actual_output_source_forward_relative_finite
#check @NumStability.higham21_sne_householder_direction_radius_transfers
#check @NumStability.higham21_sne_householder_reference_forward_error_closed_direction_radius
