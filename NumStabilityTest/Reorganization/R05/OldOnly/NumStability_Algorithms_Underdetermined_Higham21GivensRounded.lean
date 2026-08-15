import NumStability.Algorithms.Underdetermined.Higham21GivensRounded

/-!
# R05 historical-only test — `Higham21GivensRounded`

Imports exactly the historical path; checks its preserved public
surface (5 declarations).
-/

#check @NumStability.higham21_q_method_fixed_accumulation_rowwise_backward_stable
#check @NumStability.higham21_theorem21_4_givens_stored_replay_omegaR_le
#check @NumStability.higham21_theorem21_4_givens_stored_replay_omegaR_le_of_bridge
#check @NumStability.higham21_theorem21_4_givens_stored_replay_rowwise_backward_stable
#check @NumStability.higham21_theorem21_4_givens_stored_replay_rowwise_of_bridge
