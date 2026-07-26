import NumStability.Algorithms.Underdetermined.Higham21RowwiseMeasure

/-!
# Historical Algorithms Chapter 21 row-wise backward-error import smoke test

This test deliberately imports only the historical forwarding path.
-/

#check NumStability.Higham21RowwiseBackwardErrorFeasible
#check NumStability.higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate
#check NumStability.higham21_theorem21_4_computed_qhat_omegaR_le_gamma
