import NumStability.Algorithms.KahanCompensatedFiniteFormat

/-!
# Historical Kahan finite-format import smoke test
-/

#check NumStability.kahanFF_model
#check NumStability.kahanFF_step_exact
#check NumStability.kahanFF_kahan_correctionSub_exact
#check NumStability.kahanFF_kahanSum_backward_error
#check NumStability.kahanFF_kahanSum_forward_error
#check NumStability.kahanFF_alternativeCompensatedSum_backward_error
