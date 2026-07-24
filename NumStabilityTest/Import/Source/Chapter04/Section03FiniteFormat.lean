import NumStability.Source.Higham.Chapter04.Section03.FiniteFormat

/-!
# Higham section 4.3 finite-format aggregate smoke test
-/

#check NumStability.kahanFF_model
#check NumStability.kahanFF_step_exact
#check NumStability.kahanFF_kahan_correctionSub_exact
#check NumStability.kahanFF_kahanSum_backward_error
#check NumStability.kahanFF_kahanSum_forward_error
#check NumStability.kahanFF_alternativeCompensatedSum_backward_error
