import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.ActualOutput

/-!
# R05 historical-only test — `ActualOutput`

Imports exactly the historical path; checks its preserved public
surface (6 declarations).
-/

#check @NumStability.Higham21SNEBackwardCoefficient_nonneg_of_gammaValid
#check @NumStability.gamma_le_Higham21SNEBackwardCoefficient
#check @NumStability.higham21SNEActualOutput
#check @NumStability.higham21SNEExactFormedOutput
#check @NumStability.higham21SNETransferredForwardEnvelope
#check @NumStability.higham21_sne_actual_output_formation_backward_error
