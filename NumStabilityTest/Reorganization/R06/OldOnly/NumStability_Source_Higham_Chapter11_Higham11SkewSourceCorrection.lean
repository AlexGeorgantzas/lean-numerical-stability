import NumStability.Source.Higham.Chapter11.Higham11SkewSourceCorrection

/-!
# R06 historical-only test — `Higham11SkewSourceCorrection`

Imports exactly the historical path; checks its preserved public
surface (10 declarations).
-/

#check @NumStability.higham11_9_coupled_skew_schur_entry_bound
#check @NumStability.higham11_9_globalMaxPivot_bounds_both_multipliers
#check @NumStability.higham11_9_printed_twoColumn_search_does_not_bound_multipliers
#check @NumStability.higham11_9_twoColumnCounterexample
#check @NumStability.higham11_9_twoColumnCounterexampleInv
#check @NumStability.higham11_9_twoColumnCounterexample_argmax
#check @NumStability.higham11_9_twoColumnCounterexample_mul_inv
#check @NumStability.higham11_9_twoColumnCounterexample_nonsingular
#check @NumStability.higham11_9_twoColumnCounterexample_pivotMagnitude
#check @NumStability.higham11_9_twoColumnCounterexample_skew
