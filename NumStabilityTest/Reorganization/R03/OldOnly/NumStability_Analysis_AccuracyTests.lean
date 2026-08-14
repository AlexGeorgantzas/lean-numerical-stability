import NumStability.Analysis.AccuracyTests

/-!
# R03 historical-only test — `AccuracyTests`

Imports exactly the historical path; checks its preserved public
surface (5 declarations).
-/

#check @NumStability.codySineReducedArgument_sineTaylorOdd5_abs_error_lt_one_e20
#check @NumStability.codySineTaylorOdd5_displayedMagnitude_abs_error_lt_41e21
#check @NumStability.codySineTestExact_displayedTableDecimal17_abs_error_lt_half_last_place
#check @NumStability.codySineTestExact_sineTaylorOdd5_abs_error_lt_one_e20
#check @NumStability.sineTaylorOdd5_abs_error_le_next
