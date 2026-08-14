import NumStability.Analysis.DoubleRounding

/-!
# R03 historical-only test — `DoubleRounding`

Imports exactly the historical path; checks its preserved public
surface (6 declarations).
-/

#check @NumStability.FloatingPointFormat.problem2_9_direct_double_ne_double_rounded_extended64
#check @NumStability.FloatingPointFormat.problem2_9_direct_double_rounds_to_predecessor
#check @NumStability.FloatingPointFormat.problem2_9_direct_double_sqrt_rounds_to_predecessor
#check @NumStability.FloatingPointFormat.problem2_9_double_rounding_from_extended64
#check @NumStability.FloatingPointFormat.problem2_9_double_rounds_extended_midpoint_to_one
#check @NumStability.FloatingPointFormat.problem2_9_extended64_rounds_to_double_midpoint
