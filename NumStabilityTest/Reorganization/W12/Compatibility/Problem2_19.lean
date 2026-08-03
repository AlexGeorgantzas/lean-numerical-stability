import NumStability.Analysis.Problem2_19

/-!
# Problem2_19 old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.FloatingPointFormat.problem2_19_roundedSqrtSquare
#check @NumStability.FloatingPointFormat.problem2_19_sqrt_square_eq_abs_of_finiteSystem
#check @NumStability.FloatingPointFormat.problem2_19_first_requirement_holds_second_fails
