import NumStability.Algorithms.TestMatrices.Higham28ShiftedHilbert

/-!
# Higham28ShiftedHilbert old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.arctan_le_self_of_nonneg
#check @NumStability.div_one_add_sq_le_arctan
#check @NumStability.shiftedHilbertSchurKernel
