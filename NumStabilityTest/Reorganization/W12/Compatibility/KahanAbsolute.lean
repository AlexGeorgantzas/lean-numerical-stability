import NumStability.Algorithms.KahanAbsolute

/-!
# KahanAbsolute old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.decimal4HalfUlp
#check @NumStability.decimal4DisplaysAs
#check @NumStability.decimal4HalfUlp_pos
