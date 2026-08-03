import NumStability.Algorithms.Ch10KahanSharpness

/-!
# Ch10KahanSharpness old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W03, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.kahanR_above
#check @NumStability.kahanR_below
#check @NumStability.higham10KahanW
