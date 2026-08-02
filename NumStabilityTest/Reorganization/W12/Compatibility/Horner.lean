import NumStability.Algorithms.Horner

/-!
# Horner old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.matAdd
#check @NumStability.polyAsc
#check @NumStability.polyDesc
