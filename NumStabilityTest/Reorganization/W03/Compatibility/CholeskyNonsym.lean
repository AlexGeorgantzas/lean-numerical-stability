import NumStability.Algorithms.Cholesky.CholeskyNonsym

/-!
# CholeskyNonsym old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W03, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.chiFactor
#check @NumStability.symmetricPart
#check @NumStability.IsNonsymPosDef
