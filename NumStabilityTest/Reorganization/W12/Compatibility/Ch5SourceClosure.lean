import NumStability.Algorithms.Ch5SourceClosure

/-!
# Ch5SourceClosure old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.highamBidiagonalUInv
#check @NumStability.flHighamBidiagonalDelta
#check @NumStability.flHighamBidiagonalSolve
