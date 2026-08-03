import NumStability.Algorithms.HighamChapter10

/-!
# HighamChapter10 old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W03, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.kahanR
#check @NumStability.matMulVec_neg
#check @NumStability.opNorm2Le_add
