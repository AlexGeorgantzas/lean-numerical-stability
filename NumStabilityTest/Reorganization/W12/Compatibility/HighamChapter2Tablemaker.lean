import NumStability.Analysis.HighamChapter2Tablemaker

/-!
# HighamChapter2Tablemaker old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.Higham2LindemannExpProperty
#check @NumStability.higham2_lindemann_exp_not_machine_or_midpoint
#check @NumStability.FloatingPointFormat.finiteSystem_exists_ratCast
