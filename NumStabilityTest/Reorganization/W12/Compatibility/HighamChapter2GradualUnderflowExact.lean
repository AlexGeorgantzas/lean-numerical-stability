import NumStability.Analysis.HighamChapter2GradualUnderflowExact

/-!
# HighamChapter2GradualUnderflowExact old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.FloatingPointFormat.finiteSystem_add_finiteSystem_of_finiteUnderflowRange
#check @NumStability.FloatingPointFormat.finiteSystem_sub_finiteSystem_of_finiteUnderflowRange
#check @NumStability.FloatingPointFormat.finiteRoundToEvenOp_add_eq_exact_of_finiteUnderflowRange
