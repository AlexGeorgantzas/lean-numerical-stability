import NumStability.Source.Higham.Chapter02.Problem19.GradualUnderflowExactness.Basic

/-!
# Chapter02 Problem19 GradualUnderflowExactness Basic canonical-import test

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Analysis.HighamChapter2GradualUnderflowExact`
during wave W12 and must resolve from the canonical path alone.
-/

#check @NumStability.FloatingPointFormat.finiteSystem_add_finiteSystem_of_finiteUnderflowRange
#check @NumStability.FloatingPointFormat.finiteSystem_sub_finiteSystem_of_finiteUnderflowRange
#check @NumStability.FloatingPointFormat.finiteRoundToEvenOp_add_eq_exact_of_finiteUnderflowRange
