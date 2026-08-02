import NumStability.Source.Higham.Chapter02.Problem01.FloatingPointCounts.Basic

/-!
# Chapter02 Problem01 FloatingPointCounts Basic canonical-import test

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Analysis.Counting`
during wave W12 and must resolve from the canonical path alone.
-/

#check @NumStability.FloatingPointFormat.signedParameterCount
#check @NumStability.FloatingPointFormat.subnormalValue_true_eq_iff
#check @NumStability.FloatingPointFormat.subnormalValue_false_eq_iff
