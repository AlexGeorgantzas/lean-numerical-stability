import NumStability.Source.Higham.Chapter05.Section01.RelativeError.Basic

/-!
# Chapter05 Section01 RelativeError Basic canonical-import test

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Horner`
during wave W12 and must resolve from the canonical path alone.
-/

#check @NumStability.relErrorCounter_one
#check @NumStability.relErrorCounter_one_add
#check @NumStability.fl_rootProductEval_forward_error_bound
