import NumStability.Source.Higham.Chapter05.Section03.ResidualUnwind.Basic

/-!
# Chapter05 Section03 ResidualUnwind Basic canonical-import test

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.Ch5SourceClosure`
during wave W12 and must resolve from the canonical path alone.
-/

#check @NumStability.flDividedDifferenceUnwindStep
#check @NumStability.flDividedDifferenceUnwindStep_abs_error
#check @NumStability.fl_dividedDifferenceStep_entry_inverse_gamma3
