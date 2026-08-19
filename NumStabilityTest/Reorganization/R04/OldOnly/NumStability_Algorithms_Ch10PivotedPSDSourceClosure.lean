import NumStability.Algorithms.Ch10PivotedPSDSourceClosure

/-!
# Ch10PivotedPSDSourceClosure old-path-only test (R04)

Imports only the historical path. Every declaration checked below moved to
a canonical destination during wave R04, so this compiles only if the
compatibility surface still re-exports it under its original name.
-/
#check @NumStability.higham10_14_actual_componentwise
#check @NumStability.higham10_14_completePivotedPSD_actual_of_noTies
#check @NumStability.higham10_14_completePivotedPSD_actual_source_closed
#check @NumStability.higham10_23_25_actual_trailing_from_stop
#check @NumStability.higham10_25_actual_backwardError_opNorm2
#check @NumStability.higham10_28_implies_10_27_actual_residualNorm
