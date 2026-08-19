import NumStability.Algorithms.Cholesky.HighamMathiasSource

/-!
# HighamMathiasSource old-path-only test (R04)

Imports only the historical path. Every declaration checked below moved to
a canonical destination during wave R04, so this compiles only if the
compatibility surface still re-exports it under its original name.
-/
#check @NumStability.higham10_29_source_lu_growth_bound_opNorm2
#check @NumStability.higham10_mathias_firstRoundedSchur_sourceCondition_exists
#check @NumStability.higham10_mathias_flSchur_runsToCompletion
#check @NumStability.higham10_mathias_luSchur_kappaH_le
#check @NumStability.higham10_mathias_luSchur_symPartInv_opNorm2_le
