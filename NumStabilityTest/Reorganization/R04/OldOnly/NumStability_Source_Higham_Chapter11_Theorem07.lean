import NumStability.Source.Higham.Chapter11.Theorem07

/-!
# Theorem07 old-path-only test (R04)

Imports only the historical path. Every declaration checked below moved to
a canonical destination during wave R04, so this compiles only if the
compatibility surface still re-exports it under its original name.
-/
#check @NumStability.Ch11Closure.TriGrowthInv.bunchTriGrowthC0
#check @NumStability.Ch11Closure.TriGrowthInv.growthBcorner_nonneg
#check @NumStability.Ch11Closure.TriGrowthInv.growthFactorConst_nonneg
#check @NumStability.Ch11Closure.TriGrowthInv.higham11_7_bunch_tridiagonal_actual_schedule_middle_solve
#check @NumStability.Ch11Closure.TriGrowthInv.higham11_7_bunch_tridiagonal_actual_schedule_sparse_solve
#check @NumStability.Ch11Closure.TriGrowthInv.higham11_7_bunch_tridiagonal_backward_error_growth_derived
#check @NumStability.Ch11Closure.TriGrowthInv.higham11_7_bunch_tridiagonal_backward_error_growth_derived_of_small
#check @NumStability.Ch11Closure.TriGrowthInv.higham11_7_bunch_tridiagonal_support_aware
#check @NumStability.Ch11Closure.TriGrowthInv.one_div_fifty_lt_bunchTridiagonalAlpha
#check @NumStability.Ch11Closure.TriGrowthInv.stages_le
