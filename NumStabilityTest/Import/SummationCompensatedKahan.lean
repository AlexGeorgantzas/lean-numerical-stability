import NumStability.Algorithms.Summation.Compensated.Kahan

/-!
# Kahan reusable-family smoke test

This test imports only the declaration-free Kahan aggregate and checks
representatives from execution, finite arithmetic, both coefficient engines,
exactness, and error-bound layers.
-/

#check NumStability.fl_kahanSum
#check NumStability.finiteKahanState
#check NumStability.KahanAffineCoeffStep
#check NumStability.KahanCoupledCoeffStep
#check NumStability.fl_kahanFinalCorrectedSum_exactWithUnitRoundoff
#check NumStability.fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_tail_order_range
#check NumStability.kahanFF_kahan_correctionSub_exact
