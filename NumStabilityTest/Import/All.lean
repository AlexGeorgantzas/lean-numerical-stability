import NumStability.All

/-!
# Complete-tree entry-point smoke test

The explicit `All` entry point must retain reusable algorithms as well as the
source-correspondence corpus.
-/

namespace NumStabilityTest.All

noncomputable section

example :
    (fp : NumStability.FPModel) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
  NumStability.fl_recursiveSum

#check NumStability.not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid
#check NumStability.higham14_hadamardConditionNumberRaw_negative_one_counterexample
#check NumStability.fl_noGuardDotProduct
#check NumStability.higham20_eq20_32_Bplus_residual_eq_crossProjection
#check NumStability.problem44_outputs_exactly_Icc
#check NumStability.higham17_problem17_1
#check NumStability.StrassenRecurrence
#check NumStability.higham23_problem23_8_power_exponent
#check NumStability.higham26ADCrudeSweep_nondecreasing

end

end NumStabilityTest.All
