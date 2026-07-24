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
#check NumStability.higham12_problem12_2_two_step_recurrence
#check NumStability.higham13_demmel_sharp_multiplier_of_spectral_interval
#check NumStability.Ch22B.ch22b_refinement_converges_via_ch12
#check NumStability.higham27_problem27_6_cubic_error_bound
#check NumStability.StrassenRecurrence
#check NumStability.higham23_problem23_8_power_exponent
#check NumStability.higham26ADCrudeSweep_nondecreasing
#check NumStability.higham14SchulzStep
#check NumStability.Ch14Ext.ch14ext_schulzIter_tendsto_inverse_of_lt_two_div_norm_sq

end

end NumStabilityTest.All
