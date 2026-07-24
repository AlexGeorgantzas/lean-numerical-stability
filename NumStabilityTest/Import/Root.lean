import NumStability

/-!
# Root import compatibility smoke test

`import NumStability` historically exposes the floating-point model, analysis
definitions, and algorithms.  Keep this test while the curated `Core`,
`Higham`, and `All` entry points are introduced so that migration work does not
silently narrow the existing root import.
-/

namespace NumStabilityTest.Root

open NumStability

noncomputable section

-- Representative declarations from each of the three legacy umbrella imports.
example : Type := FPModel

example : ℝ → ℝ → ℝ := absError

example : (fp : FPModel) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
  fl_recursiveSum

#check not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid
#check higham14_hadamardConditionNumberRaw_negative_one_counterexample
#check fl_noGuardDotProduct
#check higham20_eq20_32_Bplus_residual_eq_crossProjection
#check problem44_outputs_exactly_Icc
#check higham17_problem17_1
#check higham12_problem12_2_two_step_recurrence
#check higham13_demmel_sharp_multiplier_of_spectral_interval
#check Ch22B.ch22b_refinement_converges_via_ch12
#check higham27_problem27_6_cubic_error_bound
#check StrassenRecurrence
#check higham23_problem23_8_power_exponent
#check higham26ADCrudeSweep_nondecreasing

end

end NumStabilityTest.Root
