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
#check higham14SchulzStep
#check Ch14Ext.ch14ext_schulzIter_tendsto_inverse_of_lt_two_div_norm_sq
#check FloatingPointFormat.problem2_2_lemma2_1_spacing_bounds
#check ch14ext_problem14_13_gej_bound_fin_one
#check Ch14Ext.ch14ext_hyman_flDet_backward_error_original
#check higham21Cond2With_row_scaling
#check higham21_theorem21_3_exact_attainment_or_pairing_obstruction
#check Ch14Ext.ch14ext_singularValue_abs_sub_le_of_euclideanLin_diff_bound
#check Ch14Ext.ch14ext_problem14_15_det_add_rel_le_of_kappa2_opNorm2_inv_card_guard
#check higham21_theorem21_4_computed_qhat_omegaR_le_gamma
#check higham28NormalizedHilbertDet_tendsto_atTop
#check higham28_not_HilbertDetAsymptotic
#check integral_abs_standardGaussian_difference
#check MeasureTheory.measure_eq_of_invariant_probability_of_pretransitive
#check ieeeNaiveMax_not_nan_propagating
#check problem2_22_guard_digit_a_sub_b_exact
#check complexMatrixLpNorm
#check HighamProblem61NormQuotientWitness
#check highamProblem65MonomialMatrix
#check highamProblem69_frobenius_op2_bounds
#check complexMatrixBlockShearOp2_eq_highamProblem610_sourceFormula
#check mixedInverseAmbientRelativeAmplificationRadiusSup_tendsto_conditionNumberProduct_of_positive_radii
#check problem2_11_decimalLeadingDigit
#check problem2_11EmpiricalSource
#check higham2_power_decimalLeadingDigit_frequency_tendsto

end

end NumStabilityTest.Root
