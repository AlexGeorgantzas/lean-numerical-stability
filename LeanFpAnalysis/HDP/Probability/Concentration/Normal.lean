import LeanFpAnalysis.HDP.Probability.Concentration.Chernoff
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Normal Tails

Gaussian tail estimates and truncated-moment identities from HDP Chapter 2,
Section 2.1.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace LeanFpAnalysis.HDP

section StandardNormalTail

/-- The normalizing constant in the standard normal density. -/
def standardNormalConstant : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹

@[simp]
lemma standardNormalConstant_nonneg : 0 ≤ standardNormalConstant := by
  dsimp [standardNormalConstant]
  positivity

lemma standardNormalDensity_nonneg (x : ℝ) :
    0 ≤ standardNormalDensity x :=
  ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x

/-- The standard normal tail probability as the integral over the open tail.
The endpoint has zero Lebesgue measure. -/
theorem standardNormal_tail_real_eq_integral_Ioi (t : ℝ) :
    standardNormalMeasure.real (Set.Ici t) =
      ∫ x in Set.Ioi t, standardNormalDensity x := by
  have htail := standardNormal_tail_eq_integral t
  have h_nonneg :
      0 ≤ ∫ x in Set.Ici t, standardNormalDensity x := by
    exact integral_nonneg fun x => standardNormalDensity_nonneg x
  rw [measureReal_def, htail, ENNReal.toReal_ofReal h_nonneg]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]

/-- Elementary improper integral used in Mills' upper bound. -/
lemma integral_Ioi_mul_exp_neg_sq_half (t : ℝ) :
    ∫ x in Set.Ioi t, x * Real.exp (-(x ^ 2) / 2) =
      Real.exp (-(t ^ 2) / 2) := by
  let F : ℝ → ℝ := fun x => -Real.exp (-(x ^ 2) / 2)
  have hderiv :
      ∀ x ∈ Set.Ioi t, HasDerivAt F (x * Real.exp (-(x ^ 2) / 2)) x := by
    intro x _hx
    dsimp [F]
    have hinner : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
      convert ((hasDerivAt_pow 2 x).neg.div_const 2) using 1
      ring_nf
    convert hinner.exp.neg using 1
    ring_nf
  have hcont : ContinuousWithinAt F (Set.Ici t) t := by
    dsimp [F]
    fun_prop
  have hint :
      IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) (Set.Ioi t) := by
    have hglobal :
        Integrable (fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
      integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    refine hglobal.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro x _hx
    ring_nf
  have htend : Tendsto F atTop (𝓝 0) := by
    dsimp [F]
    have hinner : Tendsto (fun x : ℝ => -(x ^ 2) / 2) atTop atBot := by
      have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
        Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
      have hmul :
          Tendsto (fun x : ℝ => (-(1 / 2 : ℝ)) * (x ^ 2)) atTop atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg
          (by norm_num : (-(1 / 2 : ℝ)) < 0) hsq
      convert hmul using 1
      ring_nf
    simpa using (Real.tendsto_exp_atBot.comp hinner).neg
  have h :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      hcont hderiv hint htend
  simpa [F] using h

/-- Integrability of the second truncated Gaussian moment integrand. -/
lemma integrableOn_sq_mul_exp_neg_sq_half_of_one_le
    {t : ℝ} (ht : 1 ≤ t) :
    IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / 2))
      (Set.Ioi t) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hbase :
      IntegrableOn
        (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
        (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 2)
  have hmono :
      IntegrableOn
        (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
        (Set.Ioi t) :=
    hbase.mono_set fun x hx => ht0.trans_lt hx
  refine hmono.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := ht0.trans_lt hx
  change
    x ^ (2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
      x ^ (2 : ℕ) * Real.exp (-(x ^ 2) / 2)
  rw [Real.rpow_two]
  ring_nf

/-- HDP Exercise 2.1.4, integration-by-parts identity before inserting the
normalizing constant. -/
lemma integral_Ioi_sq_mul_exp_neg_sq_half_of_one_le
    {t : ℝ} (ht : 1 ≤ t) :
    ∫ x in Set.Ioi t, x ^ 2 * Real.exp (-(x ^ 2) / 2) =
      t * Real.exp (-(t ^ 2) / 2) +
        ∫ x in Set.Ioi t, Real.exp (-(x ^ 2) / 2) := by
  let F : ℝ → ℝ := fun x => -(x * Real.exp (-(x ^ 2) / 2))
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hsq_int :
      IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / 2))
        (Set.Ioi t) :=
    integrableOn_sq_mul_exp_neg_sq_half_of_one_le ht
  have hexp_int :
      IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2))
        (Set.Ioi t) := by
    have hglobal :
        Integrable (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    refine hglobal.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro x _hx
    ring_nf
  have hderiv :
      ∀ x ∈ Set.Ioi t,
        HasDerivAt F ((x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2)) x := by
    intro x _hx
    dsimp [F]
    have hxderiv : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have hexp :
        HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
          (-x * Real.exp (-(x ^ 2) / 2)) x := by
      have hinner : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
        convert ((hasDerivAt_pow 2 x).neg.div_const 2) using 1
        ring_nf
      convert hinner.exp using 1
      ring_nf
    convert (hxderiv.mul hexp).neg using 1
    ring
  have hcont : ContinuousWithinAt F (Set.Ici t) t := by
    dsimp [F]
    fun_prop
  have hderiv_int :
      IntegrableOn (fun x : ℝ => (x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2))
        (Set.Ioi t) := by
    have hsub : IntegrableOn
        (fun x : ℝ =>
          x ^ 2 * Real.exp (-(x ^ 2) / 2) -
            Real.exp (-(x ^ 2) / 2))
        (Set.Ioi t) :=
      hsq_int.sub hexp_int
    refine hsub.congr_fun ?_ measurableSet_Ioi
    intro x _hx
    ring
  have htend : Tendsto F atTop (𝓝 0) := by
    dsimp [F]
    have hbase :
        Tendsto (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) atTop (𝓝 0) := by
      have hsmall :
          (fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
            =o[atTop] fun x : ℝ => Real.exp (-((1 / 2 : ℝ) * x)) :=
        by
          simpa [Real.rpow_one] using
            (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
              (by norm_num : (0 : ℝ) < 1 / 2) (1 : ℝ))
      have hexp_zero :
          Tendsto (fun x : ℝ => Real.exp (-((1 / 2 : ℝ) * x))) atTop (𝓝 0) := by
        have hlin :
            Tendsto (fun x : ℝ => -((1 / 2 : ℝ) * x)) atTop atBot := by
          convert
            Filter.Tendsto.const_mul_atTop_of_neg
              (by norm_num : (-(1 / 2 : ℝ)) < 0) tendsto_id using 1
          ext x
          simp
        exact Real.tendsto_exp_atBot.comp hlin
      have hzero :=
        hsmall.tendsto_zero_of_tendsto hexp_zero
      simpa [Real.rpow_one, one_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hzero
    simpa using hbase.neg
  have h :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      hcont hderiv hderiv_int htend
  have h' :
      ∫ x in Set.Ioi t, (x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2) =
        t * Real.exp (-(t ^ 2) / 2) := by
    calc
      ∫ x in Set.Ioi t, (x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2)
          = 0 - F t := h
      _ = t * Real.exp (-(t ^ 2) / 2) := by simp [F]
  have hsub :
      ∫ x in Set.Ioi t,
          (x ^ 2 * Real.exp (-(x ^ 2) / 2) -
            Real.exp (-(x ^ 2) / 2)) =
        t * Real.exp (-(t ^ 2) / 2) := by
    rw [← h']
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x _hx
    ring
  have hsub' :
      (∫ x in Set.Ioi t, x ^ 2 * Real.exp (-(x ^ 2) / 2)) -
          ∫ x in Set.Ioi t, Real.exp (-(x ^ 2) / 2) =
        t * Real.exp (-(t ^ 2) / 2) := by
    rw [← MeasureTheory.integral_sub hsq_int hexp_int]
    simpa using hsub
  linarith

/-- The density integral over the upper tail is bounded by Mills' elementary
upper estimate. -/
theorem standardNormal_tail_integral_le_mills_upper
    {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioi t, standardNormalDensity x
      ≤ (1 / t) * standardNormalConstant * Real.exp (-(t ^ 2) / 2) := by
  let f : ℝ → ℝ := fun x => standardNormalDensity x
  let g : ℝ → ℝ :=
    fun x => (1 / t) * standardNormalConstant *
      (x * Real.exp (-(x ^ 2) / 2))
  have hf_int : IntegrableOn f (Set.Ioi t) := by
    have hglobal :
        Integrable (fun x : ℝ =>
          standardNormalConstant * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
        standardNormalConstant
    refine hglobal.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro x _hx
    dsimp [f]
    rw [standardNormalDensity_eq]
    dsimp [standardNormalConstant]
    congr 1
    ring_nf
  have hg_int : IntegrableOn g (Set.Ioi t) := by
    have hbase :
        IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) (Set.Ioi t) := by
      have hglobal :
          Integrable (fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
        integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      refine hglobal.integrableOn.congr_fun ?_ measurableSet_Ioi
      intro x _hx
      ring_nf
    simpa [g, mul_assoc] using
      (hbase.const_mul ((1 / t) * standardNormalConstant))
  have hpoint : ∀ x ∈ Set.Ioi t, f x ≤ g x := by
    intro x hx
    have hxpos : 0 < x := ht.trans hx
    have htx : t ≤ x := hx.le
    have hone_le : 1 ≤ x / t := by
      rw [le_div_iff₀ ht]
      simpa using htx
    have hexp_nonneg : 0 ≤ Real.exp (-(x ^ 2) / 2) := (Real.exp_pos _).le
    have hconst_nonneg : 0 ≤ standardNormalConstant := standardNormalConstant_nonneg
    calc
      f x = standardNormalConstant * Real.exp (-(x ^ 2) / 2) := by
        simp [f, standardNormalDensity_eq, standardNormalConstant]
      _ ≤ (x / t) * standardNormalConstant * Real.exp (-(x ^ 2) / 2) := by
        have hmul :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hone_le hconst_nonneg)
            hexp_nonneg
        simpa [mul_assoc] using hmul
      _ = g x := by
        simp [g]
        field_simp [ne_of_gt ht]
  calc
    ∫ x in Set.Ioi t, standardNormalDensity x = ∫ x in Set.Ioi t, f x := rfl
    _ ≤ ∫ x in Set.Ioi t, g x :=
      MeasureTheory.setIntegral_mono_on hf_int hg_int measurableSet_Ioi hpoint
    _ = (1 / t) * standardNormalConstant * Real.exp (-(t ^ 2) / 2) := by
      rw [show (∫ x in Set.Ioi t, g x) =
          ((1 / t) * standardNormalConstant) *
            ∫ x in Set.Ioi t, x * Real.exp (-(x ^ 2) / 2) by
        simp [g, MeasureTheory.integral_const_mul, mul_assoc]]
      rw [integral_Ioi_mul_exp_neg_sq_half]

/-- Integrability of the sign-changing derivative used in Mills' lower bound. -/
lemma integrableOn_one_sub_three_div_pow_four_mul_exp_neg_sq_half
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn
      (fun x : ℝ => (1 - 3 / x ^ 4) * Real.exp (-(x ^ 2) / 2))
      (Set.Ioi t) := by
  let C : ℝ := 1 + 3 / t ^ 4
  have hbase :
      IntegrableOn (fun x : ℝ => C * Real.exp (-(x ^ 2) / 2))
        (Set.Ioi t) := by
    have hglobal :
        Integrable (fun x : ℝ => C * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
    refine hglobal.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro x _hx
    ring_nf
  change
    Integrable (fun x : ℝ => (1 - 3 / x ^ 4) * Real.exp (-(x ^ 2) / 2))
      (volume.restrict (Set.Ioi t))
  change
    Integrable (fun x : ℝ => C * Real.exp (-(x ^ 2) / 2))
      (volume.restrict (Set.Ioi t)) at hbase
  refine hbase.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := ht.trans hx
  have hxpow_le : t ^ 4 ≤ x ^ 4 := by
    exact pow_le_pow_left₀ ht.le hx.le 4
  have ht4pos : 0 < t ^ 4 := pow_pos ht 4
  have hx4pos : 0 < x ^ 4 := pow_pos hxpos 4
  have hdiv_le : 3 / x ^ 4 ≤ 3 / t ^ 4 := by
    have hinv : (x ^ 4)⁻¹ ≤ (t ^ 4)⁻¹ :=
      (inv_le_inv₀ hx4pos ht4pos).2 hxpow_le
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 3))
  have hdiv_nonneg : 0 ≤ 3 / x ^ 4 := by positivity
  have habs :
      |1 - 3 / x ^ 4| ≤ 1 + 3 / x ^ 4 := by
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
  have hcoeff : |1 - 3 / x ^ 4| ≤ C := by
    calc
      |1 - 3 / x ^ 4| ≤ 1 + 3 / x ^ 4 := habs
      _ ≤ 1 + 3 / t ^ 4 := by linarith
      _ = C := rfl
  have hexp_nonneg : 0 ≤ Real.exp (-(x ^ 2) / 2) := (Real.exp_pos _).le
  calc
    ‖(1 - 3 / x ^ 4) * Real.exp (-(x ^ 2) / 2)‖
        = |(1 - 3 / x ^ 4) * Real.exp (-(x ^ 2) / 2)| := rfl
    _ = |1 - 3 / x ^ 4| * Real.exp (-(x ^ 2) / 2) := by
      rw [abs_mul, abs_of_nonneg hexp_nonneg]
    _ ≤ C * Real.exp (-(x ^ 2) / 2) :=
      mul_le_mul_of_nonneg_right hcoeff hexp_nonneg

/-- The integration-by-parts identity used for the lower Mills bound. -/
lemma integral_Ioi_one_sub_three_div_pow_four_mul_exp_neg_sq_half
    {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioi t, (1 - 3 / x ^ 4) * Real.exp (-(x ^ 2) / 2) =
      (1 / t - 1 / t ^ 3) * Real.exp (-(t ^ 2) / 2) := by
  let F : ℝ → ℝ :=
    fun x => -((1 / x - 1 / x ^ 3) * Real.exp (-(x ^ 2) / 2))
  have hderiv :
      ∀ x ∈ Set.Ioi t,
        HasDerivAt F ((1 - 3 / x ^ 4) * Real.exp (-(x ^ 2) / 2)) x := by
    intro x hx
    have hxpos : 0 < x := ht.trans hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    dsimp [F]
    have hcoef :
        HasDerivAt (fun y : ℝ => 1 / y - 1 / y ^ 3)
          (-1 / x ^ 2 + 3 / x ^ 4) x := by
      have h₁ : HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
        convert hasDerivAt_inv hxne using 1
        · ext y
          simp [one_div]
        · simp [div_eq_mul_inv]
      have h₂ : HasDerivAt (fun y : ℝ => 1 / y ^ 3) (-3 / x ^ 4) x := by
        have hpow : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
          convert hasDerivAt_pow 3 x using 1
        have h_inv := hpow.inv (pow_ne_zero 3 hxne)
        convert h_inv using 1
        · ext y
          simp [one_div]
        · field_simp [hxne]
      convert h₁.sub h₂ using 1
      ring
    have hexp :
        HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
          (-x * Real.exp (-(x ^ 2) / 2)) x := by
      have hinner : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
        convert ((hasDerivAt_pow 2 x).neg.div_const 2) using 1
        ring_nf
      convert hinner.exp using 1
      ring_nf
    convert (hcoef.mul hexp).neg using 1
    field_simp [hxne]
    ring
  have hcont : ContinuousWithinAt F (Set.Ici t) t := by
    dsimp [F]
    have htne : t ≠ 0 := ne_of_gt ht
    have ht3ne : t ^ 3 ≠ 0 := pow_ne_zero 3 htne
    have hct : ContinuousAt (fun x : ℝ =>
        -((1 / x - 1 / x ^ 3) * Real.exp (-(x ^ 2) / 2))) t := by
      fun_prop (disch := assumption)
    exact hct.continuousWithinAt
  have hint :
      IntegrableOn
        (fun x : ℝ => (1 - 3 / x ^ 4) * Real.exp (-(x ^ 2) / 2))
        (Set.Ioi t) :=
    integrableOn_one_sub_three_div_pow_four_mul_exp_neg_sq_half ht
  have htend : Tendsto F atTop (𝓝 0) := by
    dsimp [F]
    have hcoef :
        Tendsto (fun x : ℝ => 1 / x - 1 / x ^ 3) atTop (𝓝 (0 - 0)) := by
      have h1 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
        simpa [one_div] using
          (Filter.Tendsto.const_div_atTop (𝕜 := ℝ) tendsto_id (1 : ℝ))
      have hpow3 : Tendsto (fun x : ℝ => x ^ 3) atTop atTop :=
        Filter.tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)
      have h3 : Tendsto (fun x : ℝ => 1 / x ^ 3) atTop (𝓝 0) := by
        simpa [one_div] using
          (Filter.Tendsto.const_div_atTop (𝕜 := ℝ) hpow3 (1 : ℝ))
      exact h1.sub h3
    have hexp :
        Tendsto (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) atTop (𝓝 0) := by
      have hinner : Tendsto (fun x : ℝ => -(x ^ 2) / 2) atTop atBot := by
        have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
          Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
        have hmul :
            Tendsto (fun x : ℝ => (-(1 / 2 : ℝ)) * (x ^ 2)) atTop atBot :=
          Filter.Tendsto.const_mul_atTop_of_neg
            (by norm_num : (-(1 / 2 : ℝ)) < 0) hsq
        convert hmul using 1
        ring_nf
      simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp hinner
    have hprod :
        Tendsto
          (fun x : ℝ =>
            (1 / x - 1 / x ^ 3) * Real.exp (-(x ^ 2) / 2))
          atTop (𝓝 ((0 - 0) * 0)) :=
      hcoef.mul hexp
    simpa using hprod.neg
  have h :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      hcont hderiv hint htend
  simpa [F, sub_eq_add_neg, one_div] using h

/-- The density integral over the upper tail is bounded below by Mills'
elementary lower estimate. -/
theorem mills_lower_le_standardNormal_tail_integral
    {t : ℝ} (ht : 0 < t) :
    (1 / t - 1 / t ^ 3) * standardNormalConstant *
        Real.exp (-(t ^ 2) / 2)
      ≤ ∫ x in Set.Ioi t, standardNormalDensity x := by
  by_cases ht_le_one : t ≤ 1
  · have hcoeff : 1 / t - 1 / t ^ 3 ≤ 0 := by
      have htpos : 0 < t := ht
      have ht_sq_le_one : t ^ 2 ≤ 1 := by nlinarith [mul_le_mul ht_le_one ht_le_one ht.le (by norm_num : (0 : ℝ) ≤ 1)]
      have hle : 1 / t ≤ 1 / t ^ 3 := by
        rw [one_div, one_div]
        have ht3pos : 0 < t ^ 3 := pow_pos ht 3
        have ht_le_t3 : t ^ 3 ≤ t := by
          nlinarith [mul_nonneg ht.le ht.le, ht_sq_le_one]
        exact (inv_le_inv₀ ht ht3pos).2 ht_le_t3
      linarith
    have hfactor_nonneg :
        0 ≤ standardNormalConstant * Real.exp (-(t ^ 2) / 2) :=
      mul_nonneg standardNormalConstant_nonneg (Real.exp_pos _).le
    have hleft_nonpos :
        (1 / t - 1 / t ^ 3) *
            (standardNormalConstant * Real.exp (-(t ^ 2) / 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoeff hfactor_nonneg
    have htail_nonneg :
        0 ≤ ∫ x in Set.Ioi t, standardNormalDensity x :=
      integral_nonneg fun x => standardNormalDensity_nonneg x
    calc
      (1 / t - 1 / t ^ 3) * standardNormalConstant *
          Real.exp (-(t ^ 2) / 2)
          = (1 / t - 1 / t ^ 3) *
              (standardNormalConstant * Real.exp (-(t ^ 2) / 2)) := by ring
      _ ≤ 0 := hleft_nonpos
      _ ≤ ∫ x in Set.Ioi t, standardNormalDensity x := htail_nonneg
  · have hone_lt : 1 < t := lt_of_not_ge ht_le_one
    let f : ℝ → ℝ := fun x => standardNormalDensity x
    let g : ℝ → ℝ :=
      fun x => standardNormalConstant *
        ((1 - 3 / x ^ 4) * Real.exp (-(x ^ 2) / 2))
    have hf_int : IntegrableOn f (Set.Ioi t) := by
      have hglobal :
          Integrable (fun x : ℝ =>
            standardNormalConstant * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
        (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
          standardNormalConstant
      refine hglobal.integrableOn.congr_fun ?_ measurableSet_Ioi
      intro x _hx
      dsimp [f]
      rw [standardNormalDensity_eq]
      dsimp [standardNormalConstant]
      congr 1
      ring_nf
    have hg_int : IntegrableOn g (Set.Ioi t) :=
      (integrableOn_one_sub_three_div_pow_four_mul_exp_neg_sq_half ht).const_mul
        standardNormalConstant
    have hpoint : ∀ x ∈ Set.Ioi t, g x ≤ f x := by
      intro x hx
      have hxpos : 0 < x := ht.trans hx
      have hfrac_nonneg : 0 ≤ 3 / x ^ 4 := by positivity
      have hcoeff_le : 1 - 3 / x ^ 4 ≤ 1 := by linarith
      have hexp_nonneg : 0 ≤ Real.exp (-(x ^ 2) / 2) := (Real.exp_pos _).le
      calc
        g x = standardNormalConstant *
            ((1 - 3 / x ^ 4) * Real.exp (-(x ^ 2) / 2)) := rfl
        _ ≤ standardNormalConstant *
            (1 * Real.exp (-(x ^ 2) / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ standardNormalConstant_nonneg
          exact mul_le_mul_of_nonneg_right hcoeff_le hexp_nonneg
        _ = f x := by
          simp [f, standardNormalDensity_eq, standardNormalConstant]
    calc
      (1 / t - 1 / t ^ 3) * standardNormalConstant *
          Real.exp (-(t ^ 2) / 2)
          = standardNormalConstant *
              ((1 / t - 1 / t ^ 3) * Real.exp (-(t ^ 2) / 2)) := by ring
      _ = ∫ x in Set.Ioi t, g x := by
        rw [show (∫ x in Set.Ioi t, g x) =
            standardNormalConstant *
              ∫ x in Set.Ioi t,
                (1 - 3 / x ^ 4) * Real.exp (-(x ^ 2) / 2) by
          simp [g, MeasureTheory.integral_const_mul]]
        rw [integral_Ioi_one_sub_three_div_pow_four_mul_exp_neg_sq_half ht]
      _ ≤ ∫ x in Set.Ioi t, f x :=
        MeasureTheory.setIntegral_mono_on hg_int hf_int measurableSet_Ioi hpoint
      _ = ∫ x in Set.Ioi t, standardNormalDensity x := rfl

/-- HDP Proposition 2.1.2, Mills' lower bound for the standard normal tail. -/
theorem mills_lower_le_standardNormal_tail {t : ℝ} (ht : 0 < t) :
    (1 / t - 1 / t ^ 3) * standardNormalConstant *
        Real.exp (-(t ^ 2) / 2)
      ≤ standardNormalMeasure.real (Set.Ici t) := by
  rw [standardNormal_tail_real_eq_integral_Ioi]
  exact mills_lower_le_standardNormal_tail_integral ht

/-- HDP Exercise 2.1.4, truncated second moment identity for the standard
normal density. This is the book's
`E g^2 1_{g > t} = t φ(t) + P(g > t)` written in density-integral form. -/
theorem standardNormal_truncated_secondMoment_density_eq
    {t : ℝ} (ht : 1 ≤ t) :
    ∫ x in Set.Ioi t, x ^ 2 * standardNormalDensity x =
      t * standardNormalConstant * Real.exp (-(t ^ 2) / 2) +
        ∫ x in Set.Ioi t, standardNormalDensity x := by
  have hraw := integral_Ioi_sq_mul_exp_neg_sq_half_of_one_le ht
  have hleft :
      ∫ x in Set.Ioi t, x ^ 2 * standardNormalDensity x =
        standardNormalConstant *
          ∫ x in Set.Ioi t, x ^ 2 * Real.exp (-(x ^ 2) / 2) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x _hx
    rw [standardNormalDensity_eq]
    dsimp [standardNormalConstant]
    ring
  have htail :
      ∫ x in Set.Ioi t, standardNormalDensity x =
        standardNormalConstant *
          ∫ x in Set.Ioi t, Real.exp (-(x ^ 2) / 2) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x _hx
    rw [standardNormalDensity_eq]
    dsimp [standardNormalConstant]
  calc
    ∫ x in Set.Ioi t, x ^ 2 * standardNormalDensity x
        = standardNormalConstant *
          ∫ x in Set.Ioi t, x ^ 2 * Real.exp (-(x ^ 2) / 2) := hleft
    _ = standardNormalConstant *
        (t * Real.exp (-(t ^ 2) / 2) +
          ∫ x in Set.Ioi t, Real.exp (-(x ^ 2) / 2)) := by
      rw [hraw]
    _ = t * standardNormalConstant * Real.exp (-(t ^ 2) / 2) +
        standardNormalConstant *
          ∫ x in Set.Ioi t, Real.exp (-(x ^ 2) / 2) := by ring
    _ = t * standardNormalConstant * Real.exp (-(t ^ 2) / 2) +
        ∫ x in Set.Ioi t, standardNormalDensity x := by rw [htail]

/-- HDP Exercise 2.1.4, truncated second moment upper bound. -/
theorem standardNormal_truncated_secondMoment_density_le
    {t : ℝ} (ht : 1 ≤ t) :
    ∫ x in Set.Ioi t, x ^ 2 * standardNormalDensity x
      ≤ (t + 1 / t) * standardNormalConstant *
          Real.exp (-(t ^ 2) / 2) := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have heq := standardNormal_truncated_secondMoment_density_eq ht
  have htail := standardNormal_tail_integral_le_mills_upper htpos
  calc
    ∫ x in Set.Ioi t, x ^ 2 * standardNormalDensity x
        = t * standardNormalConstant * Real.exp (-(t ^ 2) / 2) +
          ∫ x in Set.Ioi t, standardNormalDensity x := heq
    _ ≤ t * standardNormalConstant * Real.exp (-(t ^ 2) / 2) +
        (1 / t) * standardNormalConstant * Real.exp (-(t ^ 2) / 2) :=
      add_le_add le_rfl htail
    _ = (t + 1 / t) * standardNormalConstant *
          Real.exp (-(t ^ 2) / 2) := by ring

/-- HDP Proposition 2.1.2, Mills' upper bound for the standard normal tail. -/
theorem standardNormal_tail_le_mills_upper {t : ℝ} (ht : 0 < t) :
    standardNormalMeasure.real (Set.Ici t)
      ≤ (1 / t) * standardNormalConstant * Real.exp (-(t ^ 2) / 2) := by
  rw [standardNormal_tail_real_eq_integral_Ioi]
  exact standardNormal_tail_integral_le_mills_upper ht

/-- HDP Proposition 2.1.2, the displayed `t ≥ 1` corollary. -/
theorem standardNormal_tail_le_exp_sq_div_two_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    standardNormalMeasure.real (Set.Ici t)
      ≤ standardNormalConstant * Real.exp (-(t ^ 2) / 2) := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have htail := standardNormal_tail_le_mills_upper htpos
  have hfactor : 1 / t ≤ 1 := by
    simpa [one_div] using inv_le_one_of_one_le₀ ht
  have hnonneg :
      0 ≤ standardNormalConstant * Real.exp (-(t ^ 2) / 2) :=
    mul_nonneg standardNormalConstant_nonneg (Real.exp_pos _).le
  calc
    standardNormalMeasure.real (Set.Ici t)
        ≤ (1 / t) * standardNormalConstant * Real.exp (-(t ^ 2) / 2) := htail
    _ = (1 / t) * (standardNormalConstant * Real.exp (-(t ^ 2) / 2)) := by ring
    _ ≤ 1 * (standardNormalConstant * Real.exp (-(t ^ 2) / 2)) :=
      mul_le_mul_of_nonneg_right hfactor hnonneg
    _ = standardNormalConstant * Real.exp (-(t ^ 2) / 2) := by ring

end StandardNormalTail

end LeanFpAnalysis.HDP
