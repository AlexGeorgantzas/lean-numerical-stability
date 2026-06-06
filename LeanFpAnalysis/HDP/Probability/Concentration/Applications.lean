import LeanFpAnalysis.HDP.Probability.Concentration.Normal
import LeanFpAnalysis.HDP.Probability.Inequalities
import Mathlib.Probability.Density

/-!
# Concentration Applications

Book-facing application corollaries from HDP Chapter 2, Section 2.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace LeanFpAnalysis.HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section RandomizedAlgorithms

variable [IsProbabilityMeasure μ]

/-- HDP Exercise 2.2.8, majority amplification for a randomized algorithm.

`X i` is the indicator of an incorrect answer on run `i`. If each run is
incorrect with probability at most `1/2 - η`, then the probability that a
majority of the `N` runs is incorrect is at most `exp (-2 N η^2)`. The book's
sample-size condition `N ≥ (2η²)⁻¹ log(1/ε)` is the immediate rearrangement of
this bound. -/
theorem majority_vote_failure_bound
    {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η)
    {X : Fin N → Ω → ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1)
    (hmean : ∀ i, μ[X i] ≤ 1 / 2 - η) :
    μ.real {ω | (N : ℝ) / 2 ≤ ∑ i : Fin N, X i ω}
      ≤ Real.exp (-2 * (N : ℝ) * η ^ 2) := by
  classical
  let m : Fin N → ℝ := fun _ => 0
  let M : Fin N → ℝ := fun _ => 1
  let t : ℝ := (N : ℝ) * η
  have hNreal_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have htpos : 0 < t := mul_pos hNreal_pos hη
  have hhoeff :=
    hoeffding_bounded (μ := μ) (X := X) (m := m) (M := M)
      hindep hXm hbdd (t := t) htpos
  have hsubset :
      {ω | (N : ℝ) / 2 ≤ ∑ i : Fin N, X i ω}
        ⊆ {ω | t ≤ ∑ i : Fin N, (X i ω - μ[X i])} := by
    intro ω hω
    have hmean_sum :
        ∑ i : Fin N, μ[X i] ≤ ∑ _i : Fin N, (1 / 2 - η : ℝ) :=
      Finset.sum_le_sum fun i _ => hmean i
    have hconst :
        ∑ _i : Fin N, (1 / 2 - η : ℝ) =
          (N : ℝ) * (1 / 2 - η) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    have hsum_mean :
        ∑ i : Fin N, μ[X i] ≤ (N : ℝ) * (1 / 2 - η) := by
      rw [← hconst]
      exact hmean_sum
    change (N : ℝ) / 2 ≤ ∑ i : Fin N, X i ω at hω
    calc
      t = (N : ℝ) * η := rfl
      _ ≤ (∑ i : Fin N, X i ω) - ∑ i : Fin N, μ[X i] := by
        nlinarith [hω, hsum_mean]
      _ = ∑ i : Fin N, (X i ω - μ[X i]) := by
        rw [Finset.sum_sub_distrib]
  calc
    μ.real {ω | (N : ℝ) / 2 ≤ ∑ i : Fin N, X i ω}
        ≤ μ.real {ω | t ≤ ∑ i : Fin N, (X i ω - μ[X i])} :=
      measureReal_mono hsubset
    _ ≤ Real.exp (-(2 * t ^ 2) / boundedRangeSqSum m M) := hhoeff
    _ = Real.exp (-2 * (N : ℝ) * η ^ 2) := by
      congr 1
      have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hNreal_pos
      simp [t, m, M, boundedRangeSqSum, Finset.sum_const, nsmul_eq_mul]
      field_simp [hN_ne]

/-- HDP Exercise 2.2.8, the same amplification bound with the book's
`ε`-condition left as an explicit premise. -/
theorem majority_vote_failure_le_epsilon
    {N : ℕ} (hN : 0 < N)
    {η ε : ℝ} (hη : 0 < η)
    {X : Fin N → Ω → ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1)
    (hmean : ∀ i, μ[X i] ≤ 1 / 2 - η)
    (hε : Real.exp (-2 * (N : ℝ) * η ^ 2) ≤ ε) :
    μ.real {ω | (N : ℝ) / 2 ≤ ∑ i : Fin N, X i ω} ≤ ε :=
  (majority_vote_failure_bound (μ := μ) hN hη hindep hXm hbdd hmean).trans hε

end RandomizedAlgorithms

section RobustMean

variable [IsProbabilityMeasure μ]

/-- HDP Exercise 2.2.9(a), the Chebyshev sample-mean guarantee used for a
weak mean estimate. If the independent observations have common mean `m` and
variance `σ2`, then the sample mean misses by at least `ε` with probability at
most `σ2 / (N ε²)`. -/
theorem robust_mean_sampleMean_failure_bound
    {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {m σ2 ε : ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hmean : ∀ i, μ[X i] = m)
    (hvar : ∀ i, Var[X i; μ] = σ2)
    (hε : 0 < ε) :
    μ.real {ω | ε ≤ |(N : ℝ)⁻¹ * (∑ i : Fin N, X i ω) - m|}
      ≤ σ2 / ((N : ℝ) * ε ^ 2) := by
  classical
  let Y : Ω → ℝ := fun ω => (N : ℝ)⁻¹ * ∑ i : Fin N, X i ω
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hX_int : ∀ i : Fin N, Integrable (X i) μ := fun i =>
    (hX i).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hsum_memLp : MemLp (fun ω => ∑ i : Fin N, X i ω) 2 μ := by
    simpa using
      (memLp_finset_sum (μ := μ) (p := (2 : ℝ≥0∞))
        (s := (Finset.univ : Finset (Fin N))) (f := fun i ω => X i ω)
        (fun i _ => hX i))
  have hY_memLp : MemLp Y 2 μ := by
    simpa [Y] using hsum_memLp.const_mul ((N : ℝ)⁻¹)
  have hY_mean : μ[Y] = m := by
    calc
      μ[Y] = (N : ℝ)⁻¹ * μ[fun ω => ∑ i : Fin N, X i ω] := by
        simp [Y, integral_const_mul]
      _ = (N : ℝ)⁻¹ * (∑ i : Fin N, μ[X i]) := by
        rw [integral_finset_sum]
        intro i _
        exact hX_int i
      _ = (N : ℝ)⁻¹ * ((N : ℝ) * m) := by
        simp [hmean, Finset.sum_const, nsmul_eq_mul]
      _ = m := by
        field_simp [hN_ne]
  have hY_var : Var[Y; μ] = σ2 / (N : ℝ) := by
    simpa [Y] using
      variance_sampleMean_eq (μ := μ) (N := N) hN
        (X := X) (σ2 := σ2) hX hindep hvar
  have hcheb := chebyshev_inequality (μ := μ) (X := Y) hY_memLp hε
  calc
    μ.real {ω | ε ≤ |(N : ℝ)⁻¹ * (∑ i : Fin N, X i ω) - m|}
        = μ.real {ω | ε ≤ |Y ω - μ[Y]|} := by
          simp [Y, hY_mean]
    _ ≤ Var[Y; μ] / ε ^ 2 := hcheb
    _ = σ2 / ((N : ℝ) * ε ^ 2) := by
          rw [hY_var]
          field_simp [hN_ne]

/-- HDP Exercise 2.2.9(a), one explicit sample-size corollary: under the
premise `σ² / (N ε²) ≤ 1/4`, the sample mean is an `ε`-accurate weak estimate
with failure probability at most `1/4`. -/
theorem robust_mean_sampleMean_failure_le_quarter
    {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {m σ2 ε : ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hmean : ∀ i, μ[X i] = m)
    (hvar : ∀ i, Var[X i; μ] = σ2)
    (hε : 0 < ε)
    (hNε : σ2 / ((N : ℝ) * ε ^ 2) ≤ 1 / 4) :
    μ.real {ω | ε ≤ |(N : ℝ)⁻¹ * (∑ i : Fin N, X i ω) - m|}
      ≤ 1 / 4 :=
  (robust_mean_sampleMean_failure_bound
    (μ := μ) hN hX hindep hmean hvar hε).trans hNε

/-- HDP Exercise 2.2.9(b), the median-of-weak-estimates amplification step
expressed through bad-estimate indicators. If each independent weak estimate
fails with probability at most `1/4`, then the probability that at least half
of the estimates fail is at most `exp (-N/8)`. -/
theorem median_weak_estimates_failure_bound
    {N : ℕ} (hN : 0 < N)
    {B : Fin N → Ω → ℝ}
    (hindep : iIndepFun B μ)
    (hBm : ∀ i, AEMeasurable (B i) μ)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, B i ω ∈ Set.Icc 0 1)
    (hmean : ∀ i, μ[B i] ≤ 1 / 4) :
    μ.real {ω | (N : ℝ) / 2 ≤ ∑ i : Fin N, B i ω}
      ≤ Real.exp (-(N : ℝ) / 8) := by
  have hη : (0 : ℝ) < 1 / 4 := by norm_num
  have hmean' : ∀ i, μ[B i] ≤ 1 / 2 - (1 / 4 : ℝ) := by
    intro i
    have hconst : (1 / 2 : ℝ) - 1 / 4 = 1 / 4 := by norm_num
    rw [hconst]
    exact hmean i
  have h :=
    majority_vote_failure_bound
      (μ := μ) hN hη hindep hBm hbdd hmean'
  exact h.trans_eq (by
    congr 1
    ring)

/-- The bad-event set for one weak estimate. -/
def badEstimateSet (Y : Ω → ℝ) (m ε : ℝ) : Set Ω :=
  {ω | ε ≤ |Y ω - m|}

/-- The `0`/`1` indicator of a weak estimate missing the target mean by at
least `ε`. -/
def badEstimateIndicator (Y : Ω → ℝ) (m ε : ℝ) : Ω → ℝ :=
  (badEstimateSet Y m ε).indicator fun _ => (1 : ℝ)

/-- A pointwise certificate that `M ω` is a median of the finite family
`Y i ω`: at least half of the values lie on each side. This predicate is useful
because the robust-mean proof only needs this order-theoretic property of the
median. -/
def IsMedianEstimate {N : ℕ} (Y : Fin N → Ω → ℝ) (M : Ω → ℝ) : Prop :=
  ∀ ω,
    (N : ℝ) / 2 ≤ ∑ i : Fin N, (if Y i ω ≤ M ω then (1 : ℝ) else 0) ∧
    (N : ℝ) / 2 ≤ ∑ i : Fin N, (if M ω ≤ Y i ω then (1 : ℝ) else 0)

omit [MeasurableSpace Ω] in
/-- Deterministic core of the median-of-means argument: if a certified median
misses `m` by at least `ε`, then at least half of the weak estimates miss `m`
by at least `ε`. -/
lemma median_failure_subset_bad_majority
    {N : ℕ} {Y : Fin N → Ω → ℝ} {M : Ω → ℝ} {m ε : ℝ}
    (hmed : IsMedianEstimate Y M) :
    {ω | ε ≤ |M ω - m|}
      ⊆ {ω | (N : ℝ) / 2 ≤
          ∑ i : Fin N, badEstimateIndicator (Y i) m ε ω} := by
  intro ω hfail
  have hfail' : ε ≤ |M ω - m| := hfail
  rcases (le_abs.mp hfail') with hhigh | hlow
  · have hsum :
        (∑ i : Fin N, (if M ω ≤ Y i ω then (1 : ℝ) else 0))
          ≤ ∑ i : Fin N, badEstimateIndicator (Y i) m ε ω := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      by_cases hi : M ω ≤ Y i ω
      · have hbad : ε ≤ |Y i ω - m| := by
          exact le_abs.mpr (Or.inl (by linarith))
        simp [badEstimateIndicator, badEstimateSet, hi, hbad]
      · by_cases hbad : ε ≤ |Y i ω - m|
        · simp [badEstimateIndicator, badEstimateSet, hi, hbad]
        · simp [badEstimateIndicator, badEstimateSet, hi, hbad]
    exact (hmed ω).2.trans hsum
  · have hsum :
        (∑ i : Fin N, (if Y i ω ≤ M ω then (1 : ℝ) else 0))
          ≤ ∑ i : Fin N, badEstimateIndicator (Y i) m ε ω := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      by_cases hi : Y i ω ≤ M ω
      · have hbad : ε ≤ |Y i ω - m| := by
          exact le_abs.mpr (Or.inr (by linarith))
        simp [badEstimateIndicator, badEstimateSet, hi, hbad]
      · by_cases hbad : ε ≤ |Y i ω - m|
        · simp [badEstimateIndicator, badEstimateSet, hi, hbad]
        · simp [badEstimateIndicator, badEstimateSet, hi, hbad]
    exact (hmed ω).1.trans hsum

/-- HDP Exercise 2.2.9, median-of-weak-estimates guarantee in value form.

If `Y i` are independent weak estimates of `m`, each failing by at least `ε`
with probability at most `1/4`, then any pointwise median `M` of these estimates
fails with probability at most `exp (-N/8)`. -/
theorem median_weak_estimates_value_failure_bound
    {N : ℕ} (hN : 0 < N)
    {Y : Fin N → Ω → ℝ} {M : Ω → ℝ} {m ε : ℝ}
    (hmed : IsMedianEstimate Y M)
    (hindep : iIndepFun Y μ)
    (hYm : ∀ i, Measurable (Y i))
    (hweak : ∀ i, μ.real (badEstimateSet (Y i) m ε) ≤ 1 / 4) :
    μ.real {ω | ε ≤ |M ω - m|} ≤ Real.exp (-(N : ℝ) / 8) := by
  classical
  let B : Fin N → Ω → ℝ := fun i => badEstimateIndicator (Y i) m ε
  have hindepB : iIndepFun B μ := by
    have hcomp :=
      ProbabilityTheory.iIndepFun.comp (μ := μ) hindep
        (fun _i (x : ℝ) =>
          ({x | ε ≤ |x - m|} : Set ℝ).indicator (fun _ => (1 : ℝ)) x)
        (fun _i => by measurability)
    simpa [B, badEstimateIndicator, badEstimateSet, Function.comp_def] using hcomp
  have hBm : ∀ i, AEMeasurable (B i) μ := by
    intro i
    have hs : MeasurableSet (badEstimateSet (Y i) m ε) := by
      simp [badEstimateSet]
      measurability
    exact (Measurable.indicator measurable_const hs).aemeasurable
  have hbdd : ∀ i, ∀ᵐ ω ∂μ, B i ω ∈ Set.Icc 0 1 := by
    intro i
    exact ae_of_all μ fun ω => by
      by_cases hbad : ω ∈ badEstimateSet (Y i) m ε
      · simp [B, badEstimateIndicator, hbad]
      · simp [B, badEstimateIndicator, hbad]
  have hmean : ∀ i, μ[B i] ≤ 1 / 4 := by
    intro i
    have hs : MeasurableSet (badEstimateSet (Y i) m ε) := by
      simp [badEstimateSet]
      measurability
    calc
      μ[B i] = μ.real (badEstimateSet (Y i) m ε) := by
        change ∫ ω, (badEstimateSet (Y i) m ε).indicator (fun _ => (1 : ℝ)) ω ∂μ =
          μ.real (badEstimateSet (Y i) m ε)
        exact MeasureTheory.integral_indicator_one hs
      _ ≤ 1 / 4 := hweak i
  have hsubset :
      {ω | ε ≤ |M ω - m|}
        ⊆ {ω | (N : ℝ) / 2 ≤ ∑ i : Fin N, B i ω} := by
    simpa [B] using
      median_failure_subset_bad_majority
        (Y := Y) (M := M) (m := m) (ε := ε) hmed
  calc
    μ.real {ω | ε ≤ |M ω - m|}
        ≤ μ.real {ω | (N : ℝ) / 2 ≤ ∑ i : Fin N, B i ω} :=
          measureReal_mono hsubset
    _ ≤ Real.exp (-(N : ℝ) / 8) :=
          median_weak_estimates_failure_bound
            (μ := μ) hN hindepB hBm hbdd hmean

end RobustMean

section SmallBall

variable [IsProbabilityMeasure μ]

/-- A nonnegative random variable has finite negative exponential moments. -/
lemma integrable_exp_neg_mul_of_ae_nonnegative
    {X : Ω → ℝ}
    (hX_ae : AEMeasurable X μ)
    (hX_nonneg : 0 ≤ᵐ[μ] X)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ω => Real.exp ((-t) * X ω)) μ := by
  have h_bound : ∀ᵐ ω ∂μ, ‖Real.exp ((-t) * X ω)‖ ≤ (1 : ℝ) := by
    filter_upwards [hX_nonneg] with ω hω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) hω)
  exact (integrable_const (1 : ℝ)).mono' (by fun_prop) h_bound

/-- HDP Exercise 2.2.10(a), Laplace-transform estimate from a bounded
density. If `X` is nonnegative and its Lebesgue density is bounded by `1`,
then `E exp(-t X) ≤ 1 / t` for every `t > 0`. -/
theorem laplace_transform_le_of_nonnegative_pdf_le_one
    {X : Ω → ℝ} [MeasureTheory.HasPDF X μ (volume : Measure ℝ)]
    (hX_nonneg : 0 ≤ᵐ[μ] X)
    (hpdf_le_one : ∀ᵐ x ∂volume, MeasureTheory.pdf X μ volume x ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    mgf X μ (-t) ≤ 1 / t := by
  let f : ℝ → ℝ := fun x => (MeasureTheory.pdf X μ volume x).toReal * Real.exp ((-t) * x)
  let g : ℝ → ℝ := fun x => (Set.Ici (0 : ℝ)).indicator
    (fun y => Real.exp ((-t) * y)) x
  have hX_ae : AEMeasurable X μ := MeasureTheory.HasPDF.aemeasurable X μ volume
  have h_exp_int : Integrable (fun ω => Real.exp ((-t) * X ω)) μ :=
    integrable_exp_neg_mul_of_ae_nonnegative hX_ae hX_nonneg ht
  have h_lotus :
      ∫ x, f x ∂volume = ∫ ω, Real.exp ((-t) * X ω) ∂μ := by
    have h :=
      @MeasureTheory.pdf.integral_pdf_smul
        Ω ℝ _ _ μ (volume : Measure ℝ) ℝ _ _ _ X _
        (fun x : ℝ => Real.exp ((-t) * x)) (by fun_prop)
    simpa [f, smul_eq_mul] using h
  have hpre_zero : μ {ω | X ω < 0} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hX_nonneg] with ω hω hlt
    exact (not_lt.mpr hω) hlt
  have hmap_neg : Measure.map X μ (Set.Iio (0 : ℝ)) = 0 := by
    rw [Measure.map_apply_of_aemeasurable hX_ae measurableSet_Iio]
    simpa [Set.preimage, Set.mem_Iio] using hpre_zero
  have hpdf_zero_neg :
      ∀ᵐ x ∂volume, x ∈ Set.Iio (0 : ℝ) → MeasureTheory.pdf X μ volume x = 0 := by
    have hlin :
        ∫⁻ x in Set.Iio (0 : ℝ), MeasureTheory.pdf X μ volume x ∂volume = 0 := by
      rw [← MeasureTheory.map_eq_setLIntegral_pdf X μ volume measurableSet_Iio]
      exact hmap_neg
    exact
      (MeasureTheory.setLIntegral_eq_zero_iff measurableSet_Iio
        (MeasureTheory.measurable_pdf X μ volume)).1 hlin
  have hfg_ae : f ≤ᵐ[volume] g := by
    filter_upwards [hpdf_zero_neg, hpdf_le_one] with x hneg hle
    by_cases hx : x < 0
    · have hpdf0 : MeasureTheory.pdf X μ volume x = 0 := hneg hx
      simp [f, g, hpdf0, hx]
    · have hx0 : 0 ≤ x := le_of_not_gt hx
      have hpdf_toReal_le : (MeasureTheory.pdf X μ volume x).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle
      have hpdf_toReal_nonneg : 0 ≤ (MeasureTheory.pdf X μ volume x).toReal := ENNReal.toReal_nonneg
      have hexp_nonneg : 0 ≤ Real.exp ((-t) * x) := (Real.exp_pos _).le
      calc
        f x = (MeasureTheory.pdf X μ volume x).toReal * Real.exp ((-t) * x) := rfl
        _ ≤ 1 * Real.exp ((-t) * x) :=
          mul_le_mul_of_nonneg_right hpdf_toReal_le hexp_nonneg
        _ = g x := by simp [g, hx0]
  have hf_int : Integrable f volume := by
    have hiff :=
      @MeasureTheory.pdf.integrable_pdf_smul_iff
        Ω ℝ _ _ μ (volume : Measure ℝ) ℝ _ _ _ X _
        (fun x : ℝ => Real.exp ((-t) * x)) (by fun_prop)
    simpa [f, smul_eq_mul] using hiff.mpr h_exp_int
  have hg_int : Integrable g volume := by
    have h_on : IntegrableOn (fun x : ℝ => Real.exp ((-t) * x)) (Set.Ici (0 : ℝ)) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_exp_mul_Ioi (by linarith : -t < 0) 0
    change Integrable ((Set.Ici (0 : ℝ)).indicator
      (fun y => Real.exp ((-t) * y))) volume
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ici).2 h_on
  have h_integral_le : ∫ x, f x ∂volume ≤ ∫ x, g x ∂volume :=
    integral_mono_ae hf_int hg_int hfg_ae
  have hg_eq : ∫ x, g x ∂volume = 1 / t := by
    calc
      ∫ x, g x ∂volume
          = ∫ x in Set.Ici (0 : ℝ), Real.exp ((-t) * x) ∂volume := by
            rw [← integral_indicator measurableSet_Ici]
      _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp ((-t) * x) ∂volume := by
            rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
      _ = 1 / t := by
            rw [integral_exp_mul_Ioi (by linarith : -t < 0) 0]
            simp
  calc
    mgf X μ (-t) = ∫ ω, Real.exp ((-t) * X ω) ∂μ := rfl
    _ = ∫ x, f x ∂volume := h_lotus.symm
    _ ≤ ∫ x, g x ∂volume := h_integral_le
    _ = 1 / t := hg_eq

/-- HDP Exercise 2.2.10(b), small-ball bound from the Laplace-transform
estimate in part (a). If independent nonnegative variables satisfy
`E exp(-X_i/ε) ≤ ε`, then
`P{sum X_i ≤ ε N} ≤ (e ε)^N`. The density-bound part of the exercise supplies
this Laplace estimate with `ε = 1 / t`. -/
theorem small_ball_sum_le_of_laplace_bound
    {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {X : Fin N → Ω → ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hlaplace_int :
      ∀ i, Integrable (fun ω => Real.exp ((-(ε⁻¹)) * X i ω)) μ)
    (hlaplace :
      ∀ i, mgf (X i) μ (-(ε⁻¹)) ≤ ε) :
    μ.real {ω | ∑ i : Fin N, X i ω ≤ ε * (N : ℝ)}
      ≤ (Real.exp 1 * ε) ^ N := by
  classical
  let θ : ℝ := -ε⁻¹
  let S : Ω → ℝ := fun ω => ∑ i : Fin N, X i ω
  have hθ_nonpos : θ ≤ 0 := by
    dsimp [θ]
    exact neg_nonpos.mpr (inv_nonneg.mpr hε.le)
  have hsum_int :
      Integrable (fun ω => Real.exp (θ * S ω)) μ := by
    have h :=
      hindep.integrable_exp_mul_sum
        (t := θ) hXm (s := (Finset.univ : Finset (Fin N)))
        (by
          intro i _
          simpa [θ] using hlaplace_int i)
    simpa [S, Finset.sum_apply] using h
  have htail :
      μ.real {ω | S ω ≤ ε * (N : ℝ)}
        ≤ Real.exp (-θ * (ε * (N : ℝ))) * mgf S μ θ := by
    simpa [mgf] using
      ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := μ) (X := S) (ε * (N : ℝ)) hθ_nonpos hsum_int
  have hmgf_sum :
      mgf S μ θ = ∏ i : Fin N, mgf (X i) μ θ := by
    have hsum :
        mgf (∑ i ∈ (Finset.univ : Finset (Fin N)), X i) μ θ =
          ∏ i ∈ (Finset.univ : Finset (Fin N)), mgf (X i) μ θ :=
      hindep.mgf_sum (t := θ) hXm (Finset.univ : Finset (Fin N))
    have hfun : S = (∑ i : Fin N, X i) := by
      funext ω
      simp [S, Finset.sum_apply]
    rw [hfun]
    simpa using hsum
  have hprod :
      ∏ i : Fin N, mgf (X i) μ θ ≤ ε ^ N := by
    calc
      ∏ i : Fin N, mgf (X i) μ θ
          ≤ ∏ _i : Fin N, ε := by
            refine Finset.prod_le_prod ?_ ?_
            · intro i _hi
              exact mgf_nonneg
            · intro i _hi
              simpa [θ] using hlaplace i
      _ = ε ^ N := by
            simp
  have hexp :
      Real.exp (-θ * (ε * (N : ℝ))) = Real.exp (N : ℝ) := by
    dsimp [θ]
    congr 1
    calc
      - -ε⁻¹ * (ε * (N : ℝ)) = ε⁻¹ * (ε * (N : ℝ)) := by ring
      _ = (ε⁻¹ * ε) * (N : ℝ) := by ring
      _ = 1 * (N : ℝ) := by rw [inv_mul_cancel₀ hε.ne']
      _ = (N : ℝ) := by ring
  calc
    μ.real {ω | ∑ i : Fin N, X i ω ≤ ε * (N : ℝ)}
        = μ.real {ω | S ω ≤ ε * (N : ℝ)} := by simp [S]
    _ ≤ Real.exp (-θ * (ε * (N : ℝ))) * mgf S μ θ := htail
    _ = Real.exp (N : ℝ) * (∏ i : Fin N, mgf (X i) μ θ) := by
          rw [hexp, hmgf_sum]
    _ ≤ Real.exp (N : ℝ) * ε ^ N := by
          exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = (Real.exp 1 * ε) ^ N := by
          rw [mul_pow, ← Real.exp_nat_mul]
          ring_nf

/-- HDP Exercise 2.2.10, combined density-to-small-ball form. If independent
nonnegative real variables have Lebesgue densities bounded by `1`, then
`P{sum X_i ≤ ε N} ≤ (e ε)^N`. -/
theorem small_ball_sum_le_of_nonnegative_pdf_le_one
    {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {X : Fin N → Ω → ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hpdf : ∀ i, MeasureTheory.HasPDF (X i) μ (volume : Measure ℝ))
    (hX_nonneg : ∀ i, 0 ≤ᵐ[μ] X i)
    (hpdf_le_one :
      ∀ i, ∀ᵐ x ∂volume, MeasureTheory.pdf (X i) μ volume x ≤ 1) :
    μ.real {ω | ∑ i : Fin N, X i ω ≤ ε * (N : ℝ)}
      ≤ (Real.exp 1 * ε) ^ N := by
  refine
    small_ball_sum_le_of_laplace_bound
      (μ := μ) (N := N) (ε := ε) hε hindep hXm ?_ ?_
  · intro i
    letI : MeasureTheory.HasPDF (X i) μ (volume : Measure ℝ) := hpdf i
    exact
      integrable_exp_neg_mul_of_ae_nonnegative
        (MeasureTheory.HasPDF.aemeasurable (X i) μ volume)
        (hX_nonneg i) (inv_pos.mpr hε)
  · intro i
    letI : MeasureTheory.HasPDF (X i) μ (volume : Measure ℝ) := hpdf i
    have h :=
      laplace_transform_le_of_nonnegative_pdf_le_one
        (μ := μ) (X := X i) (hX_nonneg i) (hpdf_le_one i)
        (t := ε⁻¹) (inv_pos.mpr hε)
    calc
      mgf (X i) μ (-(ε⁻¹)) ≤ 1 / ε⁻¹ := h
      _ = ε := by simp [div_eq_mul_inv]

end SmallBall

end LeanFpAnalysis.HDP
