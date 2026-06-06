import LeanFpAnalysis.HDP.Probability.Concentration.Hoeffding

/-!
# Chernoff Inequalities

Book-facing forms of HDP Chapter 2, Section 2.3, together with the Bernoulli
MGF lemmas used in their proofs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace LeanFpAnalysis.HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section BernoulliMGF

/-- Integral against the `{0,1}` Bernoulli PMF. -/
lemma bernoulliNatPMF_integral_eq
    {p : ℝ≥0} {hp : p ≤ 1} (f : ℕ → ℝ) (hf : Measurable f) :
    ∫ k, f k ∂(bernoulliNatPMF p hp).toMeasure =
      (1 - (p : ℝ)) * f 0 + (p : ℝ) * f 1 := by
  let φ : Bool → ℕ := fun b => if b then 1 else 0
  change
    ∫ k, f k ∂(PMF.map φ (PMF.bernoulli p hp)).toMeasure =
      (1 - (p : ℝ)) * f 0 + (p : ℝ) * f 1
  rw [← (PMF.toMeasure_map (PMF.bernoulli p hp)
    (f := φ) (measurable_of_finite φ))]
  rw [integral_map]
  · rw [PMF.integral_eq_sum]
    simp [φ, PMF.bernoulli_apply]
    rw [NNReal.coe_sub hp]
    norm_num
    ring_nf
  · exact (measurable_of_finite φ).aemeasurable
  · exact hf.aestronglyMeasurable

/-- MGF of a Bernoulli random variable represented as an `ℕ`-valued variable. -/
lemma mgf_coe_nat_of_hasLaw_bernoulliNatPMF
    [IsProbabilityMeasure μ]
    {X : Ω → ℕ} {p : ℝ≥0} {hp : p ≤ 1}
    (hX : HasLaw X ((bernoulliNatPMF p hp).toMeasure) μ)
    (theta : ℝ) :
    mgf (fun ω => (X ω : ℝ)) μ theta =
      (1 - (p : ℝ)) + (p : ℝ) * Real.exp theta := by
  calc
    mgf (fun ω => (X ω : ℝ)) μ theta
        = ∫ k, Real.exp (theta * (k : ℝ)) ∂(bernoulliNatPMF p hp).toMeasure := by
          simpa [mgf, Function.comp_def] using
            (hX.integral_comp
              (f := fun k : ℕ => Real.exp (theta * (k : ℝ))) (by fun_prop))
    _ = (1 - (p : ℝ)) * Real.exp (theta * (0 : ℝ))
          + (p : ℝ) * Real.exp (theta * (1 : ℝ)) := by
          simpa using
            bernoulliNatPMF_integral_eq (p := p) (hp := hp)
              (fun k : ℕ => Real.exp (theta * (k : ℝ))) (by fun_prop)
    _ = (1 - (p : ℝ)) + (p : ℝ) * Real.exp theta := by
          simp

/-- The Bernoulli MGF bound used in Chernoff's method:
`E exp(λX) ≤ exp((exp λ - 1) p)`. -/
lemma mgf_coe_nat_bernoulli_le_exp
    [IsProbabilityMeasure μ]
    {X : Ω → ℕ} {p : ℝ≥0} {hp : p ≤ 1}
    (hX : HasLaw X ((bernoulliNatPMF p hp).toMeasure) μ)
    (theta : ℝ) :
    mgf (fun ω => (X ω : ℝ)) μ theta
      ≤ Real.exp ((Real.exp theta - 1) * (p : ℝ)) := by
  rw [mgf_coe_nat_of_hasLaw_bernoulliNatPMF (μ := μ) hX theta]
  have hrewrite :
      (1 - (p : ℝ)) + (p : ℝ) * Real.exp theta =
        1 + (Real.exp theta - 1) * (p : ℝ) := by ring
  rw [hrewrite]
  exact one_add_le_exp ((Real.exp theta - 1) * (p : ℝ))

end BernoulliMGF

section ChernoffUpper

variable [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι]
variable {X : ι → Ω → ℕ} {p : ι → ℝ≥0} {hp : ∀ i, p i ≤ 1}

/-- Sum of Bernoulli parameters, the mean `μ = E S_N` in Chernoff's
inequality. -/
def bernoulliParameterSum (p : ι → ℝ≥0) : ℝ :=
  ∑ i, (p i : ℝ)

@[simp]
lemma bernoulliParameterSum_def (p : ι → ℝ≥0) :
    bernoulliParameterSum p = ∑ i, (p i : ℝ) := rfl

lemma bernoulliParameterSum_nonneg (p : ι → ℝ≥0) :
    0 ≤ bernoulliParameterSum p :=
  Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _

/-- Finite Bernoulli sums have integrable exponential moments. -/
lemma integrable_exp_mul_sum_bernoulli
    (hX : ∀ i, HasLaw (X i) ((bernoulliNatPMF (p i) (hp i)).toMeasure) μ)
    (theta : ℝ) :
    Integrable (fun ω => Real.exp (theta * ∑ i, (X i ω : ℝ))) μ := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => (X i ω : ℝ)
  change Integrable (fun ω => Real.exp (theta * ∑ i, Y i ω)) μ
  have hYmeas : ∀ i, AEMeasurable (Y i) μ := by
    intro i
    exact (measurable_of_countable fun n : ℕ => (n : ℝ)).comp_aemeasurable
      (hX i).aemeasurable
  have hsum_meas :
      AEMeasurable (fun ω => ∑ i, Y i ω) μ :=
    by
      have hsum_bundle : AEMeasurable (∑ i, Y i) μ :=
        Finset.aemeasurable_sum (s := (Finset.univ : Finset ι))
          (fun i _ => hYmeas i)
      exact hsum_bundle.congr (ae_of_all μ fun ω => by simp [Finset.sum_apply])
  refine Integrable.of_bound
    (((hsum_meas.const_mul theta).exp).aestronglyMeasurable)
    (Real.exp (|theta| * (Fintype.card ι : ℝ))) ?_
  have hsupport :
      ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 ∨ X i ω = 1 :=
    Filter.eventually_all.mpr fun i =>
      ae_eq_zero_or_one_of_hasLaw_bernoulliNatPMF
        (μ := μ) (X := X i) (p := p i) (hp := hp i) (hX i)
  filter_upwards [hsupport] with ω hω
  have hsum_le :
      ∑ i, Y i ω ≤ (Fintype.card ι : ℝ) := by
    calc
      ∑ i, Y i ω ≤ ∑ _i : ι, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        rcases hω i with hzero | hone
        · simp [Y, hzero]
        · simp [Y, hone]
      _ = (Fintype.card ι : ℝ) := by simp
  have hsum_nonneg : 0 ≤ ∑ i, Y i ω := by
    refine Finset.sum_nonneg ?_
    intro i _hi
    rcases hω i with hzero | hone
    · simp [Y, hzero]
    · simp [Y, hone]
  have hexp_le :
      Real.exp (theta * ∑ i, Y i ω)
        ≤ Real.exp (|theta| * (Fintype.card ι : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    calc
      theta * ∑ i, Y i ω ≤ |theta| * ∑ i, Y i ω :=
        mul_le_mul_of_nonneg_right (le_abs_self theta) hsum_nonneg
      _ ≤ |theta| * (Fintype.card ι : ℝ) :=
        mul_le_mul_of_nonneg_left hsum_le (abs_nonneg theta)
  simpa [Y, Real.norm_of_nonneg (Real.exp_pos _).le] using hexp_le

/-- Chernoff's MGF bound for a sum of independent Bernoulli variables, before
optimizing the exponential parameter. -/
theorem chernoff_bernoulli_upper_exp
    (hindep : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) ((bernoulliNatPMF (p i) (hp i)).toMeasure) μ)
    {theta t : ℝ} (htheta : 0 ≤ theta) :
    μ.real {ω | t ≤ ∑ i, (X i ω : ℝ)}
      ≤ Real.exp (-theta * t + (Real.exp theta - 1) * bernoulliParameterSum p) := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => (X i ω : ℝ)
  have hYindep : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hindep.comp (fun _i x => (x : ℝ))
        (fun _ => measurable_of_countable fun n : ℕ => (n : ℝ))
  have hYmeas : ∀ i, AEMeasurable (Y i) μ := by
    intro i
    exact (measurable_of_countable fun n : ℕ => (n : ℝ)).comp_aemeasurable
      (hX i).aemeasurable
  have h_int :
      Integrable (fun ω => Real.exp (theta * ∑ i, Y i ω)) μ := by
    simpa [Y] using
      integrable_exp_mul_sum_bernoulli
        (μ := μ) (X := X) (p := p) (hp := hp) hX theta
  have h_markov :
      μ.real {ω | t ≤ ∑ i, Y i ω}
        ≤ Real.exp (-theta * t) * mgf (fun ω => ∑ i, Y i ω) μ theta := by
    simpa [mgf] using
      ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := μ) (X := fun ω => ∑ i, Y i ω) t htheta h_int
  have h_mgf_sum :
      mgf (fun ω => ∑ i, Y i ω) μ theta =
        ∏ i, mgf (Y i) μ theta := by
    have hfun : (fun ω => ∑ i, Y i ω) = (∑ i, Y i) := by
      funext ω
      simp [Finset.sum_apply]
    rw [hfun]
    exact hYindep.mgf_sum₀ (t := theta) hYmeas (Finset.univ : Finset ι)
  have h_mgf_le :
      mgf (fun ω => ∑ i, Y i ω) μ theta
        ≤ Real.exp ((Real.exp theta - 1) * bernoulliParameterSum p) := by
    calc
      mgf (fun ω => ∑ i, Y i ω) μ theta
          = ∏ i, mgf (Y i) μ theta := h_mgf_sum
      _ ≤ ∏ i, Real.exp ((Real.exp theta - 1) * (p i : ℝ)) := by
          refine Finset.prod_le_prod ?_ ?_
          · intro i _hi
            exact mgf_nonneg
          · intro i _hi
            simpa [Y] using
              mgf_coe_nat_bernoulli_le_exp
                (μ := μ) (X := X i) (p := p i) (hp := hp i) (hX i) theta
      _ = Real.exp (∑ i, (Real.exp theta - 1) * (p i : ℝ)) := by
          rw [Real.exp_sum]
      _ = Real.exp ((Real.exp theta - 1) * bernoulliParameterSum p) := by
          congr 1
          simp [bernoulliParameterSum, Finset.mul_sum]
  calc
    μ.real {ω | t ≤ ∑ i, (X i ω : ℝ)}
        = μ.real {ω | t ≤ ∑ i, Y i ω} := by simp [Y]
    _ ≤ Real.exp (-theta * t) * mgf (fun ω => ∑ i, Y i ω) μ theta := h_markov
    _ ≤ Real.exp (-theta * t)
        * Real.exp ((Real.exp theta - 1) * bernoulliParameterSum p) := by
          exact mul_le_mul_of_nonneg_left h_mgf_le (Real.exp_pos _).le
    _ = Real.exp (-theta * t + (Real.exp theta - 1) * bernoulliParameterSum p) := by
          rw [Real.exp_add]

/-- HDP Theorem 2.3.1, Chernoff's inequality for the upper tail of a sum of
independent Bernoulli random variables. This is the nondegenerate case
`0 < μ`; the degenerate case `μ = 0` is handled separately below. -/
theorem chernoff_bernoulli_upper_pos_mean
    (hindep : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) ((bernoulliNatPMF (p i) (hp i)).toMeasure) μ)
    (hmu : 0 < bernoulliParameterSum p)
    {t : ℝ} (ht : bernoulliParameterSum p < t) :
    μ.real {ω | t ≤ ∑ i, (X i ω : ℝ)}
      ≤ Real.exp (-(bernoulliParameterSum p))
          * (Real.exp 1 * bernoulliParameterSum p / t) ^ t := by
  classical
  let m : ℝ := bernoulliParameterSum p
  have htpos : 0 < t := hmu.trans ht
  have hratio_pos : 0 < t / m := div_pos htpos hmu
  have hone_le_ratio : 1 ≤ t / m := by
    rw [le_div_iff₀ hmu]
    simpa [m] using ht.le
  have htheta_nonneg : 0 ≤ Real.log (t / m) :=
    Real.log_nonneg hone_le_ratio
  have htail :=
    chernoff_bernoulli_upper_exp
      (μ := μ) (X := X) (p := p) (hp := hp)
      hindep hX (theta := Real.log (t / m)) (t := t) htheta_nonneg
  have hclosed :
      Real.exp (-(Real.log (t / m)) * t
          + (Real.exp (Real.log (t / m)) - 1) * m)
        =
      Real.exp (-m) * (Real.exp 1 * m / t) ^ t := by
    have hm_ne : m ≠ 0 := ne_of_gt hmu
    have ht_ne : t ≠ 0 := ne_of_gt htpos
    have hbase_pos : 0 < Real.exp 1 * m / t := by
      positivity
    have hlog_base :
        Real.log (Real.exp 1 * m / t) = 1 - Real.log (t / m) := by
      calc
        Real.log (Real.exp 1 * m / t)
            = Real.log (Real.exp 1 * (m / t)) := by ring_nf
        _ = Real.log (Real.exp 1) + Real.log (m / t) := by
          rw [Real.log_mul (Real.exp_ne_zero 1) (div_ne_zero hm_ne ht_ne)]
        _ = 1 + (Real.log m - Real.log t) := by
          rw [Real.log_exp, Real.log_div hm_ne ht_ne]
        _ = 1 - Real.log (t / m) := by
          rw [Real.log_div ht_ne hm_ne]
          ring
    rw [Real.rpow_def_of_pos hbase_pos]
    rw [← Real.exp_add]
    congr 1
    rw [Real.exp_log hratio_pos, hlog_base]
    field_simp [hm_ne, ht_ne]
    ring
  exact htail.trans_eq (by simpa [m] using hclosed)

/-- Chernoff's MGF bound for the lower tail of a sum of independent Bernoulli
variables, before optimizing the exponential parameter. -/
theorem chernoff_bernoulli_lower_exp
    (hindep : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) ((bernoulliNatPMF (p i) (hp i)).toMeasure) μ)
    {theta t : ℝ} (htheta : theta ≤ 0) :
    μ.real {ω | ∑ i, (X i ω : ℝ) ≤ t}
      ≤ Real.exp (-theta * t + (Real.exp theta - 1) * bernoulliParameterSum p) := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => (X i ω : ℝ)
  have hYindep : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hindep.comp (fun _i x => (x : ℝ))
        (fun _ => measurable_of_countable fun n : ℕ => (n : ℝ))
  have hYmeas : ∀ i, AEMeasurable (Y i) μ := by
    intro i
    exact (measurable_of_countable fun n : ℕ => (n : ℝ)).comp_aemeasurable
      (hX i).aemeasurable
  have h_int :
      Integrable (fun ω => Real.exp (theta * ∑ i, Y i ω)) μ := by
    simpa [Y] using
      integrable_exp_mul_sum_bernoulli
        (μ := μ) (X := X) (p := p) (hp := hp) hX theta
  have h_markov :
      μ.real {ω | ∑ i, Y i ω ≤ t}
        ≤ Real.exp (-theta * t) * mgf (fun ω => ∑ i, Y i ω) μ theta := by
    simpa [mgf] using
      ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := μ) (X := fun ω => ∑ i, Y i ω) t htheta h_int
  have h_mgf_sum :
      mgf (fun ω => ∑ i, Y i ω) μ theta =
        ∏ i, mgf (Y i) μ theta := by
    have hfun : (fun ω => ∑ i, Y i ω) = (∑ i, Y i) := by
      funext ω
      simp [Finset.sum_apply]
    rw [hfun]
    exact hYindep.mgf_sum₀ (t := theta) hYmeas (Finset.univ : Finset ι)
  have h_mgf_le :
      mgf (fun ω => ∑ i, Y i ω) μ theta
        ≤ Real.exp ((Real.exp theta - 1) * bernoulliParameterSum p) := by
    calc
      mgf (fun ω => ∑ i, Y i ω) μ theta
          = ∏ i, mgf (Y i) μ theta := h_mgf_sum
      _ ≤ ∏ i, Real.exp ((Real.exp theta - 1) * (p i : ℝ)) := by
          refine Finset.prod_le_prod ?_ ?_
          · intro i _hi
            exact mgf_nonneg
          · intro i _hi
            simpa [Y] using
              mgf_coe_nat_bernoulli_le_exp
                (μ := μ) (X := X i) (p := p i) (hp := hp i) (hX i) theta
      _ = Real.exp (∑ i, (Real.exp theta - 1) * (p i : ℝ)) := by
          rw [Real.exp_sum]
      _ = Real.exp ((Real.exp theta - 1) * bernoulliParameterSum p) := by
          congr 1
          simp [bernoulliParameterSum, Finset.mul_sum]
  calc
    μ.real {ω | ∑ i, (X i ω : ℝ) ≤ t}
        = μ.real {ω | ∑ i, Y i ω ≤ t} := by simp [Y]
    _ ≤ Real.exp (-theta * t) * mgf (fun ω => ∑ i, Y i ω) μ theta := h_markov
    _ ≤ Real.exp (-theta * t)
        * Real.exp ((Real.exp theta - 1) * bernoulliParameterSum p) := by
          exact mul_le_mul_of_nonneg_left h_mgf_le (Real.exp_pos _).le
    _ = Real.exp (-theta * t + (Real.exp theta - 1) * bernoulliParameterSum p) := by
          rw [Real.exp_add]

/-- HDP Exercise 2.3.2, Chernoff's inequality for lower tails of Bernoulli
sums, in the nondegenerate range `0 < t < μ`. -/
theorem chernoff_bernoulli_lower_pos
    (hindep : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) ((bernoulliNatPMF (p i) (hp i)).toMeasure) μ)
    {t : ℝ} (htpos : 0 < t) (ht : t < bernoulliParameterSum p) :
    μ.real {ω | ∑ i, (X i ω : ℝ) ≤ t}
      ≤ Real.exp (-(bernoulliParameterSum p))
          * (Real.exp 1 * bernoulliParameterSum p / t) ^ t := by
  classical
  let m : ℝ := bernoulliParameterSum p
  have hmu : 0 < m := htpos.trans ht
  have hratio_pos : 0 < t / m := div_pos htpos hmu
  have hratio_le_one : t / m ≤ 1 := by
    rw [div_le_one₀ hmu]
    exact ht.le
  have htheta_nonpos : Real.log (t / m) ≤ 0 :=
    Real.log_nonpos hratio_pos.le hratio_le_one
  have htail :=
    chernoff_bernoulli_lower_exp
      (μ := μ) (X := X) (p := p) (hp := hp)
      hindep hX (theta := Real.log (t / m)) (t := t) htheta_nonpos
  have hclosed :
      Real.exp (-(Real.log (t / m)) * t
          + (Real.exp (Real.log (t / m)) - 1) * m)
        =
      Real.exp (-m) * (Real.exp 1 * m / t) ^ t := by
    have hm_ne : m ≠ 0 := ne_of_gt hmu
    have ht_ne : t ≠ 0 := ne_of_gt htpos
    have hbase_pos : 0 < Real.exp 1 * m / t := by
      positivity
    have hlog_base :
        Real.log (Real.exp 1 * m / t) = 1 - Real.log (t / m) := by
      calc
        Real.log (Real.exp 1 * m / t)
            = Real.log (Real.exp 1 * (m / t)) := by ring_nf
        _ = Real.log (Real.exp 1) + Real.log (m / t) := by
          rw [Real.log_mul (Real.exp_ne_zero 1) (div_ne_zero hm_ne ht_ne)]
        _ = 1 + (Real.log m - Real.log t) := by
          rw [Real.log_exp, Real.log_div hm_ne ht_ne]
        _ = 1 - Real.log (t / m) := by
          rw [Real.log_div ht_ne hm_ne]
          ring
    rw [Real.rpow_def_of_pos hbase_pos]
    rw [← Real.exp_add]
    congr 1
    rw [Real.exp_log hratio_pos, hlog_base]
    field_simp [hm_ne, ht_ne]
    ring
  exact htail.trans_eq (by simpa [m] using hclosed)

/-- HDP Exercise 2.3.5, Chernoff's inequality for small deviations of
Bernoulli sums. The book states this with an unspecified absolute constant;
this formalization gives the explicit constant `c = 1/4`. -/
theorem chernoff_bernoulli_two_sided_small_deviation
    (hindep : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) ((bernoulliNatPMF (p i) (hp i)).toMeasure) μ)
    {ε : ℝ} (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) :
    μ.real {ω | ε * bernoulliParameterSum p
        ≤ |(∑ i, (X i ω : ℝ)) - bernoulliParameterSum p|}
      ≤ 2 * Real.exp (-(1 / 4) * bernoulliParameterSum p * ε ^ 2) := by
  classical
  let m : ℝ := bernoulliParameterSum p
  let θ : ℝ := ε / 2
  let S : Ω → ℝ := fun ω => ∑ i, (X i ω : ℝ)
  let U : Set Ω := {ω | (1 + ε) * m ≤ S ω}
  let L : Set Ω := {ω | S ω ≤ (1 - ε) * m}
  have hm_nonneg : 0 ≤ m := by
    simpa [m] using bernoulliParameterSum_nonneg p
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ]
    linarith
  have hθ_le_one : θ ≤ 1 := by
    dsimp [θ]
    linarith [hε_le_one]
  have hθ_mem : θ ∈ Set.Icc 0 1 := ⟨hθ_nonneg, hθ_le_one⟩
  have h_upper_tail :
      μ.real U ≤ Real.exp (-(1 / 4) * m * ε ^ 2) := by
    have hchernoff :=
      chernoff_bernoulli_upper_exp
        (μ := μ) (X := X) (p := p) (hp := hp)
        hindep hX (theta := θ) (t := (1 + ε) * m) hθ_nonneg
    have h_exp :
        -θ * ((1 + ε) * m) + (Real.exp θ - 1) * m
          ≤ -(1 / 4) * m * ε ^ 2 := by
      have hpoint : Real.exp θ - 1 ≤ θ + θ ^ 2 :=
        exp_sub_one_le_self_add_sq_of_mem_Icc hθ_mem
      have hmul : (Real.exp θ - 1) * m ≤ (θ + θ ^ 2) * m :=
        mul_le_mul_of_nonneg_right hpoint hm_nonneg
      calc
        -θ * ((1 + ε) * m) + (Real.exp θ - 1) * m
            ≤ -θ * ((1 + ε) * m) + (θ + θ ^ 2) * m :=
              by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_left hmul (-θ * ((1 + ε) * m))
        _ = -(1 / 4) * m * ε ^ 2 := by
              simp [θ]
              ring
    calc
      μ.real U
          ≤ Real.exp (-θ * ((1 + ε) * m) + (Real.exp θ - 1) * m) := by
            simpa [U, S, m] using hchernoff
      _ ≤ Real.exp (-(1 / 4) * m * ε ^ 2) :=
            Real.exp_le_exp.mpr h_exp
  have h_lower_tail :
      μ.real L ≤ Real.exp (-(1 / 4) * m * ε ^ 2) := by
    have hθ_nonpos : -θ ≤ 0 := by linarith
    have hchernoff :=
      chernoff_bernoulli_lower_exp
        (μ := μ) (X := X) (p := p) (hp := hp)
        hindep hX (theta := -θ) (t := (1 - ε) * m) hθ_nonpos
    have h_exp :
        -(-θ) * ((1 - ε) * m) + (Real.exp (-θ) - 1) * m
          ≤ -(1 / 4) * m * ε ^ 2 := by
      have hpoint : Real.exp (-θ) - 1 ≤ -θ + θ ^ 2 :=
        exp_neg_sub_one_le_neg_add_sq_of_mem_Icc hθ_mem
      have hmul : (Real.exp (-θ) - 1) * m ≤ (-θ + θ ^ 2) * m :=
        mul_le_mul_of_nonneg_right hpoint hm_nonneg
      calc
        -(-θ) * ((1 - ε) * m) + (Real.exp (-θ) - 1) * m
            ≤ -(-θ) * ((1 - ε) * m) + (-θ + θ ^ 2) * m :=
              by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_left hmul (-(-θ) * ((1 - ε) * m))
        _ = -(1 / 4) * m * ε ^ 2 := by
              simp [θ]
              ring
    calc
      μ.real L
          ≤ Real.exp (-(-θ) * ((1 - ε) * m) + (Real.exp (-θ) - 1) * m) := by
            simpa [L, S, m] using hchernoff
      _ ≤ Real.exp (-(1 / 4) * m * ε ^ 2) :=
            Real.exp_le_exp.mpr h_exp
  have hsubset :
      {ω | ε * bernoulliParameterSum p
          ≤ |(∑ i, (X i ω : ℝ)) - bernoulliParameterSum p|}
        ⊆ U ∪ L := by
    intro ω hω
    by_cases hnonneg : 0 ≤ S ω - m
    · left
      have hω' : ε * m ≤ |S ω - m| := by
        simpa [S, m] using hω
      have hdist : ε * m ≤ S ω - m := by
        simpa [abs_of_nonneg hnonneg] using hω'
      dsimp [U, S]
      nlinarith
    · right
      have hneg : S ω - m < 0 := lt_of_not_ge hnonneg
      have hω' : ε * m ≤ |S ω - m| := by
        simpa [S, m] using hω
      have hdist : ε * m ≤ -(S ω - m) := by
        simpa [abs_of_neg hneg] using hω'
      dsimp [L, S]
      nlinarith
  calc
    μ.real {ω | ε * bernoulliParameterSum p
        ≤ |(∑ i, (X i ω : ℝ)) - bernoulliParameterSum p|}
        ≤ μ.real (U ∪ L) := measureReal_mono hsubset
    _ ≤ μ.real U + μ.real L := measureReal_union_le U L
    _ ≤ Real.exp (-(1 / 4) * m * ε ^ 2)
        + Real.exp (-(1 / 4) * m * ε ^ 2) :=
          add_le_add h_upper_tail h_lower_tail
    _ = 2 * Real.exp (-(1 / 4) * bernoulliParameterSum p * ε ^ 2) := by
          simp [m]
          ring

end ChernoffUpper

section PoissonChernoff

/-- Exponential moments of a Poisson random variable are integrable. -/
lemma integrable_exp_mul_poissonMeasure (lam : ℝ≥0) (theta : ℝ) :
    Integrable (fun n : ℕ => Real.exp (theta * (n : ℝ)))
      (ProbabilityTheory.poissonMeasure lam) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have hs :
      Summable fun n : ℕ =>
        Real.exp (-(lam : ℝ)) * (((lam : ℝ) * Real.exp theta) ^ n / (n.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * Real.exp theta)).summable.mul_left
      (Real.exp (-(lam : ℝ)))
  refine hs.congr ?_
  intro n
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hnfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [mul_pow, mul_comm theta (n : ℝ), Real.exp_nat_mul]
  field_simp [hnfac]

/-- MGF of a Poisson random variable. -/
lemma mgf_coe_nat_poissonMeasure_eq (lam : ℝ≥0) (theta : ℝ) :
    mgf (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure lam) theta =
      Real.exp ((Real.exp theta - 1) * (lam : ℝ)) := by
  rw [mgf, ProbabilityTheory.integral_poissonMeasure]
  have hseries :=
    (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * Real.exp theta)).mul_left
      (Real.exp (-(lam : ℝ)))
  calc
    (∑' n : ℕ,
        (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ)) •
          Real.exp (theta * (n : ℝ)))
        =
      ∑' n : ℕ,
        Real.exp (-(lam : ℝ)) * (((lam : ℝ) * Real.exp theta) ^ n / (n.factorial : ℝ)) := by
        apply tsum_congr
        intro n
        have hnfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        simp only [smul_eq_mul]
        rw [mul_pow, mul_comm theta (n : ℝ), Real.exp_nat_mul]
        field_simp [hnfac]
    _ = Real.exp (-(lam : ℝ)) * Real.exp ((lam : ℝ) * Real.exp theta) :=
        by simpa [← Real.exp_eq_exp_ℝ] using hseries.tsum_eq
    _ = Real.exp ((Real.exp theta - 1) * (lam : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- Chernoff's MGF bound for the upper tail of a Poisson random variable,
before optimizing the exponential parameter. -/
theorem chernoff_poisson_upper_exp
    {lam : ℝ≥0} {theta t : ℝ} (htheta : 0 ≤ theta) :
    (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | t ≤ (n : ℝ)}
      ≤ Real.exp (-theta * t + (Real.exp theta - 1) * (lam : ℝ)) := by
  have h_int :
      Integrable (fun n : ℕ => Real.exp (theta * (n : ℝ)))
        (ProbabilityTheory.poissonMeasure lam) :=
    integrable_exp_mul_poissonMeasure lam theta
  have htail :
      (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | t ≤ (n : ℝ)}
        ≤ Real.exp (-theta * t)
          * mgf (fun n : ℕ => (n : ℝ))
              (ProbabilityTheory.poissonMeasure lam) theta := by
    simpa [mgf] using
      ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := ProbabilityTheory.poissonMeasure lam) (X := fun n : ℕ => (n : ℝ))
        t htheta h_int
  calc
    (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | t ≤ (n : ℝ)}
        ≤ Real.exp (-theta * t)
          * mgf (fun n : ℕ => (n : ℝ))
              (ProbabilityTheory.poissonMeasure lam) theta := htail
    _ = Real.exp (-theta * t)
        * Real.exp ((Real.exp theta - 1) * (lam : ℝ)) := by
          simp [mgf_coe_nat_poissonMeasure_eq]
    _ = Real.exp (-theta * t + (Real.exp theta - 1) * (lam : ℝ)) := by
          rw [Real.exp_add]

/-- Chernoff's MGF bound for the lower tail of a Poisson random variable,
before optimizing the exponential parameter. -/
theorem chernoff_poisson_lower_exp
    {lam : ℝ≥0} {theta t : ℝ} (htheta : theta ≤ 0) :
    (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | (n : ℝ) ≤ t}
      ≤ Real.exp (-theta * t + (Real.exp theta - 1) * (lam : ℝ)) := by
  have h_int :
      Integrable (fun n : ℕ => Real.exp (theta * (n : ℝ)))
        (ProbabilityTheory.poissonMeasure lam) :=
    integrable_exp_mul_poissonMeasure lam theta
  have htail :
      (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | (n : ℝ) ≤ t}
        ≤ Real.exp (-theta * t)
          * mgf (fun n : ℕ => (n : ℝ))
              (ProbabilityTheory.poissonMeasure lam) theta := by
    simpa [mgf] using
      ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := ProbabilityTheory.poissonMeasure lam) (X := fun n : ℕ => (n : ℝ))
        t htheta h_int
  calc
    (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | (n : ℝ) ≤ t}
        ≤ Real.exp (-theta * t)
          * mgf (fun n : ℕ => (n : ℝ))
              (ProbabilityTheory.poissonMeasure lam) theta := htail
    _ = Real.exp (-theta * t)
        * Real.exp ((Real.exp theta - 1) * (lam : ℝ)) := by
          simp [mgf_coe_nat_poissonMeasure_eq]
    _ = Real.exp (-theta * t + (Real.exp theta - 1) * (lam : ℝ)) := by
          rw [Real.exp_add]

/-- HDP Exercise 2.3.3, Poisson upper-tail Chernoff bound, in the
nondegenerate case `0 < λ`. -/
theorem chernoff_poisson_upper_pos_mean
    {lam : ℝ≥0} (hlam : 0 < (lam : ℝ)) {t : ℝ} (ht : (lam : ℝ) < t) :
    (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | t ≤ (n : ℝ)}
      ≤ Real.exp (-(lam : ℝ)) * (Real.exp 1 * (lam : ℝ) / t) ^ t := by
  let m : ℝ := (lam : ℝ)
  have htpos : 0 < t := hlam.trans ht
  have hratio_pos : 0 < t / m := div_pos htpos hlam
  have hone_le_ratio : 1 ≤ t / m := by
    rw [le_div_iff₀ hlam]
    simpa [m] using ht.le
  have htheta_nonneg : 0 ≤ Real.log (t / m) :=
    Real.log_nonneg hone_le_ratio
  have h_int :
      Integrable (fun n : ℕ => Real.exp (Real.log (t / m) * (n : ℝ)))
        (ProbabilityTheory.poissonMeasure lam) :=
    integrable_exp_mul_poissonMeasure lam (Real.log (t / m))
  have htail :
      (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | t ≤ (n : ℝ)}
        ≤ Real.exp (-(Real.log (t / m)) * t)
          * mgf (fun n : ℕ => (n : ℝ))
              (ProbabilityTheory.poissonMeasure lam) (Real.log (t / m)) := by
    simpa [mgf] using
      ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := ProbabilityTheory.poissonMeasure lam) (X := fun n : ℕ => (n : ℝ))
        t htheta_nonneg h_int
  have hclosed :
      Real.exp (-(Real.log (t / m)) * t)
        * Real.exp ((Real.exp (Real.log (t / m)) - 1) * m)
        =
      Real.exp (-m) * (Real.exp 1 * m / t) ^ t := by
    have hm_ne : m ≠ 0 := ne_of_gt hlam
    have ht_ne : t ≠ 0 := ne_of_gt htpos
    have hbase_pos : 0 < Real.exp 1 * m / t := by
      positivity
    have hlog_base :
        Real.log (Real.exp 1 * m / t) = 1 - Real.log (t / m) := by
      calc
        Real.log (Real.exp 1 * m / t)
            = Real.log (Real.exp 1 * (m / t)) := by ring_nf
        _ = Real.log (Real.exp 1) + Real.log (m / t) := by
          rw [Real.log_mul (Real.exp_ne_zero 1) (div_ne_zero hm_ne ht_ne)]
        _ = 1 + (Real.log m - Real.log t) := by
          rw [Real.log_exp, Real.log_div hm_ne ht_ne]
        _ = 1 - Real.log (t / m) := by
          rw [Real.log_div ht_ne hm_ne]
          ring
    rw [← Real.exp_add]
    rw [Real.rpow_def_of_pos hbase_pos]
    rw [← Real.exp_add]
    congr 1
    rw [Real.exp_log hratio_pos, hlog_base]
    field_simp [hm_ne, ht_ne]
    ring
  calc
    (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | t ≤ (n : ℝ)}
        ≤ Real.exp (-(Real.log (t / m)) * t)
          * mgf (fun n : ℕ => (n : ℝ))
              (ProbabilityTheory.poissonMeasure lam) (Real.log (t / m)) := htail
    _ = Real.exp (-(Real.log (t / m)) * t)
        * Real.exp ((Real.exp (Real.log (t / m)) - 1) * m) := by
          simp [mgf_coe_nat_poissonMeasure_eq, m]
    _ = Real.exp (-m) * (Real.exp 1 * m / t) ^ t := hclosed
    _ = Real.exp (-(lam : ℝ)) * (Real.exp 1 * (lam : ℝ) / t) ^ t := by simp [m]

end PoissonChernoff

section PoissonLowerChernoff

/-- HDP Exercise 2.3.6 support lemma: Poisson lower-tail Chernoff bound, in
the nondegenerate range `0 < t < λ`. -/
theorem chernoff_poisson_lower_pos
    {lam : ℝ≥0} {t : ℝ} (htpos : 0 < t) (ht : t < (lam : ℝ)) :
    (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | (n : ℝ) ≤ t}
      ≤ Real.exp (-(lam : ℝ)) * (Real.exp 1 * (lam : ℝ) / t) ^ t := by
  let m : ℝ := (lam : ℝ)
  have hlam : 0 < m := htpos.trans ht
  have hratio_pos : 0 < t / m := div_pos htpos hlam
  have hratio_le_one : t / m ≤ 1 := by
    rw [div_le_one₀ hlam]
    exact ht.le
  have htheta_nonpos : Real.log (t / m) ≤ 0 :=
    Real.log_nonpos hratio_pos.le hratio_le_one
  have h_int :
      Integrable (fun n : ℕ => Real.exp (Real.log (t / m) * (n : ℝ)))
        (ProbabilityTheory.poissonMeasure lam) :=
    integrable_exp_mul_poissonMeasure lam (Real.log (t / m))
  have htail :
      (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | (n : ℝ) ≤ t}
        ≤ Real.exp (-(Real.log (t / m)) * t)
          * mgf (fun n : ℕ => (n : ℝ))
              (ProbabilityTheory.poissonMeasure lam) (Real.log (t / m)) := by
    simpa [mgf] using
      ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := ProbabilityTheory.poissonMeasure lam) (X := fun n : ℕ => (n : ℝ))
        t htheta_nonpos h_int
  have hclosed :
      Real.exp (-(Real.log (t / m)) * t)
        * Real.exp ((Real.exp (Real.log (t / m)) - 1) * m)
        =
      Real.exp (-m) * (Real.exp 1 * m / t) ^ t := by
    have hm_ne : m ≠ 0 := ne_of_gt hlam
    have ht_ne : t ≠ 0 := ne_of_gt htpos
    have hbase_pos : 0 < Real.exp 1 * m / t := by
      positivity
    have hlog_base :
        Real.log (Real.exp 1 * m / t) = 1 - Real.log (t / m) := by
      calc
        Real.log (Real.exp 1 * m / t)
            = Real.log (Real.exp 1 * (m / t)) := by ring_nf
        _ = Real.log (Real.exp 1) + Real.log (m / t) := by
          rw [Real.log_mul (Real.exp_ne_zero 1) (div_ne_zero hm_ne ht_ne)]
        _ = 1 + (Real.log m - Real.log t) := by
          rw [Real.log_exp, Real.log_div hm_ne ht_ne]
        _ = 1 - Real.log (t / m) := by
          rw [Real.log_div ht_ne hm_ne]
          ring
    rw [← Real.exp_add]
    rw [Real.rpow_def_of_pos hbase_pos]
    rw [← Real.exp_add]
    congr 1
    rw [Real.exp_log hratio_pos, hlog_base]
    field_simp [hm_ne, ht_ne]
    ring
  calc
    (ProbabilityTheory.poissonMeasure lam).real {n : ℕ | (n : ℝ) ≤ t}
        ≤ Real.exp (-(Real.log (t / m)) * t)
          * mgf (fun n : ℕ => (n : ℝ))
              (ProbabilityTheory.poissonMeasure lam) (Real.log (t / m)) := htail
    _ = Real.exp (-(Real.log (t / m)) * t)
        * Real.exp ((Real.exp (Real.log (t / m)) - 1) * m) := by
          simp [mgf_coe_nat_poissonMeasure_eq, m]
    _ = Real.exp (-m) * (Real.exp 1 * m / t) ^ t := hclosed
    _ = Real.exp (-(lam : ℝ)) * (Real.exp 1 * (lam : ℝ) / t) ^ t := by simp [m]

end PoissonLowerChernoff

section PoissonSmallDeviation

/-- HDP Exercise 2.3.6, Poisson distribution near the mean. The book states
the result with an unspecified absolute constant; this formalization gives the
explicit constant `c = 1/4`. -/
theorem poisson_two_sided_near_mean
    {lam : ℝ≥0} {ε : ℝ} (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) :
    (ProbabilityTheory.poissonMeasure lam).real
        {n : ℕ | ε * (lam : ℝ) ≤ |(n : ℝ) - (lam : ℝ)|}
      ≤ 2 * Real.exp (-(1 / 4) * (lam : ℝ) * ε ^ 2) := by
  let m : ℝ := (lam : ℝ)
  let θ : ℝ := ε / 2
  let U : Set ℕ := {n : ℕ | (1 + ε) * m ≤ (n : ℝ)}
  let L : Set ℕ := {n : ℕ | (n : ℝ) ≤ (1 - ε) * m}
  have hm_nonneg : 0 ≤ m := by exact_mod_cast (NNReal.coe_nonneg lam)
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ]
    linarith
  have hθ_le_one : θ ≤ 1 := by
    dsimp [θ]
    linarith [hε_le_one]
  have hθ_mem : θ ∈ Set.Icc 0 1 := ⟨hθ_nonneg, hθ_le_one⟩
  have h_upper_tail :
      (ProbabilityTheory.poissonMeasure lam).real U
        ≤ Real.exp (-(1 / 4) * m * ε ^ 2) := by
    have hchernoff :=
      chernoff_poisson_upper_exp
        (lam := lam) (theta := θ) (t := (1 + ε) * m) hθ_nonneg
    have h_exp :
        -θ * ((1 + ε) * m) + (Real.exp θ - 1) * m
          ≤ -(1 / 4) * m * ε ^ 2 := by
      have hpoint : Real.exp θ - 1 ≤ θ + θ ^ 2 :=
        exp_sub_one_le_self_add_sq_of_mem_Icc hθ_mem
      have hmul : (Real.exp θ - 1) * m ≤ (θ + θ ^ 2) * m :=
        mul_le_mul_of_nonneg_right hpoint hm_nonneg
      calc
        -θ * ((1 + ε) * m) + (Real.exp θ - 1) * m
            ≤ -θ * ((1 + ε) * m) + (θ + θ ^ 2) * m :=
              by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_left hmul (-θ * ((1 + ε) * m))
        _ = -(1 / 4) * m * ε ^ 2 := by
              simp [θ]
              ring
    calc
      (ProbabilityTheory.poissonMeasure lam).real U
          ≤ Real.exp (-θ * ((1 + ε) * m) + (Real.exp θ - 1) * (lam : ℝ)) := by
            simpa [U, m] using hchernoff
      _ = Real.exp (-θ * ((1 + ε) * m) + (Real.exp θ - 1) * m) := by
            simp [m]
      _ ≤ Real.exp (-(1 / 4) * m * ε ^ 2) :=
            Real.exp_le_exp.mpr h_exp
  have h_lower_tail :
      (ProbabilityTheory.poissonMeasure lam).real L
        ≤ Real.exp (-(1 / 4) * m * ε ^ 2) := by
    have hθ_nonpos : -θ ≤ 0 := by linarith
    have hchernoff :=
      chernoff_poisson_lower_exp
        (lam := lam) (theta := -θ) (t := (1 - ε) * m) hθ_nonpos
    have h_exp :
        -(-θ) * ((1 - ε) * m) + (Real.exp (-θ) - 1) * m
          ≤ -(1 / 4) * m * ε ^ 2 := by
      have hpoint : Real.exp (-θ) - 1 ≤ -θ + θ ^ 2 :=
        exp_neg_sub_one_le_neg_add_sq_of_mem_Icc hθ_mem
      have hmul : (Real.exp (-θ) - 1) * m ≤ (-θ + θ ^ 2) * m :=
        mul_le_mul_of_nonneg_right hpoint hm_nonneg
      calc
        -(-θ) * ((1 - ε) * m) + (Real.exp (-θ) - 1) * m
            ≤ -(-θ) * ((1 - ε) * m) + (-θ + θ ^ 2) * m :=
              by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_left hmul (-(-θ) * ((1 - ε) * m))
        _ = -(1 / 4) * m * ε ^ 2 := by
              simp [θ]
              ring
    calc
      (ProbabilityTheory.poissonMeasure lam).real L
          ≤ Real.exp (-(-θ) * ((1 - ε) * m) + (Real.exp (-θ) - 1) * (lam : ℝ)) := by
            simpa [L, m] using hchernoff
      _ = Real.exp (-(-θ) * ((1 - ε) * m) + (Real.exp (-θ) - 1) * m) := by
            simp [m]
      _ ≤ Real.exp (-(1 / 4) * m * ε ^ 2) :=
            Real.exp_le_exp.mpr h_exp
  have hsubset :
      {n : ℕ | ε * (lam : ℝ) ≤ |(n : ℝ) - (lam : ℝ)|}
        ⊆ U ∪ L := by
    intro n hn
    by_cases hnonneg : 0 ≤ (n : ℝ) - m
    · left
      have hdist : ε * m ≤ (n : ℝ) - m := by
        simpa [m, abs_of_nonneg hnonneg] using hn
      dsimp [U]
      nlinarith
    · right
      have hneg : (n : ℝ) - m < 0 := lt_of_not_ge hnonneg
      have hdist : ε * m ≤ -((n : ℝ) - m) := by
        simpa [m, abs_of_neg hneg] using hn
      dsimp [L]
      nlinarith
  calc
    (ProbabilityTheory.poissonMeasure lam).real
        {n : ℕ | ε * (lam : ℝ) ≤ |(n : ℝ) - (lam : ℝ)|}
        ≤ (ProbabilityTheory.poissonMeasure lam).real (U ∪ L) :=
          measureReal_mono hsubset
    _ ≤ (ProbabilityTheory.poissonMeasure lam).real U
        + (ProbabilityTheory.poissonMeasure lam).real L :=
          measureReal_union_le U L
    _ ≤ Real.exp (-(1 / 4) * m * ε ^ 2)
        + Real.exp (-(1 / 4) * m * ε ^ 2) :=
          add_le_add h_upper_tail h_lower_tail
    _ = 2 * Real.exp (-(1 / 4) * (lam : ℝ) * ε ^ 2) := by
          simp [m]
          ring

/-- HDP Exercise 2.3.6 in the book's `t`-deviation parameterization:
`P{|X - λ| ≥ t} ≤ 2 exp (-c t² / λ)` for `0 ≤ t ≤ λ`, with `c = 1/4`.
The case `λ = 0` is included through the explicit hypotheses. -/
theorem poisson_two_sided_near_mean_t
    {lam : ℝ≥0} {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_le : t ≤ (lam : ℝ)) :
    (ProbabilityTheory.poissonMeasure lam).real
        {n : ℕ | t ≤ |(n : ℝ) - (lam : ℝ)|}
      ≤ 2 * Real.exp (-(1 / 4) * t ^ 2 / (lam : ℝ)) := by
  by_cases hlam : (lam : ℝ) = 0
  · have ht0 : t = 0 := by linarith
    have hbound :
        2 * Real.exp (-(1 / 4) * t ^ 2 / (lam : ℝ)) = 2 := by
      simp [ht0, hlam]
    calc
      (ProbabilityTheory.poissonMeasure lam).real
          {n : ℕ | t ≤ |(n : ℝ) - (lam : ℝ)|}
          ≤ 1 := measureReal_le_one
      _ ≤ 2 := by norm_num
      _ = 2 * Real.exp (-(1 / 4) * t ^ 2 / (lam : ℝ)) := hbound.symm
  · have hlam_pos : 0 < (lam : ℝ) :=
      lt_of_le_of_ne (by exact_mod_cast (NNReal.coe_nonneg lam)) (Ne.symm hlam)
    let ε : ℝ := t / (lam : ℝ)
    have hε_nonneg : 0 ≤ ε := div_nonneg ht_nonneg hlam_pos.le
    have hε_le_one : ε ≤ 1 := by
      rw [div_le_one₀ hlam_pos]
      exact ht_le
    have hmain := poisson_two_sided_near_mean
      (lam := lam) (ε := ε) hε_nonneg hε_le_one
    have hevent :
        {n : ℕ | t ≤ |(n : ℝ) - (lam : ℝ)|}
          =
        {n : ℕ | ε * (lam : ℝ) ≤ |(n : ℝ) - (lam : ℝ)|} := by
      ext n
      simp [ε, hlam]
    have hexp :
        2 * Real.exp (-(1 / 4) * (lam : ℝ) * ε ^ 2)
          =
        2 * Real.exp (-(1 / 4) * t ^ 2 / (lam : ℝ)) := by
      have hexponent :
          -(1 / 4) * (lam : ℝ) * ε ^ 2
            =
          -(1 / 4) * t ^ 2 / (lam : ℝ) := by
        dsimp [ε]
        field_simp [hlam]
      rw [hexponent]
    calc
      (ProbabilityTheory.poissonMeasure lam).real
          {n : ℕ | t ≤ |(n : ℝ) - (lam : ℝ)|}
          =
        (ProbabilityTheory.poissonMeasure lam).real
          {n : ℕ | ε * (lam : ℝ) ≤ |(n : ℝ) - (lam : ℝ)|} := by
          rw [hevent]
      _ ≤ 2 * Real.exp (-(1 / 4) * (lam : ℝ) * ε ^ 2) := hmain
      _ = 2 * Real.exp (-(1 / 4) * t ^ 2 / (lam : ℝ)) := hexp

end PoissonSmallDeviation

end LeanFpAnalysis.HDP
