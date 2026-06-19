import LeanFpAnalysis.HDP.Probability.Concentration.Hoeffding
import LeanFpAnalysis.HDP.Probability.Concentration.Normal
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Pareto
import Mathlib.Probability.Moments.SubGaussian

/-!
# Sub-gaussian Random Variables

Book-facing statements for HDP Chapter 2, Sections 2.5 and 2.6, phrased in
terms of mathlib's centered MGF proxy `HasSubgaussianMGF`.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace LeanFpAnalysis.HDP

section Proxies

variable {ι : Type*}

/-- The square of a real constant as a nonnegative sub-gaussian MGF proxy. -/
def subgaussianProxy (K : ℝ) : ℝ≥0 :=
  ⟨K ^ 2, sq_nonneg K⟩

/-- Sum of sub-gaussian MGF proxies, coerced to `ℝ` for exponential bounds. -/
def subgaussianProxySum [Fintype ι] (c : ι → ℝ≥0) : ℝ :=
  ∑ i, (c i : ℝ)

/-- Weighted sum of MGF proxies for `∑ i, a_i X_i`. -/
def weightedSubgaussianProxySum [Fintype ι] (a : ι → ℝ) (c : ι → ℝ≥0) : ℝ :=
  ∑ i, a i ^ 2 * (c i : ℝ)

@[simp]
lemma subgaussianProxy_coe (K : ℝ) :
    ((subgaussianProxy K : ℝ≥0) : ℝ) = K ^ 2 := rfl

lemma weightedSubgaussianProxySum_uniform [Fintype ι] (a : ι → ℝ) (K : ℝ) :
    weightedSubgaussianProxySum a (fun _ => subgaussianProxy K)
      = K ^ 2 * coeffL2NormSq a := by
  classical
  simp [weightedSubgaussianProxySum, coeffL2NormSq, Finset.mul_sum, mul_comm]

end Proxies

section OrliczDefinition

variable {Ω : Type*} [MeasurableSpace Ω]

/-- HDP Proposition 2.5.2(i): two-sided sub-gaussian tail decay with scale
`K`. -/
def subGaussianTailCondition (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ t, 0 ≤ t →
      μ.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2)

/-- HDP Proposition 2.5.2(ii): `L^p` growth at most `K sqrt p`.
The exponent is encoded as a nonnegative real, which is the native exponent
type for mathlib's `eLpNorm`. -/
def subGaussianMomentCondition (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ p : ℝ≥0, 1 ≤ (p : ℝ) →
      MemLp X (p : ℝ≥0∞) μ ∧
        eLpNorm X (p : ℝ≥0∞) μ ≤ ENNReal.ofReal (K * Real.sqrt (p : ℝ))

/-- HDP Proposition 2.5.2(iii): local exponential-square control. -/
def subGaussianSquareMGFCondition (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ θ, |θ| ≤ 1 / K →
      Integrable (fun ω => Real.exp (θ ^ 2 * X ω ^ 2)) μ ∧
        ∫ ω, Real.exp (θ ^ 2 * X ω ^ 2) ∂μ ≤
          Real.exp (K ^ 2 * θ ^ 2)

/-- HDP Definition 2.5.6, the Orlicz integrability condition
`E exp(X² / K²) ≤ 2` for a positive scale `K`. -/
def subGaussianOrliczCondition (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    Integrable (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) μ ∧
      ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2

/-- HDP Proposition 2.5.2(v): centered MGF growth in the book's convention,
`E exp(θX) ≤ exp(K²θ²)`. Mathlib's `HasSubgaussianMGF` uses the sharper
proxy convention `exp(c θ² / 2)`, and bridge lemmas below translate between
the two. -/
def subGaussianMGFCondition (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ θ,
      Integrable (fun ω => Real.exp (θ * X ω)) μ ∧
        mgf X μ θ ≤ Real.exp (K ^ 2 * θ ^ 2)

/-- HDP Definition 2.5.6: a random variable is sub-gaussian when it satisfies
the Orlicz exponential-square condition for some positive scale. -/
def IsSubGaussian (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ K, subGaussianOrliczCondition X μ K

/-- HDP Definition 2.5.6: the sub-gaussian norm
`‖X‖_{ψ₂} = inf {K > 0 : E exp(X² / K²) ≤ 2}`. -/
def subGaussianNorm (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | subGaussianOrliczCondition X μ K}

/-- A concrete Orlicz scale makes the random variable sub-gaussian. -/
theorem isSubGaussian_of_subGaussianOrliczCondition
    {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (hX : subGaussianOrliczCondition X μ K) :
    IsSubGaussian X μ :=
  ⟨K, hX⟩

/-- Any admissible Orlicz scale bounds the sub-gaussian norm from above. -/
theorem subGaussianNorm_le_of_subGaussianOrliczCondition
    {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (hX : subGaussianOrliczCondition X μ K) :
    subGaussianNorm X μ ≤ K := by
  unfold subGaussianNorm
  exact csInf_le
    ⟨0, fun L hL => hL.1.le⟩
    hX

/-- The `ψ₂` gauge is always nonnegative. If no Orlicz scale is admissible,
the defining `sInf` is the empty infimum, which is `0` in `ℝ`. -/
theorem subGaussianNorm_nonneg
    (X : Ω → ℝ) (μ : Measure Ω) :
    0 ≤ subGaussianNorm X μ := by
  unfold subGaussianNorm
  by_cases hne :
      ({K : ℝ | subGaussianOrliczCondition X μ K}).Nonempty
  · exact le_csInf hne fun K hK => hK.1.le
  · have hempty :
        {K : ℝ | subGaussianOrliczCondition X μ K} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

/-- Every positive scale is admissible for the zero random variable. -/
theorem subGaussianOrliczCondition_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℝ}
    (hK : 0 < K) :
    subGaussianOrliczCondition (fun _ω : Ω => (0 : ℝ)) μ K := by
  refine ⟨hK, ?_, ?_⟩
  · simp
  · simp

/-- Exercise 2.5.7 foundation: the zero random variable has `ψ₂` norm zero. -/
theorem subGaussianNorm_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ] :
    subGaussianNorm (fun _ω : Ω => (0 : ℝ)) μ = 0 := by
  refine le_antisymm ?_ (subGaussianNorm_nonneg _ μ)
  exact le_of_forall_gt_imp_ge_of_dense fun ε hε =>
    subGaussianNorm_le_of_subGaussianOrliczCondition
      (μ := μ) (X := fun _ω : Ω => (0 : ℝ)) (K := ε)
      (subGaussianOrliczCondition_zero (μ := μ) (K := ε) hε)

/-- Exercise 2.5.7 scaling infrastructure: multiplying a random variable by a
nonzero scalar multiplies every admissible Orlicz scale by `|a|`. -/
theorem subGaussianOrliczCondition_const_mul
    {X : Ω → ℝ} {μ : Measure Ω} {K a : ℝ}
    (ha : a ≠ 0)
    (hX : subGaussianOrliczCondition X μ K) :
    subGaussianOrliczCondition (fun ω => a * X ω) μ (|a| * K) := by
  rcases hX with ⟨hK, hInt, hBound⟩
  have hscale_pos : 0 < |a| * K :=
    mul_pos (abs_pos.mpr ha) hK
  have hEq :
      (fun ω => Real.exp ((a * X ω) ^ 2 / (|a| * K) ^ 2))
        = fun ω => Real.exp (X ω ^ 2 / K ^ 2) := by
    funext ω
    congr 1
    rw [mul_pow, mul_pow, sq_abs]
    field_simp [ha, hK.ne']
  refine ⟨hscale_pos, ?_, ?_⟩
  · rw [hEq]
    exact hInt
  · rw [hEq]
    exact hBound

/-- Exercise 2.5.7 scaling infrastructure, norm upper-bound form:
`‖aX‖_{ψ₂} ≤ |a| K` whenever `K` is an admissible Orlicz scale for `X`. -/
theorem subGaussianNorm_const_mul_le
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {K a : ℝ}
    (hX : subGaussianOrliczCondition X μ K) :
    subGaussianNorm (fun ω => a * X ω) μ ≤ |a| * K := by
  by_cases ha : a = 0
  · have hzero :
        (fun ω => a * X ω) = fun _ω : Ω => (0 : ℝ) := by
      funext ω
      simp [ha]
    rw [hzero, subGaussianNorm_zero]
    simp [ha]
  · exact
      subGaussianNorm_le_of_subGaussianOrliczCondition
        (subGaussianOrliczCondition_const_mul (μ := μ) (X := X) (K := K)
          (a := a) ha hX)

/-- Nonzero scalar multiples of sub-gaussian random variables are
sub-gaussian. -/
theorem isSubGaussian_const_mul_of_ne_zero
    {X : Ω → ℝ} {μ : Measure Ω} {a : ℝ}
    (ha : a ≠ 0) (hXsg : IsSubGaussian X μ) :
    IsSubGaussian (fun ω => a * X ω) μ := by
  rcases hXsg with ⟨K, hK⟩
  exact ⟨|a| * K, subGaussianOrliczCondition_const_mul ha hK⟩

/-- Exercise 2.5.7 scalar homogeneity, upper-bound half:
`‖aX‖_{ψ₂} ≤ |a| ‖X‖_{ψ₂}`. -/
theorem subGaussianNorm_const_mul_le_norm
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {a : ℝ}
    (hXsg : IsSubGaussian X μ) :
    subGaussianNorm (fun ω => a * X ω) μ
      ≤ |a| * subGaussianNorm X μ := by
  by_cases ha : a = 0
  · simp [ha, subGaussianNorm_zero]
  have ha_abs_pos : 0 < |a| := abs_pos.mpr ha
  have hXset :
      ({K : ℝ | subGaussianOrliczCondition X μ K}).Nonempty := by
    simpa [IsSubGaussian] using hXsg
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro r hr
  have hgap : 0 < r - |a| * subGaussianNorm X μ := by
    linarith
  have hε : 0 < (r - |a| * subGaussianNorm X μ) / |a| :=
    div_pos hgap ha_abs_pos
  obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos hXset hε
  have hKlt' :
      K < subGaussianNorm X μ
        + (r - |a| * subGaussianNorm X μ) / |a| := by
    simpa [subGaussianNorm] using hKlt
  have hmul_lt :
      |a| * K < r := by
    have hmul := mul_lt_mul_of_pos_left hKlt' ha_abs_pos
    have hright :
        |a| *
            (subGaussianNorm X μ
              + (r - |a| * subGaussianNorm X μ) / |a|) = r := by
      field_simp [ha_abs_pos.ne']
      ring
    simpa [hright] using hmul
  exact (subGaussianNorm_const_mul_le (μ := μ) (X := X) (K := K)
    (a := a) hK).trans hmul_lt.le

/-- Exercise 2.5.7 scalar homogeneity for the `ψ₂` gauge. -/
theorem subGaussianNorm_const_mul_eq
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {a : ℝ}
    (hXsg : IsSubGaussian X μ) :
    subGaussianNorm (fun ω => a * X ω) μ
      = |a| * subGaussianNorm X μ := by
  by_cases ha : a = 0
  · simp [ha, subGaussianNorm_zero]
  refine le_antisymm (subGaussianNorm_const_mul_le_norm (a := a) hXsg) ?_
  have hAXsg :
      IsSubGaussian (fun ω => a * X ω) μ :=
    isSubGaussian_const_mul_of_ne_zero (μ := μ) (X := X) (a := a) ha hXsg
  have hfun :
      (fun ω => a⁻¹ * (a * X ω)) = X := by
    funext ω
    field_simp [ha]
  have hinv_le :
      subGaussianNorm X μ
        ≤ |a⁻¹| * subGaussianNorm (fun ω => a * X ω) μ := by
    simpa [hfun] using
      (subGaussianNorm_const_mul_le_norm
        (μ := μ) (X := fun ω => a * X ω) (a := a⁻¹) hAXsg)
  have hmul :=
    mul_le_mul_of_nonneg_left hinv_le (abs_nonneg a)
  have habs_inv : |a| * |a⁻¹| = 1 := by
    rw [abs_inv]
    exact mul_inv_cancel₀ (abs_ne_zero.mpr ha)
  calc
    |a| * subGaussianNorm X μ
        ≤ |a| * (|a⁻¹| * subGaussianNorm (fun ω => a * X ω) μ) :=
      hmul
    _ = subGaussianNorm (fun ω => a * X ω) μ := by
      rw [← mul_assoc, habs_inv, one_mul]

/-- One direction of HDP Proposition 2.5.2: the Orlicz condition
`E exp(X² / K²) ≤ 2` implies the two-sided tail bound
`P{|X| ≥ t} ≤ 2 exp(-t² / K²)`. -/
theorem subGaussianOrliczCondition_tail_le
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {K t : ℝ}
    (hX : subGaussianOrliczCondition X μ K) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|}
      ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) := by
  rcases hX with ⟨hKpos, hInt, hExp_le⟩
  let Y : Ω → ℝ := fun ω => Real.exp (X ω ^ 2 / K ^ 2)
  have hY_nonneg : 0 ≤ᵐ[μ] Y :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have hthreshold_pos : 0 < Real.exp (t ^ 2 / K ^ 2) :=
    Real.exp_pos _
  have hsubset :
      {ω | t ≤ |X ω|} ⊆ {ω | Real.exp (t ^ 2 / K ^ 2) ≤ Y ω} := by
    intro ω hω
    change Real.exp (t ^ 2 / K ^ 2) ≤ Y ω
    rw [Real.exp_le_exp]
    have ht_abs : t ≤ |X ω| := by
      simpa using hω
    have hsquares : t ^ 2 ≤ |X ω| ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg ht] using ht_abs)
    have hden_nonneg : 0 ≤ K ^ 2 := sq_nonneg K
    have hdiv : t ^ 2 / K ^ 2 ≤ |X ω| ^ 2 / K ^ 2 :=
      div_le_div_of_nonneg_right hsquares hden_nonneg
    simpa [Y, sq_abs] using hdiv
  have hmarkov :=
    markov_inequality
      (μ := μ) (X := Y) hY_nonneg hInt (t := Real.exp (t ^ 2 / K ^ 2))
      hthreshold_pos
  calc
    μ.real {ω | t ≤ |X ω|}
        ≤ μ.real {ω | Real.exp (t ^ 2 / K ^ 2) ≤ Y ω} :=
      MeasureTheory.measureReal_mono hsubset
    _ ≤ (∫ ω, Y ω ∂μ) / Real.exp (t ^ 2 / K ^ 2) := hmarkov
    _ ≤ 2 / Real.exp (t ^ 2 / K ^ 2) := by
      exact div_le_div_of_nonneg_right hExp_le hthreshold_pos.le
    _ = 2 * Real.exp (-(t ^ 2) / K ^ 2) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring_nf

/-- Book-facing predicate form of the implication
`E exp(X² / K²) ≤ 2` `⇒` sub-gaussian tails. -/
theorem subGaussianTailCondition_of_subGaussianOrliczCondition
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℝ}
    (hX : subGaussianOrliczCondition X μ K) :
    subGaussianTailCondition X μ K :=
  ⟨hX.1, fun t ht => subGaussianOrliczCondition_tail_le (t := t) hX ht⟩

/-- Sub-gaussian tail scales are monotone: if `K` works and `K ≤ L`, then
the larger scale `L` also works. -/
theorem subGaussianTailCondition_mono_scale
    {X : Ω → ℝ} {μ : Measure Ω} {K L : ℝ}
    (hX : subGaussianTailCondition X μ K)
    (hKL : K ≤ L) :
    subGaussianTailCondition X μ L := by
  refine ⟨hX.1.trans_le hKL, ?_⟩
  intro t ht
  have hKpos : 0 < K := hX.1
  have hLpos : 0 < L := hKpos.trans_le hKL
  have hsq : K ^ 2 ≤ L ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_pos hKpos, abs_of_pos hLpos] using hKL)
  have hdiv :
      -(t ^ 2) / K ^ 2 ≤ -(t ^ 2) / L ^ 2 := by
    have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hKpos
    have hLsq_pos : 0 < L ^ 2 := sq_pos_of_pos hLpos
    rw [div_le_div_iff₀ hKsq_pos hLsq_pos]
    have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg t)
    nlinarith
  calc
    μ.real {ω | t ≤ |X ω|}
        ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) := hX.2 t ht
    _ ≤ 2 * Real.exp (-(t ^ 2) / L ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hdiv)
        (by norm_num : (0 : ℝ) ≤ 2)

/-- Any scale strictly larger than the `ψ₂` norm is an admissible tail scale.
This is the norm-to-tail bridge used in the exact Exercise 2.5.10 corollaries. -/
theorem subGaussianTailCondition_of_subGaussianNorm_lt
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℝ}
    (hXsg : IsSubGaussian X μ)
    (hK : subGaussianNorm X μ < K) :
    subGaussianTailCondition X μ K := by
  have hXset :
      ({L : ℝ | subGaussianOrliczCondition X μ L}).Nonempty := by
    simpa [IsSubGaussian] using hXsg
  have hε : 0 < K - subGaussianNorm X μ := by linarith
  obtain ⟨L, hL, hLlt⟩ := Real.lt_sInf_add_pos hXset hε
  have hLltK : L < K := by
    have hLlt' : L < subGaussianNorm X μ + (K - subGaussianNorm X μ) := by
      simpa [subGaussianNorm] using hLlt
    simpa using hLlt'
  exact subGaussianTailCondition_mono_scale
    (subGaussianTailCondition_of_subGaussianOrliczCondition (μ := μ) hL)
    hLltK.le

/-- If an Orlicz scale `K` is available, then all smaller square-exponential
parameters `θ² ≤ 1/K²` are integrable and have expectation at most `2`.
This is the direct monotonicity part behind the easy `iv ⇒ iii` step in
HDP Proposition 2.5.2. -/
theorem subGaussianOrliczCondition_square_exp_le
    {X : Ω → ℝ} {μ : Measure Ω} {K θ : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subGaussianOrliczCondition X μ K)
    (hθ : θ ^ 2 ≤ 1 / K ^ 2) :
    Integrable (fun ω => Real.exp (θ ^ 2 * X ω ^ 2)) μ ∧
      ∫ ω, Real.exp (θ ^ 2 * X ω ^ 2) ∂μ ≤ 2 := by
  rcases hX with ⟨_hKpos, hInt, hExp_le⟩
  have hf_aemeas :
      AEMeasurable (fun ω => Real.exp (θ ^ 2 * X ω ^ 2)) μ := by
    fun_prop
  have hpoint :
      ∀ ω, Real.exp (θ ^ 2 * X ω ^ 2)
        ≤ Real.exp (X ω ^ 2 / K ^ 2) := by
    intro ω
    rw [Real.exp_le_exp]
    have hx2_nonneg : 0 ≤ X ω ^ 2 := sq_nonneg _
    calc
      θ ^ 2 * X ω ^ 2 ≤ (1 / K ^ 2) * X ω ^ 2 :=
        mul_le_mul_of_nonneg_right hθ hx2_nonneg
      _ = X ω ^ 2 / K ^ 2 := by ring
  have hInt_small :
      Integrable (fun ω => Real.exp (θ ^ 2 * X ω ^ 2)) μ := by
    refine hInt.mono hf_aemeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hpoint ω
  refine ⟨hInt_small, ?_⟩
  calc
    ∫ ω, Real.exp (θ ^ 2 * X ω ^ 2) ∂μ
        ≤ ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ :=
      integral_mono hInt_small hInt hpoint
    _ ≤ 2 := hExp_le

/-- The preceding monotonicity lemma in the book's local form
`|θ| ≤ 1/K`. -/
theorem subGaussianOrliczCondition_square_exp_le_of_abs_le
    {X : Ω → ℝ} {μ : Measure Ω} {K θ : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subGaussianOrliczCondition X μ K)
    (hθ : |θ| ≤ 1 / K) :
    Integrable (fun ω => Real.exp (θ ^ 2 * X ω ^ 2)) μ ∧
      ∫ ω, Real.exp (θ ^ 2 * X ω ^ 2) ∂μ ≤ 2 := by
  have hKpos : 0 < K := hX.1
  have hθ_abs : |θ| ≤ |1 / K| := by
    simpa [one_div, abs_inv, abs_of_pos hKpos] using hθ
  have hsq : θ ^ 2 ≤ (1 / K) ^ 2 :=
    sq_le_sq.mpr hθ_abs
  have hsq' : θ ^ 2 ≤ 1 / K ^ 2 := by
    simpa [one_div, inv_pow] using hsq
  exact subGaussianOrliczCondition_square_exp_le hXm hX hsq'

/-- Admissible Orlicz scales are monotone: if `K` works and `K ≤ L`, then
the larger scale `L` also works. -/
theorem subGaussianOrliczCondition_mono_scale
    {X : Ω → ℝ} {μ : Measure Ω} {K L : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subGaussianOrliczCondition X μ K)
    (hKL : K ≤ L) :
    subGaussianOrliczCondition X μ L := by
  have hKpos : 0 < K := hX.1
  have hLpos : 0 < L := hKpos.trans_le hKL
  have hrecip : 1 / L ≤ 1 / K :=
    (one_div_le_one_div hLpos hKpos).mpr hKL
  have hθ : |1 / L| ≤ 1 / K := by
    rw [abs_of_pos (one_div_pos.mpr hLpos)]
    exact hrecip
  have hsmall :=
    subGaussianOrliczCondition_square_exp_le_of_abs_le
      (μ := μ) (X := X) (K := K) (θ := 1 / L)
      hXm hX hθ
  have hfun :
      (fun ω => Real.exp (X ω ^ 2 / L ^ 2)) =
        fun ω => Real.exp ((1 / L) ^ 2 * X ω ^ 2) := by
    funext ω
    congr 1
    ring
  refine ⟨hLpos, ?_, ?_⟩
  · rw [hfun]
    exact hsmall.1
  · rw [hfun]
    exact hsmall.2

/-- Pointwise Luxemburg convexity estimate behind the triangle inequality for
the `ψ₂` gauge. -/
lemma exp_sq_add_div_le_weighted_exp_sq
    {x y K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    Real.exp ((x + y) ^ 2 / (K + L) ^ 2)
      ≤ K / (K + L) * Real.exp (x ^ 2 / K ^ 2)
        + L / (K + L) * Real.exp (y ^ 2 / L ^ 2) := by
  have hKL : 0 < K + L := add_pos hK hL
  let a : ℝ := K / (K + L)
  let b : ℝ := L / (K + L)
  let u : ℝ := |x| / K
  let v : ℝ := |y| / L
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    positivity
  have hv_nonneg : 0 ≤ v := by
    dsimp [v]
    positivity
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [hKL.ne']
  have habs_le : |x + y| / (K + L) ≤ a * u + b * v := by
    calc
      |x + y| / (K + L) ≤ (|x| + |y|) / (K + L) :=
        div_le_div_of_nonneg_right (abs_add_le x y) hKL.le
      _ = a * u + b * v := by
        dsimp [a, b, u, v]
        field_simp [hK.ne', hL.ne', hKL.ne']
  have hright_nonneg : 0 ≤ a * u + b * v :=
    add_nonneg (mul_nonneg ha_nonneg hu_nonneg)
      (mul_nonneg hb_nonneg hv_nonneg)
  have hsq_abs :
      (|x + y| / (K + L)) ^ 2 ≤ (a * u + b * v) ^ 2 := by
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg (div_nonneg (abs_nonneg _) hKL.le),
        abs_of_nonneg hright_nonneg] using habs_le)
  have hsq_weight :
      (a * u + b * v) ^ 2 ≤ a * u ^ 2 + b * v ^ 2 := by
    have hnonneg : 0 ≤ a * b * (u - v) ^ 2 :=
      mul_nonneg (mul_nonneg ha_nonneg hb_nonneg) (sq_nonneg _)
    nlinarith [hab, hnonneg]
  have hquad :
      (x + y) ^ 2 / (K + L) ^ 2
        ≤ a * (x ^ 2 / K ^ 2) + b * (y ^ 2 / L ^ 2) := by
    calc
      (x + y) ^ 2 / (K + L) ^ 2
          = (|x + y| / (K + L)) ^ 2 := by
        rw [div_pow, sq_abs]
      _ ≤ (a * u + b * v) ^ 2 := hsq_abs
      _ ≤ a * u ^ 2 + b * v ^ 2 := hsq_weight
      _ = a * (x ^ 2 / K ^ 2) + b * (y ^ 2 / L ^ 2) := by
        dsimp [u, v]
        rw [div_pow, div_pow, sq_abs, sq_abs]
  have hconv :
      Real.exp (a * (x ^ 2 / K ^ 2) + b * (y ^ 2 / L ^ 2))
        ≤ a * Real.exp (x ^ 2 / K ^ 2)
          + b * Real.exp (y ^ 2 / L ^ 2) := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (convexOn_exp.2 (Set.mem_univ (x ^ 2 / K ^ 2))
        (Set.mem_univ (y ^ 2 / L ^ 2)) ha_nonneg hb_nonneg hab)
  calc
    Real.exp ((x + y) ^ 2 / (K + L) ^ 2)
        ≤ Real.exp (a * (x ^ 2 / K ^ 2) + b * (y ^ 2 / L ^ 2)) :=
      Real.exp_le_exp.mpr hquad
    _ ≤ a * Real.exp (x ^ 2 / K ^ 2)
        + b * Real.exp (y ^ 2 / L ^ 2) := hconv
    _ = K / (K + L) * Real.exp (x ^ 2 / K ^ 2)
        + L / (K + L) * Real.exp (y ^ 2 / L ^ 2) := by
      rfl

/-- Exercise 2.5.7 addition infrastructure: admissible Orlicz scales add. -/
theorem subGaussianOrliczCondition_add
    {X Y : Ω → ℝ} {μ : Measure Ω} {K L : ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : subGaussianOrliczCondition X μ K)
    (hY : subGaussianOrliczCondition Y μ L) :
    subGaussianOrliczCondition (fun ω => X ω + Y ω) μ (K + L) := by
  rcases hX with ⟨hKpos, hXInt, hXBound⟩
  rcases hY with ⟨hLpos, hYInt, hYBound⟩
  have hKL : 0 < K + L := add_pos hKpos hLpos
  let a : ℝ := K / (K + L)
  let b : ℝ := L / (K + L)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [hKL.ne']
  let F : Ω → ℝ :=
    fun ω => Real.exp ((X ω + Y ω) ^ 2 / (K + L) ^ 2)
  let G : Ω → ℝ :=
    fun ω => a * Real.exp (X ω ^ 2 / K ^ 2)
      + b * Real.exp (Y ω ^ 2 / L ^ 2)
  have hpoint : ∀ ω, F ω ≤ G ω := by
    intro ω
    dsimp [F, G, a, b]
    exact exp_sq_add_div_le_weighted_exp_sq hKpos hLpos
  have hGInt : Integrable G μ := by
    dsimp [G]
    exact (hXInt.const_mul a).add (hYInt.const_mul b)
  have hFaem : AEMeasurable F μ := by
    dsimp [F]
    fun_prop
  have hFInt : Integrable F μ := by
    refine hGInt.mono_nonneg hFaem.aestronglyMeasurable ?_ ?_
    · exact Filter.Eventually.of_forall fun ω => by
        dsimp [F]
        exact (Real.exp_pos _).le
    · exact Filter.Eventually.of_forall hpoint
  refine ⟨hKL, ?_, ?_⟩
  · simpa [F] using hFInt
  · calc
      ∫ ω, Real.exp ((X ω + Y ω) ^ 2 / (K + L) ^ 2) ∂μ
          = ∫ ω, F ω ∂μ := rfl
      _ ≤ ∫ ω, G ω ∂μ :=
        integral_mono hFInt hGInt hpoint
      _ = a * ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ
          + b * ∫ ω, Real.exp (Y ω ^ 2 / L ^ 2) ∂μ := by
        dsimp [G]
        rw [integral_add (hXInt.const_mul a) (hYInt.const_mul b),
          integral_const_mul, integral_const_mul]
      _ ≤ a * 2 + b * 2 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hXBound ha_nonneg)
          (mul_le_mul_of_nonneg_left hYBound hb_nonneg)
      _ = 2 := by
        rw [← add_mul, hab]
        ring

/-- Exercise 2.5.7 addition infrastructure, norm upper-bound form:
`‖X+Y‖_{ψ₂} ≤ K + L` when `K` and `L` are admissible scales. -/
theorem subGaussianNorm_add_le_of_subGaussianOrliczCondition
    {X Y : Ω → ℝ} {μ : Measure Ω} {K L : ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : subGaussianOrliczCondition X μ K)
    (hY : subGaussianOrliczCondition Y μ L) :
    subGaussianNorm (fun ω => X ω + Y ω) μ ≤ K + L :=
  subGaussianNorm_le_of_subGaussianOrliczCondition
    (subGaussianOrliczCondition_add hXm hYm hX hY)

/-- Exercise 2.5.7 triangle inequality for the `ψ₂` gauge on sub-gaussian
random variables. -/
theorem subGaussianNorm_add_le
    {X Y : Ω → ℝ} {μ : Measure Ω}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hXsg : IsSubGaussian X μ) (hYsg : IsSubGaussian Y μ) :
    subGaussianNorm (fun ω => X ω + Y ω) μ
      ≤ subGaussianNorm X μ + subGaussianNorm Y μ := by
  have hXset :
      ({K : ℝ | subGaussianOrliczCondition X μ K}).Nonempty := by
    simpa [IsSubGaussian] using hXsg
  have hYset :
      ({L : ℝ | subGaussianOrliczCondition Y μ L}).Nonempty := by
    simpa [IsSubGaussian] using hYsg
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro r hr
  have hgap : 0 < r - (subGaussianNorm X μ + subGaussianNorm Y μ) := by
    linarith
  have hhalf : 0 < (r - (subGaussianNorm X μ + subGaussianNorm Y μ)) / 2 := by
    positivity
  obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos hXset hhalf
  obtain ⟨L, hL, hLlt⟩ := Real.lt_sInf_add_pos hYset hhalf
  have hKlt' :
      K < subGaussianNorm X μ
        + (r - (subGaussianNorm X μ + subGaussianNorm Y μ)) / 2 := by
    simpa [subGaussianNorm] using hKlt
  have hLlt' :
      L < subGaussianNorm Y μ
        + (r - (subGaussianNorm X μ + subGaussianNorm Y μ)) / 2 := by
    simpa [subGaussianNorm] using hLlt
  have hadd :
      subGaussianNorm (fun ω => X ω + Y ω) μ ≤ K + L :=
    subGaussianNorm_add_le_of_subGaussianOrliczCondition hXm hYm hK hL
  have hsum_lt : K + L < r := by
    linarith
  exact hadd.trans hsum_lt.le

/-- If the `ψ₂` norm is positive and finite through an admissible scale, then
twice the norm is itself an admissible Orlicz scale. -/
theorem subGaussianOrliczCondition_two_mul_norm
    {X : Ω → ℝ} {μ : Measure Ω}
    (hXm : AEMeasurable X μ)
    (hXsg : IsSubGaussian X μ)
    (hpos : 0 < subGaussianNorm X μ) :
    subGaussianOrliczCondition X μ (2 * subGaussianNorm X μ) := by
  let S : Set ℝ := {K : ℝ | subGaussianOrliczCondition X μ K}
  have hSnonempty : S.Nonempty := by
    rcases hXsg with ⟨K, hK⟩
    exact ⟨K, hK⟩
  obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos (s := S) hSnonempty hpos
  have hKlt' : K < subGaussianNorm X μ + subGaussianNorm X μ := by
    simpa [subGaussianNorm, S] using hKlt
  have hKlt_two : K < 2 * subGaussianNorm X μ := by
    nlinarith
  exact subGaussianOrliczCondition_mono_scale hXm hK hKlt_two.le

/-- If a sub-gaussian variable has `ψ₂` gauge zero, then every positive
Orlicz scale is admissible. -/
theorem subGaussianOrliczCondition_of_subGaussianNorm_eq_zero
    {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hXsg : IsSubGaussian X μ)
    (hnorm : subGaussianNorm X μ = 0)
    (hK : 0 < K) :
    subGaussianOrliczCondition X μ K := by
  have hXset :
      ({L : ℝ | subGaussianOrliczCondition X μ L}).Nonempty := by
    simpa [IsSubGaussian] using hXsg
  obtain ⟨L, hL, hLlt⟩ := Real.lt_sInf_add_pos hXset hK
  have hLltK : L < K := by
    have hsInf_zero :
        sInf {L : ℝ | subGaussianOrliczCondition X μ L} = 0 := by
      simpa [subGaussianNorm] using hnorm
    simpa [hsInf_zero] using hLlt
  exact subGaussianOrliczCondition_mono_scale hXm hL hLltK.le

/-- Positive tails of a zero-`ψ₂` sub-gaussian variable have probability
zero. -/
theorem subGaussianNorm_eq_zero_tail_measureReal
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {t : ℝ}
    (hXm : AEMeasurable X μ)
    (hXsg : IsSubGaussian X μ)
    (hnorm : subGaussianNorm X μ = 0)
    (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} = 0 := by
  let A : Set Ω := {ω | t ≤ |X ω|}
  have hle_bound :
      ∀ n : ℕ, μ.real A
        ≤ 2 * Real.exp (-(((n : ℝ) + 1) ^ 2)) := by
    intro n
    let K : ℝ := t / ((n : ℝ) + 1)
    have hnpos : 0 < (n : ℝ) + 1 := by positivity
    have hKpos : 0 < K := by
      dsimp [K]
      positivity
    have hKcond :
        subGaussianOrliczCondition X μ K :=
      subGaussianOrliczCondition_of_subGaussianNorm_eq_zero
        hXm hXsg hnorm hKpos
    have htail :
        μ.real {ω | t ≤ |X ω|}
          ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) :=
      subGaussianOrliczCondition_tail_le (μ := μ) (X := X)
        (K := K) (t := t) hKcond ht.le
    calc
      μ.real A = μ.real {ω | t ≤ |X ω|} := rfl
      _ ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) := htail
      _ = 2 * Real.exp (-(((n : ℝ) + 1) ^ 2)) := by
        congr 1
        dsimp [K]
        field_simp [ht.ne', hnpos.ne']
  have hsq :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2)
        Filter.atTop Filter.atTop := by
    exact (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hneg :
      Filter.Tendsto (fun n : ℕ => -(((n : ℝ) + 1) ^ 2))
        Filter.atTop Filter.atBot := by
    simpa using
      (Filter.Tendsto.const_mul_atTop_of_neg
        (by norm_num : (-1 : ℝ) < 0) hsq)
  have hlim :
      Filter.Tendsto
        (fun n : ℕ => 2 * Real.exp (-(((n : ℝ) + 1) ^ 2)))
        Filter.atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hneg).const_mul 2
  exact le_antisymm (ge_of_tendsto' hlim hle_bound) measureReal_nonneg

/-- Definiteness of Exercise 2.5.7: zero `ψ₂` gauge forces a sub-gaussian
random variable to be zero almost surely. -/
theorem ae_eq_zero_of_subGaussianNorm_eq_zero
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hXm : AEMeasurable X μ)
    (hXsg : IsSubGaussian X μ)
    (hnorm : subGaussianNorm X μ = 0) :
    X =ᵐ[μ] fun _ω => (0 : ℝ) := by
  rw [Filter.EventuallyEq, ae_iff]
  have htail_null :
      ∀ n : ℕ,
        μ {ω | (1 : ℝ) / ((n : ℝ) + 1) ≤ |X ω|} = 0 := by
    intro n
    have htpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    have htail_real :=
      subGaussianNorm_eq_zero_tail_measureReal
        (μ := μ) (X := X) (t := (1 : ℝ) / ((n : ℝ) + 1))
        hXm hXsg hnorm htpos
    exact (MeasureTheory.measureReal_eq_zero_iff (μ := μ)
      (s := {ω | (1 : ℝ) / ((n : ℝ) + 1) ≤ |X ω|})).mp htail_real
  refine measure_mono_null ?_ (measure_iUnion_null htail_null)
  intro ω hω
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  have hne : X ω ≠ 0 := by
    simpa using hω
  have habs_pos : 0 < |X ω| := abs_pos.mpr hne
  obtain ⟨n, hnpos, hnlt⟩ := Real.exists_nat_pos_inv_lt habs_pos
  refine ⟨n, ?_⟩
  have hn_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hle_inv : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hn_cast_pos (by linarith)
  have hnlt' : 1 / (n : ℝ) < |X ω| := by
    simpa [one_div] using hnlt
  exact hle_inv.trans hnlt'.le

/-- Almost-surely zero random variables satisfy every positive Orlicz scale. -/
theorem subGaussianOrliczCondition_of_ae_eq_zero
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℝ}
    (hK : 0 < K)
    (hX0 : X =ᵐ[μ] fun _ω => (0 : ℝ)) :
    subGaussianOrliczCondition X μ K := by
  have hExpEq :
      (fun ω => Real.exp (X ω ^ 2 / K ^ 2))
        =ᵐ[μ] fun _ω => (1 : ℝ) := by
    filter_upwards [hX0] with ω hω
    simp [hω]
  have hInt :
      Integrable (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) μ :=
    (integrable_const (1 : ℝ)).congr hExpEq.symm
  refine ⟨hK, hInt, ?_⟩
  calc
    ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ
        = ∫ _ω : Ω, (1 : ℝ) ∂μ :=
      integral_congr_ae hExpEq
    _ = 1 := by simp
    _ ≤ 2 := by norm_num

/-- The zero a.e. direction of Exercise 2.5.7. -/
theorem subGaussianNorm_eq_zero_of_ae_eq_zero
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX0 : X =ᵐ[μ] fun _ω => (0 : ℝ)) :
    subGaussianNorm X μ = 0 := by
  refine le_antisymm ?_ (subGaussianNorm_nonneg X μ)
  exact le_of_forall_gt_imp_ge_of_dense fun ε hε =>
    subGaussianNorm_le_of_subGaussianOrliczCondition
      (μ := μ) (X := X) (K := ε)
      (subGaussianOrliczCondition_of_ae_eq_zero (μ := μ) hε hX0)

/-- Exercise 2.5.7 definiteness, stated on the sub-gaussian domain. -/
theorem subGaussianNorm_eq_zero_iff_ae_eq_zero
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hXm : AEMeasurable X μ)
    (hXsg : IsSubGaussian X μ) :
    subGaussianNorm X μ = 0 ↔ X =ᵐ[μ] fun _ω => (0 : ℝ) :=
  ⟨ae_eq_zero_of_subGaussianNorm_eq_zero hXm hXsg,
    subGaussianNorm_eq_zero_of_ae_eq_zero⟩

/-- Zero-aware norm-to-Orlicz bridge for the `ψ₂` gauge.  If
`‖X‖_{ψ₂} ≤ K` with `K > 0`, then `2K` is an admissible Orlicz scale, even
when the norm is zero. -/
theorem subGaussianOrliczCondition_two_mul_of_norm_le
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hXsg : IsSubGaussian X μ)
    (hKpos : 0 < K)
    (hNormK : subGaussianNorm X μ ≤ K) :
    subGaussianOrliczCondition X μ (2 * K) := by
  by_cases hzero : subGaussianNorm X μ = 0
  · exact
      subGaussianOrliczCondition_of_subGaussianNorm_eq_zero
        (μ := μ) (X := X) hXm hXsg hzero (by positivity)
  · have hnorm_nonneg : 0 ≤ subGaussianNorm X μ :=
      subGaussianNorm_nonneg X μ
    have hnorm_pos : 0 < subGaussianNorm X μ :=
      lt_of_le_of_ne hnorm_nonneg (Ne.symm hzero)
    have htwo_norm :
        subGaussianOrliczCondition X μ (2 * subGaussianNorm X μ) :=
      subGaussianOrliczCondition_two_mul_norm hXm hXsg hnorm_pos
    have hle : 2 * subGaussianNorm X μ ≤ 2 * K :=
      mul_le_mul_of_nonneg_left hNormK (by norm_num)
    exact subGaussianOrliczCondition_mono_scale hXm htwo_norm hle

/-- Elementary estimate used in the proof of Proposition 2.5.2:
for `y ≥ 0`, `y ≤ exp(y²)`. -/
lemma nonneg_le_exp_sq {y : ℝ} (hy : 0 ≤ y) :
    y ≤ Real.exp (y ^ 2) := by
  have hone : 1 + y ^ 2 ≤ Real.exp (y ^ 2) :=
    one_add_le_exp (y ^ 2)
  by_cases hy1 : y ≤ 1
  · linarith [sq_nonneg y]
  · have h1y : 1 ≤ y := le_of_not_ge hy1
    have hysq : y ≤ y ^ 2 := by nlinarith
    linarith

/-- A scaled form of `y ≤ exp(y²)`: for `C > 0` and `r ≥ 1`,
`|x|^r` is dominated by a constant times a Gaussian exponential. -/
lemma abs_rpow_le_scaled_exp_sq {x C r : ℝ}
    (hC : 0 < C) (hr : 1 ≤ r) :
    |x| ^ r ≤ C ^ r * Real.exp (r * (|x| / C) ^ 2) := by
  let y : ℝ := |x| / C
  have hy_nonneg : 0 ≤ y := div_nonneg (abs_nonneg x) hC.le
  have hy_le : y ≤ Real.exp (y ^ 2) := nonneg_le_exp_sq hy_nonneg
  have hscaled : |x| ≤ C * Real.exp (y ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hy_le hC.le
    have hCy : C * y = |x| := by
      dsimp [y]
      field_simp [hC.ne']
    simpa [hCy] using hmul
  have hpow :=
    Real.rpow_le_rpow (abs_nonneg x) hscaled (by linarith : 0 ≤ r)
  calc
    |x| ^ r ≤ (C * Real.exp (y ^ 2)) ^ r := hpow
    _ = C ^ r * (Real.exp (y ^ 2)) ^ r :=
      Real.mul_rpow hC.le (Real.exp_pos _).le
    _ = C ^ r * Real.exp (r * y ^ 2) := by
      rw [← Real.exp_mul]
      ring_nf

/-- Elementary shifted-power integral used in the layer-cake proof of the
tail-to-Orlicz implication:
`∫₀^∞ (1 + t)^{-4} dt = 1/3`. -/
lemma integral_Ioi_one_add_rpow_neg_four :
    ∫ t in Set.Ioi (0 : ℝ), (1 + t) ^ (-4 : ℝ) = 1 / 3 := by
  have hderiv :
      ∀ x ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun t : ℝ => (t + 1) ^ (-3 : ℝ) / (-3 : ℝ))
          ((x + 1) ^ (-4 : ℝ)) x := by
    intro x hx
    convert (((hasDerivAt_id x).add_const (1 : ℝ)).rpow_const
      (p := (-3 : ℝ)) (Or.inl ?_)).div_const (-3 : ℝ) using 1
    · have hxpos : 0 < x + 1 := by
        linarith [Set.mem_Ici.mp hx]
      rw [show (-3 - 1 : ℝ) = -4 by norm_num]
      rw [Real.rpow_neg hxpos.le]
      norm_num [Real.rpow_natCast]
      rfl
    · change x + 1 ≠ 0
      linarith [Set.mem_Ici.mp hx]
  have hint :
      IntegrableOn (fun t : ℝ => (t + 1) ^ (-4 : ℝ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_add_rpow_Ioi_of_lt
      (a := (-4 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ))
      (by norm_num) (by norm_num)
  have htend :
      Tendsto (fun t : ℝ => (t + 1) ^ (-3 : ℝ) / (-3 : ℝ))
        atTop (𝓝 (0 / (-3 : ℝ))) := by
    have hpow :
        Tendsto (fun t : ℝ => (t + 1) ^ (-3 : ℝ)) atTop (𝓝 0) := by
      exact (tendsto_rpow_neg_atTop (by norm_num : 0 < (3 : ℝ))).comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
    exact hpow.div_const (-3 : ℝ)
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := (0 : ℝ)) (f := fun t : ℝ => (t + 1) ^ (-3 : ℝ) / (-3 : ℝ))
      (f' := fun t : ℝ => (t + 1) ^ (-4 : ℝ)) (m := 0 / (-3 : ℝ))
      hderiv hint htend
  simpa [add_comm] using h

/-- Nonnegative `lintegral` form of `integral_Ioi_one_add_rpow_neg_four`. -/
lemma lintegral_Ioi_ofReal_two_mul_one_add_rpow_neg_four :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * (1 + t) ^ (-4 : ℝ)) =
      ENNReal.ofReal (2 / 3 : ℝ) := by
  let f : ℝ → ℝ := fun t => 2 * (1 + t) ^ (-4 : ℝ)
  have hint_base :
      Integrable (fun t : ℝ => (1 + t) ^ (-4 : ℝ))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine (integrableOn_add_rpow_Ioi_of_lt
      (a := (-4 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ))
      (by norm_num) (by norm_num)).congr ?_
    exact Filter.Eventually.of_forall fun t => by
      ring_nf
  have hint : Integrable f (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hint_base.const_mul 2
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp ht]) _)
  have h_ofReal :=
    ofReal_integral_eq_lintegral_ofReal
      (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := f) hint hnonneg
  rw [← h_ofReal]
  congr 1
  calc
    ∫ t in Set.Ioi (0 : ℝ), f t
        = 2 * ∫ t in Set.Ioi (0 : ℝ), (1 + t) ^ (-4 : ℝ) := by
      dsimp [f]
      rw [integral_const_mul]
    _ = 2 / 3 := by
      rw [integral_Ioi_one_add_rpow_neg_four]
      norm_num

/-- HDP Proposition 2.5.2, direction `(i) ⇒ (iv)` with explicit absolute
constant: the two-sided tail bound at scale `K` implies the Orlicz condition
at scale `2K`. -/
theorem subGaussianOrliczCondition_of_subGaussianTailCondition
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subGaussianTailCondition X μ K) :
    subGaussianOrliczCondition X μ (2 * K) := by
  rcases hX with ⟨hKpos, htail⟩
  let Y : Ω → ℝ :=
    fun ω => Real.exp (X ω ^ 2 / (2 * K) ^ 2) - 1
  have hscale_pos : 0 < 2 * K := by positivity
  have hY_nonneg : 0 ≤ᵐ[μ] Y := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [Y]
      have hexp_ge_one :
          1 ≤ Real.exp (X ω ^ 2 / (2 * K) ^ 2) := by
        rw [← Real.exp_zero, Real.exp_le_exp]
        exact div_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
  have hY_aem : AEMeasurable Y μ := by
    fun_prop
  have hlayer :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt μ hY_nonneg hY_aem
  have htail_layer :
      (∫⁻ s in Set.Ioi (0 : ℝ), μ {ω | s < Y ω})
        ≤ ∫⁻ s in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (2 * (1 + s) ^ (-4 : ℝ)) := by
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with s hs
    have hspos : 0 < s := Set.mem_Ioi.mp hs
    have h1s_pos : 0 < 1 + s := by linarith
    have hlog_nonneg : 0 ≤ Real.log (1 + s) := by
      exact Real.log_nonneg (by linarith : 1 ≤ 1 + s)
    let t : ℝ := 2 * K * Real.sqrt (Real.log (1 + s))
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      positivity
    have hsubset : {ω | s < Y ω} ⊆ {ω | t ≤ |X ω|} := by
      intro ω hω
      dsimp [Y] at hω
      have hlt_exp :
          1 + s < Real.exp (X ω ^ 2 / (2 * K) ^ 2) := by
        linarith
      have hlog_lt :
          Real.log (1 + s) < X ω ^ 2 / (2 * K) ^ 2 := by
        rwa [Real.log_lt_iff_lt_exp h1s_pos]
      have habs_div_nonneg : 0 ≤ |X ω| / (2 * K) :=
        div_nonneg (abs_nonneg _) hscale_pos.le
      have hsqrt_lt : Real.sqrt (Real.log (1 + s)) < |X ω| / (2 * K) := by
        rw [Real.sqrt_lt hlog_nonneg habs_div_nonneg]
        convert hlog_lt using 1
        rw [div_pow, sq_abs]
      have hmul := mul_lt_mul_of_pos_left hsqrt_lt hscale_pos
      have ht_lt_abs : t < |X ω| := by
        dsimp [t] at hmul ⊢
        rwa [mul_div_cancel₀ _ hscale_pos.ne'] at hmul
      exact ht_lt_abs.le
    have htail_real :
        μ.real {ω | s < Y ω} ≤ 2 * (1 + s) ^ (-4 : ℝ) := by
      have htail_t := htail t ht_nonneg
      have hmono : μ.real {ω | s < Y ω} ≤ μ.real {ω | t ≤ |X ω|} :=
        measureReal_mono hsubset
      have htail_simplified :
          2 * Real.exp (-(t ^ 2) / K ^ 2) =
            2 * (1 + s) ^ (-4 : ℝ) := by
        congr 1
        dsimp [t]
        have hsqrt_sq : Real.sqrt (Real.log (1 + s)) ^ 2 = Real.log (1 + s) :=
          Real.sq_sqrt hlog_nonneg
        rw [mul_pow, mul_pow, hsqrt_sq]
        field_simp [hKpos.ne']
        rw [Real.rpow_def_of_pos h1s_pos]
        apply Real.exp_injective
        ring_nf
      exact hmono.trans (by simpa [htail_simplified] using htail_t)
    have hbound_nonneg : 0 ≤ 2 * (1 + s) ^ (-4 : ℝ) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg h1s_pos.le _)
    exact
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hbound_nonneg).mpr
        (by simpa [measureReal_def] using htail_real)
  have hlin_Y :
      (∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ) ≤ ENNReal.ofReal (2 / 3 : ℝ) := by
    calc
      ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ
          = ∫⁻ s in Set.Ioi (0 : ℝ), μ {ω | s < Y ω} := hlayer
      _ ≤ ∫⁻ s in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (2 * (1 + s) ^ (-4 : ℝ)) := htail_layer
      _ = ENNReal.ofReal (2 / 3 : ℝ) :=
        lintegral_Ioi_ofReal_two_mul_one_add_rpow_neg_four
  have hY_int : Integrable Y μ := by
    refine ⟨hY_aem.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal hY_nonneg).mpr
      (hlin_Y.trans_lt ENNReal.ofReal_lt_top)
  have hY_integral_le : ∫ ω, Y ω ∂μ ≤ 2 / 3 := by
    have h_ofReal :=
      ofReal_integral_eq_lintegral_ofReal (μ := μ) (f := Y) hY_int hY_nonneg
    have hle :
        ENNReal.ofReal (∫ ω, Y ω ∂μ) ≤ ENNReal.ofReal (2 / 3 : ℝ) := by
      rwa [h_ofReal]
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2 / 3)).mp hle
  have hExp_int : Integrable (fun ω => Real.exp (X ω ^ 2 / (2 * K) ^ 2)) μ := by
    have hsum : Integrable (fun ω => Y ω + 1) μ :=
      hY_int.add (integrable_const (1 : ℝ))
    convert hsum using 1
    funext ω
    dsimp [Y]
    ring_nf
  refine ⟨by positivity, hExp_int, ?_⟩
  calc
    ∫ ω, Real.exp (X ω ^ 2 / (2 * K) ^ 2) ∂μ
        = ∫ ω, (Y ω + 1) ∂μ := by
      congr with ω
      dsimp [Y]
      ring_nf
    _ = ∫ ω, Y ω ∂μ + ∫ _ω : Ω, (1 : ℝ) ∂μ := by
      rw [integral_add hY_int (integrable_const (1 : ℝ))]
    _ = ∫ ω, Y ω ∂μ + 1 := by
      simp
    _ ≤ 2 := by
      linarith

/-- The scalar inequality `eˣ ≤ x + eˣ²` used in the book's proof of
Proposition 2.5.2, direction `(iii) ⇒ (v)`. -/
lemma exp_le_self_add_exp_sq (x : ℝ) :
    Real.exp x ≤ x + Real.exp (x ^ 2) := by
  by_cases hxabs : |x| ≤ 1
  · have hlocal := exp_sub_one_le_self_add_sq_of_abs_le_one hxabs
    have hone : 1 + x ^ 2 ≤ Real.exp (x ^ 2) :=
      one_add_le_exp (x ^ 2)
    linarith
  · have hxabs_gt : 1 < |x| := lt_of_not_ge hxabs
    by_cases hx_nonneg : 0 ≤ x
    · have hx_ge_one : 1 ≤ x := by
        rw [abs_of_nonneg hx_nonneg] at hxabs_gt
        exact hxabs_gt.le
      have hx_le_sq : x ≤ x ^ 2 := by nlinarith
      calc
        Real.exp x ≤ Real.exp (x ^ 2) := Real.exp_le_exp.mpr hx_le_sq
        _ ≤ x + Real.exp (x ^ 2) := by linarith
    · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
      have hx_le_neg_one : x ≤ -1 := by
        rw [abs_of_neg hx_neg] at hxabs_gt
        linarith
      have hexp_le_one : Real.exp x ≤ 1 :=
        Real.exp_le_one_iff.mpr hx_neg.le
      have hone : 1 + x ^ 2 ≤ Real.exp (x ^ 2) :=
        one_add_le_exp (x ^ 2)
      have hquad : 1 ≤ x + Real.exp (x ^ 2) := by
        nlinarith
      exact hexp_le_one.trans hquad

/-- Exponential-square integrability implies ordinary integrability. This is
the measurability bridge needed because Lean represents a random variable as a
plain function plus an explicit measurability hypothesis. -/
theorem integrable_of_integrable_exp_sq_div
    {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (hXm : AEMeasurable X μ) (hK : 0 < K)
    (hInt : Integrable (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) μ) :
    Integrable X μ := by
  have hdom : Integrable (fun ω => K * Real.exp (X ω ^ 2 / K ^ 2)) μ :=
    hInt.const_mul K
  refine hdom.mono hXm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    let y : ℝ := |X ω| / K
    have hy_nonneg : 0 ≤ y := div_nonneg (abs_nonneg _) hK.le
    have hy_le : y ≤ Real.exp (y ^ 2) := nonneg_le_exp_sq hy_nonneg
    have hscaled : |X ω| ≤ K * Real.exp (y ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left hy_le hK.le
      have hxy : K * y = |X ω| := by
        dsimp [y]
        field_simp [hK.ne']
      simpa [hxy] using hmul
    have hy_sq : y ^ 2 = X ω ^ 2 / K ^ 2 := by
      dsimp [y]
      field_simp [hK.ne']
      rw [sq_abs]
    calc
      ‖X ω‖ = |X ω| := Real.norm_eq_abs _
      _ ≤ K * Real.exp (y ^ 2) := hscaled
      _ = ‖K * Real.exp (X ω ^ 2 / K ^ 2)‖ := by
        rw [hy_sq, Real.norm_eq_abs, abs_mul, abs_of_pos hK,
          abs_of_nonneg (Real.exp_pos _).le]

/-- HDP Proposition 2.5.2, direction `(iv) ⇒ (ii)` with explicit absolute
constant: the Orlicz condition at scale `K` implies
`‖X‖_{L^p} ≤ 2 K √p` for all `p ≥ 1`. -/
theorem subGaussianMomentCondition_of_subGaussianOrliczCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hXm : AEStronglyMeasurable X μ)
    (hX : subGaussianOrliczCondition X μ K) :
    subGaussianMomentCondition X μ (2 * K) := by
  rcases hX with ⟨hKpos, hExpInt, hExp_le⟩
  refine ⟨by positivity, fun p hp => ?_⟩
  let r : ℝ := p
  have hr_ge_one : 1 ≤ r := by
    simpa [r] using hp
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr_ge_one
  let C : ℝ := K * Real.sqrt r
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCnonneg : 0 ≤ C := hCpos.le
  have hCpow_nonneg : 0 ≤ C ^ r :=
    Real.rpow_nonneg hCnonneg r
  have hdom_int :
      Integrable (fun ω => C ^ r * Real.exp (X ω ^ 2 / K ^ 2)) μ :=
    hExpInt.const_mul (C ^ r)
  have hpoint :
      ∀ ω, ‖X ω‖ ^ r ≤ C ^ r * Real.exp (X ω ^ 2 / K ^ 2) := by
    intro ω
    have hscaled :=
      abs_rpow_le_scaled_exp_sq (x := X ω) (C := C) (r := r)
        hCpos hr_ge_one
    have hquad_eq :
        r * (|X ω| / C) ^ 2 = X ω ^ 2 / K ^ 2 := by
      rw [div_pow, sq_abs]
      dsimp [C]
      rw [mul_pow, Real.sq_sqrt hr_pos.le]
      field_simp [hKpos.ne', hr_pos.ne']
    calc
      ‖X ω‖ ^ r = |X ω| ^ r := by rw [Real.norm_eq_abs]
      _ ≤ C ^ r * Real.exp (r * (|X ω| / C) ^ 2) := hscaled
      _ = C ^ r * Real.exp (X ω ^ 2 / K ^ 2) := by
        rw [hquad_eq]
  have hpow_int :
      Integrable (fun ω => ‖X ω‖ ^ r) μ := by
    refine hdom_int.mono ?_ ?_
    · exact (hXm.norm.aemeasurable.pow_const r).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        have htarget_nonneg : 0 ≤ ‖X ω‖ ^ r :=
          Real.rpow_nonneg (norm_nonneg _) r
        have hdom_nonneg : 0 ≤ C ^ r * Real.exp (X ω ^ 2 / K ^ 2) :=
          mul_nonneg hCpow_nonneg (Real.exp_pos _).le
        calc
          ‖‖X ω‖ ^ r‖ = ‖X ω‖ ^ r := by
            rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
          _ ≤ C ^ r * Real.exp (X ω ^ 2 / K ^ 2) := hpoint ω
          _ = ‖C ^ r * Real.exp (X ω ^ 2 / K ^ 2)‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hdom_nonneg]
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    have hr0 : r = 0 := by
      simp [r, hp0]
    exact hr_pos.ne' hr0
  have hmem : MemLp X (p : ℝ≥0∞) μ := by
    rw [← integrable_norm_rpow_iff
      (μ := μ) (f := X) hXm
      (by exact_mod_cast hp_ne_zero)
      (by exact ENNReal.coe_ne_top)]
    simpa [r] using hpow_int
  have hintegral_bound :
      ∫ ω, ‖X ω‖ ^ r ∂μ ≤ C ^ r * 2 := by
    calc
      ∫ ω, ‖X ω‖ ^ r ∂μ
          ≤ ∫ ω, C ^ r * Real.exp (X ω ^ 2 / K ^ 2) ∂μ :=
        integral_mono hpow_int hdom_int hpoint
      _ = C ^ r * ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ := by
        rw [integral_const_mul]
      _ ≤ C ^ r * 2 :=
        mul_le_mul_of_nonneg_left hExp_le hCpow_nonneg
  have htwo_le_two_rpow : (2 : ℝ) ≤ 2 ^ r :=
    by simpa [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hr_ge_one
  have hintegral_bound_C :
      ∫ ω, ‖X ω‖ ^ r ∂μ ≤ (2 * K * Real.sqrt r) ^ r := by
    have hCpow_mul_two_le : C ^ r * 2 ≤ (2 * K * Real.sqrt r) ^ r := by
      dsimp [C]
      calc
        (K * Real.sqrt r) ^ r * 2
            ≤ (K * Real.sqrt r) ^ r * 2 ^ r :=
          mul_le_mul_of_nonneg_left htwo_le_two_rpow
            (Real.rpow_nonneg hCnonneg r)
        _ = (2 * (K * Real.sqrt r)) ^ r := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hCnonneg]
          ring
        _ = (2 * K * Real.sqrt r) ^ r := by
          ring_nf
    exact hintegral_bound.trans hCpow_mul_two_le
  have hlp_real :
      MeasureTheory.lpNorm X (p : ℝ≥0∞) μ ≤ 2 * K * Real.sqrt r := by
    rw [lpNorm_nnreal_eq_integral_norm_rpow
      (μ := μ) (f := X) (p := p)
      hp_ne_zero hXm]
    have hintegral_nonneg : 0 ≤ ∫ ω, ‖X ω‖ ^ r ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) r
    calc
      (∫ ω, ‖X ω‖ ^ r ∂μ) ^ ((p : ℝ≥0)⁻¹ : ℝ)
          ≤ ((2 * K * Real.sqrt r) ^ r) ^ ((p : ℝ≥0)⁻¹ : ℝ) := by
        exact Real.rpow_le_rpow hintegral_nonneg hintegral_bound_C
          (by positivity)
      _ = 2 * K * Real.sqrt r := by
        have hbase_pos : 0 < 2 * K * Real.sqrt r := by
          positivity
        rw [← Real.rpow_mul hbase_pos.le]
        have hinv_eq : (((p : ℝ≥0)⁻¹ : ℝ)) = r⁻¹ := by
          simp [r]
        rw [hinv_eq]
        have hmul : r * r⁻¹ = 1 := by
          field_simp [hr_pos.ne']
        rw [hmul, Real.rpow_one]
  refine ⟨hmem, ?_⟩
  rw [← ofReal_lpNorm hmem]
  exact ENNReal.ofReal_le_ofReal (by simpa [r, mul_assoc] using hlp_real)

/-- HDP Proposition 2.5.2, composite direction `(i) ⇒ (ii)`: the book tail
condition implies the moment growth condition, with an explicit absolute
constant. -/
theorem subGaussianMomentCondition_of_subGaussianTailCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hXm : AEStronglyMeasurable X μ)
    (hX : subGaussianTailCondition X μ K) :
    subGaussianMomentCondition X μ (4 * K) := by
  have hOrl :
      subGaussianOrliczCondition X μ (2 * K) :=
    subGaussianOrliczCondition_of_subGaussianTailCondition
      (μ := μ) (X := X) (K := K) hXm.aemeasurable hX
  have hMom :
      subGaussianMomentCondition X μ (2 * (2 * K)) :=
    subGaussianMomentCondition_of_subGaussianOrliczCondition
      (μ := μ) (X := X) (K := 2 * K) hXm hOrl
  have hscale : 2 * (2 * K) = 4 * K := by ring
  simpa [hscale] using hMom

/-- A small numerical estimate used in the moment-to-tail direction of HDP
Proposition 2.5.2. -/
lemma one_le_two_mul_exp_neg_of_le_one_fourth {u : ℝ}
    (hu : u ≤ 1 / 4) :
    1 ≤ 2 * Real.exp (-u) := by
  have hlinear : 1 - u ≤ Real.exp (-u) := by
    have h := Real.add_one_le_exp (-u)
    linarith
  have hthree : (3 / 4 : ℝ) ≤ Real.exp (-u) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hthree (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

/-- The elementary bound `1 / 4 ≤ log 2`, proved from `1 + x ≤ exp x`.
It keeps the moment-to-tail proof independent of decimal approximations. -/
lemma one_fourth_le_log_two : (1 / 4 : ℝ) ≤ Real.log 2 := by
  have hhalf_exp : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
    norm_num at h ⊢
    exact h
  have hprod :
      Real.exp (1 / 2 : ℝ) * (1 / 2 : ℝ) ≤ 1 := by
    calc
      Real.exp (1 / 2 : ℝ) * (1 / 2 : ℝ)
          ≤ Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hhalf_exp
          (Real.exp_pos (1 / 2 : ℝ)).le
      _ = 1 := by
        rw [← Real.exp_add]
        norm_num
  have hexp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hlog_half : (1 / 2 : ℝ) ≤ Real.log 2 :=
    (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).2
      hexp_half_le_two
  nlinarith

/-- The optimized base estimate behind the moment-to-tail implication:
`(1/2)^p` is dominated by the target Gaussian exponential up to the leading
factor `2`. -/
lemma one_half_rpow_le_two_mul_exp_neg_quarter {p : ℝ}
    (hp : 0 ≤ p) :
    (1 / 2 : ℝ) ^ p ≤ 2 * Real.exp (-p / 4) := by
  have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.log_inv]
  have hlog_bound : Real.log (1 / 2 : ℝ) * p ≤ -p / 4 := by
    rw [hlog_half]
    nlinarith [one_fourth_le_log_two, hp]
  calc
    (1 / 2 : ℝ) ^ p
        = Real.exp (Real.log (1 / 2 : ℝ) * p) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ Real.exp (-p / 4) :=
      Real.exp_le_exp.mpr hlog_bound
    _ ≤ 2 * Real.exp (-p / 4) := by
      exact le_mul_of_one_le_left (Real.exp_pos _).le
        (by norm_num : (1 : ℝ) ≤ 2)

/-- A Markov-`L^p` tail bound extracted from HDP Proposition 2.5.2(ii). -/
theorem subGaussianMomentCondition_tail_rpow_bound
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K t : ℝ} {p : ℝ≥0}
    (hX : subGaussianMomentCondition X μ K)
    (hp : 1 ≤ (p : ℝ)) (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} ≤
      (K * Real.sqrt (p : ℝ) / t) ^ (p : ℝ) := by
  rcases hX with ⟨hKpos, hMom⟩
  let r : ℝ := p
  have hr_ge_one : 1 ≤ r := by simpa [r] using hp
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr_ge_one
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    have : r = 0 := by simp [r, hp0]
    linarith
  have hp_ne_zero_enn : (p : ℝ≥0∞) ≠ 0 := by
    simp [hp_ne_zero]
  have hp_ne_top_enn : (p : ℝ≥0∞) ≠ ∞ := by
    simp
  rcases hMom p hp with ⟨hmem, hnorm⟩
  have hYint_p : Integrable (fun ω => ‖X ω‖ ^ (p : ℝ)) μ := by
    change Integrable
      (fun ω => ‖X ω‖ ^ (p : ℝ≥0∞).toReal) μ
    rw [integrable_norm_rpow_iff
      (μ := μ) (f := X) hmem.aestronglyMeasurable
      hp_ne_zero_enn hp_ne_top_enn]
    exact hmem
  have hYint : Integrable (fun ω => ‖X ω‖ ^ r) μ := by
    simpa [r] using hYint_p
  have hYnonneg : 0 ≤ᵐ[μ] fun ω => ‖X ω‖ ^ r :=
    Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (norm_nonneg _) r
  have ht_rpow_pos : 0 < t ^ r :=
    Real.rpow_pos_of_pos ht r
  have hmarkov :=
    markov_inequality (μ := μ)
      (X := fun ω => ‖X ω‖ ^ r) hYnonneg hYint ht_rpow_pos
  have hevent :
      {ω | t ^ r ≤ ‖X ω‖ ^ r} = {ω | t ≤ |X ω|} := by
    ext ω
    change t ^ r ≤ ‖X ω‖ ^ r ↔ t ≤ |X ω|
    rw [Real.rpow_le_rpow_iff ht.le (norm_nonneg _) hr_pos,
      Real.norm_eq_abs]
  have htail :
      μ.real {ω | t ≤ |X ω|} ≤
        (∫ ω, ‖X ω‖ ^ r ∂μ) / t ^ r := by
    have hmarkov' :
        μ.real {ω | t ^ r ≤ ‖X ω‖ ^ r} ≤
          (∫ ω, ‖X ω‖ ^ r ∂μ) / t ^ r := by
      simpa using hmarkov
    rw [hevent] at hmarkov'
    exact hmarkov'
  let B : ℝ := K * Real.sqrt r
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hlp_real :
      MeasureTheory.lpNorm X (p : ℝ≥0∞) μ ≤ B := by
    have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    simpa [B, r, MeasureTheory.toReal_eLpNorm hmem.aestronglyMeasurable,
      ENNReal.toReal_ofReal hB_nonneg] using hto
  let I : ℝ := ∫ ω, ‖X ω‖ ^ r ∂μ
  have hI_nonneg : 0 ≤ I := by
    have hI_abs : 0 ≤ ∫ ω, |X ω| ^ r ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r
    simpa [I, Real.norm_eq_abs] using hI_abs
  have hroot_bound :
      I ^ (((p : ℝ≥0)⁻¹ : ℝ)) ≤ B := by
    have hlp_eq :
        MeasureTheory.lpNorm X (p : ℝ≥0∞) μ =
          I ^ (((p : ℝ≥0)⁻¹ : ℝ)) := by
      dsimp [I, r]
      rw [lpNorm_nnreal_eq_integral_norm_rpow
        (μ := μ) (f := X) (p := p)
        hp_ne_zero hmem.aestronglyMeasurable]
      simp [Real.norm_eq_abs]
    simpa [hlp_eq] using hlp_real
  have hI_bound : I ≤ B ^ r := by
    have hinv_eq : (((p : ℝ≥0)⁻¹ : ℝ)) = r⁻¹ := by
      simp [r]
    have hpow :=
      Real.rpow_le_rpow
        (Real.rpow_nonneg hI_nonneg (((p : ℝ≥0)⁻¹ : ℝ)))
        hroot_bound hr_pos.le
    rw [hinv_eq] at hpow
    have hleft : (I ^ r⁻¹) ^ r = I := by
      exact Real.rpow_inv_rpow hI_nonneg hr_pos.ne'
    simpa [hleft] using hpow
  calc
    μ.real {ω | t ≤ |X ω|} ≤ I / t ^ r := htail
    _ ≤ B ^ r / t ^ r :=
      div_le_div_of_nonneg_right hI_bound ht_rpow_pos.le
    _ = (B / t) ^ r := by
      rw [Real.div_rpow hB_nonneg ht.le]
    _ = (K * Real.sqrt (p : ℝ) / t) ^ (p : ℝ) := by
      simp [B, r]

/-- HDP Proposition 2.5.2, direction `(ii) ⇒ (i)` with explicit absolute
constant: moment growth at scale `K` implies the two-sided Gaussian tail
condition at scale `4K`. -/
theorem subGaussianTailCondition_of_subGaussianMomentCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hX : subGaussianMomentCondition X μ K) :
    subGaussianTailCondition X μ (4 * K) := by
  rcases hX with ⟨hKpos, hMom⟩
  refine ⟨by positivity, fun t ht => ?_⟩
  by_cases ht_small : t < 2 * K
  · have hprob : μ.real {ω | t ≤ |X ω|} ≤ 1 :=
      measureReal_le_one
    have hu : t ^ 2 / (4 * K) ^ 2 ≤ 1 / 4 := by
      have ht_le : t ≤ 2 * K := le_of_lt ht_small
      have ht_sq_le : t ^ 2 ≤ (2 * K) ^ 2 := by
        have htwoK_nonneg : 0 ≤ 2 * K := by positivity
        have habs : |t| ≤ |2 * K| := by
          simpa [abs_of_nonneg ht, abs_of_nonneg htwoK_nonneg] using ht_le
        exact sq_le_sq.mpr habs
      have hden_pos : 0 < (4 * K) ^ 2 := by positivity
      rw [div_le_iff₀ hden_pos]
      nlinarith
    have hsmall :
        1 ≤ 2 * Real.exp (-(t ^ 2 / (4 * K) ^ 2)) :=
      one_le_two_mul_exp_neg_of_le_one_fourth hu
    have hsmall' :
        1 ≤ 2 * Real.exp (-t ^ 2 / (4 * K) ^ 2) := by
      convert hsmall using 2
      ring_nf
    exact hprob.trans hsmall'
  · have ht_big : 2 * K ≤ t := le_of_not_gt ht_small
    have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) ht_big
    let pReal : ℝ := t ^ 2 / (4 * K ^ 2)
    have hpReal_nonneg : 0 ≤ pReal := by
      dsimp [pReal]
      positivity
    let p : ℝ≥0 := ⟨pReal, hpReal_nonneg⟩
    have hp_coe : (p : ℝ) = pReal := rfl
    have hp_ge_one : 1 ≤ (p : ℝ) := by
      rw [hp_coe]
      dsimp [pReal]
      have hden_pos : 0 < 4 * K ^ 2 := by positivity
      rw [le_div_iff₀ hden_pos]
      nlinarith
    have htail :=
      subGaussianMomentCondition_tail_rpow_bound
        (μ := μ) (X := X) (K := K) (t := t) (p := p)
        ⟨hKpos, hMom⟩ hp_ge_one ht_pos
    have hsqrt_p : Real.sqrt (p : ℝ) = t / (2 * K) := by
      rw [hp_coe]
      dsimp [pReal]
      have harg_nonneg : 0 ≤ t ^ 2 / (4 * K ^ 2) := by positivity
      have hrhs_nonneg : 0 ≤ t / (2 * K) := by positivity
      rw [Real.sqrt_eq_iff_eq_sq harg_nonneg hrhs_nonneg]
      field_simp [hKpos.ne']
      ring_nf
    have hbase :
        K * Real.sqrt (p : ℝ) / t = 1 / 2 := by
      rw [hsqrt_p]
      field_simp [hKpos.ne', ht_pos.ne']
    have htail_half :
        μ.real {ω | t ≤ |X ω|} ≤ (1 / 2 : ℝ) ^ (p : ℝ) := by
      simpa [hbase] using htail
    have hexp :
        (1 / 2 : ℝ) ^ (p : ℝ) ≤
          2 * Real.exp (-(p : ℝ) / 4) :=
      one_half_rpow_le_two_mul_exp_neg_quarter
        (by exact_mod_cast hpReal_nonneg)
    calc
      μ.real {ω | t ≤ |X ω|} ≤ (1 / 2 : ℝ) ^ (p : ℝ) := htail_half
      _ ≤ 2 * Real.exp (-(p : ℝ) / 4) := hexp
      _ = 2 * Real.exp (-(t ^ 2) / (4 * K) ^ 2) := by
        congr 1
        rw [hp_coe]
        dsimp [pReal]
        field_simp [hKpos.ne']

/-- HDP Proposition 2.5.2, composite direction `(ii) ⇒ (iv)`: moment growth
implies the Orlicz square-exponential condition, with an explicit absolute
constant. -/
theorem subGaussianOrliczCondition_of_subGaussianMomentCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hX : subGaussianMomentCondition X μ K) :
    subGaussianOrliczCondition X μ (8 * K) := by
  rcases hX with ⟨hKpos, hMom⟩
  have hTail :
      subGaussianTailCondition X μ (4 * K) :=
    subGaussianTailCondition_of_subGaussianMomentCondition
      (μ := μ) (X := X) (K := K) ⟨hKpos, hMom⟩
  have hmem1 : MemLp X (1 : ℝ≥0∞) μ :=
    (hMom 1 (by norm_num)).1
  have hOrl :
      subGaussianOrliczCondition X μ (2 * (4 * K)) :=
    subGaussianOrliczCondition_of_subGaussianTailCondition
      (μ := μ) (X := X) (K := 4 * K)
      hmem1.aestronglyMeasurable.aemeasurable hTail
  have hscale : 2 * (4 * K) = 8 * K := by ring
  simpa [hscale] using hOrl

/-- HDP Proposition 2.5.2, direction `(iv) ⇒ (iii)`: the Orlicz
condition implies the local square-MGF estimate with the same scale in the
book's convention. The key step is Jensen's inequality for the concave map
`y ↦ y ^ (θ²K²)` on `[0, ∞)`. -/
theorem subGaussianSquareMGFCondition_of_subGaussianOrliczCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hX : subGaussianOrliczCondition X μ K) :
    subGaussianSquareMGFCondition X μ K := by
  rcases hX with ⟨hKpos, hInt, hExp_le⟩
  refine ⟨hKpos, fun θ hθ => ?_⟩
  let Y : Ω → ℝ := fun ω => Real.exp (X ω ^ 2 / K ^ 2)
  let α : ℝ := θ ^ 2 * K ^ 2
  have hθ_abs : |θ| ≤ |1 / K| := by
    simpa [one_div, abs_inv, abs_of_pos hKpos] using hθ
  have hθsq_le : θ ^ 2 ≤ 1 / K ^ 2 := by
    have hs := sq_le_sq.mpr hθ_abs
    simpa [one_div, inv_pow] using hs
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact mul_nonneg (sq_nonneg θ) (sq_nonneg K)
  have hα_le_one : α ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hθsq_le (sq_nonneg K)
    dsimp [α]
    convert hmul using 1
    field_simp [hKpos.ne']
  have hY_nonneg : ∀ ω, 0 ≤ Y ω :=
    fun ω => (Real.exp_pos _).le
  have hY_ge_one : ∀ ω, 1 ≤ Y ω := by
    intro ω
    dsimp [Y]
    rw [← Real.exp_zero, Real.exp_le_exp]
    exact div_nonneg (sq_nonneg _) (sq_nonneg K)
  have hcont_rpow : Continuous fun y : ℝ => y ^ α :=
    Real.continuous_rpow_const hα_nonneg
  have hYpow_aesm : AEStronglyMeasurable (fun ω => Y ω ^ α) μ :=
    (hcont_rpow.measurable.comp_aemeasurable hInt.aemeasurable).aestronglyMeasurable
  have hYpow_int : Integrable (fun ω => Y ω ^ α) μ := by
    refine hInt.mono hYpow_aesm ?_
    exact Filter.Eventually.of_forall fun ω => by
      have hle : Y ω ^ α ≤ Y ω :=
        Real.rpow_le_self_of_one_le (hY_ge_one ω) hα_le_one
      have hpow_nonneg : 0 ≤ Y ω ^ α :=
        Real.rpow_nonneg (hY_nonneg ω) α
      simpa [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg,
        abs_of_nonneg (hY_nonneg ω)] using hle
  have hpow_eq :
      (fun ω => Y ω ^ α) =
        fun ω => Real.exp (θ ^ 2 * X ω ^ 2) := by
    funext ω
    dsimp [Y, α]
    rw [← Real.exp_mul]
    congr 1
    field_simp [hKpos.ne']
  have htarget_int :
      Integrable (fun ω => Real.exp (θ ^ 2 * X ω ^ 2)) μ := by
    rw [← hpow_eq]
    exact hYpow_int
  have hY_mem : ∀ᵐ ω ∂μ, Y ω ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun ω => hY_nonneg ω
  have hY_int_nonneg : 0 ≤ ∫ ω, Y ω ∂μ :=
    integral_nonneg hY_nonneg
  have hYpow_le :
      ∫ ω, Y ω ^ α ∂μ ≤ (∫ ω, Y ω ∂μ) ^ α := by
    exact
      (Real.concaveOn_rpow hα_nonneg hα_le_one).le_map_integral
        hcont_rpow.continuousOn isClosed_Ici hY_mem hInt hYpow_int
  refine ⟨htarget_int, ?_⟩
  calc
    ∫ ω, Real.exp (θ ^ 2 * X ω ^ 2) ∂μ
        = ∫ ω, Y ω ^ α ∂μ := by rw [← hpow_eq]
    _ ≤ (∫ ω, Y ω ∂μ) ^ α := hYpow_le
    _ ≤ (2 : ℝ) ^ α :=
      Real.rpow_le_rpow hY_int_nonneg hExp_le hα_nonneg
    _ = Real.exp (Real.log 2 * α) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp α := by
      rw [Real.exp_le_exp]
      have hlog2_le_one : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
      nlinarith
    _ = Real.exp (K ^ 2 * θ ^ 2) := by
      congr 1
      dsimp [α]
      ring

/-- HDP Proposition 2.5.2, composite direction `(i) ⇒ (iii)`: the book tail
condition implies the local square-MGF condition, with an explicit absolute
constant. -/
theorem subGaussianSquareMGFCondition_of_subGaussianTailCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subGaussianTailCondition X μ K) :
    subGaussianSquareMGFCondition X μ (2 * K) :=
  subGaussianSquareMGFCondition_of_subGaussianOrliczCondition
    (μ := μ) (X := X) (K := 2 * K)
    (subGaussianOrliczCondition_of_subGaussianTailCondition
      (μ := μ) (X := X) (K := K) hXm hX)

/-- HDP Proposition 2.5.2, composite direction `(ii) ⇒ (iii)`: moment
growth implies the local square-MGF condition, with an explicit absolute
constant. -/
theorem subGaussianSquareMGFCondition_of_subGaussianMomentCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hX : subGaussianMomentCondition X μ K) :
    subGaussianSquareMGFCondition X μ (8 * K) :=
  subGaussianSquareMGFCondition_of_subGaussianOrliczCondition
    (μ := μ) (X := X) (K := 8 * K)
    (subGaussianOrliczCondition_of_subGaussianMomentCondition
      (μ := μ) (X := X) (K := K) hX)

/-- HDP Proposition 2.5.2, centered direction `(iii) ⇒ (v)`: if `X` is
mean zero and has the local square-MGF bound, then it has the global MGF
bound in the book's convention. -/
theorem subGaussianMGFCondition_of_squareMGFCondition_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subGaussianSquareMGFCondition X μ K)
    (hmean : ∫ ω, X ω ∂μ = 0) :
    subGaussianMGFCondition X μ K := by
  rcases hX with ⟨hKpos, hsq⟩
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hKpos
  have hKsq_nonneg : 0 ≤ K ^ 2 := hKsq_pos.le
  have hone_over_abs : |1 / K| ≤ 1 / K := by
    rw [abs_of_pos (one_div_pos.mpr hKpos)]
  have hExpSq_at_one := hsq (1 / K) hone_over_abs
  have hExpSq_at_one_fun :
      Integrable (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) μ := by
    convert hExpSq_at_one.1 using 1
    funext ω
    congr 1
    field_simp [hKpos.ne']
  have hXint : Integrable X μ :=
    integrable_of_integrable_exp_sq_div hXm hKpos hExpSq_at_one_fun
  refine ⟨hKpos, fun θ => ?_⟩
  by_cases hsmall : |θ| ≤ 1 / K
  · have hsquare := hsq θ hsmall
    have hlin_int : Integrable (fun ω => θ * X ω) μ := hXint.const_mul θ
    have hdom_int :
        Integrable (fun ω => θ * X ω + Real.exp (θ ^ 2 * X ω ^ 2)) μ :=
      hlin_int.add hsquare.1
    have htarget_aesm :
        AEStronglyMeasurable (fun ω => Real.exp (θ * X ω)) μ := by
      exact
        (Measurable.comp_aemeasurable Real.measurable_exp
          (hXm.const_mul θ)).aestronglyMeasurable
    have hpoint :
        ∀ ω, Real.exp (θ * X ω)
          ≤ θ * X ω + Real.exp (θ ^ 2 * X ω ^ 2) := by
      intro ω
      simpa [mul_pow] using exp_le_self_add_exp_sq (θ * X ω)
    have hdom_nonneg :
        ∀ ω, 0 ≤ θ * X ω + Real.exp (θ ^ 2 * X ω ^ 2) :=
      fun ω => (Real.exp_pos _).le.trans (hpoint ω)
    have htarget_int : Integrable (fun ω => Real.exp (θ * X ω)) μ := by
      refine hdom_int.mono htarget_aesm ?_
      exact Filter.Eventually.of_forall fun ω => by
        have htarget_nonneg : 0 ≤ Real.exp (θ * X ω) := (Real.exp_pos _).le
        simpa [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg,
          abs_of_nonneg (hdom_nonneg ω)] using hpoint ω
    refine ⟨htarget_int, ?_⟩
    calc
      mgf X μ θ = ∫ ω, Real.exp (θ * X ω) ∂μ := rfl
      _ ≤ ∫ ω, θ * X ω + Real.exp (θ ^ 2 * X ω ^ 2) ∂μ :=
        integral_mono htarget_int hdom_int hpoint
      _ = θ * (∫ ω, X ω ∂μ) + ∫ ω, Real.exp (θ ^ 2 * X ω ^ 2) ∂μ := by
        rw [integral_add hlin_int hsquare.1, integral_const_mul]
      _ = ∫ ω, Real.exp (θ ^ 2 * X ω ^ 2) ∂μ := by
        rw [hmean, mul_zero, zero_add]
      _ ≤ Real.exp (K ^ 2 * θ ^ 2) := hsquare.2
  · have hlarge : 1 / K < |θ| := lt_of_not_ge hsmall
    let lam : ℝ := 1 / (Real.sqrt 2 * K)
    have hsqrt2_pos : 0 < Real.sqrt 2 :=
      Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
    have hlam_abs : |lam| ≤ 1 / K := by
      have hsqrt2_ge_one : 1 ≤ Real.sqrt 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          sq_nonneg (Real.sqrt 2)]
      dsimp [lam]
      rw [abs_of_pos (div_pos zero_lt_one (mul_pos hsqrt2_pos hKpos))]
      exact div_le_div_of_nonneg_left zero_le_one hKpos (by
        nlinarith [hKpos, hsqrt2_ge_one])
    have hsquare := hsq lam hlam_abs
    have hlam_sq_fun :
        (fun ω => Real.exp (lam ^ 2 * X ω ^ 2)) =
          fun ω => Real.exp (X ω ^ 2 / (2 * K ^ 2)) := by
      funext ω
      congr 1
      dsimp [lam]
      field_simp [hKpos.ne', hsqrt2_pos.ne']
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hlam_bound : K ^ 2 * lam ^ 2 = 1 / 2 := by
      dsimp [lam]
      field_simp [hKpos.ne', hsqrt2_pos.ne']
      ring_nf
      exact (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm
    have hhalf_int :
        Integrable (fun ω => Real.exp (X ω ^ 2 / (2 * K ^ 2))) μ := by
      rw [← hlam_sq_fun]
      exact hsquare.1
    have htarget_aesm :
        AEStronglyMeasurable (fun ω => Real.exp (θ * X ω)) μ := by
      exact
        (Measurable.comp_aemeasurable Real.measurable_exp
          (hXm.const_mul θ)).aestronglyMeasurable
    have hdom_int :
        Integrable
          (fun ω => Real.exp (K ^ 2 * θ ^ 2 / 2) *
            Real.exp (X ω ^ 2 / (2 * K ^ 2))) μ :=
      hhalf_int.const_mul (Real.exp (K ^ 2 * θ ^ 2 / 2))
    have hyoung :
        ∀ x : ℝ, θ * x ≤ K ^ 2 * θ ^ 2 / 2 + x ^ 2 / (2 * K ^ 2) := by
      intro x
      have hsq_nonneg : 0 ≤ (θ * K - x / K) ^ 2 := sq_nonneg _
      field_simp [hKpos.ne'] at hsq_nonneg ⊢
      nlinarith
    have hpoint :
        ∀ ω, Real.exp (θ * X ω)
          ≤ Real.exp (K ^ 2 * θ ^ 2 / 2) *
              Real.exp (X ω ^ 2 / (2 * K ^ 2)) := by
      intro ω
      calc
        Real.exp (θ * X ω)
            ≤ Real.exp (K ^ 2 * θ ^ 2 / 2 + X ω ^ 2 / (2 * K ^ 2)) :=
          Real.exp_le_exp.mpr (hyoung (X ω))
        _ = Real.exp (K ^ 2 * θ ^ 2 / 2) *
              Real.exp (X ω ^ 2 / (2 * K ^ 2)) := by
          rw [Real.exp_add]
    have hdom_nonneg :
        ∀ ω, 0 ≤ Real.exp (K ^ 2 * θ ^ 2 / 2) *
          Real.exp (X ω ^ 2 / (2 * K ^ 2)) :=
      fun _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    have htarget_int : Integrable (fun ω => Real.exp (θ * X ω)) μ := by
      refine hdom_int.mono htarget_aesm ?_
      exact Filter.Eventually.of_forall fun ω => by
        have htarget_nonneg : 0 ≤ Real.exp (θ * X ω) := (Real.exp_pos _).le
        simpa [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg,
          abs_of_nonneg (hdom_nonneg ω)] using hpoint ω
    have hlarge_sq : 1 ≤ K ^ 2 * θ ^ 2 := by
      have hlarge_sq' : (1 / K) ^ 2 ≤ |θ| ^ 2 := by
        exact (sq_le_sq.mpr (by
          rw [abs_of_pos (one_div_pos.mpr hKpos), abs_of_nonneg (abs_nonneg θ)]
          exact hlarge.le))
      rw [sq_abs] at hlarge_sq'
      have hmul := mul_le_mul_of_nonneg_right hlarge_sq' hKsq_nonneg
      field_simp [hKpos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    refine ⟨htarget_int, ?_⟩
    calc
      mgf X μ θ = ∫ ω, Real.exp (θ * X ω) ∂μ := rfl
      _ ≤ ∫ ω, Real.exp (K ^ 2 * θ ^ 2 / 2) *
            Real.exp (X ω ^ 2 / (2 * K ^ 2)) ∂μ :=
        integral_mono htarget_int hdom_int hpoint
      _ = Real.exp (K ^ 2 * θ ^ 2 / 2) *
            ∫ ω, Real.exp (X ω ^ 2 / (2 * K ^ 2)) ∂μ := by
        rw [integral_const_mul]
      _ ≤ Real.exp (K ^ 2 * θ ^ 2 / 2) * Real.exp (1 / 2) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [hlam_sq_fun, hlam_bound] using hsquare.2)
          (Real.exp_pos _).le
      _ = Real.exp (K ^ 2 * θ ^ 2 / 2 + 1 / 2) := by
        rw [Real.exp_add]
      _ ≤ Real.exp (K ^ 2 * θ ^ 2) := by
        rw [Real.exp_le_exp]
        nlinarith

/-- Mean-zero Orlicz sub-gaussian variables satisfy the book's global MGF
bound. This is the `(iv) ⇒ (iii) ⇒ (v)` chain in Proposition 2.5.2. -/
theorem subGaussianMGFCondition_of_orliczCondition_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subGaussianOrliczCondition X μ K)
    (hmean : ∫ ω, X ω ∂μ = 0) :
    subGaussianMGFCondition X μ K :=
  subGaussianMGFCondition_of_squareMGFCondition_of_integral_eq_zero
    hXm (subGaussianSquareMGFCondition_of_subGaussianOrliczCondition hX) hmean

/-- HDP Proposition 2.5.2, direction `(iii) ⇒ (iv)` with an explicit
absolute-constant rescaling. Taking
`θ = sqrt(log 2) / K` in the local square-MGF bound gives
`E exp(X² / (K / sqrt(log 2))²) ≤ 2`. -/
theorem subGaussianOrliczCondition_of_squareMGFCondition
    {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (hX : subGaussianSquareMGFCondition X μ K) :
    subGaussianOrliczCondition X μ (K / Real.sqrt (Real.log 2)) := by
  rcases hX with ⟨hKpos, hsq⟩
  have hlog2_pos : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hsqrt_pos : 0 < Real.sqrt (Real.log 2) :=
    Real.sqrt_pos.2 hlog2_pos
  have hsqrt_sq : Real.sqrt (Real.log 2) ^ 2 = Real.log 2 :=
    Real.sq_sqrt hlog2_pos.le
  let θ : ℝ := Real.sqrt (Real.log 2) / K
  have hθ_abs : |θ| ≤ 1 / K := by
    have hsqrt_le_one : Real.sqrt (Real.log 2) ≤ 1 := by
      simpa using (Real.sqrt_le_one (x := Real.log 2)).2 hlog2_le_one
    dsimp [θ]
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hKpos]
    exact div_le_div_of_nonneg_right hsqrt_le_one hKpos.le
  have hθ := hsq θ hθ_abs
  have hscale_pos : 0 < K / Real.sqrt (Real.log 2) :=
    div_pos hKpos hsqrt_pos
  have hfun :
      (fun ω => Real.exp (θ ^ 2 * X ω ^ 2)) =
        fun ω => Real.exp (X ω ^ 2 / (K / Real.sqrt (Real.log 2)) ^ 2) := by
    funext ω
    congr 1
    dsimp [θ]
    field_simp [hKpos.ne', hsqrt_pos.ne']
  have hKθ : K ^ 2 * θ ^ 2 = Real.log 2 := by
    dsimp [θ]
    field_simp [hKpos.ne']
    exact hsqrt_sq
  refine ⟨hscale_pos, ?_, ?_⟩
  · simpa [hfun] using hθ.1
  · calc
      ∫ ω, Real.exp (X ω ^ 2 / (K / Real.sqrt (Real.log 2)) ^ 2) ∂μ
          = ∫ ω, Real.exp (θ ^ 2 * X ω ^ 2) ∂μ := by
            rw [← hfun]
      _ ≤ Real.exp (K ^ 2 * θ ^ 2) := hθ.2
      _ = 2 := by
        rw [hKθ, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Exercise 2.5.5(b), tail-zero form: if the square-exponential MGF is
bounded by `exp(K θ²)` for every real `θ`, then all tails above `sqrt K`
have probability zero. -/
theorem squareMGF_global_bound_tail_zero_of_sqrt_lt
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {K B : ℝ}
    (hK : 0 ≤ K)
    (hX : ∀ θ,
      Integrable (fun ω => Real.exp (θ ^ 2 * X ω ^ 2)) μ ∧
        ∫ ω, Real.exp (θ ^ 2 * X ω ^ 2) ∂μ ≤ Real.exp (K * θ ^ 2))
    (hB : Real.sqrt K < B) :
    μ.real {ω | B ≤ |X ω|} = 0 := by
  have hBpos : 0 < B :=
    lt_of_le_of_lt (Real.sqrt_nonneg K) hB
  have hK_lt_Bsq : K < B ^ 2 := by
    have hsquares : Real.sqrt K ^ 2 < B ^ 2 := by
      exact sq_lt_sq.mpr (by
        simpa [abs_of_nonneg (Real.sqrt_nonneg K), abs_of_pos hBpos] using hB)
    simpa [Real.sq_sqrt hK] using hsquares
  let A : Set Ω := {ω | B ≤ |X ω|}
  have hle_bound :
      ∀ θ : ℝ, μ.real A ≤ Real.exp (-(B ^ 2 - K) * θ ^ 2) := by
    intro θ
    let Y : Ω → ℝ := fun ω => Real.exp (θ ^ 2 * X ω ^ 2)
    have hY_nonneg : 0 ≤ᵐ[μ] Y :=
      Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
    have hthreshold_pos : 0 < Real.exp (θ ^ 2 * B ^ 2) :=
      Real.exp_pos _
    have hsubset :
        A ⊆ {ω | Real.exp (θ ^ 2 * B ^ 2) ≤ Y ω} := by
      intro ω hω
      change Real.exp (θ ^ 2 * B ^ 2) ≤ Y ω
      rw [Real.exp_le_exp]
      have hsquares : B ^ 2 ≤ |X ω| ^ 2 := by
        exact sq_le_sq.mpr (by
          simpa [abs_of_pos hBpos] using hω)
      have hmul : θ ^ 2 * B ^ 2 ≤ θ ^ 2 * X ω ^ 2 := by
        have hmul' := mul_le_mul_of_nonneg_left hsquares (sq_nonneg θ)
        simpa [sq_abs] using hmul'
      simpa [Y] using hmul
    have hmarkov :=
      markov_inequality
        (μ := μ) (X := Y) hY_nonneg (hX θ).1
        (t := Real.exp (θ ^ 2 * B ^ 2)) hthreshold_pos
    calc
      μ.real A
          ≤ μ.real {ω | Real.exp (θ ^ 2 * B ^ 2) ≤ Y ω} :=
        MeasureTheory.measureReal_mono hsubset
      _ ≤ (∫ ω, Y ω ∂μ) / Real.exp (θ ^ 2 * B ^ 2) := hmarkov
      _ ≤ Real.exp (K * θ ^ 2) / Real.exp (θ ^ 2 * B ^ 2) := by
        exact div_le_div_of_nonneg_right (hX θ).2 hthreshold_pos.le
      _ = Real.exp (-(B ^ 2 - K) * θ ^ 2) := by
        rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
        congr 1
        ring
  have hlim :
      Filter.Tendsto
        (fun θ : ℝ => Real.exp (-(B ^ 2 - K) * θ ^ 2))
        Filter.atTop (𝓝 0) := by
    have hsq :
        Filter.Tendsto (fun θ : ℝ => θ ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    have hneg :
        Filter.Tendsto (fun θ : ℝ => -(B ^ 2 - K) * θ ^ 2)
          Filter.atTop Filter.atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg
        (by linarith : -(B ^ 2 - K) < 0) hsq
    exact Real.tendsto_exp_atBot.comp hneg
  exact le_antisymm (ge_of_tendsto' hlim hle_bound) measureReal_nonneg

/-- Exercise 2.5.5(b), a.e.-boundedness form. Under a global
square-exponential MGF bound, `|X| ≤ B` almost surely for every
`B > sqrt K`. -/
theorem squareMGF_global_bound_ae_abs_le_of_sqrt_lt
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {K B : ℝ}
    (hK : 0 ≤ K)
    (hX : ∀ θ,
      Integrable (fun ω => Real.exp (θ ^ 2 * X ω ^ 2)) μ ∧
        ∫ ω, Real.exp (θ ^ 2 * X ω ^ 2) ∂μ ≤ Real.exp (K * θ ^ 2))
    (hB : Real.sqrt K < B) :
    ∀ᵐ ω ∂μ, |X ω| ≤ B := by
  rw [ae_iff]
  have hzero_real :=
    squareMGF_global_bound_tail_zero_of_sqrt_lt
      (X := X) (μ := μ) hK hX hB
  have hzero : μ {ω | B ≤ |X ω|} = 0 := by
    exact (MeasureTheory.measureReal_eq_zero_iff (μ := μ)
      (s := {ω | B ≤ |X ω|})).mp hzero_real
  exact measure_mono_null (fun ω hω => le_of_lt (not_le.mp hω)) hzero

end OrliczDefinition

section MGFProperties

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Mathlib's MGF-proxy predicate implies HDP Proposition 2.5.2(v), in the
book's convention `exp(K²θ²)`, when the proxy is `K²`. -/
theorem subGaussianMGFCondition_of_hasSubgaussianMGF
    {X : Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hX : HasSubgaussianMGF X (subgaussianProxy K) μ) :
    subGaussianMGFCondition X μ K := by
  refine ⟨hK, fun θ => ?_⟩
  refine ⟨hX.integrable_exp_mul θ, ?_⟩
  calc
    mgf X μ θ
        ≤ Real.exp (((subgaussianProxy K : ℝ≥0) : ℝ) * θ ^ 2 / 2) :=
      hX.mgf_le θ
    _ = Real.exp (K ^ 2 * θ ^ 2 / 2) := by
      rw [subgaussianProxy_coe]
    _ ≤ Real.exp (K ^ 2 * θ ^ 2) := by
      rw [Real.exp_le_exp]
      have hnonneg : 0 ≤ K ^ 2 * θ ^ 2 :=
        mul_nonneg (sq_nonneg K) (sq_nonneg θ)
      nlinarith

/-- The book's global MGF condition `E exp(θX) ≤ exp(K²θ²)` gives mathlib's
`HasSubgaussianMGF` predicate with proxy `(sqrt 2 * K)^2`. -/
theorem hasSubgaussianMGF_of_subGaussianMGFCondition
    {X : Ω → ℝ} {K : ℝ}
    (hX : subGaussianMGFCondition X μ K) :
    HasSubgaussianMGF X (subgaussianProxy (Real.sqrt 2 * K)) μ := by
  rcases hX with ⟨hKpos, hmgf⟩
  refine ⟨fun θ => (hmgf θ).1, fun θ => ?_⟩
  calc
    mgf X μ θ ≤ Real.exp (K ^ 2 * θ ^ 2) := (hmgf θ).2
    _ = Real.exp (((subgaussianProxy (Real.sqrt 2 * K) : ℝ≥0) : ℝ)
          * θ ^ 2 / 2) := by
      congr 1
      rw [subgaussianProxy_coe]
      have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      rw [mul_pow, hsqrt_sq]
      ring

/-- Mathlib's MGF-proxy predicate gives finite moments of all orders. This is
the finite-moment content used on the way to HDP Proposition 2.5.2(ii). -/
theorem memLp_of_hasSubgaussianMGF
    {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) (p : ℝ≥0) :
    MemLp X (p : ℝ≥0∞) μ :=
  hX.memLp p

/-- HDP Exercise 2.5.4, MGF-proxy form: property (v) forces centering.
The proof observes that `mgf X θ - exp(c θ²/2)` has a local maximum at
`θ = 0`, hence its derivative there is zero. -/
theorem integral_eq_zero_of_hasSubgaussianMGF
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) :
    ∫ ω, X ω ∂μ = 0 := by
  let F : ℝ → ℝ :=
    fun θ => mgf X μ θ - Real.exp ((c : ℝ) * θ ^ 2 / 2)
  have hF_local : IsLocalMax F 0 := by
    change ∀ᶠ θ in 𝓝 0, F θ ≤ F 0
    refine Filter.Eventually.of_forall ?_
    intro θ
    have hle : mgf X μ θ ≤ Real.exp ((c : ℝ) * θ ^ 2 / 2) :=
      hX.mgf_le θ
    have hFθ : F θ ≤ 0 := by
      exact sub_nonpos.mpr hle
    have hF0 : F 0 = 0 := by
      simp [F, mgf]
    simpa [hF0]
  have hderiv_local : deriv F 0 = 0 :=
    hF_local.deriv_eq_zero
  have h0 : 0 ∈ interior (integrableExpSet X μ) := by
    rw [hX.integrableExpSet_eq_univ, interior_univ]
    exact Set.mem_univ 0
  have henv_deriv :
      deriv (fun θ : ℝ => Real.exp ((c : ℝ) * θ ^ 2 / 2)) 0 = 0 := by
    rw [deriv_exp (by fun_prop)]
    simp
  have hderiv_F : deriv F 0 = ∫ ω, X ω ∂μ := by
    have hmgf_diff : DifferentiableAt ℝ (mgf X μ) 0 :=
      ProbabilityTheory.differentiableAt_mgf h0
    have henv_diff :
        DifferentiableAt ℝ
          (fun θ : ℝ => Real.exp ((c : ℝ) * θ ^ 2 / 2)) 0 := by
      fun_prop
    calc
      deriv F 0
          = deriv (mgf X μ) 0
              - deriv (fun θ : ℝ => Real.exp ((c : ℝ) * θ ^ 2 / 2)) 0 := by
        simpa [F] using deriv_fun_sub hmgf_diff henv_diff
      _ = ∫ ω, X ω ∂μ := by
        rw [ProbabilityTheory.deriv_mgf_zero h0, henv_deriv, sub_zero]
  rwa [hderiv_F] at hderiv_local

/-- HDP Exercise 2.5.4 in the book's property `(v)` convention: a global
sub-gaussian MGF bound forces the random variable to be centered. -/
theorem integral_eq_zero_of_subGaussianMGFCondition
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hX : subGaussianMGFCondition X μ K) :
    ∫ ω, X ω ∂μ = 0 := by
  rcases hX with ⟨_hKpos, hmgf⟩
  let F : ℝ → ℝ :=
    fun θ => mgf X μ θ - Real.exp (K ^ 2 * θ ^ 2)
  have hF_local : IsLocalMax F 0 := by
    change ∀ᶠ θ in 𝓝 0, F θ ≤ F 0
    refine Filter.Eventually.of_forall ?_
    intro θ
    have hle : mgf X μ θ ≤ Real.exp (K ^ 2 * θ ^ 2) := (hmgf θ).2
    have hFθ : F θ ≤ 0 := sub_nonpos.mpr hle
    have hF0 : F 0 = 0 := by
      simp [F, mgf]
    simpa [hF0]
  have hderiv_local : deriv F 0 = 0 :=
    hF_local.deriv_eq_zero
  have hExpSet : integrableExpSet X μ = Set.univ := by
    ext θ
    simp [integrableExpSet, (hmgf θ).1]
  have h0 : 0 ∈ interior (integrableExpSet X μ) := by
    rw [hExpSet, interior_univ]
    exact Set.mem_univ 0
  have henv_deriv :
      deriv (fun θ : ℝ => Real.exp (K ^ 2 * θ ^ 2)) 0 = 0 := by
    rw [deriv_exp (by fun_prop)]
    simp
  have hderiv_F : deriv F 0 = ∫ ω, X ω ∂μ := by
    have hmgf_diff : DifferentiableAt ℝ (mgf X μ) 0 :=
      ProbabilityTheory.differentiableAt_mgf h0
    have henv_diff :
        DifferentiableAt ℝ
          (fun θ : ℝ => Real.exp (K ^ 2 * θ ^ 2)) 0 := by
      fun_prop
    calc
      deriv F 0
          = deriv (mgf X μ) 0
              - deriv (fun θ : ℝ => Real.exp (K ^ 2 * θ ^ 2)) 0 := by
        simpa [F] using deriv_fun_sub hmgf_diff henv_diff
      _ = ∫ ω, X ω ∂μ := by
        rw [ProbabilityTheory.deriv_mgf_zero h0, henv_deriv, sub_zero]
  rwa [hderiv_F] at hderiv_local

/-- HDP Proposition 2.5.2, direction `(v) ⇒ (i)`: the book's MGF
condition gives two-sided sub-gaussian tails, with scale enlarged from `K` to
`2K`. -/
theorem subGaussianMGFCondition_tail_le
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K t : ℝ}
    (hX : subGaussianMGFCondition X μ K) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|}
      ≤ 2 * Real.exp (-(t ^ 2) / ((2 * K) ^ 2)) := by
  rcases hX with ⟨hKpos, hmgf⟩
  let θ : ℝ := t / (2 * K ^ 2)
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hKpos
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ]
    positivity
  have hthreshold_pos : 0 < Real.exp (θ * t) :=
    Real.exp_pos _
  have htail_pos :
      μ.real {ω | t ≤ X ω}
        ≤ Real.exp (-(t ^ 2) / ((2 * K) ^ 2)) := by
    let Y : Ω → ℝ := fun ω => Real.exp (θ * X ω)
    have hY_nonneg : 0 ≤ᵐ[μ] Y :=
      Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
    have hsubset :
        {ω | t ≤ X ω} ⊆ {ω | Real.exp (θ * t) ≤ Y ω} := by
      intro ω hω
      change Real.exp (θ * t) ≤ Y ω
      rw [Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left hω hθ_nonneg
    have hmarkov :=
      markov_inequality
        (μ := μ) (X := Y) hY_nonneg (hmgf θ).1
        (t := Real.exp (θ * t)) hthreshold_pos
    calc
      μ.real {ω | t ≤ X ω}
          ≤ μ.real {ω | Real.exp (θ * t) ≤ Y ω} :=
        MeasureTheory.measureReal_mono hsubset
      _ ≤ (∫ ω, Y ω ∂μ) / Real.exp (θ * t) := hmarkov
      _ ≤ Real.exp (K ^ 2 * θ ^ 2) / Real.exp (θ * t) := by
        exact div_le_div_of_nonneg_right (hmgf θ).2 hthreshold_pos.le
      _ = Real.exp (-(t ^ 2) / ((2 * K) ^ 2)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
        congr 1
        dsimp [θ]
        field_simp [hKpos.ne']
        ring
  have htail_neg :
      μ.real {ω | t ≤ -X ω}
        ≤ Real.exp (-(t ^ 2) / ((2 * K) ^ 2)) := by
    let Y : Ω → ℝ := fun ω => Real.exp ((-θ) * X ω)
    have hY_nonneg : 0 ≤ᵐ[μ] Y :=
      Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
    have hsubset :
        {ω | t ≤ -X ω} ⊆ {ω | Real.exp (θ * t) ≤ Y ω} := by
      intro ω hω
      change Real.exp (θ * t) ≤ Y ω
      rw [Real.exp_le_exp]
      have hmul := mul_le_mul_of_nonneg_left hω hθ_nonneg
      simpa [Y, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hmarkov :=
      markov_inequality
        (μ := μ) (X := Y) hY_nonneg (hmgf (-θ)).1
        (t := Real.exp (θ * t)) hthreshold_pos
    calc
      μ.real {ω | t ≤ -X ω}
          ≤ μ.real {ω | Real.exp (θ * t) ≤ Y ω} :=
        MeasureTheory.measureReal_mono hsubset
      _ ≤ (∫ ω, Y ω ∂μ) / Real.exp (θ * t) := hmarkov
      _ ≤ Real.exp (K ^ 2 * (-θ) ^ 2) / Real.exp (θ * t) := by
        exact div_le_div_of_nonneg_right (hmgf (-θ)).2 hthreshold_pos.le
      _ = Real.exp (-(t ^ 2) / ((2 * K) ^ 2)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
        congr 1
        dsimp [θ]
        field_simp [hKpos.ne']
        ring
  let A : Set Ω := {ω | t ≤ X ω}
  let B : Set Ω := {ω | t ≤ -X ω}
  have hsubset_abs : {ω | t ≤ |X ω|} ⊆ A ∪ B := by
    intro ω hω
    by_cases hx : 0 ≤ X ω
    · exact Or.inl (by simpa [A, abs_of_nonneg hx] using hω)
    · have hxneg : X ω < 0 := lt_of_not_ge hx
      exact Or.inr (by simpa [B, abs_of_neg hxneg] using hω)
  calc
    μ.real {ω | t ≤ |X ω|} ≤ μ.real (A ∪ B) :=
      MeasureTheory.measureReal_mono hsubset_abs
    _ ≤ μ.real A + μ.real B :=
      MeasureTheory.measureReal_union_le A B
    _ ≤ Real.exp (-(t ^ 2) / ((2 * K) ^ 2))
        + Real.exp (-(t ^ 2) / ((2 * K) ^ 2)) :=
      add_le_add (by simpa [A] using htail_pos) (by simpa [B] using htail_neg)
    _ = 2 * Real.exp (-(t ^ 2) / ((2 * K) ^ 2)) := by ring

/-- Predicate form of the preceding implication. -/
theorem subGaussianTailCondition_of_subGaussianMGFCondition
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hX : subGaussianMGFCondition X μ K) :
    subGaussianTailCondition X μ (2 * K) :=
  ⟨mul_pos (by norm_num) hX.1,
    fun t ht => subGaussianMGFCondition_tail_le (K := K) hX ht⟩

/-- A `HasSubgaussianMGF` proxy gives the book's moment-growth condition, with
an explicit absolute-constant loss. -/
theorem subGaussianMomentCondition_of_hasSubgaussianMGF
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hK : 0 < K)
    (hX : HasSubgaussianMGF X (subgaussianProxy K) μ) :
    subGaussianMomentCondition X μ (8 * K) := by
  have hBookMGF :
      subGaussianMGFCondition X μ K :=
    subGaussianMGFCondition_of_hasSubgaussianMGF (μ := μ) (X := X) hK hX
  have hTail :
      subGaussianTailCondition X μ (2 * K) :=
    subGaussianTailCondition_of_subGaussianMGFCondition
      (μ := μ) (X := X) (K := K) hBookMGF
  have hMom :
      subGaussianMomentCondition X μ (4 * (2 * K)) :=
    subGaussianMomentCondition_of_subGaussianTailCondition
      (μ := μ) (X := X) (K := 2 * K)
      hX.aestronglyMeasurable hTail
  have hscale : 4 * (2 * K) = 8 * K := by ring
  simpa [hscale] using hMom

end MGFProperties

section Examples

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- HDP Example 2.5.8(c), quantitative Orlicz form: an a.e. bounded random
variable is sub-gaussian. If `|X| ≤ B` and `B²/K² ≤ log 2`, then
`E exp(X²/K²) ≤ 2`. -/
theorem subGaussianOrliczCondition_of_ae_abs_le
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {B K : ℝ}
    (hXm : AEMeasurable X μ)
    (hB : 0 ≤ B)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ B)
    (hK : 0 < K)
    (hscale : B ^ 2 / K ^ 2 ≤ Real.log 2) :
    subGaussianOrliczCondition X μ K := by
  have hf_aemeas :
      AEMeasurable (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) μ := by
    fun_prop
  have hle_ae :
      (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) ≤ᵐ[μ]
        fun _ω : Ω => (2 : ℝ) := by
    filter_upwards [hbound] with ω hω
    have hsquares : X ω ^ 2 ≤ B ^ 2 :=
      sq_le_sq.mpr (by simpa [abs_of_nonneg hB] using hω)
    have hdiv : X ω ^ 2 / K ^ 2 ≤ B ^ 2 / K ^ 2 :=
      div_le_div_of_nonneg_right hsquares (sq_nonneg K)
    calc
      Real.exp (X ω ^ 2 / K ^ 2)
          ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr (hdiv.trans hscale)
      _ = 2 := Real.exp_log (by norm_num : (0 : ℝ) < 2)
  have hInt :
      Integrable (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) μ := by
    refine Integrable.of_bound hf_aemeas.aestronglyMeasurable 2 ?_
    exact hle_ae.mono fun ω hω => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hω
  refine ⟨hK, hInt, ?_⟩
  have hconst_int : Integrable (fun _ω : Ω => (2 : ℝ)) μ := integrable_const 2
  have hint_le :
      ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ
        ≤ ∫ _ω : Ω, (2 : ℝ) ∂μ :=
    integral_mono_ae hInt hconst_int hle_ae
  simpa using hint_le

/-- A positive a.e. bound `B` gives the concrete scale
`B / sqrt(log 2)`, matching the constant in HDP Example 2.5.8(c). -/
theorem subGaussianOrliczCondition_of_ae_abs_le_scaled
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {B : ℝ}
    (hXm : AEMeasurable X μ)
    (hB : 0 < B)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ B) :
    subGaussianOrliczCondition X μ (B / Real.sqrt (Real.log 2)) := by
  have hlog2_pos : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsqrt_pos : 0 < Real.sqrt (Real.log 2) :=
    Real.sqrt_pos.2 hlog2_pos
  have hK : 0 < B / Real.sqrt (Real.log 2) :=
    div_pos hB hsqrt_pos
  have hsqrt_sq : Real.sqrt (Real.log 2) ^ 2 = Real.log 2 :=
    Real.sq_sqrt hlog2_pos.le
  have hscale : B ^ 2 / (B / Real.sqrt (Real.log 2)) ^ 2 ≤ Real.log 2 := by
    have hB_ne : B ≠ 0 := ne_of_gt hB
    have hsqrt_ne : Real.sqrt (Real.log 2) ≠ 0 := ne_of_gt hsqrt_pos
    rw [div_pow, hsqrt_sq]
    field_simp [hB_ne, hsqrt_ne, hlog2_pos.ne']
    norm_num
  exact
    subGaussianOrliczCondition_of_ae_abs_le
      hXm hB.le hbound hK hscale

/-- HDP Example 2.5.8(c), `ψ₂`-norm form: an a.e. bounded random variable
satisfies `‖X‖_{ψ₂} ≤ B / sqrt(log 2)` whenever `|X| ≤ B` a.e. -/
theorem subGaussianNorm_le_of_ae_abs_le_scaled
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {B : ℝ}
    (hXm : AEMeasurable X μ)
    (hB : 0 < B)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ B) :
    subGaussianNorm X μ ≤ B / Real.sqrt (Real.log 2) :=
  subGaussianNorm_le_of_subGaussianOrliczCondition
    (subGaussianOrliczCondition_of_ae_abs_le_scaled hXm hB hbound)

/-- HDP Example 2.5.8(b), MGF-proxy form: a symmetric Bernoulli/Rademacher
variable has proxy `1`. -/
theorem symmetricBernoulli_hasSubgaussianMGF
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : IsSymmetricBernoulli X μ) :
    HasSubgaussianMGF X 1 μ :=
  hasSubgaussianMGF_of_isSymmetricBernoulli hX

/-- HDP Example 2.5.8(b), book MGF convention. -/
theorem symmetricBernoulli_subGaussianMGFCondition
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : IsSymmetricBernoulli X μ) :
    subGaussianMGFCondition X μ 1 := by
  simpa using
    subGaussianMGFCondition_of_hasSubgaussianMGF
      (μ := μ) (X := X) (K := 1) (by norm_num)
      (by simpa [subgaussianProxy] using symmetricBernoulli_hasSubgaussianMGF hX)

/-- HDP Example 2.5.8(b), `ψ₂`-norm form: a symmetric
Bernoulli/Rademacher variable has `ψ₂` norm at most `1 / sqrt(log 2)`. -/
theorem symmetricBernoulli_subGaussianNorm_le
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : IsSymmetricBernoulli X μ) :
    subGaussianNorm X μ ≤ 1 / Real.sqrt (Real.log 2) := by
  refine
    subGaussianNorm_le_of_ae_abs_le_scaled
      (μ := μ) (X := X) (B := 1) hX.aemeasurable (by norm_num) ?_
  filter_upwards [ae_mem_Icc_of_isSymmetricBernoulli (μ := μ) hX] with ω hω
  simpa [Set.mem_Icc, abs_le] using hω

/-- Square-exponential integral for a symmetric Bernoulli/Rademacher
variable. This is the computation behind the exact value in HDP
Example 2.5.8(b). -/
theorem symmetricBernoulli_integral_exp_sq_div_eq
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : IsSymmetricBernoulli X μ) (K : ℝ) :
    ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ =
      Real.exp (1 / K ^ 2) := by
  calc
    ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ
        = ∫ x, Real.exp (x ^ 2 / K ^ 2) ∂rademacherPMF.toMeasure :=
      by
        simpa [Function.comp_def] using
          hX.integral_comp
            (f := fun x : ℝ => Real.exp (x ^ 2 / K ^ 2))
            (by fun_prop)
    _ = Real.exp (1 / K ^ 2) := by
      rw [rademacher_integral_eq _ (by fun_prop)]
      ring_nf

/-- HDP Example 2.5.8(b), exact `ψ₂` norm of a symmetric
Bernoulli/Rademacher variable: `‖X‖_{ψ₂} = 1 / sqrt(log 2)`. -/
theorem symmetricBernoulli_subGaussianNorm_eq
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : IsSymmetricBernoulli X μ) :
    subGaussianNorm X μ = 1 / Real.sqrt (Real.log 2) := by
  refine le_antisymm (symmetricBernoulli_subGaussianNorm_le (μ := μ) hX) ?_
  let c : ℝ := 1 / Real.sqrt (Real.log 2)
  have hlog2_pos : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hbound : ∀ᵐ ω ∂μ, |X ω| ≤ 1 := by
    filter_upwards [ae_mem_Icc_of_isSymmetricBernoulli (μ := μ) hX] with ω hω
    simpa [Set.mem_Icc, abs_le] using hω
  have hcond_c : subGaussianOrliczCondition X μ c := by
    simpa [c] using
      subGaussianOrliczCondition_of_ae_abs_le_scaled
        (μ := μ) (X := X) (B := 1)
        hX.aemeasurable (by norm_num) hbound
  unfold subGaussianNorm
  refine le_csInf ⟨c, hcond_c⟩ ?_
  intro K hK
  have hKpos : 0 < K := hK.1
  have hExp_le : Real.exp (1 / K ^ 2) ≤ 2 := by
    rw [← symmetricBernoulli_integral_exp_sq_div_eq (μ := μ) hX K]
    exact hK.2.2
  have hlog_le : 1 / K ^ 2 ≤ Real.log 2 := by
    have h :=
      Real.log_le_log (Real.exp_pos (1 / K ^ 2)) hExp_le
    simpa using h
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hKpos
  have hKsq_ge : 1 / Real.log 2 ≤ K ^ 2 :=
    (one_div_le hKsq_pos hlog2_pos).mp hlog_le
  have hc_sq : c ^ 2 = 1 / Real.log 2 := by
    dsimp [c]
    rw [div_pow, one_pow, Real.sq_sqrt hlog2_pos.le]
  have hsq_le : c ^ 2 ≤ K ^ 2 := by
    simpa [hc_sq] using hKsq_ge
  exact (sq_le_sq₀ hc_nonneg hKpos.le).mp hsq_le

/-- HDP Example 2.5.8(c), centered bounded MGF-proxy form. This is the
Hoeffding-lemma bridge used throughout Chapter 2. -/
theorem bounded_centered_hasSubgaussianMGF
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {a b : ℝ}
    (hXm : AEMeasurable X μ)
    (hbdd : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hmean : ∫ ω, X ω ∂μ = 0) :
    HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) μ :=
  ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    hXm hbdd hmean

end Examples

section NegativeExamples

/-- Tail of the exponential distribution: for `t ≥ 0`,
`P{X > t} = exp (-rt)`.  The strict tail avoids any atom bookkeeping. -/
theorem expMeasure_real_Ioi_eq_exp_neg_mul {r t : ℝ}
    (hr : 0 < r) (ht : 0 ≤ t) :
    (ProbabilityTheory.expMeasure r).real (Set.Ioi t) =
      Real.exp (-(r * t)) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  have hcompl : (Set.Iic t : Set ℝ)ᶜ = Set.Ioi t := by
    ext x
    simp
  calc
    (ProbabilityTheory.expMeasure r).real (Set.Ioi t)
        = (ProbabilityTheory.expMeasure r).real ((Set.Iic t : Set ℝ)ᶜ) := by
      rw [hcompl]
    _ = 1 - (ProbabilityTheory.expMeasure r).real (Set.Iic t) := by
      rw [MeasureTheory.measureReal_compl (μ := ProbabilityTheory.expMeasure r)
        measurableSet_Iic]
      rw [MeasureTheory.probReal_univ]
    _ = 1 - ProbabilityTheory.cdf (ProbabilityTheory.expMeasure r) t := by
      rw [ProbabilityTheory.cdf_eq_real]
    _ = 1 - (1 - Real.exp (-(r * t))) := by
      rw [ProbabilityTheory.cdf_expMeasure_eq hr t, if_pos ht]
    _ = Real.exp (-(r * t)) := by ring

/-- Quadratic Gaussian tails are eventually strictly smaller than an
exponential tail.  This is the scalar comparison used in Exercise 2.5.9. -/
lemma two_mul_exp_neg_sq_lt_exp_neg_linear
    {K r t : ℝ} (hquad : Real.log 2 < t ^ 2 / K ^ 2 - r * t) :
    2 * Real.exp (-(t ^ 2) / K ^ 2) < Real.exp (-(r * t)) := by
  have hlt :
      Real.log 2 + (-(t ^ 2) / K ^ 2) < -(r * t) := by
    have hneg_div : (-(t ^ 2) / K ^ 2) = -(t ^ 2 / K ^ 2) := by
      ring
    rw [hneg_div]
    linarith
  calc
    2 * Real.exp (-(t ^ 2) / K ^ 2)
        = Real.exp (Real.log 2 + (-(t ^ 2) / K ^ 2)) := by
      calc
        2 * Real.exp (-(t ^ 2) / K ^ 2)
            = Real.exp (Real.log 2) * Real.exp (-(t ^ 2) / K ^ 2) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        _ = Real.exp (Real.log 2 + (-(t ^ 2) / K ^ 2)) := by
          rw [← Real.exp_add]
    _ < Real.exp (-(r * t)) := Real.exp_lt_exp.mpr hlt

/-- A threshold form of the quadratic-vs-linear tail comparison: once `t` is
at least this explicit scale, `2 exp(-t²/K²) < exp(-rt)`. -/
lemma two_mul_exp_neg_sq_lt_exp_neg_linear_of_ge
    {K r t : ℝ} (hK : 0 < K) (hr : 0 < r)
    (ht :
      K ^ 2 * (r + 1) + (Real.log 2 + 1) ≤ t) :
    2 * Real.exp (-(t ^ 2) / K ^ 2) < Real.exp (-(r * t)) := by
  have hlog2_pos : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hlog2p_nonneg : 0 ≤ Real.log 2 + 1 := by linarith
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hK
  have hKsq_ne : K ^ 2 ≠ 0 := ne_of_gt hKsq_pos
  have hthreshold_ge_log2p :
      Real.log 2 + 1 ≤ K ^ 2 * (r + 1) + (Real.log 2 + 1) := by
    nlinarith [sq_nonneg K, hr.le]
  have ht_ge_log2p : Real.log 2 + 1 ≤ t :=
    hthreshold_ge_log2p.trans ht
  have ht_nonneg : 0 ≤ t := hlog2p_nonneg.trans ht_ge_log2p
  have hbase_factor :
      (K ^ 2 * (r + 1) + (Real.log 2 + 1)) / K ^ 2 - r =
        1 + (Real.log 2 + 1) / K ^ 2 := by
    field_simp [hKsq_ne]
    ring
  have hdiv :
      (K ^ 2 * (r + 1) + (Real.log 2 + 1)) / K ^ 2 ≤
        t / K ^ 2 :=
    div_le_div_of_nonneg_right ht hKsq_pos.le
  have hfactor_ge_one : 1 ≤ t / K ^ 2 - r := by
    have hnonneg : 0 ≤ (Real.log 2 + 1) / K ^ 2 :=
      div_nonneg hlog2p_nonneg hKsq_pos.le
    linarith
  have hprod_ge :
      Real.log 2 + 1 ≤ t * (t / K ^ 2 - r) := by
    have h :=
      mul_le_mul ht_ge_log2p hfactor_ge_one
        (by norm_num : (0 : ℝ) ≤ 1) ht_nonneg
    simpa using h
  have hquad :
      Real.log 2 < t ^ 2 / K ^ 2 - r * t := by
    have hquad_eq :
        t ^ 2 / K ^ 2 - r * t = t * (t / K ^ 2 - r) := by
      ring
    rw [hquad_eq]
    linarith
  exact two_mul_exp_neg_sq_lt_exp_neg_linear hquad

/-- A concrete scale where the preceding quadratic-vs-linear comparison holds. -/
lemma exists_two_mul_exp_neg_sq_lt_exp_neg_linear
    {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    ∃ t : ℝ, 0 ≤ t ∧
      2 * Real.exp (-(t ^ 2) / K ^ 2) < Real.exp (-(r * t)) := by
  let t : ℝ := K ^ 2 * (r + 1) + (Real.log 2 + 1)
  have hlog2_pos : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hlog2p_nonneg : 0 ≤ Real.log 2 + 1 := by linarith
  have ht_ge_log2p : Real.log 2 + 1 ≤ t := by
    dsimp [t]
    nlinarith [sq_nonneg K, hr.le]
  have ht_nonneg : 0 ≤ t := hlog2p_nonneg.trans ht_ge_log2p
  exact ⟨t, ht_nonneg,
    two_mul_exp_neg_sq_lt_exp_neg_linear_of_ge hK hr (by rfl)⟩

/-- Lower exponential tails obstruct sub-gaussianity. This is the reusable
tail-comparison criterion behind the exponential example in HDP
Exercise 2.5.9. -/
theorem not_isSubGaussian_of_exp_tail_lower_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {r : ℝ}
    (hr : 0 < r)
    (htail : ∀ t, 0 ≤ t →
      Real.exp (-(r * t)) ≤ μ.real {ω | t ≤ |X ω|}) :
    ¬ IsSubGaussian X μ := by
  rintro ⟨K, hKcond⟩
  rcases exists_two_mul_exp_neg_sq_lt_exp_neg_linear hKcond.1 hr with
    ⟨t, ht_nonneg, hstrict⟩
  have htail_lower :
      Real.exp (-(r * t)) ≤ μ.real {ω | t ≤ |X ω|} :=
    htail t ht_nonneg
  have htail_upper :
      μ.real {ω | t ≤ |X ω|}
        ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) :=
    subGaussianOrliczCondition_tail_le
      (μ := μ) (X := X) (K := K) (t := t) hKcond ht_nonneg
  linarith

/-- Eventual lower exponential tails also obstruct sub-gaussianity.  This is
the threshold-friendly form intended for heavier-tailed examples where the
lower bound is only proved past a large point. -/
theorem not_isSubGaussian_of_arbitrarily_large_exp_tail_lower_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {r : ℝ}
    (hr : 0 < r)
    (htail : ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧
      Real.exp (-(r * t)) ≤ μ.real {ω | t ≤ |X ω|}) :
    ¬ IsSubGaussian X μ := by
  rintro ⟨K, hKcond⟩
  let T : ℝ := K ^ 2 * (r + 1) + (Real.log 2 + 1)
  rcases htail T with ⟨t, ht_ge, htail_lower⟩
  have hlog2_pos : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    nlinarith [sq_nonneg K, hr.le, hlog2_pos.le]
  have ht_nonneg : 0 ≤ t := hT_nonneg.trans ht_ge
  have hstrict :
      2 * Real.exp (-(t ^ 2) / K ^ 2) < Real.exp (-(r * t)) :=
    two_mul_exp_neg_sq_lt_exp_neg_linear_of_ge
      hKcond.1 hr ht_ge
  have htail_upper :
      μ.real {ω | t ≤ |X ω|}
        ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) :=
    subGaussianOrliczCondition_tail_le
      (μ := μ) (X := X) (K := K) (t := t) hKcond ht_nonneg
  linarith

/-- The elementary asymptotic comparison `x log x = o(x²)`.  This is the
growth separation behind the Poisson example in Exercise 2.5.9. -/
lemma mul_log_isLittleO_sq_atTop :
    (fun x : ℝ => x * Real.log x) =o[atTop] fun x : ℝ => x ^ 2 := by
  have hlog :
      Real.log =o[atTop] fun x : ℝ => x ^ (1 : ℝ) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)
  have hid :
      (fun x : ℝ => x) =O[atTop] fun x : ℝ => x :=
    Asymptotics.isBigO_refl (fun x : ℝ => x) atTop
  have h := hlog.mul_isBigO hid
  simpa [Real.rpow_one, pow_two, mul_comm, mul_left_comm, mul_assoc] using h

/-- Eventual scalar form of `x log x = o(x²)`. -/
lemma eventually_mul_log_le_mul_sq {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x * Real.log x ≤ c * x ^ 2 := by
  filter_upwards [mul_log_isLittleO_sq_atTop.def hc,
    eventually_ge_atTop (0 : ℝ)] with x hx hx_nonneg
  have hx_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hnorm_sq : ‖x ^ 2‖ = x ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx_sq_nonneg]
  exact (le_abs_self (x * Real.log x)).trans (by
    simpa [hnorm_sq, Real.norm_eq_abs] using hx)

/-- Point mass of the native Poisson law, as a real number. -/
theorem poissonMeasure_real_singleton_eq (lam : ℝ≥0) (n : ℕ) :
    (ProbabilityTheory.poissonMeasure lam).real ({n} : Set ℕ) =
      Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ) := by
  have hnonneg :
      0 ≤ Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n /
        (n.factorial : ℝ) := by
    positivity
  rw [measureReal_def, ProbabilityTheory.poissonMeasure_singleton,
    ENNReal.toReal_ofReal hnonneg]

/-- For every putative sub-gaussian scale `K`, a positive-parameter Poisson
law has a singleton atom whose mass is larger than the corresponding Gaussian
tail bound. -/
lemma exists_poisson_singleton_gt_gaussian_tail
    {K : ℝ} (hK : 0 < K) {lam : ℝ≥0} (hlam : 0 < lam) :
    ∃ n : ℕ, 1 ≤ n ∧
      2 * Real.exp (-((n : ℝ) ^ 2) / K ^ 2) <
        Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ) := by
  let L : ℝ := lam
  have hL_pos : 0 < L := by exact_mod_cast hlam
  let A : ℝ := Real.log 2 + L
  let B : ℝ := |Real.log L|
  let q : ℝ := 1 / (4 * K ^ 2)
  have hK_sq_pos : 0 < K ^ 2 := sq_pos_of_pos hK
  have hden_pos : 0 < 4 * K ^ 2 := by positivity
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hlarge :
      ∀ᶠ x : ℝ in atTop,
        max 1 (max (4 * K ^ 2 * A) (4 * K ^ 2 * B)) ≤ x :=
    eventually_ge_atTop (max 1 (max (4 * K ^ 2 * A) (4 * K ^ 2 * B)))
  have hevent :
      ∀ᶠ x : ℝ in atTop,
        1 ≤ x ∧
        A + (-(x * Real.log L)) + x * Real.log x < x ^ 2 / K ^ 2 := by
    filter_upwards [hlarge, eventually_mul_log_le_mul_sq hq_pos] with x hx_large hx_log
    have hx_ge_one : 1 ≤ x :=
      (le_max_left (1 : ℝ) (max (4 * K ^ 2 * A) (4 * K ^ 2 * B))).trans hx_large
    have hx_nonneg : 0 ≤ x := by linarith
    have hx_pos : 0 < x := by linarith
    have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_pos hx_pos
    have hx_ge_A :
        4 * K ^ 2 * A ≤ x :=
      (le_max_left (4 * K ^ 2 * A) (4 * K ^ 2 * B)).trans
        ((le_max_right (1 : ℝ) (max (4 * K ^ 2 * A) (4 * K ^ 2 * B))).trans
          hx_large)
    have hx_ge_B :
        4 * K ^ 2 * B ≤ x :=
      (le_max_right (4 * K ^ 2 * A) (4 * K ^ 2 * B)).trans
        ((le_max_right (1 : ℝ) (max (4 * K ^ 2 * A) (4 * K ^ 2 * B))).trans
          hx_large)
    have hA_le_linear : A ≤ x / (4 * K ^ 2) := by
      rw [le_div_iff₀ hden_pos]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hx_ge_A
    have hx_le_sq : x ≤ x ^ 2 := by nlinarith
    have hA_le : A ≤ q * x ^ 2 := by
      calc
        A ≤ x / (4 * K ^ 2) := hA_le_linear
        _ ≤ x ^ 2 / (4 * K ^ 2) :=
          div_le_div_of_nonneg_right hx_le_sq hden_pos.le
        _ = q * x ^ 2 := by
          dsimp [q]
          ring
    have hB_le_linear : B ≤ x / (4 * K ^ 2) := by
      rw [le_div_iff₀ hden_pos]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hx_ge_B
    have hB_le : B * x ≤ q * x ^ 2 := by
      calc
        B * x ≤ (x / (4 * K ^ 2)) * x :=
          mul_le_mul_of_nonneg_right hB_le_linear hx_nonneg
        _ = q * x ^ 2 := by
          dsimp [q]
          ring
    have hneg_log : -(x * Real.log L) ≤ B * x := by
      have hlog_bound : -Real.log L ≤ B := by
        dsimp [B]
        exact neg_le_abs (Real.log L)
      have hmul := mul_le_mul_of_nonneg_left hlog_bound hx_nonneg
      nlinarith
    have hthree_lt : q * x ^ 2 + q * x ^ 2 + q * x ^ 2 < x ^ 2 / K ^ 2 := by
      dsimp [q]
      field_simp [hK_sq_pos.ne']
      nlinarith [hx_sq_pos, hK_sq_pos]
    refine ⟨hx_ge_one, ?_⟩
    have hsum_le :
        A + (-(x * Real.log L)) + x * Real.log x ≤
          q * x ^ 2 + q * x ^ 2 + q * x ^ 2 := by
      nlinarith
    exact lt_of_le_of_lt hsum_le hthree_lt
  have hnat :
      ∀ᶠ n : ℕ in atTop,
        1 ≤ (n : ℝ) ∧
        A + (-((n : ℝ) * Real.log L)) + (n : ℝ) * Real.log (n : ℝ) <
          (n : ℝ) ^ 2 / K ^ 2 :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hevent
  rcases hnat.exists with ⟨n, hn_ge_one_real, hn_exp_bound⟩
  have hn_ge_one : 1 ≤ n := by exact_mod_cast hn_ge_one_real
  have hn_pos : 0 < n := Nat.succ_le_iff.mp hn_ge_one
  have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have hfact_pos : 0 < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hn_pow_pos : 0 < (n : ℝ) ^ n := pow_pos hn_real_pos n
  have hnum_nonneg :
      0 ≤ Real.exp (-L) * L ^ n := by
    positivity
  have hfact_le_pow : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hden_lower :
      Real.exp (-L) * L ^ n / ((n : ℝ) ^ n) ≤
        Real.exp (-L) * L ^ n / (n.factorial : ℝ) :=
    div_le_div_of_nonneg_left hnum_nonneg hfact_pos hfact_le_pow
  have hpow_L :
      Real.exp ((n : ℝ) * Real.log L) = L ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log hL_pos]
  have hpow_n :
      Real.exp ((n : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log hn_real_pos]
  have hpoint_exp :
      Real.exp (-L + (n : ℝ) * Real.log L -
          (n : ℝ) * Real.log (n : ℝ)) =
        Real.exp (-L) * L ^ n / ((n : ℝ) ^ n) := by
    rw [Real.exp_sub, Real.exp_add, hpow_L, hpow_n]
  have hleft_exp :
      2 * Real.exp (-((n : ℝ) ^ 2) / K ^ 2) =
        Real.exp (Real.log 2 + (-((n : ℝ) ^ 2) / K ^ 2)) := by
    calc
      2 * Real.exp (-((n : ℝ) ^ 2) / K ^ 2)
          = Real.exp (Real.log 2) *
              Real.exp (-((n : ℝ) ^ 2) / K ^ 2) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp (Real.log 2 + (-((n : ℝ) ^ 2) / K ^ 2)) := by
            rw [← Real.exp_add]
  have hexponent :
      Real.log 2 + (-((n : ℝ) ^ 2) / K ^ 2) <
        -L + (n : ℝ) * Real.log L -
          (n : ℝ) * Real.log (n : ℝ) := by
    have hneg_div :
        (-((n : ℝ) ^ 2) / K ^ 2) = -(((n : ℝ) ^ 2) / K ^ 2) := by ring
    rw [hneg_div]
    dsimp [A] at hn_exp_bound
    linarith
  refine ⟨n, hn_ge_one, ?_⟩
  calc
    2 * Real.exp (-((n : ℝ) ^ 2) / K ^ 2)
        = Real.exp (Real.log 2 + (-((n : ℝ) ^ 2) / K ^ 2)) := hleft_exp
    _ < Real.exp (-L + (n : ℝ) * Real.log L -
          (n : ℝ) * Real.log (n : ℝ)) :=
        Real.exp_lt_exp.mpr hexponent
    _ = Real.exp (-L) * L ^ n / ((n : ℝ) ^ n) := hpoint_exp
    _ ≤ Real.exp (-L) * L ^ n / (n.factorial : ℝ) := hden_lower

/-- HDP Exercise 2.5.9, Poisson example: a positive-parameter Poisson random
variable is not sub-gaussian.  The random variable is the canonical coercion
`ℕ → ℝ` under the native Poisson law. -/
theorem not_isSubGaussian_coe_poissonMeasure {lam : ℝ≥0} (hlam : 0 < lam) :
    ¬ IsSubGaussian (fun n : ℕ => (n : ℝ))
      (ProbabilityTheory.poissonMeasure lam) := by
  rintro ⟨K, hKcond⟩
  rcases exists_poisson_singleton_gt_gaussian_tail hKcond.1 hlam with
    ⟨n, hn_ge_one, hstrict⟩
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have htail_lower :
      Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ) ≤
        (ProbabilityTheory.poissonMeasure lam).real
          {m : ℕ | (n : ℝ) ≤ |(m : ℝ)|} := by
    have hsubset : ({n} : Set ℕ) ⊆ {m : ℕ | (n : ℝ) ≤ |(m : ℝ)|} := by
      intro m hm
      rw [Set.mem_singleton_iff] at hm
      subst m
      simp
    calc
      Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n.factorial : ℝ)
          = (ProbabilityTheory.poissonMeasure lam).real ({n} : Set ℕ) :=
            (poissonMeasure_real_singleton_eq lam n).symm
      _ ≤ (ProbabilityTheory.poissonMeasure lam).real
          {m : ℕ | (n : ℝ) ≤ |(m : ℝ)|} :=
            MeasureTheory.measureReal_mono hsubset
  have htail_upper :
      (ProbabilityTheory.poissonMeasure lam).real
          {m : ℕ | (n : ℝ) ≤ |(m : ℝ)|}
        ≤ 2 * Real.exp (-((n : ℝ) ^ 2) / K ^ 2) :=
    subGaussianOrliczCondition_tail_le
      (μ := ProbabilityTheory.poissonMeasure lam)
      (X := fun n : ℕ => (n : ℝ)) (K := K) (t := (n : ℝ))
      hKcond hn_nonneg
  linarith

/-- HDP Exercise 2.5.9, exponential example: an exponential random variable
with positive rate is not sub-gaussian. -/
theorem not_isSubGaussian_id_expMeasure {r : ℝ} (hr : 0 < r) :
    ¬ IsSubGaussian (fun x : ℝ => x) (ProbabilityTheory.expMeasure r) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  refine not_isSubGaussian_of_exp_tail_lower_one
    (μ := ProbabilityTheory.expMeasure r) (X := fun x : ℝ => x) hr ?_
  intro t ht_nonneg
  have htail_lower :
      Real.exp (-(r * t)) ≤
        (ProbabilityTheory.expMeasure r).real {x : ℝ | t ≤ |x|} := by
    have hsubset : Set.Ioi t ⊆ {x : ℝ | t ≤ |x|} := by
      intro x hx
      have hx_nonneg : 0 ≤ x := ht_nonneg.trans hx.le
      simpa [abs_of_nonneg hx_nonneg] using hx.le
    calc
      Real.exp (-(r * t))
          = (ProbabilityTheory.expMeasure r).real (Set.Ioi t) :=
        (expMeasure_real_Ioi_eq_exp_neg_mul hr ht_nonneg).symm
      _ ≤ (ProbabilityTheory.expMeasure r).real {x : ℝ | t ≤ |x|} :=
        MeasureTheory.measureReal_mono hsubset
  exact htail_lower

/-- Exact upper-tail mass of the Pareto distribution, computed from its
density.  For `x` beyond the scale, `P{Y ≥ x} = t^r x^{-r}`. -/
theorem paretoMeasure_real_Ici_eq_mul_rpow_neg
    {t r x : ℝ} (ht : 0 < t) (hr : 0 < r) (hx : t ≤ x) :
    (ProbabilityTheory.paretoMeasure t r).real (Set.Ici x) =
      t ^ r * x ^ (-r) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.paretoMeasure t r) :=
    ProbabilityTheory.isProbabilityMeasure_paretoMeasure ht hr
  have hxpos : 0 < x := ht.trans_le hx
  let f : ℝ → ℝ := fun y => r * t ^ r * y ^ (-(r + 1))
  have hset :
      (∫⁻ y in Set.Ici x, ProbabilityTheory.paretoPDF t r y) =
        ∫⁻ y in Set.Ici x, ENNReal.ofReal (f y) := by
    refine setLIntegral_congr_fun measurableSet_Ici ?_
    intro y hy
    exact ProbabilityTheory.paretoPDF_of_le (hx.trans hy)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ici x)] f := by
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ici]
    filter_upwards with y hy
    dsimp [f]
    positivity [ht.trans_le (hx.trans hy)]
  have hint : IntegrableOn f (Set.Ici x) := by
    dsimp [f]
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (c := x)
      (a := -(r + 1)) (by linarith) hxpos).const_mul (r * t ^ r)
  have hlintegral :
      ENNReal.ofReal (∫ y in Set.Ici x, f y) =
        ∫⁻ y in Set.Ici x, ENNReal.ofReal (f y) :=
    ofReal_integral_eq_lintegral_ofReal hint hnonneg
  have hIntegral :
      ∫ y in Set.Ici x, f y = t ^ r * x ^ (-r) := by
    calc
      ∫ y in Set.Ici x, f y
          = ∫ y in Set.Ici x, r * t ^ r * y ^ (-(r + 1)) := rfl
      _ = r * t ^ r * ∫ y in Set.Ici x, y ^ (-(r + 1)) := by
        rw [integral_const_mul]
      _ = r * t ^ r * ∫ y in Set.Ioi x, y ^ (-(r + 1)) := by
        rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
      _ = r * t ^ r * (-x ^ (-(r + 1) + 1) / (-(r + 1) + 1)) := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hxpos]
      _ = t ^ r * x ^ (-r) := by
        field_simp [hr.ne']
        ring_nf
  have htail_nonneg : 0 ≤ t ^ r * x ^ (-r) := by
    positivity
  rw [ProbabilityTheory.paretoMeasure, measureReal_def,
    withDensity_apply _ measurableSet_Ici, hset, ← hlintegral, hIntegral,
    ENNReal.toReal_ofReal htail_nonneg]

/-- HDP Exercise 2.5.9, Pareto example: a Pareto random variable with positive
scale and shape is not sub-gaussian. -/
theorem not_isSubGaussian_id_paretoMeasure
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ¬ IsSubGaussian (fun x : ℝ => x) (ProbabilityTheory.paretoMeasure t r) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.paretoMeasure t r) :=
    ProbabilityTheory.isProbabilityMeasure_paretoMeasure ht hr
  refine not_isSubGaussian_of_arbitrarily_large_exp_tail_lower_one
    (μ := ProbabilityTheory.paretoMeasure t r) (X := fun x : ℝ => x)
    (r := 1) (by norm_num) ?_
  intro T
  have hscale_pos : 0 < t ^ r := Real.rpow_pos_of_pos ht r
  have hsmall :=
    (isLittleO_exp_neg_mul_rpow_atTop (a := 1) (by norm_num) (-r)).def
      hscale_pos
  have hevent :
      ∀ᶠ x : ℝ in atTop,
        Real.exp (-(1 * x)) ≤ t ^ r * x ^ (-r) := by
    filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hx hx_nonneg
    have hexp_nonneg : 0 ≤ Real.exp (-(1 * x)) := (Real.exp_pos _).le
    have hrpow_nonneg : 0 ≤ x ^ (-r) := Real.rpow_nonneg hx_nonneg (-r)
    simpa [Real.norm_eq_abs, abs_of_nonneg hexp_nonneg,
      abs_of_nonneg hrpow_nonneg, one_mul] using hx
  have hlarge :
      ∀ᶠ x : ℝ in atTop, max (max T t) 0 ≤ x :=
    eventually_ge_atTop (max (max T t) 0)
  rcases (hevent.and hlarge).exists with ⟨x, hx_tail, hx_large⟩
  have hx_ge_T : T ≤ x := (le_max_left T t).trans
    ((le_max_left (max T t) 0).trans hx_large)
  have hx_ge_t : t ≤ x := (le_max_right T t).trans
    ((le_max_left (max T t) 0).trans hx_large)
  have hx_nonneg : 0 ≤ x := (le_max_right (max T t) 0).trans hx_large
  refine ⟨x, hx_ge_T, ?_⟩
  have htail_exact :
      (ProbabilityTheory.paretoMeasure t r).real (Set.Ici x) =
        t ^ r * x ^ (-r) :=
    paretoMeasure_real_Ici_eq_mul_rpow_neg ht hr hx_ge_t
  have hsubset : Set.Ici x ⊆ {y : ℝ | x ≤ |y|} := by
    intro y hy
    have hy_nonneg : 0 ≤ y := hx_nonneg.trans hy
    simpa [abs_of_nonneg hy_nonneg] using hy
  calc
    Real.exp (-(1 * x)) ≤ t ^ r * x ^ (-r) := hx_tail
    _ = (ProbabilityTheory.paretoMeasure t r).real (Set.Ici x) :=
      htail_exact.symm
    _ ≤ (ProbabilityTheory.paretoMeasure t r).real {y : ℝ | x ≤ |y|} :=
      MeasureTheory.measureReal_mono hsubset

/-- A pointwise lower bound for the Cauchy density on the unit interval
`[x, x + 1]` once `x` dominates the location and scale parameters. -/
lemma cauchyPDFReal_lower_on_Icc
    {x₀ x y : ℝ} {γ : ℝ≥0} (hγ : 0 < γ)
    (hx1 : 1 ≤ x) (hx₀ : |x₀| ≤ x) (hγx : (γ : ℝ) ≤ x)
    (hy : y ∈ Set.Icc x (x + 1)) :
    (Real.pi⁻¹ * (γ : ℝ)) * (10 * x ^ 2)⁻¹ ≤
      ProbabilityTheory.cauchyPDFReal x₀ γ y := by
  let G : ℝ := γ
  have hG_pos : 0 < G := by exact_mod_cast hγ
  have hx_nonneg : 0 ≤ x := by linarith
  have hx_pos : 0 < x := by linarith
  have h3x_nonneg : 0 ≤ 3 * x := by positivity
  have hx₀_upper : x₀ ≤ x := (le_abs_self x₀).trans hx₀
  have hy_minus_nonneg : 0 ≤ y - x₀ := by linarith [hy.1, hx₀_upper]
  have hy_minus_upper : y - x₀ ≤ 3 * x := by
    have hneg_x₀_abs : -x₀ ≤ |x₀| := neg_le_abs x₀
    linarith [hy.2, hx₀, hx1, hneg_x₀_abs]
  have habs : |y - x₀| ≤ 3 * x := by
    rw [abs_of_nonneg hy_minus_nonneg]
    exact hy_minus_upper
  have hsquare : (y - x₀) ^ 2 ≤ (3 * x) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg h3x_nonneg] using habs
  have hG_nonneg : 0 ≤ G := hG_pos.le
  have hG_sq_le : G ^ 2 ≤ x ^ 2 :=
    (sq_le_sq₀ hG_nonneg hx_nonneg).mpr hγx
  have hden_le : (y - x₀) ^ 2 + G ^ 2 ≤ 10 * x ^ 2 := by
    nlinarith
  have hden_pos : 0 < (y - x₀) ^ 2 + G ^ 2 := by
    nlinarith [sq_nonneg (y - x₀), sq_pos_of_pos hG_pos]
  have hten_pos : 0 < 10 * x ^ 2 := by positivity
  have hinv : (10 * x ^ 2)⁻¹ ≤ ((y - x₀) ^ 2 + G ^ 2)⁻¹ :=
    (inv_le_inv₀ hten_pos hden_pos).mpr hden_le
  have hcoeff_nonneg : 0 ≤ Real.pi⁻¹ * G := by positivity
  calc
    (Real.pi⁻¹ * (γ : ℝ)) * (10 * x ^ 2)⁻¹
        = (Real.pi⁻¹ * G) * (10 * x ^ 2)⁻¹ := rfl
    _ ≤ (Real.pi⁻¹ * G) * (((y - x₀) ^ 2 + G ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hinv hcoeff_nonneg
    _ = ProbabilityTheory.cauchyPDFReal x₀ γ y := by
      rw [ProbabilityTheory.cauchyPDFReal_def]

/-- Real mass of a Cauchy interval as the integral of its real density. -/
theorem cauchyMeasure_real_Icc_eq_integral
    {x₀ : ℝ} {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) :
    (ProbabilityTheory.cauchyMeasure x₀ γ).real (Set.Icc x (x + 1)) =
      ∫ y in Set.Icc x (x + 1),
        ProbabilityTheory.cauchyPDFReal x₀ γ y ∂volume := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc x (x + 1))]
      ProbabilityTheory.cauchyPDFReal x₀ γ := by
    filter_upwards with y
    exact (ProbabilityTheory.cauchyPDF_pos x₀ hγ y).le
  have hint : IntegrableOn (ProbabilityTheory.cauchyPDFReal x₀ γ)
      (Set.Icc x (x + 1)) volume :=
    (ProbabilityTheory.integrable_cauchyPDFReal x₀).integrableOn
  have hlintegral :
      ENNReal.ofReal (∫ y in Set.Icc x (x + 1),
        ProbabilityTheory.cauchyPDFReal x₀ γ y ∂volume) =
        ∫⁻ y in Set.Icc x (x + 1),
          ENNReal.ofReal (ProbabilityTheory.cauchyPDFReal x₀ γ y) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hint hnonneg
  have hintegral_nonneg :
      0 ≤ ∫ y in Set.Icc x (x + 1),
        ProbabilityTheory.cauchyPDFReal x₀ γ y ∂volume :=
    integral_nonneg_of_ae hnonneg
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero x₀ hγ, measureReal_def,
    withDensity_apply _ measurableSet_Icc]
  change (∫⁻ y in Set.Icc x (x + 1),
          ENNReal.ofReal (ProbabilityTheory.cauchyPDFReal x₀ γ y) ∂volume).toReal =
        ∫ y in Set.Icc x (x + 1),
          ProbabilityTheory.cauchyPDFReal x₀ γ y ∂volume
  rw [← hlintegral, ENNReal.toReal_ofReal hintegral_nonneg]

/-- A polynomial lower bound for the positive Cauchy tail over `[x, x + 1]`. -/
theorem cauchyMeasure_real_Icc_lower
    {x₀ x : ℝ} {γ : ℝ≥0} (hγ : 0 < γ)
    (hx1 : 1 ≤ x) (hx₀ : |x₀| ≤ x) (hγx : (γ : ℝ) ≤ x) :
    (Real.pi⁻¹ * (γ : ℝ)) * (10 * x ^ 2)⁻¹ ≤
      (ProbabilityTheory.cauchyMeasure x₀ γ).real (Set.Icc x (x + 1)) := by
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ
  rw [cauchyMeasure_real_Icc_eq_integral hγ_ne x]
  have hconst_int :
      IntegrableOn
        (fun _ : ℝ => (Real.pi⁻¹ * (γ : ℝ)) * (10 * x ^ 2)⁻¹)
        (Set.Icc x (x + 1)) volume :=
    integrableOn_const (μ := volume) (s := Set.Icc x (x + 1))
      (hs := by simp [Real.volume_Icc])
  have hpdf_int : IntegrableOn (ProbabilityTheory.cauchyPDFReal x₀ γ)
      (Set.Icc x (x + 1)) volume :=
    (ProbabilityTheory.integrable_cauchyPDFReal x₀).integrableOn
  calc
    (Real.pi⁻¹ * (γ : ℝ)) * (10 * x ^ 2)⁻¹
        = ∫ y in Set.Icc x (x + 1),
            ((Real.pi⁻¹ * (γ : ℝ)) * (10 * x ^ 2)⁻¹ : ℝ) ∂volume := by
          rw [integral_const]
          rw [measureReal_def]
          simp [Real.volume_Icc]
    _ ≤ ∫ y in Set.Icc x (x + 1),
          ProbabilityTheory.cauchyPDFReal x₀ γ y ∂volume :=
      setIntegral_mono_on hconst_int hpdf_int measurableSet_Icc
        (fun y hy => cauchyPDFReal_lower_on_Icc hγ hx1 hx₀ hγx hy)

lemma cauchy_interval_lower_eq_rpow {G x : ℝ} (hx : 0 ≤ x) :
    (Real.pi⁻¹ * G) * (10 * x ^ 2)⁻¹ =
      (Real.pi⁻¹ * G / 10) * x ^ (-2 : ℝ) := by
  rw [Real.rpow_neg hx]
  norm_num
  ring

/-- HDP Exercise 2.5.9, Cauchy example: every nondegenerate Cauchy law is not
sub-gaussian. -/
theorem not_isSubGaussian_id_cauchyMeasure
    {x₀ : ℝ} {γ : ℝ≥0} (hγ : 0 < γ) :
    ¬ IsSubGaussian (fun x : ℝ => x) (ProbabilityTheory.cauchyMeasure x₀ γ) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.cauchyMeasure x₀ γ) := inferInstance
  refine not_isSubGaussian_of_arbitrarily_large_exp_tail_lower_one
    (μ := ProbabilityTheory.cauchyMeasure x₀ γ) (X := fun x : ℝ => x)
    (r := 1) (by norm_num) ?_
  intro T
  let G : ℝ := γ
  have hG_pos : 0 < G := by exact_mod_cast hγ
  let C : ℝ := Real.pi⁻¹ * G / 10
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hsmall :=
    (isLittleO_exp_neg_mul_rpow_atTop (a := 1) (by norm_num) (-2 : ℝ)).def
      hC_pos
  have hevent :
      ∀ᶠ x : ℝ in atTop,
        Real.exp (-(1 * x)) ≤ (Real.pi⁻¹ * G) * (10 * x ^ 2)⁻¹ := by
    filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hxsmall hx_nonneg
    have hexp_nonneg : 0 ≤ Real.exp (-(1 * x)) := (Real.exp_pos _).le
    have hrpow_nonneg : 0 ≤ x ^ (-2 : ℝ) :=
      Real.rpow_nonneg hx_nonneg (-2 : ℝ)
    have hxsmall' :
        Real.exp (-(1 * x)) ≤ C * x ^ (-2 : ℝ) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hexp_nonneg,
        abs_of_nonneg hrpow_nonneg, abs_of_nonneg hx_nonneg, C] using hxsmall
    calc
      Real.exp (-(1 * x)) ≤ C * x ^ (-2 : ℝ) := hxsmall'
      _ = (Real.pi⁻¹ * G) * (10 * x ^ 2)⁻¹ := by
        rw [cauchy_interval_lower_eq_rpow hx_nonneg]
  have hlarge :
      ∀ᶠ x : ℝ in atTop, max (max (max T 1) |x₀|) G ≤ x :=
    eventually_ge_atTop (max (max (max T 1) |x₀|) G)
  rcases (hevent.and hlarge).exists with ⟨x, hx_tail, hx_large⟩
  have hx_ge_T : T ≤ x := (le_max_left T 1).trans
    ((le_max_left (max T 1) |x₀|).trans
      ((le_max_left (max (max T 1) |x₀|) G).trans hx_large))
  have hx_ge_one : 1 ≤ x := (le_max_right T 1).trans
    ((le_max_left (max T 1) |x₀|).trans
      ((le_max_left (max (max T 1) |x₀|) G).trans hx_large))
  have hx_ge_x₀ : |x₀| ≤ x := (le_max_right (max T 1) |x₀|).trans
    ((le_max_left (max (max T 1) |x₀|) G).trans hx_large)
  have hx_ge_G : G ≤ x := (le_max_right (max (max T 1) |x₀|) G).trans hx_large
  have hx_nonneg : 0 ≤ x := by linarith
  refine ⟨x, hx_ge_T, ?_⟩
  have hinterval_lower :
      (Real.pi⁻¹ * (γ : ℝ)) * (10 * x ^ 2)⁻¹ ≤
        (ProbabilityTheory.cauchyMeasure x₀ γ).real (Set.Icc x (x + 1)) :=
    cauchyMeasure_real_Icc_lower hγ hx_ge_one hx_ge_x₀ hx_ge_G
  have hsubset : Set.Icc x (x + 1) ⊆ {y : ℝ | x ≤ |y|} := by
    intro y hy
    have hy_nonneg : 0 ≤ y := hx_nonneg.trans hy.1
    simpa [abs_of_nonneg hy_nonneg] using hy.1
  calc
    Real.exp (-(1 * x)) ≤ (Real.pi⁻¹ * G) * (10 * x ^ 2)⁻¹ := hx_tail
    _ = (Real.pi⁻¹ * (γ : ℝ)) * (10 * x ^ 2)⁻¹ := rfl
    _ ≤ (ProbabilityTheory.cauchyMeasure x₀ γ).real (Set.Icc x (x + 1)) :=
      hinterval_lower
    _ ≤ (ProbabilityTheory.cauchyMeasure x₀ γ).real {y : ℝ | x ≤ |y|} :=
      MeasureTheory.measureReal_mono hsubset

end NegativeExamples

section StandardNormal

/-- A centered real Gaussian with variance proxy `v` satisfies the exact
sub-gaussian MGF bound with proxy `v`. -/
theorem hasSubgaussianMGF_id_centeredGaussian (v : ℝ≥0) :
    HasSubgaussianMGF id v (ProbabilityTheory.gaussianReal 0 v) := by
  refine ⟨?_, ?_⟩
  · intro theta
    simpa using
      (ProbabilityTheory.integrable_exp_mul_gaussianReal
        (μ := 0) (v := v) theta)
  · intro theta
    rw [ProbabilityTheory.mgf_id_gaussianReal]
    simp

/-- HDP (2.12): the MGF of a standard normal random variable is
`E exp(λX) = exp(λ²/2)`.  The random variable is the identity on the standard
normal probability space. -/
theorem standardNormal_mgf_eq (theta : ℝ) :
    mgf id standardNormalMeasure theta = Real.exp (theta ^ 2 / 2) := by
  rw [standardNormalMeasure, ProbabilityTheory.mgf_id_gaussianReal]
  norm_num

/-- The standard normal has sub-gaussian MGF proxy `1`. -/
theorem hasSubgaussianMGF_id_standardNormal :
    HasSubgaussianMGF id 1 standardNormalMeasure := by
  simpa [standardNormalMeasure] using
    hasSubgaussianMGF_id_centeredGaussian (1 : ℝ≥0)

/-- HDP Example 2.5.8(a), MGF form: the standard normal is sub-gaussian in
the book's MGF convention with scale `1`. -/
theorem standardNormal_subGaussianMGFCondition :
    subGaussianMGFCondition id standardNormalMeasure 1 := by
  exact
    subGaussianMGFCondition_of_hasSubgaussianMGF
      (μ := standardNormalMeasure) (X := id) (K := 1) (by norm_num)
      (by simpa [subgaussianProxy] using hasSubgaussianMGF_id_standardNormal)

/-- The standard normal has mean zero. -/
theorem standardNormal_mean_eq_zero :
    ∫ x, x ∂standardNormalMeasure = 0 := by
  simp [standardNormalMeasure]

/-- The standard normal has variance one. -/
theorem standardNormal_variance_eq_one :
    Var[id; standardNormalMeasure] = 1 := by
  simp [standardNormalMeasure]

/-- Exercise 2.5.1, finite-moment part: all finite `L^p` moments of the
standard normal are finite. -/
theorem standardNormal_memLp_id (p : ℝ≥0) :
    MemLp id (p : ℝ≥0∞) standardNormalMeasure := by
  simpa [standardNormalMeasure] using
    (ProbabilityTheory.memLp_id_gaussianReal
      (μ := 0) (v := (1 : ℝ≥0)) p)

/-- The gamma-integral normalization behind Exercise 2.5.1. -/
lemma standardNormal_absoluteMoment_gamma_normalization (p G : ℝ) :
    2 * standardNormalConstant *
        ((1 / 2 : ℝ) ^ (-(p + 1) / 2) * (1 / 2 : ℝ) * G) =
      2 ^ (p / 2) * G / Real.Gamma (1 / 2) := by
  rw [standardNormalConstant, Real.Gamma_one_half_eq]
  have hsqrt2 : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
  have hsqrt2π :
      Real.sqrt (2 * Real.pi) =
        (2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hsqrt2]
  rw [hsqrt2π]
  have hhalf :
      (1 / 2 : ℝ) ^ (-(p + 1) / 2) =
        (2 : ℝ) ^ ((p + 1) / 2) := by
    have hexp : (-(p + 1) / 2 : ℝ) = -((p + 1) / 2) := by ring
    rw [hexp, Real.rpow_neg_eq_inv_rpow]
    norm_num
  rw [hhalf]
  have htwo :
      (2 : ℝ) ^ ((p + 1) / 2) / (2 : ℝ) ^ (1 / 2 : ℝ) =
        2 ^ (p / 2) := by
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hnonzero : (2 : ℝ) ^ (1 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne'
  rw [← htwo]
  field_simp [hnonzero, Real.sqrt_pos.2 Real.pi_pos]

/-- Exercise 2.5.1, exact standard-normal absolute moment:
`E |X|^p = 2^(p/2) Γ((p+1)/2) / Γ(1/2)` for `p > -1`.
The book uses this for `p ≥ 1`. -/
theorem standardNormal_absoluteMoment_eq_gamma {p : ℝ} (hp : -1 < p) :
    absoluteMoment id standardNormalMeasure p =
      2 ^ (p / 2) * Real.Gamma ((p + 1) / 2) / Real.Gamma (1 / 2) := by
  rw [absoluteMoment]
  have hgauss :
      ∫ x, |id x| ^ p ∂standardNormalMeasure =
        ∫ x, ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x * |x| ^ p := by
    rw [standardNormalMeasure,
      ProbabilityTheory.integral_gaussianReal_eq_integral_smul
        (by norm_num : (1 : ℝ≥0) ≠ 0)]
    simp [smul_eq_mul]
  rw [hgauss]
  let f : ℝ → ℝ :=
    fun y => standardNormalConstant * y ^ p * Real.exp (-(y ^ 2) / 2)
  have hfg :
      (fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x * |x| ^ p)
        = fun x => f |x| := by
    funext x
    dsimp [f, standardNormalConstant]
    rw [ProbabilityTheory.gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [sq_abs]
    ring_nf
  rw [hfg, integral_comp_abs]
  have hgamma :=
    integral_rpow_mul_exp_neg_mul_rpow
      (p := (2 : ℝ)) (q := p) (b := (1 / 2 : ℝ))
      (by norm_num) hp (by norm_num)
  have hset :
      ∫ x in Set.Ioi (0 : ℝ), f x =
        standardNormalConstant *
          ∫ x in Set.Ioi (0 : ℝ), x ^ p * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ)) := by
    dsimp [f]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    simp
    ring_nf
  rw [hset, hgamma]
  simpa [mul_assoc] using
    standardNormal_absoluteMoment_gamma_normalization
      p (Real.Gamma ((p + 1) / 2))

/-- Exercise 2.5.1, displayed `L^p`-norm formula for the standard normal,
written as the `p`th root of the absolute moment. -/
theorem standardNormal_realLpNorm_eq_gamma {p : ℝ} (hp : 0 < p) :
    (absoluteMoment id standardNormalMeasure p) ^ (1 / p) =
      Real.sqrt 2 *
        (Real.Gamma ((p + 1) / 2) / Real.Gamma (1 / 2)) ^ (1 / p) := by
  have hmom :=
    standardNormal_absoluteMoment_eq_gamma (p := p) (by linarith : -1 < p)
  rw [hmom]
  let R : ℝ := Real.Gamma ((p + 1) / 2) / Real.Gamma (1 / 2)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have h2_nonneg : 0 ≤ (2 : ℝ) ^ (p / 2) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
  have hrewrite :
      2 ^ (p / 2) * Real.Gamma ((p + 1) / 2) / Real.Gamma (1 / 2) =
        2 ^ (p / 2) * R := by
    dsimp [R]
    ring
  rw [hrewrite, Real.mul_rpow h2_nonneg hR_nonneg]
  have hpow :
      ((2 : ℝ) ^ (p / 2)) ^ (1 / p) = Real.sqrt 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hpne : p ≠ 0 := ne_of_gt hp
    have hexp : p / 2 * (1 / p) = (1 / 2 : ℝ) := by
      field_simp [hpne]
    rw [hexp, Real.sqrt_eq_rpow]
  rw [hpow]

/-- Exercise 2.5.5(a), finite side: for `X ~ N(0,1)`,
`E exp(θ² X²)` is finite when `θ² < 1/2`. -/
theorem standardNormal_integrable_exp_sq_mul_of_sq_lt_half {theta : ℝ}
    (hθ : theta ^ 2 < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (theta ^ 2 * x ^ 2)) standardNormalMeasure := by
  have hstd :
      standardNormalMeasure =
        volume.withDensity (ProbabilityTheory.gaussianPDF 0 (1 : ℝ≥0)) := by
    rw [standardNormalMeasure, ProbabilityTheory.gaussianReal_of_var_ne_zero]
    norm_num
  rw [hstd]
  rw [integrable_withDensity_iff
    (ProbabilityTheory.measurable_gaussianPDF 0 (1 : ℝ≥0))
    (ae_of_all _ fun _ => ProbabilityTheory.gaussianPDF_lt_top)]
  have hb : 0 < (1 / 2 : ℝ) - theta ^ 2 := by linarith
  have hbase :
      Integrable (fun x : ℝ => Real.exp (-((1 / 2 : ℝ) - theta ^ 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hconst :
      Integrable (fun x : ℝ =>
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-((1 / 2 : ℝ) - theta ^ 2) * x ^ 2)) :=
    hbase.const_mul _
  refine hconst.congr ?_
  filter_upwards with x
  rw [ProbabilityTheory.toReal_gaussianPDF, ProbabilityTheory.gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-((1 / 2 : ℝ) - theta ^ 2) * x ^ 2)
        = (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.exp (theta ^ 2 * x ^ 2) * Real.exp (-(x ^ 2) / 2)) := by
      congr 1
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (theta ^ 2 * x ^ 2) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) := by
      ring_nf

/-- Exercise 2.5.5(a), divergent side: for `X ~ N(0,1)`,
`E exp(θ² X²)` is not finite when `θ² ≥ 1/2`. -/
theorem standardNormal_not_integrable_exp_sq_mul_of_half_le_sq {theta : ℝ}
    (hθ : 1 / 2 ≤ theta ^ 2) :
    ¬ Integrable (fun x : ℝ => Real.exp (theta ^ 2 * x ^ 2)) standardNormalMeasure := by
  intro hInt
  have hstd :
      standardNormalMeasure =
        volume.withDensity (ProbabilityTheory.gaussianPDF 0 (1 : ℝ≥0)) := by
    rw [standardNormalMeasure, ProbabilityTheory.gaussianReal_of_var_ne_zero]
    norm_num
  rw [hstd] at hInt
  rw [integrable_withDensity_iff
    (ProbabilityTheory.measurable_gaussianPDF 0 (1 : ℝ≥0))
    (ae_of_all _ fun _ => ProbabilityTheory.gaussianPDF_lt_top)] at hInt
  let b : ℝ := (1 / 2 : ℝ) - theta ^ 2
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hc_ne : c ≠ 0 := by
    dsimp [c]
    positivity
  have hprod :
      (fun x : ℝ =>
          Real.exp (theta ^ 2 * x ^ 2) *
            (ProbabilityTheory.gaussianPDF 0 (1 : ℝ≥0) x).toReal)
        =ᵐ[volume]
      (fun x : ℝ => c * Real.exp (-b * x ^ 2)) := by
    filter_upwards with x
    rw [ProbabilityTheory.toReal_gaussianPDF, ProbabilityTheory.gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    calc
      Real.exp (theta ^ 2 * x ^ 2) *
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2))
          = c * (Real.exp (theta ^ 2 * x ^ 2) * Real.exp (-(x ^ 2) / 2)) := by
        dsimp [c]
        ring_nf
      _ = c * Real.exp (-b * x ^ 2) := by
        congr 1
        rw [← Real.exp_add]
        congr 1
        dsimp [b]
        ring
  have hb_nonpos : ¬ 0 < b := by
    dsimp [b]
    linarith
  have hbad : ¬ Integrable (fun x : ℝ => c * Real.exp (-b * x ^ 2)) := by
    intro hcint
    have hc_unit : IsUnit c := isUnit_iff_ne_zero.mpr hc_ne
    have hbase : Integrable (fun x : ℝ => Real.exp (-b * x ^ 2)) := by
      exact
        (integrable_const_mul_iff hc_unit
          (fun x : ℝ => Real.exp (-b * x ^ 2))).mp hcint
    exact hb_nonpos (integrable_exp_neg_mul_sq_iff.mp hbase)
  exact hbad (hInt.congr hprod)

/-- Exercise 2.5.5(a), exact finiteness threshold for the standard normal:
`E exp(θ²X²)` is finite iff `θ² < 1/2`. -/
theorem standardNormal_integrable_exp_sq_mul_iff (theta : ℝ) :
    Integrable (fun x : ℝ => Real.exp (theta ^ 2 * x ^ 2)) standardNormalMeasure
      ↔ theta ^ 2 < 1 / 2 := by
  constructor
  · intro hInt
    by_contra hnot
    exact
      standardNormal_not_integrable_exp_sq_mul_of_half_le_sq
        (theta := theta) (not_lt.mp hnot) hInt
  · exact standardNormal_integrable_exp_sq_mul_of_sq_lt_half

/-- The exact square-exponential value used for the standard-normal Orlicz
example: `E exp(X²/4) = sqrt 2`. -/
theorem standardNormal_integral_exp_sq_div_four :
    ∫ x : ℝ, Real.exp (id x ^ 2 / (2 : ℝ) ^ 2) ∂standardNormalMeasure =
      Real.sqrt 2 := by
  have hgauss :
      ∫ x : ℝ, Real.exp (id x ^ 2 / (2 : ℝ) ^ 2) ∂standardNormalMeasure =
        ∫ x : ℝ,
          ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x *
            Real.exp (x ^ 2 / 4) := by
    rw [standardNormalMeasure,
      ProbabilityTheory.integral_gaussianReal_eq_integral_smul
        (by norm_num : (1 : ℝ≥0) ≠ 0)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [smul_eq_mul, id_eq]
    congr 1
    ring_nf
  rw [hgauss]
  have hconst :
      (∫ x : ℝ,
          ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x *
            Real.exp (x ^ 2 / 4))
        =
      standardNormalConstant *
        ∫ x : ℝ, Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [ProbabilityTheory.gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero, standardNormalConstant]
    calc
      (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) * Real.exp (x ^ 2 / 4)
          = (√(2 * Real.pi))⁻¹ *
              (Real.exp (-(x ^ 2) / 2) * Real.exp (x ^ 2 / 4)) := by ring_nf
      _ = (√(2 * Real.pi))⁻¹ * Real.exp (-(1 / 4) * x ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
  rw [hconst, integral_gaussian (1 / 4)]
  have hsqrt_pi_div :
      Real.sqrt (Real.pi / (1 / 4 : ℝ)) = 2 * Real.sqrt Real.pi := by
    have hpi_nonneg : 0 ≤ Real.pi := Real.pi_pos.le
    calc
      Real.sqrt (Real.pi / (1 / 4 : ℝ))
          = Real.sqrt (4 * Real.pi) := by norm_num [div_eq_mul_inv, mul_comm]
      _ = Real.sqrt 4 * Real.sqrt Real.pi := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) Real.pi]
      _ = 2 * Real.sqrt Real.pi := by norm_num
  have hsqrt_two_pi :
      Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Real.pi]
  rw [standardNormalConstant, hsqrt_pi_div, hsqrt_two_pi]
  field_simp [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2),
    Real.sqrt_pos.2 Real.pi_pos]
  exact (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm

/-- HDP Example 2.5.8(a), Orlicz form: a standard normal random variable has
`ψ₂` scale at most `2`. -/
theorem standardNormal_subGaussianOrliczCondition :
    subGaussianOrliczCondition id standardNormalMeasure 2 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · have hint :=
      standardNormal_integrable_exp_sq_mul_of_sq_lt_half
        (theta := (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) ^ 2 < 1 / 2)
    simpa [id_eq, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using hint
  · calc
      ∫ x : ℝ, Real.exp (id x ^ 2 / (2 : ℝ) ^ 2) ∂standardNormalMeasure
          = Real.sqrt 2 := standardNormal_integral_exp_sq_div_four
      _ ≤ 2 := by
        have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith [sq_nonneg (Real.sqrt 2), hsq]

/-- HDP Example 2.5.8(a), `ψ₂`-norm form: the standard normal has
`ψ₂` norm at most `2`. -/
theorem standardNormal_subGaussianNorm_le :
    subGaussianNorm id standardNormalMeasure ≤ 2 :=
  subGaussianNorm_le_of_subGaussianOrliczCondition
    standardNormal_subGaussianOrliczCondition

end StandardNormal

section Tails

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Two-sided tail bound obtained from the centered MGF definition. This is
the MGF-based part of HDP Proposition 2.5.2, specialized to the constants
carried by mathlib's `HasSubgaussianMGF` predicate. -/
theorem hasSubgaussianMGF_measure_abs_ge_le
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|}
      ≤ 2 * Real.exp (-(t ^ 2) / (2 * (c : ℝ))) := by
  let A : Set Ω := {ω | t ≤ X ω}
  let B : Set Ω := {ω | t ≤ -X ω}
  have hsubset : {ω | t ≤ |X ω|} ⊆ A ∪ B := by
    intro ω hω
    by_cases hx : 0 ≤ X ω
    · exact Or.inl (by simpa [A, abs_of_nonneg hx] using hω)
    · have hxneg : X ω < 0 := lt_of_not_ge hx
      exact Or.inr (by simpa [B, abs_of_neg hxneg] using hω)
  have hupper :
      μ.real A ≤ Real.exp (-(t ^ 2) / (2 * (c : ℝ))) := by
    simpa [A] using hX.measure_ge_le ht
  have hlower :
      μ.real B ≤ Real.exp (-(t ^ 2) / (2 * (c : ℝ))) := by
    simpa [B, Pi.neg_apply] using hX.neg.measure_ge_le ht
  calc
    μ.real {ω | t ≤ |X ω|} ≤ μ.real (A ∪ B) :=
      MeasureTheory.measureReal_mono hsubset
    _ ≤ μ.real A + μ.real B :=
      MeasureTheory.measureReal_union_le A B
    _ ≤ Real.exp (-(t ^ 2) / (2 * (c : ℝ)))
        + Real.exp (-(t ^ 2) / (2 * (c : ℝ))) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-(t ^ 2) / (2 * (c : ℝ))) := by ring

/-- HDP (2.10): the two-sided standard normal tail bound
`P {|X| ≥ t} ≤ 2 exp(-t²/2)`, for `t ≥ 0`. -/
theorem standardNormal_abs_tail_le_exp {t : ℝ} (ht : 0 ≤ t) :
    standardNormalMeasure.real {x : ℝ | t ≤ |x|}
      ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
  have htail :=
    (hasSubgaussianMGF_measure_abs_ge_le
      (X := id)
      (μ := standardNormalMeasure) hasSubgaussianMGF_id_standardNormal
      (t := t) ht)
  simpa using htail

/-- HDP Example 2.5.8(a), tail form: the standard normal satisfies the
book-facing sub-gaussian tail predicate with scale `sqrt 2`. -/
theorem standardNormal_subGaussianTailCondition :
    subGaussianTailCondition id standardNormalMeasure (Real.sqrt 2) := by
  refine ⟨Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2), ?_⟩
  intro t ht
  have htail := standardNormal_abs_tail_le_exp (t := t) ht
  simpa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using htail

/-- HDP Example 2.5.8(a), general centered Gaussian tail form:
if `X ~ N(0,v)` with `v > 0`, then `X` is sub-gaussian at tail scale
`sqrt(2v)` in the book's convention. -/
theorem centeredGaussian_subGaussianTailCondition
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) :
    subGaussianTailCondition id (ProbabilityTheory.gaussianReal 0 v)
      (Real.sqrt (2 * (v : ℝ))) := by
  refine ⟨Real.sqrt_pos.2 (mul_pos (by norm_num : (0 : ℝ) < 2) hv), ?_⟩
  intro t ht
  have htail :=
    hasSubgaussianMGF_measure_abs_ge_le
      (X := id)
      (μ := ProbabilityTheory.gaussianReal 0 v)
      (c := v)
      (hasSubgaussianMGF_id_centeredGaussian v)
      (t := t) ht
  have hsq :
      (Real.sqrt 2 * Real.sqrt (v : ℝ)) ^ 2 = 2 * (v : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt hv.le]
  simpa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (v : ℝ), hsq]
    using htail

/-- HDP Example 2.5.8(a), general centered Gaussian Orlicz form. -/
theorem centeredGaussian_subGaussianOrliczCondition
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) :
    subGaussianOrliczCondition id (ProbabilityTheory.gaussianReal 0 v)
      (2 * Real.sqrt (2 * (v : ℝ))) :=
  subGaussianOrliczCondition_of_subGaussianTailCondition
    (μ := ProbabilityTheory.gaussianReal 0 v) (X := id)
    measurable_id.aemeasurable
    (centeredGaussian_subGaussianTailCondition (v := v) hv)

/-- HDP Example 2.5.8(a), general centered Gaussian `ψ₂`-norm bound. -/
theorem centeredGaussian_subGaussianNorm_le
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) :
    subGaussianNorm id (ProbabilityTheory.gaussianReal 0 v)
      ≤ 2 * Real.sqrt (2 * (v : ℝ)) :=
  subGaussianNorm_le_of_subGaussianOrliczCondition
    (centeredGaussian_subGaussianOrliczCondition (v := v) hv)

end Tails

section Maxima

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {ι : Type*} [Fintype ι]

/-- The upper-tail event for the maximum absolute value of a finite family:
some coordinate has magnitude at least `t`. This avoids choosing an explicit
finite maximum value and is the event used in Exercise 2.5.10. -/
def finiteMaxAbsTailEvent (X : ι → Ω → ℝ) (t : ℝ) : Set Ω :=
  {ω | ∃ i, t ≤ |X i ω|}

/-- Union bound for the finite maximum absolute-value event. -/
theorem finiteMaxAbsTail_probability_le_sum
    (X : ι → Ω → ℝ) (t : ℝ) :
    μ.real (finiteMaxAbsTailEvent X t)
      ≤ ∑ i, μ.real {ω | t ≤ |X i ω|} := by
  classical
  simpa [finiteMaxAbsTailEvent] using
    (measureReal_exists_le_sum
      (μ := μ) (A := fun i : ι => {ω | t ≤ |X i ω|}))

/-- HDP Exercise 2.5.10, finite tail core: a union bound for a finite maximum
of sub-gaussian random variables, with possibly different tail scales. No
independence is required. -/
theorem finiteMaxAbsTail_subGaussian_le_sum
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K : ι → ℝ} {t : ℝ}
    (hX : ∀ i, subGaussianTailCondition (X i) μ (K i))
    (ht : 0 ≤ t) :
    μ.real (finiteMaxAbsTailEvent X t)
      ≤ ∑ i, 2 * Real.exp (-(t ^ 2) / (K i) ^ 2) := by
  classical
  calc
    μ.real (finiteMaxAbsTailEvent X t)
        ≤ ∑ i, μ.real {ω | t ≤ |X i ω|} :=
      finiteMaxAbsTail_probability_le_sum (μ := μ) X t
    _ ≤ ∑ i, 2 * Real.exp (-(t ^ 2) / (K i) ^ 2) := by
      exact Finset.sum_le_sum fun i _hi => (hX i).2 t ht

/-- Uniform-scale version of the finite maximum tail bound:
`P{maxᵢ |Xᵢ| ≥ t} ≤ n · 2 exp(-t²/K²)`. -/
theorem finiteMaxAbsTail_subGaussian_le_card_mul
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K t : ℝ}
    (hX : ∀ i, subGaussianTailCondition (X i) μ K)
    (ht : 0 ≤ t) :
    μ.real (finiteMaxAbsTailEvent X t)
      ≤ (Fintype.card ι : ℝ) *
          (2 * Real.exp (-(t ^ 2) / K ^ 2)) := by
  classical
  calc
    μ.real (finiteMaxAbsTailEvent X t)
        ≤ ∑ _i : ι, 2 * Real.exp (-(t ^ 2) / K ^ 2) :=
      finiteMaxAbsTail_subGaussian_le_sum
        (μ := μ) (X := X) (K := fun _ => K) hX ht
    _ = (Fintype.card ι : ℝ) *
          (2 * Real.exp (-(t ^ 2) / K ^ 2)) := by
      simp

section FiniteMaxValue

variable [Nonempty ι]

/-- The finite maximum `maxᵢ Xᵢ` for a nonempty finite family. -/
def finiteMax (X : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty
    (fun i => X i ω)

omit [MeasurableSpace Ω] in theorem le_finiteMax
    (X : ι → Ω → ℝ) (i : ι) (ω : Ω) :
    X i ω ≤ finiteMax X ω := by
  classical
  exact
    Finset.le_sup'
      (s := (Finset.univ : Finset ι))
      (f := fun i => X i ω)
      (Finset.mem_univ i)

omit [MeasurableSpace Ω] in theorem finiteMax_lt_iff
    (X : ι → Ω → ℝ) (ω : Ω) (t : ℝ) :
    finiteMax X ω < t ↔ ∀ i, X i ω < t := by
  classical
  rw [finiteMax, Finset.sup'_lt_iff]
  simp

/-- The upper-tail event for the ordinary finite maximum. -/
def finiteMaxTailEvent (X : ι → Ω → ℝ) (t : ℝ) : Set Ω :=
  {ω | ∃ i, t ≤ X i ω}

omit [MeasurableSpace Ω] in theorem finiteMaxTailEvent_eq_preimage
    (X : ι → Ω → ℝ) (t : ℝ) :
    finiteMaxTailEvent X t = {ω | t ≤ finiteMax X ω} := by
  classical
  ext ω
  simp [finiteMaxTailEvent, finiteMax, Finset.le_sup'_iff]

omit [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] in
theorem finiteMaxTailEvent_eq_compl_iInter_lt
    (X : ι → Ω → ℝ) (t : ℝ) :
    finiteMaxTailEvent X t = (⋂ i, {ω | X i ω < t})ᶜ := by
  classical
  ext ω
  simp [finiteMaxTailEvent, not_lt]

/-- Measurability of the ordinary finite maximum. -/
theorem measurable_finiteMax
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    Measurable (finiteMax X) := by
  classical
  let Y : Ω → ℝ :=
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i : ι => fun ω : Ω => X i ω)
  have hY : Measurable Y :=
    (Finset.measurable_sup'
      (s := (Finset.univ : Finset ι))
      (hs := Finset.univ_nonempty)
      (f := fun i ω => X i ω)
      (fun i _hi => hX i))
  have hEq : finiteMax X = Y := by
    funext ω
    simp [finiteMax, Y]
  rw [hEq]
  exact hY

/-- Independence converts the lower tail of a finite ordinary maximum into the
product of the one-dimensional lower tails. This is the probability identity
used in the Gaussian lower-bound Exercise 2.5.11. -/
theorem finiteMaxTail_probability_eq_one_sub_prod_lt
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ}
    (hindep : iIndepFun X μ)
    (hX : ∀ i, Measurable (X i)) (t : ℝ) :
    μ.real (finiteMaxTailEvent X t)
      = 1 - ∏ i, μ.real {ω | X i ω < t} := by
  classical
  let A : Set Ω := ⋂ i, {ω | X i ω < t}
  have hA_meas : MeasurableSet A := by
    dsimp [A]
    exact MeasurableSet.iInter fun i => (hX i) measurableSet_Iio
  have htail_eq : finiteMaxTailEvent X t = Aᶜ := by
    dsimp [A]
    exact finiteMaxTailEvent_eq_compl_iInter_lt X t
  have hA_measure :
      μ A = ∏ i, μ {ω | X i ω < t} := by
    dsimp [A]
    simpa using
      (hindep.meas_iInter
        (s := fun i : ι => {ω | X i ω < t})
        (fun i =>
          (show MeasurableSet[MeasurableSpace.comap (X i) inferInstance]
            {ω | X i ω < t} from
              MeasurableSpace.measurableSet_comap.2
                ⟨Set.Iio t, measurableSet_Iio, rfl⟩)))
  have hA_real :
      μ.real A = ∏ i, μ.real {ω | X i ω < t} := by
    rw [measureReal_def, hA_measure, ENNReal.toReal_prod]
    simp [measureReal_def]
  rw [htail_eq, MeasureTheory.measureReal_compl hA_meas,
    MeasureTheory.probReal_univ, hA_real]

/-- A.e. measurability of the ordinary finite maximum. -/
theorem aemeasurable_finiteMax
    {X : ι → Ω → ℝ} (hX : ∀ i, AEMeasurable (X i) μ) :
    AEMeasurable (finiteMax X) μ := by
  classical
  let Y : Ω → ℝ :=
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i : ι => fun ω : Ω => X i ω)
  have hY : AEMeasurable Y μ :=
    Finset.sup'_induction
      (s := (Finset.univ : Finset ι))
      (H := Finset.univ_nonempty)
      (f := fun i : ι => fun ω : Ω => X i ω)
      (p := fun f : Ω → ℝ => AEMeasurable f μ)
      (fun f hf g hg => hf.max hg)
      (fun i _hi => hX i)
  have hEq : finiteMax X = Y := by
    funext ω
    simp [finiteMax, Y]
  rw [hEq]
  exact hY

/-- The finite maximum `maxᵢ |Xᵢ|` for a nonempty finite family. -/
def finiteMaxAbs (X : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty
    (fun i => |X i ω|)

omit [MeasurableSpace Ω] in theorem finiteMaxAbs_nonneg (X : ι → Ω → ℝ) (ω : Ω) :
    0 ≤ finiteMaxAbs X ω := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  exact
    (abs_nonneg (X i₀ ω)).trans
      (Finset.le_sup'
        (s := (Finset.univ : Finset ι))
        (f := fun i => |X i ω|)
        (Finset.mem_univ i₀))

-- The event form used above is exactly the upper tail of `maxᵢ |Xᵢ|`.
omit [MeasurableSpace Ω] in theorem finiteMaxAbsTailEvent_eq_preimage
    (X : ι → Ω → ℝ) (t : ℝ) :
    finiteMaxAbsTailEvent X t = {ω | t ≤ finiteMaxAbs X ω} := by
  classical
  ext ω
  simp [finiteMaxAbsTailEvent, finiteMaxAbs, Finset.le_sup'_iff]

/-- Measurability of the finite maximum of absolute values. -/
theorem measurable_finiteMaxAbs
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    Measurable (finiteMaxAbs X) := by
  classical
  let Y : Ω → ℝ :=
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i : ι => fun ω : Ω => |X i ω|)
  have hY : Measurable Y :=
    (Finset.measurable_sup'
      (s := (Finset.univ : Finset ι))
      (hs := Finset.univ_nonempty)
      (f := fun i ω => |X i ω|)
      (fun i _hi => (hX i).abs))
  have hEq : finiteMaxAbs X = Y := by
    funext ω
    simp [finiteMaxAbs, Y]
  rw [hEq]
  exact hY

/-- A.e. measurability of the finite maximum of absolute values. -/
theorem aemeasurable_finiteMaxAbs
    {X : ι → Ω → ℝ} (hX : ∀ i, AEMeasurable (X i) μ) :
    AEMeasurable (finiteMaxAbs X) μ := by
  classical
  let Y : Ω → ℝ :=
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i : ι => fun ω : Ω => |X i ω|)
  have hAbs :
      ∀ i,
        AEMeasurable (fun ω => |X i ω|) μ :=
    fun i => (hX i).abs
  have hY : AEMeasurable Y μ :=
    Finset.sup'_induction
      (s := (Finset.univ : Finset ι))
      (H := Finset.univ_nonempty)
      (f := fun i : ι => fun ω : Ω => |X i ω|)
      (p := fun f : Ω → ℝ => AEMeasurable f μ)
      (fun f hf g hg => hf.max hg)
      (fun i _hi => hAbs i)
  have hEq : finiteMaxAbs X = Y := by
    funext ω
    simp [finiteMaxAbs, Y]
  rw [hEq]
  exact hY

-- Deterministic domination of the finite maximum by the sum of absolute values.
omit [MeasurableSpace Ω] in theorem finiteMaxAbs_le_sum_abs
    (X : ι → Ω → ℝ) (ω : Ω) :
    finiteMaxAbs X ω ≤ ∑ i, |X i ω| := by
  classical
  rw [finiteMaxAbs, Finset.sup'_le_iff]
  intro i hi
  exact
    Finset.single_le_sum
      (s := (Finset.univ : Finset ι))
      (f := fun i => |X i ω|)
      (fun j _hj => abs_nonneg (X j ω))
      hi

omit [MeasurableSpace Ω] in theorem finiteMax_le_finiteMaxAbs
    (X : ι → Ω → ℝ) (ω : Ω) :
    finiteMax X ω ≤ finiteMaxAbs X ω := by
  classical
  rw [finiteMax, Finset.sup'_le_iff]
  intro i hi
  exact (le_abs_self (X i ω)).trans
    (Finset.le_sup'
      (s := (Finset.univ : Finset ι))
      (f := fun i => |X i ω|)
      hi)

omit [MeasurableSpace Ω] in theorem neg_finiteMax_le_finiteMaxAbs
    (X : ι → Ω → ℝ) (ω : Ω) :
    -finiteMax X ω ≤ finiteMaxAbs X ω := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  have hmax_ge : X i₀ ω ≤ finiteMax X ω := le_finiteMax X i₀ ω
  have habs_ge : |X i₀ ω| ≤ finiteMaxAbs X ω :=
    Finset.le_sup'
      (s := (Finset.univ : Finset ι))
      (f := fun i => |X i ω|)
      (Finset.mem_univ i₀)
  have hneg : -finiteMax X ω ≤ -X i₀ ω := neg_le_neg hmax_ge
  exact hneg.trans ((neg_le_abs (X i₀ ω)).trans habs_ge)

omit [MeasurableSpace Ω] in theorem abs_finiteMax_le_finiteMaxAbs
    (X : ι → Ω → ℝ) (ω : Ω) :
    |finiteMax X ω| ≤ finiteMaxAbs X ω := by
  have hneg : -finiteMaxAbs X ω ≤ finiteMax X ω := by
    linarith [neg_finiteMax_le_finiteMaxAbs X ω]
  exact abs_le.mpr
    ⟨hneg, finiteMax_le_finiteMaxAbs X ω⟩

/-- A finite maximum of integrable real random variables is integrable. -/
theorem integrable_finiteMaxAbs_of_integrable
    {X : ι → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) μ) :
    Integrable (finiteMaxAbs X) μ := by
  classical
  have hsum :
      Integrable (fun ω => ∑ i, |X i ω|) μ := by
    simpa using
      (integrable_finset_sum
        (μ := μ) (s := (Finset.univ : Finset ι))
        (f := fun i ω => |X i ω|)
        (fun i _hi => (hX i).abs))
  refine
    hsum.mono_nonneg
      ((aemeasurable_finiteMaxAbs
        (μ := μ) (X := X) (fun i => (hX i).aemeasurable)).aestronglyMeasurable)
      ?_ ?_
  · exact Filter.Eventually.of_forall fun ω => finiteMaxAbs_nonneg X ω
  · exact Filter.Eventually.of_forall fun ω => finiteMaxAbs_le_sum_abs X ω

/-- An ordinary finite maximum of integrable real random variables is integrable. -/
theorem integrable_finiteMax_of_integrable
    {X : ι → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) μ) :
    Integrable (finiteMax X) μ := by
  classical
  have hAbs : Integrable (finiteMaxAbs X) μ :=
    integrable_finiteMaxAbs_of_integrable (μ := μ) (X := X) hX
  refine hAbs.mono ?_ ?_
  · exact
      ((aemeasurable_finiteMax
        (μ := μ) (X := X) (fun i => (hX i).aemeasurable)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (finiteMaxAbs_nonneg X ω)]
        using abs_finiteMax_le_finiteMaxAbs X ω

/-- A threshold lower bound for the expectation of a finite ordinary maximum:
if the maximum exceeds `a` on an event `A`, the only possible loss on the
complement is controlled by one coordinate's absolute first moment. -/
theorem finiteMax_integral_ge_threshold_mul_tail_sub_abs
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (i₀ : ι) (a : ℝ)
    (hXint : ∀ i, Integrable (X i) μ)
    (hA :
      MeasurableSet (finiteMaxTailEvent X a)) :
    a * μ.real (finiteMaxTailEvent X a) - ∫ ω, |X i₀ ω| ∂μ
      ≤ ∫ ω, finiteMax X ω ∂μ := by
  classical
  let A : Set Ω := finiteMaxTailEvent X a
  let L : Ω → ℝ := fun ω => A.indicator (fun _ => a) ω - |X i₀ ω|
  have hMaxInt : Integrable (finiteMax X) μ :=
    integrable_finiteMax_of_integrable (μ := μ) (X := X) hXint
  have hLInt : Integrable L μ := by
    exact (integrable_const a).indicator hA |>.sub ((hXint i₀).abs)
  have hpoint : ∀ᵐ ω ∂μ, L ω ≤ finiteMax X ω :=
    Filter.Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ A
      · have htail : a ≤ finiteMax X ω := by
          have hω' : ω ∈ finiteMaxTailEvent X a := by
            simpa [A] using hω
          rw [finiteMaxTailEvent_eq_preimage] at hω'
          exact hω'
        have hL : L ω = a - |X i₀ ω| := by
          simp [L, A, hω]
        rw [hL]
        linarith [abs_nonneg (X i₀ ω)]
      · have hcoord : -|X i₀ ω| ≤ finiteMax X ω := by
          exact (neg_abs_le (X i₀ ω)).trans (le_finiteMax X i₀ ω)
        have hL : L ω = -|X i₀ ω| := by
          simp [L, A, hω]
        simpa [hL] using hcoord
  have hmono := integral_mono_ae hLInt hMaxInt hpoint
  have hLint_eq :
      ∫ ω, L ω ∂μ =
        a * μ.real (finiteMaxTailEvent X a) - ∫ ω, |X i₀ ω| ∂μ := by
    rw [show (∫ ω, L ω ∂μ) =
        ∫ ω, A.indicator (fun _ => a) ω ∂μ -
          ∫ ω, |X i₀ ω| ∂μ by
          exact integral_sub ((integrable_const a).indicator hA) ((hXint i₀).abs)]
    rw [MeasureTheory.integral_indicator_const a hA]
    simp [smul_eq_mul, mul_comm]
  linarith

/-- The standard normal has `E |g| ≤ 1`. This coarse form is enough for the
Gaussian maximum lower-bound exercise. -/
theorem standardNormal_integral_abs_le_one :
    ∫ x : ℝ, |x| ∂standardNormalMeasure ≤ 1 := by
  have hsq :
      ∫ x : ℝ, x ^ 2 ∂standardNormalMeasure = 1 := by
    have hvar :=
      variance_eq_expectation_sq_sub_mean
        (μ := standardNormalMeasure) (X := id) measurable_id.aemeasurable
    rw [standardNormal_variance_eq_one] at hvar
    simpa [id, standardNormal_mean_eq_zero] using hvar.symm
  have hbound :=
    integral_abs_le_sqrt_integral_sq
      (μ := standardNormalMeasure) (X := id)
      (standardNormal_memLp_id 2)
  simpa [hsq] using hbound

/-- A concrete lower-bound certificate for HDP Exercise 2.5.11. For
independent standard normal coordinates, any threshold `a` gives
`E maxᵢ Xᵢ ≥ a P(maxᵢ Xᵢ ≥ a) - 1`, and the tail probability is computed by
the independence product identity. -/
theorem finiteMax_standardNormal_integral_ge_threshold
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (i₀ : ι) (a : ℝ)
    (hindep : iIndepFun X μ)
    (hXmeas : ∀ i, Measurable (X i))
    (hLaw : ∀ i, μ.map (X i) = standardNormalMeasure) :
    a * (1 - ∏ _i : ι, standardNormalMeasure.real (Set.Iio a)) - 1
      ≤ ∫ ω, finiteMax X ω ∂μ := by
  classical
  have hXint : ∀ i, Integrable (X i) μ := by
    intro i
    have hmem_map : MemLp id (1 : ℝ≥0∞) (μ.map (X i)) := by
      rw [hLaw i]
      exact (standardNormal_memLp_id 1)
    have hmem : MemLp (X i) (1 : ℝ≥0∞) μ := by
      simpa [Function.comp_def] using
        (MemLp.comp_of_map hmem_map (hXmeas i).aemeasurable)
    simpa using (memLp_one_iff_integrable.mp hmem)
  have hA :
      MeasurableSet (finiteMaxTailEvent X a) := by
    rw [finiteMaxTailEvent_eq_preimage]
    exact (measurable_finiteMax (X := X) hXmeas) measurableSet_Ici
  have hbase :=
    finiteMax_integral_ge_threshold_mul_tail_sub_abs
      (μ := μ) (X := X) i₀ a hXint hA
  have htail :
      μ.real (finiteMaxTailEvent X a)
        = 1 - ∏ i, μ.real {ω | X i ω < a} :=
    finiteMaxTail_probability_eq_one_sub_prod_lt
      (μ := μ) (X := X) hindep hXmeas a
  have hmarg : ∀ i, μ.real {ω | X i ω < a}
      = standardNormalMeasure.real (Set.Iio a) := by
    intro i
    change μ.real ((X i) ⁻¹' Set.Iio a)
      = standardNormalMeasure.real (Set.Iio a)
    rw [← MeasureTheory.map_measureReal_apply
      (μ := μ) (f := X i) (hXmeas i) measurableSet_Iio, hLaw i]
  have hprod :
      ∏ i, μ.real {ω | X i ω < a}
        = ∏ _i : ι, standardNormalMeasure.real (Set.Iio a) := by
    exact Finset.prod_congr rfl fun i _hi => hmarg i
  have habs :
      ∫ ω, |X i₀ ω| ∂μ ≤ 1 := by
    have hHasLaw : HasLaw (X i₀) standardNormalMeasure μ :=
      ⟨(hXmeas i₀).aemeasurable, hLaw i₀⟩
    have hEq :
        ∫ ω, |X i₀ ω| ∂μ =
          ∫ x : ℝ, |x| ∂standardNormalMeasure := by
      simpa [Function.comp_def] using
        (hHasLaw.integral_comp (f := fun x : ℝ => |x|) (by fun_prop))
    rw [hEq]
    exact standardNormal_integral_abs_le_one
  rw [htail, hprod] at hbase
  linarith

/-- The lower-tail product for independent standard normals is controlled by
the exponential of the upper-tail mass. This is the standard
`(1 - q)^N ≤ exp(-Nq)` step in the proof of Exercise 2.5.11. -/
theorem standardNormal_Iio_prod_le_exp_neg_card_mul_tail
    (a : ℝ) :
    ∏ _i : ι, standardNormalMeasure.real (Set.Iio a)
      ≤ Real.exp
        (-(Fintype.card ι : ℝ) *
          standardNormalMeasure.real (Set.Ici a)) := by
  classical
  let q : ℝ := standardNormalMeasure.real (Set.Ici a)
  have hlower_eq :
      standardNormalMeasure.real (Set.Iio a) = 1 - q := by
    have hcompl :=
      MeasureTheory.measureReal_compl
        (μ := standardNormalMeasure) (s := Set.Ici a) measurableSet_Ici
    rw [Set.compl_Ici, MeasureTheory.probReal_univ] at hcompl
    simpa [q] using hcompl
  have hterm :
      ∀ i : ι,
        standardNormalMeasure.real (Set.Iio a) ≤ Real.exp (-q) := by
    intro _i
    rw [hlower_eq]
    exact Real.one_sub_le_exp_neg q
  calc
    ∏ _i : ι, standardNormalMeasure.real (Set.Iio a)
        ≤ ∏ _i : ι, Real.exp (-q) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro i _hi
        exact MeasureTheory.measureReal_nonneg
      · intro i _hi
        exact hterm i
    _ = (Real.exp (-q)) ^ Fintype.card ι := by
      simp
    _ = Real.exp (-(Fintype.card ι : ℝ) * q) := by
      rw [← Real.exp_nat_mul]
      ring_nf

/-- If the total Gaussian upper-tail budget is at least `log 2`, then the
independent lower-tail product is at most `1/2`. -/
theorem standardNormal_Iio_prod_le_half_of_log_two_le_card_mul_tail
    {a : ℝ}
    (hbudget :
      Real.log 2 ≤ (Fintype.card ι : ℝ) *
        standardNormalMeasure.real (Set.Ici a)) :
    ∏ _i : ι, standardNormalMeasure.real (Set.Iio a) ≤ 1 / 2 := by
  classical
  have hprod :=
    standardNormal_Iio_prod_le_exp_neg_card_mul_tail
      (ι := ι) a
  have hexp :
      Real.exp
          (-(Fintype.card ι : ℝ) *
            standardNormalMeasure.real (Set.Ici a))
        ≤ 1 / 2 := by
    calc
      Real.exp
          (-(Fintype.card ι : ℝ) *
            standardNormalMeasure.real (Set.Ici a))
          ≤ Real.exp (-Real.log 2) := by
        exact Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  exact hprod.trans hexp

/-- Mills' lower bound supplies the `log 2` budget needed to make the
independent lower-tail product at most `1/2`. -/
theorem standardNormal_Iio_prod_le_half_of_mills_budget
    {a : ℝ} (ha : 0 < a)
    (hbudget :
      Real.log 2 ≤ (Fintype.card ι : ℝ) *
        ((1 / a - 1 / a ^ 3) * standardNormalConstant *
          Real.exp (-(a ^ 2) / 2))) :
    ∏ _i : ι, standardNormalMeasure.real (Set.Iio a) ≤ 1 / 2 := by
  classical
  have htail := mills_lower_le_standardNormal_tail (t := a) ha
  have hcard_nonneg : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  refine standardNormal_Iio_prod_le_half_of_log_two_le_card_mul_tail
    (ι := ι) (a := a) ?_
  calc
    Real.log 2
        ≤ (Fintype.card ι : ℝ) *
          ((1 / a - 1 / a ^ 3) * standardNormalConstant *
            Real.exp (-(a ^ 2) / 2)) := hbudget
    _ ≤ (Fintype.card ι : ℝ) *
          standardNormalMeasure.real (Set.Ici a) :=
      mul_le_mul_of_nonneg_left htail hcard_nonneg

/-- Exercise 2.5.11 proof-spine corollary: once the standard Mills lower bound
at threshold `sqrt(log N)/4` gives enough total tail budget, the expectation of
the maximum is bounded below by an explicit constant times `sqrt(log N)`.
The theorem `finiteMax_standardNormal_integral_ge_sqrt_log_card_of_large_card`
below discharges this budget from the elementary growth assumption
`sqrt(log N) ≥ 16`. -/
theorem finiteMax_standardNormal_integral_ge_sqrt_log_card_of_mills_budget
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (i₀ : ι)
    (hindep : iIndepFun X μ)
    (hXmeas : ∀ i, Measurable (X i))
    (hLaw : ∀ i, μ.map (X i) = standardNormalMeasure)
    (hlarge : 16 ≤ Real.sqrt (Real.log (Fintype.card ι : ℝ)))
    (hmillsBudget :
      Real.log 2 ≤ (Fintype.card ι : ℝ) *
        ((1 / ((1 / 4 : ℝ) *
            Real.sqrt (Real.log (Fintype.card ι : ℝ))) -
          1 / ((1 / 4 : ℝ) *
            Real.sqrt (Real.log (Fintype.card ι : ℝ))) ^ 3) *
          standardNormalConstant *
          Real.exp
            (-(((1 / 4 : ℝ) *
              Real.sqrt (Real.log (Fintype.card ι : ℝ))) ^ 2) / 2))) :
    (1 / 16 : ℝ) * Real.sqrt (Real.log (Fintype.card ι : ℝ))
      ≤ ∫ ω, finiteMax X ω ∂μ := by
  classical
  let s : ℝ := Real.sqrt (Real.log (Fintype.card ι : ℝ))
  let a : ℝ := (1 / 4 : ℝ) * s
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hs_large : 16 ≤ s := by
    simpa [s] using hlarge
  have ha_pos : 0 < a := by
    dsimp [a]
    nlinarith
  have hprod_half :
      ∏ _i : ι, standardNormalMeasure.real (Set.Iio a) ≤ 1 / 2 := by
    refine standardNormal_Iio_prod_le_half_of_mills_budget
      (ι := ι) (a := a) ha_pos ?_
    simpa [a, s] using hmillsBudget
  have hbase :=
    finiteMax_standardNormal_integral_ge_threshold
      (μ := μ) (X := X) i₀ a hindep hXmeas hLaw
  have hprob :
      1 / 2 ≤
        1 - ∏ _i : ι, standardNormalMeasure.real (Set.Iio a) := by
    linarith
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have hbudget :
      (1 / 16 : ℝ) * s
        ≤ a * (1 - ∏ _i : ι,
          standardNormalMeasure.real (Set.Iio a)) - 1 := by
    have hmul :
        a * (1 / 2 : ℝ)
          ≤ a * (1 - ∏ _i : ι,
            standardNormalMeasure.real (Set.Iio a)) :=
      mul_le_mul_of_nonneg_left hprob ha_nonneg
    calc
      (1 / 16 : ℝ) * s
          ≤ a * (1 / 2 : ℝ) - 1 := by
        dsimp [a]
        nlinarith
      _ ≤ a * (1 - ∏ _i : ι,
            standardNormalMeasure.real (Set.Iio a)) - 1 := by
        linarith
  exact hbudget.trans hbase

/-- The elementary growth estimate that discharges the Mills-budget hypothesis
in the proof of Exercise 2.5.11. For `s = sqrt(log N) ≥ 16` and
`a = s / 4`, the lower Mills bound contributes at least `log 2` total mass
across the `N` independent Gaussian coordinates. -/
theorem standardNormal_mills_budget_quarter_sqrt_log_card_of_large_card
    (hlarge : 16 ≤ Real.sqrt (Real.log (Fintype.card ι : ℝ))) :
    Real.log 2 ≤ (Fintype.card ι : ℝ) *
      ((1 / ((1 / 4 : ℝ) *
          Real.sqrt (Real.log (Fintype.card ι : ℝ))) -
        1 / ((1 / 4 : ℝ) *
          Real.sqrt (Real.log (Fintype.card ι : ℝ))) ^ 3) *
        standardNormalConstant *
        Real.exp
          (-(((1 / 4 : ℝ) *
            Real.sqrt (Real.log (Fintype.card ι : ℝ))) ^ 2) / 2)) := by
  classical
  let N : ℝ := Fintype.card ι
  let s : ℝ := Real.sqrt (Real.log N)
  let a : ℝ := (1 / 4 : ℝ) * s
  have hs_large : 16 ≤ s := by
    simpa [s, N] using hlarge
  have hs_pos : 0 < s := by
    nlinarith
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hlog_pos : 0 < Real.log N := by
    exact Real.sqrt_pos.mp (by simpa [s] using hs_pos)
  have hs_sq : s ^ 2 = Real.log N := by
    dsimp [s]
    exact Real.sq_sqrt hlog_pos.le
  have hcard_nat_pos : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr inferInstance
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast hcard_nat_pos
  have hcoeff :
      2 / s ≤ 1 / a - 1 / a ^ 3 := by
    have hs_sq_ge : (32 : ℝ) ≤ s ^ 2 := by
      nlinarith
    dsimp [a]
    field_simp [hs_ne]
    nlinarith
  have hNexp_eq :
      N * Real.exp (-(a ^ 2) / 2)
        = Real.exp ((31 / 32 : ℝ) * s ^ 2) := by
    calc
      N * Real.exp (-(a ^ 2) / 2)
          = Real.exp (Real.log N) * Real.exp (-(a ^ 2) / 2) := by
        rw [Real.exp_log hN_pos]
      _ = Real.exp (Real.log N + (-(a ^ 2) / 2)) := by
        rw [← Real.exp_add]
      _ = Real.exp ((31 / 32 : ℝ) * s ^ 2) := by
        congr 1
        rw [← hs_sq]
        dsimp [a]
        ring
  have hNexp_lower :
      (31 / 32 : ℝ) * s ^ 2 ≤ N * Real.exp (-(a ^ 2) / 2) := by
    rw [hNexp_eq]
    have h := Real.add_one_le_exp ((31 / 32 : ℝ) * s ^ 2)
    linarith
  have hunit_eq :
      ((31 / 32 : ℝ) * s ^ 2) * (2 / s) * (1 / 16 : ℝ)
        = (31 / 256 : ℝ) * s := by
    field_simp [hs_ne]
    ring
  have hunit :
      (1 : ℝ) ≤
        ((31 / 32 : ℝ) * s ^ 2) * (2 / s) * (1 / 16 : ℝ) := by
    rw [hunit_eq]
    nlinarith
  have htwo_div_nonneg : 0 ≤ 2 / s := by
    positivity
  have hNexp_nonneg : 0 ≤ N * Real.exp (-(a ^ 2) / 2) := by
    positivity
  have hcoeff_nonneg : 0 ≤ 1 / a - 1 / a ^ 3 :=
    htwo_div_nonneg.trans hcoeff
  have hproduct_lower :
      ((31 / 32 : ℝ) * s ^ 2) * (2 / s) * (1 / 16 : ℝ)
        ≤ (N * Real.exp (-(a ^ 2) / 2)) *
          (1 / a - 1 / a ^ 3) * standardNormalConstant := by
    calc
      ((31 / 32 : ℝ) * s ^ 2) * (2 / s) * (1 / 16 : ℝ)
          ≤ (N * Real.exp (-(a ^ 2) / 2)) *
              (2 / s) * (1 / 16 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hNexp_lower htwo_div_nonneg)
          (by norm_num)
      _ ≤ (N * Real.exp (-(a ^ 2) / 2)) *
              (1 / a - 1 / a ^ 3) * (1 / 16 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoeff hNexp_nonneg)
          (by norm_num)
      _ ≤ (N * Real.exp (-(a ^ 2) / 2)) *
              (1 / a - 1 / a ^ 3) * standardNormalConstant := by
        exact mul_le_mul_of_nonneg_left
          one_sixteenth_le_standardNormalConstant
          (mul_nonneg hNexp_nonneg hcoeff_nonneg)
  have hmain :
      (1 : ℝ) ≤ N *
        ((1 / a - 1 / a ^ 3) * standardNormalConstant *
          Real.exp (-(a ^ 2) / 2)) := by
    calc
      (1 : ℝ)
          ≤ ((31 / 32 : ℝ) * s ^ 2) * (2 / s) *
              (1 / 16 : ℝ) := hunit
      _ ≤ (N * Real.exp (-(a ^ 2) / 2)) *
            (1 / a - 1 / a ^ 3) * standardNormalConstant := hproduct_lower
      _ = N * ((1 / a - 1 / a ^ 3) *
            standardNormalConstant * Real.exp (-(a ^ 2) / 2)) := by
        ring
  have hlog_two_le_one : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  exact hlog_two_le_one.trans (by simpa [a, s, N] using hmain)

/-- Exercise 2.5.11, explicit large-cardinality form: for independent standard
normal coordinates and `sqrt(log N) ≥ 16`, the expected maximum is at least a
universal constant times `sqrt(log N)`. -/
theorem finiteMax_standardNormal_integral_ge_sqrt_log_card_of_large_card
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (i₀ : ι)
    (hindep : iIndepFun X μ)
    (hXmeas : ∀ i, Measurable (X i))
    (hLaw : ∀ i, μ.map (X i) = standardNormalMeasure)
    (hlarge : 16 ≤ Real.sqrt (Real.log (Fintype.card ι : ℝ))) :
    (1 / 16 : ℝ) * Real.sqrt (Real.log (Fintype.card ι : ℝ))
      ≤ ∫ ω, finiteMax X ω ∂μ := by
  refine
    finiteMax_standardNormal_integral_ge_sqrt_log_card_of_mills_budget
      (μ := μ) (X := X) i₀ hindep hXmeas hLaw hlarge ?_
  exact standardNormal_mills_budget_quarter_sqrt_log_card_of_large_card
    (ι := ι) hlarge

/-- A finite maximum is integrable when each coordinate satisfies the
book-facing moment condition from Proposition 2.5.2(ii). -/
theorem integrable_finiteMaxAbs_of_subGaussianMomentCondition
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K : ι → ℝ}
    (hX : ∀ i, subGaussianMomentCondition (X i) μ (K i)) :
    Integrable (finiteMaxAbs X) μ := by
  refine integrable_finiteMaxAbs_of_integrable (μ := μ) (X := X) ?_
  intro i
  have hmem : MemLp (X i) (1 : ℝ≥0∞) μ :=
    ((hX i).2 (1 : ℝ≥0) (by norm_num : (1 : ℝ) ≤ 1)).1
  simpa using (memLp_one_iff_integrable.mp hmem)

/-- Layer-cake identity for the expectation of a finite nonnegative maximum,
written with the exact tail event from Exercise 2.5.10. -/
theorem finiteMaxAbs_integral_eq_tail
    {X : ι → Ω → ℝ}
    (hInt : Integrable (finiteMaxAbs X) μ) :
    ∫ ω, finiteMaxAbs X ω ∂μ =
      ∫ t in Set.Ioi (0 : ℝ), μ.real (finiteMaxAbsTailEvent X t) := by
  rw [hInt.integral_eq_integral_meas_le]
  · refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _ht
    exact congrArg (fun s : Set Ω => μ.real s)
      (finiteMaxAbsTailEvent_eq_preimage X t).symm
  · exact Filter.Eventually.of_forall fun ω => finiteMaxAbs_nonneg X ω

/-- Exercise 2.5.10 layer-cake bridge: any integrable upper bound for the
maximum tail integrates to an expectation bound for the finite maximum. -/
theorem finiteMaxAbs_integral_le_of_tail_bound
    {X : ι → Ω → ℝ}
    (hInt : Integrable (finiteMaxAbs X) μ)
    {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Ioi (0 : ℝ)))
    (hbound : ∀ t, 0 < t → μ.real (finiteMaxAbsTailEvent X t) ≤ g t) :
    ∫ ω, finiteMaxAbs X ω ∂μ ≤
      ∫ t in Set.Ioi (0 : ℝ), g t := by
  rw [finiteMaxAbs_integral_eq_tail (μ := μ) (X := X) hInt]
  refine
    integral_mono_of_nonneg
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (f := fun t => μ.real (finiteMaxAbsTailEvent X t))
      (g := g)
      ?_ hg ?_
  · exact Filter.Eventually.of_forall fun _t => measureReal_nonneg
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    exact hbound t ht

/-- Uniform sub-gaussian version of the finite maximum expectation bound
before the final one-dimensional calculus estimate. No independence is
required. -/
theorem finiteMaxAbs_integral_le_uniform_subGaussian_tail_integral
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K : ℝ}
    (hInt : Integrable (finiteMaxAbs X) μ)
    (hX : ∀ i, subGaussianTailCondition (X i) μ K) :
    ∫ ω, finiteMaxAbs X ω ∂μ ≤
      ∫ t in Set.Ioi (0 : ℝ),
        (Fintype.card ι : ℝ) *
          (2 * Real.exp (-(t ^ 2) / K ^ 2)) := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  have hK : 0 < K := (hX i₀).1
  have hcoef : 0 < 1 / K ^ 2 := by
    positivity
  have hbase :
      Integrable (fun t : ℝ => Real.exp (-(1 / K ^ 2) * t ^ 2)) :=
    integrable_exp_neg_mul_sq hcoef
  have hg :
      IntegrableOn
        (fun t : ℝ =>
          (Fintype.card ι : ℝ) *
            (2 * Real.exp (-(t ^ 2) / K ^ 2)))
        (Set.Ioi (0 : ℝ)) := by
    have hconst :
        Integrable
          (fun t : ℝ =>
            ((Fintype.card ι : ℝ) * 2) *
              Real.exp (-(1 / K ^ 2) * t ^ 2)) :=
      hbase.const_mul ((Fintype.card ι : ℝ) * 2)
    refine hconst.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro t _ht
    ring_nf
  exact
    finiteMaxAbs_integral_le_of_tail_bound
      (μ := μ) (X := X) hInt hg
      (fun t ht =>
        finiteMaxAbsTail_subGaussian_le_card_mul
          (μ := μ) (X := X) (K := K) hX ht.le)

/-- The tail function in the finite-maximum layer-cake identity is integrable
on `(0, ∞)` whenever the maximum itself is integrable. -/
theorem integrableOn_finiteMaxAbsTail_probability
    {X : ι → Ω → ℝ}
    (hInt : Integrable (finiteMaxAbs X) μ) :
    IntegrableOn (fun t : ℝ => μ.real (finiteMaxAbsTailEvent X t))
      (Set.Ioi (0 : ℝ)) := by
  classical
  let Y : Ω → ℝ := finiteMaxAbs X
  have hY_nonneg : 0 ≤ᵐ[μ] Y :=
    Filter.Eventually.of_forall fun ω => finiteMaxAbs_nonneg X ω
  have hY_aemeas : AEMeasurable Y μ := hInt.aemeasurable
  have hLayer :
      ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ =
        ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | t ≤ Y ω} :=
    MeasureTheory.lintegral_eq_lintegral_meas_le μ hY_nonneg hY_aemeas
  have hleft_ne_top :
      (∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ) ≠ ∞ :=
    hInt.lintegral_lt_top.ne
  have hright_ne_top :
      (∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | t ≤ Y ω}) ≠ ∞ := by
    simpa [hLayer] using hleft_ne_top
  have hfinite :
      (fun t : ℝ => ENNReal.ofReal (μ.real {ω | t ≤ Y ω}))
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
          fun t : ℝ => μ {ω | t ≤ Y ω} := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ENNReal.ofReal_toReal
      (Integrable.measure_ge_lt_top (f := Y) hInt (by simpa using ht)).ne
  have hreal_ne_top :
      (∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (μ.real {ω | t ≤ Y ω})) ≠ ∞ := by
    rw [lintegral_congr_ae hfinite]
    exact hright_ne_top
  have hTail_eq :
      (fun t : ℝ => μ.real (finiteMaxAbsTailEvent X t))
        = fun t : ℝ => μ.real {ω | t ≤ Y ω} := by
    funext t
    rw [finiteMaxAbsTailEvent_eq_preimage]
  have hmeas_enn :
      Measurable (fun t : ℝ => μ {ω | t ≤ Y ω}) :=
    Antitone.measurable fun s t hst =>
      measure_mono fun ω hω => hst.trans hω
  have hstrong :
      AEStronglyMeasurable (fun t : ℝ => μ.real {ω | t ≤ Y ω})
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (Measurable.ennreal_toReal hmeas_enn).aestronglyMeasurable
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun t : ℝ => μ.real {ω | t ≤ Y ω} :=
    Filter.Eventually.of_forall fun _ => measureReal_nonneg
  have hInt_tail :
      Integrable (fun t : ℝ => μ.real {ω | t ≤ Y ω})
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (lintegral_ofReal_ne_top_iff_integrable hstrong hnonneg).mp
      hreal_ne_top
  simpa [IntegrableOn, hTail_eq]
    using hInt_tail

/-- Split the layer-cake integral for the finite maximum at a deterministic
threshold `u`. On the first interval the tail probability is bounded by `1`;
after `u` one may insert any integrable tail majorant. -/
theorem finiteMaxAbs_integral_le_split_tail
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ}
    (hInt : Integrable (finiteMaxAbs X) μ)
    {u : ℝ} (hu : 0 ≤ u)
    {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Ioi u))
    (hbound : ∀ t, u < t → μ.real (finiteMaxAbsTailEvent X t) ≤ g t) :
    ∫ ω, finiteMaxAbs X ω ∂μ ≤
      u + ∫ t in Set.Ioi u, g t := by
  classical
  let F : ℝ → ℝ := fun t => μ.real (finiteMaxAbsTailEvent X t)
  have hFint :
      IntegrableOn F (Set.Ioi (0 : ℝ)) :=
    integrableOn_finiteMaxAbsTail_probability (μ := μ) (X := X) hInt
  have hleft_int : IntegrableOn F (Set.Ioc (0 : ℝ) u) :=
    hFint.mono_set Set.Ioc_subset_Ioi_self
  have hright_int : IntegrableOn F (Set.Ioi u) :=
    hFint.mono_set fun t ht => hu.trans_lt ht
  have hsplit :
      ∫ t in Set.Ioi (0 : ℝ), F t =
        (∫ t in Set.Ioc (0 : ℝ) u, F t) +
          (∫ t in Set.Ioi u, F t) := by
    have hI : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) u ∪ Set.Ioi u :=
      (Set.Ioc_union_Ioi_eq_Ioi hu).symm
    rw [hI]
    exact
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hleft_int hright_int
  have hleft :
      ∫ t in Set.Ioc (0 : ℝ) u, F t ≤ u := by
    have hone_int : IntegrableOn (fun _t : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) u) := by
      exact integrableOn_const (μ := volume) (s := Set.Ioc (0 : ℝ) u)
        (by simp [Real.volume_Ioc])
    calc
      ∫ t in Set.Ioc (0 : ℝ) u, F t
          ≤ ∫ t in Set.Ioc (0 : ℝ) u, (1 : ℝ) := by
        exact integral_mono_ae hleft_int hone_int
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            exact measureReal_le_one)
      _ = u := by
        rw [setIntegral_const]
        simp [hu]
  have hright :
      ∫ t in Set.Ioi u, F t ≤ ∫ t in Set.Ioi u, g t := by
    exact integral_mono_ae hright_int hg
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hbound t ht)
  calc
    ∫ ω, finiteMaxAbs X ω ∂μ
        = ∫ t in Set.Ioi (0 : ℝ), F t := by
      simpa [F] using finiteMaxAbs_integral_eq_tail (μ := μ) (X := X) hInt
    _ = (∫ t in Set.Ioc (0 : ℝ) u, F t) +
          (∫ t in Set.Ioi u, F t) := hsplit
    _ ≤ u + ∫ t in Set.Ioi u, g t := add_le_add hleft hright

/-- Elementary one-sided Gaussian tail integral estimate used in
Exercise 2.5.10: beyond `u`, the quadratic exponent is dominated by the
linear exponent tangent at the origin with slope `u / K²`. -/
lemma integral_Ioi_exp_neg_sq_div_le
    {K u : ℝ} (hK : 0 < K) (hu : 0 < u) :
    ∫ t in Set.Ioi u, Real.exp (-(t ^ 2) / K ^ 2)
      ≤ K ^ 2 / u * Real.exp (-(u ^ 2) / K ^ 2) := by
  have hcoef_pos : 0 < 1 / K ^ 2 := by positivity
  have hquad_int :
      IntegrableOn
        (fun t : ℝ => Real.exp (-(t ^ 2) / K ^ 2))
        (Set.Ioi u) := by
    have hglobal :
        Integrable (fun t : ℝ => Real.exp (-(1 / K ^ 2) * t ^ 2)) :=
      integrable_exp_neg_mul_sq hcoef_pos
    refine hglobal.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro t _ht
    ring_nf
  have hlin_int :
      IntegrableOn
        (fun t : ℝ => Real.exp (-(u / K ^ 2) * t))
        (Set.Ioi u) := by
    have ha : -(u / K ^ 2) < 0 := by
      have hdiv : 0 < u / K ^ 2 := by positivity
      linarith
    exact integrableOn_exp_mul_Ioi (a := -(u / K ^ 2)) ha u
  have hpoint :
      ∀ t ∈ Set.Ioi u,
        Real.exp (-(t ^ 2) / K ^ 2)
          ≤ Real.exp (-(u / K ^ 2) * t) := by
    intro t ht
    rw [Real.exp_le_exp]
    have ht_nonneg : 0 ≤ t := hu.le.trans ht.le
    have hmul : u * t ≤ t ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right ht.le ht_nonneg]
    have hden_nonneg : 0 ≤ K ^ 2 := sq_nonneg K
    have hdiv : (u * t) / K ^ 2 ≤ t ^ 2 / K ^ 2 :=
      div_le_div_of_nonneg_right hmul hden_nonneg
    have hneg : -(t ^ 2 / K ^ 2) ≤ -(u * t / K ^ 2) :=
      neg_le_neg hdiv
    have hlhs : -(t ^ 2) / K ^ 2 = -(t ^ 2 / K ^ 2) := by ring
    have hrhs : -(u / K ^ 2) * t = -(u * t / K ^ 2) := by ring
    simpa [hlhs, hrhs] using hneg
  calc
    ∫ t in Set.Ioi u, Real.exp (-(t ^ 2) / K ^ 2)
        ≤ ∫ t in Set.Ioi u, Real.exp (-(u / K ^ 2) * t) := by
      exact integral_mono_ae hquad_int hlin_int
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact hpoint t ht)
    _ = K ^ 2 / u * Real.exp (-(u ^ 2) / K ^ 2) := by
      have ha : -(u / K ^ 2) < 0 := by
        have hdiv : 0 < u / K ^ 2 := by positivity
        linarith
      rw [integral_exp_mul_Ioi ha u]
      field_simp [hu.ne', hK.ne']

/-- Uniform finite-maximum expectation bound after a threshold split. This is
the one-dimensional calculus core of HDP Exercise 2.5.10. -/
theorem finiteMaxAbs_integral_le_uniform_subGaussian_split
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K u : ℝ}
    (hInt : Integrable (finiteMaxAbs X) μ)
    (hX : ∀ i, subGaussianTailCondition (X i) μ K)
    (hu : 0 < u) :
    ∫ ω, finiteMaxAbs X ω ∂μ ≤
      u + (Fintype.card ι : ℝ) * 2 *
        (K ^ 2 / u * Real.exp (-(u ^ 2) / K ^ 2)) := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  have hK : 0 < K := (hX i₀).1
  have hg :
      IntegrableOn
        (fun t : ℝ =>
          (Fintype.card ι : ℝ) *
            (2 * Real.exp (-(t ^ 2) / K ^ 2)))
        (Set.Ioi u) := by
    have hcoef : 0 < 1 / K ^ 2 := by positivity
    have hbase :
        Integrable (fun t : ℝ => Real.exp (-(1 / K ^ 2) * t ^ 2)) :=
      integrable_exp_neg_mul_sq hcoef
    have hconst :
        Integrable
          (fun t : ℝ =>
            ((Fintype.card ι : ℝ) * 2) *
              Real.exp (-(1 / K ^ 2) * t ^ 2)) :=
      hbase.const_mul ((Fintype.card ι : ℝ) * 2)
    refine hconst.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro t _ht
    ring_nf
  have hsplit :=
    finiteMaxAbs_integral_le_split_tail
      (μ := μ) (X := X) hInt hu.le hg
      (fun t ht =>
        finiteMaxAbsTail_subGaussian_le_card_mul
          (μ := μ) (X := X) (K := K) hX (le_of_lt (hu.trans ht)))
  have htail :=
    integral_Ioi_exp_neg_sq_div_le (K := K) (u := u) hK hu
  have hconst_nonneg : 0 ≤ (Fintype.card ι : ℝ) * 2 := by positivity
  calc
    ∫ ω, finiteMaxAbs X ω ∂μ
        ≤ u + ∫ t in Set.Ioi u,
          (Fintype.card ι : ℝ) *
            (2 * Real.exp (-(t ^ 2) / K ^ 2)) := hsplit
    _ = u + ((Fintype.card ι : ℝ) * 2) *
          ∫ t in Set.Ioi u, Real.exp (-(t ^ 2) / K ^ 2) := by
      have hfun :
          (fun t : ℝ =>
            (Fintype.card ι : ℝ) *
              (2 * Real.exp (-(t ^ 2) / K ^ 2)))
            =
          fun t : ℝ =>
            ((Fintype.card ι : ℝ) * 2) *
              Real.exp (-(t ^ 2) / K ^ 2) := by
        funext t
        ring
      rw [hfun]
      rw [integral_const_mul]
    _ ≤ u + ((Fintype.card ι : ℝ) * 2) *
          (K ^ 2 / u * Real.exp (-(u ^ 2) / K ^ 2)) :=
      add_le_add (le_refl u)
        (mul_le_mul_of_nonneg_left htail hconst_nonneg)
    _ = u + (Fintype.card ι : ℝ) * 2 *
        (K ^ 2 / u * Real.exp (-(u ^ 2) / K ^ 2)) := by ring

/-- HDP Exercise 2.5.10, finite `N` corollary with an explicit universal
constant: for `N ≥ 2`, a finite family with a common sub-gaussian tail scale
`K` satisfies `E maxᵢ |Xᵢ| ≤ 10 K sqrt(log N)`. No independence is required. -/
theorem finiteMaxAbs_integral_le_uniform_subGaussian_ten_sqrt_log_card
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K : ℝ}
    (hInt : Integrable (finiteMaxAbs X) μ)
    (hX : ∀ i, subGaussianTailCondition (X i) μ K)
    (hcard : 2 ≤ Fintype.card ι) :
    ∫ ω, finiteMaxAbs X ω ∂μ ≤
      10 * K * Real.sqrt (Real.log (Fintype.card ι : ℝ)) := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  have hK : 0 < K := (hX i₀).1
  let n : ℝ := Fintype.card ι
  let s : ℝ := Real.sqrt (Real.log n)
  have hn_two : (2 : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast hcard
  have hn_pos : 0 < n := by
    exact (by norm_num : (0 : ℝ) < 2).trans_le hn_two
  have hlog_pos : 0 < Real.log n := by
    exact Real.log_pos ((by norm_num : (1 : ℝ) < 2).trans_le hn_two)
  have hs_pos : 0 < s := Real.sqrt_pos.2 hlog_pos
  have hs_sq : s ^ 2 = Real.log n := by
    simpa [s] using Real.sq_sqrt hlog_pos.le
  have hsplit :=
    finiteMaxAbs_integral_le_uniform_subGaussian_split
      (μ := μ) (X := X) (K := K) (u := K * s)
      hInt hX (mul_pos hK hs_pos)
  have hbudget :
      K * s + (Fintype.card ι : ℝ) * 2 *
        (K ^ 2 / (K * s) *
          Real.exp (-((K * s) ^ 2) / K ^ 2))
        = K * s + 2 * K / s := by
    have hK_ne : K ≠ 0 := hK.ne'
    have hs_ne : s ≠ 0 := hs_pos.ne'
    have hexp :
        Real.exp (-((K * s) ^ 2) / K ^ 2) = 1 / n := by
      have harg : -((K * s) ^ 2) / K ^ 2 = -Real.log n := by
        field_simp [hK_ne]
        rw [hs_sq]
      rw [harg, Real.exp_neg, Real.exp_log hn_pos, one_div]
    rw [hexp]
    field_simp [hK_ne, hs_ne, hn_pos.ne']
    ring
  have hs_sq_lower : (1 / 4 : ℝ) ≤ s ^ 2 := by
    rw [hs_sq]
    exact one_fourth_le_log_two.trans
      (Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        hn_two)
  have hinv_bound : 2 * K / s ≤ 8 * K * s := by
    have hs_nonneg : 0 ≤ s := hs_pos.le
    have hmul : (2 : ℝ) ≤ 8 * s ^ 2 := by nlinarith
    have hmulK : 2 * K ≤ 8 * K * s ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hmul hK.le]
    have hspos : 0 < s := hs_pos
    rw [div_le_iff₀ hspos]
    nlinarith
  have hsum : K * s + 2 * K / s ≤ 10 * K * s := by
    nlinarith [hinv_bound]
  calc
    ∫ ω, finiteMaxAbs X ω ∂μ
        ≤ K * s + (Fintype.card ι : ℝ) * 2 *
          (K ^ 2 / (K * s) *
            Real.exp (-((K * s) ^ 2) / K ^ 2)) := hsplit
    _ = K * s + 2 * K / s := hbudget
    _ ≤ 10 * K * s := hsum
    _ = 10 * K * Real.sqrt (Real.log (Fintype.card ι : ℝ)) := rfl

/-- The normalized initial segment from HDP Exercise 2.5.10:
`X_i / sqrt(1 + log(i+1))`, using zero-based Lean indices. -/
def logNormalizedInitialSegment (X : ℕ → Ω → ℝ) (N : ℕ) : Fin N → Ω → ℝ :=
  fun i ω => X i.1 ω / Real.sqrt (1 + Real.log (((i.1 + 1 : ℕ) : ℝ)))

lemma log_weight_sqrt_pos {N : ℕ} (i : Fin N) :
    0 < Real.sqrt (1 + Real.log (((i.1 + 1 : ℕ) : ℝ))) := by
  have hone_le : (1 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.1)
  have hlog_nonneg : 0 ≤ Real.log (((i.1 + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg hone_le
  exact Real.sqrt_pos.2 (by linarith)

lemma exp_neg_mul_one_add_log_le_exp_neg_mul_inv_sq
    {a n : ℝ} (ha : 2 ≤ a) (hn : 1 ≤ n) :
    Real.exp (-(a * (1 + Real.log n))) ≤ Real.exp (-a) * (n ^ 2)⁻¹ := by
  have hn_pos : 0 < n := (by norm_num : (0 : ℝ) < 1).trans_le hn
  have hpow_le : n ^ (-a) ≤ n ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hpow_neg_two : n ^ (-2 : ℝ) = (n ^ 2)⁻¹ := by
    rw [Real.rpow_neg hn_pos.le]
    norm_num
  have hnonneg : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  calc
    Real.exp (-(a * (1 + Real.log n)))
        = Real.exp (-a + (-a) * Real.log n) := by
          congr 1
          ring_nf
    _ = Real.exp (-a) * n ^ (-a) := by
          rw [Real.exp_add]
          rw [Real.rpow_def_of_pos hn_pos]
          congr 1
          ring_nf
    _ ≤ Real.exp (-a) * n ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow_le hnonneg
    _ = Real.exp (-a) * (n ^ 2)⁻¹ := by rw [hpow_neg_two]

lemma sum_range_inv_sq_add_one_le_two (N : ℕ) :
    (∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤ 2 := by
  have hbij :
      (∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) =
        ∑ j ∈ Finset.Ioo 0 (N + 1), (((j : ℕ) : ℝ) ^ 2)⁻¹ := by
    refine Finset.sum_bij (fun i _hi => i + 1) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_Ioo]
      rw [Finset.mem_range] at hi
      change 0 < i + 1 ∧ i + 1 < N + 1
      omega
    · intro a ha b hb h
      change a + 1 = b + 1 at h
      omega
    · intro j hj
      rw [Finset.mem_Ioo] at hj
      refine ⟨j - 1, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · change (j - 1) + 1 = j
        omega
    · intro i hi
      rfl
  rw [hbij]
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1)
  norm_num at h
  exact h

/-- Tail bound for the normalized finite initial segment in HDP Exercise 2.5.10.
For `t ≥ 2K`, the union bound and reciprocal-square summation give
`P{max_{i<N} |X_i|/sqrt(1+log(i+1)) ≥ t} ≤ 4 exp(-t²/K²)`. -/
theorem finiteLogNormalizedMaxTail_le_four_exp
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {K : ℝ} {N : ℕ} {t : ℝ}
    (hK : 0 < K)
    (hX : ∀ i : Fin N, subGaussianTailCondition (X i.1) μ K)
    (ht_large : 2 * K ≤ t) :
    μ.real (finiteMaxAbsTailEvent (logNormalizedInitialSegment X N) t)
      ≤ 4 * Real.exp (-(t ^ 2) / K ^ 2) := by
  classical
  have ht_nonneg : 0 ≤ t := by nlinarith [hK]
  let a : ℝ := t ^ 2 / K ^ 2
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hK
  have ha_ge_four : 4 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ hKsq_pos]
    nlinarith
  have ha_ge_two : 2 ≤ a := by linarith
  have htail_sum :
      μ.real (finiteMaxAbsTailEvent (logNormalizedInitialSegment X N) t) ≤
        ∑ i : Fin N,
          2 * Real.exp (-a) * ((((i.1 + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    calc
      μ.real (finiteMaxAbsTailEvent (logNormalizedInitialSegment X N) t)
          ≤ ∑ i : Fin N,
              μ.real {ω | t ≤ |logNormalizedInitialSegment X N i ω|} :=
        finiteMaxAbsTail_probability_le_sum
          (μ := μ) (X := logNormalizedInitialSegment X N) t
      _ ≤ ∑ i : Fin N,
          2 * Real.exp (-a) * ((((i.1 + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        let nR : ℝ := ((i.1 + 1 : ℕ) : ℝ)
        let s : ℝ := Real.sqrt (1 + Real.log nR)
        have hs_pos : 0 < s := by
          dsimp [s, nR]
          exact log_weight_sqrt_pos i
        have hs_nonneg : 0 ≤ s := hs_pos.le
        have hn_ge_one : (1 : ℝ) ≤ nR := by
          dsimp [nR]
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.1)
        have hlog_nonneg : 0 ≤ Real.log nR := Real.log_nonneg hn_ge_one
        have hs_sq : s ^ 2 = 1 + Real.log nR := by
          dsimp [s]
          rw [Real.sq_sqrt]
          linarith
        have hsubset :
            {ω | t ≤ |logNormalizedInitialSegment X N i ω|} ⊆
              {ω | t * s ≤ |X i.1 ω|} := by
          intro ω hω
          have h_abs : |logNormalizedInitialSegment X N i ω| = |X i.1 ω| / s := by
            change |X i.1 ω / s| = |X i.1 ω| / s
            rw [abs_div, abs_of_pos hs_pos]
          have hmul := mul_le_mul_of_nonneg_right hω hs_nonneg
          rwa [h_abs, div_mul_cancel₀ _ hs_pos.ne'] at hmul
        have htail_i :
            μ.real {ω | t ≤ |logNormalizedInitialSegment X N i ω|} ≤
              2 * Real.exp (-((t * s) ^ 2) / K ^ 2) := by
          calc
            μ.real {ω | t ≤ |logNormalizedInitialSegment X N i ω|}
                ≤ μ.real {ω | t * s ≤ |X i.1 ω|} :=
              MeasureTheory.measureReal_mono hsubset
            _ ≤ 2 * Real.exp (-((t * s) ^ 2) / K ^ 2) :=
              (hX i).2 (t * s) (mul_nonneg ht_nonneg hs_nonneg)
        have hexp_bound :
            Real.exp (-((t * s) ^ 2) / K ^ 2) ≤
              Real.exp (-a) * (nR ^ 2)⁻¹ := by
          have harg : -((t * s) ^ 2) / K ^ 2 = -(a * (1 + Real.log nR)) := by
            dsimp [a]
            have hmul_sq : (t * s) ^ 2 = t ^ 2 * s ^ 2 := by ring
            rw [hmul_sq, hs_sq]
            field_simp [hK.ne']
          rw [harg]
          exact exp_neg_mul_one_add_log_le_exp_neg_mul_inv_sq
            ha_ge_two hn_ge_one
        calc
          μ.real {ω | t ≤ |logNormalizedInitialSegment X N i ω|}
              ≤ 2 * Real.exp (-((t * s) ^ 2) / K ^ 2) := htail_i
          _ ≤ 2 * (Real.exp (-a) * (nR ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hexp_bound (by norm_num : (0 : ℝ) ≤ 2)
          _ = 2 * Real.exp (-a) * ((((i.1 + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
            dsimp [nR]
            ring_nf
  have hsum_fin :
      (∑ i : Fin N, ((((i.1 + 1 : ℕ) : ℝ) ^ 2)⁻¹)) ≤ 2 := by
    have hcast :
        (∑ i : Fin N, ((((i.1 + 1 : ℕ) : ℝ) ^ 2)⁻¹)) =
          ∑ i : Fin N, ((((i.1 : ℝ) + 1) ^ 2)⁻¹) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      norm_num [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => (((i : ℝ) + 1) ^ 2)⁻¹) N]
    simpa [Nat.cast_add, Nat.cast_one] using sum_range_inv_sq_add_one_le_two N
  calc
    μ.real (finiteMaxAbsTailEvent (logNormalizedInitialSegment X N) t)
        ≤ ∑ i : Fin N,
          2 * Real.exp (-a) * ((((i.1 + 1 : ℕ) : ℝ) ^ 2)⁻¹) := htail_sum
    _ = (2 * Real.exp (-a)) *
          ∑ i : Fin N, ((((i.1 + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * Real.exp (-a)) * 2 :=
      mul_le_mul_of_nonneg_left hsum_fin (by positivity)
    _ = 4 * Real.exp (-(t ^ 2) / K ^ 2) := by
      dsimp [a]
      ring_nf

/-- HDP Exercise 2.5.10, normalized finite-initial-segment form: for every
`N ≥ 1`, no independence assumption is needed to bound
`E max_{i<N} |X_i| / sqrt(1 + log(i+1))` by an absolute multiple of the common
sub-gaussian scale. -/
theorem finiteLogNormalizedMax_integral_le_four_mul
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {K : ℝ} {N : ℕ}
    [Nonempty (Fin N)] (hK : 0 < K)
    (hXm : ∀ i : Fin N, AEStronglyMeasurable (X i.1) μ)
    (hX : ∀ i : Fin N, subGaussianTailCondition (X i.1) μ K) :
    ∫ ω, finiteMaxAbs (logNormalizedInitialSegment X N) ω ∂μ ≤ 4 * K := by
  classical
  let Y : Fin N → Ω → ℝ := logNormalizedInitialSegment X N
  have hYtail : ∀ i : Fin N, subGaussianTailCondition (Y i) μ K := by
    intro i
    refine ⟨hK, ?_⟩
    intro t ht
    let nR : ℝ := ((i.1 + 1 : ℕ) : ℝ)
    let s : ℝ := Real.sqrt (1 + Real.log nR)
    have hs_pos : 0 < s := by
      dsimp [s, nR]
      exact log_weight_sqrt_pos i
    have hn_ge_one : (1 : ℝ) ≤ nR := by
      dsimp [nR]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.1)
    have hlog_nonneg : 0 ≤ Real.log nR := Real.log_nonneg hn_ge_one
    have hs_ge_one : 1 ≤ s := by
      dsimp [s]
      have h :=
        Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + Real.log nR by linarith)
      simpa using h
    have hsubset : {ω | t ≤ |Y i ω|} ⊆ {ω | t ≤ |X i.1 ω|} := by
      intro ω hω
      have h_abs : |Y i ω| = |X i.1 ω| / s := by
        change |X i.1 ω / s| = |X i.1 ω| / s
        rw [abs_div, abs_of_pos hs_pos]
      calc
        t ≤ |Y i ω| := hω
        _ = |X i.1 ω| / s := h_abs
        _ ≤ |X i.1 ω| := by
          rw [div_le_iff₀ hs_pos]
          nlinarith [abs_nonneg (X i.1 ω), hs_ge_one]
    exact (MeasureTheory.measureReal_mono hsubset).trans ((hX i).2 t ht)
  have hYm : ∀ i : Fin N, AEStronglyMeasurable (Y i) μ := by
    intro i
    let s : ℝ := Real.sqrt (1 + Real.log (((i.1 + 1 : ℕ) : ℝ)))
    refine ((hXm i).mul_const s⁻¹).congr ?_
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [Y, logNormalizedInitialSegment, s]
      ring
  have hYmom : ∀ i : Fin N, subGaussianMomentCondition (Y i) μ (4 * K) := by
    intro i
    exact subGaussianMomentCondition_of_subGaussianTailCondition (hYm i) (hYtail i)
  have hInt : Integrable (finiteMaxAbs Y) μ :=
    integrable_finiteMaxAbs_of_subGaussianMomentCondition (μ := μ) (X := Y) hYmom
  have hu_pos : 0 < 2 * K := by positivity
  have hg : IntegrableOn (fun t : ℝ => 4 * Real.exp (-(t ^ 2) / K ^ 2))
      (Set.Ioi (2 * K)) := by
    have hcoef : 0 < 1 / K ^ 2 := by positivity
    have hbase : Integrable (fun t : ℝ => Real.exp (-(1 / K ^ 2) * t ^ 2)) :=
      integrable_exp_neg_mul_sq hcoef
    have hconst : Integrable (fun t : ℝ => 4 * Real.exp (-(1 / K ^ 2) * t ^ 2)) :=
      hbase.const_mul 4
    refine hconst.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro t _ht
    ring_nf
  have hsplit :=
    finiteMaxAbs_integral_le_split_tail
      (μ := μ) (X := Y) hInt hu_pos.le hg
      (fun t ht => finiteLogNormalizedMaxTail_le_four_exp
        (μ := μ) (X := X) (K := K) (N := N) hK hX (le_of_lt ht))
  have htail := integral_Ioi_exp_neg_sq_div_le (K := K) (u := 2 * K) hK hu_pos
  have htail_scaled :
      ∫ t in Set.Ioi (2 * K), 4 * Real.exp (-(t ^ 2) / K ^ 2) ≤ 2 * K := by
    calc
      ∫ t in Set.Ioi (2 * K), 4 * Real.exp (-(t ^ 2) / K ^ 2)
          = 4 * ∫ t in Set.Ioi (2 * K),
              Real.exp (-(t ^ 2) / K ^ 2) := by
            rw [integral_const_mul]
      _ ≤ 4 * (K ^ 2 / (2 * K) *
            Real.exp (-((2 * K) ^ 2) / K ^ 2)) :=
            mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 4)
      _ ≤ 2 * K := by
            have hK_ne : K ≠ 0 := hK.ne'
            have hexp_le_one :
                Real.exp (-((2 * K) ^ 2) / K ^ 2) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              have hnonneg : 0 ≤ ((2 * K) ^ 2) / K ^ 2 :=
                div_nonneg (sq_nonneg (2 * K)) (sq_nonneg K)
              have harg :
                  -((2 * K) ^ 2) / K ^ 2 =
                    -(((2 * K) ^ 2) / K ^ 2) := by ring
              rw [harg]
              exact neg_nonpos.mpr hnonneg
            have hfactor : K ^ 2 / (2 * K) = K / 2 := by
              field_simp [hK_ne]
            rw [hfactor]
            nlinarith [mul_le_mul_of_nonneg_left hexp_le_one
              (by positivity : 0 ≤ K / 2)]
  calc
    ∫ ω, finiteMaxAbs (logNormalizedInitialSegment X N) ω ∂μ
        = ∫ ω, finiteMaxAbs Y ω ∂μ := rfl
    _ ≤ 2 * K + ∫ t in Set.Ioi (2 * K),
          4 * Real.exp (-(t ^ 2) / K ^ 2) := by
          simpa [Y] using hsplit
    _ ≤ 2 * K + 2 * K := add_le_add (le_refl (2 * K)) htail_scaled
    _ = 4 * K := by ring

/-- HDP Exercise 2.5.10, finite normalized form stated with the book's
`ψ₂`-norm scale: if every coordinate in the initial segment has
`‖Xᵢ‖_{ψ₂} ≤ K`, then
`E max_{i<N} |Xᵢ| / sqrt(1 + log(i+1)) ≤ 4K`. -/
theorem finiteLogNormalizedMax_integral_le_four_mul_subGaussianNorm
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {K : ℝ} {N : ℕ}
    [Nonempty (Fin N)]
    (hK : 0 ≤ K)
    (hXm : ∀ i : Fin N, AEStronglyMeasurable (X i.1) μ)
    (hXsg : ∀ i : Fin N, IsSubGaussian (X i.1) μ)
    (hNorm : ∀ i : Fin N, subGaussianNorm (X i.1) μ ≤ K) :
    ∫ ω, finiteMaxAbs (logNormalizedInitialSegment X N) ω ∂μ ≤ 4 * K := by
  classical
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro q hq
  let r : ℝ := q / 4
  have hr_gt : K < r := by
    dsimp [r]
    nlinarith
  have hr_pos : 0 < r := hK.trans_lt hr_gt
  have hTail :
      ∀ i : Fin N, subGaussianTailCondition (X i.1) μ r := by
    intro i
    exact subGaussianTailCondition_of_subGaussianNorm_lt
      (μ := μ) (X := X i.1) (K := r)
      (hXsg i) ((hNorm i).trans_lt hr_gt)
  have hbound :
      ∫ ω, finiteMaxAbs (logNormalizedInitialSegment X N) ω ∂μ ≤ 4 * r :=
    finiteLogNormalizedMax_integral_le_four_mul
      (μ := μ) (X := X) (K := r) (N := N)
      hr_pos hXm hTail
  have hqr : 4 * r = q := by
    dsimp [r]
    ring
  exact hbound.trans_eq hqr

/-- The real-valued `n`th finite approximation to the infinite normalized
maximum in HDP Exercise 2.5.10. The approximation with index `n` keeps
coordinates `0, …, n`. -/
def logNormalizedMaxApproxReal (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  finiteMaxAbs (logNormalizedInitialSegment X (n + 1)) ω

/-- The `ENNReal` finite approximation to the infinite normalized maximum in
HDP Exercise 2.5.10. -/
def logNormalizedMaxApprox (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (logNormalizedMaxApproxReal X n ω)

/-- The pointwise supremum of the normalized finite initial maxima from HDP
Exercise 2.5.10, represented as an `ENNReal` random variable. -/
def logNormalizedMaxSup (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, logNormalizedMaxApprox X n ω

omit [MeasurableSpace Ω] in
lemma finiteMaxAbs_logNormalizedInitialSegment_mono_succ
    (X : ℕ → Ω → ℝ) (ω : Ω) {n m : ℕ} (hnm : n ≤ m) :
    finiteMaxAbs (logNormalizedInitialSegment X (n + 1)) ω
      ≤ finiteMaxAbs (logNormalizedInitialSegment X (m + 1)) ω := by
  classical
  rw [finiteMaxAbs, Finset.sup'_le_iff]
  intro i _hi
  let j : Fin (m + 1) :=
    ⟨i.1, lt_of_lt_of_le i.2 (Nat.succ_le_succ hnm)⟩
  have hle :
      |logNormalizedInitialSegment X (m + 1) j ω|
        ≤ finiteMaxAbs (logNormalizedInitialSegment X (m + 1)) ω :=
    Finset.le_sup'
      (s := (Finset.univ : Finset (Fin (m + 1))))
      (f := fun j : Fin (m + 1) =>
        |logNormalizedInitialSegment X (m + 1) j ω|)
      (Finset.mem_univ j)
  simpa [finiteMaxAbs, logNormalizedInitialSegment, j] using hle

omit [MeasurableSpace Ω] in
lemma logNormalizedMaxApproxReal_mono (X : ℕ → Ω → ℝ) (ω : Ω) :
    Monotone fun n => logNormalizedMaxApproxReal X n ω := by
  intro n m hnm
  exact finiteMaxAbs_logNormalizedInitialSegment_mono_succ X ω hnm

omit [MeasurableSpace Ω] in
lemma logNormalizedMaxApprox_mono (X : ℕ → Ω → ℝ) (ω : Ω) :
    Monotone fun n => logNormalizedMaxApprox X n ω := by
  intro n m hnm
  exact ENNReal.ofReal_le_ofReal
    (logNormalizedMaxApproxReal_mono X ω hnm)

/-- The normalized initial segment has a.e. strongly measurable coordinates
when the original coordinates do. -/
theorem logNormalizedInitialSegment_aestronglyMeasurable
    {X : ℕ → Ω → ℝ} {N : ℕ}
    (hXm : ∀ i : Fin N, AEStronglyMeasurable (X i.1) μ) :
    ∀ i : Fin N,
      AEStronglyMeasurable (logNormalizedInitialSegment X N i) μ := by
  intro i
  let s : ℝ := Real.sqrt (1 + Real.log (((i.1 + 1 : ℕ) : ℝ)))
  refine ((hXm i).mul_const s⁻¹).congr ?_
  exact Filter.Eventually.of_forall fun ω => by
    dsimp [logNormalizedInitialSegment, s]
    ring

/-- Dividing by the logarithmic weight, which is at least one, preserves a
common sub-gaussian tail scale. -/
theorem logNormalizedInitialSegment_subGaussianTailCondition
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {K : ℝ} {N : ℕ}
    (hK : 0 < K)
    (hX : ∀ i : Fin N, subGaussianTailCondition (X i.1) μ K) :
    ∀ i : Fin N,
      subGaussianTailCondition (logNormalizedInitialSegment X N i) μ K := by
  intro i
  refine ⟨hK, ?_⟩
  intro t ht
  let nR : ℝ := ((i.1 + 1 : ℕ) : ℝ)
  let s : ℝ := Real.sqrt (1 + Real.log nR)
  have hs_pos : 0 < s := by
    dsimp [s, nR]
    exact log_weight_sqrt_pos i
  have hn_ge_one : (1 : ℝ) ≤ nR := by
    dsimp [nR]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.1)
  have hlog_nonneg : 0 ≤ Real.log nR := Real.log_nonneg hn_ge_one
  have hs_ge_one : 1 ≤ s := by
    dsimp [s]
    have h :=
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + Real.log nR by linarith)
    simpa using h
  have hsubset :
      {ω | t ≤ |logNormalizedInitialSegment X N i ω|}
        ⊆ {ω | t ≤ |X i.1 ω|} := by
    intro ω hω
    have h_abs :
        |logNormalizedInitialSegment X N i ω| = |X i.1 ω| / s := by
      change |X i.1 ω / s| = |X i.1 ω| / s
      rw [abs_div, abs_of_pos hs_pos]
    calc
      t ≤ |logNormalizedInitialSegment X N i ω| := hω
      _ = |X i.1 ω| / s := h_abs
      _ ≤ |X i.1 ω| := by
        rw [div_le_iff₀ hs_pos]
        nlinarith [abs_nonneg (X i.1 ω), hs_ge_one]
  exact (MeasureTheory.measureReal_mono hsubset).trans ((hX i).2 t ht)

/-- Integrability of the finite normalized maximum used in the infinite
Exercise 2.5.10 monotone-convergence argument. -/
theorem integrable_finiteLogNormalizedMax
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {K : ℝ} {N : ℕ}
    [Nonempty (Fin N)] (hK : 0 < K)
    (hXm : ∀ i : Fin N, AEStronglyMeasurable (X i.1) μ)
    (hX : ∀ i : Fin N, subGaussianTailCondition (X i.1) μ K) :
    Integrable (finiteMaxAbs (logNormalizedInitialSegment X N)) μ := by
  classical
  let Y : Fin N → Ω → ℝ := logNormalizedInitialSegment X N
  have hYm : ∀ i : Fin N, AEStronglyMeasurable (Y i) μ := by
    simpa [Y] using
      logNormalizedInitialSegment_aestronglyMeasurable
        (μ := μ) (X := X) (N := N) hXm
  have hYtail : ∀ i : Fin N, subGaussianTailCondition (Y i) μ K := by
    simpa [Y] using
      logNormalizedInitialSegment_subGaussianTailCondition
        (μ := μ) (X := X) (K := K) (N := N) hK hX
  have hYmom : ∀ i : Fin N, subGaussianMomentCondition (Y i) μ (4 * K) := by
    intro i
    exact subGaussianMomentCondition_of_subGaussianTailCondition (hYm i) (hYtail i)
  simpa [Y] using
    integrable_finiteMaxAbs_of_subGaussianMomentCondition
      (μ := μ) (X := Y) hYmom

/-- HDP Exercise 2.5.10, infinite normalized-maximum form in extended
expectation: no independence is required, and the pointwise supremum of the
finite initial normalized maxima has `ENNReal` expectation at most `4K`. -/
theorem lintegral_logNormalizedMaxSup_le_four_mul
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {K : ℝ}
    (hK : 0 < K)
    (hXm : ∀ i : ℕ, AEStronglyMeasurable (X i) μ)
    (hX : ∀ i : ℕ, subGaussianTailCondition (X i) μ K) :
    ∫⁻ ω, logNormalizedMaxSup X ω ∂μ ≤ ENNReal.ofReal (4 * K) := by
  classical
  let F : ℕ → Ω → ℝ≥0∞ := logNormalizedMaxApprox X
  have hF_meas : ∀ n, AEMeasurable (F n) μ := by
    intro n
    have hXm_n :
        ∀ i : Fin (n + 1),
          AEStronglyMeasurable (X i.1) μ := fun i => hXm i.1
    have hY_meas :
        AEMeasurable
          (finiteMaxAbs (logNormalizedInitialSegment X (n + 1))) μ := by
      exact aemeasurable_finiteMaxAbs
        (μ := μ)
        (X := logNormalizedInitialSegment X (n + 1))
        (fun i =>
          (logNormalizedInitialSegment_aestronglyMeasurable
            (μ := μ) (X := X) (N := n + 1) hXm_n i).aemeasurable)
    simpa [F, logNormalizedMaxApprox, logNormalizedMaxApproxReal]
      using hY_meas.ennreal_ofReal
  have hF_mono : ∀ᵐ ω ∂μ, Monotone fun n => F n ω :=
    Filter.Eventually.of_forall fun ω => by
      simpa [F] using logNormalizedMaxApprox_mono X ω
  have hmc :
      ∫⁻ ω, (⨆ n : ℕ, F n ω) ∂μ =
        ⨆ n : ℕ, ∫⁻ ω, F n ω ∂μ :=
    MeasureTheory.lintegral_iSup' (μ := μ) hF_meas hF_mono
  calc
    ∫⁻ ω, logNormalizedMaxSup X ω ∂μ
        = ∫⁻ ω, (⨆ n : ℕ, F n ω) ∂μ := by
          simp [logNormalizedMaxSup, F]
    _ = ⨆ n : ℕ, ∫⁻ ω, F n ω ∂μ := hmc
    _ ≤ ENNReal.ofReal (4 * K) := by
      refine iSup_le ?_
      intro n
      have hXm_n :
          ∀ i : Fin (n + 1),
            AEStronglyMeasurable (X i.1) μ := fun i => hXm i.1
      have hX_n :
          ∀ i : Fin (n + 1),
            subGaussianTailCondition (X i.1) μ K := fun i => hX i.1
      have hInt :
          Integrable
            (finiteMaxAbs (logNormalizedInitialSegment X (n + 1))) μ :=
        integrable_finiteLogNormalizedMax
          (μ := μ) (X := X) (K := K) (N := n + 1)
          hK hXm_n hX_n
      have hnonneg :
          0 ≤ᵐ[μ]
            fun ω => finiteMaxAbs (logNormalizedInitialSegment X (n + 1)) ω :=
        Filter.Eventually.of_forall fun ω =>
          finiteMaxAbs_nonneg (logNormalizedInitialSegment X (n + 1)) ω
      have hlin :
          ∫⁻ ω, F n ω ∂μ =
            ENNReal.ofReal
              (∫ ω, finiteMaxAbs (logNormalizedInitialSegment X (n + 1)) ω ∂μ) := by
        have hEq :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            (μ := μ) hInt hnonneg).symm
        simpa [F, logNormalizedMaxApprox, logNormalizedMaxApproxReal] using hEq
      have hreal :
          ∫ ω, finiteMaxAbs (logNormalizedInitialSegment X (n + 1)) ω ∂μ
            ≤ 4 * K :=
        finiteLogNormalizedMax_integral_le_four_mul
          (μ := μ) (X := X) (K := K) (N := n + 1)
          hK hXm_n hX_n
      calc
        ∫⁻ ω, F n ω ∂μ
            = ENNReal.ofReal
              (∫ ω, finiteMaxAbs (logNormalizedInitialSegment X (n + 1)) ω ∂μ) := hlin
        _ ≤ ENNReal.ofReal (4 * K) := ENNReal.ofReal_le_ofReal hreal

/-- HDP Exercise 2.5.10, infinite normalized-maximum form stated with the
book's `ψ₂`-norm scale. If every coordinate satisfies
`‖Xᵢ‖_{ψ₂} ≤ K`, then the extended expectation of the pointwise supremum of
the normalized finite initial maxima is at most `4K`. No independence is used. -/
theorem lintegral_logNormalizedMaxSup_le_four_mul_subGaussianNorm
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {K : ℝ}
    (hK : 0 ≤ K)
    (hXm : ∀ i : ℕ, AEStronglyMeasurable (X i) μ)
    (hXsg : ∀ i : ℕ, IsSubGaussian (X i) μ)
    (hNorm : ∀ i : ℕ, subGaussianNorm (X i) μ ≤ K) :
    ∫⁻ ω, logNormalizedMaxSup X ω ∂μ ≤ ENNReal.ofReal (4 * K) := by
  classical
  let F : ℕ → Ω → ℝ≥0∞ := logNormalizedMaxApprox X
  have hF_meas : ∀ n, AEMeasurable (F n) μ := by
    intro n
    have hXm_n :
        ∀ i : Fin (n + 1),
          AEStronglyMeasurable (X i.1) μ := fun i => hXm i.1
    have hY_meas :
        AEMeasurable
          (finiteMaxAbs (logNormalizedInitialSegment X (n + 1))) μ := by
      exact aemeasurable_finiteMaxAbs
        (μ := μ)
        (X := logNormalizedInitialSegment X (n + 1))
        (fun i =>
          (logNormalizedInitialSegment_aestronglyMeasurable
            (μ := μ) (X := X) (N := n + 1) hXm_n i).aemeasurable)
    simpa [F, logNormalizedMaxApprox, logNormalizedMaxApproxReal]
      using hY_meas.ennreal_ofReal
  have hF_mono : ∀ᵐ ω ∂μ, Monotone fun n => F n ω :=
    Filter.Eventually.of_forall fun ω => by
      simpa [F] using logNormalizedMaxApprox_mono X ω
  have hmc :
      ∫⁻ ω, (⨆ n : ℕ, F n ω) ∂μ =
        ⨆ n : ℕ, ∫⁻ ω, F n ω ∂μ :=
    MeasureTheory.lintegral_iSup' (μ := μ) hF_meas hF_mono
  calc
    ∫⁻ ω, logNormalizedMaxSup X ω ∂μ
        = ∫⁻ ω, (⨆ n : ℕ, F n ω) ∂μ := by
          simp [logNormalizedMaxSup, F]
    _ = ⨆ n : ℕ, ∫⁻ ω, F n ω ∂μ := hmc
    _ ≤ ENNReal.ofReal (4 * K) := by
      refine iSup_le ?_
      intro n
      have hXm_n :
          ∀ i : Fin (n + 1),
            AEStronglyMeasurable (X i.1) μ := fun i => hXm i.1
      have hXsg_n :
          ∀ i : Fin (n + 1),
            IsSubGaussian (X i.1) μ := fun i => hXsg i.1
      have hNorm_n :
          ∀ i : Fin (n + 1),
            subGaussianNorm (X i.1) μ ≤ K := fun i => hNorm i.1
      let R : ℝ := K + 1
      have hRpos : 0 < R := by
        dsimp [R]
        linarith
      have hTail_R :
          ∀ i : Fin (n + 1),
            subGaussianTailCondition (X i.1) μ R := by
        intro i
        exact subGaussianTailCondition_of_subGaussianNorm_lt
          (μ := μ) (X := X i.1) (K := R)
          (hXsg_n i) ((hNorm_n i).trans_lt (by dsimp [R]; linarith))
      have hInt :
          Integrable
            (finiteMaxAbs (logNormalizedInitialSegment X (n + 1))) μ :=
        integrable_finiteLogNormalizedMax
          (μ := μ) (X := X) (K := R) (N := n + 1)
          hRpos hXm_n hTail_R
      have hnonneg :
          0 ≤ᵐ[μ]
            fun ω => finiteMaxAbs (logNormalizedInitialSegment X (n + 1)) ω :=
        Filter.Eventually.of_forall fun ω =>
          finiteMaxAbs_nonneg (logNormalizedInitialSegment X (n + 1)) ω
      have hlin :
          ∫⁻ ω, F n ω ∂μ =
            ENNReal.ofReal
              (∫ ω, finiteMaxAbs (logNormalizedInitialSegment X (n + 1)) ω ∂μ) := by
        have hEq :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            (μ := μ) hInt hnonneg).symm
        simpa [F, logNormalizedMaxApprox, logNormalizedMaxApproxReal] using hEq
      have hreal :
          ∫ ω, finiteMaxAbs (logNormalizedInitialSegment X (n + 1)) ω ∂μ
            ≤ 4 * K :=
        finiteLogNormalizedMax_integral_le_four_mul_subGaussianNorm
          (μ := μ) (X := X) (K := K) (N := n + 1)
          hK hXm_n hXsg_n hNorm_n
      calc
        ∫⁻ ω, F n ω ∂μ
            = ENNReal.ofReal
              (∫ ω, finiteMaxAbs (logNormalizedInitialSegment X (n + 1)) ω ∂μ) := hlin
        _ ≤ ENNReal.ofReal (4 * K) := ENNReal.ofReal_le_ofReal hreal

end FiniteMaxValue

end Maxima

section Centering

/-- HDP equation (2.19): centering can only decrease the `L²` norm. -/
theorem l2Norm_centered_le_l2Norm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    (hXm : AEStronglyMeasurable X μ) :
    l2Norm (fun ω => X ω - μ[X]) μ ≤ l2Norm X μ := by
  unfold l2Norm
  refine Real.sqrt_le_sqrt ?_
  calc
    μ[fun ω => (X ω - μ[X]) ^ 2]
        = Var[X; μ] := by
          rw [ProbabilityTheory.variance_eq_integral hXm.aemeasurable]
    _ ≤ μ[X ^ 2] :=
      ProbabilityTheory.variance_le_expectation_sq hXm
    _ = μ[fun ω => X ω ^ 2] := by
      rfl

/-- Addition closure for sub-gaussian random variables in the `ψ₂` Orlicz
sense. -/
theorem isSubGaussian_add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hXsg : IsSubGaussian X μ) (hYsg : IsSubGaussian Y μ) :
    IsSubGaussian (fun ω => X ω + Y ω) μ := by
  rcases hXsg with ⟨K, hK⟩
  rcases hYsg with ⟨L, hL⟩
  exact ⟨K + L, subGaussianOrliczCondition_add hXm hYm hK hL⟩

/-- Constant random variables are sub-gaussian. -/
theorem isSubGaussian_const
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (a : ℝ) :
    IsSubGaussian (fun _ω : Ω => a) μ := by
  by_cases ha : a = 0
  · rw [ha]
    exact isSubGaussian_of_subGaussianOrliczCondition
      (subGaussianOrliczCondition_zero (μ := μ) (K := 1) (by norm_num))
  · have hB : 0 < |a| := abs_pos.mpr ha
    refine isSubGaussian_of_subGaussianOrliczCondition
      (K := |a| / Real.sqrt (Real.log 2)) ?_
    refine subGaussianOrliczCondition_of_ae_abs_le_scaled
      (μ := μ) (X := fun _ω : Ω => a) (B := |a|)
      (by fun_prop) hB ?_
    exact Filter.Eventually.of_forall fun _ω => le_rfl

/-- A constant random variable has `ψ₂` norm bounded by the bounded-variable
scale from Example 2.5.8(c). -/
theorem subGaussianNorm_const_le_abs_div_sqrt_log_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (a : ℝ) :
    subGaussianNorm (fun _ω : Ω => a) μ ≤ |a| / Real.sqrt (Real.log 2) := by
  by_cases ha : a = 0
  · rw [ha]
    simp [subGaussianNorm_zero]
  · have hB : 0 < |a| := abs_pos.mpr ha
    refine subGaussianNorm_le_of_ae_abs_le_scaled
      (μ := μ) (X := fun _ω : Ω => a) (B := |a|)
      (by fun_prop) hB ?_
    exact Filter.Eventually.of_forall fun _ω => le_rfl

/-- An admissible `ψ₂` Orlicz scale controls the absolute mean. This is the
`p = 1` moment-growth consequence used in HDP Lemma 2.6.8. -/
theorem abs_integral_le_two_mul_of_subGaussianOrliczCondition
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hXm : AEStronglyMeasurable X μ)
    (hX : subGaussianOrliczCondition X μ K) :
    |μ[X]| ≤ 2 * K := by
  have hMom : subGaussianMomentCondition X μ (2 * K) :=
    subGaussianMomentCondition_of_subGaussianOrliczCondition (μ := μ) hXm hX
  have hp : (1 : ℝ) ≤ ((1 : ℝ≥0) : ℝ) := by norm_num
  rcases hMom.2 1 hp with ⟨hmem, hle⟩
  have h_rhs_toReal :
      (ENNReal.ofReal (2 * K * Real.sqrt ((1 : ℝ≥0) : ℝ))).toReal = 2 * K := by
    rw [ENNReal.toReal_ofReal]
    · norm_num
    · have hKpos : 0 < K := hX.1
      positivity
  have hlp_real : MeasureTheory.lpNorm X (1 : ℝ≥0∞) μ ≤ 2 * K := by
    have hle_toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [MeasureTheory.toReal_eLpNorm hXm, h_rhs_toReal] at hle_toReal
    simpa using hle_toReal
  have hint_abs : μ[fun ω => |X ω|] ≤ 2 * K := by
    have hlp_one := MeasureTheory.lpNorm_one_eq_integral_norm hXm
    rw [hlp_one] at hlp_real
    simpa [Real.norm_eq_abs] using hlp_real
  exact abs_integral_le_integral_abs.trans hint_abs

/-- The `ψ₂` norm controls the absolute mean. -/
theorem abs_integral_le_two_mul_subGaussianNorm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    (hXm : AEStronglyMeasurable X μ)
    (hXsg : IsSubGaussian X μ) :
    |μ[X]| ≤ 2 * subGaussianNorm X μ := by
  let S : Set ℝ := {K : ℝ | subGaussianOrliczCondition X μ K}
  have hXset : S.Nonempty := by
    rcases hXsg with ⟨K, hK⟩
    exact ⟨K, hK⟩
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro r hr
  have hgap : 0 < r / 2 - subGaussianNorm X μ := by linarith
  obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos (s := S) hXset hgap
  have hK_cond : subGaussianOrliczCondition X μ K := hK
  have hKlt' : K < subGaussianNorm X μ + (r / 2 - subGaussianNorm X μ) := by
    change K < subGaussianNorm X μ + (r / 2 - subGaussianNorm X μ)
    exact hKlt
  have hKlt_half : K < r / 2 := by linarith
  have hmeanK : |μ[X]| ≤ 2 * K :=
    abs_integral_le_two_mul_of_subGaussianOrliczCondition hXm hK_cond
  have h2Klt : 2 * K < r := by linarith
  exact hmeanK.trans h2Klt.le

/-- The explicit absolute constant used in the formalized form of HDP
Lemma 2.6.8. -/
def subGaussianCenteringConstant : ℝ :=
  1 + 2 / Real.sqrt (Real.log 2)

/-- The centering constant in Lemma 2.6.8 is positive. -/
theorem subGaussianCenteringConstant_pos : 0 < subGaussianCenteringConstant := by
  have hlog2_pos : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsqrt_pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hlog2_pos
  unfold subGaussianCenteringConstant
  positivity

/-- HDP Lemma 2.6.8, norm estimate: centering preserves sub-gaussianity with
an absolute constant. -/
theorem subGaussianNorm_centered_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    (hXm : AEStronglyMeasurable X μ)
    (hXsg : IsSubGaussian X μ) :
    subGaussianNorm (fun ω => X ω - μ[X]) μ
      ≤ subGaussianCenteringConstant * subGaussianNorm X μ := by
  have hlog2_pos : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsqrt_pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hlog2_pos
  let m : ℝ := μ[X]
  let Y : Ω → ℝ := fun _ω => -m
  have hconst_sg : IsSubGaussian Y μ := by
    simpa [Y, m] using isSubGaussian_const (μ := μ) (-μ[X])
  have hcenter_eq :
      (fun ω => X ω - μ[X]) = fun ω => X ω + Y ω := by
    funext ω
    dsimp [Y, m]
    ring
  have hadd :
      subGaussianNorm (fun ω => X ω + Y ω) μ
        ≤ subGaussianNorm X μ + subGaussianNorm Y μ :=
    subGaussianNorm_add_le (μ := μ)
      (X := X) (Y := Y)
      hXm.aemeasurable (by dsimp [Y]; fun_prop) hXsg hconst_sg
  have hconst_bound :
      subGaussianNorm Y μ
        ≤ |μ[X]| / Real.sqrt (Real.log 2) := by
    have h := subGaussianNorm_const_le_abs_div_sqrt_log_two
      (μ := μ) (-μ[X])
    simpa [Y, m] using h
  have hmean_bound : |μ[X]| ≤ 2 * subGaussianNorm X μ :=
    abs_integral_le_two_mul_subGaussianNorm hXm hXsg
  have hmean_scaled :
      |μ[X]| / Real.sqrt (Real.log 2)
        ≤ (2 * subGaussianNorm X μ) / Real.sqrt (Real.log 2) :=
    div_le_div_of_nonneg_right hmean_bound hsqrt_pos.le
  rw [hcenter_eq]
  calc
    subGaussianNorm (fun ω => X ω + Y ω) μ
        ≤ subGaussianNorm X μ + subGaussianNorm Y μ := hadd
    _ ≤ subGaussianNorm X μ + |μ[X]| / Real.sqrt (Real.log 2) :=
      add_le_add le_rfl hconst_bound
    _ ≤ subGaussianNorm X μ
        + (2 * subGaussianNorm X μ) / Real.sqrt (Real.log 2) :=
      add_le_add le_rfl hmean_scaled
    _ = subGaussianCenteringConstant * subGaussianNorm X μ := by
      unfold subGaussianCenteringConstant
      ring

/-- HDP Lemma 2.6.8, predicate form: centering preserves sub-gaussianity. -/
theorem isSubGaussian_centered
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    (hXm : AEMeasurable X μ)
    (hXsg : IsSubGaussian X μ) :
    IsSubGaussian (fun ω => X ω - μ[X]) μ := by
  let m : ℝ := μ[X]
  let Y : Ω → ℝ := fun _ω => -m
  have hconst_sg : IsSubGaussian Y μ := by
    simpa [Y, m] using isSubGaussian_const (μ := μ) (-μ[X])
  have hcenter_eq :
      (fun ω => X ω - μ[X]) = fun ω => X ω + Y ω := by
    funext ω
    dsimp [Y, m]
    ring
  rw [hcenter_eq]
  exact isSubGaussian_add (μ := μ)
    (X := X) (Y := Y) hXm (by dsimp [Y]; fun_prop) hXsg hconst_sg

/-- The Bernoulli parameter used in the concrete HDP Exercise 2.6.9
counterexample. -/
theorem subGaussianCenteringCounterexampleProb_le_one :
    (49 / 50 : ℝ≥0) ≤ 1 := by
  rw [← NNReal.coe_le_coe]
  norm_num

/-- A two-point probability mass function for the HDP Exercise 2.6.9
counterexample. -/
def subGaussianCenteringCounterexamplePMF : PMF Bool :=
  PMF.bernoulli (49 / 50 : ℝ≥0) subGaussianCenteringCounterexampleProb_le_one

/-- The two-point probability space for the HDP Exercise 2.6.9
counterexample. -/
def subGaussianCenteringCounterexampleMeasure : Measure Bool :=
  subGaussianCenteringCounterexamplePMF.toMeasure

instance : IsProbabilityMeasure subGaussianCenteringCounterexampleMeasure := by
  rw [subGaussianCenteringCounterexampleMeasure]
  infer_instance

/-- The random variable used in the HDP Exercise 2.6.9 counterexample. -/
def subGaussianCenteringCounterexample (b : Bool) : ℝ :=
  if b then (17 / 10 : ℝ) else (-24 / 5 : ℝ)

/-- The two-point counterexample random variable is measurable. -/
theorem subGaussianCenteringCounterexample_measurable :
    Measurable subGaussianCenteringCounterexample := by
  simpa [subGaussianCenteringCounterexample] using
    (SimpleFunc.ofFinite subGaussianCenteringCounterexample).measurable

/-- The two-point counterexample random variable is a.e.-measurable. -/
theorem subGaussianCenteringCounterexample_aemeasurable :
    AEMeasurable subGaussianCenteringCounterexample
      subGaussianCenteringCounterexampleMeasure :=
  subGaussianCenteringCounterexample_measurable.aemeasurable

/-- The exact mean of the HDP Exercise 2.6.9 two-point variable. -/
theorem subGaussianCenteringCounterexample_integral :
    ∫ b, subGaussianCenteringCounterexample b
        ∂subGaussianCenteringCounterexampleMeasure = (157 / 100 : ℝ) := by
  rw [subGaussianCenteringCounterexampleMeasure,
    subGaussianCenteringCounterexamplePMF, PMF.integral_eq_sum]
  simp [subGaussianCenteringCounterexample, PMF.bernoulli_apply]
  rw [NNReal.coe_sub subGaussianCenteringCounterexampleProb_le_one]
  norm_num

/-- A rational upper certificate for `exp`, used to make the two-point
counterexample fully rigorous without decimal approximations. -/
theorem real_exp_le_inv_one_sub_div_pow {x : ℝ} {n : ℕ} (hn : 0 < n)
    (hx : x < n) :
    Real.exp x ≤ ((1 - x / (n : ℝ)) ^ n)⁻¹ := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbase_pos : 0 < 1 - x / (n : ℝ) := by
    rw [sub_pos]
    exact (div_lt_one hnreal).2 hx
  have hpow_pos : 0 < (1 - x / (n : ℝ)) ^ n :=
    pow_pos hbase_pos n
  have hle := Real.one_sub_div_pow_le_exp_neg (n := n) (t := x) hx.le
  have hinv : 1 / Real.exp (-x) ≤ 1 / ((1 - x / (n : ℝ)) ^ n) := by
    exact (one_div_le_one_div (Real.exp_pos _) hpow_pos).mpr hle
  simpa [Real.exp_neg, one_div] using hinv

theorem subGaussianCenteringCounterexample_complement :
    (((1 : ℝ≥0) - (49 / 50 : ℝ≥0) : ℝ≥0) : ℝ) = (1 / 50 : ℝ) := by
  rw [NNReal.coe_sub subGaussianCenteringCounterexampleProb_le_one]
  norm_num

/-- Exact expansion of the Orlicz integral for the uncentered two-point
counterexample at scale `14 / 5`. -/
theorem subGaussianCenteringCounterexample_exp_integral :
    ∫ b, Real.exp
        (subGaussianCenteringCounterexample b ^ 2 / (14 / 5 : ℝ) ^ 2)
        ∂subGaussianCenteringCounterexampleMeasure =
      (49 / 50 : ℝ) *
          Real.exp ((17 / 10 : ℝ) ^ 2 / (14 / 5 : ℝ) ^ 2)
        + (((1 : ℝ≥0) - (49 / 50 : ℝ≥0) : ℝ≥0) : ℝ) *
          Real.exp ((-24 / 5 : ℝ) ^ 2 / (14 / 5 : ℝ) ^ 2) := by
  rw [subGaussianCenteringCounterexampleMeasure,
    subGaussianCenteringCounterexamplePMF, PMF.integral_eq_sum]
  simp [subGaussianCenteringCounterexample, PMF.bernoulli_apply]

/-- The uncentered variable has admissible `ψ₂` scale `14 / 5`. -/
theorem subGaussianCenteringCounterexample_exp_integral_le_two :
    ∫ b, Real.exp
        (subGaussianCenteringCounterexample b ^ 2 / (14 / 5 : ℝ) ^ 2)
        ∂subGaussianCenteringCounterexampleMeasure ≤ 2 := by
  rw [subGaussianCenteringCounterexample_exp_integral,
    subGaussianCenteringCounterexample_complement]
  have h1 :
      Real.exp ((17 / 10 : ℝ) ^ 2 / (14 / 5 : ℝ) ^ 2)
        ≤ ((1 - (((17 / 10 : ℝ) ^ 2 / (14 / 5 : ℝ) ^ 2) / (20 : ℝ)))
            ^ 20)⁻¹ :=
    real_exp_le_inv_one_sub_div_pow (n := 20) (by norm_num) (by norm_num)
  have h2 :
      Real.exp ((-24 / 5 : ℝ) ^ 2 / (14 / 5 : ℝ) ^ 2)
        ≤ ((1 - (((-24 / 5 : ℝ) ^ 2 / (14 / 5 : ℝ) ^ 2) / (20 : ℝ)))
            ^ 20)⁻¹ :=
    real_exp_le_inv_one_sub_div_pow (n := 20) (by norm_num) (by norm_num)
  calc
    (49 / 50 : ℝ) *
          Real.exp ((17 / 10 : ℝ) ^ 2 / (14 / 5 : ℝ) ^ 2)
        + (1 / 50 : ℝ) *
          Real.exp ((-24 / 5 : ℝ) ^ 2 / (14 / 5 : ℝ) ^ 2)
        ≤ (49 / 50 : ℝ) *
            ((1 - (((17 / 10 : ℝ) ^ 2 / (14 / 5 : ℝ) ^ 2) / (20 : ℝ)))
              ^ 20)⁻¹
          + (1 / 50 : ℝ) *
            ((1 - (((-24 / 5 : ℝ) ^ 2 / (14 / 5 : ℝ) ^ 2) / (20 : ℝ)))
              ^ 20)⁻¹ := by
          gcongr
    _ ≤ 2 := by norm_num

/-- The uncentered variable in Exercise 2.6.9 is sub-gaussian. -/
theorem subGaussianCenteringCounterexample_orliczCondition :
    subGaussianOrliczCondition subGaussianCenteringCounterexample
      subGaussianCenteringCounterexampleMeasure (14 / 5) := by
  refine ⟨by norm_num, ?_, subGaussianCenteringCounterexample_exp_integral_le_two⟩
  rw [subGaussianCenteringCounterexampleMeasure]
  simp

/-- Upper bound for the uncentered `ψ₂` norm in the Exercise 2.6.9
counterexample. -/
theorem subGaussianCenteringCounterexample_norm_le :
    subGaussianNorm subGaussianCenteringCounterexample
      subGaussianCenteringCounterexampleMeasure ≤ (14 / 5 : ℝ) :=
  subGaussianNorm_le_of_subGaussianOrliczCondition
    subGaussianCenteringCounterexample_orliczCondition

/-- Exact expansion of the centered Orlicz integral in the Exercise 2.6.9
counterexample. -/
theorem subGaussianCenteringCounterexample_centered_exp_integral {K : ℝ} :
    ∫ b, Real.exp
        ((subGaussianCenteringCounterexample b -
            ∫ b, subGaussianCenteringCounterexample b
              ∂subGaussianCenteringCounterexampleMeasure) ^ 2 / K ^ 2)
        ∂subGaussianCenteringCounterexampleMeasure =
      (49 / 50 : ℝ) * Real.exp (((13 / 100 : ℝ) ^ 2) / K ^ 2)
        + (((1 : ℝ≥0) - (49 / 50 : ℝ≥0) : ℝ≥0) : ℝ) *
            Real.exp (((-637 / 100 : ℝ) ^ 2) / K ^ 2) := by
  rw [subGaussianCenteringCounterexample_integral]
  rw [subGaussianCenteringCounterexampleMeasure,
    subGaussianCenteringCounterexamplePMF, PMF.integral_eq_sum]
  simp [subGaussianCenteringCounterexample, PMF.bernoulli_apply]
  ring_nf

theorem subGaussianCenteringCounterexample_rare_exp_lower {K : ℝ}
    (hKpos : 0 < K) (hKlt : K < 29 / 10) :
    (100 : ℝ) < Real.exp (((637 / 100 : ℝ) ^ 2) / K ^ 2) := by
  have hqexp : (100 : ℝ) < Real.exp (405769 / 84100 : ℝ) := by
    have hsum :
        (100 : ℝ) <
          ∑ i ∈ Finset.range 8,
            ((405769 / 84100 : ℝ) ^ i / i.factorial) := by
      norm_num
    exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 8)
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hKpos
  have hBpos : 0 < (29 / 10 : ℝ) := by norm_num
  have hKsq_lt : K ^ 2 < (29 / 10 : ℝ) ^ 2 := by
    exact sq_lt_sq.mpr
      (by simpa [abs_of_pos hKpos, abs_of_pos hBpos] using hKlt)
  have hnum_pos : 0 < (637 / 100 : ℝ) ^ 2 := by norm_num
  have hquot :
      (405769 / 84100 : ℝ) < ((637 / 100 : ℝ) ^ 2) / K ^ 2 := by
    have h := div_lt_div_of_pos_left hnum_pos hKsq_pos hKsq_lt
    norm_num at h ⊢
    exact h
  exact hqexp.trans (Real.exp_lt_exp.mpr hquot)

/-- Below scale `29 / 10`, the centered Orlicz integral of the Exercise 2.6.9
counterexample is already larger than `2`. -/
theorem subGaussianCenteringCounterexample_centered_exp_gt_two_of_lt {K : ℝ}
    (hKpos : 0 < K) (hKlt : K < 29 / 10) :
    2 <
      ∫ b, Real.exp
        ((subGaussianCenteringCounterexample b -
            ∫ b, subGaussianCenteringCounterexample b
              ∂subGaussianCenteringCounterexampleMeasure) ^ 2 / K ^ 2)
        ∂subGaussianCenteringCounterexampleMeasure := by
  rw [subGaussianCenteringCounterexample_centered_exp_integral]
  have hrare :
      (100 : ℝ) < Real.exp (((-637 / 100 : ℝ) ^ 2) / K ^ 2) := by
    have hsquare :
        ((-637 / 100 : ℝ) ^ 2) = ((637 / 100 : ℝ) ^ 2) := by
      norm_num
    simpa [hsquare] using
      subGaussianCenteringCounterexample_rare_exp_lower hKpos hKlt
  rw [subGaussianCenteringCounterexample_complement]
  have hrare_weighted :
      (2 : ℝ) < (1 / 50 : ℝ) *
        Real.exp (((-637 / 100 : ℝ) ^ 2) / K ^ 2) := by
    nlinarith
  have hcommon_nonneg :
      0 ≤ (49 / 50 : ℝ) *
        Real.exp (((13 / 100 : ℝ) ^ 2) / K ^ 2) := by
    positivity
  nlinarith

/-- Lower bound for the centered `ψ₂` norm in the Exercise 2.6.9
counterexample. -/
theorem subGaussianCenteringCounterexample_centered_norm_ge :
    (29 / 10 : ℝ) ≤
      subGaussianNorm
        (fun b => subGaussianCenteringCounterexample b -
          ∫ b, subGaussianCenteringCounterexample b
            ∂subGaussianCenteringCounterexampleMeasure)
        subGaussianCenteringCounterexampleMeasure := by
  unfold subGaussianNorm
  refine le_csInf ?hne ?hlower
  · have hsg :
        IsSubGaussian
          (fun b => subGaussianCenteringCounterexample b -
            ∫ b, subGaussianCenteringCounterexample b
              ∂subGaussianCenteringCounterexampleMeasure)
          subGaussianCenteringCounterexampleMeasure := by
      exact isSubGaussian_centered
        (μ := subGaussianCenteringCounterexampleMeasure)
        (X := subGaussianCenteringCounterexample)
        subGaussianCenteringCounterexample_aemeasurable
        (isSubGaussian_of_subGaussianOrliczCondition
          subGaussianCenteringCounterexample_orliczCondition)
    rcases hsg with ⟨K, hK⟩
    exact ⟨K, hK⟩
  · intro K hK
    by_contra hnot
    have hKlt : K < 29 / 10 := lt_of_not_ge hnot
    have hgt :=
      subGaussianCenteringCounterexample_centered_exp_gt_two_of_lt hK.1 hKlt
    exact not_lt_of_ge hK.2.2 hgt

/-- HDP Exercise 2.6.9: centering does not satisfy the `ψ₂` norm inequality
with constant `1`.  This explicit two-point sub-gaussian variable has
strictly larger centered `ψ₂` norm. -/
theorem subGaussianCentering_not_contracting_constant_one :
    subGaussianNorm subGaussianCenteringCounterexample
        subGaussianCenteringCounterexampleMeasure <
      subGaussianNorm
        (fun b => subGaussianCenteringCounterexample b -
          ∫ b, subGaussianCenteringCounterexample b
            ∂subGaussianCenteringCounterexampleMeasure)
        subGaussianCenteringCounterexampleMeasure := by
  have hlt : (14 / 5 : ℝ) < 29 / 10 := by norm_num
  exact lt_of_le_of_lt subGaussianCenteringCounterexample_norm_le
    (hlt.trans_le subGaussianCenteringCounterexample_centered_norm_ge)

/-- Existential form of HDP Exercise 2.6.9. -/
theorem exists_subGaussian_centering_not_contracting_constant_one :
    ∃ μ : Measure Bool, IsProbabilityMeasure μ ∧ ∃ X : Bool → ℝ,
      IsSubGaussian X μ ∧
        subGaussianNorm X μ <
          subGaussianNorm (fun b => X b - ∫ b, X b ∂μ) μ := by
  refine ⟨subGaussianCenteringCounterexampleMeasure, inferInstance,
    subGaussianCenteringCounterexample, ?_, ?_⟩
  · exact isSubGaussian_of_subGaussianOrliczCondition
      subGaussianCenteringCounterexample_orliczCondition
  · exact subGaussianCentering_not_contracting_constant_one

end Centering

section Sums

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {ι : Type*} [Fintype ι]

/-- HDP equation (2.18): a finite sum of independent centered Gaussian
random variables is centered Gaussian, with variance equal to the sum of the
variances. -/
theorem gaussianReal_sum_of_iIndepFun
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {v : ι → ℝ≥0}
    (hindep : iIndepFun X μ)
    (hX : ∀ i, μ.map (X i) = ProbabilityTheory.gaussianReal 0 (v i)) :
    μ.map (fun ω => ∑ i, X i ω)
      = ProbabilityTheory.gaussianReal 0 (∑ i, v i) := by
  classical
  have hXm : ∀ i, AEMeasurable (X i) μ := by
    intro i
    apply AEMeasurable.of_map_ne_zero
    rw [hX i]
    intro hzero
    have hmass :
        ProbabilityTheory.gaussianReal 0 (v i) Set.univ = 1 := by
      simp
    rw [hzero] at hmass
    simp at hmass
  haveI : IsFiniteMeasure (μ.map (fun ω => ∑ i, X i ω)) :=
    Measure.isFiniteMeasure_map μ (fun ω => ∑ i, X i ω)
  have hsum_fun :
      (∑ i, X i) = fun ω => ∑ i, X i ω := by
    funext ω
    simp
  refine Measure.ext_of_charFun ?_
  ext t
  calc
    charFun (μ.map (fun ω => ∑ i, X i ω)) t
        = ∏ i, charFun (μ.map (X i)) t := by
      rw [← hsum_fun]
      simpa using congr_fun (hindep.charFun_map_sum_eq_prod hXm) t
    _ = ∏ i, charFun (ProbabilityTheory.gaussianReal 0 (v i)) t := by
      simp [hX]
    _ = charFun (ProbabilityTheory.gaussianReal 0 (∑ i, v i)) t := by
      simp_rw [ProbabilityTheory.charFun_gaussianReal]
      rw [← Complex.exp_sum]
      congr 1
      simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
        Finset.sum_neg_distrib]
      congr 1
      rw [← Finset.sum_div, ← Finset.sum_mul]
      rw [NNReal.coe_sum]
      rw [Complex.ofReal_sum]

/-- HDP Proposition 2.6.1 in MGF-proxy form: a finite sum of independent
mean-zero sub-gaussian variables is sub-gaussian, with proxy equal to the sum
of the individual proxies. -/
theorem hasSubgaussianMGF_sum_of_iIndepFun
    {X : ι → Ω → ℝ} {c : ι → ℝ≥0}
    (hindep : iIndepFun X μ)
    (hX : ∀ i, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (fun ω => ∑ i, X i ω) (∑ i, c i) μ := by
  classical
  simpa using
    (ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
      (μ := μ) (X := X) (c := c) (s := (Finset.univ : Finset ι))
      hindep (by intro i _hi; exact hX i))

/-- HDP Theorem 2.6.2 in MGF-proxy form. -/
theorem general_hoeffding_sum
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {c : ι → ℝ≥0}
    (hindep : iIndepFun X μ)
    (hX : ∀ i, HasSubgaussianMGF (X i) (c i) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp (-(t ^ 2) / (2 * subgaussianProxySum c)) := by
  classical
  have hsum :=
    hasSubgaussianMGF_sum_of_iIndepFun
      (μ := μ) (X := X) (c := c) hindep hX
  have htail :=
    hasSubgaussianMGF_measure_abs_ge_le
      (μ := μ) (X := fun ω => ∑ i, X i ω) hsum (t := t) ht
  simpa [subgaussianProxySum] using htail

/-- HDP Theorem 2.6.3, weighted general Hoeffding inequality, with explicit
per-variable MGF proxies. -/
theorem general_hoeffding_weighted
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {c : ι → ℝ≥0} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hX : ∀ i, HasSubgaussianMGF (X i) (c i) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-(t ^ 2) / (2 * weightedSubgaussianProxySum a c)) := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  let d : ι → ℝ≥0 := fun i => ⟨a i ^ 2, sq_nonneg (a i)⟩ * c i
  have hindepY : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hindep.comp (fun i x => a i * x) (fun _ => by fun_prop)
  have hY : ∀ i, HasSubgaussianMGF (Y i) (d i) μ := by
    intro i
    simpa [Y, d] using (hX i).const_mul (a i)
  have htail :=
    general_hoeffding_sum
      (μ := μ) (X := Y) (c := d) hindepY hY (t := t) ht
  simpa [weightedSubgaussianProxySum, subgaussianProxySum, d, Y,
    mul_comm, mul_left_comm, mul_assoc] using htail

/-- HDP Theorem 2.6.3 in the common uniform proxy form
`P{|∑ aᵢXᵢ| ≥ t} ≤ 2 exp(-t² / (2K²‖a‖₂²))`. -/
theorem general_hoeffding_weighted_uniform_proxy
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (a : ι → ℝ) {K : ℝ}
    (hindep : iIndepFun X μ)
    (hX : ∀ i, HasSubgaussianMGF (X i) (subgaussianProxy K) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-(t ^ 2) / (2 * (K ^ 2 * coeffL2NormSq a))) := by
  classical
  have htail :=
    general_hoeffding_weighted
      (μ := μ) (X := X) (c := fun _ => subgaussianProxy K)
      a hindep hX (t := t) ht
  simpa [weightedSubgaussianProxySum_uniform] using htail

/-- A weighted finite sum of independent sub-gaussian variables is
sub-gaussian with proxy `K²‖a‖₂²`. -/
theorem hasSubgaussianMGF_weighted_sum_uniform_proxy
    {X : ι → Ω → ℝ} (a : ι → ℝ) {K : ℝ}
    (hindep : iIndepFun X μ)
    (hX : ∀ i, HasSubgaussianMGF (X i) (subgaussianProxy K) μ) :
    HasSubgaussianMGF (fun ω => ∑ i, a i * X i ω)
      (subgaussianProxy (K * coeffL2Norm a)) μ := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  let c : ι → ℝ≥0 := fun i => ⟨a i ^ 2, sq_nonneg (a i)⟩ * subgaussianProxy K
  have hindepY : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hindep.comp (fun i x => a i * x) (fun _ => by fun_prop)
  have hY : ∀ i, HasSubgaussianMGF (Y i) (c i) μ := by
    intro i
    simpa [Y, c] using (hX i).const_mul (a i)
  have hsum :
      HasSubgaussianMGF (fun ω => ∑ i, Y i ω) (∑ i, c i) μ :=
    hasSubgaussianMGF_sum_of_iIndepFun
      (μ := μ) (X := Y) (c := c) hindepY hY
  have hproxy : (∑ i, c i) = subgaussianProxy (K * coeffL2Norm a) := by
    rw [← NNReal.coe_inj]
    calc
      (((∑ i, c i) : ℝ≥0) : ℝ)
          = ∑ i, ((c i : ℝ≥0) : ℝ) := by
        simp
      _ = ∑ i, a i ^ 2 * K ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        dsimp [c, subgaussianProxy]
        change a i ^ 2 * K ^ 2 = a i ^ 2 * K ^ 2
        rfl
      _ = ∑ i, K ^ 2 * a i ^ 2 := by
        exact Finset.sum_congr rfl fun i _ => by ring
      _ = K ^ 2 * coeffL2NormSq a := by
        simp [coeffL2NormSq, Finset.mul_sum]
      _ = ((subgaussianProxy (K * coeffL2Norm a) : ℝ≥0) : ℝ) := by
        rw [subgaussianProxy_coe, mul_pow, coeffL2Norm_sq]
  rw [← hproxy]
  convert hsum using 1

/-- Moment-growth form for weighted independent sub-gaussian sums, away from
the degenerate all-zero coefficient vector. -/
theorem subGaussianMomentCondition_weighted_sum_uniform_proxy
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (a : ι → ℝ) {K : ℝ}
    (hindep : iIndepFun X μ)
    (hK : 0 < K)
    (ha : 0 < coeffL2Norm a)
    (hX : ∀ i, HasSubgaussianMGF (X i) (subgaussianProxy K) μ) :
    subGaussianMomentCondition (fun ω => ∑ i, a i * X i ω) μ
      (8 * K * coeffL2Norm a) := by
  have hscale : 0 < K * coeffL2Norm a := mul_pos hK ha
  have hsum :
      HasSubgaussianMGF (fun ω => ∑ i, a i * X i ω)
        (subgaussianProxy (K * coeffL2Norm a)) μ :=
    hasSubgaussianMGF_weighted_sum_uniform_proxy
      (μ := μ) (X := X) a hindep hX
  have hMom :
      subGaussianMomentCondition (fun ω => ∑ i, a i * X i ω) μ
        (8 * (K * coeffL2Norm a)) :=
    subGaussianMomentCondition_of_hasSubgaussianMGF
      (μ := μ) (X := fun ω => ∑ i, a i * X i ω)
      (K := K * coeffL2Norm a) hscale hsum
  simpa [mul_assoc] using hMom

/-- HDP Exercise 2.6.5, upper Khintchine estimate in the MGF-proxy form:
for nonzero coefficient vectors, an independent weighted sum satisfies
`‖∑ aᵢXᵢ‖_p ≤ C K √p ‖a‖₂` with the explicit absolute constant `C = 8`. -/
theorem khintchine_subGaussian_upper_hasSubgaussianMGF_nonzero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (a : ι → ℝ) {K : ℝ} {p : ℝ≥0}
    (hindep : iIndepFun X μ)
    (hK : 0 < K)
    (ha : 0 < coeffL2Norm a)
    (hX : ∀ i, HasSubgaussianMGF (X i) (subgaussianProxy K) μ)
    (hp : 2 ≤ (p : ℝ)) :
    eLpNorm (fun ω => ∑ i, a i * X i ω) (p : ℝ≥0∞) μ
      ≤ ENNReal.ofReal (8 * K * Real.sqrt (p : ℝ) * coeffL2Norm a) := by
  have hMom :
      subGaussianMomentCondition (fun ω => ∑ i, a i * X i ω) μ
        (8 * K * coeffL2Norm a) :=
    subGaussianMomentCondition_weighted_sum_uniform_proxy
      (μ := μ) (X := X) a hindep hK ha hX
  have hp_one : 1 ≤ (p : ℝ) := by linarith
  have h :=
    (hMom.2 p hp_one).2
  convert h using 2
  ring

/-- HDP Exercise 2.6.5, upper Khintchine estimate in the MGF-proxy form:
an independent weighted sum satisfies
`‖∑ aᵢXᵢ‖_p ≤ C K √p ‖a‖₂` with the explicit absolute constant `C = 8`.
This version includes the degenerate all-zero coefficient vector. -/
theorem khintchine_subGaussian_upper_hasSubgaussianMGF
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (a : ι → ℝ) {K : ℝ} {p : ℝ≥0}
    (hindep : iIndepFun X μ)
    (hK : 0 < K)
    (hX : ∀ i, HasSubgaussianMGF (X i) (subgaussianProxy K) μ)
    (hp : 2 ≤ (p : ℝ)) :
    eLpNorm (fun ω => ∑ i, a i * X i ω) (p : ℝ≥0∞) μ
      ≤ ENNReal.ofReal (8 * K * Real.sqrt (p : ℝ) * coeffL2Norm a) := by
  by_cases ha0 : coeffL2Norm a = 0
  · have hsumsq : coeffL2NormSq a = 0 := by
      rw [← coeffL2Norm_sq, ha0]
      norm_num
    have hai : ∀ i, a i = 0 := by
      intro i
      have hterms :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (s := (Finset.univ : Finset ι))
          (f := fun i => a i ^ 2)
          (fun i _hi => sq_nonneg (a i))).mp
          (by simpa [coeffL2NormSq] using hsumsq)
      exact sq_eq_zero_iff.mp (hterms i (Finset.mem_univ i))
    have hsum_zero :
        (fun ω => ∑ i, a i * X i ω) = fun _ω => (0 : ℝ) := by
      funext ω
      simp [hai]
    rw [hsum_zero, ha0]
    simp
  · have ha_nonneg : 0 ≤ coeffL2Norm a := by
      unfold coeffL2Norm
      exact Real.sqrt_nonneg _
    have ha_pos : 0 < coeffL2Norm a :=
      lt_of_le_of_ne ha_nonneg (Ne.symm ha0)
    exact khintchine_subGaussian_upper_hasSubgaussianMGF_nonzero
      (μ := μ) (X := X) a hindep hK ha_pos hX hp

/-- HDP Exercise 2.6.5, upper Khintchine estimate in the book-facing
`ψ₂`-norm form.  If all centered summands satisfy `‖Xᵢ‖_{ψ₂} ≤ K`, then
`‖∑ aᵢXᵢ‖_p ≤ C K sqrt(p) ‖a‖₂` with the explicit absolute constant
`C = 16 sqrt 2`. -/
theorem khintchine_subGaussian_upper_psi2Norm
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (a : ι → ℝ) {K : ℝ} {p : ℝ≥0}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hXsg : ∀ i, IsSubGaussian (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subGaussianNorm (X i) μ ≤ K)
    (hp : 2 ≤ (p : ℝ)) :
    eLpNorm (fun ω => ∑ i, a i * X i ω) (p : ℝ≥0∞) μ
      ≤ ENNReal.ofReal (16 * Real.sqrt 2 * K * Real.sqrt (p : ℝ) * coeffL2Norm a) := by
  have hOrlicz : ∀ i, subGaussianOrliczCondition (X i) μ (2 * K) := by
    intro i
    exact
      subGaussianOrliczCondition_two_mul_of_norm_le
        (μ := μ) (X := X i) (K := K) (hXm i) (hXsg i) hKpos (hNormK i)
  have hHas :
      ∀ i, HasSubgaussianMGF (X i) (subgaussianProxy (Real.sqrt 2 * (2 * K))) μ := by
    intro i
    have hMGF :
        subGaussianMGFCondition (X i) μ (2 * K) :=
      subGaussianMGFCondition_of_orliczCondition_of_integral_eq_zero
        (μ := μ) (X := X i) (K := 2 * K) (hXm i) (hOrlicz i) (hmean i)
    exact hasSubgaussianMGF_of_subGaussianMGFCondition (μ := μ) hMGF
  have hscale_pos : 0 < Real.sqrt 2 * (2 * K) := by
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) (by positivity)
  have hupper :=
    khintchine_subGaussian_upper_hasSubgaussianMGF
      (μ := μ) (X := X) a (K := Real.sqrt 2 * (2 * K)) (p := p)
      hindep hscale_pos hHas hp
  calc
    eLpNorm (fun ω => ∑ i, a i * X i ω) (p : ℝ≥0∞) μ
        ≤ ENNReal.ofReal
          (8 * (Real.sqrt 2 * (2 * K)) * Real.sqrt (p : ℝ) * coeffL2Norm a) :=
      hupper
    _ = ENNReal.ofReal
          (16 * Real.sqrt 2 * K * Real.sqrt (p : ℝ) * coeffL2Norm a) := by
      congr 1
      ring

/-- The repository's real `L²` wrapper agrees with mathlib's extended
`eLpNorm` at exponent `2` for square-integrable real random variables. -/
theorem l2Norm_eq_eLpNorm_two
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    ENNReal.ofReal (l2Norm X μ) = eLpNorm X (2 : ℝ≥0∞) μ := by
  rw [← MeasureTheory.ofReal_lpNorm hX]
  congr 1
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ℝ≥0∞))
    (by norm_num) (by simp) hX.aestronglyMeasurable]
  unfold l2Norm
  simp [Real.sqrt_eq_rpow, sq_abs]

/-- Exponent arithmetic for the `L¹`/`L²`/`L³` Khintchine extrapolation. -/
lemma ennreal_two_mul_ofReal_half :
    (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
  rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  rw [← ENNReal.coe_ofNat, ← ENNReal.coe_mul]
  congr 1
  ext
  norm_num [NNReal.coe_mul]

/-- Exponent arithmetic for the `L¹`/`L²`/`L³` Khintchine extrapolation. -/
lemma ennreal_two_mul_ofReal_three_halves :
    (2 : ℝ≥0∞) * ENNReal.ofReal (3 / 2 : ℝ) = 3 := by
  rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num : 0 ≤ (3 / 2 : ℝ))]
  rw [← ENNReal.coe_ofNat, ← ENNReal.coe_mul]
  congr 1
  ext
  norm_num [NNReal.coe_mul]

lemma norm_rpow_half_mul_three_halves (x : ℝ) :
    ‖x‖ ^ ((1 / 2 : ℝ)) * ‖x‖ ^ ((3 / 2 : ℝ)) = ‖x‖ ^ (2 : ℝ) := by
  by_cases hx : ‖x‖ = 0
  · simp [hx]
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    rw [← Real.rpow_add hxpos]
    norm_num

/-- The interpolation inequality used in HDP Exercise 2.6.6:
`‖S‖₂² ≤ ‖S‖₁^(1/2) ‖S‖₃^(3/2)`. -/
theorem eLpNorm_two_sq_le_one_half_mul_three_halves
    {S : Ω → ℝ} (hS : AEStronglyMeasurable S μ) :
    eLpNorm S (2 : ℝ≥0∞) μ ^ (2 : ℝ) ≤
      eLpNorm S (1 : ℝ≥0∞) μ ^ ((1 / 2 : ℝ)) *
        eLpNorm S (3 : ℝ≥0∞) μ ^ ((3 / 2 : ℝ)) := by
  have hf : AEStronglyMeasurable (fun ω => ‖S ω‖ ^ ((1 / 2 : ℝ))) μ :=
    (hS.norm.aemeasurable.pow_const (1 / 2 : ℝ)).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun ω => ‖S ω‖ ^ ((3 / 2 : ℝ))) μ :=
    (hS.norm.aemeasurable.pow_const (3 / 2 : ℝ)).aestronglyMeasurable
  have hholder :=
    MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
      (μ := μ)
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (f := fun ω => ‖S ω‖ ^ ((1 / 2 : ℝ)))
      (g := fun ω => ‖S ω‖ ^ ((3 / 2 : ℝ)))
      (b := fun x y : ℝ => x * y) (c := (1 : ℝ≥0)) hf hg ?_
  · rw [show (fun x => (fun x y : ℝ => x * y)
          ((fun ω => ‖S ω‖ ^ ((1 / 2 : ℝ))) x)
          ((fun ω => ‖S ω‖ ^ ((3 / 2 : ℝ))) x)) =
        (fun ω => ‖S ω‖ ^ (2 : ℝ)) by
        funext ω
        change ‖S ω‖ ^ ((1 / 2 : ℝ)) * ‖S ω‖ ^ ((3 / 2 : ℝ)) =
          ‖S ω‖ ^ (2 : ℝ)
        exact norm_rpow_half_mul_three_halves (S ω)] at hholder
    rw [MeasureTheory.eLpNorm_norm_rpow (μ := μ) (f := S)
        (p := (1 : ℝ≥0∞)) (q := (2 : ℝ)) (by norm_num : 0 < (2 : ℝ))] at hholder
    rw [show (1 : ℝ≥0∞) * ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by
      rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num : 0 ≤ (2 : ℝ))]
      rw [one_mul]
      rfl] at hholder
    rw [MeasureTheory.eLpNorm_norm_rpow (μ := μ) (f := S)
        (p := (2 : ℝ≥0∞)) (q := (1 / 2 : ℝ))
        (by norm_num : 0 < (1 / 2 : ℝ))] at hholder
    rw [ennreal_two_mul_ofReal_half] at hholder
    rw [MeasureTheory.eLpNorm_norm_rpow (μ := μ) (f := S)
        (p := (2 : ℝ≥0∞)) (q := (3 / 2 : ℝ))
        (by norm_num : 0 < (3 / 2 : ℝ))] at hholder
    rw [ennreal_two_mul_ofReal_three_halves] at hholder
    simpa using hholder
  · filter_upwards with ω
    simp [Real.norm_eq_abs]

/-- Real arithmetic behind the `L¹` Khintchine extrapolation. -/
lemma khintchine_l1_real_lower {A B u : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hu : 0 ≤ u)
    (h : A ^ 2 ≤ u ^ ((1 / 2 : ℝ)) * (B * A) ^ ((3 / 2 : ℝ))) :
    A / B ^ 3 ≤ u := by
  let C : ℝ := (B * A) ^ ((3 / 2 : ℝ))
  have hBA : 0 < B * A := mul_pos hB hA
  have hC : 0 < C := by
    dsimp [C]
    exact Real.rpow_pos_of_pos hBA (3 / 2 : ℝ)
  have hdiv : A ^ 2 / C ≤ u ^ ((1 / 2 : ℝ)) := by
    rw [div_le_iff₀ hC]
    simpa [C, mul_comm, mul_left_comm, mul_assoc] using h
  have hdiv_nonneg : 0 ≤ A ^ 2 / C := div_nonneg (sq_nonneg A) hC.le
  have hsqrt_nonneg : 0 ≤ u ^ ((1 / 2 : ℝ)) := Real.rpow_nonneg hu _
  have hsq := mul_le_mul hdiv hdiv hdiv_nonneg hsqrt_nonneg
  have hright : u ^ ((1 / 2 : ℝ)) * u ^ ((1 / 2 : ℝ)) = u := by
    simpa [Real.sqrt_eq_rpow, sq] using Real.sq_sqrt hu
  have hC_sq : C ^ 2 = (B * A) ^ 3 := by
    dsimp [C]
    rw [← Real.rpow_natCast ((B * A) ^ ((3 / 2 : ℝ))) 2]
    rw [← Real.rpow_mul hBA.le]
    norm_num [Real.rpow_natCast]
  have hleft : A / B ^ 3 = (A ^ 2 / C) * (A ^ 2 / C) := by
    rw [show (A ^ 2 / C) * (A ^ 2 / C) = A ^ 4 / C ^ 2 by ring]
    rw [hC_sq]
    field_simp [hA.ne', hB.ne']
  calc
    A / B ^ 3 = (A ^ 2 / C) * (A ^ 2 / C) := hleft
    _ ≤ u ^ ((1 / 2 : ℝ)) * u ^ ((1 / 2 : ℝ)) := hsq
    _ = u := hright

/-- Extended-real form of the `L¹` Khintchine extrapolation step. -/
lemma khintchine_l1_lower_of_interpolation
    {L1 L2 L3 : ℝ≥0∞} {A B : ℝ}
    (hinterp : L2 ^ (2 : ℝ) ≤ L1 ^ ((1 / 2 : ℝ)) * L3 ^ ((3 / 2 : ℝ)))
    (h2 : L2 = ENNReal.ofReal A)
    (h3 : L3 ≤ ENNReal.ofReal (B * A))
    (hL1top : L1 ≠ ∞)
    (hA : 0 ≤ A) (hB : 0 < B) :
    ENNReal.ofReal (A / B ^ 3) ≤ L1 := by
  by_cases hAzero : A = 0
  · subst A
    simp
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
  have hBA_nonneg : 0 ≤ B * A := (mul_pos hB hApos).le
  have hmain :
      ENNReal.ofReal (A ^ 2) ≤
        L1 ^ ((1 / 2 : ℝ)) * (ENNReal.ofReal (B * A)) ^ ((3 / 2 : ℝ)) := by
    calc
      ENNReal.ofReal (A ^ 2) = (ENNReal.ofReal A) ^ (2 : ℝ) := by
        simpa [Real.rpow_natCast] using
          (ENNReal.ofReal_rpow_of_nonneg hA (by norm_num : 0 ≤ (2 : ℝ))).symm
      _ = L2 ^ (2 : ℝ) := by rw [h2]
      _ ≤ L1 ^ ((1 / 2 : ℝ)) * L3 ^ ((3 / 2 : ℝ)) := hinterp
      _ ≤ L1 ^ ((1 / 2 : ℝ)) * (ENNReal.ofReal (B * A)) ^ ((3 / 2 : ℝ)) := by
        exact mul_le_mul_left'
          (ENNReal.rpow_le_rpow h3 (by norm_num : 0 ≤ (3 / 2 : ℝ))) _
  have hright_top :
      L1 ^ ((1 / 2 : ℝ)) * (ENNReal.ofReal (B * A)) ^ ((3 / 2 : ℝ)) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) hL1top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num : 0 ≤ (3 / 2 : ℝ))
        ENNReal.ofReal_ne_top)
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hright_top).2 hmain
  have hreal' :
      A ^ 2 ≤ L1.toReal ^ ((1 / 2 : ℝ)) * (B * A) ^ ((3 / 2 : ℝ)) := by
    rw [ENNReal.toReal_ofReal (sq_nonneg A)] at hreal
    rw [ENNReal.toReal_mul] at hreal
    rw [← ENNReal.toReal_rpow] at hreal
    rw [← ENNReal.toReal_rpow] at hreal
    rw [ENNReal.toReal_ofReal hBA_nonneg] at hreal
    exact hreal
  have hlower_real : A / B ^ 3 ≤ L1.toReal :=
    khintchine_l1_real_lower hApos hB ENNReal.toReal_nonneg hreal'
  exact (ENNReal.ofReal_le_iff_le_toReal hL1top).2 hlower_real

/-- Holder exponents for the low-`p` Khintchine interpolation:
`1 / (3 - p) + 1 / ((3 - p) / (2 - p)) = 1`. -/
lemma holderTriple_subGaussian_low_p {p : ℝ} (_hp0 : 0 < p) (hp2 : p < 2) :
    ENNReal.HolderTriple (ENNReal.ofReal (3 - p))
      (ENNReal.ofReal ((3 - p) / (2 - p))) (1 : ℝ≥0∞) := by
  have hqpos : 0 < 3 - p := by linarith
  have hdenpos : 0 < 2 - p := sub_pos.mpr hp2
  have hrpos : 0 < (3 - p) / (2 - p) := div_pos hqpos hdenpos
  refine ⟨?_⟩
  have hreal : (3 - p)⁻¹ + ((3 - p) / (2 - p))⁻¹ = (1 : ℝ) := by
    field_simp [sub_ne_zero.mpr (by linarith : 3 ≠ p),
      sub_ne_zero.mpr (by linarith : 2 ≠ p)]
    ring
  rw [← ENNReal.ofReal_inv_of_pos hqpos]
  rw [← ENNReal.ofReal_inv_of_pos hrpos]
  rw [← ENNReal.ofReal_add (inv_nonneg.mpr hqpos.le) (inv_nonneg.mpr hrpos.le)]
  rw [hreal]
  norm_num [ENNReal.ofReal]

lemma ennreal_low_p_left_exp {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) :
    ENNReal.ofReal (3 - p) * ENNReal.ofReal (p / (3 - p)) =
      ENNReal.ofReal p := by
  have hqpos : 0 < 3 - p := by linarith
  rw [← ENNReal.ofReal_mul hqpos.le]
  congr 1
  field_simp [hqpos.ne']

lemma ennreal_low_p_right_exp {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) :
    ENNReal.ofReal ((3 - p) / (2 - p)) *
        ENNReal.ofReal (3 * (2 - p) / (3 - p)) = (3 : ℝ≥0∞) := by
  have hqpos : 0 < 3 - p := by linarith
  have hdenpos : 0 < 2 - p := sub_pos.mpr hp2
  have hrnonneg : 0 ≤ (3 - p) / (2 - p) := (div_pos hqpos hdenpos).le
  rw [← ENNReal.ofReal_mul hrnonneg]
  have hreal :
      (3 - p) / (2 - p) * (3 * (2 - p) / (3 - p)) = (3 : ℝ) := by
    field_simp [hdenpos.ne', hqpos.ne']
  rw [hreal]
  norm_num [ENNReal.ofReal]

lemma norm_rpow_low_p_mul {p x : ℝ} (hp0 : 0 < p) (hp2 : p < 2) :
    ‖x‖ ^ (p / (3 - p)) * ‖x‖ ^ (3 * (2 - p) / (3 - p)) =
      ‖x‖ ^ (2 : ℝ) := by
  have hqpos : 0 < 3 - p := by linarith
  have hdenpos : 0 < 2 - p := sub_pos.mpr hp2
  have hleft_pos : 0 < p / (3 - p) := div_pos hp0 hqpos
  have hright_pos : 0 < 3 * (2 - p) / (3 - p) :=
    div_pos (mul_pos (by norm_num) hdenpos) hqpos
  by_cases hx : ‖x‖ = 0
  · rw [hx]
    simp [hleft_pos.ne', hright_pos.ne']
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    rw [← Real.rpow_add hxpos]
    congr 1
    field_simp [hqpos.ne']
    ring_nf

/-- The interpolation inequality used in HDP Exercise 2.6.7:
`‖S‖₂² ≤ ‖S‖p^(p/(3-p)) ‖S‖₃^(3(2-p)/(3-p))`. -/
theorem eLpNorm_two_sq_le_low_p_mul_three
    {S : Ω → ℝ} {p : ℝ}
    (hp0 : 0 < p) (hp2 : p < 2)
    (hS : AEStronglyMeasurable S μ) :
    eLpNorm S (2 : ℝ≥0∞) μ ^ (2 : ℝ) ≤
      eLpNorm S (ENNReal.ofReal p) μ ^ (p / (3 - p)) *
        eLpNorm S (3 : ℝ≥0∞) μ ^ (3 * (2 - p) / (3 - p)) := by
  letI : ENNReal.HolderTriple (ENNReal.ofReal (3 - p))
      (ENNReal.ofReal ((3 - p) / (2 - p))) (1 : ℝ≥0∞) :=
    holderTriple_subGaussian_low_p hp0 hp2
  have hf : AEStronglyMeasurable (fun ω => ‖S ω‖ ^ (p / (3 - p))) μ :=
    (hS.norm.aemeasurable.pow_const (p / (3 - p))).aestronglyMeasurable
  have hg :
      AEStronglyMeasurable (fun ω => ‖S ω‖ ^ (3 * (2 - p) / (3 - p))) μ :=
    (hS.norm.aemeasurable.pow_const (3 * (2 - p) / (3 - p))).aestronglyMeasurable
  have hholder :=
    MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
      (μ := μ)
      (p := ENNReal.ofReal (3 - p))
      (q := ENNReal.ofReal ((3 - p) / (2 - p)))
      (r := (1 : ℝ≥0∞))
      (f := fun ω => ‖S ω‖ ^ (p / (3 - p)))
      (g := fun ω => ‖S ω‖ ^ (3 * (2 - p) / (3 - p)))
      (b := fun x y : ℝ => x * y) (c := (1 : ℝ≥0)) hf hg ?_
  · rw [show (fun x => (fun x y : ℝ => x * y)
          ((fun ω => ‖S ω‖ ^ (p / (3 - p))) x)
          ((fun ω => ‖S ω‖ ^ (3 * (2 - p) / (3 - p))) x)) =
        (fun ω => ‖S ω‖ ^ (2 : ℝ)) by
        funext ω
        change ‖S ω‖ ^ (p / (3 - p)) *
            ‖S ω‖ ^ (3 * (2 - p) / (3 - p)) = ‖S ω‖ ^ (2 : ℝ)
        exact norm_rpow_low_p_mul hp0 hp2] at hholder
    rw [MeasureTheory.eLpNorm_norm_rpow (μ := μ) (f := S)
        (p := (1 : ℝ≥0∞)) (q := (2 : ℝ)) (by norm_num : 0 < (2 : ℝ))] at hholder
    rw [show (1 : ℝ≥0∞) * ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by
      rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num : 0 ≤ (2 : ℝ))]
      rw [one_mul]
      rfl] at hholder
    rw [MeasureTheory.eLpNorm_norm_rpow (μ := μ) (f := S)
        (p := ENNReal.ofReal (3 - p)) (q := (p / (3 - p)))
        (div_pos hp0 (by linarith : 0 < 3 - p))] at hholder
    rw [ennreal_low_p_left_exp hp0 hp2] at hholder
    rw [MeasureTheory.eLpNorm_norm_rpow (μ := μ) (f := S)
        (p := ENNReal.ofReal ((3 - p) / (2 - p)))
        (q := (3 * (2 - p) / (3 - p)))
        (div_pos (mul_pos (by norm_num) (sub_pos.mpr hp2))
          (by linarith : 0 < 3 - p))] at hholder
    rw [ennreal_low_p_right_exp hp0 hp2] at hholder
    simpa using hholder
  · filter_upwards with ω
    simp [Real.norm_eq_abs]

lemma khintchine_rpow_extrapolate_left {A B α β : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hα : 0 < α) (hsum : α + β = 2) :
    (A ^ 2 / ((B * A) ^ β)) ^ α⁻¹ = A / B ^ (β / α) := by
  have hBA : 0 < B * A := mul_pos hB hA
  have hαne : α ≠ 0 := hα.ne'
  have hsum' : 2 - β = α := by linarith
  rw [Real.div_rpow (sq_nonneg A) (Real.rpow_nonneg hBA.le β)]
  have hA2 : A ^ 2 = A ^ (2 : ℝ) := (Real.rpow_natCast A 2).symm
  conv_lhs =>
    arg 1
    rw [hA2]
    rw [← Real.rpow_mul hA.le]
  conv_lhs =>
    arg 2
    rw [← Real.rpow_mul hBA.le]
    rw [Real.mul_rpow hB.le hA.le]
  calc
    A ^ (2 * α⁻¹) / (B ^ (β * α⁻¹) * A ^ (β * α⁻¹))
        = A ^ ((2 - β) * α⁻¹) / B ^ (β * α⁻¹) := by
          calc
            A ^ (2 * α⁻¹) / (B ^ (β * α⁻¹) * A ^ (β * α⁻¹))
                = (A ^ (2 * α⁻¹) / A ^ (β * α⁻¹)) / B ^ (β * α⁻¹) := by
                  have hAnz : A ^ (β * α⁻¹) ≠ 0 :=
                    (Real.rpow_pos_of_pos hA _).ne'
                  have hBnz : B ^ (β * α⁻¹) ≠ 0 :=
                    (Real.rpow_pos_of_pos hB _).ne'
                  field_simp [hAnz, hBnz]
            _ = A ^ ((2 - β) * α⁻¹) / B ^ (β * α⁻¹) := by
              rw [← Real.rpow_sub hA]
              congr 2
              ring
    _ = A / B ^ (β / α) := by
      have hexpA : (2 - β) * α⁻¹ = 1 := by
        rw [hsum']
        field_simp [hαne]
      rw [hexpA, Real.rpow_one]
      congr 1

lemma khintchine_low_p_real_lower {A B u α β : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hu : 0 ≤ u)
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β = 2)
    (h : A ^ 2 ≤ u ^ α * (B * A) ^ β) :
    A / B ^ (β / α) ≤ u := by
  let C : ℝ := (B * A) ^ β
  have hBA : 0 < B * A := mul_pos hB hA
  have hC : 0 < C := by
    dsimp [C]
    exact Real.rpow_pos_of_pos hBA β
  have hdiv : A ^ 2 / C ≤ u ^ α := by
    rw [div_le_iff₀ hC]
    simpa [C, mul_comm, mul_left_comm, mul_assoc] using h
  have hdiv_nonneg : 0 ≤ A ^ 2 / C := div_nonneg (sq_nonneg A) hC.le
  have hpow := Real.rpow_le_rpow hdiv_nonneg hdiv (inv_nonneg.mpr hα.le)
  have hright : (u ^ α) ^ α⁻¹ = u := by
    rw [← Real.rpow_mul hu]
    have hmul : α * α⁻¹ = (1 : ℝ) := by field_simp [hα.ne']
    rw [hmul, Real.rpow_one]
  have hleft : (A ^ 2 / C) ^ α⁻¹ = A / B ^ (β / α) := by
    dsimp [C]
    exact khintchine_rpow_extrapolate_left hA hB hα hsum
  calc
    A / B ^ (β / α) = (A ^ 2 / C) ^ α⁻¹ := hleft.symm
    _ ≤ (u ^ α) ^ α⁻¹ := hpow
    _ = u := hright

/-- Extended-real form of the low-`p` Khintchine extrapolation step. -/
lemma khintchine_low_p_lower_of_interpolation
    {Lp L2 L3 : ℝ≥0∞} {A B p : ℝ}
    (hp0 : 0 < p) (hp2 : p < 2)
    (hinterp :
      L2 ^ (2 : ℝ) ≤ Lp ^ (p / (3 - p)) * L3 ^ (3 * (2 - p) / (3 - p)))
    (h2 : L2 = ENNReal.ofReal A)
    (h3 : L3 ≤ ENNReal.ofReal (B * A))
    (hLptop : Lp ≠ ∞)
    (hA : 0 ≤ A) (hB : 0 < B) :
    ENNReal.ofReal (A / B ^ ((3 * (2 - p) / (3 - p)) / (p / (3 - p)))) ≤ Lp := by
  let α : ℝ := p / (3 - p)
  let β : ℝ := 3 * (2 - p) / (3 - p)
  have hαpos : 0 < α := by
    dsimp [α]
    exact div_pos hp0 (by linarith : 0 < 3 - p)
  have hβpos : 0 < β := by
    dsimp [β]
    exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hp2)) (by linarith : 0 < 3 - p)
  have hsum : α + β = 2 := by
    dsimp [α, β]
    have hq : 3 - p ≠ 0 := sub_ne_zero.mpr (by linarith : 3 ≠ p)
    field_simp [hq]
    ring
  by_cases hAzero : A = 0
  · subst A
    simp
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
  have hBA_nonneg : 0 ≤ B * A := (mul_pos hB hApos).le
  have hmain :
      ENNReal.ofReal (A ^ 2) ≤ Lp ^ α * (ENNReal.ofReal (B * A)) ^ β := by
    calc
      ENNReal.ofReal (A ^ 2) = (ENNReal.ofReal A) ^ (2 : ℝ) := by
        simpa [Real.rpow_natCast] using
          (ENNReal.ofReal_rpow_of_nonneg hA (by norm_num : 0 ≤ (2 : ℝ))).symm
      _ = L2 ^ (2 : ℝ) := by rw [h2]
      _ ≤ Lp ^ α * L3 ^ β := by simpa [α, β] using hinterp
      _ ≤ Lp ^ α * (ENNReal.ofReal (B * A)) ^ β := by
        exact mul_le_mul_left' (ENNReal.rpow_le_rpow h3 hβpos.le) _
  have hright_top : Lp ^ α * (ENNReal.ofReal (B * A)) ^ β ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hαpos.le hLptop)
      (ENNReal.rpow_ne_top_of_nonneg hβpos.le ENNReal.ofReal_ne_top)
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hright_top).2 hmain
  have hreal' : A ^ 2 ≤ Lp.toReal ^ α * (B * A) ^ β := by
    rw [ENNReal.toReal_ofReal (sq_nonneg A)] at hreal
    rw [ENNReal.toReal_mul] at hreal
    rw [← ENNReal.toReal_rpow] at hreal
    rw [← ENNReal.toReal_rpow] at hreal
    rw [ENNReal.toReal_ofReal hBA_nonneg] at hreal
    exact hreal
  have hlower_real : A / B ^ (β / α) ≤ Lp.toReal :=
    khintchine_low_p_real_lower hApos hB ENNReal.toReal_nonneg hαpos hβpos hsum hreal'
  have : ENNReal.ofReal (A / B ^ (β / α)) ≤ Lp :=
    (ENNReal.ofReal_le_iff_le_toReal hLptop).2 hlower_real
  simpa [α, β] using this

/-- Variance identity for weighted sums of independent mean-zero unit-variance
variables.  This is the `L²` core of the lower Khintchine inequality. -/
theorem weighted_sum_variance_unit_of_iIndepFun
    {X : ι → Ω → ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (hvar : ∀ i, Var[X i; μ] = 1) :
    Var[(fun ω => ∑ i, a i * X i ω); μ] = coeffL2NormSq a := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  have hY2 : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    simpa [Y] using (hX2 i).const_mul (a i)
  have hindepY : iIndepFun Y μ := by
    have hcomp :=
      hindep.comp (fun i x => a i * x) (by
        intro i
        fun_prop)
    simpa [Y, Function.comp_def] using hcomp
  have hpairY : Pairwise (fun i j => Y i ⟂ᵢ[μ] Y j) := by
    intro i j hij
    exact hindepY.indepFun hij
  have hvar_sum :
      Var[(fun ω => ∑ i, Y i ω); μ] = ∑ i, Var[Y i; μ] :=
    variance_sum_independent (μ := μ) (X := Y) hY2 hpairY
  calc
    Var[(fun ω => ∑ i, a i * X i ω); μ]
        = Var[(fun ω => ∑ i, Y i ω); μ] := by simp [Y]
    _ = ∑ i, Var[Y i; μ] := hvar_sum
    _ = ∑ i, a i ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [ProbabilityTheory.variance_const_mul, hvar i]
      ring
    _ = coeffL2NormSq a := rfl

/-- The exact `L²` norm of a weighted sum of independent mean-zero
unit-variance variables. -/
theorem khintchine_subGaussian_l2_unitVariance
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Var[X i; μ] = 1) :
    eLpNorm (fun ω => ∑ i, a i * X i ω) (2 : ℝ≥0∞) μ =
      ENNReal.ofReal (coeffL2Norm a) := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  let S : Ω → ℝ := fun ω => ∑ i, Y i ω
  have hY2 : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    simpa [Y] using (hX2 i).const_mul (a i)
  have hS2 : MemLp S 2 μ := by
    simpa [S] using
      (memLp_finset_sum (μ := μ) (p := (2 : ℝ≥0∞))
        (s := (Finset.univ : Finset ι)) (f := fun i ω => Y i ω)
        (fun i _ => hY2 i))
  have hYint : ∀ i, Integrable (Y i) μ := fun i =>
    (hY2 i).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hmeanY : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    simp [Y, integral_const_mul, hmean i]
  have hmeanS : ∫ ω, S ω ∂μ = 0 := by
    calc
      ∫ ω, S ω ∂μ = ∑ i, ∫ ω, Y i ω ∂μ := by
        dsimp [S]
        rw [integral_finset_sum]
        intro i _
        exact hYint i
      _ = 0 := by simp [hmeanY]
  have hvar_sum : Var[S; μ] = coeffL2NormSq a := by
    calc
      Var[S; μ] = Var[(fun ω => ∑ i, a i * X i ω); μ] := by rfl
      _ = coeffL2NormSq a :=
        weighted_sum_variance_unit_of_iIndepFun
          (μ := μ) (X := X) a hindep hX2 hvar
  have hvar_integral : Var[S; μ] = ∫ ω, S ω ^ 2 ∂μ := by
    simpa [hmeanS] using
      ProbabilityTheory.variance_eq_integral (μ := μ) hS2.aemeasurable
  have hl2 : l2Norm S μ = coeffL2Norm a := by
    unfold l2Norm coeffL2Norm
    rw [← hvar_integral, hvar_sum]
  calc
    eLpNorm (fun ω => ∑ i, a i * X i ω) (2 : ℝ≥0∞) μ
        = eLpNorm S (2 : ℝ≥0∞) μ := rfl
    _ = ENNReal.ofReal (l2Norm S μ) := by
      exact (l2Norm_eq_eLpNorm_two (μ := μ) hS2).symm
    _ = ENNReal.ofReal (coeffL2Norm a) := by rw [hl2]

/-- HDP Exercise 2.6.5, lower Khintchine estimate.  The lower bound only
uses the mean-zero, unit-variance, and independence assumptions: for `p ≥ 2`,
`‖a‖₂ ≤ ‖∑ aᵢXᵢ‖_p`. -/
theorem khintchine_subGaussian_lower_unitVariance
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (a : ι → ℝ) {p : ℝ≥0}
    (hindep : iIndepFun X μ)
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Var[X i; μ] = 1)
    (hp : 2 ≤ (p : ℝ)) :
    ENNReal.ofReal (coeffL2Norm a) ≤
      eLpNorm (fun ω => ∑ i, a i * X i ω) (p : ℝ≥0∞) μ := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  let S : Ω → ℝ := fun ω => ∑ i, Y i ω
  have hY2 : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    simpa [Y] using (hX2 i).const_mul (a i)
  have hS2 : MemLp S 2 μ := by
    simpa [S] using
      (memLp_finset_sum (μ := μ) (p := (2 : ℝ≥0∞))
        (s := (Finset.univ : Finset ι)) (f := fun i ω => Y i ω)
        (fun i _ => hY2 i))
  have hYint : ∀ i, Integrable (Y i) μ := fun i =>
    (hY2 i).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hmeanY : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    simp [Y, integral_const_mul, hmean i]
  have hmeanS : ∫ ω, S ω ∂μ = 0 := by
    calc
      ∫ ω, S ω ∂μ = ∑ i, ∫ ω, Y i ω ∂μ := by
        dsimp [S]
        rw [integral_finset_sum]
        intro i _
        exact hYint i
      _ = 0 := by simp [hmeanY]
  have hvar_sum : Var[S; μ] = coeffL2NormSq a := by
    calc
      Var[S; μ] = Var[(fun ω => ∑ i, a i * X i ω); μ] := by rfl
      _ = coeffL2NormSq a :=
        weighted_sum_variance_unit_of_iIndepFun
          (μ := μ) (X := X) a hindep hX2 hvar
  have hvar_integral : Var[S; μ] = ∫ ω, S ω ^ 2 ∂μ := by
    simpa [hmeanS] using
      ProbabilityTheory.variance_eq_integral (μ := μ) hS2.aemeasurable
  have hl2 : l2Norm S μ = coeffL2Norm a := by
    unfold l2Norm coeffL2Norm
    rw [← hvar_integral, hvar_sum]
  have hmono :
      eLpNorm S (2 : ℝ≥0∞) μ ≤ eLpNorm S (p : ℝ≥0∞) μ := by
    exact lpNorm_mono_exponent (μ := μ) (X := S)
      (p := (2 : ℝ≥0∞)) (q := (p : ℝ≥0∞)) (by exact_mod_cast hp)
      hS2.aestronglyMeasurable
  calc
    ENNReal.ofReal (coeffL2Norm a) = eLpNorm S (2 : ℝ≥0∞) μ := by
      rw [← hl2]
      exact l2Norm_eq_eLpNorm_two (μ := μ) hS2
    _ ≤ eLpNorm S (p : ℝ≥0∞) μ := hmono
    _ = eLpNorm (fun ω => ∑ i, a i * X i ω) (p : ℝ≥0∞) μ := rfl

/-- HDP Exercise 2.6.6, upper `p = 1` Khintchine estimate.  Under the
unit-variance normalization, `‖∑ aᵢXᵢ‖₁ ≤ ‖a‖₂`. -/
theorem khintchine_subGaussian_l1_upper_unitVariance
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Var[X i; μ] = 1) :
    eLpNorm (fun ω => ∑ i, a i * X i ω) (1 : ℝ≥0∞) μ ≤
      ENNReal.ofReal (coeffL2Norm a) := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  let S : Ω → ℝ := fun ω => ∑ i, Y i ω
  have hY2 : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    simpa [Y] using (hX2 i).const_mul (a i)
  have hS2 : MemLp S 2 μ := by
    simpa [S] using
      (memLp_finset_sum (μ := μ) (p := (2 : ℝ≥0∞))
        (s := (Finset.univ : Finset ι)) (f := fun i ω => Y i ω)
        (fun i _ => hY2 i))
  have hmono :
      eLpNorm S (1 : ℝ≥0∞) μ ≤ eLpNorm S (2 : ℝ≥0∞) μ :=
    lpNorm_mono_exponent (μ := μ) (X := S)
      (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      (by norm_num) hS2.aestronglyMeasurable
  calc
    eLpNorm (fun ω => ∑ i, a i * X i ω) (1 : ℝ≥0∞) μ
        = eLpNorm S (1 : ℝ≥0∞) μ := rfl
    _ ≤ eLpNorm S (2 : ℝ≥0∞) μ := hmono
    _ = ENNReal.ofReal (coeffL2Norm a) := by
      exact khintchine_subGaussian_l2_unitVariance
        (μ := μ) (X := X) a hindep hX2 hmean hvar

/-- HDP Exercise 2.6.6, lower `p = 1` Khintchine estimate.  The explicit
constant is the extrapolation constant obtained from `L¹`, `L²`, and `L³`:
`c(K) = (16 sqrt 2 K sqrt 3)⁻³`. -/
theorem khintchine_subGaussian_l1_lower_unitVariance
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (a : ι → ℝ) {K : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hXsg : ∀ i, IsSubGaussian (X i) μ)
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Var[X i; μ] = 1)
    (hK : 0 < K)
    (hKnorm : ∀ i, subGaussianNorm (X i) μ ≤ K) :
    ENNReal.ofReal
        (coeffL2Norm a / (16 * Real.sqrt 2 * K * Real.sqrt 3) ^ 3) ≤
      eLpNorm (fun ω => ∑ i, a i * X i ω) (1 : ℝ≥0∞) μ := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  let S : Ω → ℝ := fun ω => ∑ i, Y i ω
  let A : ℝ := coeffL2Norm a
  let B : ℝ := 16 * Real.sqrt 2 * K * Real.sqrt 3
  have hY2 : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    simpa [Y] using (hX2 i).const_mul (a i)
  have hS2 : MemLp S 2 μ := by
    simpa [S] using
      (memLp_finset_sum (μ := μ) (p := (2 : ℝ≥0∞))
        (s := (Finset.univ : Finset ι)) (f := fun i ω => Y i ω)
        (fun i _ => hY2 i))
  have hinterp :
      eLpNorm S (2 : ℝ≥0∞) μ ^ (2 : ℝ) ≤
        eLpNorm S (1 : ℝ≥0∞) μ ^ ((1 / 2 : ℝ)) *
          eLpNorm S (3 : ℝ≥0∞) μ ^ ((3 / 2 : ℝ)) :=
    eLpNorm_two_sq_le_one_half_mul_three_halves
      (μ := μ) hS2.aestronglyMeasurable
  have h2 :
      eLpNorm S (2 : ℝ≥0∞) μ = ENNReal.ofReal A := by
    dsimp [S, Y, A]
    exact khintchine_subGaussian_l2_unitVariance
      (μ := μ) (X := X) a hindep hX2 hmean hvar
  have h3raw :
      eLpNorm (fun ω => ∑ i, a i * X i ω) ((3 : ℝ≥0) : ℝ≥0∞) μ
        ≤ ENNReal.ofReal
          (16 * Real.sqrt 2 * K * Real.sqrt ((3 : ℝ≥0) : ℝ) * coeffL2Norm a) :=
    khintchine_subGaussian_upper_psi2Norm
      (μ := μ) (X := X) a (K := K) (p := (3 : ℝ≥0))
      hindep hXm hXsg hmean hK hKnorm (by norm_num : 2 ≤ ((3 : ℝ≥0) : ℝ))
  have h3 :
      eLpNorm S (3 : ℝ≥0∞) μ ≤ ENNReal.ofReal (B * A) := by
    dsimp [S, Y, A, B]
    simpa [mul_assoc] using h3raw
  have hL1top : eLpNorm S (1 : ℝ≥0∞) μ ≠ ∞ := by
    have hmono :
        eLpNorm S (1 : ℝ≥0∞) μ ≤ eLpNorm S (3 : ℝ≥0∞) μ :=
      lpNorm_mono_exponent (μ := μ) (X := S)
        (p := (1 : ℝ≥0∞)) (q := (3 : ℝ≥0∞))
        (by norm_num) hS2.aestronglyMeasurable
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmono.trans h3)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, coeffL2Norm]
    exact Real.sqrt_nonneg _
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hlow :
      ENNReal.ofReal (A / B ^ 3) ≤ eLpNorm S (1 : ℝ≥0∞) μ :=
    khintchine_l1_lower_of_interpolation
      (L1 := eLpNorm S (1 : ℝ≥0∞) μ)
      (L2 := eLpNorm S (2 : ℝ≥0∞) μ)
      (L3 := eLpNorm S (3 : ℝ≥0∞) μ)
      (A := A) (B := B) hinterp h2 h3 hL1top hA_nonneg hB_pos
  simpa [S, Y, A, B] using hlow

/-- HDP Exercise 2.6.7, upper Khintchine estimate for `0 < p < 2`.
Under the unit-variance normalization, monotonicity gives
`‖∑ aᵢXᵢ‖_p ≤ ‖a‖₂`. -/
theorem khintchine_subGaussian_low_p_upper_unitVariance
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (a : ι → ℝ) {p : ℝ≥0}
    (hindep : iIndepFun X μ)
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Var[X i; μ] = 1)
    (hp0 : 0 < (p : ℝ)) (hp2 : (p : ℝ) < 2) :
    eLpNorm (fun ω => ∑ i, a i * X i ω) (p : ℝ≥0∞) μ ≤
      ENNReal.ofReal (coeffL2Norm a) := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  let S : Ω → ℝ := fun ω => ∑ i, Y i ω
  have hY2 : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    simpa [Y] using (hX2 i).const_mul (a i)
  have hS2 : MemLp S 2 μ := by
    simpa [S] using
      (memLp_finset_sum (μ := μ) (p := (2 : ℝ≥0∞))
        (s := (Finset.univ : Finset ι)) (f := fun i ω => Y i ω)
        (fun i _ => hY2 i))
  have hmono :
      eLpNorm S (p : ℝ≥0∞) μ ≤ eLpNorm S (2 : ℝ≥0∞) μ :=
    lpNorm_mono_exponent (μ := μ) (X := S)
      (p := (p : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      (by exact_mod_cast hp2.le) hS2.aestronglyMeasurable
  calc
    eLpNorm (fun ω => ∑ i, a i * X i ω) (p : ℝ≥0∞) μ
        = eLpNorm S (p : ℝ≥0∞) μ := rfl
    _ ≤ eLpNorm S (2 : ℝ≥0∞) μ := hmono
    _ = ENNReal.ofReal (coeffL2Norm a) := by
      exact khintchine_subGaussian_l2_unitVariance
        (μ := μ) (X := X) a hindep hX2 hmean hvar

/-- HDP Exercise 2.6.7, lower Khintchine estimate for `0 < p < 2`.
The explicit constant is obtained by interpolating `L^p`, `L²`, and `L³`:
`c(p,K) = (16 sqrt 2 K sqrt 3)^(-3(2-p)/p)`. -/
theorem khintchine_subGaussian_low_p_lower_unitVariance
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (a : ι → ℝ) {K : ℝ} {p : ℝ≥0}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hXsg : ∀ i, IsSubGaussian (X i) μ)
    (hX2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ i, Var[X i; μ] = 1)
    (hK : 0 < K)
    (hKnorm : ∀ i, subGaussianNorm (X i) μ ≤ K)
    (hp0 : 0 < (p : ℝ)) (hp2 : (p : ℝ) < 2) :
    ENNReal.ofReal
        (coeffL2Norm a /
          (16 * Real.sqrt 2 * K * Real.sqrt 3) ^ (3 * (2 - (p : ℝ)) / (p : ℝ))) ≤
      eLpNorm (fun ω => ∑ i, a i * X i ω) (p : ℝ≥0∞) μ := by
  classical
  let pr : ℝ := (p : ℝ)
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  let S : Ω → ℝ := fun ω => ∑ i, Y i ω
  let A : ℝ := coeffL2Norm a
  let B : ℝ := 16 * Real.sqrt 2 * K * Real.sqrt 3
  have hpENN : ENNReal.ofReal pr = (p : ℝ≥0∞) := by
    dsimp [pr]
    exact ENNReal.ofReal_eq_coe_nnreal p.2
  have hY2 : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    simpa [Y] using (hX2 i).const_mul (a i)
  have hS2 : MemLp S 2 μ := by
    simpa [S] using
      (memLp_finset_sum (μ := μ) (p := (2 : ℝ≥0∞))
        (s := (Finset.univ : Finset ι)) (f := fun i ω => Y i ω)
        (fun i _ => hY2 i))
  have hinterp :
      eLpNorm S (2 : ℝ≥0∞) μ ^ (2 : ℝ) ≤
        eLpNorm S (ENNReal.ofReal pr) μ ^ (pr / (3 - pr)) *
          eLpNorm S (3 : ℝ≥0∞) μ ^ (3 * (2 - pr) / (3 - pr)) :=
    eLpNorm_two_sq_le_low_p_mul_three
      (μ := μ) (p := pr) hp0 hp2 hS2.aestronglyMeasurable
  have h2 :
      eLpNorm S (2 : ℝ≥0∞) μ = ENNReal.ofReal A := by
    dsimp [S, Y, A]
    exact khintchine_subGaussian_l2_unitVariance
      (μ := μ) (X := X) a hindep hX2 hmean hvar
  have h3raw :
      eLpNorm (fun ω => ∑ i, a i * X i ω) ((3 : ℝ≥0) : ℝ≥0∞) μ
        ≤ ENNReal.ofReal
          (16 * Real.sqrt 2 * K * Real.sqrt ((3 : ℝ≥0) : ℝ) * coeffL2Norm a) :=
    khintchine_subGaussian_upper_psi2Norm
      (μ := μ) (X := X) a (K := K) (p := (3 : ℝ≥0))
      hindep hXm hXsg hmean hK hKnorm (by norm_num : 2 ≤ ((3 : ℝ≥0) : ℝ))
  have h3 :
      eLpNorm S (3 : ℝ≥0∞) μ ≤ ENNReal.ofReal (B * A) := by
    dsimp [S, Y, A, B]
    simpa [mul_assoc] using h3raw
  have hLptop : eLpNorm S (ENNReal.ofReal pr) μ ≠ ∞ := by
    have hp_le_three : ENNReal.ofReal pr ≤ (3 : ℝ≥0∞) := by
      dsimp [pr]
      rw [hpENN]
      exact_mod_cast (by linarith : (p : ℝ) ≤ 3)
    have hmono :
        eLpNorm S (ENNReal.ofReal pr) μ ≤ eLpNorm S (3 : ℝ≥0∞) μ :=
      lpNorm_mono_exponent (μ := μ) (X := S)
        (p := ENNReal.ofReal pr) (q := (3 : ℝ≥0∞))
        hp_le_three hS2.aestronglyMeasurable
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmono.trans h3)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, coeffL2Norm]
    exact Real.sqrt_nonneg _
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hlow :
      ENNReal.ofReal
          (A / B ^ ((3 * (2 - pr) / (3 - pr)) / (pr / (3 - pr)))) ≤
        eLpNorm S (ENNReal.ofReal pr) μ :=
    khintchine_low_p_lower_of_interpolation
      (Lp := eLpNorm S (ENNReal.ofReal pr) μ)
      (L2 := eLpNorm S (2 : ℝ≥0∞) μ)
      (L3 := eLpNorm S (3 : ℝ≥0∞) μ)
      (A := A) (B := B) (p := pr)
      hp0 hp2 hinterp h2 h3 hLptop hA_nonneg hB_pos
  have hexp :
      (3 * (2 - pr) / (3 - pr)) / (pr / (3 - pr)) =
        3 * (2 - pr) / pr := by
    have hq : 3 - pr ≠ 0 := sub_ne_zero.mpr (by dsimp [pr]; linarith : 3 ≠ (p : ℝ))
    have hpne : pr ≠ 0 := by dsimp [pr]; exact ne_of_gt hp0
    field_simp [hq, hpne]
  rw [hexp] at hlow
  rw [hpENN] at hlow
  simpa [S, Y, A, B, pr] using hlow

/-- HDP Exercise 2.6.4: the bounded-variable Hoeffding inequality is recovered
as the bounded-specialization already formalized earlier in Chapter 2. -/
theorem bounded_hoeffding_from_general
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {m M : ι → ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (m i) (M i))
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ∑ i, (X i ω - μ[X i])}
      ≤ Real.exp (-(2 * t ^ 2) / boundedRangeSqSum m M) :=
  hoeffding_bounded (μ := μ) (X := X) (m := m) (M := M)
    hindep hXm hbdd ht

end Sums

end LeanFpAnalysis.HDP
