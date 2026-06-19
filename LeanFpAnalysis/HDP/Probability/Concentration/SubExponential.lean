import LeanFpAnalysis.HDP.Probability.Concentration.SubGaussian
import LeanFpAnalysis.HDP.Probability.Concentration.Chernoff

/-!
# Sub-exponential Random Variables

Book-facing definitions and first reusable facts for HDP Chapter 2, Section 2.7.

The primary gauge is the `ψ₁` Orlicz condition
`E exp(|X| / K) ≤ 2`.  This file deliberately builds on the existing
`ψ₂` API in `SubGaussian.lean`, so later Bernstein results can reuse the same
finite-sum and MGF style instead of introducing parallel abstractions.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace LeanFpAnalysis.HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Definitions

/-- HDP Proposition 2.7.1(a): two-sided sub-exponential tail decay with
scale `K`. -/
def subExponentialTailCondition (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ t, 0 ≤ t →
      μ.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-(t / K))

/-- HDP Proposition 2.7.1(b): moment growth at most `K p` for `p ≥ 1`. -/
def subExponentialMomentCondition (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ p : ℝ≥0, 1 ≤ (p : ℝ) →
      MemLp X (p : ℝ≥0∞) μ ∧
        eLpNorm X (p : ℝ≥0∞) μ ≤ ENNReal.ofReal (K * (p : ℝ))

/-- HDP Proposition 2.7.1(c): local MGF control for `|X|`. -/
def subExponentialAbsMGFCondition (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ θ, 0 ≤ θ → θ ≤ 1 / K →
      Integrable (fun ω => Real.exp (θ * |X ω|)) μ ∧
        ∫ ω, Real.exp (θ * |X ω|) ∂μ ≤ Real.exp (K * θ)

/-- HDP Definition 2.7.5, the `ψ₁` Orlicz integrability condition
`E exp(|X| / K) ≤ 2` for a positive scale `K`. -/
def subExponentialOrliczCondition (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    Integrable (fun ω => Real.exp (|X ω| / K)) μ ∧
      ∫ ω, Real.exp (|X ω| / K) ∂μ ≤ 2

/-- HDP Proposition 2.7.1(e): for centered variables, local signed MGF control
in the book's convention. -/
def subExponentialMGFCondition (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ θ, |θ| ≤ 1 / K →
      Integrable (fun ω => Real.exp (θ * X ω)) μ ∧
        mgf X μ θ ≤ Real.exp (K ^ 2 * θ ^ 2)

/-- HDP Definition 2.7.5: a random variable is sub-exponential when it
satisfies the `ψ₁` Orlicz condition at some positive scale. -/
def IsSubExponential (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ K, subExponentialOrliczCondition X μ K

/-- HDP Definition 2.7.5: the sub-exponential norm
`‖X‖_{ψ₁} = inf {K > 0 : E exp(|X| / K) ≤ 2}`. -/
def subExponentialNorm (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | subExponentialOrliczCondition X μ K}

/-- A concrete Orlicz scale makes the random variable sub-exponential. -/
theorem isSubExponential_of_subExponentialOrliczCondition
    {X : Ω → ℝ} {K : ℝ}
    (hX : subExponentialOrliczCondition X μ K) :
    IsSubExponential X μ :=
  ⟨K, hX⟩

/-- Any admissible `ψ₁` scale bounds the sub-exponential norm from above. -/
theorem subExponentialNorm_le_of_subExponentialOrliczCondition
    {X : Ω → ℝ} {K : ℝ}
    (hX : subExponentialOrliczCondition X μ K) :
    subExponentialNorm X μ ≤ K := by
  unfold subExponentialNorm
  exact csInf_le
    ⟨0, fun L hL => hL.1.le⟩
    hX

/-- The `ψ₁` gauge is always nonnegative. If no Orlicz scale is admissible,
the defining `sInf` is the empty infimum, which is `0` in `ℝ`. -/
theorem subExponentialNorm_nonneg (X : Ω → ℝ) (μ : Measure Ω) :
    0 ≤ subExponentialNorm X μ := by
  unfold subExponentialNorm
  by_cases hne :
      ({K : ℝ | subExponentialOrliczCondition X μ K}).Nonempty
  · exact le_csInf hne fun K hK => hK.1.le
  · have hempty :
        {K : ℝ | subExponentialOrliczCondition X μ K} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

/-- Every positive scale is admissible for the zero random variable. -/
theorem subExponentialOrliczCondition_zero
    [IsProbabilityMeasure μ] {K : ℝ} (hK : 0 < K) :
    subExponentialOrliczCondition (fun _ω : Ω => (0 : ℝ)) μ K := by
  refine ⟨hK, ?_, ?_⟩
  · simp
  · simp

/-- The zero random variable has `ψ₁` norm zero. -/
theorem subExponentialNorm_zero [IsProbabilityMeasure μ] :
    subExponentialNorm (fun _ω : Ω => (0 : ℝ)) μ = 0 := by
  refine le_antisymm ?_ (subExponentialNorm_nonneg _ μ)
  exact le_of_forall_gt_imp_ge_of_dense fun ε hε =>
    subExponentialNorm_le_of_subExponentialOrliczCondition
      (μ := μ) (X := fun _ω : Ω => (0 : ℝ)) (K := ε)
      (subExponentialOrliczCondition_zero (μ := μ) (K := ε) hε)

/-- Admissible `ψ₁` scales are monotone: if `K` works and `K ≤ L`, then
the larger scale `L` also works. -/
theorem subExponentialOrliczCondition_mono_scale
    {X : Ω → ℝ} {K L : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subExponentialOrliczCondition X μ K)
    (hKL : K ≤ L) :
    subExponentialOrliczCondition X μ L := by
  rcases hX with ⟨hKpos, hInt, hBound⟩
  have hLpos : 0 < L := hKpos.trans_le hKL
  have hrecip : 1 / L ≤ 1 / K :=
    (one_div_le_one_div hLpos hKpos).mpr hKL
  have hpoint :
      ∀ ω, Real.exp (|X ω| / L) ≤ Real.exp (|X ω| / K) := by
    intro ω
    rw [Real.exp_le_exp]
    calc
      |X ω| / L = |X ω| * (1 / L) := by ring
      _ ≤ |X ω| * (1 / K) :=
        mul_le_mul_of_nonneg_left hrecip (abs_nonneg _)
      _ = |X ω| / K := by ring
  have hsmall_aem :
      AEMeasurable (fun ω => Real.exp (|X ω| / L)) μ := by
    fun_prop
  have hIntL :
      Integrable (fun ω => Real.exp (|X ω| / L)) μ := by
    refine hInt.mono hsmall_aem.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
        using hpoint ω
  refine ⟨hLpos, hIntL, ?_⟩
  calc
    ∫ ω, Real.exp (|X ω| / L) ∂μ
        ≤ ∫ ω, Real.exp (|X ω| / K) ∂μ :=
      integral_mono hIntL hInt hpoint
    _ ≤ 2 := hBound

/-- If the `ψ₁` norm is positive and finite through an admissible scale, then
twice the norm is itself an admissible Orlicz scale. This is the basic
`sInf` bridge used to pass from scale statements to norm statements without
assuming the infimum is attained. -/
theorem subExponentialOrliczCondition_two_mul_norm
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ)
    (hXse : IsSubExponential X μ)
    (hpos : 0 < subExponentialNorm X μ) :
    subExponentialOrliczCondition X μ (2 * subExponentialNorm X μ) := by
  let S : Set ℝ := {K : ℝ | subExponentialOrliczCondition X μ K}
  have hSnonempty : S.Nonempty := by
    rcases hXse with ⟨K, hK⟩
    exact ⟨K, hK⟩
  obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos (s := S) hSnonempty hpos
  have hKlt' : K < subExponentialNorm X μ + subExponentialNorm X μ := by
    simpa [subExponentialNorm, S] using hKlt
  have hKlt_two : K < 2 * subExponentialNorm X μ := by
    nlinarith
  exact subExponentialOrliczCondition_mono_scale hXm hK hKlt_two.le

/-- Scaling infrastructure for the `ψ₁` gauge: multiplying by a nonzero scalar
multiplies every admissible scale by `|a|`. -/
theorem subExponentialOrliczCondition_const_mul
    {X : Ω → ℝ} {K a : ℝ}
    (ha : a ≠ 0)
    (hX : subExponentialOrliczCondition X μ K) :
    subExponentialOrliczCondition (fun ω => a * X ω) μ (|a| * K) := by
  rcases hX with ⟨hKpos, hInt, hBound⟩
  have hscale_pos : 0 < |a| * K :=
    mul_pos (abs_pos.mpr ha) hKpos
  have hEq :
      (fun ω => Real.exp (|a * X ω| / (|a| * K)))
        = fun ω => Real.exp (|X ω| / K) := by
    funext ω
    congr 1
    rw [abs_mul]
    field_simp [(abs_pos.mpr ha).ne', hKpos.ne']
  refine ⟨hscale_pos, ?_, ?_⟩
  · rw [hEq]
    exact hInt
  · rw [hEq]
    exact hBound

/-- Norm upper-bound form of `ψ₁` scaling. -/
theorem subExponentialNorm_const_mul_le
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K a : ℝ}
    (hX : subExponentialOrliczCondition X μ K) :
    subExponentialNorm (fun ω => a * X ω) μ ≤ |a| * K := by
  by_cases ha : a = 0
  · have hzero :
        (fun ω => a * X ω) = fun _ω : Ω => (0 : ℝ) := by
      funext ω
      simp [ha]
    rw [hzero, subExponentialNorm_zero]
    simp [ha]
  · exact
      subExponentialNorm_le_of_subExponentialOrliczCondition
        (subExponentialOrliczCondition_const_mul (μ := μ) (X := X) (K := K)
          (a := a) ha hX)

/-- Scaling infrastructure for the local signed MGF condition in
Proposition 2.7.1(e). Multiplication by a nonzero scalar multiplies the
admissible local-MGF scale by `|a|`. -/
theorem subExponentialMGFCondition_const_mul
    {X : Ω → ℝ} {K a : ℝ}
    (ha : a ≠ 0)
    (hX : subExponentialMGFCondition X μ K) :
    subExponentialMGFCondition (fun ω => a * X ω) μ (|a| * K) := by
  rcases hX with ⟨hKpos, hmgf⟩
  have habs_pos : 0 < |a| := abs_pos.mpr ha
  have hscale_pos : 0 < |a| * K := mul_pos habs_pos hKpos
  refine ⟨hscale_pos, fun θ hθ => ?_⟩
  have hθa_window : |θ * a| ≤ 1 / K := by
    rw [abs_mul]
    calc
      |θ| * |a| ≤ (1 / (|a| * K)) * |a| :=
        mul_le_mul_of_nonneg_right hθ (abs_nonneg a)
      _ = 1 / K := by
        field_simp [habs_pos.ne', hKpos.ne']
  rcases hmgf (θ * a) hθa_window with ⟨hint, hbound⟩
  have hmgf_eq : mgf (fun ω => a * X ω) μ θ = mgf X μ (θ * a) := by
    unfold mgf
    congr 1
    funext ω
    change Real.exp (θ * (a * X ω)) = Real.exp (θ * a * X ω)
    apply congrArg Real.exp
    ring_nf
  refine ⟨?_, ?_⟩
  · simpa [mul_assoc, mul_comm, mul_left_comm] using hint
  · calc
      mgf (fun ω => a * X ω) μ θ = mgf X μ (θ * a) := hmgf_eq
      _ ≤ Real.exp (K ^ 2 * (θ * a) ^ 2) := hbound
      _ = Real.exp ((|a| * K) ^ 2 * θ ^ 2) := by
        congr 1
        rw [mul_pow, mul_pow]
        rw [sq_abs]
        ring

/-- The local signed MGF condition is monotone in the scale parameter.  A
larger scale gives a smaller admissible neighborhood and a larger quadratic
envelope. -/
theorem subExponentialMGFCondition_mono_scale
    {X : Ω → ℝ} {K L : ℝ}
    (hX : subExponentialMGFCondition X μ K)
    (hKL : K ≤ L) :
    subExponentialMGFCondition X μ L := by
  rcases hX with ⟨hKpos, hmgf⟩
  have hLpos : 0 < L := hKpos.trans_le hKL
  refine ⟨hLpos, fun θ hθ => ?_⟩
  have hrecip : 1 / L ≤ 1 / K :=
    (one_div_le_one_div hLpos hKpos).mpr hKL
  have hθK : |θ| ≤ 1 / K := hθ.trans hrecip
  rcases hmgf θ hθK with ⟨hint, hbound⟩
  refine ⟨hint, hbound.trans ?_⟩
  have hsqKL : K ^ 2 ≤ L ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_pos hKpos, abs_of_pos hLpos] using hKL
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hsqKL (sq_nonneg θ))

/-- The zero random variable satisfies the centered local MGF condition at
every positive scale. -/
theorem subExponentialMGFCondition_zero
    [IsProbabilityMeasure μ] {K : ℝ} (hK : 0 < K) :
    subExponentialMGFCondition (fun _ω : Ω => (0 : ℝ)) μ K := by
  refine ⟨hK, fun θ _hθ => ?_⟩
  refine ⟨?_, ?_⟩
  · simp
  · calc
      mgf (fun _ω : Ω => (0 : ℝ)) μ θ = 1 := by simp [mgf]
      _ = Real.exp 0 := by norm_num
      _ ≤ Real.exp (K ^ 2 * θ ^ 2) := Real.exp_le_exp.mpr (by positivity)

/-- Uniform scalar MGF estimate used in the weighted Bernstein inequality.
If `|a| ≤ A` and `|θ| ≤ 1 / (K A)`, then the MGF of `aX` has the precise
quadratic proxy `K^2 a^2`; the proof includes the zero-scalar case. -/
theorem subExponentialMGFCondition_const_mul_bound_of_abs_le
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K A a θ : ℝ}
    (hX : subExponentialMGFCondition X μ K)
    (hApos : 0 < A)
    (haA : |a| ≤ A)
    (hθ : |θ| ≤ 1 / (K * A)) :
    Integrable (fun ω => Real.exp (θ * (a * X ω))) μ ∧
      mgf (fun ω => a * X ω) μ θ ≤ Real.exp (K ^ 2 * a ^ 2 * θ ^ 2) := by
  rcases hX with ⟨hKpos, hmgf⟩
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨?_, ?_⟩
    · simp
    · calc
        mgf (fun ω => (0 : ℝ) * X ω) μ θ = 1 := by simp [mgf]
        _ = Real.exp 0 := by norm_num
        _ ≤ Real.exp (K ^ 2 * 0 ^ 2 * θ ^ 2) := by norm_num
  · have hθa_window : |θ * a| ≤ 1 / K := by
      rw [abs_mul]
      calc
        |θ| * |a| ≤ (1 / (K * A)) * A := by
          exact mul_le_mul hθ haA (abs_nonneg a) (by positivity)
        _ = 1 / K := by
          field_simp [hKpos.ne', hApos.ne']
    rcases hmgf (θ * a) hθa_window with ⟨hint, hbound⟩
    have hmgf_eq : mgf (fun ω => a * X ω) μ θ = mgf X μ (θ * a) := by
      unfold mgf
      congr 1
      funext ω
      change Real.exp (θ * (a * X ω)) = Real.exp (θ * a * X ω)
      apply congrArg Real.exp
      ring_nf
    refine ⟨?_, ?_⟩
    · simpa [mul_assoc, mul_comm, mul_left_comm] using hint
    · calc
        mgf (fun ω => a * X ω) μ θ = mgf X μ (θ * a) := hmgf_eq
        _ ≤ Real.exp (K ^ 2 * (θ * a) ^ 2) := hbound
        _ = Real.exp (K ^ 2 * a ^ 2 * θ ^ 2) := by
          congr 1
          ring

/-- Remark 2.7.9, reusable local-MGF principle: a centered random variable
that is almost surely bounded by `K` in absolute value satisfies the local
sub-exponential signed-MGF condition at scale `K`.  This is Hoeffding's lemma
viewed through the Section 2.7 local-MGF API. -/
theorem subExponentialMGFCondition_of_ae_abs_le_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hK : 0 < K)
    (hXm : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K)
    (hmean : ∫ ω, X ω ∂μ = 0) :
    subExponentialMGFCondition X μ K := by
  have hbdd : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-K) K := by
    filter_upwards [hbound] with ω hω
    simpa [Set.mem_Icc, abs_le] using hω
  have hHas :
      HasSubgaussianMGF X ((‖K - -K‖₊ / 2) ^ 2) μ :=
    bounded_centered_hasSubgaussianMGF
      (μ := μ) (X := X) (a := -K) (b := K) hXm hbdd hmean
  refine ⟨hK, fun θ _hθ => ?_⟩
  refine ⟨hHas.integrable_exp_mul θ, ?_⟩
  have hproxy :
      (((((‖K - -K‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * θ ^ 2 / 2)
        ≤ K ^ 2 * θ ^ 2) := by
    have hscale : ((((‖K - -K‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)) = K ^ 2 := by
      rw [NNReal.coe_pow, NNReal.coe_div]
      simp [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < K + K)]
    rw [hscale]
    have hhalf : K ^ 2 * θ ^ 2 / 2 ≤ K ^ 2 * θ ^ 2 := by
      nlinarith [sq_nonneg K, sq_nonneg θ]
    simpa [mul_div_assoc] using hhalf
  exact (hHas.mgf_le θ).trans (Real.exp_le_exp.mpr hproxy)

/-- Elementary exponential domination used to control moments from a `ψ₁`
Orlicz scale. -/
theorem real_nonneg_le_exp_self {x : ℝ} (_hx : 0 ≤ x) : x ≤ Real.exp x := by
  have h := Real.add_one_le_exp x
  nlinarith [Real.exp_pos x]

/-- Linear Orlicz addition estimate for the `ψ₁` gauge. -/
theorem exp_abs_add_div_le_weighted_exp_abs {x y K L : ℝ}
    (hK : 0 < K) (hL : 0 < L) :
    Real.exp (|x + y| / (K + L))
      ≤ K / (K + L) * Real.exp (|x| / K)
        + L / (K + L) * Real.exp (|y| / L) := by
  let a : ℝ := K / (K + L)
  let b : ℝ := L / (K + L)
  have hKL : 0 < K + L := add_pos hK hL
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [hKL.ne']
  have hlin :
      |x + y| / (K + L) ≤ a * (|x| / K) + b * (|y| / L) := by
    calc
      |x + y| / (K + L) ≤ (|x| + |y|) / (K + L) := by
        exact div_le_div_of_nonneg_right (abs_add_le x y) hKL.le
      _ = a * (|x| / K) + b * (|y| / L) := by
        dsimp [a, b]
        field_simp [hK.ne', hL.ne', hKL.ne']
  have hconv :
      Real.exp (a * (|x| / K) + b * (|y| / L))
        ≤ a * Real.exp (|x| / K) + b * Real.exp (|y| / L) := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (convexOn_exp.2 (Set.mem_univ (|x| / K)) (Set.mem_univ (|y| / L))
        ha_nonneg hb_nonneg hab)
  calc
    Real.exp (|x + y| / (K + L))
        ≤ Real.exp (a * (|x| / K) + b * (|y| / L)) :=
      Real.exp_le_exp.mpr hlin
    _ ≤ a * Real.exp (|x| / K) + b * Real.exp (|y| / L) := hconv
    _ = K / (K + L) * Real.exp (|x| / K)
        + L / (K + L) * Real.exp (|y| / L) := rfl

/-- Admissible `ψ₁` Orlicz scales add. -/
theorem subExponentialOrliczCondition_add
    {X Y : Ω → ℝ} {K L : ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : subExponentialOrliczCondition X μ K)
    (hY : subExponentialOrliczCondition Y μ L) :
    subExponentialOrliczCondition (fun ω => X ω + Y ω) μ (K + L) := by
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
  let F : Ω → ℝ := fun ω => Real.exp (|X ω + Y ω| / (K + L))
  let G : Ω → ℝ :=
    fun ω => a * Real.exp (|X ω| / K) + b * Real.exp (|Y ω| / L)
  have hpoint : ∀ ω, F ω ≤ G ω := by
    intro ω
    dsimp [F, G, a, b]
    exact exp_abs_add_div_le_weighted_exp_abs hKpos hLpos
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
      ∫ ω, Real.exp (|X ω + Y ω| / (K + L)) ∂μ
          = ∫ ω, F ω ∂μ := rfl
      _ ≤ ∫ ω, G ω ∂μ :=
        integral_mono hFInt hGInt hpoint
      _ = a * ∫ ω, Real.exp (|X ω| / K) ∂μ
          + b * ∫ ω, Real.exp (|Y ω| / L) ∂μ := by
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

/-- Norm upper-bound form of `ψ₁` addition. -/
theorem subExponentialNorm_add_le_of_subExponentialOrliczCondition
    {X Y : Ω → ℝ} {K L : ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : subExponentialOrliczCondition X μ K)
    (hY : subExponentialOrliczCondition Y μ L) :
    subExponentialNorm (fun ω => X ω + Y ω) μ ≤ K + L :=
  subExponentialNorm_le_of_subExponentialOrliczCondition
    (subExponentialOrliczCondition_add hXm hYm hX hY)

/-- Triangle inequality for the `ψ₁` gauge on sub-exponential random
variables. -/
theorem subExponentialNorm_add_le
    {X Y : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hXse : IsSubExponential X μ) (hYse : IsSubExponential Y μ) :
    subExponentialNorm (fun ω => X ω + Y ω) μ
      ≤ subExponentialNorm X μ + subExponentialNorm Y μ := by
  have hXset :
      ({K : ℝ | subExponentialOrliczCondition X μ K}).Nonempty := by
    simpa [IsSubExponential] using hXse
  have hYset :
      ({L : ℝ | subExponentialOrliczCondition Y μ L}).Nonempty := by
    simpa [IsSubExponential] using hYse
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro r hr
  have hgap : 0 < r - (subExponentialNorm X μ + subExponentialNorm Y μ) := by
    linarith
  have hhalf : 0 < (r - (subExponentialNorm X μ + subExponentialNorm Y μ)) / 2 := by
    positivity
  obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos hXset hhalf
  obtain ⟨L, hL, hLlt⟩ := Real.lt_sInf_add_pos hYset hhalf
  have hKlt' :
      K < subExponentialNorm X μ
        + (r - (subExponentialNorm X μ + subExponentialNorm Y μ)) / 2 := by
    simpa [subExponentialNorm] using hKlt
  have hLlt' :
      L < subExponentialNorm Y μ
        + (r - (subExponentialNorm X μ + subExponentialNorm Y μ)) / 2 := by
    simpa [subExponentialNorm] using hLlt
  have hadd :
      subExponentialNorm (fun ω => X ω + Y ω) μ ≤ K + L :=
    subExponentialNorm_add_le_of_subExponentialOrliczCondition hXm hYm hK hL
  have hsum_lt : K + L < r := by
    linarith
  exact hadd.trans hsum_lt.le

/-- Constant random variables are sub-exponential. -/
theorem isSubExponential_const
    [IsProbabilityMeasure μ] (a : ℝ) :
    IsSubExponential (fun _ω : Ω => a) μ := by
  by_cases ha : a = 0
  · rw [ha]
    exact isSubExponential_of_subExponentialOrliczCondition
      (subExponentialOrliczCondition_zero (μ := μ) (K := 1) (by norm_num))
  · refine isSubExponential_of_subExponentialOrliczCondition
      (K := |a| / Real.log 2) ?_
    have hlogpos : 0 < Real.log 2 := by
      rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hfun :
        (fun _ω : Ω => Real.exp (|(a : ℝ)| / (|a| / Real.log 2)))
          = fun _ω => (2 : ℝ) := by
      funext ω
      have harg : |a| / (|a| / Real.log 2) = Real.log 2 := by
        field_simp [(abs_pos.mpr ha).ne', hlogpos.ne']
      rw [harg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    refine ⟨by positivity, ?_, ?_⟩
    · rw [hfun]
      simp
    · rw [hfun]
      simp

/-- A constant random variable has `ψ₁` norm bounded by the exact
Orlicz-point scale. -/
theorem subExponentialNorm_const_le_abs_div_log_two
    [IsProbabilityMeasure μ] (a : ℝ) :
    subExponentialNorm (fun _ω : Ω => a) μ ≤ |a| / Real.log 2 := by
  by_cases ha : a = 0
  · rw [ha]
    simp [subExponentialNorm_zero]
  · refine subExponentialNorm_le_of_subExponentialOrliczCondition ?_
    have hlogpos : 0 < Real.log 2 := by
      rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hfun :
        (fun _ω : Ω => Real.exp (|(a : ℝ)| / (|a| / Real.log 2)))
          = fun _ω => (2 : ℝ) := by
      funext ω
      have harg : |a| / (|a| / Real.log 2) = Real.log 2 := by
        field_simp [(abs_pos.mpr ha).ne', hlogpos.ne']
      rw [harg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    refine ⟨by positivity, ?_, ?_⟩
    · rw [hfun]
      simp
    · rw [hfun]
      simp

end Definitions

section OrliczConsequences

/-- The `ψ₁` Orlicz condition implies the sub-exponential tail bound with
the same scale, by Markov's inequality. -/
theorem subExponentialOrliczCondition_tail_le
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K t : ℝ}
    (hX : subExponentialOrliczCondition X μ K) (_ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-(t / K)) := by
  rcases hX with ⟨hKpos, hInt, hBound⟩
  let Y : Ω → ℝ := fun ω => Real.exp (|X ω| / K)
  have hY_nonneg : 0 ≤ᵐ[μ] Y :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have hthreshold_pos : 0 < Real.exp (t / K) :=
    Real.exp_pos _
  have hsubset :
      {ω | t ≤ |X ω|} ⊆ {ω | Real.exp (t / K) ≤ Y ω} := by
    intro ω hω
    change Real.exp (t / K) ≤ Y ω
    rw [Real.exp_le_exp]
    exact div_le_div_of_nonneg_right hω hKpos.le
  have hmarkov :=
    markov_inequality
      (μ := μ) (X := Y) hY_nonneg hInt
      (t := Real.exp (t / K)) hthreshold_pos
  calc
    μ.real {ω | t ≤ |X ω|}
        ≤ μ.real {ω | Real.exp (t / K) ≤ Y ω} :=
      MeasureTheory.measureReal_mono hsubset
    _ ≤ (∫ ω, Y ω ∂μ) / Real.exp (t / K) := hmarkov
    _ ≤ 2 / Real.exp (t / K) := by
      exact div_le_div_of_nonneg_right hBound hthreshold_pos.le
    _ = 2 * Real.exp (-(t / K)) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]

/-- Predicate form of the Orlicz-to-tail implication in
HDP Proposition 2.7.1. -/
theorem subExponentialTailCondition_of_subExponentialOrliczCondition
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hX : subExponentialOrliczCondition X μ K) :
    subExponentialTailCondition X μ K :=
  ⟨hX.1, fun t ht => subExponentialOrliczCondition_tail_le (t := t) hX ht⟩

/-- HDP Proposition 2.7.1, direction `(d) ⇒ (c)`: the Orlicz point condition
implies local MGF control for `|X|` with the same scale. -/
theorem subExponentialAbsMGFCondition_of_subExponentialOrliczCondition
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hX : subExponentialOrliczCondition X μ K) :
    subExponentialAbsMGFCondition X μ K := by
  rcases hX with ⟨hKpos, hInt, hBound⟩
  refine ⟨hKpos, fun θ hθ_nonneg hθ_le => ?_⟩
  let Y : Ω → ℝ := fun ω => Real.exp (|X ω| / K)
  let α : ℝ := K * θ
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity
  have hα_le_one : α ≤ 1 := by
    dsimp [α]
    have hmul := mul_le_mul_of_nonneg_left hθ_le hKpos.le
    field_simp [hKpos.ne'] at hmul
    simpa [mul_comm] using hmul
  have hY_nonneg : ∀ ω, 0 ≤ Y ω :=
    fun ω => (Real.exp_pos _).le
  have hY_ge_one : ∀ ω, 1 ≤ Y ω := by
    intro ω
    dsimp [Y]
    rw [← Real.exp_zero, Real.exp_le_exp]
    exact div_nonneg (abs_nonneg _) hKpos.le
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
      (fun ω => Y ω ^ α) = fun ω => Real.exp (θ * |X ω|) := by
    funext ω
    dsimp [Y, α]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    field_simp [hKpos.ne']
  have htarget_int :
      Integrable (fun ω => Real.exp (θ * |X ω|)) μ := by
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
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  refine ⟨htarget_int, ?_⟩
  calc
    ∫ ω, Real.exp (θ * |X ω|) ∂μ
        = ∫ ω, Y ω ^ α ∂μ := by rw [← hpow_eq]
    _ ≤ (∫ ω, Y ω ∂μ) ^ α := hYpow_le
    _ ≤ (2 : ℝ) ^ α :=
      Real.rpow_le_rpow hY_int_nonneg hBound hα_nonneg
    _ = Real.exp (Real.log 2 * α) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp α := by
      rw [Real.exp_le_exp]
      exact mul_le_of_le_one_left hα_nonneg hlog2_le_one
    _ = Real.exp (K * θ) := rfl

/-- HDP Proposition 2.7.1, direction `(c) ⇒ (d)`: local MGF control of
`|X|` implies the Orlicz point condition, with an explicit absolute scale
change. -/
theorem subExponentialOrliczCondition_of_subExponentialAbsMGFCondition
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hX : subExponentialAbsMGFCondition X μ K) :
    subExponentialOrliczCondition X μ (K / Real.log 2) := by
  rcases hX with ⟨hKpos, hMGF⟩
  have hlogpos : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hlog_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  let θ : ℝ := Real.log 2 / K
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ]
    positivity
  have hθ_le : θ ≤ 1 / K := by
    dsimp [θ]
    exact div_le_div_of_nonneg_right hlog_le_one hKpos.le
  rcases hMGF θ hθ_nonneg hθ_le with ⟨hInt, hBound⟩
  have hscale_pos : 0 < K / Real.log 2 := by
    positivity
  have hfun :
      (fun ω => Real.exp (|X ω| / (K / Real.log 2)))
        = fun ω => Real.exp (θ * |X ω|) := by
    funext ω
    congr 1
    dsimp [θ]
    field_simp [hKpos.ne', hlogpos.ne']
  refine ⟨hscale_pos, ?_, ?_⟩
  · rw [hfun]
    exact hInt
  · rw [hfun]
    calc
      ∫ ω, Real.exp (θ * |X ω|) ∂μ ≤ Real.exp (K * θ) := hBound
      _ = 2 := by
        dsimp [θ]
        field_simp [hKpos.ne']
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Real-variable estimate behind the `ψ₁` Orlicz-to-moment implication. -/
lemma rpow_div_le_exp {y r : ℝ} (hy : 0 ≤ y) (hr : 0 < r) :
    y ^ r ≤ Real.exp (r * y) := by
  by_cases hy0 : y = 0
  · subst hy0
    simp [Real.zero_rpow hr.ne']
  · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    have hlog_le_sub := Real.log_le_sub_one_of_pos hypos
    have hlog_le : Real.log y ≤ y := by
      linarith
    have hmul : r * Real.log y ≤ r * y :=
      mul_le_mul_of_nonneg_left hlog_le hr.le
    rw [Real.rpow_def_of_pos hypos]
    exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hmul)

/-- Global second-order Taylor remainder bound for the real exponential. -/
lemma abs_exp_sub_one_sub_id_le_sq_mul_exp_abs (x : ℝ) :
    |Real.exp x - 1 - x| ≤ x ^ 2 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x := (x : ℂ)) 2
  norm_num at h
  have hsum :
      (∑ m ∈ Finset.range 2, (x : ℂ) ^ m / (m.factorial : ℂ)) = 1 + x := by
    simp [Finset.sum_range_succ]
  have hnorm :
      ‖Complex.exp (x : ℂ) - (1 + (x : ℂ))‖ =
        |Real.exp x - 1 - x| := by
    rw [← Complex.ofReal_exp x]
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_sub]
    rw [show ‖((Real.exp x - (1 + x) : ℝ) : ℂ)‖ =
        |Real.exp x - (1 + x)| from RCLike.norm_ofReal (K := ℂ) _]
    congr 1
    ring
  rw [hsum] at h
  rwa [hnorm] at h

/-- Pointwise upper Taylor bound for the real exponential with a remainder
that can be dominated by a `ψ₁` Orlicz integrand. -/
lemma exp_le_one_add_self_add_sq_mul_exp_abs (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  have hrem := abs_exp_sub_one_sub_id_le_sq_mul_exp_abs x
  have hle : Real.exp x - 1 - x ≤ x ^ 2 * Real.exp |x| :=
    (le_abs_self _).trans hrem
  linarith

/-- Under the local Bernstein window `|θ| ≤ 1/(8K)`, the Taylor remainder is
controlled by the `ψ₁` Orlicz integrand at scale `K`. -/
lemma exp_taylor_remainder_le_subExponential_orlicz_dom
    {K θ x : ℝ} (hK : 0 < K) (hθ : |θ| ≤ 1 / (8 * K)) :
    (θ * x) ^ 2 * Real.exp |θ * x|
      ≤ 16 * K ^ 2 * θ ^ 2 * Real.exp (|x| / K) := by
  let y : ℝ := |x| / (4 * K)
  have h4Kpos : 0 < 4 * K := by positivity
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy_le_exp := rpow_div_le_exp (y := y) (r := (2 : ℝ)) hy_nonneg (by norm_num)
  have hxsq_le : x ^ 2 ≤ 16 * K ^ 2 * Real.exp (|x| / (2 * K)) := by
    have hscaled :
        |x| ^ (2 : ℝ) ≤ (4 * K) ^ (2 : ℝ) * Real.exp (|x| / (2 * K)) := by
      calc
        |x| ^ (2 : ℝ) = ((4 * K) * y) ^ (2 : ℝ) := by
          congr 1
          dsimp [y]
          field_simp [h4Kpos.ne']
        _ = (4 * K) ^ (2 : ℝ) * y ^ (2 : ℝ) := by
          rw [Real.mul_rpow h4Kpos.le hy_nonneg]
        _ ≤ (4 * K) ^ (2 : ℝ) * Real.exp ((2 : ℝ) * y) := by
          exact mul_le_mul_of_nonneg_left hy_le_exp (Real.rpow_nonneg h4Kpos.le 2)
        _ = (4 * K) ^ (2 : ℝ) * Real.exp (|x| / (2 * K)) := by
          congr 2
          dsimp [y]
          field_simp [hK.ne']
          ring
    rw [Real.rpow_two, Real.rpow_two] at hscaled
    calc
      x ^ 2 = |x| ^ 2 := by rw [sq_abs]
      _ ≤ (4 * K) ^ 2 * Real.exp (|x| / (2 * K)) := hscaled
      _ = 16 * K ^ 2 * Real.exp (|x| / (2 * K)) := by ring
  have hexp_le : Real.exp |θ * x| ≤ Real.exp (|x| / (8 * K)) := by
    rw [Real.exp_le_exp]
    rw [abs_mul]
    calc
      |θ| * |x| ≤ (1 / (8 * K)) * |x| :=
        mul_le_mul_of_nonneg_right hθ (abs_nonneg x)
      _ = |x| / (8 * K) := by ring
  have hmul_le :
      x ^ 2 * Real.exp |θ * x|
        ≤ (16 * K ^ 2 * Real.exp (|x| / (2 * K))) *
            Real.exp (|x| / (8 * K)) := by
    exact mul_le_mul hxsq_le hexp_le (Real.exp_pos _).le (by positivity)
  have hcombine :
      (16 * K ^ 2 * Real.exp (|x| / (2 * K))) * Real.exp (|x| / (8 * K))
        ≤ 16 * K ^ 2 * Real.exp (|x| / K) := by
    have hcoef_nonneg : 0 ≤ 16 * K ^ 2 := by positivity
    calc
      (16 * K ^ 2 * Real.exp (|x| / (2 * K))) * Real.exp (|x| / (8 * K))
          = 16 * K ^ 2 * Real.exp (|x| / (2 * K) + |x| / (8 * K)) := by
        rw [Real.exp_add]
        ring
      _ ≤ 16 * K ^ 2 * Real.exp (|x| / K) := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.exp_le_exp.mpr
          have hx_nonneg : 0 ≤ |x| := abs_nonneg x
          field_simp [hK.ne']
          nlinarith
        · exact hcoef_nonneg
  have hx_exp_le := hmul_le.trans hcombine
  calc
    (θ * x) ^ 2 * Real.exp |θ * x|
        = θ ^ 2 * (x ^ 2 * Real.exp |θ * x|) := by ring
    _ ≤ θ ^ 2 * (16 * K ^ 2 * Real.exp (|x| / K)) := by
      exact mul_le_mul_of_nonneg_left hx_exp_le (sq_nonneg θ)
    _ = 16 * K ^ 2 * θ ^ 2 * Real.exp (|x| / K) := by ring

/-- HDP Proposition 2.7.1, direction `(d) ⇒ (b)` with explicit absolute
constant: the Orlicz point condition at scale `K` implies
`‖X‖_{L^p} ≤ 2 K p` for all `p ≥ 1`. -/
theorem subExponentialMomentCondition_of_subExponentialOrliczCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hXm : AEStronglyMeasurable X μ)
    (hX : subExponentialOrliczCondition X μ K) :
    subExponentialMomentCondition X μ (2 * K) := by
  rcases hX with ⟨hKpos, hExpInt, hExp_le⟩
  refine ⟨by positivity, fun p hp => ?_⟩
  let r : ℝ := p
  have hr_ge_one : 1 ≤ r := by
    simpa [r] using hp
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr_ge_one
  let C : ℝ := K * r
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCnonneg : 0 ≤ C := hCpos.le
  have hCpow_nonneg : 0 ≤ C ^ r :=
    Real.rpow_nonneg hCnonneg r
  have hdom_int :
      Integrable (fun ω => C ^ r * Real.exp (|X ω| / K)) μ :=
    hExpInt.const_mul (C ^ r)
  have hpoint :
      ∀ ω, ‖X ω‖ ^ r ≤ C ^ r * Real.exp (|X ω| / K) := by
    intro ω
    let y : ℝ := |X ω| / C
    have hy_nonneg : 0 ≤ y :=
      div_nonneg (abs_nonneg _) hCnonneg
    have hy_le := rpow_div_le_exp (y := y) (r := r) hy_nonneg hr_pos
    have hscaled : |X ω| ^ r ≤ C ^ r * Real.exp (r * y) := by
      calc
        |X ω| ^ r = (C * y) ^ r := by
          congr 1
          dsimp [y]
          field_simp [hCpos.ne']
        _ = C ^ r * y ^ r := by
          rw [Real.mul_rpow hCnonneg hy_nonneg]
        _ ≤ C ^ r * Real.exp (r * y) :=
          mul_le_mul_of_nonneg_left hy_le hCpow_nonneg
    have hry : r * y = |X ω| / K := by
      dsimp [y, C]
      field_simp [hKpos.ne', hr_pos.ne']
    calc
      ‖X ω‖ ^ r = |X ω| ^ r := by
        rw [Real.norm_eq_abs]
      _ ≤ C ^ r * Real.exp (r * y) := hscaled
      _ = C ^ r * Real.exp (|X ω| / K) := by
        rw [hry]
  have hpow_int :
      Integrable (fun ω => ‖X ω‖ ^ r) μ := by
    refine hdom_int.mono ?_ ?_
    · exact (hXm.norm.aemeasurable.pow_const r).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        have htarget_nonneg : 0 ≤ ‖X ω‖ ^ r :=
          Real.rpow_nonneg (norm_nonneg _) r
        have hdom_nonneg : 0 ≤ C ^ r * Real.exp (|X ω| / K) :=
          mul_nonneg hCpow_nonneg (Real.exp_pos _).le
        calc
          ‖‖X ω‖ ^ r‖ = ‖X ω‖ ^ r := by
            rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
          _ ≤ C ^ r * Real.exp (|X ω| / K) := hpoint ω
          _ = ‖C ^ r * Real.exp (|X ω| / K)‖ := by
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
          ≤ ∫ ω, C ^ r * Real.exp (|X ω| / K) ∂μ :=
        integral_mono hpow_int hdom_int hpoint
      _ = C ^ r * ∫ ω, Real.exp (|X ω| / K) ∂μ := by
        rw [integral_const_mul]
      _ ≤ C ^ r * 2 :=
        mul_le_mul_of_nonneg_left hExp_le hCpow_nonneg
  have htwo_le_two_rpow : (2 : ℝ) ≤ 2 ^ r := by
    simpa [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hr_ge_one
  have hintegral_bound_C :
      ∫ ω, ‖X ω‖ ^ r ∂μ ≤ (2 * K * r) ^ r := by
    have hCpow_mul_two_le : C ^ r * 2 ≤ (2 * K * r) ^ r := by
      dsimp [C]
      calc
        (K * r) ^ r * 2
            ≤ (K * r) ^ r * 2 ^ r :=
          mul_le_mul_of_nonneg_left htwo_le_two_rpow
            (Real.rpow_nonneg hCnonneg r)
        _ = (2 * (K * r)) ^ r := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hCnonneg]
          ring
        _ = (2 * K * r) ^ r := by
          ring_nf
    exact hintegral_bound.trans hCpow_mul_two_le
  have hlp_real :
      MeasureTheory.lpNorm X (p : ℝ≥0∞) μ ≤ 2 * K * r := by
    rw [lpNorm_nnreal_eq_integral_norm_rpow
      (μ := μ) (f := X) (p := p)
      hp_ne_zero hXm]
    have hintegral_nonneg : 0 ≤ ∫ ω, ‖X ω‖ ^ r ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) r
    calc
      (∫ ω, ‖X ω‖ ^ r ∂μ) ^ ((p : ℝ≥0)⁻¹ : ℝ)
          ≤ ((2 * K * r) ^ r) ^ ((p : ℝ≥0)⁻¹ : ℝ) := by
        exact Real.rpow_le_rpow hintegral_nonneg hintegral_bound_C
          (by positivity)
      _ = 2 * K * r := by
        have hbase_pos : 0 < 2 * K * r := by
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

/-- A Markov-`L^p` tail bound extracted from HDP Proposition 2.7.1(b). -/
theorem subExponentialMomentCondition_tail_rpow_bound
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K t : ℝ} {p : ℝ≥0}
    (hX : subExponentialMomentCondition X μ K)
    (hp : 1 ≤ (p : ℝ)) (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} ≤ (K * (p : ℝ) / t) ^ (p : ℝ) := by
  rcases hX with ⟨hKpos, hMom⟩
  let r : ℝ := p
  have hr_ge_one : 1 ≤ r := by
    simpa [r] using hp
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr_ge_one
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    have : r = 0 := by
      simp [r, hp0]
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
  let B : ℝ := K * r
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
    have hleft : (I ^ r⁻¹) ^ r = I :=
      Real.rpow_inv_rpow hI_nonneg hr_pos.ne'
    simpa [hleft] using hpow
  calc
    μ.real {ω | t ≤ |X ω|} ≤ I / t ^ r := htail
    _ ≤ B ^ r / t ^ r :=
      div_le_div_of_nonneg_right hI_bound ht_rpow_pos.le
    _ = (B / t) ^ r := by
      rw [Real.div_rpow hB_nonneg ht.le]
    _ = (K * (p : ℝ) / t) ^ (p : ℝ) := by
      simp [B, r]

lemma one_div_exp_one_rpow_eq_exp_neg {p : ℝ} (_hp : 0 ≤ p) :
    (1 / Real.exp 1 : ℝ) ^ p = Real.exp (-p) := by
  rw [Real.rpow_def_of_pos]
  · congr 1
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (Real.exp_pos 1).ne',
      Real.log_one, Real.log_exp]
    ring
  · positivity

lemma exp_neg_le_two_mul_exp_neg_quarter {p : ℝ} (hp : 0 ≤ p) :
    Real.exp (-p) ≤ 2 * Real.exp (-p / 4) := by
  calc
    Real.exp (-p) ≤ Real.exp (-p / 4) := by
      rw [Real.exp_le_exp]
      nlinarith
    _ ≤ 2 * Real.exp (-p / 4) :=
      le_mul_of_one_le_left (Real.exp_pos _).le
        (by norm_num : (1 : ℝ) ≤ 2)

/-- HDP Proposition 2.7.1, direction `(b) ⇒ (a)` with explicit absolute
constant: moment growth at scale `K` implies the two-sided exponential tail
condition at scale `4 e K`. -/
theorem subExponentialTailCondition_of_subExponentialMomentCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hX : subExponentialMomentCondition X μ K) :
    subExponentialTailCondition X μ (4 * Real.exp 1 * K) := by
  rcases hX with ⟨hKpos, hMom⟩
  refine ⟨by positivity, fun t ht => ?_⟩
  by_cases ht_small : t < Real.exp 1 * K
  · have hprob : μ.real {ω | t ≤ |X ω|} ≤ 1 :=
      measureReal_le_one
    have hu : t / (4 * Real.exp 1 * K) ≤ 1 / 4 := by
      have hden_pos : 0 < 4 * Real.exp 1 * K := by
        positivity
      rw [div_le_iff₀ hden_pos]
      nlinarith [Real.exp_pos 1]
    have hsmall :
        1 ≤ 2 * Real.exp (-(t / (4 * Real.exp 1 * K))) :=
      one_le_two_mul_exp_neg_of_le_one_fourth hu
    have hsmall' :
        1 ≤ 2 * Real.exp (-(t / (4 * Real.exp 1 * K))) := hsmall
    simpa [mul_assoc] using hprob.trans hsmall'
  · have ht_big : Real.exp 1 * K ≤ t := le_of_not_gt ht_small
    have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) ht_big
    let pReal : ℝ := t / (Real.exp 1 * K)
    have hpReal_nonneg : 0 ≤ pReal := by
      dsimp [pReal]
      positivity
    let p : ℝ≥0 := ⟨pReal, hpReal_nonneg⟩
    have hp_coe : (p : ℝ) = pReal := rfl
    have hp_ge_one : 1 ≤ (p : ℝ) := by
      rw [hp_coe]
      dsimp [pReal]
      rw [le_div_iff₀ (by positivity : 0 < Real.exp 1 * K)]
      simpa using ht_big
    have htail :=
      subExponentialMomentCondition_tail_rpow_bound
        (μ := μ) (X := X) (K := K) (t := t) (p := p)
        ⟨hKpos, hMom⟩ hp_ge_one ht_pos
    have hbase :
        K * (p : ℝ) / t = 1 / Real.exp 1 := by
      rw [hp_coe]
      dsimp [pReal]
      field_simp [hKpos.ne', ht_pos.ne', (Real.exp_pos 1).ne']
    have htail_exp :
        μ.real {ω | t ≤ |X ω|} ≤ Real.exp (-(p : ℝ)) := by
      calc
        μ.real {ω | t ≤ |X ω|} ≤ (K * (p : ℝ) / t) ^ (p : ℝ) :=
          htail
        _ = (1 / Real.exp 1 : ℝ) ^ (p : ℝ) := by
          rw [hbase]
        _ = Real.exp (-(p : ℝ)) :=
          one_div_exp_one_rpow_eq_exp_neg
            (show 0 ≤ (p : ℝ) from NNReal.coe_nonneg p)
    calc
      μ.real {ω | t ≤ |X ω|} ≤ Real.exp (-(p : ℝ)) := htail_exp
      _ ≤ 2 * Real.exp (-(p : ℝ) / 4) :=
        exp_neg_le_two_mul_exp_neg_quarter (NNReal.coe_nonneg p)
      _ = 2 * Real.exp (-(t / (4 * Real.exp 1 * K))) := by
        rw [hp_coe]
        dsimp [pReal]
        congr 1
        field_simp [hKpos.ne', (Real.exp_pos 1).ne']

/-- HDP Proposition 2.7.1, direction `(a) ⇒ (d)` with explicit absolute
constant: exponential tails at scale `K` imply the Orlicz point condition at
scale `4K`. -/
theorem subExponentialOrliczCondition_of_subExponentialTailCondition
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subExponentialTailCondition X μ K) :
    subExponentialOrliczCondition X μ (4 * K) := by
  rcases hX with ⟨hKpos, htail⟩
  let Y : Ω → ℝ := fun ω => Real.exp (|X ω| / (4 * K)) - 1
  have hscale_pos : 0 < 4 * K := by
    positivity
  have hY_nonneg : 0 ≤ᵐ[μ] Y := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [Y]
      have hexp_ge_one : 1 ≤ Real.exp (|X ω| / (4 * K)) := by
        rw [← Real.exp_zero, Real.exp_le_exp]
        exact div_nonneg (abs_nonneg _) hscale_pos.le
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
    have h1s_pos : 0 < 1 + s := by
      linarith
    have hlog_nonneg : 0 ≤ Real.log (1 + s) :=
      Real.log_nonneg (by linarith : 1 ≤ 1 + s)
    let t : ℝ := 4 * K * Real.log (1 + s)
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      positivity
    have hsubset : {ω | s < Y ω} ⊆ {ω | t ≤ |X ω|} := by
      intro ω hω
      dsimp [Y] at hω
      have hlt_exp : 1 + s < Real.exp (|X ω| / (4 * K)) := by
        linarith
      have hlog_lt : Real.log (1 + s) < |X ω| / (4 * K) := by
        rwa [Real.log_lt_iff_lt_exp h1s_pos]
      have hmul := mul_lt_mul_of_pos_left hlog_lt hscale_pos
      have ht_lt_abs : t < |X ω| := by
        dsimp [t] at hmul ⊢
        rwa [mul_div_cancel₀ _ hscale_pos.ne'] at hmul
      exact ht_lt_abs.le
    have htail_real :
        μ.real {ω | s < Y ω} ≤ 2 * (1 + s) ^ (-4 : ℝ) := by
      have htail_t := htail t ht_nonneg
      have hmono :
          μ.real {ω | s < Y ω} ≤ μ.real {ω | t ≤ |X ω|} :=
        measureReal_mono hsubset
      have htail_simplified :
          2 * Real.exp (-(t / K)) = 2 * (1 + s) ^ (-4 : ℝ) := by
        congr 1
        dsimp [t]
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
  have hExp_int :
      Integrable (fun ω => Real.exp (|X ω| / (4 * K))) μ := by
    have hsum : Integrable (fun ω => Y ω + 1) μ :=
      hY_int.add (integrable_const (1 : ℝ))
    convert hsum using 1
    funext ω
    dsimp [Y]
    ring_nf
  refine ⟨by positivity, hExp_int, ?_⟩
  calc
    ∫ ω, Real.exp (|X ω| / (4 * K)) ∂μ
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

/-- Composite direction `(a) ⇒ (b)` in HDP Proposition 2.7.1, with explicit
absolute constant. -/
theorem subExponentialMomentCondition_of_subExponentialTailCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hXm : AEStronglyMeasurable X μ)
    (hX : subExponentialTailCondition X μ K) :
    subExponentialMomentCondition X μ (8 * K) := by
  have hOrl :
      subExponentialOrliczCondition X μ (4 * K) :=
    subExponentialOrliczCondition_of_subExponentialTailCondition
      (μ := μ) (X := X) (K := K) hXm.aemeasurable hX
  have hMom :
      subExponentialMomentCondition X μ (2 * (4 * K)) :=
    subExponentialMomentCondition_of_subExponentialOrliczCondition
      (μ := μ) (X := X) (K := 4 * K) hXm hOrl
  have hscale : 2 * (4 * K) = 8 * K := by
    ring
  simpa [hscale] using hMom

/-- Existential form of the `(a) ⇔ (d)` part of HDP Proposition 2.7.1:
two-sided exponential tails are equivalent to the `ψ₁` Orlicz point
condition, up to absolute changes of scale. -/
theorem exists_subExponentialTailCondition_iff_exists_subExponentialOrliczCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) :
    (∃ K, subExponentialTailCondition X μ K) ↔
      ∃ K, subExponentialOrliczCondition X μ K := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨4 * K,
      subExponentialOrliczCondition_of_subExponentialTailCondition
        (μ := μ) (X := X) (K := K) hXm hK⟩
  · rintro ⟨K, hK⟩
    exact ⟨K, subExponentialTailCondition_of_subExponentialOrliczCondition hK⟩

/-- Existential form of the `(b) ⇔ (d)` part of HDP Proposition 2.7.1:
linear moment growth is equivalent to the `ψ₁` Orlicz point condition, up to
absolute changes of scale. -/
theorem exists_subExponentialMomentCondition_iff_exists_subExponentialOrliczCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    (hXm : AEStronglyMeasurable X μ) :
    (∃ K, subExponentialMomentCondition X μ K) ↔
      ∃ K, subExponentialOrliczCondition X μ K := by
  constructor
  · rintro ⟨K, hK⟩
    have hTail :
        subExponentialTailCondition X μ (4 * Real.exp 1 * K) :=
      subExponentialTailCondition_of_subExponentialMomentCondition
        (μ := μ) (X := X) (K := K) hK
    exact ⟨4 * (4 * Real.exp 1 * K),
      subExponentialOrliczCondition_of_subExponentialTailCondition
        (μ := μ) (X := X) (K := 4 * Real.exp 1 * K)
        hXm.aemeasurable hTail⟩
  · rintro ⟨K, hK⟩
    exact ⟨2 * K,
      subExponentialMomentCondition_of_subExponentialOrliczCondition
        (μ := μ) (X := X) (K := K) hXm hK⟩

/-- Existential form of the `(c) ⇔ (d)` part of HDP Proposition 2.7.1:
local MGF control of `|X|` is equivalent to the `ψ₁` Orlicz point condition,
up to absolute changes of scale. -/
theorem exists_subExponentialAbsMGFCondition_iff_exists_subExponentialOrliczCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} :
    (∃ K, subExponentialAbsMGFCondition X μ K) ↔
      ∃ K, subExponentialOrliczCondition X μ K := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K / Real.log 2,
      subExponentialOrliczCondition_of_subExponentialAbsMGFCondition
        (μ := μ) (X := X) (K := K) hK⟩
  · rintro ⟨K, hK⟩
    exact ⟨K,
      subExponentialAbsMGFCondition_of_subExponentialOrliczCondition
        (μ := μ) (X := X) (K := K) hK⟩

/-- HDP Exercise 2.7.2: the first four conditions in Proposition 2.7.1 are
equivalent after allowing absolute changes of the scale parameter. -/
theorem exercise_2_7_2_subExponential_equiv_a_b_c_d
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    (hXm : AEStronglyMeasurable X μ) :
    ((∃ K, subExponentialTailCondition X μ K) ↔
        ∃ K, subExponentialMomentCondition X μ K) ∧
      ((∃ K, subExponentialTailCondition X μ K) ↔
        ∃ K, subExponentialAbsMGFCondition X μ K) ∧
      ((∃ K, subExponentialTailCondition X μ K) ↔
        ∃ K, subExponentialOrliczCondition X μ K) := by
  have hTailOrlicz :=
    exists_subExponentialTailCondition_iff_exists_subExponentialOrliczCondition
      (μ := μ) (X := X) hXm.aemeasurable
  have hMomentOrlicz :=
    exists_subExponentialMomentCondition_iff_exists_subExponentialOrliczCondition
      (μ := μ) (X := X) hXm
  have hAbsMGFOrlicz :=
    exists_subExponentialAbsMGFCondition_iff_exists_subExponentialOrliczCondition
      (μ := μ) (X := X)
  refine ⟨?_, ?_, hTailOrlicz⟩
  · exact hTailOrlicz.trans hMomentOrlicz.symm
  · exact hTailOrlicz.trans hAbsMGFOrlicz.symm

/-- The zero random variable satisfies the local `|X|` MGF condition at every
positive scale. -/
theorem subExponentialAbsMGFCondition_zero
    [IsProbabilityMeasure μ]
    {K : ℝ} (hK : 0 < K) :
    subExponentialAbsMGFCondition (fun _ω : Ω => (0 : ℝ)) μ K := by
  refine ⟨hK, fun θ hθ_nonneg _hθ_le => ?_⟩
  constructor
  · simp
  · have hnonneg : 0 ≤ K * θ := mul_nonneg hK.le hθ_nonneg
    simpa using Real.one_le_exp hnonneg

/-- HDP Exercise 2.7.4: the local MGF estimate for `|X|` in Proposition
2.7.1(c) cannot be extended to all signed parameters with `|θ| ≤ 1 / K`.
Already the zero random variable would force the false inequality
`1 ≤ exp (Kθ)` for negative `θ`. -/
theorem exercise_2_7_4_abs_mgf_signed_extension_counterexample
    [IsProbabilityMeasure μ]
    {K : ℝ} (hK : 0 < K) :
    subExponentialAbsMGFCondition (fun _ω : Ω => (0 : ℝ)) μ K ∧
      ∃ θ, |θ| ≤ 1 / K ∧
        ¬ (∫ _ω : Ω, Real.exp (θ * |(0 : ℝ)|) ∂μ ≤ Real.exp (K * θ)) := by
  refine ⟨subExponentialAbsMGFCondition_zero (μ := μ) (K := K) hK, ?_⟩
  let θ : ℝ := -(1 / (2 * K))
  refine ⟨θ, ?_, ?_⟩
  · have h2Kpos : 0 < 2 * K := by positivity
    have hle : 1 / (2 * K) ≤ 1 / K :=
      (one_div_le_one_div h2Kpos hK).mpr (by nlinarith)
    have hθabs : |θ| = 1 / (2 * K) := by
      dsimp [θ]
      rw [abs_neg, abs_of_pos]
      exact one_div_pos.mpr h2Kpos
    simpa [hθabs] using hle
  · intro hbad
    have hleft :
        (∫ _ω : Ω, Real.exp (θ * |(0 : ℝ)|) ∂μ) = 1 := by
      simp
    have hKθ : K * θ = -(1 / 2 : ℝ) := by
      dsimp [θ]
      field_simp [hK.ne']
    have hright_lt : Real.exp (K * θ) < 1 := by
      rw [hKθ]
      exact Real.exp_lt_one_iff.mpr (by norm_num)
    linarith

end OrliczConsequences

section NormDefiniteness

/-- If a sub-exponential variable has `ψ₁` gauge zero, then every positive
Orlicz scale is admissible. -/
theorem subExponentialOrliczCondition_of_subExponentialNorm_eq_zero
    {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hXse : IsSubExponential X μ)
    (hnorm : subExponentialNorm X μ = 0)
    (hK : 0 < K) :
    subExponentialOrliczCondition X μ K := by
  have hXset :
      ({L : ℝ | subExponentialOrliczCondition X μ L}).Nonempty := by
    simpa [IsSubExponential] using hXse
  obtain ⟨L, hL, hLlt⟩ := Real.lt_sInf_add_pos hXset hK
  have hLltK : L < K := by
    have hsInf_zero :
        sInf {L : ℝ | subExponentialOrliczCondition X μ L} = 0 := by
      simpa [subExponentialNorm] using hnorm
    simpa [hsInf_zero] using hLlt
  exact subExponentialOrliczCondition_mono_scale hXm hL hLltK.le

/-- Positive tails of a zero-`ψ₁` sub-exponential variable have probability
zero. -/
theorem subExponentialNorm_eq_zero_tail_measureReal
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {t : ℝ}
    (hXm : AEMeasurable X μ)
    (hXse : IsSubExponential X μ)
    (hnorm : subExponentialNorm X μ = 0)
    (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} = 0 := by
  let A : Set Ω := {ω | t ≤ |X ω|}
  have hle_bound :
      ∀ n : ℕ, μ.real A ≤ 2 * Real.exp (-((n : ℝ) + 1)) := by
    intro n
    let K : ℝ := t / ((n : ℝ) + 1)
    have hnpos : 0 < (n : ℝ) + 1 := by positivity
    have hKpos : 0 < K := by
      dsimp [K]
      positivity
    have hKcond :
        subExponentialOrliczCondition X μ K :=
      subExponentialOrliczCondition_of_subExponentialNorm_eq_zero
        hXm hXse hnorm hKpos
    have htail :
        μ.real {ω | t ≤ |X ω|}
          ≤ 2 * Real.exp (-(t / K)) :=
      subExponentialOrliczCondition_tail_le (μ := μ) (X := X)
        (K := K) (t := t) hKcond ht.le
    calc
      μ.real A = μ.real {ω | t ≤ |X ω|} := rfl
      _ ≤ 2 * Real.exp (-(t / K)) := htail
      _ = 2 * Real.exp (-((n : ℝ) + 1)) := by
        congr 1
        dsimp [K]
        field_simp [ht.ne', hnpos.ne']
  have hlin :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1))
        Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hneg :
      Filter.Tendsto (fun n : ℕ => -((n : ℝ) + 1))
        Filter.atTop Filter.atBot := by
    simpa using
      (Filter.Tendsto.const_mul_atTop_of_neg
        (by norm_num : (-1 : ℝ) < 0) hlin)
  have hlim :
      Filter.Tendsto
        (fun n : ℕ => 2 * Real.exp (-((n : ℝ) + 1)))
        Filter.atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hneg).const_mul 2
  exact le_antisymm (ge_of_tendsto' hlim hle_bound) measureReal_nonneg

/-- Definiteness of the `ψ₁` gauge: zero norm forces a sub-exponential
random variable to be zero almost surely. -/
theorem ae_eq_zero_of_subExponentialNorm_eq_zero
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hXm : AEMeasurable X μ)
    (hXse : IsSubExponential X μ)
    (hnorm : subExponentialNorm X μ = 0) :
    X =ᵐ[μ] fun _ω => (0 : ℝ) := by
  rw [Filter.EventuallyEq, ae_iff]
  have htail_null :
      ∀ n : ℕ,
        μ {ω | (1 : ℝ) / ((n : ℝ) + 1) ≤ |X ω|} = 0 := by
    intro n
    have htpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    have htail_real :=
      subExponentialNorm_eq_zero_tail_measureReal
        (μ := μ) (X := X) (t := (1 : ℝ) / ((n : ℝ) + 1))
        hXm hXse hnorm htpos
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

/-- Almost-surely zero random variables satisfy every positive `ψ₁` Orlicz
scale. -/
theorem subExponentialOrliczCondition_of_ae_eq_zero
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℝ}
    (hK : 0 < K)
    (hX0 : X =ᵐ[μ] fun _ω => (0 : ℝ)) :
    subExponentialOrliczCondition X μ K := by
  have hExpEq :
      (fun ω => Real.exp (|X ω| / K))
        =ᵐ[μ] fun _ω => (1 : ℝ) := by
    filter_upwards [hX0] with ω hω
    simp [hω]
  have hInt :
      Integrable (fun ω => Real.exp (|X ω| / K)) μ :=
    (integrable_const (1 : ℝ)).congr hExpEq.symm
  refine ⟨hK, hInt, ?_⟩
  calc
    ∫ ω, Real.exp (|X ω| / K) ∂μ
        = ∫ _ω : Ω, (1 : ℝ) ∂μ :=
      integral_congr_ae hExpEq
    _ = 1 := by simp
    _ ≤ 2 := by norm_num

/-- The zero-a.e. direction of `ψ₁` definiteness. -/
theorem subExponentialNorm_eq_zero_of_ae_eq_zero
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX0 : X =ᵐ[μ] fun _ω => (0 : ℝ)) :
    subExponentialNorm X μ = 0 := by
  refine le_antisymm ?_ (subExponentialNorm_nonneg X μ)
  exact le_of_forall_gt_imp_ge_of_dense fun ε hε =>
    subExponentialNorm_le_of_subExponentialOrliczCondition
      (μ := μ) (X := X) (K := ε)
      (subExponentialOrliczCondition_of_ae_eq_zero (μ := μ) hε hX0)

/-- Definiteness of the `ψ₁` gauge, stated on the sub-exponential domain. -/
theorem subExponentialNorm_eq_zero_iff_ae_eq_zero
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hXm : AEMeasurable X μ)
    (hXse : IsSubExponential X μ) :
    subExponentialNorm X μ = 0 ↔ X =ᵐ[μ] fun _ω => (0 : ℝ) :=
  ⟨ae_eq_zero_of_subExponentialNorm_eq_zero hXm hXse,
    subExponentialNorm_eq_zero_of_ae_eq_zero⟩

/-- Norm-to-scale bridge for `ψ₁` that also handles the zero-norm case.
If `‖X‖ψ₁ ≤ K` with `K > 0`, then `2K` is an admissible Orlicz scale. -/
theorem subExponentialOrliczCondition_two_mul_of_norm_le
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hXse : IsSubExponential X μ)
    (hKpos : 0 < K)
    (hNormK : subExponentialNorm X μ ≤ K) :
    subExponentialOrliczCondition X μ (2 * K) := by
  by_cases hzero : subExponentialNorm X μ = 0
  · exact
      subExponentialOrliczCondition_of_ae_eq_zero
        (μ := μ) (X := X) (K := 2 * K) (by positivity)
        (ae_eq_zero_of_subExponentialNorm_eq_zero hXm hXse hzero)
  · have hpos : 0 < subExponentialNorm X μ := by
      exact lt_of_le_of_ne (subExponentialNorm_nonneg X μ) (Ne.symm hzero)
    have htwo_norm :
        subExponentialOrliczCondition X μ
          (2 * subExponentialNorm X μ) :=
      subExponentialOrliczCondition_two_mul_norm hXm hXse hpos
    have hle : 2 * subExponentialNorm X μ ≤ 2 * K :=
      mul_le_mul_of_nonneg_left hNormK (by norm_num)
    exact subExponentialOrliczCondition_mono_scale hXm htwo_norm hle

end NormDefiniteness

section GeneralAlpha

/-- HDP Exercise 2.7.3: general `exp (-t^α)` tail condition.  The cases
`α = 2` and `α = 1` recover the sub-gaussian and sub-exponential tail
predicates, respectively. -/
def subWeibullTailCondition (α : ℝ) (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < α ∧ 0 < K ∧
    ∀ t, 0 ≤ t →
      μ.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-((t / K) ^ α))

/-- HDP Exercise 2.7.3: general Orlicz condition corresponding to
`exp (-t^α)` tails. -/
def subWeibullOrliczCondition (α : ℝ) (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < α ∧ 0 < K ∧
    Integrable (fun ω => Real.exp ((|X ω| / K) ^ α)) μ ∧
      ∫ ω, Real.exp ((|X ω| / K) ^ α) ∂μ ≤ 2

/-- HDP Exercise 2.7.3: moment-growth condition for the general
`exp (-t^α)` hierarchy. -/
def subWeibullMomentCondition (α : ℝ) (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < α ∧ 0 < K ∧
    ∀ p : ℝ≥0, 1 ≤ (p : ℝ) →
      MemLp X (p : ℝ≥0∞) μ ∧
        eLpNorm X (p : ℝ≥0∞) μ ≤ ENNReal.ofReal (K * (p : ℝ) ^ (1 / α))

/-- Exercise 2.7.3, Orlicz-to-tail direction for every `α > 0`, by
Markov's inequality. -/
theorem subWeibullOrliczCondition_tail_le
    [IsProbabilityMeasure μ] {α : ℝ} {X : Ω → ℝ} {K t : ℝ}
    (hX : subWeibullOrliczCondition α X μ K) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|}
      ≤ 2 * Real.exp (-((t / K) ^ α)) := by
  rcases hX with ⟨hαpos, hKpos, hInt, hBound⟩
  let Y : Ω → ℝ := fun ω => Real.exp ((|X ω| / K) ^ α)
  have hY_nonneg : 0 ≤ᵐ[μ] Y :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have hthreshold_pos : 0 < Real.exp ((t / K) ^ α) :=
    Real.exp_pos _
  have htbase_nonneg : 0 ≤ t / K :=
    div_nonneg ht hKpos.le
  have hsubset :
      {ω | t ≤ |X ω|} ⊆ {ω | Real.exp ((t / K) ^ α) ≤ Y ω} := by
    intro ω hω
    change Real.exp ((t / K) ^ α) ≤ Y ω
    rw [Real.exp_le_exp]
    have hbase :
        t / K ≤ |X ω| / K :=
      div_le_div_of_nonneg_right hω hKpos.le
    exact Real.rpow_le_rpow htbase_nonneg hbase hαpos.le
  have hmarkov :=
    markov_inequality
      (μ := μ) (X := Y) hY_nonneg hInt
      (t := Real.exp ((t / K) ^ α)) hthreshold_pos
  calc
    μ.real {ω | t ≤ |X ω|}
        ≤ μ.real {ω | Real.exp ((t / K) ^ α) ≤ Y ω} :=
      MeasureTheory.measureReal_mono hsubset
    _ ≤ (∫ ω, Y ω ∂μ) / Real.exp ((t / K) ^ α) := hmarkov
    _ ≤ 2 / Real.exp ((t / K) ^ α) :=
      div_le_div_of_nonneg_right hBound hthreshold_pos.le
    _ = 2 * Real.exp (-((t / K) ^ α)) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]

/-- Predicate form of the Orlicz-to-tail implication in Exercise 2.7.3. -/
theorem subWeibullTailCondition_of_subWeibullOrliczCondition
    [IsProbabilityMeasure μ] {α : ℝ} {X : Ω → ℝ} {K : ℝ}
    (hX : subWeibullOrliczCondition α X μ K) :
    subWeibullTailCondition α X μ K :=
  ⟨hX.1, hX.2.1, fun t ht =>
    subWeibullOrliczCondition_tail_le (μ := μ) (X := X) (K := K) (t := t) hX ht⟩

/-- Exercise 2.7.3, Orlicz-to-moment direction for every `α > 0`.
An admissible scale `K` for `E exp((|X|/K)^α) ≤ 2` gives
`‖X‖_{L^p} ≤ C(α) K p^(1/α)` for all `p ≥ 1`, with the explicit
constant `C(α) = 2 α^(-1/α)`. -/
theorem subWeibullMomentCondition_of_subWeibullOrliczCondition
    [IsProbabilityMeasure μ]
    {α : ℝ} {X : Ω → ℝ} {K : ℝ}
    (hXm : AEStronglyMeasurable X μ)
    (hX : subWeibullOrliczCondition α X μ K) :
    subWeibullMomentCondition α X μ
      (2 * K * (1 / α) ^ (1 / α)) := by
  rcases hX with ⟨hαpos, hKpos, hExpInt, hExp_le⟩
  have hαnonneg : 0 ≤ α := hαpos.le
  have hinvα_pos : 0 < 1 / α := by positivity
  have hscale_pos : 0 < 2 * K * (1 / α) ^ (1 / α) := by
    positivity
  refine ⟨hαpos, hscale_pos, fun p hp => ?_⟩
  let r : ℝ := p
  have hr_ge_one : 1 ≤ r := by
    simpa [r] using hp
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr_ge_one
  let q : ℝ := r / α
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hq_nonneg : 0 ≤ q := hq_pos.le
  let C : ℝ := K * q ^ (1 / α)
  have hqpow_pos : 0 < q ^ (1 / α) :=
    Real.rpow_pos_of_pos hq_pos (1 / α)
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCnonneg : 0 ≤ C := hCpos.le
  have hCpow_nonneg : 0 ≤ C ^ r :=
    Real.rpow_nonneg hCnonneg r
  have hdom_int :
      Integrable (fun ω => C ^ r * Real.exp ((|X ω| / K) ^ α)) μ :=
    hExpInt.const_mul (C ^ r)
  have hpoint :
      ∀ ω, ‖X ω‖ ^ r ≤ C ^ r * Real.exp ((|X ω| / K) ^ α) := by
    intro ω
    let u : ℝ := |X ω| / K
    have hu_nonneg : 0 ≤ u :=
      div_nonneg (abs_nonneg _) hKpos.le
    let y : ℝ := u ^ α / q
    have huα_nonneg : 0 ≤ u ^ α :=
      Real.rpow_nonneg hu_nonneg α
    have hy_nonneg : 0 ≤ y :=
      div_nonneg huα_nonneg hq_nonneg
    have hy_le := rpow_div_le_exp (y := y) (r := q) hy_nonneg hq_pos
    have hq_mul_y : q * y = u ^ α := by
      dsimp [y]
      field_simp [hq_pos.ne']
    have hu_r_eq : u ^ r = q ^ q * y ^ q := by
      calc
        u ^ r = (u ^ α) ^ q := by
          rw [← Real.rpow_mul hu_nonneg]
          have hmul : α * q = r := by
            dsimp [q]
            field_simp [hαpos.ne']
          rw [hmul]
        _ = (q * y) ^ q := by
          rw [hq_mul_y]
        _ = q ^ q * y ^ q := by
          rw [Real.mul_rpow hq_nonneg hy_nonneg]
    have hCpow_eq : C ^ r = K ^ r * q ^ q := by
      dsimp [C]
      rw [Real.mul_rpow hKpos.le (Real.rpow_nonneg hq_nonneg (1 / α))]
      congr 1
      rw [← Real.rpow_mul hq_nonneg]
      have hmul : (1 / α) * r = q := by
        dsimp [q]
        ring_nf
      rw [hmul]
    have hscaled : |X ω| ^ r ≤ C ^ r * Real.exp (u ^ α) := by
      calc
        |X ω| ^ r = (K * u) ^ r := by
          congr 1
          dsimp [u]
          field_simp [hKpos.ne']
        _ = K ^ r * u ^ r := by
          rw [Real.mul_rpow hKpos.le hu_nonneg]
        _ = K ^ r * (q ^ q * y ^ q) := by
          rw [hu_r_eq]
        _ = (K ^ r * q ^ q) * y ^ q := by ring
        _ ≤ (K ^ r * q ^ q) * Real.exp (q * y) := by
          have hcoef_nonneg : 0 ≤ K ^ r * q ^ q := by
            exact mul_nonneg (Real.rpow_nonneg hKpos.le r)
              (Real.rpow_nonneg hq_nonneg q)
          exact mul_le_mul_of_nonneg_left hy_le hcoef_nonneg
        _ = C ^ r * Real.exp (u ^ α) := by
          rw [hq_mul_y, hCpow_eq]
    calc
      ‖X ω‖ ^ r = |X ω| ^ r := by
        rw [Real.norm_eq_abs]
      _ ≤ C ^ r * Real.exp (u ^ α) := hscaled
      _ = C ^ r * Real.exp ((|X ω| / K) ^ α) := rfl
  have hpow_int :
      Integrable (fun ω => ‖X ω‖ ^ r) μ := by
    refine hdom_int.mono ?_ ?_
    · exact (hXm.norm.aemeasurable.pow_const r).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        have htarget_nonneg : 0 ≤ ‖X ω‖ ^ r :=
          Real.rpow_nonneg (norm_nonneg _) r
        have hdom_nonneg :
            0 ≤ C ^ r * Real.exp ((|X ω| / K) ^ α) :=
          mul_nonneg hCpow_nonneg (Real.exp_pos _).le
        calc
          ‖‖X ω‖ ^ r‖ = ‖X ω‖ ^ r := by
            rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
          _ ≤ C ^ r * Real.exp ((|X ω| / K) ^ α) := hpoint ω
          _ = ‖C ^ r * Real.exp ((|X ω| / K) ^ α)‖ := by
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
          ≤ ∫ ω, C ^ r * Real.exp ((|X ω| / K) ^ α) ∂μ :=
        integral_mono hpow_int hdom_int hpoint
      _ = C ^ r * ∫ ω, Real.exp ((|X ω| / K) ^ α) ∂μ := by
        rw [integral_const_mul]
      _ ≤ C ^ r * 2 :=
        mul_le_mul_of_nonneg_left hExp_le hCpow_nonneg
  have htwo_le_two_rpow : (2 : ℝ) ≤ 2 ^ r := by
    simpa [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hr_ge_one
  have hintegral_bound_C :
      ∫ ω, ‖X ω‖ ^ r ∂μ ≤ (2 * C) ^ r := by
    have hCpow_mul_two_le : C ^ r * 2 ≤ (2 * C) ^ r := by
      calc
        C ^ r * 2 ≤ C ^ r * 2 ^ r :=
          mul_le_mul_of_nonneg_left htwo_le_two_rpow
            (Real.rpow_nonneg hCnonneg r)
        _ = (C * 2) ^ r := by
          rw [Real.mul_rpow hCnonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ = (2 * C) ^ r := by ring_nf
    exact hintegral_bound.trans hCpow_mul_two_le
  have hlp_real :
      MeasureTheory.lpNorm X (p : ℝ≥0∞) μ ≤ 2 * C := by
    rw [lpNorm_nnreal_eq_integral_norm_rpow
      (μ := μ) (f := X) (p := p)
      hp_ne_zero hXm]
    have hintegral_nonneg : 0 ≤ ∫ ω, ‖X ω‖ ^ r ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) r
    calc
      (∫ ω, ‖X ω‖ ^ r ∂μ) ^ ((p : ℝ≥0)⁻¹ : ℝ)
          ≤ ((2 * C) ^ r) ^ ((p : ℝ≥0)⁻¹ : ℝ) := by
        exact Real.rpow_le_rpow hintegral_nonneg hintegral_bound_C
          (by positivity)
      _ = 2 * C := by
        have hbase_pos : 0 < 2 * C := by
          positivity
        rw [← Real.rpow_mul hbase_pos.le]
        have hinv_eq : (((p : ℝ≥0)⁻¹ : ℝ)) = r⁻¹ := by
          simp [r]
        rw [hinv_eq]
        have hmul : r * r⁻¹ = 1 := by
          field_simp [hr_pos.ne']
        rw [hmul, Real.rpow_one]
  have hscale_eq :
      2 * C =
        (2 * K * (1 / α) ^ (1 / α)) * r ^ (1 / α) := by
    dsimp [C, q]
    have hr_nonneg : 0 ≤ r := hr_pos.le
    have hinv_nonneg : 0 ≤ 1 / α := hinvα_pos.le
    have hdiv :
        (r / α) ^ (1 / α) =
          r ^ (1 / α) * (1 / α) ^ (1 / α) := by
      have hmul :
          (r * (1 / α)) ^ (1 / α) =
            r ^ (1 / α) * (1 / α) ^ (1 / α) := by
        rw [Real.mul_rpow hr_nonneg hinv_nonneg]
      simpa [div_eq_mul_inv, one_div] using hmul
    rw [hdiv]
    ring
  refine ⟨hmem, ?_⟩
  rw [← ofReal_lpNorm hmem]
  exact ENNReal.ofReal_le_ofReal (by
    calc
      MeasureTheory.lpNorm X (p : ℝ≥0∞) μ ≤ 2 * C := hlp_real
      _ = (2 * K * (1 / α) ^ (1 / α)) * (p : ℝ) ^ (1 / α) := by
        simpa [r] using hscale_eq)

/-- A Markov-`L^p` tail bound extracted from Exercise 2.7.3 moment growth. -/
theorem subWeibullMomentCondition_tail_rpow_bound
    [IsProbabilityMeasure μ]
    {α : ℝ} {X : Ω → ℝ} {K t : ℝ} {p : ℝ≥0}
    (hX : subWeibullMomentCondition α X μ K)
    (hp : 1 ≤ (p : ℝ)) (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|}
      ≤ (K * (p : ℝ) ^ (1 / α) / t) ^ (p : ℝ) := by
  rcases hX with ⟨hαpos, hKpos, hMom⟩
  let r : ℝ := p
  have hr_ge_one : 1 ≤ r := by
    simpa [r] using hp
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr_ge_one
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    have : r = 0 := by
      simp [r, hp0]
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
  let B : ℝ := K * r ^ (1 / α)
  have hrpow_pos : 0 < r ^ (1 / α) :=
    Real.rpow_pos_of_pos hr_pos (1 / α)
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hB_nonneg : 0 ≤ B := hB_pos.le
  have hlp_real :
      MeasureTheory.lpNorm X (p : ℝ≥0∞) μ ≤ B := by
    have hscale_nonneg : 0 ≤ K * (p : ℝ) ^ (1 / α) := by
      simpa [B, r] using hB_nonneg
    have hscale_nonneg_inv : 0 ≤ K * (p : ℝ) ^ α⁻¹ := by
      simpa [one_div] using hscale_nonneg
    have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    have hto_real :
        (eLpNorm X (p : ℝ≥0∞) μ).toReal
          ≤ K * (p : ℝ) ^ α⁻¹ := by
      simpa [ENNReal.toReal_ofReal hscale_nonneg_inv] using hto
    have hto_lp :
        MeasureTheory.lpNorm X (p : ℝ≥0∞) μ
          ≤ K * (p : ℝ) ^ (1 / α) := by
      simpa [one_div, MeasureTheory.toReal_eLpNorm hmem.aestronglyMeasurable]
        using hto_real
    simpa [B, r] using hto_lp
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
    have hleft : (I ^ r⁻¹) ^ r = I :=
      Real.rpow_inv_rpow hI_nonneg hr_pos.ne'
    simpa [hleft] using hpow
  calc
    μ.real {ω | t ≤ |X ω|} ≤ I / t ^ r := htail
    _ ≤ B ^ r / t ^ r :=
      div_le_div_of_nonneg_right hI_bound ht_rpow_pos.le
    _ = (B / t) ^ r := by
      rw [Real.div_rpow hB_nonneg ht.le]
    _ = (K * (p : ℝ) ^ (1 / α) / t) ^ (p : ℝ) := by
      simp [B, r]

/-- For positive exponents, raising a nonnegative number to `α` and then
to `1 / α` returns the original number. -/
lemma rpow_rpow_one_div_eq_self {α u : ℝ}
    (hα : 0 < α) (hu : 0 ≤ u) :
    (u ^ α) ^ (1 / α) = u := by
  rw [← Real.rpow_mul hu]
  have hmul : α * (1 / α) = 1 := by
    field_simp [hα.ne']
  rw [hmul, Real.rpow_one]

/-- The scale `4^(1/α) e K` turns the general Weibull exponent into a
quarter of the optimizing moment parameter. -/
lemma subWeibull_scaled_exponent_eq_quarter
    {α K t : ℝ} (hα : 0 < α) (hK : 0 < K) (ht : 0 ≤ t) :
    (t / ((4 : ℝ) ^ (1 / α) * Real.exp 1 * K)) ^ α
      = (t / (Real.exp 1 * K)) ^ α / 4 := by
  let c : ℝ := (4 : ℝ) ^ (1 / α)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (1 / α)
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hu_nonneg : 0 ≤ t / (Real.exp 1 * K) := by
    positivity
  have hc_pow : c ^ α = 4 := by
    dsimp [c]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hmul : (1 / α) * α = 1 := by
      field_simp [hα.ne']
    rw [hmul, Real.rpow_one]
  calc
    (t / ((4 : ℝ) ^ (1 / α) * Real.exp 1 * K)) ^ α
        = ((t / (Real.exp 1 * K)) / c) ^ α := by
      congr 1
      dsimp [c]
      field_simp [hc_pos.ne', (Real.exp_pos 1).ne', hK.ne']
    _ = (t / (Real.exp 1 * K)) ^ α / c ^ α := by
      rw [Real.div_rpow hu_nonneg hc_nonneg]
    _ = (t / (Real.exp 1 * K)) ^ α / 4 := by
      rw [hc_pow]

/-- Exercise 2.7.3, moment-to-tail direction for every `α > 0`.  If
`‖X‖_{L^p} ≤ K p^(1/α)` for all `p ≥ 1`, then `X` has
`exp(-t^α)` tails at the explicit scale `4^(1/α) e K`. -/
theorem subWeibullTailCondition_of_subWeibullMomentCondition
    [IsProbabilityMeasure μ]
    {α : ℝ} {X : Ω → ℝ} {K : ℝ}
    (hX : subWeibullMomentCondition α X μ K) :
    subWeibullTailCondition α X μ
      ((4 : ℝ) ^ (1 / α) * Real.exp 1 * K) := by
  rcases hX with ⟨hαpos, hKpos, hMom⟩
  let scale : ℝ := (4 : ℝ) ^ (1 / α) * Real.exp 1 * K
  have hfour_rpow_pos : 0 < (4 : ℝ) ^ (1 / α) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (1 / α)
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  refine ⟨hαpos, hscale_pos, fun t ht => ?_⟩
  have hq_eq :
      (t / scale) ^ α =
        (t / (Real.exp 1 * K)) ^ α / 4 := by
    simpa [scale, mul_assoc] using
      subWeibull_scaled_exponent_eq_quarter
        (α := α) (K := K) (t := t) hαpos hKpos ht
  by_cases ht_small : t < Real.exp 1 * K
  · have hprob : μ.real {ω | t ≤ |X ω|} ≤ 1 :=
      measureReal_le_one
    have hu_nonneg : 0 ≤ t / (Real.exp 1 * K) := by
      positivity
    have hu_le_one : t / (Real.exp 1 * K) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < Real.exp 1 * K)]
      exact le_of_lt ht_small
    have hpow_le_one :
        (t / (Real.exp 1 * K)) ^ α ≤ 1 :=
      Real.rpow_le_one hu_nonneg hu_le_one hαpos.le
    have hq_le : (t / scale) ^ α ≤ 1 / 4 := by
      rw [hq_eq]
      nlinarith
    have hsmall :
        1 ≤ 2 * Real.exp (-((t / scale) ^ α)) :=
      one_le_two_mul_exp_neg_of_le_one_fourth hq_le
    exact hprob.trans hsmall
  · have ht_big : Real.exp 1 * K ≤ t := le_of_not_gt ht_small
    have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) ht_big
    let pReal : ℝ := (t / (Real.exp 1 * K)) ^ α
    have hu_nonneg : 0 ≤ t / (Real.exp 1 * K) := by
      positivity
    have hpReal_nonneg : 0 ≤ pReal := by
      dsimp [pReal]
      exact Real.rpow_nonneg hu_nonneg α
    let p : ℝ≥0 := ⟨pReal, hpReal_nonneg⟩
    have hp_coe : (p : ℝ) = pReal := rfl
    have hp_ge_one : 1 ≤ (p : ℝ) := by
      rw [hp_coe]
      dsimp [pReal]
      have hu_ge_one : 1 ≤ t / (Real.exp 1 * K) := by
        rw [le_div_iff₀ (by positivity : 0 < Real.exp 1 * K)]
        simpa using ht_big
      have hpow :=
        Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
          hu_ge_one hαpos.le
      simpa using hpow
    have htail :=
      subWeibullMomentCondition_tail_rpow_bound
        (μ := μ) (X := X) (α := α) (K := K) (t := t) (p := p)
        ⟨hαpos, hKpos, hMom⟩ hp_ge_one ht_pos
    have hroot :
        ((t / (Real.exp 1 * K)) ^ α) ^ (1 / α)
          = t / (Real.exp 1 * K) :=
      rpow_rpow_one_div_eq_self hαpos hu_nonneg
    have hbase :
        K * (p : ℝ) ^ (1 / α) / t = 1 / Real.exp 1 := by
      rw [hp_coe]
      dsimp [pReal]
      rw [hroot]
      field_simp [hKpos.ne', ht_pos.ne', (Real.exp_pos 1).ne']
    have htail_exp :
        μ.real {ω | t ≤ |X ω|} ≤ Real.exp (-(p : ℝ)) := by
      calc
        μ.real {ω | t ≤ |X ω|}
            ≤ (K * (p : ℝ) ^ (1 / α) / t) ^ (p : ℝ) :=
          htail
        _ = (1 / Real.exp 1 : ℝ) ^ (p : ℝ) := by
          rw [hbase]
        _ = Real.exp (-(p : ℝ)) :=
          one_div_exp_one_rpow_eq_exp_neg
            (show 0 ≤ (p : ℝ) from NNReal.coe_nonneg p)
    calc
      μ.real {ω | t ≤ |X ω|} ≤ Real.exp (-(p : ℝ)) := htail_exp
      _ ≤ 2 * Real.exp (-(p : ℝ) / 4) :=
        exp_neg_le_two_mul_exp_neg_quarter (NNReal.coe_nonneg p)
      _ = 2 * Real.exp (-((t / scale) ^ α)) := by
        rw [hq_eq, hp_coe]
        dsimp [pReal]
        congr 2
        ring

/-- Exercise 2.7.3, tail-to-Orlicz direction for every `α > 0`.  Tails at
scale `K` imply the Orlicz point condition at scale `4^(1/α) K`. -/
theorem subWeibullOrliczCondition_of_subWeibullTailCondition
    [IsProbabilityMeasure μ]
    {α : ℝ} {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subWeibullTailCondition α X μ K) :
    subWeibullOrliczCondition α X μ
      ((4 : ℝ) ^ (1 / α) * K) := by
  rcases hX with ⟨hαpos, hKpos, htail⟩
  let c : ℝ := (4 : ℝ) ^ (1 / α)
  let scale : ℝ := c * K
  have hinvα_pos : 0 < 1 / α := by positivity
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (1 / α)
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  have hscale_nonneg : 0 ≤ scale := hscale_pos.le
  have hc_pow : c ^ α = 4 := by
    dsimp [c]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hmul : (1 / α) * α = 1 := by
      field_simp [hαpos.ne']
    rw [hmul, Real.rpow_one]
  let Y : Ω → ℝ := fun ω => Real.exp ((|X ω| / scale) ^ α) - 1
  have hY_nonneg : 0 ≤ᵐ[μ] Y := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [Y]
      have hpow_nonneg : 0 ≤ (|X ω| / scale) ^ α :=
        Real.rpow_nonneg (div_nonneg (abs_nonneg _) hscale_nonneg) α
      have hexp_ge_one : 1 ≤ Real.exp ((|X ω| / scale) ^ α) := by
        rw [← Real.exp_zero, Real.exp_le_exp]
        exact hpow_nonneg
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
    have h1s_pos : 0 < 1 + s := by
      linarith
    have hlog_nonneg : 0 ≤ Real.log (1 + s) :=
      Real.log_nonneg (by linarith : 1 ≤ 1 + s)
    let logRoot : ℝ := Real.log (1 + s) ^ (1 / α)
    let t0 : ℝ := scale * logRoot
    have hlogRoot_nonneg : 0 ≤ logRoot := by
      dsimp [logRoot]
      exact Real.rpow_nonneg hlog_nonneg (1 / α)
    have ht0_nonneg : 0 ≤ t0 := by
      dsimp [t0]
      positivity
    have hlogRoot_pow : logRoot ^ α = Real.log (1 + s) := by
      dsimp [logRoot]
      rw [← Real.rpow_mul hlog_nonneg]
      have hmul : (1 / α) * α = 1 := by
        field_simp [hαpos.ne']
      rw [hmul, Real.rpow_one]
    have hsubset : {ω | s < Y ω} ⊆ {ω | t0 ≤ |X ω|} := by
      intro ω hω
      dsimp [Y] at hω
      have hlt_exp :
          1 + s < Real.exp ((|X ω| / scale) ^ α) := by
        linarith
      have hlog_lt :
          Real.log (1 + s) < (|X ω| / scale) ^ α := by
        rwa [Real.log_lt_iff_lt_exp h1s_pos]
      have hbase_nonneg : 0 ≤ |X ω| / scale :=
        div_nonneg (abs_nonneg _) hscale_nonneg
      have hroot_lt :
          logRoot < |X ω| / scale := by
        have hpow_lt :=
          Real.rpow_lt_rpow hlog_nonneg hlog_lt hinvα_pos
        rw [rpow_rpow_one_div_eq_self hαpos hbase_nonneg] at hpow_lt
        exact hpow_lt
      have hmul := mul_lt_mul_of_pos_left hroot_lt hscale_pos
      have ht_lt_abs : t0 < |X ω| := by
        dsimp [t0] at hmul ⊢
        rwa [mul_div_cancel₀ _ hscale_pos.ne'] at hmul
      exact ht_lt_abs.le
    have hpow_t0 :
        (t0 / K) ^ α = 4 * Real.log (1 + s) := by
      calc
        (t0 / K) ^ α = (c * logRoot) ^ α := by
          congr 1
          dsimp [t0, scale]
          field_simp [hKpos.ne']
        _ = c ^ α * logRoot ^ α := by
          rw [Real.mul_rpow hc_nonneg hlogRoot_nonneg]
        _ = 4 * Real.log (1 + s) := by
          rw [hc_pow, hlogRoot_pow]
    have htail_real :
        μ.real {ω | s < Y ω} ≤ 2 * (1 + s) ^ (-4 : ℝ) := by
      have htail_t := htail t0 ht0_nonneg
      have hmono :
          μ.real {ω | s < Y ω} ≤ μ.real {ω | t0 ≤ |X ω|} :=
        measureReal_mono hsubset
      have htail_simplified :
          2 * Real.exp (-((t0 / K) ^ α))
            = 2 * (1 + s) ^ (-4 : ℝ) := by
        congr 1
        rw [hpow_t0]
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
  have hExp_int :
      Integrable (fun ω => Real.exp ((|X ω| / scale) ^ α)) μ := by
    have hsum : Integrable (fun ω => Y ω + 1) μ :=
      hY_int.add (integrable_const (1 : ℝ))
    convert hsum using 1
    funext ω
    dsimp [Y]
    ring_nf
  refine ⟨hαpos, hscale_pos, hExp_int, ?_⟩
  calc
    ∫ ω, Real.exp ((|X ω| / scale) ^ α) ∂μ
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

/-- Exercise 2.7.3, `α = 1`: the general Orlicz condition is exactly the
sub-exponential `ψ₁` condition. -/
theorem subWeibullOrliczCondition_one_iff_subExponentialOrliczCondition
    {X : Ω → ℝ} {K : ℝ} :
    subWeibullOrliczCondition 1 X μ K ↔
      subExponentialOrliczCondition X μ K := by
  constructor
  · intro hX
    rcases hX with ⟨_hα, hKpos, hInt, hBound⟩
    refine ⟨hKpos, ?_, ?_⟩
    · simpa [Real.rpow_one] using hInt
    · simpa [Real.rpow_one] using hBound
  · intro hX
    rcases hX with ⟨hKpos, hInt, hBound⟩
    refine ⟨by norm_num, hKpos, ?_, ?_⟩
    · simpa [Real.rpow_one] using hInt
    · simpa [Real.rpow_one] using hBound

/-- Exercise 2.7.3, tail form at `α = 1`: the general tail predicate is
exactly the sub-exponential tail predicate. -/
theorem subWeibullTailCondition_one_iff_subExponentialTailCondition
    {X : Ω → ℝ} {K : ℝ} :
    subWeibullTailCondition 1 X μ K ↔
      subExponentialTailCondition X μ K := by
  constructor
  · intro hX
    rcases hX with ⟨_hα, hKpos, htail⟩
    refine ⟨hKpos, fun t ht => ?_⟩
    simpa [Real.rpow_one] using htail t ht
  · intro hX
    rcases hX with ⟨hKpos, htail⟩
    refine ⟨by norm_num, hKpos, fun t ht => ?_⟩
    simpa [Real.rpow_one] using htail t ht

/-- Exercise 2.7.3, `α = 2`: the general Orlicz condition is exactly the
sub-gaussian `ψ₂` Orlicz condition. -/
theorem subWeibullOrliczCondition_two_iff_subGaussianOrliczCondition
    {X : Ω → ℝ} {K : ℝ} :
    subWeibullOrliczCondition 2 X μ K ↔
      subGaussianOrliczCondition X μ K := by
  constructor
  · intro hX
    rcases hX with ⟨_hα, hKpos, hInt, hBound⟩
    have hfun :
        (fun ω => Real.exp ((|X ω| / K) ^ (2 : ℝ)))
          = fun ω => Real.exp (X ω ^ 2 / K ^ 2) := by
      funext ω
      congr 1
      rw [Real.rpow_two, div_pow, sq_abs]
    rw [hfun] at hInt hBound
    refine ⟨hKpos, ?_, ?_⟩
    · exact hInt
    · exact hBound
  · intro hX
    rcases hX with ⟨hKpos, hInt, hBound⟩
    have hfun :
        (fun ω => Real.exp ((|X ω| / K) ^ (2 : ℝ)))
          = fun ω => Real.exp (X ω ^ 2 / K ^ 2) := by
      funext ω
      congr 1
      rw [Real.rpow_two, div_pow, sq_abs]
    refine ⟨by norm_num, hKpos, ?_, ?_⟩
    · rw [hfun]
      exact hInt
    · rw [hfun]
      exact hBound

/-- Exercise 2.7.3, tail form at `α = 2`: the general tail predicate is
exactly the sub-gaussian tail predicate. -/
theorem subWeibullTailCondition_two_iff_subGaussianTailCondition
    {X : Ω → ℝ} {K : ℝ} :
    subWeibullTailCondition 2 X μ K ↔
      subGaussianTailCondition X μ K := by
  constructor
  · intro hX
    rcases hX with ⟨_hα, hKpos, htail⟩
    refine ⟨hKpos, fun t ht => ?_⟩
    have hpow : (t / K) ^ (2 : ℝ) = t ^ 2 / K ^ 2 := by
      rw [Real.rpow_two, div_pow]
    have harg : -(t ^ 2 / K ^ 2) = -(t ^ 2) / K ^ 2 := by
      ring
    simpa [hpow, harg] using htail t ht
  · intro hX
    rcases hX with ⟨hKpos, htail⟩
    refine ⟨by norm_num, hKpos, fun t ht => ?_⟩
    have hpow : (t / K) ^ (2 : ℝ) = t ^ 2 / K ^ 2 := by
      rw [Real.rpow_two, div_pow]
    have harg : -(t ^ 2 / K ^ 2) = -(t ^ 2) / K ^ 2 := by
      ring
    simpa [hpow, harg] using htail t ht

end GeneralAlpha

section Centering

/-- A `ψ₁` Orlicz scale implies ordinary integrability. -/
theorem integrable_of_subExponentialOrliczCondition
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subExponentialOrliczCondition X μ K) :
    Integrable X μ := by
  rcases hX with ⟨hKpos, hInt, _hBound⟩
  have hpoint : ∀ ω, ‖X ω‖ ≤ K * Real.exp (|X ω| / K) := by
    intro ω
    rw [Real.norm_eq_abs]
    have hxnonneg : 0 ≤ |X ω| / K :=
      div_nonneg (abs_nonneg _) hKpos.le
    have hxle := real_nonneg_le_exp_self hxnonneg
    calc
      |X ω| = K * (|X ω| / K) := by
        field_simp [hKpos.ne']
      _ ≤ K * Real.exp (|X ω| / K) :=
        mul_le_mul_of_nonneg_left hxle hKpos.le
  have hdom_int :
      Integrable (fun ω => K * Real.exp (|X ω| / K)) μ :=
    hInt.const_mul K
  refine hdom_int.mono hXm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    have hdom_nonneg : 0 ≤ K * Real.exp (|X ω| / K) :=
      mul_nonneg hKpos.le (Real.exp_pos _).le
    simpa [Real.norm_eq_abs, abs_of_nonneg hdom_nonneg, abs_of_pos hKpos] using hpoint ω

/-- HDP Proposition 2.7.1, centered direction `(d) ⇒ (e)`: a centered
sub-exponential variable has local signed MGF control.  The explicit scale
`8K` is an absolute-constant version of the book statement. -/
theorem subExponentialMGFCondition_of_orliczCondition_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subExponentialOrliczCondition X μ K)
    (hmean : ∫ ω, X ω ∂μ = 0) :
    subExponentialMGFCondition X μ (8 * K) := by
  rcases hX with ⟨hKpos, hExpInt, hExpBound⟩
  have hX_orlicz : subExponentialOrliczCondition X μ K :=
    ⟨hKpos, hExpInt, hExpBound⟩
  have hXint : Integrable X μ :=
    integrable_of_subExponentialOrliczCondition hXm hX_orlicz
  refine ⟨by positivity, fun θ hθ => ?_⟩
  have hθ_small : |θ| ≤ 1 / (8 * K) := by
    simpa [mul_assoc] using hθ
  have hθ_le_one_div_K : |θ| ≤ 1 / K := by
    have h8Kpos : 0 < 8 * K := by positivity
    have hle : 1 / (8 * K) ≤ 1 / K :=
      (one_div_le_one_div h8Kpos hKpos).mpr (by nlinarith)
    exact hθ_small.trans hle
  have htarget_aesm :
      AEStronglyMeasurable (fun ω => Real.exp (θ * X ω)) μ := by
    exact
      (Measurable.comp_aemeasurable Real.measurable_exp
        (hXm.const_mul θ)).aestronglyMeasurable
  have htarget_int : Integrable (fun ω => Real.exp (θ * X ω)) μ := by
    refine hExpInt.mono htarget_aesm ?_
    exact Filter.Eventually.of_forall fun ω => by
      have harg_le : θ * X ω ≤ |X ω| / K := by
        calc
          θ * X ω ≤ |θ * X ω| := le_abs_self _
          _ = |θ| * |X ω| := by rw [abs_mul]
          _ ≤ (1 / K) * |X ω| :=
            mul_le_mul_of_nonneg_right hθ_le_one_div_K (abs_nonneg _)
          _ = |X ω| / K := by ring
      have hle_exp : Real.exp (θ * X ω) ≤ Real.exp (|X ω| / K) :=
        Real.exp_le_exp.mpr harg_le
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
        abs_of_nonneg (Real.exp_pos _).le] using hle_exp
  let R : Ω → ℝ := fun ω => (θ * X ω) ^ 2 * Real.exp |θ * X ω|
  let D : Ω → ℝ := fun ω => 16 * K ^ 2 * θ ^ 2 * Real.exp (|X ω| / K)
  have hR_aesm : AEStronglyMeasurable R μ := by
    dsimp [R]
    fun_prop
  have hD_int : Integrable D μ := by
    dsimp [D]
    exact hExpInt.const_mul (16 * K ^ 2 * θ ^ 2)
  have hR_le_D : ∀ ω, R ω ≤ D ω := by
    intro ω
    dsimp [R, D]
    exact exp_taylor_remainder_le_subExponential_orlicz_dom hKpos hθ_small
  have hR_int : Integrable R μ := by
    refine hD_int.mono hR_aesm ?_
    exact Filter.Eventually.of_forall fun ω => by
      have hR_nonneg : 0 ≤ R ω := by
        dsimp [R]
        positivity
      have hD_nonneg : 0 ≤ D ω := by
        dsimp [D]
        positivity
      simpa [Real.norm_eq_abs, abs_of_nonneg hR_nonneg, abs_of_nonneg hD_nonneg]
        using hR_le_D ω
  let B : Ω → ℝ := fun ω => 1 + θ * X ω + R ω
  have hB_int : Integrable B μ := by
    dsimp [B]
    exact ((integrable_const (1 : ℝ)).add (hXint.const_mul θ)).add hR_int
  have hpoint : ∀ ω, Real.exp (θ * X ω) ≤ B ω := by
    intro ω
    dsimp [B, R]
    simpa [mul_assoc] using exp_le_one_add_self_add_sq_mul_exp_abs (θ * X ω)
  have hR_integral_le :
      ∫ ω, R ω ∂μ ≤ ∫ ω, D ω ∂μ :=
    integral_mono hR_int hD_int hR_le_D
  have hD_integral_le :
      ∫ ω, D ω ∂μ ≤ 32 * K ^ 2 * θ ^ 2 := by
    calc
      ∫ ω, D ω ∂μ
          = (16 * K ^ 2 * θ ^ 2) *
              ∫ ω, Real.exp (|X ω| / K) ∂μ := by
        dsimp [D]
        rw [integral_const_mul]
      _ ≤ (16 * K ^ 2 * θ ^ 2) * 2 := by
        exact mul_le_mul_of_nonneg_left hExpBound (by positivity)
      _ = 32 * K ^ 2 * θ ^ 2 := by ring
  have hmgf_le_basic :
      mgf X μ θ ≤ 1 + 32 * K ^ 2 * θ ^ 2 := by
    calc
      mgf X μ θ = ∫ ω, Real.exp (θ * X ω) ∂μ := rfl
      _ ≤ ∫ ω, B ω ∂μ :=
        integral_mono htarget_int hB_int hpoint
      _ = ∫ _ω : Ω, (1 : ℝ) ∂μ + ∫ ω, θ * X ω ∂μ + ∫ ω, R ω ∂μ := by
        dsimp [B]
        have hsplit :
            ∫ ω, ((1 : ℝ) + θ * X ω) + R ω ∂μ =
              ∫ _ω : Ω, (1 : ℝ) ∂μ + ∫ ω, θ * X ω ∂μ + ∫ ω, R ω ∂μ := by
          have hsplit_outer :
              ∫ ω, ((1 : ℝ) + θ * X ω) + R ω ∂μ =
                ∫ ω, ((1 : ℝ) + θ * X ω) ∂μ + ∫ ω, R ω ∂μ := by
            simpa [Pi.add_apply] using
              integral_add ((integrable_const (1 : ℝ)).add (hXint.const_mul θ)) hR_int
          have hsplit_inner :
              ∫ ω, ((1 : ℝ) + θ * X ω) ∂μ =
                ∫ _ω : Ω, (1 : ℝ) ∂μ + ∫ ω, θ * X ω ∂μ := by
            simpa [Pi.add_apply] using
              integral_add (integrable_const (1 : ℝ)) (hXint.const_mul θ)
          rw [hsplit_outer, hsplit_inner]
        simpa [add_assoc] using hsplit
      _ = 1 + θ * (∫ ω, X ω ∂μ) + ∫ ω, R ω ∂μ := by
        rw [integral_const_mul]
        simp
      _ = 1 + ∫ ω, R ω ∂μ := by
        rw [hmean, mul_zero, add_zero]
      _ ≤ 1 + 32 * K ^ 2 * θ ^ 2 := by
        exact add_le_add le_rfl (hR_integral_le.trans hD_integral_le)
  have hquad_nonneg : 0 ≤ K ^ 2 * θ ^ 2 := mul_nonneg (sq_nonneg K) (sq_nonneg θ)
  have hlinear_exp : 1 + 32 * K ^ 2 * θ ^ 2 ≤ Real.exp (32 * K ^ 2 * θ ^ 2) := by
    calc
      1 + 32 * K ^ 2 * θ ^ 2 = 32 * K ^ 2 * θ ^ 2 + 1 := by ring
      _ ≤ Real.exp (32 * K ^ 2 * θ ^ 2) :=
        Real.add_one_le_exp (32 * K ^ 2 * θ ^ 2)
  have hexp_mono :
      Real.exp (32 * K ^ 2 * θ ^ 2) ≤ Real.exp ((8 * K) ^ 2 * θ ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h32 : 32 * (K ^ 2 * θ ^ 2) ≤ 64 * (K ^ 2 * θ ^ 2) :=
      mul_le_mul_of_nonneg_right (by norm_num : (32 : ℝ) ≤ 64) hquad_nonneg
    calc
      32 * K ^ 2 * θ ^ 2 = 32 * (K ^ 2 * θ ^ 2) := by ring
      _ ≤ 64 * (K ^ 2 * θ ^ 2) := h32
      _ = (8 * K) ^ 2 * θ ^ 2 := by ring
  refine ⟨htarget_int, ?_⟩
  exact hmgf_le_basic.trans (hlinear_exp.trans hexp_mono)

/-- An admissible `ψ₁` Orlicz scale controls the absolute mean. -/
theorem abs_integral_le_two_mul_of_subExponentialOrliczCondition
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subExponentialOrliczCondition X μ K) :
    |μ[X]| ≤ 2 * K := by
  rcases hX with ⟨hKpos, hInt, hBound⟩
  have habs_aem : AEMeasurable (fun ω => |X ω|) μ := by
    fun_prop
  have hpoint : ∀ ω, |X ω| ≤ K * Real.exp (|X ω| / K) := by
    intro ω
    have hxnonneg : 0 ≤ |X ω| / K :=
      div_nonneg (abs_nonneg _) hKpos.le
    have hxle := real_nonneg_le_exp_self hxnonneg
    have hKnonneg : 0 ≤ K := hKpos.le
    calc
      |X ω| = K * (|X ω| / K) := by
        field_simp [hKpos.ne']
      _ ≤ K * Real.exp (|X ω| / K) :=
        mul_le_mul_of_nonneg_left hxle hKnonneg
  have hdom_int :
      Integrable (fun ω => K * Real.exp (|X ω| / K)) μ :=
    hInt.const_mul K
  have habs_int : Integrable (fun ω => |X ω|) μ := by
    refine hdom_int.mono habs_aem.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      have lhs_nonneg : 0 ≤ |X ω| := abs_nonneg _
      have rhs_nonneg : 0 ≤ K * Real.exp (|X ω| / K) :=
        mul_nonneg hKpos.le (Real.exp_pos _).le
      simpa [Real.norm_eq_abs, abs_of_nonneg lhs_nonneg,
        abs_of_nonneg rhs_nonneg, abs_of_pos hKpos] using hpoint ω
  have hint_abs : μ[fun ω => |X ω|] ≤ 2 * K := by
    calc
      μ[fun ω => |X ω|]
          ≤ ∫ ω, K * Real.exp (|X ω| / K) ∂μ :=
        integral_mono habs_int hdom_int hpoint
      _ = K * ∫ ω, Real.exp (|X ω| / K) ∂μ := by
        rw [integral_const_mul]
      _ ≤ K * 2 :=
        mul_le_mul_of_nonneg_left hBound hKpos.le
      _ = 2 * K := by ring
  exact abs_integral_le_integral_abs.trans hint_abs

/-- The `ψ₁` norm controls the absolute mean. -/
theorem abs_integral_le_two_mul_subExponentialNorm
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ)
    (hXse : IsSubExponential X μ) :
    |μ[X]| ≤ 2 * subExponentialNorm X μ := by
  let S : Set ℝ := {K : ℝ | subExponentialOrliczCondition X μ K}
  have hXset : S.Nonempty := by
    rcases hXse with ⟨K, hK⟩
    exact ⟨K, hK⟩
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro r hr
  have hgap : 0 < r / 2 - subExponentialNorm X μ := by
    linarith
  obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos (s := S) hXset hgap
  have hKlt' :
      K < subExponentialNorm X μ
        + (r / 2 - subExponentialNorm X μ) := by
    change K < subExponentialNorm X μ
      + (r / 2 - subExponentialNorm X μ)
    exact hKlt
  have hKlt_half : K < r / 2 := by
    linarith
  have hmeanK : |μ[X]| ≤ 2 * K :=
    abs_integral_le_two_mul_of_subExponentialOrliczCondition hXm hK
  have h2Klt : 2 * K < r := by
    linarith
  exact hmeanK.trans h2Klt.le

/-- The explicit absolute constant used in the formalized form of HDP
Exercise 2.7.10. -/
def subExponentialCenteringConstant : ℝ :=
  1 + 2 / Real.log 2

/-- The centering constant in Exercise 2.7.10 is positive. -/
theorem subExponentialCenteringConstant_pos :
    0 < subExponentialCenteringConstant := by
  have hlog2_pos : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  unfold subExponentialCenteringConstant
  positivity

/-- HDP Exercise 2.7.10: centering preserves sub-exponentiality with an
absolute `ψ₁` norm constant. -/
theorem subExponentialNorm_centered_le
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ)
    (hXse : IsSubExponential X μ) :
    subExponentialNorm (fun ω => X ω - μ[X]) μ
      ≤ subExponentialCenteringConstant * subExponentialNorm X μ := by
  have hlog2_pos : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  let m : ℝ := μ[X]
  let Y : Ω → ℝ := fun _ω => -m
  have hconst_se : IsSubExponential Y μ := by
    simpa [Y, m] using isSubExponential_const (μ := μ) (-μ[X])
  have hcenter_eq :
      (fun ω => X ω - μ[X]) = fun ω => X ω + Y ω := by
    funext ω
    dsimp [Y, m]
    ring
  have hadd :
      subExponentialNorm (fun ω => X ω + Y ω) μ
        ≤ subExponentialNorm X μ + subExponentialNorm Y μ :=
    subExponentialNorm_add_le (μ := μ)
      (X := X) (Y := Y) hXm (by dsimp [Y]; fun_prop) hXse hconst_se
  have hconst_bound :
      subExponentialNorm Y μ ≤ |μ[X]| / Real.log 2 := by
    have h := subExponentialNorm_const_le_abs_div_log_two
      (μ := μ) (-μ[X])
    simpa [Y, m] using h
  have hmean_bound : |μ[X]| ≤ 2 * subExponentialNorm X μ :=
    abs_integral_le_two_mul_subExponentialNorm hXm hXse
  have hmean_scaled :
      |μ[X]| / Real.log 2
        ≤ (2 * subExponentialNorm X μ) / Real.log 2 :=
    div_le_div_of_nonneg_right hmean_bound hlog2_pos.le
  rw [hcenter_eq]
  calc
    subExponentialNorm (fun ω => X ω + Y ω) μ
        ≤ subExponentialNorm X μ + subExponentialNorm Y μ := hadd
    _ ≤ subExponentialNorm X μ + |μ[X]| / Real.log 2 :=
      add_le_add le_rfl hconst_bound
    _ ≤ subExponentialNorm X μ
        + (2 * subExponentialNorm X μ) / Real.log 2 :=
      add_le_add le_rfl hmean_scaled
    _ = subExponentialCenteringConstant * subExponentialNorm X μ := by
      unfold subExponentialCenteringConstant
      ring

/-- Predicate form of HDP Exercise 2.7.10: centering preserves
sub-exponentiality. -/
theorem isSubExponential_centered
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ)
    (hXse : IsSubExponential X μ) :
    IsSubExponential (fun ω => X ω - μ[X]) μ := by
  let m : ℝ := μ[X]
  let Y : Ω → ℝ := fun _ω => -m
  have hconst_se : IsSubExponential Y μ := by
    simpa [Y, m] using isSubExponential_const (μ := μ) (-μ[X])
  have hcenter_eq :
      (fun ω => X ω - μ[X]) = fun ω => X ω + Y ω := by
    funext ω
    dsimp [Y, m]
    ring
  rw [hcenter_eq]
  rcases hXse with ⟨K, hK⟩
  rcases hconst_se with ⟨L, hL⟩
  exact ⟨K + L, subExponentialOrliczCondition_add
    hXm (by dsimp [Y]; fun_prop) hK hL⟩

end Centering

section RelationToSubGaussian

/-- Pointwise estimate used to show every sub-gaussian random variable is
sub-exponential. -/
lemma exp_abs_div_four_le_exp_const_mul_exp_sq_half {x K : ℝ}
    (_hK : 0 < K) :
    Real.exp (|x| / (4 * K))
      ≤ Real.exp (1 / 32 : ℝ) * Real.exp (x ^ 2 / (2 * K ^ 2)) := by
  have harg :
      |x| / (4 * K) ≤ x ^ 2 / (2 * K ^ 2) + (1 / 32 : ℝ) := by
    let u : ℝ := |x| / K
    have hu_sq : u ^ 2 = x ^ 2 / K ^ 2 := by
      dsimp [u]
      rw [div_pow, sq_abs]
    have hbase : u / 4 ≤ u ^ 2 / 2 + (1 / 32 : ℝ) := by
      have hsq : 0 ≤ (u - (1 / 4 : ℝ)) ^ 2 := sq_nonneg _
      nlinarith
    calc
      |x| / (4 * K) = u / 4 := by
        dsimp [u]
        ring
      _ ≤ u ^ 2 / 2 + (1 / 32 : ℝ) := hbase
      _ = x ^ 2 / (2 * K ^ 2) + (1 / 32 : ℝ) := by
        rw [hu_sq]
        ring
  calc
    Real.exp (|x| / (4 * K))
        ≤ Real.exp (x ^ 2 / (2 * K ^ 2) + (1 / 32 : ℝ)) :=
      Real.exp_le_exp.mpr harg
    _ = Real.exp (1 / 32 : ℝ) * Real.exp (x ^ 2 / (2 * K ^ 2)) := by
      rw [Real.exp_add]
      ring

lemma exp_one_div_thirty_two_mul_sqrt_two_le_two :
    Real.exp (1 / 32 : ℝ) * Real.sqrt 2 ≤ 2 := by
  have hexp : Real.exp (1 / 32 : ℝ) ≤ (4 / 3 : ℝ) := by
    have h := real_exp_le_inv_one_sub_div_pow
      (x := (1 / 32 : ℝ)) (n := 2) (by norm_num) (by norm_num)
    calc
      Real.exp (1 / 32 : ℝ)
          ≤ ((1 - ((1 / 32 : ℝ) / (2 : ℝ))) ^ 2)⁻¹ := h
      _ ≤ (4 / 3 : ℝ) := by norm_num
  have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    norm_num
  nlinarith [Real.sqrt_nonneg 2]

/-- Example 2.7.8(a): a sub-gaussian Orlicz scale gives a sub-exponential
Orlicz scale, with an explicit absolute factor. -/
theorem subExponentialOrliczCondition_of_subGaussianOrliczCondition
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subGaussianOrliczCondition X μ K) :
    subExponentialOrliczCondition X μ (4 * K) := by
  rcases hX with ⟨hKpos, hInt, hBound⟩
  let Y : Ω → ℝ := fun ω => Real.exp (X ω ^ 2 / K ^ 2)
  let α : ℝ := (1 / 2 : ℝ)
  have hscale_pos : 0 < 4 * K := by
    positivity
  have hY_nonneg : ∀ ω, 0 ≤ Y ω :=
    fun ω => (Real.exp_pos _).le
  have hY_ge_one : ∀ ω, 1 ≤ Y ω := by
    intro ω
    dsimp [Y]
    rw [← Real.exp_zero, Real.exp_le_exp]
    exact div_nonneg (sq_nonneg _) (sq_nonneg K)
  have hYhalf_eq :
      (fun ω => Y ω ^ α) =
        fun ω => Real.exp (X ω ^ 2 / (2 * K ^ 2)) := by
    funext ω
    dsimp [Y, α]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have hcont_rpow : Continuous fun y : ℝ => y ^ α :=
    Real.continuous_rpow_const (by norm_num : 0 ≤ α)
  have hYhalf_aesm : AEStronglyMeasurable (fun ω => Y ω ^ α) μ :=
    (hcont_rpow.measurable.comp_aemeasurable hInt.aemeasurable).aestronglyMeasurable
  have hYhalf_int : Integrable (fun ω => Y ω ^ α) μ := by
    refine hInt.mono hYhalf_aesm ?_
    exact Filter.Eventually.of_forall fun ω => by
      have hle : Y ω ^ α ≤ Y ω :=
        Real.rpow_le_self_of_one_le (hY_ge_one ω) (by norm_num : α ≤ 1)
      have hpow_nonneg : 0 ≤ Y ω ^ α :=
        Real.rpow_nonneg (hY_nonneg ω) α
      simpa [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg,
        abs_of_nonneg (hY_nonneg ω)] using hle
  have htarget_aem :
      AEMeasurable (fun ω => Real.exp (|X ω| / (4 * K))) μ := by
    fun_prop
  have hpoint :
      ∀ ω, Real.exp (|X ω| / (4 * K))
        ≤ Real.exp (1 / 32 : ℝ) * (Y ω ^ α) := by
    intro ω
    have h := exp_abs_div_four_le_exp_const_mul_exp_sq_half (x := X ω) hKpos
    have hval : Y ω ^ α = Real.exp (X ω ^ 2 / (2 * K ^ 2)) :=
      congrFun hYhalf_eq ω
    rw [hval]
    exact h
  have hdom_int :
      Integrable (fun ω => Real.exp (1 / 32 : ℝ) * (Y ω ^ α)) μ :=
    hYhalf_int.const_mul (Real.exp (1 / 32 : ℝ))
  have htarget_int :
      Integrable (fun ω => Real.exp (|X ω| / (4 * K))) μ := by
    refine hdom_int.mono_nonneg htarget_aem.aestronglyMeasurable ?_ ?_
    · exact Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
    · exact Filter.Eventually.of_forall hpoint
  have hY_mem : ∀ᵐ ω ∂μ, Y ω ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun ω => hY_nonneg ω
  have hY_int_nonneg : 0 ≤ ∫ ω, Y ω ∂μ :=
    integral_nonneg hY_nonneg
  have hYhalf_le : ∫ ω, Y ω ^ α ∂μ ≤ (∫ ω, Y ω ∂μ) ^ α := by
    exact
      (Real.concaveOn_rpow (by norm_num : 0 ≤ α) (by norm_num : α ≤ 1)).le_map_integral
        hcont_rpow.continuousOn isClosed_Ici hY_mem hInt hYhalf_int
  refine ⟨hscale_pos, htarget_int, ?_⟩
  calc
    ∫ ω, Real.exp (|X ω| / (4 * K)) ∂μ
        ≤ ∫ ω, Real.exp (1 / 32 : ℝ) * (Y ω ^ α) ∂μ :=
      integral_mono htarget_int hdom_int hpoint
    _ = Real.exp (1 / 32 : ℝ) * ∫ ω, Y ω ^ α ∂μ := by
      rw [integral_const_mul]
    _ ≤ Real.exp (1 / 32 : ℝ) * ((∫ ω, Y ω ∂μ) ^ α) :=
      mul_le_mul_of_nonneg_left hYhalf_le (Real.exp_pos _).le
    _ ≤ Real.exp (1 / 32 : ℝ) * ((2 : ℝ) ^ α) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hY_int_nonneg hBound (by norm_num : 0 ≤ α))
        (Real.exp_pos _).le
    _ = Real.exp (1 / 32 : ℝ) * Real.sqrt 2 := by
      have halpha : (2 : ℝ) ^ α = Real.sqrt 2 := by
        dsimp [α]
        rw [← Real.sqrt_eq_rpow]
      rw [halpha]
    _ ≤ 2 := exp_one_div_thirty_two_mul_sqrt_two_le_two

/-- Norm upper-bound form of Example 2.7.8(a). -/
theorem subExponentialNorm_le_of_subGaussianOrliczCondition
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ)
    (hX : subGaussianOrliczCondition X μ K) :
    subExponentialNorm X μ ≤ 4 * K :=
  subExponentialNorm_le_of_subExponentialOrliczCondition
    (subExponentialOrliczCondition_of_subGaussianOrliczCondition hXm hX)

/-- Predicate form of Example 2.7.8(a): every sub-gaussian random variable is
sub-exponential. -/
theorem isSubExponential_of_isSubGaussian
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ)
    (hX : IsSubGaussian X μ) :
    IsSubExponential X μ := by
  rcases hX with ⟨K, hK⟩
  exact ⟨4 * K, subExponentialOrliczCondition_of_subGaussianOrliczCondition hXm hK⟩

/-- HDP Lemma 2.7.6, easy direction at a concrete scale:
if `X` has `ψ₂` Orlicz scale `K`, then `X²` has `ψ₁` Orlicz scale `K²`. -/
theorem subExponentialOrliczCondition_sq_of_subGaussianOrliczCondition
    {X : Ω → ℝ} {K : ℝ}
    (hX : subGaussianOrliczCondition X μ K) :
    subExponentialOrliczCondition (fun ω => X ω ^ 2) μ (K ^ 2) := by
  rcases hX with ⟨hKpos, hInt, hBound⟩
  have hfun :
      (fun ω => Real.exp (|(fun ω => X ω ^ 2) ω| / K ^ 2))
        = fun ω => Real.exp (X ω ^ 2 / K ^ 2) := by
    funext ω
    congr 1
    rw [abs_of_nonneg (sq_nonneg (X ω))]
  refine ⟨sq_pos_of_pos hKpos, ?_, ?_⟩
  · simpa [hfun] using hInt
  · simpa [hfun] using hBound

/-- Norm upper-bound form of one direction of HDP Lemma 2.7.6. -/
theorem subExponentialNorm_sq_le_of_subGaussianOrliczCondition
    {X : Ω → ℝ} {K : ℝ}
    (hX : subGaussianOrliczCondition X μ K) :
    subExponentialNorm (fun ω => X ω ^ 2) μ ≤ K ^ 2 :=
  subExponentialNorm_le_of_subExponentialOrliczCondition
    (subExponentialOrliczCondition_sq_of_subGaussianOrliczCondition hX)

/-- HDP Lemma 2.7.6, converse at a concrete scale:
if `X²` has `ψ₁` Orlicz scale `K`, then `X` has `ψ₂` Orlicz scale `sqrt K`. -/
theorem subGaussianOrliczCondition_of_subExponentialOrliczCondition_sq
    {X : Ω → ℝ} {K : ℝ}
    (hX : subExponentialOrliczCondition (fun ω => X ω ^ 2) μ K) :
    subGaussianOrliczCondition X μ (Real.sqrt K) := by
  rcases hX with ⟨hKpos, hInt, hBound⟩
  have hsqrt_pos : 0 < Real.sqrt K := Real.sqrt_pos.2 hKpos
  have hfun :
      (fun ω => Real.exp (X ω ^ 2 / (Real.sqrt K) ^ 2))
        = fun ω => Real.exp (|(fun ω => X ω ^ 2) ω| / K) := by
    funext ω
    congr 1
    rw [Real.sq_sqrt hKpos.le, abs_of_nonneg (sq_nonneg (X ω))]
  refine ⟨hsqrt_pos, ?_, ?_⟩
  · simpa [hfun] using hInt
  · simpa [hfun] using hBound

/-- Predicate form of HDP Lemma 2.7.6:
`X` is sub-gaussian iff `X²` is sub-exponential. -/
theorem isSubGaussian_iff_isSubExponential_sq
    {X : Ω → ℝ} :
    IsSubGaussian X μ ↔ IsSubExponential (fun ω => X ω ^ 2) μ := by
  constructor
  · intro hX
    rcases hX with ⟨K, hK⟩
    exact ⟨K ^ 2, subExponentialOrliczCondition_sq_of_subGaussianOrliczCondition hK⟩
  · intro hX
    rcases hX with ⟨K, hK⟩
    exact ⟨Real.sqrt K, subGaussianOrliczCondition_of_subExponentialOrliczCondition_sq hK⟩

/-- HDP Lemma 2.7.6, exact norm identity for finite `ψ₂` norm:
`‖X²‖_{ψ₁} = ‖X‖_{ψ₂}²`. -/
theorem subExponentialNorm_sq_eq_subGaussianNorm_sq
    {X : Ω → ℝ}
    (hXse : IsSubGaussian X μ) :
    subExponentialNorm (fun ω => X ω ^ 2) μ = subGaussianNorm X μ ^ 2 := by
  have hSgSet :
      ({K : ℝ | subGaussianOrliczCondition X μ K}).Nonempty := by
    simpa [IsSubGaussian] using hXse
  have hExpSet :
      ({K : ℝ |
        subExponentialOrliczCondition (fun ω => X ω ^ 2) μ K}).Nonempty := by
    rcases hXse with ⟨K, hK⟩
    exact ⟨K ^ 2,
      subExponentialOrliczCondition_sq_of_subGaussianOrliczCondition hK⟩
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense ?_
    intro r hr
    have hsg_nonneg : 0 ≤ subGaussianNorm X μ :=
      subGaussianNorm_nonneg X μ
    have hr_pos : 0 < r :=
      lt_of_le_of_lt (sq_nonneg (subGaussianNorm X μ)) hr
    have hsg_lt_sqrt : subGaussianNorm X μ < Real.sqrt r := by
      exact (Real.lt_sqrt hsg_nonneg).mpr (by simpa [pow_two] using hr)
    have hgap : 0 < Real.sqrt r - subGaussianNorm X μ := by
      linarith
    obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos
      (s := {K : ℝ | subGaussianOrliczCondition X μ K}) hSgSet hgap
    have hKlt_sqrt : K < Real.sqrt r := by
      have hKlt' :
          K < subGaussianNorm X μ
            + (Real.sqrt r - subGaussianNorm X μ) := by
        simpa [subGaussianNorm] using hKlt
      simpa using hKlt'
    have hKsq_lt : K ^ 2 < r :=
      (Real.lt_sqrt hK.1.le).mp hKlt_sqrt
    have hupper :
        subExponentialNorm (fun ω => X ω ^ 2) μ ≤ K ^ 2 :=
      subExponentialNorm_sq_le_of_subGaussianOrliczCondition hK
    exact hupper.trans hKsq_lt.le
  · refine le_csInf hExpSet ?_
    intro K hK
    have hsg_le :
        subGaussianNorm X μ ≤ Real.sqrt K :=
      subGaussianNorm_le_of_subGaussianOrliczCondition
        (subGaussianOrliczCondition_of_subExponentialOrliczCondition_sq hK)
    have hsq_le :
        subGaussianNorm X μ ^ 2 ≤ (Real.sqrt K) ^ 2 := by
      exact (sq_le_sq₀
        (subGaussianNorm_nonneg X μ)
        (Real.sqrt_nonneg K)).mpr hsg_le
    exact hsq_le.trans_eq (Real.sq_sqrt hK.1.le)

/-- Young's inequality in the exponential form used in HDP Lemma 2.7.7. -/
lemma exp_abs_mul_div_le_half_exp_sq_add_half_exp_sq
    {x y K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    Real.exp (|x * y| / (K * L))
      ≤ (1 / 2 : ℝ) * Real.exp (x ^ 2 / K ^ 2)
        + (1 / 2 : ℝ) * Real.exp (y ^ 2 / L ^ 2) := by
  let u : ℝ := |x| / K
  let v : ℝ := |y| / L
  have hyoung : u * v ≤ (u ^ 2 + v ^ 2) / 2 := by
    have hsq : 0 ≤ (u - v) ^ 2 := sq_nonneg (u - v)
    nlinarith
  have hleft_eq : |x * y| / (K * L) = u * v := by
    dsimp [u, v]
    rw [abs_mul]
    field_simp [hK.ne', hL.ne']
  have hu_sq : u ^ 2 = x ^ 2 / K ^ 2 := by
    dsimp [u]
    rw [div_pow, sq_abs]
  have hv_sq : v ^ 2 = y ^ 2 / L ^ 2 := by
    dsimp [v]
    rw [div_pow, sq_abs]
  have hexp_arg :
      |x * y| / (K * L) ≤ (x ^ 2 / K ^ 2 + y ^ 2 / L ^ 2) / 2 := by
    calc
      |x * y| / (K * L) = u * v := hleft_eq
      _ ≤ (u ^ 2 + v ^ 2) / 2 := hyoung
      _ = (x ^ 2 / K ^ 2 + y ^ 2 / L ^ 2) / 2 := by
        rw [hu_sq, hv_sq]
  have hconv :
      Real.exp ((x ^ 2 / K ^ 2 + y ^ 2 / L ^ 2) / 2)
        ≤ (1 / 2 : ℝ) * Real.exp (x ^ 2 / K ^ 2)
          + (1 / 2 : ℝ) * Real.exp (y ^ 2 / L ^ 2) := by
    have h :=
      convexOn_exp.2
        (Set.mem_univ (x ^ 2 / K ^ 2))
        (Set.mem_univ (y ^ 2 / L ^ 2))
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    convert h using 1
    ring_nf
  calc
    Real.exp (|x * y| / (K * L))
        ≤ Real.exp ((x ^ 2 / K ^ 2 + y ^ 2 / L ^ 2) / 2) :=
      Real.exp_le_exp.mpr hexp_arg
    _ ≤ (1 / 2 : ℝ) * Real.exp (x ^ 2 / K ^ 2)
        + (1 / 2 : ℝ) * Real.exp (y ^ 2 / L ^ 2) := hconv

/-- HDP Lemma 2.7.7 at concrete Orlicz scales: the product of two
sub-gaussian variables is sub-exponential.  No independence is needed. -/
theorem subExponentialOrliczCondition_mul_of_subGaussianOrliczCondition
    [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} {K L : ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : subGaussianOrliczCondition X μ K)
    (hY : subGaussianOrliczCondition Y μ L) :
    subExponentialOrliczCondition (fun ω => X ω * Y ω) μ (K * L) := by
  rcases hX with ⟨hKpos, hXInt, hXBound⟩
  rcases hY with ⟨hLpos, hYInt, hYBound⟩
  have hKLpos : 0 < K * L := mul_pos hKpos hLpos
  let F : Ω → ℝ := fun ω => Real.exp (|X ω * Y ω| / (K * L))
  let G : Ω → ℝ :=
    fun ω => (1 / 2 : ℝ) * Real.exp (X ω ^ 2 / K ^ 2)
      + (1 / 2 : ℝ) * Real.exp (Y ω ^ 2 / L ^ 2)
  have hpoint : ∀ ω, F ω ≤ G ω := by
    intro ω
    exact exp_abs_mul_div_le_half_exp_sq_add_half_exp_sq hKpos hLpos
  have hGInt : Integrable G μ := by
    dsimp [G]
    exact (hXInt.const_mul (1 / 2 : ℝ)).add (hYInt.const_mul (1 / 2 : ℝ))
  have hFaem : AEMeasurable F μ := by
    dsimp [F]
    fun_prop
  have hFInt : Integrable F μ := by
    refine hGInt.mono hFaem.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      have hF_nonneg : 0 ≤ F ω := (Real.exp_pos _).le
      have hG_nonneg : 0 ≤ G ω := (hF_nonneg.trans (hpoint ω))
      simpa [Real.norm_eq_abs, abs_of_nonneg hF_nonneg, abs_of_nonneg hG_nonneg]
        using hpoint ω
  refine ⟨hKLpos, ?_, ?_⟩
  · simpa [F] using hFInt
  · calc
      ∫ ω, Real.exp (|X ω * Y ω| / (K * L)) ∂μ
          = ∫ ω, F ω ∂μ := rfl
      _ ≤ ∫ ω, G ω ∂μ :=
        integral_mono hFInt hGInt hpoint
      _ = (1 / 2 : ℝ) * ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ
          + (1 / 2 : ℝ) * ∫ ω, Real.exp (Y ω ^ 2 / L ^ 2) ∂μ := by
        dsimp [G]
        rw [integral_add (hXInt.const_mul (1 / 2 : ℝ))
          (hYInt.const_mul (1 / 2 : ℝ)), integral_const_mul, integral_const_mul]
      _ ≤ (1 / 2 : ℝ) * 2 + (1 / 2 : ℝ) * 2 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hXBound (by norm_num))
          (mul_le_mul_of_nonneg_left hYBound (by norm_num))
      _ = 2 := by norm_num

/-- Norm upper-bound form of HDP Lemma 2.7.7 at concrete Orlicz scales. -/
theorem subExponentialNorm_mul_le_of_subGaussianOrliczCondition
    [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} {K L : ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : subGaussianOrliczCondition X μ K)
    (hY : subGaussianOrliczCondition Y μ L) :
    subExponentialNorm (fun ω => X ω * Y ω) μ ≤ K * L :=
  subExponentialNorm_le_of_subExponentialOrliczCondition
    (subExponentialOrliczCondition_mul_of_subGaussianOrliczCondition
      hXm hYm hX hY)

/-- HDP Lemma 2.7.7, norm form: the product of two sub-gaussian random
variables is sub-exponential and its `ψ₁` norm is bounded by the product of
the `ψ₂` norms. No independence is needed. -/
theorem subExponentialNorm_mul_le_subGaussianNorm_mul
    [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hXse : IsSubGaussian X μ) (hYse : IsSubGaussian Y μ) :
    subExponentialNorm (fun ω => X ω * Y ω) μ
      ≤ subGaussianNorm X μ * subGaussianNorm Y μ := by
  let a : ℝ := subGaussianNorm X μ
  let b : ℝ := subGaussianNorm Y μ
  have hXset :
      ({K : ℝ | subGaussianOrliczCondition X μ K}).Nonempty := by
    simpa [IsSubGaussian] using hXse
  have hYset :
      ({L : ℝ | subGaussianOrliczCondition Y μ L}).Nonempty := by
    simpa [IsSubGaussian] using hYse
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact subGaussianNorm_nonneg X μ
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact subGaussianNorm_nonneg Y μ
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro r hr
  have hgap : 0 < r - a * b := by
    simpa [a, b] using sub_pos.mpr hr
  have hden_pos : 0 < 2 * (a + b + 1) := by
    positivity
  let ε : ℝ := min 1 ((r - a * b) / (2 * (a + b + 1)))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min zero_lt_one (div_pos hgap hden_pos)
  have hε_nonneg : 0 ≤ ε := hε_pos.le
  have hε_le_one : ε ≤ 1 := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_le_gap :
      ε ≤ (r - a * b) / (2 * (a + b + 1)) := by
    dsimp [ε]
    exact min_le_right _ _
  have hε_sq_le : ε ^ 2 ≤ ε := by
    nlinarith [sq_nonneg ε, hε_nonneg, hε_le_one]
  have hε_mul_le_half :
      ε * (a + b + 1) ≤ (r - a * b) / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hε_le_gap
      (by positivity : 0 ≤ a + b + 1)
    have hsimpl :
        ((r - a * b) / (2 * (a + b + 1))) * (a + b + 1)
          = (r - a * b) / 2 := by
      field_simp [(show a + b + 1 ≠ 0 by positivity)]
    simpa [hsimpl] using hmul
  have hprod_bound :
      (a + ε) * (b + ε) < r := by
    have hextra :
        ε * (a + b) + ε ^ 2 ≤ ε * (a + b + 1) := by
      nlinarith [hε_sq_le, hε_nonneg, ha_nonneg, hb_nonneg]
    calc
      (a + ε) * (b + ε)
          = a * b + (ε * (a + b) + ε ^ 2) := by ring
      _ ≤ a * b + ε * (a + b + 1) := by
        nlinarith
      _ ≤ a * b + (r - a * b) / 2 := by
        nlinarith
      _ < r := by
        linarith
  obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos
    (s := {K : ℝ | subGaussianOrliczCondition X μ K}) hXset hε_pos
  obtain ⟨L, hL, hLlt⟩ := Real.lt_sInf_add_pos
    (s := {L : ℝ | subGaussianOrliczCondition Y μ L}) hYset hε_pos
  have hKlt' : K < a + ε := by
    have hKlt'' : K < subGaussianNorm X μ + ε := by
      simpa [subGaussianNorm] using hKlt
    simpa [a] using hKlt''
  have hLlt' : L < b + ε := by
    have hLlt'' : L < subGaussianNorm Y μ + ε := by
      simpa [subGaussianNorm] using hLlt
    simpa [b] using hLlt''
  have haε_nonneg : 0 ≤ a + ε := by positivity
  have hKL_le : K * L ≤ (a + ε) * (b + ε) :=
    mul_le_mul hKlt'.le hLlt'.le hL.1.le haε_nonneg
  have hKL_lt : K * L < r := hKL_le.trans_lt hprod_bound
  have hnorm_le :
      subExponentialNorm (fun ω => X ω * Y ω) μ ≤ K * L :=
    subExponentialNorm_mul_le_of_subGaussianOrliczCondition
      (μ := μ) hXm hYm hK hL
  exact hnorm_le.trans hKL_lt.le

/-- Predicate form of HDP Lemma 2.7.7: the product of two sub-gaussian
variables is sub-exponential. No independence is needed. -/
theorem isSubExponential_mul_of_isSubGaussian
    [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : IsSubGaussian X μ) (hY : IsSubGaussian Y μ) :
    IsSubExponential (fun ω => X ω * Y ω) μ := by
  rcases hX with ⟨K, hK⟩
  rcases hY with ⟨L, hL⟩
  exact ⟨K * L,
    subExponentialOrliczCondition_mul_of_subGaussianOrliczCondition
      hXm hYm hK hL⟩

end RelationToSubGaussian

section Examples

/-- Example 2.7.8(b): the square of a standard normal random variable is
sub-exponential, with an explicit `ψ₁` scale inherited from the standard
normal `ψ₂` scale. -/
theorem standardNormal_sq_subExponentialOrliczCondition :
    subExponentialOrliczCondition (fun x : ℝ => x ^ 2) standardNormalMeasure 4 := by
  have h :=
    subExponentialOrliczCondition_sq_of_subGaussianOrliczCondition
      (μ := standardNormalMeasure) (X := id)
      standardNormal_subGaussianOrliczCondition
  norm_num at h
  exact h

/-- Example 2.7.8(b), norm form: `g²` for a standard normal `g` has bounded
`ψ₁` norm. -/
theorem standardNormal_sq_subExponentialNorm_le :
    subExponentialNorm (fun x : ℝ => x ^ 2) standardNormalMeasure ≤ 4 :=
  subExponentialNorm_le_of_subExponentialOrliczCondition
    standardNormal_sq_subExponentialOrliczCondition

/-- Example 2.7.8(b), Gaussian-square scale for `N(0,v)`. -/
theorem centeredGaussian_sq_subExponentialOrliczCondition
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) :
    subExponentialOrliczCondition (fun x : ℝ => x ^ 2)
      (ProbabilityTheory.gaussianReal 0 v) (8 * (v : ℝ)) := by
  have hsq :=
    subExponentialOrliczCondition_sq_of_subGaussianOrliczCondition
      (μ := ProbabilityTheory.gaussianReal 0 v) (X := id)
      (centeredGaussian_subGaussianOrliczCondition (v := v) hv)
  have hscale :
      (2 * (Real.sqrt 2 * Real.sqrt (v : ℝ))) ^ 2 = 8 * (v : ℝ) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt hv.le]
    ring
  simpa [hscale] using hsq

/-- Example 2.7.8(b), norm form for Gaussian squares. -/
theorem centeredGaussian_sq_subExponentialNorm_le
    {v : ℝ≥0} (hv : 0 < (v : ℝ)) :
    subExponentialNorm (fun x : ℝ => x ^ 2)
      (ProbabilityTheory.gaussianReal 0 v) ≤ 8 * (v : ℝ) :=
  subExponentialNorm_le_of_subExponentialOrliczCondition
    (centeredGaussian_sq_subExponentialOrliczCondition (v := v) hv)

/-- Density rewrite for the exponential-law MGF calculation in HDP
Remark 2.7.9.  Under the exponential density, the integrand
`exp(θx)` becomes `r exp((θ-r)x)` on `[0,∞)`. -/
lemma expMeasure_density_mul_exp_eq_indicator {r θ : ℝ} (hr : 0 < r) :
    (fun x : ℝ => (ProbabilityTheory.exponentialPDF r x).toReal
        * Real.exp (θ * x)) =
      (Set.Ici (0 : ℝ)).indicator
        (fun x : ℝ => r * Real.exp ((θ - r) * x)) := by
  funext x
  by_cases hx : 0 ≤ x
  · have hnonneg : 0 ≤ r * Real.exp (-(r * x)) :=
      mul_nonneg hr.le (Real.exp_pos _).le
    simp [ProbabilityTheory.exponentialPDF_eq, hx,
      ENNReal.toReal_ofReal hnonneg]
    calc
      r * Real.exp (-(r * x)) * Real.exp (θ * x)
          = r * (Real.exp (-(r * x)) * Real.exp (θ * x)) := by
            ring_nf
      _ = r * Real.exp (-(r * x) + θ * x) := by
            rw [Real.exp_add]
      _ = r * Real.exp ((θ - r) * x) := by
            congr 1
            ring_nf
  · simp [ProbabilityTheory.exponentialPDF_eq, hx]

/-- HDP Remark 2.7.9, finite side of the natural MGF radius for an
exponential random variable: `E exp(θX) < ∞` when `θ < r`. -/
theorem expMeasure_integrable_exp_mul_of_lt {r θ : ℝ}
    (hr : 0 < r) (hθ : θ < r) :
    Integrable (fun x : ℝ => Real.exp (θ * x))
      (ProbabilityTheory.expMeasure r) := by
  have hf_ae :
      AEMeasurable (ProbabilityTheory.exponentialPDF r)
        (volume : Measure ℝ) := by
    change AEMeasurable
      (fun x => ENNReal.ofReal (ProbabilityTheory.exponentialPDFReal r x))
        volume
    exact (ProbabilityTheory.measurable_exponentialPDFReal r).aemeasurable.ennreal_ofReal
  have hf_top :
      ∀ᵐ x ∂(volume : Measure ℝ),
        ProbabilityTheory.exponentialPDF r x < ⊤ := by
    filter_upwards [] with x
    simp [ProbabilityTheory.exponentialPDF]
  rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure]
  change Integrable (fun x : ℝ => Real.exp (θ * x))
    ((volume : Measure ℝ).withDensity (ProbabilityTheory.exponentialPDF r))
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul₀' hf_ae hf_top]
  change Integrable
    (fun x : ℝ => (ProbabilityTheory.exponentialPDF r x).toReal
      * Real.exp (θ * x)) volume
  rw [expMeasure_density_mul_exp_eq_indicator (r := r) (θ := θ) hr]
  rw [MeasureTheory.integrable_indicator_iff measurableSet_Ici]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hcoef : θ - r < 0 := by linarith
  exact (integrableOn_exp_mul_Ioi hcoef 0).const_mul r

/-- HDP Remark 2.7.9, exact MGF formula for an exponential variable with rate
`r`: for `θ < r`, `E exp(θX) = r / (r - θ)`.  This identifies the natural
finite side of the MGF radius. -/
theorem expMeasure_mgf_eq_of_lt {r θ : ℝ}
    (hr : 0 < r) (hθ : θ < r) :
    ProbabilityTheory.mgf id (ProbabilityTheory.expMeasure r) θ
      = r / (r - θ) := by
  unfold ProbabilityTheory.mgf
  rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure]
  change
    ∫ x, Real.exp (θ * id x)
      ∂((volume : Measure ℝ).withDensity
        (ProbabilityTheory.exponentialPDF r)) = r / (r - θ)
  rw [integral_withDensity_eq_integral_toReal_smul]
  · change
      ∫ x, (ProbabilityTheory.exponentialPDF r x).toReal
          * Real.exp (θ * x) ∂volume = r / (r - θ)
    rw [expMeasure_density_mul_exp_eq_indicator (r := r) (θ := θ) hr]
    rw [MeasureTheory.integral_indicator measurableSet_Ici]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    have hcoef : θ - r < 0 := by linarith
    rw [integral_const_mul]
    rw [integral_exp_mul_Ioi hcoef 0]
    have hfrac : -1 / (θ - r) = 1 / (r - θ) := by
      have hden : θ - r = -(r - θ) := by ring
      rw [hden]
      field_simp [(sub_pos.mpr hθ).ne']
    simp
    rw [hfrac]
    ring
  · change Measurable (ProbabilityTheory.exponentialPDF r)
    change Measurable
      (fun x => ENNReal.ofReal (ProbabilityTheory.exponentialPDFReal r x))
    exact (ProbabilityTheory.measurable_exponentialPDFReal r).ennreal_ofReal
  · filter_upwards [] with x
    simp [ProbabilityTheory.exponentialPDF]

/-- A positive constant is not integrable on an infinite Lebesgue ray. -/
lemma not_integrableOn_const_Ici_of_pos {c a : ℝ} (hc : 0 < c) :
    ¬ IntegrableOn (fun _ : ℝ => c) (Set.Ici a) (volume : Measure ℝ) := by
  rw [integrableOn_const_iff]
  simp [hc.ne']

/-- If `a ≥ 0`, then `c exp(ax)` is not integrable on `[0,∞)` for
positive `c`. -/
lemma not_integrableOn_pos_mul_exp_mul_Ici_of_nonneg
    {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) :
    ¬ IntegrableOn (fun x : ℝ => c * Real.exp (a * x))
      (Set.Ici (0 : ℝ)) (volume : Measure ℝ) := by
  intro h
  have hconst :
      IntegrableOn (fun _ : ℝ => c) (Set.Ici (0 : ℝ))
        (volume : Measure ℝ) := by
    change Integrable (fun _ : ℝ => c)
      ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))
    change Integrable (fun x : ℝ => c * Real.exp (a * x))
      ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) at h
    refine h.mono (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    have hax_nonneg : 0 ≤ a * x := mul_nonneg ha hx
    have hexp_ge : 1 ≤ Real.exp (a * x) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (a * x) := Real.exp_le_exp.mpr hax_nonneg
    have hdom_nonneg : 0 ≤ c * Real.exp (a * x) :=
      mul_nonneg hc.le (Real.exp_pos _).le
    have hconst_nonneg : 0 ≤ c := hc.le
    calc
      ‖c‖ = c := by
        rw [Real.norm_eq_abs, abs_of_nonneg hconst_nonneg]
      _ ≤ c * Real.exp (a * x) := by
        calc
          c = c * 1 := by ring
          _ ≤ c * Real.exp (a * x) :=
            mul_le_mul_of_nonneg_left hexp_ge hc.le
      _ = ‖c * Real.exp (a * x)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hdom_nonneg]
  exact not_integrableOn_const_Ici_of_pos hc hconst

/-- HDP Remark 2.7.9, divergent side of the natural MGF radius for an
exponential random variable: `E exp(θX)` is not finite when `θ ≥ r`. -/
theorem expMeasure_not_integrable_exp_mul_of_ge {r θ : ℝ}
    (hr : 0 < r) (hθ : r ≤ θ) :
    ¬ Integrable (fun x : ℝ => Real.exp (θ * x))
      (ProbabilityTheory.expMeasure r) := by
  intro h
  have hf_ae :
      AEMeasurable (ProbabilityTheory.exponentialPDF r)
        (volume : Measure ℝ) := by
    change AEMeasurable
      (fun x => ENNReal.ofReal (ProbabilityTheory.exponentialPDFReal r x))
        volume
    exact (ProbabilityTheory.measurable_exponentialPDFReal r).aemeasurable.ennreal_ofReal
  have hf_top :
      ∀ᵐ x ∂(volume : Measure ℝ),
        ProbabilityTheory.exponentialPDF r x < ⊤ := by
    filter_upwards [] with x
    simp [ProbabilityTheory.exponentialPDF]
  have h' :
      Integrable (fun x : ℝ => Real.exp (θ * x))
        ((volume : Measure ℝ).withDensity
          (ProbabilityTheory.exponentialPDF r)) := by
    simpa [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure] using h
  have hweighted_smul :
      Integrable
        (fun x : ℝ =>
          (ProbabilityTheory.exponentialPDF r x).toReal
            • Real.exp (θ * x)) volume :=
    (MeasureTheory.integrable_withDensity_iff_integrable_smul₀'
      hf_ae hf_top).mp h'
  have hweighted :
      Integrable
        (fun x : ℝ =>
          (ProbabilityTheory.exponentialPDF r x).toReal
            * Real.exp (θ * x)) volume := by
    simpa [smul_eq_mul] using hweighted_smul
  rw [expMeasure_density_mul_exp_eq_indicator (r := r) (θ := θ) hr]
    at hweighted
  have hon :
      IntegrableOn (fun x : ℝ => r * Real.exp ((θ - r) * x))
        (Set.Ici (0 : ℝ)) (volume : Measure ℝ) := by
    rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ici]
    exact hweighted
  exact not_integrableOn_pos_mul_exp_mul_Ici_of_nonneg
    hr (sub_nonneg.mpr hθ) hon

/-- Example 2.7.8(c), lower scale for exponential variables: every admissible
`ψ₁` Orlicz scale for an exponential law of rate `r` is at least `2/r`. -/
theorem expMeasure_subExponentialOrliczScale_ge {r K : ℝ}
    (hr : 0 < r)
    (hK : subExponentialOrliczCondition id
      (ProbabilityTheory.expMeasure r) K) :
    2 / r ≤ K := by
  rcases hK with ⟨hKpos, hIntAbs, hBoundAbs⟩
  have hpoint : ∀ x : ℝ,
      Real.exp ((1 / K) * x) ≤ Real.exp (|id x| / K) := by
    intro x
    apply Real.exp_le_exp.mpr
    have hx : x ≤ |x| := le_abs_self x
    have hdiv := div_le_div_of_nonneg_right hx hKpos.le
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hdiv
  have hIntPos :
      Integrable (fun x : ℝ => Real.exp ((1 / K) * x))
        (ProbabilityTheory.expMeasure r) := by
    refine hIntAbs.mono (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun x => by
      have hleft_nonneg : 0 ≤ Real.exp ((1 / K) * x) :=
        (Real.exp_pos _).le
      have hright_nonneg : 0 ≤ Real.exp (|id x| / K) :=
        (Real.exp_pos _).le
      calc
        ‖Real.exp ((1 / K) * x)‖ = Real.exp ((1 / K) * x) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg]
        _ ≤ Real.exp (|id x| / K) := hpoint x
        _ = ‖Real.exp (|id x| / K)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hright_nonneg]
  have htheta_lt : 1 / K < r := by
    by_contra hnot
    exact expMeasure_not_integrable_exp_mul_of_ge
      (r := r) (θ := 1 / K) hr (not_lt.mp hnot) hIntPos
  have hmgf_le :
      ProbabilityTheory.mgf id (ProbabilityTheory.expMeasure r) (1 / K)
        ≤ 2 := by
    change
      ∫ x, Real.exp ((1 / K) * id x)
        ∂ProbabilityTheory.expMeasure r ≤ 2
    have hle :
        ∫ x, Real.exp ((1 / K) * x) ∂ProbabilityTheory.expMeasure r
          ≤ ∫ x, Real.exp (|id x| / K)
              ∂ProbabilityTheory.expMeasure r :=
      integral_mono hIntPos hIntAbs hpoint
    exact hle.trans hBoundAbs
  have hformula :=
    expMeasure_mgf_eq_of_lt (r := r) (θ := 1 / K) hr htheta_lt
  rw [hformula] at hmgf_le
  have hden_pos : 0 < r - 1 / K := sub_pos.mpr htheta_lt
  have hmul : r ≤ 2 * (r - 1 / K) :=
    (div_le_iff₀ hden_pos).mp hmgf_le
  have hmulK' : r * K ≤ (2 * (r - 1 / K)) * K :=
    mul_le_mul_of_nonneg_right hmul hKpos.le
  have hcalc : (2 * (r - 1 / K)) * K = 2 * r * K - 2 := by
    field_simp [hKpos.ne']
  have htwo_le : 2 ≤ r * K := by
    have htmp : r * K ≤ 2 * r * K - 2 := by
      calc
        r * K ≤ (2 * (r - 1 / K)) * K := hmulK'
        _ = 2 * r * K - 2 := hcalc
    linarith
  exact (div_le_iff₀ hr).mpr (by simpa [mul_comm] using htwo_le)

/-- The exponential law has no mass on the negative half-line. -/
lemma expMeasure_real_Iio_zero_eq_zero {r : ℝ} (hr : 0 < r) :
    (ProbabilityTheory.expMeasure r).real (Set.Iio (0 : ℝ)) = 0 := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  have hIic :
      (ProbabilityTheory.expMeasure r).real (Set.Iic (0 : ℝ)) = 0 := by
    calc
      (ProbabilityTheory.expMeasure r).real (Set.Iic (0 : ℝ))
          = ProbabilityTheory.cdf (ProbabilityTheory.expMeasure r) 0 := by
        rw [ProbabilityTheory.cdf_eq_real]
      _ = 0 := by
        rw [ProbabilityTheory.cdf_expMeasure_eq hr 0, if_pos le_rfl]
        simp
  have hle :
      (ProbabilityTheory.expMeasure r).real (Set.Iio (0 : ℝ))
        ≤ (ProbabilityTheory.expMeasure r).real (Set.Iic (0 : ℝ)) :=
    MeasureTheory.measureReal_mono (Set.Iio_subset_Iic_self)
  exact le_antisymm (by simpa [hIic] using hle) MeasureTheory.measureReal_nonneg

/-- Example 2.7.8(c): exponential random variables are sub-exponential.  The
scale is explicit and of the optimal order in the rate parameter. -/
theorem expMeasure_subExponentialTailCondition {r : ℝ} (hr : 0 < r) :
    subExponentialTailCondition id (ProbabilityTheory.expMeasure r) (2 / r) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  refine ⟨by positivity, fun t ht => ?_⟩
  by_cases ht0 : t = 0
  · subst ht0
    calc
      (ProbabilityTheory.expMeasure r).real {x : ℝ | 0 ≤ |id x|}
          ≤ 1 := measureReal_le_one
      _ ≤ 2 * Real.exp (-(0 / (2 / r))) := by norm_num
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let A : Set ℝ := Set.Iio (0 : ℝ)
    let B : Set ℝ := Set.Ioi (t / 2)
    have hsubset : {x : ℝ | t ≤ |id x|} ⊆ A ∪ B := by
      intro x hx
      by_cases hxneg : x < 0
      · exact Or.inl hxneg
      · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
        have hxt : t ≤ x := by simpa [id_eq, abs_of_nonneg hxnonneg] using hx
        right
        dsimp [B]
        exact lt_of_lt_of_le (by linarith : t / 2 < t) hxt
    have htail :
        (ProbabilityTheory.expMeasure r).real {x : ℝ | t ≤ |id x|}
          ≤ Real.exp (-(r * (t / 2))) := by
      calc
        (ProbabilityTheory.expMeasure r).real {x : ℝ | t ≤ |id x|}
            ≤ (ProbabilityTheory.expMeasure r).real (A ∪ B) :=
          MeasureTheory.measureReal_mono hsubset
        _ ≤ (ProbabilityTheory.expMeasure r).real A
            + (ProbabilityTheory.expMeasure r).real B :=
          MeasureTheory.measureReal_union_le A B
        _ = 0 + Real.exp (-(r * (t / 2))) := by
          rw [expMeasure_real_Iio_zero_eq_zero hr]
          rw [expMeasure_real_Ioi_eq_exp_neg_mul hr (by linarith : 0 ≤ t / 2)]
        _ = Real.exp (-(r * (t / 2))) := by ring
    calc
      (ProbabilityTheory.expMeasure r).real {x : ℝ | t ≤ |id x|}
          ≤ Real.exp (-(r * (t / 2))) := htail
      _ ≤ 2 * Real.exp (-(t / (2 / r))) := by
        have harg : -(r * (t / 2)) = -(t / (2 / r)) := by
          field_simp [hr.ne']
        rw [harg]
        exact le_mul_of_one_le_left (Real.exp_pos _).le (by norm_num : (1 : ℝ) ≤ 2)

/-- Example 2.7.8(c), Orlicz form for exponential random variables. -/
theorem expMeasure_subExponentialOrliczCondition {r : ℝ} (hr : 0 < r) :
    subExponentialOrliczCondition id (ProbabilityTheory.expMeasure r) (8 / r) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  have htail := expMeasure_subExponentialTailCondition (r := r) hr
  have horl :=
    subExponentialOrliczCondition_of_subExponentialTailCondition
      (μ := ProbabilityTheory.expMeasure r) (X := id) (K := 2 / r)
      measurable_id.aemeasurable htail
  simpa [show 4 * (2 / r) = 8 / r by ring] using horl

/-- Example 2.7.8(c), norm form for exponential random variables. -/
theorem expMeasure_subExponentialNorm_le {r : ℝ} (hr : 0 < r) :
    subExponentialNorm id (ProbabilityTheory.expMeasure r) ≤ 8 / r :=
  subExponentialNorm_le_of_subExponentialOrliczCondition
    (expMeasure_subExponentialOrliczCondition (r := r) hr)

/-- Example 2.7.8(c), lower norm form for exponential random variables:
the `ψ₁` norm has the optimal order in the rate parameter. -/
theorem expMeasure_subExponentialNorm_ge {r : ℝ} (hr : 0 < r) :
    2 / r ≤ subExponentialNorm id (ProbabilityTheory.expMeasure r) := by
  unfold subExponentialNorm
  refine le_csInf ?hne ?hlower
  · exact ⟨8 / r, expMeasure_subExponentialOrliczCondition (r := r) hr⟩
  · intro K hK
    exact expMeasure_subExponentialOrliczScale_ge (r := r) (K := K) hr hK

/-- Example 2.7.8(c), two-sided order bound for the exponential `ψ₁` norm. -/
theorem expMeasure_subExponentialNorm_order {r : ℝ} (hr : 0 < r) :
    2 / r ≤ subExponentialNorm id (ProbabilityTheory.expMeasure r)
      ∧ subExponentialNorm id (ProbabilityTheory.expMeasure r) ≤ 8 / r :=
  ⟨expMeasure_subExponentialNorm_ge (r := r) hr,
    expMeasure_subExponentialNorm_le (r := r) hr⟩

/-- A convenient explicit `ψ₁` scale for a Poisson random variable with mean
`λ`.  It is of order `1 + λ`, which is the order asserted in Example 2.7.8. -/
def poissonSubExponentialScale (lam : ℝ≥0) : ℝ :=
  1 + 2 * (lam : ℝ) / Real.log 2

lemma poissonSubExponentialScale_pos (lam : ℝ≥0) :
    0 < poissonSubExponentialScale lam := by
  have hlog : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  unfold poissonSubExponentialScale
  positivity

/-- Example 2.7.8(d): Poisson random variables are sub-exponential. -/
theorem poisson_subExponentialOrliczCondition (lam : ℝ≥0) :
    subExponentialOrliczCondition (fun n : ℕ => (n : ℝ))
      (ProbabilityTheory.poissonMeasure lam) (poissonSubExponentialScale lam) := by
  let K : ℝ := poissonSubExponentialScale lam
  have hKpos : 0 < K := poissonSubExponentialScale_pos lam
  let θ : ℝ := 1 / K
  have hθ_nonneg : 0 ≤ θ := by dsimp [θ]; positivity
  have hK_ge_one : 1 ≤ K := by
    have hlog : 0 < Real.log 2 := by
      rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hnonneg : 0 ≤ 2 * (lam : ℝ) / Real.log 2 := by
      positivity
    dsimp [K, poissonSubExponentialScale]
    linarith
  have hθ_le_one : θ ≤ 1 := by
    dsimp [θ]
    rw [div_le_iff₀ hKpos]
    simpa using hK_ge_one
  have hInt :
      Integrable (fun n : ℕ => Real.exp (|(n : ℝ)| / K))
        (ProbabilityTheory.poissonMeasure lam) := by
    have h :=
      integrable_exp_mul_poissonMeasure lam θ
    convert h using 1
    funext n
    dsimp [θ]
    rw [abs_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
    ring_nf
  have hmgf_eq :
      (∫ n : ℕ, Real.exp (|(n : ℝ)| / K) ∂ProbabilityTheory.poissonMeasure lam)
        = Real.exp ((Real.exp θ - 1) * (lam : ℝ)) := by
    calc
      (∫ n : ℕ, Real.exp (|(n : ℝ)| / K) ∂ProbabilityTheory.poissonMeasure lam)
          = mgf (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure lam) θ := by
        rw [mgf]
        congr with n
        dsimp [θ]
        rw [abs_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
        ring_nf
      _ = Real.exp ((Real.exp θ - 1) * (lam : ℝ)) :=
        mgf_coe_nat_poissonMeasure_eq lam θ
  have hlog : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hexp_sub : Real.exp θ - 1 ≤ 2 * θ := by
    have hlocal :
        Real.exp θ - 1 ≤ θ + θ ^ 2 :=
      exp_sub_one_le_self_add_sq_of_mem_Icc
        (show θ ∈ Set.Icc (0 : ℝ) 1 from ⟨hθ_nonneg, hθ_le_one⟩)
    have hsq_le : θ ^ 2 ≤ θ := by nlinarith [hθ_nonneg, hθ_le_one]
    linarith
  have hcoef :
      (Real.exp θ - 1) * (lam : ℝ) ≤ Real.log 2 := by
    have hmul :=
      mul_le_mul_of_nonneg_right hexp_sub (NNReal.coe_nonneg lam)
    have hscale :
        (2 * θ) * (lam : ℝ) ≤ Real.log 2 := by
      have htarget :
          2 * (lam : ℝ) ≤ Real.log 2 * K := by
        dsimp [K, poissonSubExponentialScale]
        field_simp [hlog.ne']
        nlinarith [hlog, NNReal.coe_nonneg lam]
      calc
        (2 * θ) * (lam : ℝ) = (2 * (lam : ℝ)) / K := by
          dsimp [θ]
          ring
        _ ≤ Real.log 2 := by
          rw [div_le_iff₀ hKpos]
          exact htarget
    exact hmul.trans hscale
  refine ⟨hKpos, hInt, ?_⟩
  rw [hmgf_eq]
  calc
    Real.exp ((Real.exp θ - 1) * (lam : ℝ))
        ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hcoef
    _ = 2 := Real.exp_log (by norm_num : (0 : ℝ) < 2)

/-- Example 2.7.8(d), norm form for Poisson random variables. -/
theorem poisson_subExponentialNorm_le (lam : ℝ≥0) :
    subExponentialNorm (fun n : ℕ => (n : ℝ))
      (ProbabilityTheory.poissonMeasure lam) ≤ poissonSubExponentialScale lam :=
  subExponentialNorm_le_of_subExponentialOrliczCondition
    (poisson_subExponentialOrliczCondition lam)

end Examples

section OrliczSpaces

/-- HDP Section 2.7.1: an Orlicz function, recorded with the basic structural
properties needed for Luxemburg gauges on real random variables. -/
structure OrliczFunction where
  toFun : ℝ → ℝ
  map_zero : toFun 0 = 0
  nonneg : ∀ x, 0 ≤ toFun x
  mono_nonneg : ∀ {x y}, 0 ≤ x → x ≤ y → toFun x ≤ toFun y
  positive_of_pos : ∀ {x}, 0 < x → 0 < toFun x
  convexOn_nonneg : ConvexOn ℝ (Set.Ici 0) toFun
  tendsto_atTop : Tendsto toFun atTop atTop
  measurable : Measurable toFun

instance : CoeFun OrliczFunction (fun _ => ℝ → ℝ) where
  coe Φ := Φ.toFun

@[simp] theorem OrliczFunction.zero (Φ : OrliczFunction) : Φ 0 = 0 :=
  Φ.map_zero

theorem OrliczFunction.apply_nonneg (Φ : OrliczFunction) (x : ℝ) :
    0 ≤ Φ x :=
  Φ.nonneg x

/-- Luxemburg admissibility at scale `K`: `E Φ(|X|/K) ≤ 1`. -/
def orliczLuxemburgCondition
    (Φ : OrliczFunction) (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧ AEMeasurable X μ ∧
    Integrable (fun ω => Φ (|X ω| / K)) μ ∧
    ∫ ω, Φ (|X ω| / K) ∂μ ≤ 1

/-- HDP Section 2.7.1: the Luxemburg-Orlicz norm/gauge generated by `Φ`. -/
def orliczNorm (Φ : OrliczFunction) (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | orliczLuxemburgCondition Φ X μ K}

/-- The Orlicz space associated to `Φ`: random variables with a finite
admissible Luxemburg scale. -/
def OrliczSpace (Φ : OrliczFunction) (μ : Measure Ω) : Set (Ω → ℝ) :=
  {X | ∃ K, orliczLuxemburgCondition Φ X μ K}

theorem orliczLuxemburgCondition_zero
    [IsProbabilityMeasure μ] (Φ : OrliczFunction) {K : ℝ} (hK : 0 < K) :
    orliczLuxemburgCondition Φ (fun _ω : Ω => (0 : ℝ)) μ K := by
  refine ⟨hK, by fun_prop, ?_, ?_⟩
  · simp
  simp

theorem orliczNorm_le_of_orliczLuxemburgCondition
    {Φ : OrliczFunction} {X : Ω → ℝ} {K : ℝ}
    (hX : orliczLuxemburgCondition Φ X μ K) :
    orliczNorm Φ X μ ≤ K := by
  unfold orliczNorm
  exact csInf_le
    ⟨0, fun L hL => hL.1.le⟩
    hX

theorem orliczNorm_nonneg
    (Φ : OrliczFunction) (X : Ω → ℝ) (μ : Measure Ω) :
    0 ≤ orliczNorm Φ X μ := by
  unfold orliczNorm
  by_cases hne :
      ({K : ℝ | orliczLuxemburgCondition Φ X μ K}).Nonempty
  · exact le_csInf hne fun K hK => hK.1.le
  · have hempty :
        {K : ℝ | orliczLuxemburgCondition Φ X μ K} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

theorem orliczNorm_zero
    [IsProbabilityMeasure μ] (Φ : OrliczFunction) :
    orliczNorm Φ (fun _ω : Ω => (0 : ℝ)) μ = 0 := by
  refine le_antisymm ?_ (orliczNorm_nonneg Φ _ μ)
  exact le_of_forall_gt_imp_ge_of_dense fun ε hε =>
    orliczNorm_le_of_orliczLuxemburgCondition
      (μ := μ) (Φ := Φ) (X := fun _ω : Ω => (0 : ℝ)) (K := ε)
      (orliczLuxemburgCondition_zero (μ := μ) Φ (K := ε) hε)

theorem orliczLuxemburgCondition_mono_scale
    {Φ : OrliczFunction} {X : Ω → ℝ} {K L : ℝ}
    (hX : orliczLuxemburgCondition Φ X μ K)
    (hKL : K ≤ L) :
    orliczLuxemburgCondition Φ X μ L := by
  rcases hX with ⟨hKpos, hXm, hInt, hBound⟩
  have hLpos : 0 < L := hKpos.trans_le hKL
  have hrecip : 1 / L ≤ 1 / K :=
    (one_div_le_one_div hLpos hKpos).mpr hKL
  have hpoint :
      ∀ ω, Φ (|X ω| / L) ≤ Φ (|X ω| / K) := by
    intro ω
    refine Φ.mono_nonneg ?_ ?_
    · exact div_nonneg (abs_nonneg _) hLpos.le
    · calc
        |X ω| / L = |X ω| * (1 / L) := by ring
        _ ≤ |X ω| * (1 / K) :=
          mul_le_mul_of_nonneg_left hrecip (abs_nonneg _)
        _ = |X ω| / K := by ring
  have hsmall_aem :
      AEMeasurable (fun ω => Φ (|X ω| / L)) μ := by
    exact Φ.measurable.comp_aemeasurable (hXm.abs.div_const L)
  have hIntL :
      Integrable (fun ω => Φ (|X ω| / L)) μ := by
    refine hInt.mono hsmall_aem.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (Φ.nonneg _)]
        using hpoint ω
  refine ⟨hLpos, hXm, hIntL, ?_⟩
  calc
    ∫ ω, Φ (|X ω| / L) ∂μ
        ≤ ∫ ω, Φ (|X ω| / K) ∂μ :=
      integral_mono hIntL hInt hpoint
    _ ≤ 1 := hBound

/-- Multiplying by a nonzero scalar multiplies every generic Orlicz admissible
scale by `|a|`. -/
theorem orliczLuxemburgCondition_const_mul
    {Φ : OrliczFunction} {X : Ω → ℝ} {K a : ℝ}
    (ha : a ≠ 0)
    (hX : orliczLuxemburgCondition Φ X μ K) :
    orliczLuxemburgCondition Φ (fun ω => a * X ω) μ (|a| * K) := by
  rcases hX with ⟨hKpos, hXm, hInt, hBound⟩
  have hscale_pos : 0 < |a| * K :=
    mul_pos (abs_pos.mpr ha) hKpos
  have hEq :
      (fun ω => Φ (|a * X ω| / (|a| * K)))
        = fun ω => Φ (|X ω| / K) := by
    funext ω
    congr 1
    rw [abs_mul]
    field_simp [(abs_pos.mpr ha).ne', hKpos.ne']
  refine ⟨hscale_pos, ?_, ?_, ?_⟩
  · exact hXm.const_mul a
  · rw [hEq]
    exact hInt
  · rw [hEq]
    exact hBound

theorem orliczNorm_const_mul_le
    [IsProbabilityMeasure μ] {Φ : OrliczFunction} {X : Ω → ℝ} {K a : ℝ}
    (hX : orliczLuxemburgCondition Φ X μ K) :
    orliczNorm Φ (fun ω => a * X ω) μ ≤ |a| * K := by
  by_cases ha : a = 0
  · have hzero :
        (fun ω => a * X ω) = fun _ω : Ω => (0 : ℝ) := by
      funext ω
      simp [ha]
    rw [hzero, orliczNorm_zero]
    simp [ha]
  · exact
      orliczNorm_le_of_orliczLuxemburgCondition
        (orliczLuxemburgCondition_const_mul (μ := μ) (Φ := Φ) (X := X) (K := K)
          (a := a) ha hX)

/-- Pointwise convexity estimate behind the Luxemburg triangle inequality for
an arbitrary Orlicz function. -/
theorem orlicz_add_div_le_weighted
    (Φ : OrliczFunction) {x y K L : ℝ}
    (hK : 0 < K) (hL : 0 < L) :
    Φ (|x + y| / (K + L))
      ≤ K / (K + L) * Φ (|x| / K)
        + L / (K + L) * Φ (|y| / L) := by
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
  have hlin :
      |x + y| / (K + L) ≤ a * u + b * v := by
    calc
      |x + y| / (K + L) ≤ (|x| + |y|) / (K + L) := by
        exact div_le_div_of_nonneg_right (abs_add_le x y) hKL.le
      _ = a * u + b * v := by
        dsimp [a, b, u, v]
        field_simp [hK.ne', hL.ne', hKL.ne']
  have hlhs_nonneg : 0 ≤ |x + y| / (K + L) :=
    div_nonneg (abs_nonneg _) hKL.le
  have hmono :
      Φ (|x + y| / (K + L)) ≤ Φ (a * u + b * v) :=
    Φ.mono_nonneg hlhs_nonneg hlin
  have hconv :
      Φ (a * u + b * v) ≤ a * Φ u + b * Φ v := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (Φ.convexOn_nonneg.2 (show u ∈ Set.Ici (0 : ℝ) from hu_nonneg)
        (show v ∈ Set.Ici (0 : ℝ) from hv_nonneg) ha_nonneg hb_nonneg hab)
  exact hmono.trans (by simpa [a, b, u, v] using hconv)

theorem orliczLuxemburgCondition_add
    {Φ : OrliczFunction} {X Y : Ω → ℝ} {K L : ℝ}
    (hX : orliczLuxemburgCondition Φ X μ K)
    (hY : orliczLuxemburgCondition Φ Y μ L) :
    orliczLuxemburgCondition Φ (fun ω => X ω + Y ω) μ (K + L) := by
  rcases hX with ⟨hKpos, hXm, hXInt, hXBound⟩
  rcases hY with ⟨hLpos, hYm, hYInt, hYBound⟩
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
  let F : Ω → ℝ := fun ω => Φ (|X ω + Y ω| / (K + L))
  let G : Ω → ℝ :=
    fun ω => a * Φ (|X ω| / K) + b * Φ (|Y ω| / L)
  have hpoint : ∀ ω, F ω ≤ G ω := by
    intro ω
    dsimp [F, G, a, b]
    exact orlicz_add_div_le_weighted Φ hKpos hLpos
  have hGInt : Integrable G μ := by
    dsimp [G]
    exact (hXInt.const_mul a).add (hYInt.const_mul b)
  have hFaem : AEMeasurable F μ := by
    dsimp [F]
    exact Φ.measurable.comp_aemeasurable ((hXm.add hYm).abs.div_const (K + L))
  have hFInt : Integrable F μ := by
    refine hGInt.mono_nonneg hFaem.aestronglyMeasurable ?_ ?_
    · exact Filter.Eventually.of_forall fun ω => by
        dsimp [F]
        exact Φ.nonneg _
    · exact Filter.Eventually.of_forall hpoint
  refine ⟨hKL, hXm.add hYm, hFInt, ?_⟩
  calc
    ∫ ω, Φ (|X ω + Y ω| / (K + L)) ∂μ
        = ∫ ω, F ω ∂μ := rfl
    _ ≤ ∫ ω, G ω ∂μ :=
      integral_mono hFInt hGInt hpoint
    _ = a * ∫ ω, Φ (|X ω| / K) ∂μ
        + b * ∫ ω, Φ (|Y ω| / L) ∂μ := by
      dsimp [G]
      rw [integral_add (hXInt.const_mul a) (hYInt.const_mul b),
        integral_const_mul, integral_const_mul]
    _ ≤ a * 1 + b * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hXBound ha_nonneg)
        (mul_le_mul_of_nonneg_left hYBound hb_nonneg)
    _ = 1 := by
      rw [← add_mul, hab]
      ring

theorem orliczNorm_add_le_of_orliczLuxemburgCondition
    {Φ : OrliczFunction} {X Y : Ω → ℝ} {K L : ℝ}
    (hX : orliczLuxemburgCondition Φ X μ K)
    (hY : orliczLuxemburgCondition Φ Y μ L) :
    orliczNorm Φ (fun ω => X ω + Y ω) μ ≤ K + L :=
  orliczNorm_le_of_orliczLuxemburgCondition
    (orliczLuxemburgCondition_add hX hY)

theorem orliczNorm_add_le
    {Φ : OrliczFunction} {X Y : Ω → ℝ}
    (hX : X ∈ OrliczSpace Φ μ) (hY : Y ∈ OrliczSpace Φ μ) :
    orliczNorm Φ (fun ω => X ω + Y ω) μ
      ≤ orliczNorm Φ X μ + orliczNorm Φ Y μ := by
  rcases hX with ⟨K0, hK0⟩
  rcases hY with ⟨L0, hL0⟩
  have hXset :
      ({K : ℝ | orliczLuxemburgCondition Φ X μ K}).Nonempty := ⟨K0, hK0⟩
  have hYset :
      ({L : ℝ | orliczLuxemburgCondition Φ Y μ L}).Nonempty := ⟨L0, hL0⟩
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro r hr
  have hgap : 0 < r - (orliczNorm Φ X μ + orliczNorm Φ Y μ) := by
    linarith
  have hhalf : 0 < (r - (orliczNorm Φ X μ + orliczNorm Φ Y μ)) / 2 := by
    positivity
  obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos hXset hhalf
  obtain ⟨L, hL, hLlt⟩ := Real.lt_sInf_add_pos hYset hhalf
  have hKlt' :
      K < orliczNorm Φ X μ
        + (r - (orliczNorm Φ X μ + orliczNorm Φ Y μ)) / 2 := by
    simpa [orliczNorm] using hKlt
  have hLlt' :
      L < orliczNorm Φ Y μ
        + (r - (orliczNorm Φ X μ + orliczNorm Φ Y μ)) / 2 := by
    simpa [orliczNorm] using hLlt
  have hadd :
      orliczNorm Φ (fun ω => X ω + Y ω) μ ≤ K + L :=
    orliczNorm_add_le_of_orliczLuxemburgCondition hK hL
  have hsum_lt : K + L < r := by
    linarith
  exact hadd.trans hsum_lt.le

theorem orliczNorm_const_mul_eq
    [IsProbabilityMeasure μ]
    {Φ : OrliczFunction} {X : Ω → ℝ}
    (hX : X ∈ OrliczSpace Φ μ) (a : ℝ) :
    orliczNorm Φ (fun ω => a * X ω) μ = |a| * orliczNorm Φ X μ := by
  by_cases ha : a = 0
  · have hzero :
        (fun ω => a * X ω) = fun _ω : Ω => (0 : ℝ) := by
      funext ω
      simp [ha]
    simp [ha, orliczNorm_zero]
  · refine le_antisymm ?_ ?_
    · rcases hX with ⟨K0, hK0⟩
      have hXset :
          ({K : ℝ | orliczLuxemburgCondition Φ X μ K}).Nonempty := ⟨K0, hK0⟩
      refine le_of_forall_gt_imp_ge_of_dense ?_
      intro r hr
      have hgap : 0 < r - |a| * orliczNorm Φ X μ := by
        linarith
      have hgap' : 0 < (r - |a| * orliczNorm Φ X μ) / |a| := by
        positivity
      obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos hXset hgap'
      have hKlt' :
          K < orliczNorm Φ X μ + (r - |a| * orliczNorm Φ X μ) / |a| := by
        simpa [orliczNorm] using hKlt
      have hle :
          orliczNorm Φ (fun ω => a * X ω) μ ≤ |a| * K :=
        orliczNorm_const_mul_le (μ := μ) (Φ := Φ) (X := X) (K := K) (a := a) hK
      have hlt : |a| * K < r := by
        have habs : 0 < |a| := abs_pos.mpr ha
        have hmul := mul_lt_mul_of_pos_left hKlt' habs
        have htarget :
            |a| * (orliczNorm Φ X μ
              + (r - |a| * orliczNorm Φ X μ) / |a|) = r := by
          field_simp [habs.ne']
          ring
        nlinarith
      exact hle.trans hlt.le
    · have hinv_space :
          (fun ω => a * X ω) ∈ OrliczSpace Φ μ := by
        rcases hX with ⟨K, hK⟩
        exact ⟨|a| * K, orliczLuxemburgCondition_const_mul
          (μ := μ) (Φ := Φ) (X := X) (K := K) (a := a) ha hK⟩
      have heq :
          (fun ω => a⁻¹ * (a * X ω)) = X := by
        funext ω
        field_simp [ha]
      have hle_inv :
          orliczNorm Φ (fun ω => a⁻¹ * (a * X ω)) μ
            ≤ |a⁻¹| * orliczNorm Φ (fun ω => a * X ω) μ := by
        rcases hinv_space with ⟨K0, hK0⟩
        have hZset :
            ({K : ℝ |
              orliczLuxemburgCondition Φ (fun ω => a * X ω) μ K}).Nonempty :=
          ⟨K0, hK0⟩
        refine le_of_forall_gt_imp_ge_of_dense ?_
        intro r hr
        have hgap :
            0 < r - |a⁻¹| * orliczNorm Φ (fun ω => a * X ω) μ := by
          linarith
        have hinv_ne : a⁻¹ ≠ 0 := inv_ne_zero ha
        have habs_inv_pos : 0 < |a⁻¹| := abs_pos.mpr hinv_ne
        have hgap' :
            0 < (r - |a⁻¹| * orliczNorm Φ (fun ω => a * X ω) μ) / |a⁻¹| := by
          positivity
        obtain ⟨K, hK, hKlt⟩ := Real.lt_sInf_add_pos hZset hgap'
        have hKlt' :
            K < orliczNorm Φ (fun ω => a * X ω) μ
              + (r - |a⁻¹| * orliczNorm Φ (fun ω => a * X ω) μ) / |a⁻¹| := by
          simpa [orliczNorm] using hKlt
        have hle :
            orliczNorm Φ (fun ω => a⁻¹ * (a * X ω)) μ ≤ |a⁻¹| * K :=
          orliczNorm_const_mul_le
            (μ := μ) (Φ := Φ) (X := fun ω => a * X ω) (K := K) (a := a⁻¹) hK
        have hlt : |a⁻¹| * K < r := by
          have hmul := mul_lt_mul_of_pos_left hKlt' habs_inv_pos
          have htarget :
              |a⁻¹| * (orliczNorm Φ (fun ω => a * X ω) μ
                + (r - |a⁻¹| * orliczNorm Φ (fun ω => a * X ω) μ) / |a⁻¹|) = r := by
            field_simp [habs_inv_pos.ne']
            ring
          nlinarith
        exact hle.trans hlt.le
      rw [heq] at hle_inv
      have habs_pos : 0 < |a| := abs_pos.mpr ha
      have hinv_abs : |a⁻¹| = |a|⁻¹ := abs_inv a
      rw [hinv_abs] at hle_inv
      have hmul := mul_le_mul_of_nonneg_left hle_inv habs_pos.le
      have hcancel :
          |a| * (|a|⁻¹ * orliczNorm Φ (fun ω => a * X ω) μ)
            = orliczNorm Φ (fun ω => a * X ω) μ := by
        field_simp [habs_pos.ne']
      simpa [mul_assoc, hcancel] using hmul

/-- Generic Orlicz tail bound from an admissible Luxemburg scale. -/
theorem orliczLuxemburgCondition_tail_le
    [IsProbabilityMeasure μ]
    {Φ : OrliczFunction} {X : Ω → ℝ} {K t : ℝ}
    (hX : orliczLuxemburgCondition Φ X μ K) (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} ≤ 1 / Φ (t / K) := by
  rcases hX with ⟨hKpos, _hXm, hInt, hBound⟩
  let Y : Ω → ℝ := fun ω => Φ (|X ω| / K)
  have hY_nonneg : 0 ≤ᵐ[μ] Y :=
    Filter.Eventually.of_forall fun _ => Φ.nonneg _
  have hthreshold_pos : 0 < Φ (t / K) :=
    Φ.positive_of_pos (div_pos ht hKpos)
  have hsubset :
      {ω | t ≤ |X ω|} ⊆ {ω | Φ (t / K) ≤ Y ω} := by
    intro ω hω
    change Φ (t / K) ≤ Φ (|X ω| / K)
    refine Φ.mono_nonneg (div_nonneg ht.le hKpos.le) ?_
    exact div_le_div_of_nonneg_right hω hKpos.le
  have hmarkov :=
    markov_inequality
      (μ := μ) (X := Y) hY_nonneg hInt
      (t := Φ (t / K)) hthreshold_pos
  calc
    μ.real {ω | t ≤ |X ω|}
        ≤ μ.real {ω | Φ (t / K) ≤ Y ω} :=
      MeasureTheory.measureReal_mono hsubset
    _ ≤ (∫ ω, Y ω ∂μ) / Φ (t / K) := hmarkov
    _ ≤ 1 / Φ (t / K) :=
      div_le_div_of_nonneg_right hBound hthreshold_pos.le

/-- If the generic Orlicz gauge is zero, every positive Luxemburg scale is
admissible. -/
theorem orliczLuxemburgCondition_of_orliczNorm_eq_zero
    {Φ : OrliczFunction} {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (hX : X ∈ OrliczSpace Φ μ)
    (hnorm : orliczNorm Φ X μ = 0)
    (hK : 0 < K) :
    orliczLuxemburgCondition Φ X μ K := by
  rcases hX with ⟨K0, hK0⟩
  have hXset :
      ({L : ℝ | orliczLuxemburgCondition Φ X μ L}).Nonempty := ⟨K0, hK0⟩
  obtain ⟨L, hL, hLlt⟩ := Real.lt_sInf_add_pos hXset hK
  have hLltK : L < K := by
    have hsInf_zero :
        sInf {L : ℝ | orliczLuxemburgCondition Φ X μ L} = 0 := by
      simpa [orliczNorm] using hnorm
    simpa [hsInf_zero] using hLlt
  exact orliczLuxemburgCondition_mono_scale hL hLltK.le

/-- Positive tails of a zero generic Orlicz-gauge random variable have
probability zero. -/
theorem orliczNorm_eq_zero_tail_measureReal
    [IsProbabilityMeasure μ]
    {Φ : OrliczFunction} {X : Ω → ℝ} {t : ℝ}
    (hX : X ∈ OrliczSpace Φ μ)
    (hnorm : orliczNorm Φ X μ = 0)
    (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} = 0 := by
  let A : Set Ω := {ω | t ≤ |X ω|}
  refine le_antisymm ?_ measureReal_nonneg
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro ε hε
  obtain ⟨R0, hR0⟩ :=
    (tendsto_atTop_atTop.mp Φ.tendsto_atTop) (1 / ε)
  let R : ℝ := max R0 1
  have hRpos : 0 < R := by
    exact zero_lt_one.trans_le (le_max_right R0 1)
  have hRge : R0 ≤ R := le_max_left R0 1
  have hPhi_ge : 1 / ε ≤ Φ R := hR0 R hRge
  have hPhi_pos : 0 < Φ R := Φ.positive_of_pos hRpos
  let K : ℝ := t / R
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hcond : orliczLuxemburgCondition Φ X μ K :=
    orliczLuxemburgCondition_of_orliczNorm_eq_zero hX hnorm hKpos
  have htail :
      μ.real {ω | t ≤ |X ω|} ≤ 1 / Φ (t / K) :=
    orliczLuxemburgCondition_tail_le hcond ht
  have htK : t / K = R := by
    dsimp [K]
    field_simp [ht.ne', hRpos.ne']
  have hinv_le : 1 / Φ R ≤ ε := by
    have hone_le : 1 ≤ Φ R * ε := by
      have hmul := mul_le_mul_of_nonneg_right hPhi_ge hε.le
      have hε_mul_inv : ε * ε⁻¹ = 1 := by
        field_simp [hε.ne']
      simpa [one_div, hε_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    rw [div_le_iff₀ hPhi_pos]
    simpa [mul_comm] using hone_le
  calc
    μ.real A = μ.real {ω | t ≤ |X ω|} := rfl
    _ ≤ 1 / Φ (t / K) := htail
    _ = 1 / Φ R := by rw [htK]
    _ ≤ ε := hinv_le

/-- Zero generic Orlicz gauge forces the random variable to vanish almost
surely. -/
theorem ae_eq_zero_of_orliczNorm_eq_zero
    [IsProbabilityMeasure μ]
    {Φ : OrliczFunction} {X : Ω → ℝ}
    (hX : X ∈ OrliczSpace Φ μ)
    (hnorm : orliczNorm Φ X μ = 0) :
    X =ᵐ[μ] fun _ω => (0 : ℝ) := by
  rw [Filter.EventuallyEq, ae_iff]
  have htail_null :
      ∀ n : ℕ,
        μ {ω | (1 : ℝ) / ((n : ℝ) + 1) ≤ |X ω|} = 0 := by
    intro n
    have htpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    have htail_real :=
      orliczNorm_eq_zero_tail_measureReal
        (μ := μ) (Φ := Φ) (X := X) (t := (1 : ℝ) / ((n : ℝ) + 1))
        hX hnorm htpos
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

theorem orliczLuxemburgCondition_of_ae_eq_zero
    [IsProbabilityMeasure μ]
    {Φ : OrliczFunction} {X : Ω → ℝ} {K : ℝ}
    (hK : 0 < K)
    (hX0 : X =ᵐ[μ] fun _ω => (0 : ℝ)) :
    orliczLuxemburgCondition Φ X μ K := by
  have hXm : AEMeasurable X μ :=
    AEMeasurable.congr (aemeasurable_const (μ := μ) (b := (0 : ℝ))) hX0.symm
  have hPhiEq :
      (fun ω => Φ (|X ω| / K)) =ᵐ[μ] fun _ω => (0 : ℝ) := by
    filter_upwards [hX0] with ω hω
    simp [hω]
  have hInt :
      Integrable (fun ω => Φ (|X ω| / K)) μ :=
    (integrable_const (0 : ℝ)).congr hPhiEq.symm
  refine ⟨hK, hXm, hInt, ?_⟩
  calc
    ∫ ω, Φ (|X ω| / K) ∂μ
        = ∫ _ω : Ω, (0 : ℝ) ∂μ :=
      integral_congr_ae hPhiEq
    _ = 0 := by simp
    _ ≤ 1 := by norm_num

theorem orliczNorm_eq_zero_of_ae_eq_zero
    [IsProbabilityMeasure μ]
    {Φ : OrliczFunction} {X : Ω → ℝ}
    (hX0 : X =ᵐ[μ] fun _ω => (0 : ℝ)) :
    orliczNorm Φ X μ = 0 := by
  refine le_antisymm ?_ (orliczNorm_nonneg Φ X μ)
  exact le_of_forall_gt_imp_ge_of_dense fun ε hε =>
    orliczNorm_le_of_orliczLuxemburgCondition
      (μ := μ) (Φ := Φ) (X := X) (K := ε)
      (orliczLuxemburgCondition_of_ae_eq_zero (μ := μ) (Φ := Φ) hε hX0)

theorem orliczNorm_eq_zero_iff_ae_eq_zero
    [IsProbabilityMeasure μ]
    {Φ : OrliczFunction} {X : Ω → ℝ}
    (hX : X ∈ OrliczSpace Φ μ) :
    orliczNorm Φ X μ = 0 ↔ X =ᵐ[μ] fun _ω => (0 : ℝ) :=
  ⟨ae_eq_zero_of_orliczNorm_eq_zero hX,
    orliczNorm_eq_zero_of_ae_eq_zero⟩

/-- HDP Exercise 2.7.11: the Luxemburg gauge has the norm algebraic laws on
the Orlicz space.  Positive definiteness is stated as the a.e. zero law for
raw random variables. -/
theorem exercise_2_7_11_orlicz_norm_axioms
    [IsProbabilityMeasure μ]
    (Φ : OrliczFunction) {X Y : Ω → ℝ}
    (hX : X ∈ OrliczSpace Φ μ) (hY : Y ∈ OrliczSpace Φ μ) :
    0 ≤ orliczNorm Φ X μ ∧
    orliczNorm Φ (fun _ω : Ω => (0 : ℝ)) μ = 0 ∧
    (orliczNorm Φ X μ = 0 ↔ X =ᵐ[μ] fun _ω => (0 : ℝ)) ∧
    (∀ a : ℝ, orliczNorm Φ (fun ω => a * X ω) μ =
      |a| * orliczNorm Φ X μ) ∧
    orliczNorm Φ (fun ω => X ω + Y ω) μ
      ≤ orliczNorm Φ X μ + orliczNorm Φ Y μ := by
  refine ⟨orliczNorm_nonneg Φ X μ, orliczNorm_zero Φ,
    orliczNorm_eq_zero_iff_ae_eq_zero hX, ?_, ?_⟩
  · intro a
    exact orliczNorm_const_mul_eq hX a
  · exact orliczNorm_add_le hX hY

/-- Example 2.7.12: the power Orlicz function `Φ(x)=|x|^p` for positive
integer `p`.  On nonnegative arguments this is the classical `x^p`. -/
def powerOrliczFunction (p : ℕ) (hp : 0 < p) : OrliczFunction where
  toFun x := |x| ^ p
  map_zero := by
    simp [Nat.pos_iff_ne_zero.mp hp]
  nonneg x := by
    positivity
  mono_nonneg := by
    intro x y hx hxy
    have hy : 0 ≤ y := hx.trans hxy
    simpa [abs_of_nonneg hx, abs_of_nonneg hy] using
      pow_le_pow_left₀ hx hxy p
  positive_of_pos := by
    intro x hx
    exact pow_pos (abs_pos.mpr hx.ne') p
  convexOn_nonneg := by
    exact (convexOn_pow p).congr fun x hx => by
      exact (abs_of_nonneg (show 0 ≤ x from hx)).symm ▸ rfl
  tendsto_atTop := by
    exact (tendsto_pow_atTop (Nat.pos_iff_ne_zero.mp hp)).congr' (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simp [abs_of_nonneg hx])
  measurable := by
    fun_prop

theorem powerOrliczFunction_apply_of_nonneg {p : ℕ} (hp : 0 < p)
    {x : ℝ} (hx : 0 ≤ x) :
    powerOrliczFunction p hp x = x ^ p := by
  simp [powerOrliczFunction, abs_of_nonneg hx]

/-- Example 2.7.13: the Orlicz function `Φ(x)=exp(x²)-1` underlying the
sub-gaussian `ψ₂` Luxemburg norm. -/
def subGaussianOrliczFunction : OrliczFunction where
  toFun x := Real.exp (x ^ 2) - 1
  map_zero := by norm_num
  nonneg x := by
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (sq_nonneg x))
  mono_nonneg := by
    intro x y hx hxy
    have hsq : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx (hx.trans hxy)).mpr hxy
    exact sub_le_sub_right (Real.exp_le_exp.mpr hsq) 1
  positive_of_pos := by
    intro x hx
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (sq_pos_of_ne_zero hx.ne'))
  convexOn_nonneg := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    have hquad :
        (a • x + b • y) ^ 2 ≤ a • x ^ 2 + b • y ^ 2 := by
      simpa [smul_eq_mul] using
        (convexOn_pow 2).2 hx hy ha hb hab
    have hconv :
        Real.exp (a • x ^ 2 + b • y ^ 2)
          ≤ a • Real.exp (x ^ 2) + b • Real.exp (y ^ 2) := by
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        (convexOn_exp.2 (Set.mem_univ (x ^ 2)) (Set.mem_univ (y ^ 2)) ha hb hab)
    calc
      Real.exp ((a • x + b • y) ^ 2) - 1
          ≤ Real.exp (a • x ^ 2 + b • y ^ 2) - 1 :=
        sub_le_sub_right (Real.exp_le_exp.mpr hquad) 1
      _ ≤ (a • Real.exp (x ^ 2) + b • Real.exp (y ^ 2)) - 1 :=
        sub_le_sub_right hconv 1
      _ = a • (Real.exp (x ^ 2) - 1) + b • (Real.exp (y ^ 2) - 1) := by
        rw [← hab]
        ring_nf
        nlinarith [hab]
  tendsto_atTop := by
    have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ)
        (Real.tendsto_exp_atTop.comp hsq))
  measurable := by
    fun_prop

theorem subGaussianOrliczFunction_condition_iff
    {X : Ω → ℝ} {K : ℝ} :
    orliczLuxemburgCondition subGaussianOrliczFunction X μ K ↔
      0 < K ∧ AEMeasurable X μ ∧
        Integrable (fun ω => Real.exp ((|X ω| / K) ^ 2) - 1) μ ∧
        ∫ ω, Real.exp ((|X ω| / K) ^ 2) - 1 ∂μ ≤ 1 := by
  rfl

end OrliczSpaces

section OrliczHierarchy

/-- HDP Remark 2.7.14, first inclusion: an essentially bounded random
variable belongs to the sub-gaussian Orlicz space `L_{ψ₂}`. -/
theorem linfty_subset_subGaussian
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {B : ℝ}
    (hXm : AEMeasurable X μ)
    (hB : 0 < B)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ B) :
    IsSubGaussian X μ :=
  isSubGaussian_of_subGaussianOrliczCondition
    (subGaussianOrliczCondition_of_ae_abs_le_scaled hXm hB hbound)

/-- HDP Remark 2.7.14, quantitative first inclusion: an essentially bounded
random variable has `ψ₂` norm controlled by its essential bound. -/
theorem subGaussianNorm_le_of_lininfty_bound
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {B : ℝ}
    (hXm : AEMeasurable X μ)
    (hB : 0 < B)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ B) :
    subGaussianNorm X μ ≤ B / Real.sqrt (Real.log 2) :=
  subGaussianNorm_le_of_ae_abs_le_scaled hXm hB hbound

/-- HDP Remark 2.7.14, second inclusion: every sub-gaussian random variable
belongs to every finite `L^p`, `p ≥ 1`. -/
theorem subGaussian_memLp
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℝ≥0}
    (hXm : AEStronglyMeasurable X μ)
    (hX : IsSubGaussian X μ)
    (hp : 1 ≤ (p : ℝ)) :
    MemLp X (p : ℝ≥0∞) μ := by
  rcases hX with ⟨K, hK⟩
  have hMom : subGaussianMomentCondition X μ (2 * K) :=
    subGaussianMomentCondition_of_subGaussianOrliczCondition
      (μ := μ) (X := X) (K := K) hXm hK
  exact (hMom.2 p hp).1

/-- HDP Remark 2.7.14, quantitative second inclusion at a concrete Orlicz
scale: `‖X‖_{L^p} ≤ 2 K sqrt p` for every finite `p ≥ 1`. -/
theorem subGaussian_eLpNorm_le_of_orliczCondition
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ} {p : ℝ≥0}
    (hXm : AEStronglyMeasurable X μ)
    (hX : subGaussianOrliczCondition X μ K)
    (hp : 1 ≤ (p : ℝ)) :
    eLpNorm X (p : ℝ≥0∞) μ ≤
      ENNReal.ofReal (2 * K * Real.sqrt (p : ℝ)) := by
  have hMom : subGaussianMomentCondition X μ (2 * K) :=
    subGaussianMomentCondition_of_subGaussianOrliczCondition
      (μ := μ) (X := X) (K := K) hXm hX
  simpa [mul_assoc] using (hMom.2 p hp).2

end OrliczHierarchy

end LeanFpAnalysis.HDP
