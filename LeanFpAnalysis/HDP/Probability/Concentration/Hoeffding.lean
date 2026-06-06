import LeanFpAnalysis.HDP.Probability.Concentration.Basic

/-!
# Hoeffding Inequalities

Book-facing forms of HDP Chapter 2, Section 2.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace LeanFpAnalysis.HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section RademacherHoeffding

variable [IsProbabilityMeasure μ]
variable {ι : Type*}
variable {X : ι → Ω → ℝ} {a : ι → ℝ}

/-- Weighted Rademacher summands are independent sub-Gaussian variables with
variance proxy `a_i^2`. -/
lemma weighted_rademacher_subgaussian
    (hX : ∀ i, IsSymmetricBernoulli (X i) μ) (i : ι) :
    HasSubgaussianMGF (fun ω => a i * X i ω) ⟨a i ^ 2, sq_nonneg (a i)⟩ μ := by
  have h := (hasSubgaussianMGF_of_isSymmetricBernoulli (μ := μ) (hX i)).const_mul (a i)
  simpa using h

variable [Fintype ι]

/-- HDP Theorem 2.2.2, Hoeffding's inequality for weighted sums of independent
symmetric Bernoulli random variables. The coordinate form `coeffL2NormSq a`
is `‖a‖₂²`. -/
theorem hoeffding_rademacher_weighted
    (hindep : iIndepFun X μ)
    (hX : ∀ i, IsSymmetricBernoulli (X i) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i, a i * X i ω}
      ≤ Real.exp (-(t ^ 2) / (2 * coeffL2NormSq a)) := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  let c : ι → ℝ≥0 := fun i => ⟨a i ^ 2, sq_nonneg (a i)⟩
  have hYindep : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hindep.comp (fun i x => a i * x) (fun _ => by fun_prop)
  have hsubG : ∀ i ∈ (Finset.univ : Finset ι), HasSubgaussianMGF (Y i) (c i) μ := by
    intro i _
    simpa [Y, c] using weighted_rademacher_subgaussian (μ := μ) (X := X) (a := a) hX i
  have h :=
    ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := μ) (X := Y) hYindep (c := c) (s := (Finset.univ : Finset ι))
      hsubG ht
  simpa [Y, c, coeffL2NormSq] using h

/-- HDP Theorem 2.2.5, two-sided Hoeffding inequality for weighted sums of
independent symmetric Bernoulli random variables. -/
theorem hoeffding_rademacher_weighted_two_sided
    (hindep : iIndepFun X μ)
    (hX : ∀ i, IsSymmetricBernoulli (X i) μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-(t ^ 2) / (2 * coeffL2NormSq a)) := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i, a i * X i ω
  let A : Set Ω := {ω | t ≤ S ω}
  let B : Set Ω := {ω | t ≤ -S ω}
  have hsubset : {ω | t ≤ |S ω|} ⊆ A ∪ B := by
    intro ω hω
    by_cases hS : 0 ≤ S ω
    · exact Or.inl (by simpa [A, S, abs_of_nonneg hS] using hω)
    · have hSneg : S ω < 0 := lt_of_not_ge hS
      exact Or.inr (by simpa [B, S, abs_of_neg hSneg] using hω)
  have hone :=
    hoeffding_rademacher_weighted (μ := μ) (X := X) (a := a)
      hindep hX ht.le
  have hneg :=
    hoeffding_rademacher_weighted (μ := μ) (X := X) (a := fun i => -a i)
      hindep hX ht.le
  have hB :
      μ.real B ≤ Real.exp (-(t ^ 2) / (2 * coeffL2NormSq a)) := by
    simpa [B, S, coeffL2NormSq, neg_mul, Finset.sum_neg_distrib] using hneg
  calc
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
        = μ.real {ω | t ≤ |S ω|} := by simp [S]
    _ ≤ μ.real (A ∪ B) := measureReal_mono hsubset
    _ ≤ μ.real A + μ.real B := measureReal_union_le A B
    _ ≤ Real.exp (-(t ^ 2) / (2 * coeffL2NormSq a))
        + Real.exp (-(t ^ 2) / (2 * coeffL2NormSq a)) := by
          exact add_le_add (by simpa [A, S] using hone) hB
    _ = 2 * Real.exp (-(t ^ 2) / (2 * coeffL2NormSq a)) := by ring

end RademacherHoeffding

section BoundedHoeffding

variable [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι]
variable {X : ι → Ω → ℝ} {m M : ι → ℝ}

/-- Sum of squared interval lengths, the denominator in the bounded-variable
Hoeffding inequality. -/
def boundedRangeSqSum (m M : ι → ℝ) : ℝ :=
  ∑ i, (M i - m i) ^ 2

@[simp]
lemma boundedRangeSqSum_def (m M : ι → ℝ) :
    boundedRangeSqSum m M = ∑ i, (M i - m i) ^ 2 := rfl

/-- HDP Theorem 2.2.6, Hoeffding's inequality for independent bounded random
variables. -/
theorem hoeffding_bounded
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (m i) (M i))
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ∑ i, (X i ω - μ[X i])}
      ≤ Real.exp (-(2 * t ^ 2) / boundedRangeSqSum m M) := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => X i ω - μ[X i]
  let c : ι → ℝ≥0 := fun i => ((‖M i - m i‖₊ / 2) ^ 2)
  have hYindep : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hindep.comp (fun i x => x - μ[X i]) (fun _ => by fun_prop)
  have hsubG : ∀ i ∈ (Finset.univ : Finset ι), HasSubgaussianMGF (Y i) (c i) μ := by
    intro i _
    simpa [Y, c] using
      ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
        (μ := μ) (X := X i) (a := m i) (b := M i)
        (hXm i) (hbdd i)
  have h :=
    ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := μ) (X := Y) hYindep (c := c) (s := (Finset.univ : Finset ι))
      hsubG ht.le
  have hsumc :
      ((∑ i, c i : ℝ≥0) : ℝ) = boundedRangeSqSum m M / 4 := by
    simp [c, boundedRangeSqSum, div_pow]
    norm_num
    rw [Finset.sum_div]
  calc
    μ.real {ω | t ≤ ∑ i, (X i ω - μ[X i])}
        = μ.real {ω | t ≤ ∑ i, Y i ω} := by simp [Y]
    _ ≤ Real.exp (-(t ^ 2) / (2 * (∑ i, c i : ℝ≥0))) := by
          simpa using h
    _ = Real.exp (-(2 * t ^ 2) / boundedRangeSqSum m M) := by
      congr 1
      rw [hsumc]
      ring

end BoundedHoeffding

end LeanFpAnalysis.HDP
