import LeanFpAnalysis.HDP.Probability.LimitTheorems
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Concentration: Basic Distributions and MGF Lemmas

Reusable definitions and numerical lemmas for HDP Chapter 2, Sections 2.1-2.3.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace LeanFpAnalysis.HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section FiniteL2

/-- Squared Euclidean norm of a finite coefficient vector, written in coordinates.
This is the denominator `‖a‖₂²` in the book's concentration bounds. -/
def coeffL2NormSq {ι : Type*} [Fintype ι] (a : ι → ℝ) : ℝ :=
  ∑ i, a i ^ 2

/-- Euclidean norm of a finite coefficient vector, written in coordinates. -/
def coeffL2Norm {ι : Type*} [Fintype ι] (a : ι → ℝ) : ℝ :=
  Real.sqrt (coeffL2NormSq a)

@[simp]
lemma coeffL2NormSq_def {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    coeffL2NormSq a = ∑ i, a i ^ 2 := rfl

lemma coeffL2NormSq_nonneg {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    0 ≤ coeffL2NormSq a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma coeffL2Norm_sq {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    coeffL2Norm a ^ 2 = coeffL2NormSq a :=
  Real.sq_sqrt (coeffL2NormSq_nonneg a)

end FiniteL2

section Rademacher

/-- Symmetric Bernoulli/Rademacher distribution on `ℝ`: mass `1/2` at `-1`
and mass `1/2` at `1`. -/
def rademacherPMF : PMF ℝ :=
  (PMF.bernoulli (1 / 2 : ℝ≥0) (by norm_num)).map fun b : Bool =>
    if b then (1 : ℝ) else -1

/-- Symmetric Bernoulli/Rademacher probability measure on `ℝ`. -/
def rademacherMeasure : ProbabilityMeasure ℝ :=
  ⟨rademacherPMF.toMeasure, inferInstance⟩

/-- A real random variable with the symmetric Bernoulli/Rademacher law. -/
def IsSymmetricBernoulli (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  HasLaw X rademacherPMF.toMeasure μ

/-- A `{0,1}`-valued Bernoulli random variable with success probability `1/2`. -/
def IsBernoulliHalf (X : Ω → ℕ) (μ : Measure Ω) : Prop :=
  HasLaw X ((bernoulliNatPMF (1 / 2 : ℝ≥0) (by norm_num)).toMeasure) μ

@[simp]
lemma rademacherPMF_apply_one :
    rademacherPMF 1 = (1 / 2 : ℝ≥0) := by
  simp [rademacherPMF, PMF.map_apply, PMF.bernoulli_apply]
  norm_num

@[simp]
lemma rademacherPMF_apply_neg_one :
    rademacherPMF (-1) = (1 / 2 : ℝ≥0) := by
  simp [rademacherPMF, PMF.map_apply, PMF.bernoulli_apply]
  norm_num

lemma rademacherPMF_apply_of_ne {x : ℝ} (hx1 : x ≠ 1) (hxn1 : x ≠ -1) :
    rademacherPMF x = 0 := by
  simp [rademacherPMF, PMF.map_apply, PMF.bernoulli_apply, hx1, hxn1]

lemma bernoulliHalf_map_two_mul_sub_one_eq_rademacherPMF :
    (bernoulliNatPMF (1 / 2 : ℝ≥0) (by norm_num)).map
        (fun n : ℕ => 2 * (n : ℝ) - 1) = rademacherPMF := by
  apply PMF.ext
  intro x
  rw [PMF.map_apply]
  by_cases hx1 : x = 1
  · subst x
    have hpre :
        (fun n : ℕ => if (1 : ℝ) = 2 * (n : ℝ) - 1
            then bernoulliNatPMF (1 / 2 : ℝ≥0) (by norm_num) n else 0)
          =
        fun n : ℕ => if n = 1
            then bernoulliNatPMF (1 / 2 : ℝ≥0) (by norm_num) n else 0 := by
      funext n
      have hiff : (1 : ℝ) = 2 * (n : ℝ) - 1 ↔ n = 1 := by
        constructor
        · intro hn
          have hnr : (n : ℝ) = 1 := by linarith
          exact_mod_cast hnr
        · intro hn
          subst hn
          norm_num
      by_cases hn : n = 1
      · subst hn
        norm_num
      · have hn' : ¬ (1 : ℝ) = 2 * (n : ℝ) - 1 := fun h => hn (hiff.mp h)
        simp [hn, hn']
    rw [hpre, tsum_ite_eq 1]
    simp
  · by_cases hxn1 : x = -1
    · subst x
      have hpre :
          (fun n : ℕ => if (-1 : ℝ) = 2 * (n : ℝ) - 1
              then bernoulliNatPMF (1 / 2 : ℝ≥0) (by norm_num) n else 0)
            =
          fun n : ℕ => if n = 0
              then bernoulliNatPMF (1 / 2 : ℝ≥0) (by norm_num) n else 0 := by
        funext n
        have hiff : (-1 : ℝ) = 2 * (n : ℝ) - 1 ↔ n = 0 := by
          constructor
          · intro hn
            have hnr : (n : ℝ) = 0 := by linarith
            exact_mod_cast hnr
          · intro hn
            subst hn
            norm_num
        by_cases hn : n = 0
        · subst hn
          norm_num
        · have hn' : ¬ (-1 : ℝ) = 2 * (n : ℝ) - 1 := fun h => hn (hiff.mp h)
          simp [hn, hn']
      rw [hpre, tsum_ite_eq 0]
      simp
    · have hpre :
          (fun n : ℕ => if x = 2 * (n : ℝ) - 1
              then bernoulliNatPMF (1 / 2 : ℝ≥0) (by norm_num) n else 0)
            =
          fun _n : ℕ => (0 : ℝ≥0∞) := by
        funext n
        by_cases hn0 : n = 0
        · simp [hn0, hxn1]
        by_cases hn1 : n = 1
        · have hx' : ¬ x = 2 * (n : ℝ) - 1 := by
            intro h
            have hxone : x = 1 := by
              calc
                x = 2 * (n : ℝ) - 1 := h
                _ = 1 := by norm_num [hn1]
            exact hx1 hxone
          simp [hx']
        have hzero :
            bernoulliNatPMF (1 / 2 : ℝ≥0) (by norm_num) n = 0 :=
          bernoulliNatPMF_apply_of_ne_zero_one hn0 hn1
        by_cases hx : x = 2 * (n : ℝ) - 1
        · simpa [hx] using hzero
        · simp [hx]
      rw [hpre, tsum_zero]
      exact (rademacherPMF_apply_of_ne hx1 hxn1).symm

lemma measureReal_eq_one_of_isSymmetricBernoulli
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : IsSymmetricBernoulli X μ) :
    μ.real {ω | X ω = 1} = 1 / 2 := by
  have hpre :
      μ {ω | X ω = 1} = rademacherPMF.toMeasure ({1} : Set ℝ) := by
    rw [← hX.map_eq]
    exact (Measure.map_apply_of_aemeasurable hX.aemeasurable
      (measurableSet_singleton (1 : ℝ))).symm
  rw [measureReal_def, hpre]
  rw [PMF.toMeasure_apply_singleton]
  · simp
  · exact measurableSet_singleton (1 : ℝ)

lemma measureReal_eq_neg_one_of_isSymmetricBernoulli
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : IsSymmetricBernoulli X μ) :
    μ.real {ω | X ω = -1} = 1 / 2 := by
  have hpre :
      μ {ω | X ω = -1} = rademacherPMF.toMeasure ({-1} : Set ℝ) := by
    rw [← hX.map_eq]
    exact (Measure.map_apply_of_aemeasurable hX.aemeasurable
      (measurableSet_singleton (-1 : ℝ))).symm
  rw [measureReal_def, hpre]
  rw [PMF.toMeasure_apply_singleton]
  · simp
  · exact measurableSet_singleton (-1 : ℝ)

lemma rademacher_integral_eq (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ x, f x ∂rademacherPMF.toMeasure = (f 1 + f (-1)) / 2 := by
  let φ : Bool → ℝ := fun b => if b then (1 : ℝ) else -1
  change
    ∫ x, f x ∂(PMF.map φ (PMF.bernoulli (1 / 2 : ℝ≥0) (by norm_num))).toMeasure =
      (f 1 + f (-1)) / 2
  rw [← (PMF.toMeasure_map (PMF.bernoulli (1 / 2 : ℝ≥0) (by norm_num))
    (f := φ) (measurable_of_finite φ))]
  rw [integral_map]
  · rw [PMF.integral_eq_sum]
    simp [φ, PMF.bernoulli_apply]
    ring
  · exact (measurable_of_finite φ).aemeasurable
  · exact hf.aestronglyMeasurable

lemma rademacher_mgf_eq_cosh (t : ℝ) :
    mgf id rademacherPMF.toMeasure t = Real.cosh t := by
  rw [mgf, rademacher_integral_eq _ (by fun_prop)]
  rw [Real.cosh_eq]
  simp

/-- HDP Definition 2.2.1: if `X` is Bernoulli with parameter `1/2`, then
`2X - 1` is symmetric Bernoulli/Rademacher. -/
lemma isSymmetricBernoulli_two_mul_sub_one_of_isBernoulliHalf
    {X : Ω → ℕ} (hX : IsBernoulliHalf X μ) :
    IsSymmetricBernoulli (fun ω => 2 * (X ω : ℝ) - 1) μ := by
  let f : ℕ → ℝ := fun n => 2 * (n : ℝ) - 1
  have hmap :
      μ.map (fun ω => 2 * (X ω : ℝ) - 1) =
        rademacherPMF.toMeasure := by
    change μ.map (f ∘ X) = rademacherPMF.toMeasure
    rw [← AEMeasurable.map_map_of_aemeasurable
      (g := f) (f := X)]
    · rw [hX.map_eq]
      exact
        (PMF.toMeasure_map
          (bernoulliNatPMF (1 / 2 : ℝ≥0) (by norm_num))
          (f := f)
          (measurable_of_countable f)).trans
          (congrArg PMF.toMeasure bernoulliHalf_map_two_mul_sub_one_eq_rademacherPMF)
    · exact (measurable_of_countable f).aemeasurable
    · exact hX.aemeasurable
  exact ⟨(measurable_of_countable f).comp_aemeasurable
    hX.aemeasurable, hmap⟩

lemma integral_eq_zero_of_isSymmetricBernoulli
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : IsSymmetricBernoulli X μ) :
    μ[X] = 0 := by
  calc
    μ[X] = ∫ x, x ∂rademacherPMF.toMeasure := HasLaw.integral_eq hX
    _ = 0 := by
      simpa using rademacher_integral_eq id measurable_id

lemma ae_mem_Icc_of_isSymmetricBernoulli
    {X : Ω → ℝ} (hX : IsSymmetricBernoulli X μ) :
    ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-1 : ℝ) 1 := by
  have hLaw : HasLaw X rademacherPMF.toMeasure μ := hX
  have hsupport : ∀ᵐ x ∂rademacherPMF.toMeasure, x ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    have hzero :
        rademacherPMF.toMeasure (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
      rw [(PMF.toMeasure_apply_eq_zero_iff (p := rademacherPMF) measurableSet_Icc.compl)]
      rw [Set.disjoint_left]
      intro x hx hxc
      rw [PMF.mem_support_iff] at hx
      by_cases hx1 : x = 1
      · exact hxc (by simp [hx1])
      by_cases hxn1 : x = -1
      · exact hxc (by simp [hxn1])
      exact hx (rademacherPMF_apply_of_ne hx1 hxn1)
    change rademacherPMF.toMeasure (Set.Icc (-1 : ℝ) 1)ᶜ = 0
    exact hzero
  exact
    (hLaw.ae_iff (p := fun x => x ∈ Set.Icc (-1 : ℝ) 1)
      (measurable_mem.mpr measurableSet_Icc)).2 hsupport

lemma hasSubgaussianMGF_of_isSymmetricBernoulli
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : IsSymmetricBernoulli X μ) :
    HasSubgaussianMGF X 1 μ := by
  have h :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := μ) (X := X) (a := -1) (b := 1)
      hX.aemeasurable (ae_mem_Icc_of_isSymmetricBernoulli (μ := μ) hX)
      (integral_eq_zero_of_isSymmetricBernoulli (μ := μ) hX)
  convert h using 1
  norm_num

end Rademacher

section Numeric

/-- HDP Exercise 2.2.3: `cosh x ≤ exp (x²/2)`. -/
lemma cosh_le_exp_sq_div_two (x : ℝ) :
    Real.cosh x ≤ Real.exp (x ^ 2 / 2) := by
  simpa using Real.cosh_le_exp_half_sq x

/-- The elementary inequality `1 + x ≤ exp x`, used in Chernoff's proof. -/
lemma one_add_le_exp (x : ℝ) : 1 + x ≤ Real.exp x :=
  by simpa [add_comm] using Real.add_one_le_exp x

/-- A second-order upper bound for the exponential near the origin. -/
lemma exp_sub_one_le_self_add_sq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x - 1 ≤ x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hx
  have hle : Real.exp x - 1 - x ≤ x ^ 2 :=
    (le_abs_self (Real.exp x - 1 - x)).trans h
  linarith

/-- The positive-parameter form of the second-order exponential upper bound. -/
lemma exp_sub_one_le_self_add_sq_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    Real.exp x - 1 ≤ x + x ^ 2 :=
  exp_sub_one_le_self_add_sq_of_abs_le_one (by simpa [abs_of_nonneg hx.1] using hx.2)

/-- The negative-parameter form of the second-order exponential upper bound. -/
lemma exp_neg_sub_one_le_neg_add_sq_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    Real.exp (-x) - 1 ≤ -x + x ^ 2 := by
  have h := exp_sub_one_le_self_add_sq_of_abs_le_one (x := -x) (by
    simpa [abs_neg, abs_of_nonneg hx.1] using hx.2)
  simpa using h

end Numeric

end LeanFpAnalysis.HDP
