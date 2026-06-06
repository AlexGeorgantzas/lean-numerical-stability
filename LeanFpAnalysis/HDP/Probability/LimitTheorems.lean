import LeanFpAnalysis.HDP.Probability.Inequalities
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic

/-!
# Limit Theorems

HDP Chapter 1, Section 1.3. The strong law is provided by mathlib and wrapped
in book-style notation. The Lindeberg-Levy CLT uses mathlib's characteristic-
function Taylor expansion and Lévy continuity theorem, together with the local
book-style normalization and characteristic-function factorization lemmas below.
-/

noncomputable section

open Asymptotics Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology
open scoped Function

namespace LeanFpAnalysis.HDP

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Laws

variable {β : Type*} [MeasurableSpace β]

/-- The probability law of a random variable as a `ProbabilityMeasure`. -/
def lawOf [IsProbabilityMeasure μ] (X : Ω → β) (hX : AEMeasurable X μ) :
    ProbabilityMeasure β :=
  ⟨μ.map X, Measure.isProbabilityMeasure_map hX⟩

@[simp]
lemma lawOf_toMeasure [IsProbabilityMeasure μ] (X : Ω → β) (hX : AEMeasurable X μ) :
    (lawOf (μ := μ) X hX : Measure β) = μ.map X := rfl

end Laws

section DiscreteConvergence

/-- On `ℕ`, convergence of probability measures follows from convergence of all
singleton probabilities. This is the discrete Portmanteau criterion used for
Poisson limit theorems. -/
theorem probabilityMeasure_nat_tendsto_of_singleton
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {νs : ι → ProbabilityMeasure ℕ} {ν : ProbabilityMeasure ℕ}
    (h : ∀ k : ℕ, Tendsto (fun i => νs i ({k} : Set ℕ)) l (𝓝 (ν ({k} : Set ℕ)))) :
    Tendsto νs l (𝓝 ν) := by
  let S : Set (Set ℕ) := {s | s.Subsingleton}
  have hS : IsPiSystem S := by
    intro s hs t ht hst
    exact hs.anti Set.inter_subset_left
  refine hS.tendsto_probabilityMeasure_of_tendsto_of_mem ?hmeas ?hbasis ?hconv
  · intro s hs
    exact hs.measurableSet
  · intro u hu x hx
    refine ⟨{x}, Set.subsingleton_singleton, ?_, ?_⟩
    · exact (discreteTopology_iff_singleton_mem_nhds.mp inferInstance) x
    · intro y hy
      have hyx : y = x := by simpa using hy
      simpa [hyx] using hx
  · intro s hs
    rcases hs.eq_empty_or_singleton with rfl | ⟨k, rfl⟩
    · simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ≥0)) l (𝓝 0))
    · exact h k

end DiscreteConvergence

section Sums

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Partial sum `S_N = X_0 + ... + X_{N-1}`. This is the zero-indexed
Lean version of the book's `X_1 + ... + X_N`. -/
def partialSum (X : ℕ → Ω → E) (N : ℕ) (ω : Ω) : E :=
  ∑ i ∈ Finset.range N, X i ω

/-- Sample mean `S_N / N`, written as scalar multiplication for vector-valued
random variables. -/
def sampleMean (X : ℕ → Ω → E) (N : ℕ) (ω : Ω) : E :=
  (N : ℝ)⁻¹ • partialSum X N ω

omit [MeasurableSpace Ω] [NormedSpace ℝ E] in
@[simp]
lemma partialSum_def (X : ℕ → Ω → E) (N : ℕ) (ω : Ω) :
    partialSum X N ω = ∑ i ∈ Finset.range N, X i ω := rfl

omit [MeasurableSpace Ω] in
@[simp]
lemma sampleMean_def (X : ℕ → Ω → E) (N : ℕ) (ω : Ω) :
    sampleMean X N ω = (N : ℝ)⁻¹ • partialSum X N ω := rfl

end Sums

section VarianceOfSampleMean

/-- HDP Section 1.3: variance of a finite sum of independent real random
variables. -/
theorem variance_sum_independent
    {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) :
    Var[(fun ω => ∑ i, X i ω); μ] =
      ∑ i, Var[X i; μ] := by
  classical
  have hsum_indep :
      Set.Pairwise (↑(Finset.univ : Finset ι)) fun i j =>
        X i ⟂ᵢ[μ] X j := by
    intro i _ j _ hij
    exact hindep hij
  have h :=
    ProbabilityTheory.IndepFun.variance_sum
      (μ := μ) (X := X) (s := (Finset.univ : Finset ι))
      (by intro i _; exact hX i) hsum_indep
  simpa [Finset.sum_fn] using h

/-- HDP (1.5): for independent variables with a common variance `σ2`, the
variance of the sample mean is `σ2 / N`. -/
theorem variance_sampleMean_eq {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {σ2 : ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hvar : ∀ i, Var[X i; μ] = σ2) :
    Var[fun ω => (N : ℝ)⁻¹ * ∑ i : Fin N, X i ω; μ] = σ2 / (N : ℝ) := by
  classical
  have hsum' :
      Var[(fun ω => ∑ i : Fin N, X i ω); μ] =
        ∑ i : Fin N, Var[X i; μ] :=
    variance_sum_independent (μ := μ) (X := X) hX hindep
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  calc
    Var[fun ω => (N : ℝ)⁻¹ * ∑ i : Fin N, X i ω; μ]
        = ((N : ℝ)⁻¹) ^ 2 * Var[(fun ω => ∑ i : Fin N, X i ω); μ] := by
          simpa using
            (ProbabilityTheory.variance_const_mul ((N : ℝ)⁻¹)
              (fun ω => ∑ i : Fin N, X i ω) μ)
    _ = ((N : ℝ)⁻¹) ^ 2 * (∑ i : Fin N, Var[X i; μ]) := by
          rw [hsum']
    _ = ((N : ℝ)⁻¹) ^ 2 * ((N : ℝ) * σ2) := by
          simp [hvar]
    _ = σ2 / (N : ℝ) := by
          field_simp [hN_ne]

/-- HDP Exercise 1.3.3: the expected absolute deviation of the sample mean is
bounded by `σ / sqrt N`, here written with `σ2 = σ^2` as
`sqrt σ2 / sqrt N`.

The hypotheses are stated for the first `N` variables of the sequence. -/
theorem expected_abs_sampleMean_sub_mean_le
    [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : ℕ → Ω → ℝ} {m σ2 : ℝ}
    (hX : ∀ i : Fin N, MemLp (X i) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun i : Fin N => X i))
    (hmean : ∀ i : Fin N, μ[X i] = m)
    (hvar : ∀ i : Fin N, Var[X i; μ] = σ2) :
    μ[fun ω => |sampleMean X N ω - m|]
      ≤ Real.sqrt σ2 / Real.sqrt (N : ℝ) := by
  classical
  let Xfin : Fin N → Ω → ℝ := fun i => X i
  let Y : Ω → ℝ := fun ω => (N : ℝ)⁻¹ * ∑ i : Fin N, X i ω
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hσ2_nonneg : 0 ≤ σ2 := by
    let i0 : Fin N := ⟨0, hN⟩
    have h := ProbabilityTheory.variance_nonneg (X (i0 : ℕ)) μ
    simpa [i0, hvar i0] using h
  have hX_int : ∀ i : Fin N, Integrable (X i) μ := fun i =>
    (hX i).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hsum_memLp : MemLp (fun ω => ∑ i : Fin N, X i ω) 2 μ := by
    simpa [Xfin] using
      (memLp_finset_sum (μ := μ) (p := (2 : ℝ≥0∞))
        (s := (Finset.univ : Finset (Fin N))) (f := fun i ω => X i ω)
        (fun i _ => hX i))
  have hY_memLp : MemLp Y 2 μ := by
    simpa [Y] using hsum_memLp.const_mul ((N : ℝ)⁻¹)
  have hY_int : Integrable Y μ :=
    hY_memLp.integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hmeanY : μ[Y] = m := by
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
  have hZ_memLp : MemLp (fun ω => Y ω - m) 2 μ :=
    hY_memLp.sub (memLp_const m)
  have hmeanZ : μ[fun ω => Y ω - m] = 0 := by
    rw [integral_sub hY_int (integrable_const m), hmeanY]
    simp
  have hvarY : Var[Y; μ] = σ2 / (N : ℝ) := by
    simpa [Y, Xfin] using
      variance_sampleMean_eq (μ := μ) (N := N) hN
        (X := Xfin) (σ2 := σ2) hX hindep hvar
  have hsq :
      μ[fun ω => (Y ω - m) ^ 2] = σ2 / (N : ℝ) := by
    rw [← ProbabilityTheory.variance_of_integral_eq_zero
      hZ_memLp.aemeasurable hmeanZ]
    rw [ProbabilityTheory.variance_sub_const hY_memLp.aestronglyMeasurable m]
    exact hvarY
  have hbound := integral_abs_le_sqrt_integral_sq (μ := μ) (X := fun ω => Y ω - m) hZ_memLp
  have hsample :
      (fun ω => |sampleMean X N ω - m|)
        = fun ω => |Y ω - m| := by
    funext ω
    simp [sampleMean, partialSum, Y, smul_eq_mul, Finset.sum_range]
  rw [hsample]
  calc
    μ[fun ω => |Y ω - m|]
        ≤ Real.sqrt (μ[fun ω => (Y ω - m) ^ 2]) := hbound
    _ = Real.sqrt (σ2 / (N : ℝ)) := by rw [hsq]
    _ = Real.sqrt σ2 / Real.sqrt (N : ℝ) := by
      rw [Real.sqrt_div hσ2_nonneg (N : ℝ)]

/-- HDP Exercise 1.3.3 in Landau notation:
`E |sampleMean_N - m| = O(N^{-1/2})`. -/
theorem exercise_1_3_3_expected_abs_sampleMean_sub_mean_isBigO
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {m σ2 : ℝ}
    (hX : ∀ i : ℕ, MemLp (X i) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hmean : ∀ i : ℕ, μ[X i] = m)
    (hvar : ∀ i : ℕ, Var[X i; μ] = σ2) :
    (fun N : ℕ => μ[fun ω => |sampleMean X N ω - m|])
      =O[atTop] (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) := by
  refine IsBigO.of_bound (Real.sqrt σ2) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : 0 < N := hN
  have hindep_fin :
      Pairwise ((· ⟂ᵢ[μ] ·) on fun i : Fin N => X i) := by
    intro i j hij
    exact hindep (fun h => hij (Fin.ext h))
  have hle :
      μ[fun ω => |sampleMean X N ω - m|]
        ≤ Real.sqrt σ2 / Real.sqrt (N : ℝ) :=
    expected_abs_sampleMean_sub_mean_le (μ := μ) (N := N) hNpos
      (X := X) (m := m) (σ2 := σ2)
      (fun i => hX i) hindep_fin (fun i => hmean i) (fun i => hvar i)
  have hf_nonneg : 0 ≤ μ[fun ω => |sampleMean X N ω - m|] :=
    integral_nonneg fun _ => abs_nonneg _
  have hg_nonneg : 0 ≤ (Real.sqrt (N : ℝ))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc
    ‖μ[fun ω => |sampleMean X N ω - m|]‖
        = μ[fun ω => |sampleMean X N ω - m|] :=
          Real.norm_of_nonneg hf_nonneg
    _ ≤ Real.sqrt σ2 / Real.sqrt (N : ℝ) := hle
    _ = Real.sqrt σ2 * ‖(Real.sqrt (N : ℝ))⁻¹‖ := by
          rw [Real.norm_of_nonneg hg_nonneg, div_eq_mul_inv]

end VarianceOfSampleMean

section StrongLaw

variable {X : ℕ → Ω → ℝ}

/-- HDP Theorem 1.3.1, strong law of large numbers, real-valued version.
Mathlib proves the slightly stronger pairwise-independent form; i.i.d. sequences
are an immediate special case. -/
theorem strong_law_large_numbers_real
    (hX : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun N : ℕ => sampleMean X N ω) atTop (𝓝 μ[X 0]) := by
  simpa [sampleMean, partialSum, smul_eq_mul, div_eq_inv_mul] using
    ProbabilityTheory.strong_law_ae_real X hX hindep hident

end StrongLaw

section GaussianLimit

/-- The standard normal distribution as a `ProbabilityMeasure`. -/
def standardNormalProbability : ProbabilityMeasure ℝ :=
  ⟨standardNormalMeasure, inferInstance⟩

/-- The standard normal upper tail written as an integral of its density. -/
theorem standardNormal_tail_eq_integral (t : ℝ) :
    standardNormalMeasure (Set.Ici t) =
      ENNReal.ofReal (∫ x in Set.Ici t, standardNormalDensity x) := by
  simpa [standardNormalMeasure, standardNormalDensity] using
    ProbabilityTheory.gaussianReal_apply_eq_integral
      0 (v := (1 : ℝ≥0)) (by norm_num) (Set.Ici t)

/-- Normalized sum from HDP Theorem 1.3.2:
`(S_N - N μ) / (σ sqrt N)`. -/
def normalizedSum (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ((∑ i ∈ Finset.range N, X i ω) - (N : ℝ) * m) / (σ * Real.sqrt (N : ℝ))

omit [MeasurableSpace Ω] in
/-- Algebraic form of the normalized sum:
`sum X_i - N m = sum (X_i - m)`. -/
theorem normalizedSum_eq_sum_centered
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (ω : Ω) :
    normalizedSum X m σ N ω =
      (∑ i ∈ Finset.range N, (X i ω - m)) /
        (σ * Real.sqrt (N : ℝ)) := by
  simp [normalizedSum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]

/-- Expectation of a finite partial sum. -/
theorem integral_partialSum_eq_sum_integral
    {X : ℕ → Ω → ℝ}
    {N : ℕ}
    (hX : ∀ i ∈ Finset.range N, Integrable (X i) μ) :
    μ[fun ω => ∑ i ∈ Finset.range N, X i ω] =
      ∑ i ∈ Finset.range N, μ[X i] := by
  classical
  simpa using
    (integral_finset_sum
      (μ := μ) (s := Finset.range N) (f := fun i ω => X i ω) hX)

/-- If the first `N` variables all have mean `m`, the partial sum has mean
`N * m`. -/
theorem integral_partialSum_eq_card_mul_mean
    {X : ℕ → Ω → ℝ}
    {N : ℕ} {m : ℝ}
    (hX : ∀ i ∈ Finset.range N, Integrable (X i) μ)
    (hmean : ∀ i ∈ Finset.range N, μ[X i] = m) :
    μ[fun ω => ∑ i ∈ Finset.range N, X i ω] = (N : ℝ) * m := by
  rw [integral_partialSum_eq_sum_integral (μ := μ) hX]
  calc
    (∑ i ∈ Finset.range N, μ[X i]) = ∑ i ∈ Finset.range N, m := by
      exact Finset.sum_congr rfl fun i hi => hmean i hi
    _ = (N : ℝ) * m := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- The normalized CLT variable has mean zero when the summands have common
mean `m`. -/
theorem integral_normalizedSum_eq_zero
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {m σ : ℝ} {N : ℕ}
    (_hden : σ * Real.sqrt (N : ℝ) ≠ 0)
    (hX : ∀ i ∈ Finset.range N, Integrable (X i) μ)
    (hmean : ∀ i ∈ Finset.range N, μ[X i] = m) :
    μ[normalizedSum X m σ N] = 0 := by
  classical
  have hsum_int : Integrable (fun ω => ∑ i ∈ Finset.range N, X i ω) μ :=
    integrable_finset_sum (s := Finset.range N)
      (f := fun i ω => X i ω) hX
  have hnum :
      μ[fun ω => (∑ i ∈ Finset.range N, X i ω) - (N : ℝ) * m] = 0 := by
    rw [integral_sub hsum_int (integrable_const _)]
    rw [integral_partialSum_eq_card_mul_mean (μ := μ) hX hmean]
    simp
  calc
    μ[normalizedSum X m σ N]
        =
      (σ * Real.sqrt (N : ℝ))⁻¹ *
        μ[fun ω => (∑ i ∈ Finset.range N, X i ω) - (N : ℝ) * m] := by
          simp [normalizedSum, div_eq_inv_mul, integral_const_mul]
    _ = 0 := by simp [hnum]

/-- The normalized CLT variable has variance one when the summands are
independent with common variance `σ^2`. -/
theorem variance_normalizedSum_eq_one
    [IsProbabilityMeasure μ]
    {N : ℕ}
    (hN : 0 < N)
    {X : Fin N → Ω → ℝ}
    {m σ : ℝ}
    (hσ : 0 < σ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hvar : ∀ i, Var[X i; μ] = σ ^ 2) :
    Var[fun ω =>
      ((∑ i : Fin N, X i ω) - (N : ℝ) * m) /
        (σ * Real.sqrt (N : ℝ)); μ] = 1 := by
  classical
  have hN_ne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hN)
  have hN_nonneg : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  have hsqrt_ne : Real.sqrt (N : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast hN)
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hden_ne : σ * Real.sqrt (N : ℝ) ≠ 0 := mul_ne_zero hσ_ne hsqrt_ne
  let S : Ω → ℝ := fun ω => ∑ i : Fin N, X i ω
  have hsum :
      Var[S; μ] = ∑ i : Fin N, Var[X i; μ] := by
    simpa [S] using
      variance_sum_independent (μ := μ) (X := X) hX hindep
  have hsum_var :
      Var[S; μ] = (N : ℝ) * σ ^ 2 := by
    rw [hsum]
    simp [hvar, Finset.sum_const, nsmul_eq_mul]
  have hcenter :
      Var[fun ω => S ω - (N : ℝ) * m; μ] = Var[S; μ] :=
    ProbabilityTheory.variance_sub_const
      ((memLp_finset_sum
        (μ := μ) (p := (2 : ℝ≥0∞))
        (s := (Finset.univ : Finset (Fin N)))
        (f := fun i ω => X i ω)
        (fun i _ => hX i)).aestronglyMeasurable)
      ((N : ℝ) * m)
  calc
    Var[fun ω =>
      ((∑ i : Fin N, X i ω) - (N : ℝ) * m) /
        (σ * Real.sqrt (N : ℝ)); μ]
        =
      ((σ * Real.sqrt (N : ℝ))⁻¹) ^ 2 *
        Var[fun ω => S ω - (N : ℝ) * m; μ] := by
          simpa [S, div_eq_inv_mul] using
            (ProbabilityTheory.variance_const_mul
              ((σ * Real.sqrt (N : ℝ))⁻¹)
              (fun ω => S ω - (N : ℝ) * m) μ)
    _ =
      ((σ * Real.sqrt (N : ℝ))⁻¹) ^ 2 * Var[S; μ] := by
        rw [hcenter]
    _ =
      ((σ * Real.sqrt (N : ℝ))⁻¹) ^ 2 * ((N : ℝ) * σ ^ 2) := by
        rw [hsum_var]
    _ = 1 := by
      field_simp [hden_ne, hσ_ne, hN_ne]
      rw [Real.sq_sqrt hN_nonneg]

/-- The convergence-in-distribution conclusion of the Lindeberg-Levy CLT. -/
def centralLimitConclusion [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (m σ : ℝ)
    (hZ : ∀ N, AEMeasurable (normalizedSum X m σ N) μ) : Prop :=
  Tendsto
    (fun N : ℕ => lawOf (μ := μ) (normalizedSum X m σ N) (hZ N))
    atTop
    (𝓝 standardNormalProbability)

/-- Characteristic-function form of the CLT conclusion:
the normalized sums have characteristic functions converging pointwise to that
of `N(0,1)`, namely `exp (-t^2/2)`. -/
def centralLimitCharacteristicFunctionConclusion [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (m σ : ℝ) : Prop :=
  ∀ t : ℝ,
    Tendsto
      (fun N : ℕ => charFun (μ.map (normalizedSum X m σ N)) t)
      atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2)))

/-- The second-order characteristic-function expansion for one centered
summand, in exactly the sequence form used in the Lindeberg-Levy proof. This is
proved below from the moment assumptions, not assumed as a CLT hypothesis. -/
def lindebergLevySecondOrderCharFunExpansion [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (σ : ℝ) : Prop :=
  ∀ t : ℝ,
    Tendsto
      (fun N : ℕ =>
        (N : ℂ) *
          (charFun (μ.map Y) (t / (σ * Real.sqrt (N : ℝ))) - 1))
      atTop
      (𝓝 (-(t : ℂ) ^ 2 / 2))

/-- Characteristic function of the standard normal probability measure. -/
theorem standardNormal_charFun (t : ℝ) :
    charFun standardNormalMeasure t =
      Complex.exp (-(t : ℂ) ^ 2 / 2) := by
  rw [standardNormalMeasure, ProbabilityTheory.charFun_gaussianReal]
  congr 1
  norm_num
  ring

/-- Lévy-continuity bridge for the CLT: pointwise convergence of
characteristic functions implies convergence in distribution of the laws. -/
theorem centralLimitConclusion_of_characteristicFunction
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hZ : ∀ N, AEMeasurable (normalizedSum X m σ N) μ)
    (hcf : centralLimitCharacteristicFunctionConclusion (μ := μ) X m σ) :
    centralLimitConclusion (μ := μ) X m σ hZ := by
  unfold centralLimitConclusion
  refine MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun ?_
  intro t
  have ht := hcf t
  simpa [lawOf_toMeasure, standardNormalProbability, standardNormal_charFun t] using ht

/-- The centered finite sum used in the characteristic-function proof of the
Lindeberg-Levy CLT. -/
def centeredPartialSum (X : ℕ → Ω → ℝ) (m : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin N, (X i ω - m)

omit [MeasurableSpace Ω] in
@[simp]
lemma centeredPartialSum_def (X : ℕ → Ω → ℝ) (m : ℝ) (N : ℕ) (ω : Ω) :
    centeredPartialSum X m N ω = ∑ i : Fin N, (X i ω - m) := rfl

omit [MeasurableSpace Ω] in
/-- The existing HDP normalization can be read as a scalar multiple of the
centered finite sum. -/
theorem normalizedSum_eq_centeredPartialSum
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (ω : Ω) :
    normalizedSum X m σ N ω =
      (σ * Real.sqrt (N : ℝ))⁻¹ * centeredPartialSum X m N ω := by
  rw [normalizedSum_eq_sum_centered]
  simp [centeredPartialSum, Finset.sum_range, div_eq_inv_mul]

omit [MeasurableSpace Ω] in
/-- The HDP normalization is the normalized sum of standardized centered
variables `(X_i - m) / σ`. -/
theorem normalizedSum_eq_inv_sqrt_mul_sum_standardized
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (ω : Ω) :
    normalizedSum X m σ N ω =
      (Real.sqrt (N : ℝ))⁻¹ *
        ∑ i ∈ Finset.range N, (X i ω - m) / σ := by
  rw [normalizedSum_eq_sum_centered]
  rw [Finset.sum_div]
  rw [Finset.mul_sum]
  simp [div_eq_inv_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- AEMeasurability of the normalized sum from AEMeasurability of the
summands. -/
theorem normalizedSum_aemeasurable
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hX : ∀ n, AEMeasurable (X n) μ) (N : ℕ) :
    AEMeasurable (normalizedSum X m σ N) μ := by
  have hsum :
      AEMeasurable (centeredPartialSum X m N) μ := by
    have hsum_fun :
        AEMeasurable (∑ i : Fin N, fun ω => X i ω - m) μ :=
      Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin N)))
        (fun i _ => (hX i).sub (aemeasurable_const (μ := μ) (b := m)))
    exact AEMeasurable.congr hsum_fun (ae_of_all μ fun ω => by
      simp [centeredPartialSum, Finset.sum_apply])
  exact AEMeasurable.congr
    (hsum.const_mul ((σ * Real.sqrt (N : ℝ))⁻¹))
    (ae_of_all μ fun ω => by
      exact (normalizedSum_eq_centeredPartialSum X m σ N ω).symm)

/-- Centering and scaling makes the first summand mean zero. -/
theorem lindebergLevy_standardized_mean_eq_zero
    [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {m σ : ℝ}
    (hY_int : Integrable Y μ)
    (hmean : μ[Y] = m)
    (hσ : σ ≠ 0) :
    μ[fun ω => (Y ω - m) / σ] = 0 := by
  calc
    μ[fun ω => (Y ω - m) / σ]
        = μ[fun ω => (Y ω - m) * σ⁻¹] := by
          simp [div_eq_mul_inv]
    _ = μ[fun ω => Y ω - m] * σ⁻¹ := by
          rw [integral_mul_const]
    _ = σ⁻¹ * μ[fun ω => Y ω - m] := by ring
    _ = σ⁻¹ * (μ[Y] - μ[fun _ : Ω => m]) := by
          rw [integral_sub hY_int (integrable_const m)]
    _ = σ⁻¹ * (m - m) := by
          simp [hmean]
    _ = σ⁻¹ * 0 := by ring
    _ = (σ⁻¹ * σ) * 0 := by ring
    _ = 0 := by
          rw [inv_mul_cancel₀ hσ]
          norm_num

/-- Centering and scaling makes the first summand have second moment one. -/
theorem lindebergLevy_standardized_second_moment_eq_one
    [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {m σ : ℝ}
    (hY_mlp : MemLp Y 2 μ)
    (hmean : μ[Y] = m)
    (hvar : Var[Y; μ] = σ ^ 2)
    (hσ : σ ≠ 0) :
    μ[fun ω => ((Y ω - m) / σ) ^ 2] = 1 := by
  have hvar_formula :
      Var[Y; μ] = μ[fun ω => (Y ω - μ[Y]) ^ 2] :=
    ProbabilityTheory.variance_eq_integral hY_mlp.aemeasurable
  have hcenter_sq :
      μ[fun ω => (Y ω - m) ^ 2] = σ ^ 2 := by
    calc
      μ[fun ω => (Y ω - m) ^ 2]
          = μ[fun ω => (Y ω - μ[Y]) ^ 2] := by
              simp [hmean]
      _ = Var[Y; μ] := by
              rw [hvar_formula]
      _ = σ ^ 2 := hvar
  calc
    μ[fun ω => ((Y ω - m) / σ) ^ 2]
        = μ[fun ω => σ⁻¹ ^ 2 * (Y ω - m) ^ 2] := by
            congr 1
            funext ω
            field_simp [hσ]
    _ = σ⁻¹ ^ 2 * μ[fun ω => (Y ω - m) ^ 2] := by
            rw [integral_const_mul]
    _ = σ⁻¹ ^ 2 * σ ^ 2 := by
            rw [hcenter_sq]
    _ = 1 := by
            field_simp [hσ]

/-- The characteristic-function Taylor expansion for the standardized first
summand. This is the analytic input replacing the old conditional
`secondOrder_charFun` hypothesis. -/
theorem lindebergLevy_standardized_charFun_taylor
    [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {m σ : ℝ}
    (hY_meas : AEMeasurable Y μ)
    (hY_int : Integrable Y μ)
    (hY_mlp : MemLp Y 2 μ)
    (hmean : μ[Y] = m)
    (hvar : Var[Y; μ] = σ ^ 2)
    (hσ : σ ≠ 0) :
    (fun u : ℝ =>
        charFun (μ.map fun ω => (Y ω - m) / σ) u
          - (1 - (u : ℂ) ^ 2 / 2))
      =o[𝓝 0]
    (fun u : ℝ => u ^ 2) := by
  have hZ_meas :
      AEMeasurable (fun ω => (Y ω - m) / σ) μ :=
    (hY_meas.sub aemeasurable_const).div_const σ
  have hZ_mean :
      μ[fun ω => (Y ω - m) / σ] = 0 :=
    lindebergLevy_standardized_mean_eq_zero
      (μ := μ) hY_int hmean hσ
  have hZ_sq :
      μ[fun ω => ((Y ω - m) / σ) ^ 2] = 1 :=
    lindebergLevy_standardized_second_moment_eq_one
      (μ := μ) hY_mlp hmean hvar hσ
  simpa using
    MeasureTheory.taylor_charFun_two
      (P := μ)
      (X := fun ω => (Y ω - m) / σ)
      hZ_meas hZ_mean hZ_sq

/-- Scaling identity for characteristic functions of divided random variables. -/
theorem charFun_div_eq_charFun_scaled
    [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {σ t : ℝ}
    (hY : AEMeasurable Y μ) :
    charFun (μ.map (fun ω => Y ω / σ)) t =
      charFun (μ.map Y) (t / σ) := by
  have hcongr :
      (fun ω => Y ω / σ) =ᵐ[μ] fun ω => σ⁻¹ * Y ω := by
    exact ae_of_all μ fun ω => by
      simp [div_eq_inv_mul, mul_comm]
  rw [Measure.map_congr hcongr]
  change charFun (Measure.map ((fun x : ℝ => σ⁻¹ * x) ∘ Y) μ) t =
    charFun (Measure.map Y μ) (t / σ)
  rw [← AEMeasurable.map_map_of_aemeasurable
    (g := fun x : ℝ => σ⁻¹ * x) (f := Y)
    (by fun_prop) hY]
  rw [charFun_map_mul]
  simp [div_eq_inv_mul, mul_comm]

/-- Frequency-specialized scaling identity used in the CLT proof. -/
theorem charFun_div_sqrt_eq_charFun_scaled_sqrt
    [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {σ : ℝ}
    (hY : AEMeasurable Y μ)
    (N : ℕ) (t : ℝ) :
    charFun (μ.map (fun ω => Y ω / σ)) (t / Real.sqrt (N : ℝ)) =
      charFun (μ.map Y) (t / (σ * Real.sqrt (N : ℝ))) := by
  convert charFun_div_eq_charFun_scaled
    (μ := μ) (Y := Y) (σ := σ) (t := t / Real.sqrt (N : ℝ)) hY using 2
  ring_nf

/-- Sequential form of the second-order Taylor expansion used in the CLT:
`φ(u) = 1 - u² / 2 + o(u²)` at `0` implies
`N * (φ(t / sqrt N) - 1) → -t² / 2`. -/
theorem standardized_secondOrder_sequence_of_taylor
    {φ : ℝ → ℂ}
    (htaylor :
      (fun u : ℝ => φ u - (1 - (u : ℂ) ^ 2 / 2))
        =o[𝓝 0]
      (fun u : ℝ => u ^ 2))
    (t : ℝ) :
    Tendsto
      (fun N : ℕ =>
        (N : ℂ) * (φ (t / Real.sqrt (N : ℝ)) - 1))
      atTop
      (𝓝 (-(t : ℂ) ^ 2 / 2)) := by
  let u : ℕ → ℝ := fun N => t / Real.sqrt (N : ℝ)
  let r : ℝ → ℂ := fun u => φ u - (1 - (u : ℂ) ^ 2 / 2)
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa [u] using
      (tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp
          (tendsto_natCast_atTop_atTop :
            Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)) :
        Tendsto (fun N : ℕ => t / Real.sqrt (N : ℝ)) atTop (𝓝 0))
  have hr_real : (fun N : ℕ => r (u N)) =o[atTop] (fun N : ℕ => (u N) ^ 2) := by
    simpa [r, Function.comp_def] using htaylor.comp_tendsto hu
  by_cases ht : t = 0
  · subst t
    have hr_const : Tendsto (fun _ : ℕ => r 0) atTop (𝓝 0) := by
      have hconst :
          (fun _ : ℕ => r 0) =o[atTop] (fun _ : ℕ => (0 : ℝ)) := by
        simpa [r, Function.comp_def] using
          htaylor.comp_tendsto
            (tendsto_const_nhds :
              Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      exact hconst.trans_tendsto tendsto_const_nhds
    have hr0 : r 0 = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hr_const
    have hφ0 : φ 0 = 1 := by
      have : φ 0 - (1 - (0 : ℂ) ^ 2 / 2) = 0 := by
        simpa [r] using hr0
      simpa using sub_eq_zero.mp this
    simp [hφ0]
  · have hr_complex :
        (fun N : ℕ => r (u N)) =o[atTop]
          (fun N : ℕ => ((u N : ℂ) ^ 2)) := by
      rw [← Asymptotics.isLittleO_norm_right]
      rw [← Asymptotics.isLittleO_norm_right] at hr_real
      simpa [Complex.normSq] using hr_real
    have hratio :
        Tendsto
          (fun N : ℕ => r (u N) / ((u N : ℂ) ^ 2))
          atTop (𝓝 0) :=
      hr_complex.tendsto_div_nhds_zero
    have hNu2 :
        Tendsto
          (fun N : ℕ => (N : ℂ) * ((u N : ℂ) ^ 2))
          atTop
          (𝓝 ((t : ℂ) ^ 2)) := by
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [eventually_ne_atTop 0] with N hN
      dsimp [u]
      have hreal :
          (N : ℝ) * (t / Real.sqrt (N : ℝ)) ^ 2 = t ^ 2 := by
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
        field_simp [Nat.cast_ne_zero.mpr hN]
      exact_mod_cast hreal
    have hrem :
        Tendsto (fun N : ℕ => (N : ℂ) * r (u N)) atTop (𝓝 0) := by
      have hprod := hNu2.mul hratio
      have heq :
          (fun N : ℕ =>
              (N : ℂ) * ((u N : ℂ) ^ 2) *
                (r (u N) / ((u N : ℂ) ^ 2))) =ᶠ[atTop]
            fun N : ℕ => (N : ℂ) * r (u N) := by
        filter_upwards [eventually_ne_atTop 0] with N hN
        have huc : (u N : ℂ) ≠ 0 := by
          dsimp [u]
          have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
            Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))
          have hune : (t / Real.sqrt (N : ℝ) : ℝ) ≠ 0 :=
            div_ne_zero ht hsqrt_pos.ne'
          exact Complex.ofReal_ne_zero.mpr hune
        have hu_ne : (u N : ℂ) ^ 2 ≠ 0 :=
          pow_ne_zero 2 huc
        rw [div_eq_mul_inv]
        calc
          (N : ℂ) * (u N : ℂ) ^ 2 *
              (r (u N) * (((u N : ℂ) ^ 2)⁻¹)) =
            (N : ℂ) * r (u N) *
              (((u N : ℂ) ^ 2) * (((u N : ℂ) ^ 2)⁻¹)) := by
              ring
          _ = (N : ℂ) * r (u N) * 1 := by
              rw [mul_inv_cancel₀ hu_ne]
          _ = (N : ℂ) * r (u N) := by
              ring
      simpa using hprod.congr' heq
    have hmain :
        Tendsto
          (fun N : ℕ =>
            (N : ℂ) * (-(u N : ℂ) ^ 2 / 2))
          atTop
          (𝓝 (-(t : ℂ) ^ 2 / 2)) := by
      have h' := hNu2.const_mul (-(1 / 2 : ℂ))
      convert h' using 1
      · ext N
        ring
      · ring_nf
    have hsum := hmain.add hrem
    have heq :
        (fun N : ℕ =>
            (N : ℂ) * (-(u N : ℂ) ^ 2 / 2) +
              (N : ℂ) * r (u N)) =ᶠ[atTop]
          fun N : ℕ => (N : ℂ) * (φ (t / Real.sqrt (N : ℝ)) - 1) := by
      filter_upwards with N
      dsimp [r, u]
      ring
    simpa using hsum.congr' heq

/-- The second-order characteristic-function expansion follows from the usual
one-variable moment assumptions. This is the former analytic gap in the
Lindeberg-Levy CLT proof. -/
theorem lindebergLevySecondOrderCharFunExpansion_of_moments
    [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {m σ : ℝ}
    (hY_meas : AEMeasurable Y μ)
    (hY_int : Integrable Y μ)
    (hY_mlp : MemLp Y 2 μ)
    (hmean : μ[Y] = m)
    (hvar : Var[Y; μ] = σ ^ 2)
    (hσ : σ ≠ 0) :
    lindebergLevySecondOrderCharFunExpansion
      (μ := μ) (fun ω => Y ω - m) σ := by
  intro t
  have htaylor :
      (fun u : ℝ =>
          charFun (μ.map fun ω => (Y ω - m) / σ) u
            - (1 - (u : ℂ) ^ 2 / 2))
        =o[𝓝 0]
      (fun u : ℝ => u ^ 2) :=
    lindebergLevy_standardized_charFun_taylor
      (μ := μ) (Y := Y) (m := m) (σ := σ)
      hY_meas hY_int hY_mlp hmean hvar hσ
  have hseq :=
    standardized_secondOrder_sequence_of_taylor htaylor t
  refine hseq.congr' ?_
  filter_upwards with N
  rw [charFun_div_sqrt_eq_charFun_scaled_sqrt
    (μ := μ) (Y := fun ω => Y ω - m) (σ := σ)
    ((hY_meas.sub aemeasurable_const)) N t]

/-- Characteristic-function factorization for the normalized sum in the
Lindeberg-Levy CLT proof. This is the genuine independence step:
the characteristic function of the normalized sum is the `N`-th power of the
characteristic function of one centered summand, evaluated at the scaled
frequency. -/
theorem charFun_normalizedSum_eq_pow
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hX : ∀ n, AEMeasurable (X n) μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ n, IdentDistrib (X 0) (X n) μ μ)
    (N : ℕ) (t : ℝ) :
    charFun (μ.map (normalizedSum X m σ N)) t =
      (charFun (μ.map (fun ω => X 0 ω - m))
        (t / (σ * Real.sqrt (N : ℝ)))) ^ N := by
  classical
  let Y : Fin N → Ω → ℝ := fun i ω => X i ω - m
  let S : Ω → ℝ := ∑ i : Fin N, Y i
  let c : ℝ := (σ * Real.sqrt (N : ℝ))⁻¹
  have hY_meas : ∀ i : Fin N, AEMeasurable (Y i) μ := by
    intro i
    exact (hX i).sub aemeasurable_const
  have hY_indep : iIndepFun Y μ := by
    have hres : iIndepFun (fun i : Fin N => X (i : ℕ)) μ :=
      hindep.precomp Fin.val_injective
    exact hres.comp (fun _ x => x - m) (fun _ => measurable_id.sub measurable_const)
  have hS_meas : AEMeasurable S μ := by
    change AEMeasurable (∑ i : Fin N, Y i) μ
    exact Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin N)))
      fun i _ => hY_meas i
  have hnorm_ae : normalizedSum X m σ N =ᵐ[μ] fun ω => c * S ω := by
    exact ae_of_all μ fun ω => by
      simp [S, Y, c, normalizedSum_eq_centeredPartialSum, centeredPartialSum]
  rw [Measure.map_congr hnorm_ae]
  change
    charFun (Measure.map ((fun x : ℝ => c * x) ∘ S) μ) t =
      charFun (Measure.map (fun ω => X 0 ω - m) μ)
        (t / (σ * Real.sqrt (N : ℝ))) ^ N
  rw [← AEMeasurable.map_map_of_aemeasurable
    (g := fun x : ℝ => c * x) (f := S)
    (by fun_prop) hS_meas]
  rw [charFun_map_mul]
  have hsum_cf :
      charFun (μ.map S) (c * t) =
        ∏ i : Fin N, charFun (μ.map (Y i)) (c * t) := by
    simpa [S] using congrFun (hY_indep.charFun_map_sum_eq_prod hY_meas) (c * t)
  rw [hsum_cf]
  have hfactor :
      ∀ i : Fin N,
        charFun (μ.map (Y i)) (c * t) =
          charFun (μ.map (fun ω => X 0 ω - m)) (c * t) := by
    intro i
    have hi : IdentDistrib (fun ω => X 0 ω - m) (Y i) μ μ :=
      (hident i).comp (measurable_id.sub measurable_const)
    rw [← hi.map_eq]
  rw [Finset.prod_congr rfl (fun i _ => hfactor i)]
  simp [c, div_eq_inv_mul, mul_comm]

/-- Characteristic-function factorization for normalized sums, expressed in
terms of the standardized one-summand law.  This is the form used by the
Berry-Esseen Fourier estimates. -/
theorem charFun_normalizedSum_eq_standardized_pow
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hX : ∀ n, AEMeasurable (X n) μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (N : ℕ) (t : ℝ) :
    charFun (μ.map (normalizedSum X m σ N)) t =
      (charFun (μ.map (fun ω => (X 0 ω - m) / σ))
        (t / Real.sqrt (N : ℝ))) ^ N := by
  rw [charFun_normalizedSum_eq_pow
    (μ := μ) hX hindep (fun n => (hident n).symm) N t]
  rw [charFun_div_sqrt_eq_charFun_scaled_sqrt
    (μ := μ) (Y := fun ω => X 0 ω - m) (σ := σ)
    ((hX 0).sub aemeasurable_const) N t]

/-- From the characteristic-function Taylor expansion for the standardized
summand, the normalized sums converge pointwise to the standard normal
characteristic function. -/
theorem lindebergLevyCentralLimitTheorem_characteristicFunction
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hX : ∀ n, AEMeasurable (X n) μ)
    (hX_int : Integrable (X 0) μ)
    (hX_mlp : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hmean : μ[X 0] = m)
    (hvar : Var[X 0; μ] = σ ^ 2)
    (hσ : 0 < σ) :
    centralLimitCharacteristicFunctionConclusion (μ := μ) X m σ := by
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hsecond :
      lindebergLevySecondOrderCharFunExpansion
        (μ := μ) (fun ω => X 0 ω - m) σ :=
    lindebergLevySecondOrderCharFunExpansion_of_moments
      (μ := μ) (Y := X 0) (m := m) (σ := σ)
      (hX 0) hX_int hX_mlp hmean hvar hσ_ne
  intro t
  have hpow :=
    Complex.tendsto_one_add_pow_exp_of_tendsto (hsecond t)
  exact hpow.congr' (by
    filter_upwards with N
    rw [charFun_normalizedSum_eq_pow
      (μ := μ) hX hindep (fun n => (hident n).symm) N t]
    congr 1
    ring)

/-- Tail form of the CLT obtained from convergence in distribution at the
Gaussian continuity set `[t, ∞)`. -/
theorem centralLimit_tail_tendsto
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    {hZ : ∀ N, AEMeasurable (normalizedSum X m σ N) μ}
    (hCLT : centralLimitConclusion (μ := μ) X m σ hZ)
    (t : ℝ) :
    Tendsto
      (fun N : ℕ =>
        (((lawOf (μ := μ) (normalizedSum X m σ N) (hZ N) : ProbabilityMeasure ℝ)
          (Set.Ici t) : ℝ≥0) : ℝ))
      atTop
      (𝓝 ((((standardNormalProbability : ProbabilityMeasure ℝ)
        (Set.Ici t) : ℝ≥0) : ℝ))) := by
  have h_cont :
      (standardNormalProbability : ProbabilityMeasure ℝ) (frontier (Set.Ici t)) = 0 := by
    have hfront : frontier (Set.Ici t) = ({t} : Set ℝ) := by
      simp [frontier, closure_Ici]
    rw [hfront]
    haveI : NoAtoms standardNormalMeasure :=
      ProbabilityTheory.noAtoms_gaussianReal (μ := 0) (v := (1 : ℝ≥0)) (by norm_num)
    ext
    simp [standardNormalProbability]
  have h_nn :
      Tendsto
        (fun N : ℕ =>
          (lawOf (μ := μ) (normalizedSum X m σ N) (hZ N) : ProbabilityMeasure ℝ)
            (Set.Ici t))
        atTop
        (𝓝 ((standardNormalProbability : ProbabilityMeasure ℝ) (Set.Ici t))) :=
    MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      hCLT h_cont
  exact (NNReal.continuous_coe.tendsto _).comp h_nn

/-- CLT tail limit written with the standard normal density integral. -/
theorem centralLimit_tail_tendsto_integral
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    {hZ : ∀ N, AEMeasurable (normalizedSum X m σ N) μ}
    (hCLT : centralLimitConclusion (μ := μ) X m σ hZ)
    (t : ℝ) :
    Tendsto
      (fun N : ℕ =>
        (((lawOf (μ := μ) (normalizedSum X m σ N) (hZ N) : ProbabilityMeasure ℝ)
          (Set.Ici t) : ℝ≥0) : ℝ))
      atTop
      (𝓝 (∫ x in Set.Ici t, standardNormalDensity x)) := by
  have htail :=
    centralLimit_tail_tendsto
      (μ := μ) (X := X) (m := m) (σ := σ) hCLT t
  have htarget :
      ((((standardNormalProbability : ProbabilityMeasure ℝ)
        (Set.Ici t) : ℝ≥0) : ℝ)) =
        ∫ x in Set.Ici t, standardNormalDensity x := by
    have h_nonneg :
        0 ≤ ∫ x in Set.Ici t, standardNormalDensity x := by
      exact integral_nonneg fun x =>
        ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x
    change (standardNormalMeasure (Set.Ici t)).toReal =
      ∫ x in Set.Ici t, standardNormalDensity x
    rw [standardNormal_tail_eq_integral t]
    exact ENNReal.toReal_ofReal h_nonneg
  simpa [htarget] using htail

/-- Book-style hypotheses for HDP Theorem 1.3.2, the Lindeberg-Levy CLT.
This structure deliberately contains only assumptions, not the conclusion. -/
structure LindebergLevyCLTHypotheses [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (m σ : ℝ) : Prop where
  aemeasurable : ∀ i, AEMeasurable (X i) μ
  integrable_zero : Integrable (X 0) μ
  square_integrable_zero : MemLp (X 0) 2 μ
  independent : iIndepFun X μ
  identDistrib : ∀ i, IdentDistrib (X i) (X 0) μ μ
  mean_eq : μ[X 0] = m
  variance_eq : Var[X 0; μ] = σ ^ 2
  sigma_pos : 0 < σ

/-- Characteristic-function form of HDP Theorem 1.3.2, proved from the
book-style hypotheses by the characteristic-function Taylor theorem. -/
theorem lindebergLevyCentralLimitTheorem_characteristicFunction_of_hypotheses
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (h : LindebergLevyCLTHypotheses (μ := μ) X m σ) :
    centralLimitCharacteristicFunctionConclusion (μ := μ) X m σ :=
  lindebergLevyCentralLimitTheorem_characteristicFunction
    (μ := μ) h.aemeasurable h.integrable_zero h.square_integrable_zero
    h.independent h.identDistrib h.mean_eq h.variance_eq h.sigma_pos

/-- Genuine Lindeberg-Levy CLT: i.i.d. real random variables with finite
second moment, mean `m`, and variance `σ²`, with `σ > 0`, have normalized sums
converging in distribution to the standard normal law. -/
theorem lindebergLevyCentralLimitTheorem
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (h : LindebergLevyCLTHypotheses (μ := μ) X m σ) :
    centralLimitConclusion
      (μ := μ) X m σ
      (normalizedSum_aemeasurable (μ := μ) h.aemeasurable) :=
  centralLimitConclusion_of_characteristicFunction
    (μ := μ)
    (X := X)
    (m := m)
    (σ := σ)
    (normalizedSum_aemeasurable (μ := μ) h.aemeasurable)
    (lindebergLevyCentralLimitTheorem_characteristicFunction_of_hypotheses
      (μ := μ) h)

/-- The convergence-in-distribution proposition stated by HDP Theorem 1.3.2. -/
def lindebergLevyCentralLimitTheoremStatement [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (m σ : ℝ) : Prop :=
  ∀ h : LindebergLevyCLTHypotheses (μ := μ) X m σ,
    centralLimitConclusion
      (μ := μ) X m σ
      (normalizedSum_aemeasurable (μ := μ) h.aemeasurable)

end GaussianLimit

section BernoulliBinomialPoisson

/-- Bernoulli distribution on `{0,1}`, represented as a PMF on `ℕ`. -/
def bernoulliNatPMF (p : ℝ≥0) (hp : p ≤ 1) : PMF ℕ :=
  (PMF.bernoulli p hp).map fun b => if b then 1 else 0

/-- Bernoulli point probability at `1`. -/
@[simp]
theorem bernoulliNatPMF_apply_one
    {p : ℝ≥0} {hp : p ≤ 1} :
    bernoulliNatPMF p hp 1 = p := by
  simp [bernoulliNatPMF, PMF.map_apply, PMF.bernoulli_apply]

/-- Bernoulli point probability at `0`. -/
@[simp]
theorem bernoulliNatPMF_apply_zero
    {p : ℝ≥0} {hp : p ≤ 1} :
    bernoulliNatPMF p hp 0 = 1 - p := by
  simp [bernoulliNatPMF, PMF.map_apply, PMF.bernoulli_apply]

/-- Bernoulli point probability away from `{0,1}`. -/
@[simp]
theorem bernoulliNatPMF_apply_of_ne_zero_one
    {p : ℝ≥0} {hp : p ≤ 1} {k : ℕ}
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    bernoulliNatPMF p hp k = 0 := by
  simp [bernoulliNatPMF, PMF.map_apply, PMF.bernoulli_apply, hk0, hk1]

/-- If a natural-valued random variable has Bernoulli law, then
`P{X = 1} = p`. -/
theorem measureReal_eq_one_of_hasLaw_bernoulliNatPMF
    [IsProbabilityMeasure μ]
    {X : Ω → ℕ}
    {p : ℝ≥0} {hp : p ≤ 1}
    (hX : HasLaw X ((bernoulliNatPMF p hp).toMeasure) μ) :
    μ.real {ω | X ω = 1} = (p : ℝ) := by
  have hpre :
      μ {ω | X ω = 1} =
        ((bernoulliNatPMF p hp).toMeasure) ({1} : Set ℕ) := by
    rw [← hX.map_eq]
    exact (Measure.map_apply_of_aemeasurable hX.aemeasurable
      (measurableSet_singleton (1 : ℕ))).symm
  rw [measureReal_def, hpre]
  rw [PMF.toMeasure_apply_singleton]
  · simp [bernoulliNatPMF_apply_one]
  · exact measurableSet_singleton (1 : ℕ)

/-- If a natural-valued random variable has Bernoulli law, then
`P{X = 0} = 1 - p`. -/
theorem measureReal_eq_zero_of_hasLaw_bernoulliNatPMF
    [IsProbabilityMeasure μ]
    {X : Ω → ℕ}
    {p : ℝ≥0} {hp : p ≤ 1}
    (hX : HasLaw X ((bernoulliNatPMF p hp).toMeasure) μ) :
    μ.real {ω | X ω = 0} = ((1 - p : ℝ≥0) : ℝ) := by
  have hpre :
      μ {ω | X ω = 0} =
        ((bernoulliNatPMF p hp).toMeasure) ({0} : Set ℕ) := by
    rw [← hX.map_eq]
    exact (Measure.map_apply_of_aemeasurable hX.aemeasurable
      (measurableSet_singleton (0 : ℕ))).symm
  rw [measureReal_def, hpre]
  rw [PMF.toMeasure_apply_singleton]
  · rw [bernoulliNatPMF_apply_zero]
    have hcoe :
        (1 : ℝ≥0∞) - (p : ℝ≥0∞) =
          ((1 - p : ℝ≥0) : ℝ≥0∞) := by
      simp
    change ((1 : ℝ≥0∞) - (p : ℝ≥0∞)).toReal =
      (((1 - p : ℝ≥0) : ℝ≥0∞).toReal)
    exact congrArg ENNReal.toReal hcoe
  · exact measurableSet_singleton (0 : ℕ)

/-- A natural-valued Bernoulli random variable is a.e. supported on `{0,1}`. -/
theorem ae_eq_zero_or_one_of_hasLaw_bernoulliNatPMF
    [IsProbabilityMeasure μ]
    {X : Ω → ℕ}
    {p : ℝ≥0} {hp : p ≤ 1}
    (hX : HasLaw X ((bernoulliNatPMF p hp).toMeasure) μ) :
    ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1 := by
  have hsupport_law :
      ∀ᵐ k ∂((bernoulliNatPMF p hp).toMeasure), k = 0 ∨ k = 1 := by
    rw [ae_iff_of_countable]
    intro k hk
    by_contra hbad
    have hk0 : k ≠ 0 := fun h0 => hbad (Or.inl h0)
    have hk1 : k ≠ 1 := fun h1 => hbad (Or.inr h1)
    have hzero :
        ((bernoulliNatPMF p hp).toMeasure) ({k} : Set ℕ) = 0 := by
      rw [PMF.toMeasure_apply_singleton]
      · simp [bernoulliNatPMF_apply_of_ne_zero_one hk0 hk1]
      · exact measurableSet_singleton k
    exact hk hzero
  exact
    (hX.ae_iff (p := fun k : ℕ => k = 0 ∨ k = 1) (by fun_prop)).mpr
      hsupport_law

private def bernoulliTrialWeight (p : ℝ≥0) (N : ℕ) (f : Fin N → Bool) :
    ℝ≥0∞ :=
  ∏ i : Fin N, if f i then (p : ℝ≥0∞) else (1 - p : ℝ≥0∞)

private theorem bernoulliTrialWeight_sum_eq_one
    (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) :
    (∑ f : Fin N → Bool, bernoulliTrialWeight p N f) = 1 := by
  classical
  calc
    (∑ f : Fin N → Bool, bernoulliTrialWeight p N f)
        =
      ∏ _i : Fin N, ∑ b : Bool,
        (if b then (p : ℝ≥0∞) else (1 - p : ℝ≥0∞)) := by
          exact
            (Fintype.prod_sum fun (_i : Fin N) (b : Bool) =>
              if b then (p : ℝ≥0∞) else (1 - p : ℝ≥0∞)).symm
    _ = 1 := by
      have hsub : (p : ℝ≥0∞) + (1 - p : ℝ≥0∞) = 1 := by
        norm_cast
        exact add_tsub_cancel_of_le hp
      simp [hsub]

/-- Product law of `N` independent Bernoulli trials, represented as Boolean
vectors. -/
def bernoulliTrialVectorPMF
    (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) : PMF (Fin N → Bool) :=
  PMF.ofFintype (bernoulliTrialWeight p N)
    (bernoulliTrialWeight_sum_eq_one p hp N)

/-- Number of successes in a Boolean vector of Bernoulli trials. -/
def bernoulliSuccessCount (N : ℕ) (f : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun i => f i).card

/-- Number of successes as an element of `Fin (N + 1)`, used to compare
directly with mathlib's finite-support binomial PMF. -/
def bernoulliSuccessCountFin (N : ℕ) (f : Fin N → Bool) :
    Fin (N + 1) :=
  ⟨bernoulliSuccessCount N f, by
    unfold bernoulliSuccessCount
    exact Nat.lt_succ_of_le (by simpa [Fintype.card_fin] using
      (Finset.card_le_univ (Finset.univ.filter fun i : Fin N => f i)))⟩

private theorem bernoulliTrialWeight_eq_successCount
    (p : ℝ≥0) (N : ℕ) (f : Fin N → Bool) :
    bernoulliTrialWeight p N f =
      (p : ℝ≥0∞) ^ bernoulliSuccessCount N f *
        (1 - p : ℝ≥0∞) ^ (N - bernoulliSuccessCount N f) := by
  classical
  unfold bernoulliTrialWeight bernoulliSuccessCount
  rw [Finset.prod_ite]
  have hcard :
      (Finset.univ.filter fun i : Fin N => f i = false).card =
        N - (Finset.univ.filter fun i : Fin N => f i).card := by
    have h :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin N))) (p := fun i => f i = true)
    have hcard_univ : (Finset.univ : Finset (Fin N)).card = N := by
      simp
    have hsum :
        (Finset.univ.filter fun i : Fin N => f i = true).card +
          (Finset.univ.filter fun i : Fin N => f i = false).card = N := by
      simpa [hcard_univ] using h
    omega
  simp [hcard]

private theorem bernoulliSuccessCount_fiber_card (N k : ℕ) :
    Fintype.card {f : Fin N → Bool // bernoulliSuccessCount N f = k} =
      N.choose k := by
  classical
  unfold bernoulliSuccessCount
  let e :
      {f : Fin N → Bool // (Finset.univ.filter fun i => f i).card = k} ≃
        {s : Finset (Fin N) // s.card = k} :=
    { toFun := fun f => ⟨Finset.univ.filter fun i => f.1 i, f.2⟩
      invFun := fun s => ⟨fun i => i ∈ s.1, by
        have hfilter :
            (Finset.univ.filter fun i : Fin N => i ∈ s.1) = s.1 := by
          ext i
          simp
        simpa [hfilter] using s.2⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        simp
      right_inv := by
        intro s
        apply Subtype.ext
        ext i
        simp }
  calc
    Fintype.card
        {f : Fin N → Bool // (Finset.univ.filter fun i => f i).card = k}
        = Fintype.card {s : Finset (Fin N) // s.card = k} :=
          Fintype.card_congr e
    _ = N.choose k := by
      rw [Fintype.card_finset_len]
      simp

/-- HDP Section 1.3: the number of successes in `N` independent Bernoulli
trials has binomial law. This is the PMF-level version, with the success count
as an element of `Fin (N + 1)`. -/
theorem bernoulliTrialVectorPMF_map_successCountFin_eq_binomial
    (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) :
    (bernoulliTrialVectorPMF p hp N).map (bernoulliSuccessCountFin N) =
      PMF.binomial p hp N := by
  classical
  ext i
  rw [bernoulliTrialVectorPMF, PMF.map_ofFintype]
  simp only [PMF.ofFintype_apply]
  rw [PMF.binomial_apply]
  let k := (i : ℕ)
  have hfiber_const :
      ∀ f : Fin N → Bool,
        bernoulliSuccessCountFin N f = i →
          bernoulliTrialWeight p N f =
            (p : ℝ≥0∞) ^ (i : ℕ) *
              (1 - p : ℝ≥0∞) ^ (N - (i : ℕ)) := by
    intro f hf
    have hcount : bernoulliSuccessCount N f = (i : ℕ) :=
      congrArg Fin.val hf
    rw [bernoulliTrialWeight_eq_successCount, hcount]
  have hsum :
      (∑ f with bernoulliSuccessCountFin N f = i,
          bernoulliTrialWeight p N f) =
        ((Finset.univ.filter fun f : Fin N → Bool =>
          bernoulliSuccessCountFin N f = i).card : ℕ) •
          ((p : ℝ≥0∞) ^ (i : ℕ) *
            (1 - p : ℝ≥0∞) ^ (N - (i : ℕ))) := by
    calc
      (∑ f with bernoulliSuccessCountFin N f = i,
          bernoulliTrialWeight p N f)
          =
        ∑ f with bernoulliSuccessCountFin N f = i,
          ((p : ℝ≥0∞) ^ (i : ℕ) *
            (1 - p : ℝ≥0∞) ^ (N - (i : ℕ))) := by
            refine Finset.sum_congr rfl ?_
            intro f hf
            exact hfiber_const f (by simpa using hf)
      _ =
        ((Finset.univ.filter fun f : Fin N → Bool =>
          bernoulliSuccessCountFin N f = i).card : ℕ) •
          ((p : ℝ≥0∞) ^ (i : ℕ) *
            (1 - p : ℝ≥0∞) ^ (N - (i : ℕ))) := by
            rw [Finset.sum_const]
  have hcard :
      (Finset.univ.filter fun f : Fin N → Bool =>
          bernoulliSuccessCountFin N f = i).card =
        N.choose (i : ℕ) := by
    have hfilter :
        (Finset.univ.filter fun f : Fin N → Bool =>
            bernoulliSuccessCountFin N f = i) =
          (Finset.univ.filter fun f : Fin N → Bool =>
            bernoulliSuccessCount N f = (i : ℕ)) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact congrArg Fin.val h
      · intro h
        apply Fin.ext
        exact h
    rw [hfilter]
    have hcardSubtype := bernoulliSuccessCount_fiber_card N (i : ℕ)
    rwa [Fintype.card_subtype] at hcardSubtype
  have htarget :
      ((Finset.univ.filter fun f : Fin N → Bool =>
          bernoulliSuccessCountFin N f = i).card : ℕ) •
          ((p : ℝ≥0∞) ^ (i : ℕ) *
            (1 - p : ℝ≥0∞) ^ (N - (i : ℕ))) =
        (p : ℝ≥0∞) ^ (i : ℕ) *
          (1 - p : ℝ≥0∞) ^ (N - (i : ℕ)) *
          (N.choose (i : ℕ) : ℝ≥0∞) := by
    rw [hcard]
    simp [nsmul_eq_mul, mul_comm, mul_left_comm]
  convert hsum.trans htarget using 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp

/-- A real-valued Bernoulli random variable has expectation `p`. -/
theorem integral_eq_of_real_bernoulli
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    {p : ℝ}
    (hX_meas : Measurable X)
    (h0_or_1 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1)
    (hprob_one : μ.real {ω | X ω = 1} = p) :
    μ[X] = p := by
  have hset : MeasurableSet {ω | X ω = 1} :=
    hX_meas (measurableSet_singleton (1 : ℝ))
  have h_indicator :
      X =ᵐ[μ] fun ω =>
        ({ω | X ω = 1}.indicator (fun _ => (1 : ℝ)) ω) := by
    filter_upwards [h0_or_1] with ω hω
    rcases hω with hzero | hone
    · simp [Set.indicator, hzero]
    · simp [Set.indicator, hone]
  calc
    μ[X]
        =
      μ[fun ω => ({ω | X ω = 1}.indicator (fun _ => (1 : ℝ)) ω)] :=
        integral_congr_ae
          (μ := μ) (f := X)
          (g := fun ω => ({ω | X ω = 1}.indicator (fun _ => (1 : ℝ)) ω))
          h_indicator
    _ = μ.real {ω | X ω = 1} := by
        simp [hset]
    _ = p := hprob_one

/-- A real-valued Bernoulli random variable has variance `p(1-p)`. -/
theorem variance_eq_of_real_bernoulli
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    {p : ℝ}
    (hX_meas : Measurable X)
    (hX_l2 : MemLp X 2 μ)
    (h0_or_1 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1)
    (hprob_one : μ.real {ω | X ω = 1} = p) :
    Var[X; μ] = p * (1 - p) := by
  have hX_int : Integrable X μ :=
    hX_l2.integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hEX :
      μ[X] = p :=
    integral_eq_of_real_bernoulli
      (μ := μ) (X := X) hX_meas h0_or_1 hprob_one
  have hsq_ae : (fun ω => X ω ^ 2) =ᵐ[μ] X := by
    filter_upwards [h0_or_1] with ω hω
    rcases hω with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hEX2 : μ[fun ω => X ω ^ 2] = p := by
    calc
      μ[fun ω => X ω ^ 2] = μ[X] :=
        integral_congr_ae
          (μ := μ) (f := fun ω => X ω ^ 2) (g := X) hsq_ae
      _ = p := hEX
  calc
    Var[X; μ]
        = μ[fun ω => X ω ^ 2] - μ[X] ^ 2 :=
          ProbabilityTheory.variance_eq_sub hX_l2
    _ = p - p ^ 2 := by rw [hEX2, hEX]
    _ = p * (1 - p) := by ring

/-- A natural-valued Bernoulli random variable has expectation `p` after
coercion to `ℝ`. -/
theorem integral_coe_nat_eq_of_hasLaw_bernoulliNatPMF
    [IsProbabilityMeasure μ]
    {X : Ω → ℕ}
    {p : ℝ≥0} {hp : p ≤ 1}
    (hX_meas : Measurable X)
    (hX_law : HasLaw X ((bernoulliNatPMF p hp).toMeasure) μ) :
    μ[fun ω => (X ω : ℝ)] = (p : ℝ) := by
  have hprob_one :
      μ.real {ω | X ω = 1} = (p : ℝ) :=
    measureReal_eq_one_of_hasLaw_bernoulliNatPMF (μ := μ) (X := X) hX_law
  have hprob_one_real :
      μ.real {ω | (X ω : ℝ) = 1} = (p : ℝ) := by
    have hset : {ω | (X ω : ℝ) = 1} = {ω | X ω = 1} := by
      ext ω
      exact Nat.cast_eq_one
    simpa [hset] using hprob_one
  have h0_or_1_real :
      ∀ᵐ ω ∂μ, (X ω : ℝ) = 0 ∨ (X ω : ℝ) = 1 := by
    filter_upwards
      [ae_eq_zero_or_one_of_hasLaw_bernoulliNatPMF
        (μ := μ) (X := X) hX_law] with ω hω
    rcases hω with h0 | h1
    · left
      simp [h0]
    · right
      simp [h1]
  exact
    integral_eq_of_real_bernoulli
      (μ := μ) (X := fun ω => (X ω : ℝ))
      (by fun_prop) h0_or_1_real hprob_one_real

/-- A natural-valued Bernoulli random variable is square-integrable after
coercion to `ℝ`. -/
theorem memLp_coe_nat_of_hasLaw_bernoulliNatPMF
    [IsProbabilityMeasure μ]
    {X : Ω → ℕ}
    {p : ℝ≥0} {hp : p ≤ 1}
    (hX_meas : Measurable X)
    (hX_law : HasLaw X ((bernoulliNatPMF p hp).toMeasure) μ) :
    MemLp (fun ω => (X ω : ℝ)) 2 μ := by
  have hset : MeasurableSet {ω | X ω = 1} :=
    hX_meas (measurableSet_singleton (1 : ℕ))
  have h_indicator :
      (fun ω => ({ω | X ω = 1}.indicator (fun _ => (1 : ℝ)) ω))
        =ᵐ[μ] fun ω => (X ω : ℝ) := by
    filter_upwards
      [ae_eq_zero_or_one_of_hasLaw_bernoulliNatPMF
        (μ := μ) (X := X) hX_law] with ω hω
    rcases hω with h0 | h1
    · simp [Set.indicator, h0]
    · simp [Set.indicator, h1]
  exact
    (memLp_indicator_const (p := (2 : ℝ≥0∞)) hset (1 : ℝ)
      (Or.inr (measure_ne_top μ {ω | X ω = 1}))).ae_eq h_indicator

/-- A natural-valued Bernoulli random variable has variance `p(1-p)` after
coercion to `ℝ`. -/
theorem variance_coe_nat_eq_of_hasLaw_bernoulliNatPMF
    [IsProbabilityMeasure μ]
    {X : Ω → ℕ}
    {p : ℝ≥0} {hp : p ≤ 1}
    (hX_meas : Measurable X)
    (hX_law : HasLaw X ((bernoulliNatPMF p hp).toMeasure) μ) :
    Var[(fun ω => (X ω : ℝ)); μ] =
      (p : ℝ) * (1 - (p : ℝ)) := by
  have hprob_one :
      μ.real {ω | X ω = 1} = (p : ℝ) :=
    measureReal_eq_one_of_hasLaw_bernoulliNatPMF (μ := μ) (X := X) hX_law
  have hprob_one_real :
      μ.real {ω | (X ω : ℝ) = 1} = (p : ℝ) := by
    have hset : {ω | (X ω : ℝ) = 1} = {ω | X ω = 1} := by
      ext ω
      exact Nat.cast_eq_one
    simpa [hset] using hprob_one
  have h0_or_1_real :
      ∀ᵐ ω ∂μ, (X ω : ℝ) = 0 ∨ (X ω : ℝ) = 1 := by
    filter_upwards
      [ae_eq_zero_or_one_of_hasLaw_bernoulliNatPMF
        (μ := μ) (X := X) hX_law] with ω hω
    rcases hω with h0 | h1
    · left
      simp [h0]
    · right
      simp [h1]
  exact
    variance_eq_of_real_bernoulli
      (μ := μ) (X := fun ω => (X ω : ℝ))
      (p := (p : ℝ)) (by fun_prop)
      (memLp_coe_nat_of_hasLaw_bernoulliNatPMF
        (μ := μ) (X := X) hX_meas hX_law)
      h0_or_1_real hprob_one_real

/-- Binomial distribution `Binom(N,p)`, represented as a PMF on `ℕ`. -/
def binomialNatPMF (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) : PMF ℕ :=
  (PMF.binomial p hp N).map fun i : Fin (N + 1) => (i : ℕ)

/-- Distribution of the number of successes in `N` independent Bernoulli
trials, represented as a PMF on `ℕ`. -/
def bernoulliSumPMF (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) : PMF ℕ :=
  (bernoulliTrialVectorPMF p hp N).map (bernoulliSuccessCount N)

/-- HDP Section 1.3: the sum of `N` independent Bernoulli variables with
common parameter `p` has binomial law. -/
theorem bernoulliSumPMF_eq_binomialNatPMF
    (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) :
    bernoulliSumPMF p hp N = binomialNatPMF p hp N := by
  unfold bernoulliSumPMF binomialNatPMF
  have hcomp :
      ((fun i : Fin (N + 1) => (i : ℕ)) ∘ bernoulliSuccessCountFin N) =
        bernoulliSuccessCount N := by
    funext f
    rfl
  rw [← hcomp]
  rw [← PMF.map_comp]
  rw [bernoulliTrialVectorPMF_map_successCountFin_eq_binomial]

/-- The Boolean Bernoulli trial-vector PMF is the finite product of the
one-dimensional Boolean Bernoulli laws. -/
theorem bernoulliTrialVectorPMF_toMeasure_eq_pi
    (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) :
    (bernoulliTrialVectorPMF p hp N).toMeasure =
      Measure.pi (fun _ : Fin N => (PMF.bernoulli p hp).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.pi_singleton]
  rw [PMF.toMeasure_apply_singleton]
  · simp only [bernoulliTrialVectorPMF, PMF.ofFintype_apply,
      bernoulliTrialWeight]
    refine Finset.prod_congr rfl ?_
    intro i _hi
    by_cases hfi : f i
    · simp [hfi]
    · have hcoe :
          (1 : ℝ≥0∞) - (p : ℝ≥0∞) =
            ((1 - p : ℝ≥0) : ℝ≥0∞) := by
        simp
      simp [hfi]
  · exact measurableSet_singleton f

/-- Product Bernoulli trials as an `ℕ`-valued vector. -/
def bernoulliNatVectorPMF
    (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) : PMF (Fin N → ℕ) :=
  (bernoulliTrialVectorPMF p hp N).map
    fun f i => if f i then 1 else 0

private lemma sum_bool_indicator_eq_successCount
    {N : ℕ} (f : Fin N → Bool) :
    (∑ i : Fin N, if f i then (1 : ℕ) else 0) =
      bernoulliSuccessCount N f := by
  classical
  unfold bernoulliSuccessCount
  rw [← Finset.sum_filter]
  simp

/-- The `ℕ`-valued Bernoulli vector PMF is the finite product of the
one-dimensional `ℕ`-valued Bernoulli laws. -/
theorem bernoulliNatVectorPMF_toMeasure_eq_pi
    (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) :
    (bernoulliNatVectorPMF p hp N).toMeasure =
      Measure.pi (fun _ : Fin N => (bernoulliNatPMF p hp).toMeasure) := by
  classical
  let natTrial : (Fin N → Bool) → (Fin N → ℕ) :=
    fun f i => if f i then 1 else 0
  have hnatTrial_meas : Measurable natTrial :=
    measurable_of_countable _
  have hcoord_meas :
      ∀ i : Fin N,
        AEMeasurable
          (fun b : Bool => if b then (1 : ℕ) else 0)
          ((PMF.bernoulli p hp).toMeasure) :=
    fun _ => (measurable_of_countable _).aemeasurable
  unfold bernoulliNatVectorPMF
  change ((bernoulliTrialVectorPMF p hp N).map natTrial).toMeasure =
    Measure.pi (fun _ : Fin N => (bernoulliNatPMF p hp).toMeasure)
  rw [← PMF.toMeasure_map natTrial
    (bernoulliTrialVectorPMF p hp N) hnatTrial_meas]
  rw [bernoulliTrialVectorPMF_toMeasure_eq_pi p hp N]
  change
    Measure.map
        (fun f : Fin N → Bool => fun i : Fin N => if f i then (1 : ℕ) else 0)
        (Measure.pi (fun _ : Fin N => (PMF.bernoulli p hp).toMeasure)) =
      Measure.pi (fun _ : Fin N => (bernoulliNatPMF p hp).toMeasure)
  rw [Measure.pi_map_pi hcoord_meas]
  congr with i
  rw [PMF.toMeasure_map]
  · rfl
  · exact measurable_of_countable _

/-- PMF-level bridge: the sum of the `ℕ`-valued Bernoulli trial vector has
binomial PMF. -/
theorem bernoulliNatVectorPMF_map_sum_eq_binomialNatPMF
    (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) :
    (bernoulliNatVectorPMF p hp N).map
      (fun x : Fin N → ℕ => ∑ i : Fin N, x i)
      =
    binomialNatPMF p hp N := by
  classical
  unfold bernoulliNatVectorPMF
  rw [PMF.map_comp]
  change
    (bernoulliTrialVectorPMF p hp N).map
      (fun f : Fin N → Bool => ∑ i : Fin N, if f i then (1 : ℕ) else 0)
      =
    binomialNatPMF p hp N
  simpa [sum_bool_indicator_eq_successCount] using
    bernoulliSumPMF_eq_binomialNatPMF p hp N

/-- If the joint law of Bernoulli variables is the Bernoulli product-vector
PMF, then the sum has binomial law. -/
theorem hasLaw_sum_bernoulliNatPMF_eq_binomialNatPMF_of_jointLaw
    [IsProbabilityMeasure μ]
    {N : ℕ}
    {p : ℝ≥0} {hp : p ≤ 1}
    {X : Fin N → Ω → ℕ}
    (hjoint :
      HasLaw
        (fun ω => fun i : Fin N => X i ω)
        ((bernoulliNatVectorPMF p hp N).toMeasure)
        μ) :
    HasLaw
      (fun ω => ∑ i : Fin N, X i ω)
      ((binomialNatPMF p hp N).toMeasure)
      μ := by
  classical
  let sumFn : (Fin N → ℕ) → ℕ :=
    fun x => ∑ i : Fin N, x i
  have hsum_under_vector_law :
      HasLaw sumFn
        ((binomialNatPMF p hp N).toMeasure)
        ((bernoulliNatVectorPMF p hp N).toMeasure) := by
    refine ⟨(measurable_of_countable sumFn).aemeasurable, ?_⟩
    change
      Measure.map sumFn ((bernoulliNatVectorPMF p hp N).toMeasure)
        =
      (binomialNatPMF p hp N).toMeasure
    rw [PMF.toMeasure_map sumFn
      (bernoulliNatVectorPMF p hp N) (measurable_of_countable sumFn)]
    rw [bernoulliNatVectorPMF_map_sum_eq_binomialNatPMF]
  simpa [sumFn, Function.comp_def] using hsum_under_vector_law.comp hjoint

/-- HDP Section 1.3: the sum of mutually independent Bernoulli random
variables has binomial law.

The hypothesis is `iIndepFun`, not pairwise independence, because the law of a
sum of three or more Bernoulli variables is determined by the joint product law. -/
theorem hasLaw_sum_bernoulliNatPMF_eq_binomialNatPMF
    [IsProbabilityMeasure μ]
    {N : ℕ}
    {p : ℝ≥0} {hp : p ≤ 1}
    {X : Fin N → Ω → ℕ}
    (hindep : iIndepFun X μ)
    (hbernoulli :
      ∀ i : Fin N,
        HasLaw (X i) ((bernoulliNatPMF p hp).toMeasure) μ) :
    HasLaw
      (fun ω => ∑ i : Fin N, X i ω)
      ((binomialNatPMF p hp N).toMeasure)
      μ := by
  classical
  have hvec_product :
      HasLaw
        (fun ω => fun i : Fin N => X i ω)
        (Measure.pi fun _ : Fin N => (bernoulliNatPMF p hp).toMeasure)
        μ := by
    refine ⟨aemeasurable_pi_lambda _ fun i => (hbernoulli i).aemeasurable, ?_⟩
    rw [(iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin N => (hbernoulli i).aemeasurable)).mp hindep]
    congr with i s
    rw [(hbernoulli i).map_eq]
  have hjoint :
      HasLaw
        (fun ω => fun i : Fin N => X i ω)
        ((bernoulliNatVectorPMF p hp N).toMeasure)
        μ := by
    refine ⟨hvec_product.aemeasurable, ?_⟩
    rw [hvec_product.map_eq, bernoulliNatVectorPMF_toMeasure_eq_pi p hp N]
  exact
    hasLaw_sum_bernoulliNatPMF_eq_binomialNatPMF_of_jointLaw
      (μ := μ) (p := p) (hp := hp) (X := X) hjoint

/-- Poisson point probability from HDP (1.8). -/
def poissonPointProbability (lam : ℝ≥0) (k : ℕ) : ℝ :=
  Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ k / (Nat.factorial k)

@[simp]
lemma poissonPointProbability_eq (lam : ℝ≥0) (k : ℕ) :
    poissonPointProbability lam k =
      Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ k / (Nat.factorial k) := rfl

/-- Poisson distribution as a probability measure on `ℕ`. -/
def poissonProbabilityMeasure (lam : ℝ≥0) : ProbabilityMeasure ℕ :=
  ⟨ProbabilityTheory.poissonMeasure lam, inferInstance⟩

/-- The Poisson probability measure gives the point mass from HDP (1.8). -/
theorem poissonProbabilityMeasure_singleton
    (lam : ℝ≥0) (k : ℕ) :
    (poissonProbabilityMeasure lam : Measure ℕ) {k}
      =
    ENNReal.ofReal
      (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ k / Nat.factorial k) := by
  simpa [poissonProbabilityMeasure] using
    ProbabilityTheory.poissonMeasure_singleton lam k

/-- Row sum `S_N = ∑_{i < N} X_{N,i}` for the Poisson limit theorem. -/
def poissonTriangularSum (X : ℕ → ℕ → Ω → ℕ) (N : ℕ) (ω : Ω) : ℕ :=
  ∑ i ∈ Finset.range N, X N i ω

/-- Sum of the Bernoulli parameters in row `N`. -/
def rowParameterSum (p : ℕ → ℕ → ℝ≥0) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, (p N i : ℝ)

/-- Maximum Bernoulli parameter in row `N`. -/
def rowParameterMax (p : ℕ → ℕ → ℝ≥0) (N : ℕ) : ℝ≥0 :=
  (Finset.range N).sup (p N)

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PoissonLimitAux

open Finset

/-- Real-valued Bernoulli point mass on `ℕ`, used by the Poisson-binomial
asymptotic proof. -/
def bernoulliPMFReal (p : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 - p else if k = 1 then p else 0

/-- Real-valued Poisson point mass. -/
def poissonPMFReal (lam : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-lam) * lam ^ k / k.factorial

/-- The row sum `S_N = ∑ᵢ X_{N,i}`. -/
def rowSum
    {Ω : ℕ → Type*}
    (X : (N : ℕ) → Fin N → Ω N → ℕ)
    (N : ℕ) : Ω N → ℕ :=
  fun ω => ∑ i : Fin N, X N i ω

/-- The row maximum `max_{i≤N} p_{N,i}`, with value `0` for the empty row. -/
def rowMax
    (p : (N : ℕ) → Fin N → ℝ)
    (N : ℕ) : ℝ :=
  if h : 0 < N then
    Finset.sup' Finset.univ ⟨⟨0, h⟩, Finset.mem_univ _⟩ (fun i : Fin N => p N i)
  else 0

/-! ## Combinatorial definitions -/

/-- The combinatorial formula for the sum of independent Bernoullis. -/
def bernoulliSumProb {N : ℕ} (p : Fin N → ℝ) (k : ℕ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
    (∏ i ∈ A, p i) * ∏ i ∈ (Finset.univ \ A), (1 - p i)

/-- The k-th elementary symmetric polynomial. -/
def esymm {N : ℕ} (x : Fin N → ℝ) (k : ℕ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
    ∏ i ∈ A, x i

/-! ## Elementary symmetric polynomial bounds -/

lemma esymm_nonneg {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) (k : ℕ) :
    0 ≤ esymm x k := by
  exact Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => hx _

lemma factorial_mul_esymm_le_sum_pow {N : ℕ} (x : Fin N → ℝ)
    (hx : ∀ i, 0 ≤ x i) (k : ℕ) :
    (k.factorial : ℝ) * esymm x k ≤ (∑ i : Fin N, x i) ^ k := by
  set F := (Fin k → Fin N) with hF_def
  set S := {f : F | Function.Injective f} with hS_def
  have hS_card : ∑ f ∈ Finset.univ.filter (fun f : F => Function.Injective f),
      (∏ i, x (f i)) = k.factorial * esymm x k := by
    have h_subset_prod :
        ∀ A ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)),
          ∑ f ∈ Finset.filter
              (fun f : F => Function.Injective f ∧ Finset.image f Finset.univ = A)
              Finset.univ,
            (∏ i, x (f i)) =
              k.factorial * (∏ i ∈ A, x i) := by
      intro A hA
      have h_subset_prod : ∀ f : F,
          Function.Injective f ∧ Finset.image f Finset.univ = A →
            (∏ i, x (f i)) = (∏ i ∈ A, x i) := by
        intro f hf
        rw [← hf.2, Finset.prod_image (by tauto)]
      rw [Finset.sum_congr rfl fun f hf => h_subset_prod f <| Finset.mem_filter.mp hf |>.2]
      norm_num [Finset.mem_powersetCard.mp hA]
      ring_nf
      have h_inj_count :
          Finset.card (Finset.filter
              (fun f : Fin k → Fin N =>
                Function.Injective f ∧ Finset.image f Finset.univ = A)
              Finset.univ) =
            Finset.card (Finset.image
              (fun f : Fin k ≃ A => fun i => (f i : Fin N))
              (Finset.univ : Finset (Fin k ≃ A))) := by
        congr with f
        simp +decide [Function.Injective, Finset.ext_iff]
        constructor <;> intro h
        · have h_equiv : ∃ a : Fin k ≃ A, ∀ i, a i = f i := by
            have h_image : Finset.image f Finset.univ = A := by
              ext
              simp [h]
            exact ⟨Equiv.ofBijective (fun i => ⟨f i, by aesop⟩)
              ⟨fun i j hij => h.1 <| by aesop, fun i => by aesop⟩,
              fun i => rfl⟩
          exact ⟨h_equiv.choose, funext h_equiv.choose_spec⟩
        · rcases h with ⟨a, rfl⟩
          simp +decide [Function.Injective, Finset.mem_image]
          exact fun i => ⟨fun ⟨j, hj⟩ => hj ▸ Subtype.mem _, fun hi =>
            ⟨a.symm ⟨i, hi⟩, by simp +decide⟩⟩
      rw [h_inj_count, Finset.card_image_of_injective] <;> norm_num [Function.Injective]
      · rw [Fintype.card_equiv]
        aesop
        exact Fintype.equivOfCardEq (by simp +decide [Finset.mem_powersetCard.mp hA])
      · simp +decide [funext_iff, Equiv.ext_iff]
    have h_sum_subset_prod :
        ∑ f ∈ Finset.univ.filter (fun f : F => Function.Injective f), (∏ i, x (f i)) =
          ∑ A ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)),
            ∑ f ∈ Finset.filter
                (fun f : F => Function.Injective f ∧ Finset.image f Finset.univ = A)
                Finset.univ,
              (∏ i, x (f i)) := by
      rw [← Finset.sum_biUnion]
      · congr with f
        simp +decide [Function.Injective]
        exact fun h => by rw [Finset.card_image_of_injective _ h, Finset.card_fin]
      · exact fun A hA B hB hAB => Finset.disjoint_left.mpr fun f hfA hfB =>
          hAB <| by aesop
    rw [h_sum_subset_prod, Finset.sum_congr rfl h_subset_prod,
      ← Finset.mul_sum _ _ _, esymm]
  rw [← hS_card]
  refine' le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => Finset.prod_nonneg fun _ _ => hx _) _
  rw [← Fin.prod_const]
  rw [Finset.prod_sum]
  simp +decide [Finset.prod_apply]
  refine' le_of_eq (Finset.sum_bij (fun f _ => fun i _ => f i) _ _ _ _) <;>
    simp +decide [Function.Injective]
  · simp +contextual [funext_iff]
    exact fun f g h => funext h
  · exact fun b => ⟨fun i => b i (Finset.mem_univ i), rfl⟩

lemma collision_sum_le {k N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i)
    (m : ℝ) (hm : ∀ i, x i ≤ m) (j l : Fin k) (hjl : j ≠ l) :
    ∑ f : Fin k → Fin N, (if f j = f l then ∏ i, x (f i) else 0) ≤
      m * (∑ a : Fin N, x a) ^ (k - 1) := by
  by_contra! h_contra
  have h_fubini :
      ∑ f : Fin k → Fin N, (if f j = f l then ∏ i, x (f i) else 0) =
        ∑ a : Fin N, ∑ f : Fin k → Fin N,
          (if f j = a ∧ f l = a then ∏ i, x (f i) else 0) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl]
    intro f hf
    by_cases h : f j = f l <;> simp +decide [h]
    rw [Finset.sum_eq_zero]
    aesop
  have h_inner : ∀ a : Fin N,
      ∑ f : Fin k → Fin N,
          (if f j = a ∧ f l = a then ∏ i, x (f i) else 0) =
        x a ^ 2 * (∑ b : Fin N, x b) ^ (k - 2) := by
    intro a
    have h_inner_sum :
        ∑ f : Fin k → Fin N,
            (if f j = a ∧ f l = a then ∏ i, x (f i) else 0) =
          ∑ f : Fin k → Fin N,
            (∏ i,
              if i = j ∨ i = l then if f i = a then x a else 0 else x (f i)) := by
      refine' Finset.sum_congr rfl fun f hf => _
      by_cases h : f j = a <;> by_cases h' : f l = a <;>
        simp +decide [h, h', Finset.prod_ite, Finset.filter_or, Finset.filter_eq']
      rw [← Finset.prod_sdiff <| Finset.subset_univ {j, l}]
      simp +decide [*, Finset.filter_insert, Finset.filter_singleton]
      rw [show (Finset.univ \ {j, l} : Finset (Fin k)) =
          Finset.filter (fun i => ¬i = j ∧ ¬i = l) Finset.univ by
        ext i
        aesop]
      ring_nf
    have h_inner_sum :
        ∑ f : Fin k → Fin N,
            (∏ i,
              if i = j ∨ i = l then if f i = a then x a else 0 else x (f i)) =
          (∏ i : Fin k,
            (∑ b : Fin N,
              if i = j ∨ i = l then if b = a then x a else 0 else x b)) := by
      rw [Finset.prod_sum]
      refine' Finset.sum_bij (fun f _ => fun i _ => f i) _ _ _ _ <;> simp +decide
      · simp +decide [funext_iff]
      · exact fun b => ⟨fun i => b i (Finset.mem_univ i), rfl⟩
    rw [‹(∑ f : Fin k → Fin N,
        if f j = a ∧ f l = a then ∏ i, x (f i) else 0) =
          ∑ f : Fin k → Fin N,
            ∏ i,
              if i = j ∨ i = l then if f i = a then x a else 0 else x (f i)›,
      h_inner_sum]
    rw [← Finset.prod_sdiff (Finset.subset_univ {j, l})]
    simp +decide [Finset.prod_ite, Finset.filter_or, Finset.filter_eq', hjl]
    simp +decide [Finset.filter_ne', Finset.filter_and, hjl]
    simp +decide [Finset.card_sdiff, Finset.card_singleton, Finset.card_univ, hjl]
    ring_nf
  have h_sum : ∑ a : Fin N, x a ^ 2 * (∑ b : Fin N, x b) ^ (k - 2)
      ≤ m * (∑ a : Fin N, x a) ^ (k - 1) := by
    have h_sq_le_m_x : ∀ a : Fin N, x a ^ 2 ≤ m * x a := by
      exact fun i => by nlinarith only [hx i, hm i]
    convert Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (h_sq_le_m_x i)
        (pow_nonneg (Finset.sum_nonneg fun _ _ => hx _) (k - 2)) using 1
    rcases k with (_ | _ | k) <;>
      simp +decide [pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _] at *
    · fin_cases j
    · fin_cases j
      fin_cases l
      trivial
    · simp +decide only [← mul_assoc, ← sum_mul]
      rw [← Finset.mul_sum _ _ _]
  grind

lemma sum_pow_sub_factorial_mul_esymm_le {N : ℕ} (x : Fin N → ℝ)
    (hx : ∀ i, 0 ≤ x i) (m : ℝ) (hm : ∀ i, x i ≤ m) (k : ℕ) :
    (∑ i : Fin N, x i) ^ k - (k.factorial : ℝ) * esymm x k ≤
      k * (k - 1) / 2 * m * (∑ i : Fin N, x i) ^ (k - 1) := by
  have hD_def :
      (∑ i, x i) ^ k - (k.factorial : ℝ) * esymm x k =
        ∑ f : Fin k → Fin N, (∏ i, x (f i)) -
          ∑ f : Fin k → Fin N,
            (if Function.Injective f then ∏ i, x (f i) else 0) := by
    have hD_def : (k.factorial : ℝ) * esymm x k =
        ∑ f : Fin k → Fin N,
          (if Function.Injective f then ∏ i : Fin k, x (f i) else 0) := by
      have h_factorial_esymm :
          ∑ f : Fin k → Fin N,
              (if Function.Injective f then ∏ i : Fin k, x (f i) else 0) =
            ∑ A ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)),
              (∏ i ∈ A, x i) * (k.factorial : ℝ) := by
        have h_inj_sum : ∀ A ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)),
            ∑ f : Fin k → Fin N,
                (if Function.Injective f ∧ Finset.image f Finset.univ = A then
                  ∏ i, x (f i) else 0) =
              (∏ i ∈ A, x i) * (Nat.factorial k : ℝ) := by
          intro A hA
          have h_inj_count :
              Finset.card (Finset.filter
                (fun f : Fin k → Fin N =>
                  Function.Injective f ∧ Finset.image f Finset.univ = A)
                (Finset.univ : Finset (Fin k → Fin N))) =
                Nat.factorial k := by
            have h_inj_sum :
                Finset.card (Finset.filter
                  (fun f : Fin k → Fin N =>
                    Function.Injective f ∧ Finset.image f Finset.univ = A)
                  (Finset.univ : Finset (Fin k → Fin N))) =
                  Finset.card (Finset.image
                    (fun f : Fin k ≃ A => fun i => f i |>.1)
                    (Finset.univ : Finset (Fin k ≃ A))) := by
              congr with f
              constructor <;> intro hf <;> simp_all +decide [Finset.ext_iff]
              · use Equiv.ofBijective (fun i => ⟨f i, by
                  exact hf.2 _ |>.1 ⟨i, rfl⟩⟩) (by
                    exact ⟨fun i j hij => hf.1 <| by
                      simpa using congr_arg Subtype.val hij, fun i => by
                        obtain ⟨j, hj⟩ := hf.2 i |>.2 i.2
                        exact ⟨j, Subtype.ext hj⟩⟩)
                aesop
              · rcases hf with ⟨a, rfl⟩
                simp +decide [Function.Injective, Finset.mem_image]
                exact fun i => ⟨fun ⟨j, hj⟩ => hj ▸ Subtype.mem _, fun hi =>
                  ⟨a.symm ⟨i, hi⟩, by simp +decide⟩⟩
            rw [h_inj_sum, Finset.card_image_of_injective]
            · simp +decide [Finset.card_univ, Fintype.card_perm]
              rw [Fintype.card_equiv]
              aesop
              exact Fintype.equivOfCardEq (by aesop)
            · intro f g hfg
              ext i
              replace hfg := congr_fun hfg i
              aesop
          have h_inj_sum : ∀ f : Fin k → Fin N,
              Function.Injective f ∧ Finset.image f Finset.univ = A →
                ∏ i, x (f i) = ∏ i ∈ A, x i := by
            intro f hf
            rw [← hf.2, Finset.prod_image (by aesop)]
          simp_all +decide [Finset.sum_ite]
          ring_nf
        rw [← Finset.sum_congr rfl h_inj_sum, Finset.sum_comm]
        congr! 1
        by_cases h : Function.Injective ‹Fin k → Fin N› <;> simp +decide [h]
        exact fun h' => False.elim <| h' <| by
          rw [Finset.card_image_of_injective _ h, Finset.card_fin]
      simp_all +decide [mul_comm, Finset.mul_sum _ _ _, esymm]
    rw [hD_def, ← Fin.prod_const]
    rw [Finset.prod_sum]
    refine' congrArg₂ _ (Finset.sum_bij (fun f hf => fun i => f i (Finset.mem_univ i))
      _ _ _ _) rfl <;> simp +decide
    · simp +contextual [funext_iff]
    · exact fun b => ⟨fun i _ => b i, rfl⟩
  have h_pair_bound : ∀ j l : Fin k, j < l →
      ∑ f : Fin k → Fin N,
        (if f j = f l then ∏ i, x (f i) else 0) ≤
          m * (∑ i, x i) ^ (k - 1) := by
    intros j l hjl
    apply collision_sum_le x hx m hm j l hjl.ne
  have h_sum_pairs :
      ∑ f : Fin k → Fin N,
          (if ∃ j l : Fin k, j < l ∧ f j = f l then ∏ i, x (f i) else 0) ≤
        (k * (k - 1) / 2 : ℝ) * m * (∑ i, x i) ^ (k - 1) := by
    have h_sum_pairs :
        ∑ f : Fin k → Fin N,
            (if ∃ j l : Fin k, j < l ∧ f j = f l then ∏ i, x (f i) else 0) ≤
          ∑ j : Fin k, ∑ l ∈ Finset.Ioi j,
            ∑ f : Fin k → Fin N,
              (if f j = f l then ∏ i, x (f i) else 0) := by
      have h_sum_pairs : ∀ f : Fin k → Fin N,
          (if ∃ j l : Fin k, j < l ∧ f j = f l then ∏ i, x (f i) else 0) ≤
            ∑ j : Fin k, ∑ l ∈ Finset.Ioi j,
              (if f j = f l then ∏ i, x (f i) else 0) := by
        intro f
        split_ifs
        · obtain ⟨j, l, hjl, h⟩ := ‹_›
          exact le_trans (by aesop)
            (Finset.single_le_sum
              (fun a _ => Finset.sum_nonneg fun b _ => by
                split_ifs <;>
                  nlinarith [show 0 ≤ ∏ i, x (f i) from
                    Finset.prod_nonneg fun _ _ => hx _])
              (Finset.mem_univ j) |>
              le_trans (Finset.single_le_sum
                (fun b _ => by
                  split_ifs <;>
                    nlinarith [show 0 ≤ ∏ i, x (f i) from
                      Finset.prod_nonneg fun _ _ => hx _])
                (Finset.mem_Ioi.mpr hjl)))
        · exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => by
            split_ifs <;> [exact Finset.prod_nonneg fun _ _ => hx _; exact le_rfl]
      refine' le_trans (Finset.sum_le_sum fun f _ => h_sum_pairs f) _
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum fun i hi => by rw [Finset.sum_comm]
    refine le_trans h_sum_pairs <|
      le_trans (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
        h_pair_bound i j <| Finset.mem_Ioi.mp hj) ?_
    norm_num [← Finset.mul_sum _ _ _, ← Finset.sum_mul]
    rw [show (∑ i : Fin k, (k - 1 - i : ℕ) : ℝ) = k * (k - 1) / 2 from by
      have hNat : (∑ i : Fin k, (k - 1 - i : ℕ)) = k * (k - 1) / 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun j => k - 1 - j) k]
        rw [Finset.sum_range_reflect (fun j => j) k]
        exact Finset.sum_range_id k
      rw [← Nat.cast_sum, hNat]
      rw [Nat.cast_div_charZero (Nat.two_dvd_mul_sub_one k)]
      by_cases hk : k = 0
      · simp [hk]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        rw [Nat.cast_mul, Nat.cast_pred hkpos]
        ring_nf]
    ring_nf
    norm_num
  convert h_sum_pairs using 1
  convert hD_def using 1
  rw [← Finset.sum_sub_distrib]
  congr
  ext f
  by_cases hf : Function.Injective f <;> simp +decide [hf]
  · exact fun i j hij h => False.elim <| hij.ne <| hf h
  · exact fun h => False.elim <| hf <| fun i j hij =>
      le_antisymm (le_of_not_gt fun hi => h _ _ hi hij.symm)
        (le_of_not_gt fun hj => h _ _ hj hij)

/-! ## Measure-theoretic lemma -/

lemma prob_sum_eq_bernoulliSumProb
    {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin N → Ω → ℕ)
    (p : Fin N → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_le_one : ∀ i, p i ≤ 1)
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_bernoulli : ∀ i k, (μ {ω | X i ω = k}).toReal = bernoulliPMFReal (p i) k)
    (k : ℕ) :
    (μ {ω | ∑ i : Fin N, X i ω = k}).toReal = bernoulliSumProb p k := by
  revert k
  intro k
  have h_sum_eq : μ {ω | (∑ i, X i ω) = k} =
      ∑ A ∈ Finset.powersetCard k Finset.univ,
        μ (⋂ i, {ω | (X i ω) = if i ∈ A then 1 else 0}) := by
    have meas_set : ∀ i, μ {ω | X i ω ≤ 1} = 1 := by
      intro i
      have h_le_one : μ {ω | X i ω ≤ 1} =
          μ {ω | X i ω = 0} + μ {ω | X i ω = 1} := by
        rw [← MeasureTheory.measure_union] <;> congr
        ext ω
        simp +decide [Nat.le_one_iff_eq_zero_or_eq_one]
        aesop
        · exact Set.disjoint_left.mpr fun ω hω₀ hω₁ => by
            simpa [hω₀.out] using hω₁.out
        · exact hX_meas i (MeasurableSingletonClass.measurableSet_singleton _)
      have := h_bernoulli i 0
      have := h_bernoulli i 1
      simp_all +decide [bernoulliPMFReal]
      rw [← ENNReal.toReal_eq_one_iff]
      have := h_bernoulli i 0
      have := h_bernoulli i 1
      simp_all +decide [ENNReal.toReal_add]
    have h_sum_eq : μ {ω | (∑ i, X i ω) = k} =
        μ (⋃ A ∈ Finset.powersetCard k Finset.univ,
          (⋂ i, {ω | (X i ω) = if i ∈ A then 1 else 0})) := by
      have h_sum_eq : ∀ᵐ ω ∂μ,
          (∑ i, X i ω) = k ↔
            ∃ A ∈ Finset.powersetCard k Finset.univ,
              ∀ i, X i ω = if i ∈ A then 1 else 0 := by
        have h_sum_eq : ∀ᵐ ω ∂μ, ∀ i, X i ω ≤ 1 := by
          have h_sum_eq : ∀ i, μ {ω | X i ω > 1} = 0 := by
            intro i
            have h_sum_eq : μ {ω | X i ω > 1} =
                μ (Set.univ \ {ω | X i ω ≤ 1}) := by
              exact congr_arg _ (by ext; simp +decide [not_le])
            rw [h_sum_eq, MeasureTheory.measure_diff] <;> norm_num [meas_set]
            exact measurableSet_le (hX_meas i) measurable_const |>
              MeasurableSet.nullMeasurableSet
          filter_upwards
            [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
              (MeasureTheory.measure_iUnion_null fun i => h_sum_eq i)] with ω hω using
              fun i => not_lt.1 fun contra => hω <| Set.mem_iUnion.2 ⟨i, contra⟩
        filter_upwards [h_sum_eq] with ω hω
        constructor
        · intro hk
          use Finset.univ.filter (fun i => X i ω = 1)
          simp_all +decide [Finset.mem_powersetCard, Finset.sum_ite]
          exact ⟨by
            rw [← hk, Finset.card_filter]
            exact Finset.sum_congr rfl fun i _ => by
              specialize hω i
              interval_cases X i ω <;> trivial, fun i => by
            specialize hω i
            interval_cases X i ω <;> trivial⟩
        · rintro ⟨A, hA₁, hA₂⟩
          simp_all +decide [Finset.sum_ite]
      exact MeasureTheory.measure_congr (Filter.eventuallyEq_set.mpr <| by simpa using h_sum_eq)
    rw [h_sum_eq, MeasureTheory.measure_biUnion_finset]
    · intro A hA B hB hAB
      simp_all +decide [Set.disjoint_left]
      grind
    · exact fun A hA => MeasurableSet.iInter fun i =>
        measurableSet_eq_fun (hX_meas i) measurable_const
  rw [h_sum_eq, ENNReal.toReal_sum]
  · refine' Finset.sum_congr rfl fun A hA => _
    have h_prod : μ (⋂ i, {ω | X i ω = if i ∈ A then 1 else 0}) =
        ∏ i, μ {ω | X i ω = if i ∈ A then 1 else 0} := by
      have := h_indep.measure_inter_preimage_eq_mul
      simpa using this Finset.univ
        (fun i _ => MeasurableSingletonClass.measurableSet_singleton _)
    simp_all +decide [bernoulliPMFReal]
    simp +decide [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.filter_not]
  · exact fun _ _ => MeasureTheory.measure_ne_top _ _

/-! ## Analytic convergence lemmas -/

lemma bernoulliSumProb_ge_esymm_mul_prod
    {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : ℕ) :
    bernoulliSumProb p k ≥ esymm p k * ∏ i : Fin N, (1 - p i) := by
  rw [ge_iff_le]
  unfold bernoulliSumProb esymm
  rw [Finset.sum_mul _ _ _]
  refine Finset.sum_le_sum ?_
  intro A _hA
  have hp_prod_nonneg : 0 ≤ ∏ i ∈ A, p i :=
    Finset.prod_nonneg fun i _ => hp i
  have hcomp_nonneg : 0 ≤ ∏ i ∈ (Finset.univ \ A), (1 - p i) :=
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (hp1 i)
  have hA_le_one : ∏ i ∈ A, (1 - p i) ≤ 1 :=
    Finset.prod_le_one
      (fun i _ => sub_nonneg.2 (hp1 i))
      (fun i _ => sub_le_self _ (hp i))
  have hall_eq :
      (∏ i : Fin N, (1 - p i)) =
        (∏ i ∈ (Finset.univ \ A), (1 - p i)) *
          ∏ i ∈ A, (1 - p i) := by
    simpa [mul_comm] using
      (Finset.prod_sdiff (s₁ := A) (s₂ := (Finset.univ : Finset (Fin N)))
        (f := fun i => 1 - p i) (Finset.subset_univ A)).symm
  rw [hall_eq]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_right hcomp_nonneg hA_le_one)
    hp_prod_nonneg

lemma bernoulliSumProb_le_esymm_mul_prod_div
    {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (m : ℝ) (hm : ∀ i, p i ≤ m) (hm1 : m < 1) (k : ℕ) :
    bernoulliSumProb p k ≤ esymm p k * (∏ i : Fin N, (1 - p i)) / (1 - m) ^ k := by
  have h_prod_sdiff : ∀ A ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)),
      ∏ i ∈ (Finset.univ \ A), (1 - p i) ≤
        (∏ i, (1 - p i)) / (1 - m) ^ k := by
    intro A hA
    have h_prod_sdiff : ∏ i ∈ (Finset.univ \ A), (1 - p i) =
        (∏ i, (1 - p i)) / (∏ i ∈ A, (1 - p i)) := by
      exact eq_div_of_mul_eq
        (Finset.prod_ne_zero_iff.mpr fun i hi => by linarith [hp i, hp1 i, hm i, hm1])
        (Finset.prod_sdiff <| Finset.subset_univ _)
    rw [h_prod_sdiff, Finset.mem_powersetCard] at *
    gcongr
    · exact Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| hp1 _
    · exact pow_pos (by linarith) _
    · exact le_trans (by norm_num [hA.2])
        (Finset.prod_le_prod (fun _ _ => sub_nonneg.2 hm1.le)
          fun _ _ => sub_le_sub_left (hm _) _)
  convert Finset.sum_le_sum fun A hA =>
    mul_le_mul_of_nonneg_left (h_prod_sdiff A hA)
      (Finset.prod_nonneg fun i _ => hp i) using 1
  unfold esymm
  simp_rw [div_eq_mul_inv]
  simp_rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring_nf

lemma prod_one_sub_tendsto_exp_neg
    (p : (N : ℕ) → Fin N → ℝ) (lam : ℝ)
    (hp_nonneg : ∀ N i, 0 ≤ p N i)
    (hp_le_one : ∀ N i, p N i ≤ 1)
    (h_max : Tendsto (fun N => rowMax p N) atTop (𝓝 0))
    (h_mean : Tendsto (fun N => ∑ i : Fin N, p N i) atTop (𝓝 lam)) :
    Tendsto (fun N => ∏ i : Fin N, (1 - p N i)) atTop (𝓝 (Real.exp (-lam))) := by
  have h_log_approx :
      Filter.Tendsto
        (fun N => ∑ i : Fin N, -Real.log (1 - p N i) - ∑ i : Fin N, p N i)
        Filter.atTop (nhds 0) := by
    have h_bound : ∀ᶠ N in Filter.atTop, ∀ i : Fin N,
        |(-Real.log (1 - p N i)) - p N i| ≤ (p N i)^2 / (1 - p N i) := by
      have h_frac_zero : ∀ᶠ N in Filter.atTop, ∀ i : Fin N, p N i < 1 := by
        filter_upwards [h_max.eventually (gt_mem_nhds zero_lt_one)] with N hN using
          fun i => lt_of_le_of_lt (by
            unfold rowMax
            split_ifs <;>
              [exact Finset.le_sup' (fun i => p N i) (Finset.mem_univ i);
               linarith [Fin.is_lt i]]) hN
      filter_upwards [h_frac_zero] with N hN i
      rw [abs_le]
      constructor <;>
        nlinarith [hp_nonneg N i, hp_le_one N i, hN i,
          Real.log_inv (1 - p N i),
          Real.log_le_sub_one_of_pos
            (inv_pos.mpr (by linarith [hp_nonneg N i, hp_le_one N i, hN i] :
              0 < 1 - p N i)),
          Real.log_le_sub_one_of_pos
            (by linarith [hp_nonneg N i, hp_le_one N i, hN i] : 0 < 1 - p N i),
          mul_inv_cancel₀
            (by linarith [hp_nonneg N i, hp_le_one N i, hN i] : (1 - p N i) ≠ 0),
          div_mul_cancel₀ (p N i ^ 2)
            (by linarith [hp_nonneg N i, hp_le_one N i, hN i] :
              (1 - p N i) ≠ 0)]
    have h_bound' : ∀ᶠ N in Filter.atTop, ∀ i : Fin N,
        |(-Real.log (1 - p N i)) - p N i| ≤ (p N i)^2 / (1 - rowMax p N) := by
      have h_bound' : ∀ᶠ N in Filter.atTop, ∀ i : Fin N, p N i ≤ rowMax p N := by
        filter_upwards [Filter.eventually_gt_atTop 0] with N hN i using by
          unfold rowMax
          aesop
      filter_upwards [h_bound, h_bound', h_max.eventually (gt_mem_nhds zero_lt_one)] with
        N hN₁ hN₂ hN₃ i using
          le_trans (hN₁ i)
            (div_le_div_of_nonneg_left (sq_nonneg _)
              (by linarith [hp_nonneg N i, hp_le_one N i]) (by linarith [hN₂ i]))
    have h_sum_sq : Filter.Tendsto (fun N => ∑ i : Fin N, (p N i)^2)
        Filter.atTop (nhds 0) := by
      have h_sum_sq_le : ∀ N,
          ∑ i : Fin N, (p N i)^2 ≤ rowMax p N * ∑ i : Fin N, p N i := by
        intro N
        rw [Finset.mul_sum _ _ _]
        refine' Finset.sum_le_sum fun i _ => _
        rcases N with (_ | N) <;> norm_num [rowMax] at *
        nlinarith only [hp_nonneg (N + 1) i, hp_le_one (N + 1) i,
          Finset.le_sup' (fun i => p (N + 1) i) (Finset.mem_univ i)]
      exact squeeze_zero (fun N => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        h_sum_sq_le (by simpa using h_max.mul h_mean)
    have h_sum_abs_diff : Filter.Tendsto
        (fun N => ∑ i : Fin N, |(-Real.log (1 - p N i)) - p N i|)
        Filter.atTop (nhds 0) := by
      refine' squeeze_zero_norm' _ _
      use fun N => (∑ i, p N i ^ 2) / (1 - rowMax p N)
      · filter_upwards [h_bound'] with N hN using by
          rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
          simpa only [Finset.sum_div _ _ _] using Finset.sum_le_sum fun i _ => hN i
      · simpa using h_sum_sq.div (h_max.const_sub 1) (by norm_num)
    refine' squeeze_zero_norm (fun N => _) h_sum_abs_diff
    simpa only [← Finset.sum_sub_distrib] using Finset.abs_sum_le_sum_abs _ _
  have h_prod_exp :
      Filter.Tendsto (fun N => Real.exp (-∑ i : Fin N, -Real.log (1 - p N i)))
        Filter.atTop (nhds (Real.exp (-lam))) := by
    exact Filter.Tendsto.rexp (by simpa using h_mean.add h_log_approx |> Filter.Tendsto.neg)
  refine h_prod_exp.congr' ?_
  have h_prod_eq_exp : ∀ᶠ N in Filter.atTop, ∀ i : Fin N, 1 - p N i > 0 := by
    filter_upwards [h_max.eventually (gt_mem_nhds zero_lt_one)] with N hN using
      fun i => sub_pos_of_lt <| lt_of_le_of_lt (show p N i ≤ rowMax p N from by
        unfold rowMax
        split_ifs <;>
          [exact Finset.le_sup' (fun i => p N i) (Finset.mem_univ i);
           linarith [Fin.is_lt i]]) hN
  filter_upwards [h_prod_eq_exp] with N hN using by
    rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum,
      Finset.prod_congr rfl fun i hi => Real.exp_log (hN i)]

lemma esymm_tendsto
    (p : (N : ℕ) → Fin N → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam)
    (hp_nonneg : ∀ N i, 0 ≤ p N i)
    (hp_le_one : ∀ N i, p N i ≤ 1)
    (h_max : Tendsto (fun N => rowMax p N) atTop (𝓝 0))
    (h_mean : Tendsto (fun N => ∑ i : Fin N, p N i) atTop (𝓝 lam))
    (k : ℕ) :
    Tendsto (fun N => esymm (p N) k) atTop (𝓝 (lam ^ k / k.factorial)) := by
  have h_squeeze : ∀ N ≥ 1,
      esymm (p N) k ≤ (∑ i, p N i) ^ k / k.factorial ∧
        esymm (p N) k ≥
          (∑ i, p N i) ^ k / k.factorial -
            k * (k - 1) / 2 * rowMax p N * (∑ i, p N i) ^ (k - 1) / k.factorial := by
    intro N hN
    constructor
    · exact le_div_iff₀' (by positivity) |>.2
        (factorial_mul_esymm_le_sum_pow (p N) (fun i => hp_nonneg N i) k)
    · have := sum_pow_sub_factorial_mul_esymm_le (p N) (hp_nonneg N) (rowMax p N) (?_) k
      · rw [div_sub_div_same, ge_iff_le, div_le_iff₀] <;> first | positivity | linarith
      · unfold rowMax
        aesop
  have h_squeeze :
      Filter.Tendsto (fun N => (∑ i, p N i) ^ k / k.factorial) atTop
          (nhds (lam ^ k / k.factorial)) ∧
        Filter.Tendsto
          (fun N =>
            k * (k - 1) / 2 * rowMax p N * (∑ i, p N i) ^ (k - 1) / k.factorial)
          atTop (nhds 0) := by
    exact ⟨by simpa using h_mean.pow k |> Filter.Tendsto.div_const <| k.factorial,
      by
        simpa using Filter.Tendsto.div_const
          (Filter.Tendsto.mul (tendsto_const_nhds.mul h_max) <| h_mean.pow (k - 1)) _⟩
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using h_squeeze.1.sub h_squeeze.2) h_squeeze.1 _ _
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN using by
      linarith [‹∀ N ≥ 1,
        esymm (p N) k ≤ (∑ i, p N i) ^ k / k.factorial ∧
          esymm (p N) k ≥
            (∑ i, p N i) ^ k / k.factorial -
              k * (k - 1) / 2 * rowMax p N *
                (∑ i, p N i) ^ (k - 1) / k.factorial› N hN]
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN using by aesop

/-! ## Main point-probability theorem -/

theorem point_probability_tendsto
    {Ω : ℕ → Type*}
    [∀ N, MeasurableSpace (Ω N)]
    (μ : (N : ℕ) → Measure (Ω N))
    [∀ N, IsProbabilityMeasure (μ N)]
    (X : (N : ℕ) → Fin N → Ω N → ℕ)
    (p : (N : ℕ) → Fin N → ℝ)
    (lam : ℝ)
    (hlam : 0 ≤ lam)
    (hp_nonneg : ∀ N i, 0 ≤ p N i)
    (hp_le_one : ∀ N i, p N i ≤ 1)
    (hX_meas : ∀ N i, Measurable (X N i))
    (h_indep : ∀ N, ProbabilityTheory.iIndepFun (fun i : Fin N => X N i) (μ N))
    (h_bernoulli :
      ∀ N i k,
        ((μ N) {ω | X N i ω = k}).toReal = bernoulliPMFReal (p N i) k)
    (h_max :
      Tendsto (fun N : ℕ => rowMax p N) atTop (𝓝 0))
    (h_mean :
      Tendsto (fun N : ℕ => ∑ i : Fin N, p N i) atTop (𝓝 lam)) :
    ∀ k : ℕ,
      Tendsto
        (fun N : ℕ => ((μ N) {ω | rowSum X N ω = k}).toReal)
        atTop
        (𝓝 (poissonPMFReal lam k)) := by
  intro k
  have h_squeeze : ∀ᶠ N in Filter.atTop, rowMax p N < 1 := by
    exact h_max.eventually (gt_mem_nhds zero_lt_one)
  have h_squeeze : ∀ᶠ N in Filter.atTop,
      bernoulliSumProb (p N) k ≥ esymm (p N) k * ∏ i, (1 - p N i) ∧
        bernoulliSumProb (p N) k ≤
          esymm (p N) k * (∏ i, (1 - p N i)) / (1 - rowMax p N) ^ k := by
    filter_upwards [h_squeeze, Filter.eventually_gt_atTop 0] with N hN hN'
    refine' ⟨bernoulliSumProb_ge_esymm_mul_prod _ (fun i => hp_nonneg N i)
      (fun i => hp_le_one N i) _, _⟩
    apply bernoulliSumProb_le_esymm_mul_prod_div
    · exact hp_nonneg N
    · exact fun i => hp_le_one N i
    · unfold rowMax
      aesop
    · exact hN
  have h_squeeze :
      Filter.Tendsto (fun N => esymm (p N) k * ∏ i, (1 - p N i)) Filter.atTop
          (nhds (lam ^ k / k.factorial * Real.exp (-lam))) ∧
        Filter.Tendsto
          (fun N => esymm (p N) k * (∏ i, (1 - p N i)) / (1 - rowMax p N) ^ k)
          Filter.atTop (nhds (lam ^ k / k.factorial * Real.exp (-lam))) := by
    have h_squeeze : Filter.Tendsto (fun N => esymm (p N) k) Filter.atTop
        (nhds (lam ^ k / k.factorial)) ∧
          Filter.Tendsto (fun N => ∏ i, (1 - p N i)) Filter.atTop
            (nhds (Real.exp (-lam))) := by
      exact ⟨esymm_tendsto p lam hlam hp_nonneg hp_le_one h_max h_mean k,
        prod_one_sub_tendsto_exp_neg p lam hp_nonneg hp_le_one h_max h_mean⟩
    exact ⟨h_squeeze.1.mul h_squeeze.2, by
      simpa using
        Filter.Tendsto.div (h_squeeze.1.mul h_squeeze.2)
          (Filter.Tendsto.pow (h_max.const_sub 1) k)
          (pow_ne_zero k (by norm_num))⟩
  have h_squeeze : Filter.Tendsto (fun N => bernoulliSumProb (p N) k) Filter.atTop
      (nhds (lam ^ k / k.factorial * Real.exp (-lam))) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_squeeze.1 h_squeeze.2
      (by filter_upwards
        [‹∀ᶠ N in atTop,
          bernoulliSumProb (p N) k ≥ esymm (p N) k * ∏ i, (1 - p N i) ∧
            bernoulliSumProb (p N) k ≤
              (esymm (p N) k * ∏ i, (1 - p N i)) / (1 - rowMax p N) ^ k›] with N hN using hN.1)
      (by filter_upwards
        [‹∀ᶠ N in atTop,
          bernoulliSumProb (p N) k ≥ esymm (p N) k * ∏ i, (1 - p N i) ∧
            bernoulliSumProb (p N) k ≤
              (esymm (p N) k * ∏ i, (1 - p N i)) / (1 - rowMax p N) ^ k›] with N hN using hN.2)
  convert h_squeeze using 1
  · ext N
    convert prob_sum_eq_bernoulliSumProb (μ N) (X N) (p N) (hp_nonneg N) (hp_le_one N)
      (hX_meas N) (h_indep N) (h_bernoulli N) k using 1
  · unfold poissonPMFReal
    ring_nf

end PoissonLimitAux

/-- The convergence-in-distribution conclusion of HDP Theorem 1.3.4. -/
def poissonLimitConclusion [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℕ) (lam : ℝ≥0)
    (hS : ∀ N, AEMeasurable (poissonTriangularSum X N) μ) : Prop :=
  Tendsto
    (fun N : ℕ => lawOf (μ := μ) (poissonTriangularSum X N) (hS N))
    atTop
    (𝓝 (poissonProbabilityMeasure lam))

/-- Book-style hypotheses for HDP Theorem 1.3.4, the Poisson limit theorem.
This structure deliberately contains only assumptions, not the conclusion. -/
structure PoissonLimitTheoremHypotheses [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℕ) (p : ℕ → ℕ → ℝ≥0) (lam : ℝ≥0) : Prop where
  measurable : ∀ N i, Measurable (X N i)
  parameter_le_one : ∀ N i, p N i ≤ 1
  independent_rows :
    ∀ N, iIndepFun (fun i : Fin N => X N i) μ
  bernoulli_law :
    ∀ N i, i < N →
      HasLaw (X N i) ((bernoulliNatPMF (p N i) (parameter_le_one N i)).toMeasure) μ
  max_parameter_tendsto_zero :
    Tendsto (fun N => rowParameterMax p N) atTop (𝓝 0)
  sum_parameter_tendsto :
    Tendsto (fun N => rowParameterSum p N) atTop (𝓝 (lam : ℝ))
  sum_aemeasurable :
    ∀ N, AEMeasurable (poissonTriangularSum X N) μ

omit [MeasurableSpace Ω] in
private lemma poissonLimitAux_rowSum_eq
    (X : ℕ → ℕ → Ω → ℕ) (N : ℕ) (ω : Ω) :
    PoissonLimitAux.rowSum (fun N (i : Fin N) (ω : Ω) => X N i ω) N ω =
      poissonTriangularSum X N ω := by
  simp [PoissonLimitAux.rowSum, poissonTriangularSum, Finset.sum_range]

private lemma finset_univ_map_fin_valEmbedding (N : ℕ) :
    (Finset.univ.map (Fin.valEmbedding : Fin N ↪ ℕ)) = Finset.range N := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_map.mp hi with ⟨a, _ha, rfl⟩
    exact Finset.mem_range.mpr a.isLt
  · intro hi
    exact Finset.mem_map.mpr ⟨⟨i, Finset.mem_range.mp hi⟩, Finset.mem_univ _, rfl⟩

private lemma poissonLimitAux_rowMax_eq_rowParameterMax
    (p : ℕ → ℕ → ℝ≥0) (N : ℕ) :
    PoissonLimitAux.rowMax (fun N (i : Fin N) => (p N i : ℝ)) N =
      (rowParameterMax p N : ℝ) := by
  unfold PoissonLimitAux.rowMax
  by_cases hN : 0 < N
  · simp [hN]
    have hsup_real :
        Finset.sup' (Finset.univ : Finset (Fin N)) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
            (fun i : Fin N => (p N i : ℝ)) =
          ((((Finset.univ : Finset (Fin N)).sup (fun i : Fin N => p N i)) : ℝ≥0) : ℝ) := by
      let H : (Finset.univ : Finset (Fin N)).Nonempty :=
        ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      let L : ℝ :=
        Finset.sup' (Finset.univ : Finset (Fin N)) H (fun i : Fin N => (p N i : ℝ))
      have hL_nonneg : 0 ≤ L := by
        have hle : (0 : ℝ) ≤ (p N (⟨0, hN⟩ : Fin N) : ℝ) := by
          exact_mod_cast (p N (⟨0, hN⟩ : Fin N)).2
        exact hle.trans
          (Finset.le_sup' (s := (Finset.univ : Finset (Fin N)))
            (fun i : Fin N => (p N i : ℝ)) (Finset.mem_univ _))
      let Lnn : ℝ≥0 := ⟨L, hL_nonneg⟩
      apply le_antisymm
      · rw [Finset.sup'_le_iff]
        intro i _hi
        exact_mod_cast
          (Finset.le_sup (s := (Finset.univ : Finset (Fin N)))
            (f := fun i : Fin N => p N i) (Finset.mem_univ i))
      · change
          ((((Finset.univ : Finset (Fin N)).sup (fun i : Fin N => p N i)) : ℝ≥0) : ℝ) ≤ L
        have hsup_le :
            ((Finset.univ : Finset (Fin N)).sup (fun i : Fin N => p N i)) ≤ Lnn := by
          exact Finset.sup_le_iff.mpr fun i _hi =>
            NNReal.coe_le_coe.mpr
              (Finset.le_sup' (s := (Finset.univ : Finset (Fin N)))
                (fun i : Fin N => (p N i : ℝ)) (Finset.mem_univ i))
        exact NNReal.coe_le_coe.mpr hsup_le
    rw [hsup_real]
    have hfin :
        (((Finset.univ : Finset (Fin N)).sup (fun i : Fin N => p N i)) : ℝ≥0) =
          rowParameterMax p N := by
      unfold rowParameterMax
      rw [← finset_univ_map_fin_valEmbedding N]
      rw [Finset.sup_map]
      rfl
    rw [hfin]
  · have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    simp [hN0, rowParameterMax]

private lemma poissonLimitAux_parameter_sum_eq
    (p : ℕ → ℕ → ℝ≥0) (N : ℕ) :
    (∑ i : Fin N, (p N i : ℝ)) = rowParameterSum p N := by
  rw [rowParameterSum]
  exact Fin.sum_univ_eq_sum_range (fun i => (p N i : ℝ)) N

private lemma bernoulli_hasLaw_pointProbability_real
    [IsProbabilityMeasure μ]
    {X : Ω → ℕ} {p : ℝ≥0} {hp : p ≤ 1}
    (hLaw : HasLaw X ((bernoulliNatPMF p hp).toMeasure) μ) :
    ∀ k : ℕ,
      (μ {ω | X ω = k}).toReal = PoissonLimitAux.bernoulliPMFReal (p : ℝ) k := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    have hzero := measureReal_eq_zero_of_hasLaw_bernoulliNatPMF (μ := μ) (X := X) hLaw
    rw [← measureReal_def]
    rw [hzero, NNReal.coe_sub hp]
    simp [PoissonLimitAux.bernoulliPMFReal]
  · by_cases hk1 : k = 1
    · subst k
      have hone := measureReal_eq_one_of_hasLaw_bernoulliNatPMF (μ := μ) (X := X) hLaw
      rw [← measureReal_def]
      simpa [PoissonLimitAux.bernoulliPMFReal] using hone
    · have hpre : μ {ω | X ω = k} = ((bernoulliNatPMF p hp).toMeasure) ({k} : Set ℕ) := by
        rw [← hLaw.map_eq]
        exact (Measure.map_apply_of_aemeasurable hLaw.aemeasurable
          (measurableSet_singleton k)).symm
      rw [hpre, PMF.toMeasure_apply_singleton]
      · simp [PoissonLimitAux.bernoulliPMFReal, hk0, hk1,
          bernoulliNatPMF_apply_of_ne_zero_one hk0 hk1]
      · exact measurableSet_singleton k

private lemma poissonProbabilityMeasure_singleton_real
    (lam : ℝ≥0) (k : ℕ) :
    ((poissonProbabilityMeasure lam ({k} : Set ℕ) : ℝ≥0) : ℝ) =
      poissonPointProbability lam k := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  rw [measureReal_def, poissonProbabilityMeasure_singleton]
  rw [ENNReal.toReal_ofReal]
  · rfl
  · positivity

private lemma lawOf_poissonTriangularSum_singleton_real
    [IsProbabilityMeasure μ]
    {X : ℕ → ℕ → Ω → ℕ}
    (hS : ∀ N, AEMeasurable (poissonTriangularSum X N) μ)
    (N k : ℕ) :
    ((lawOf (μ := μ) (poissonTriangularSum X N) (hS N) ({k} : Set ℕ) : ℝ≥0) : ℝ) =
      (μ {ω | poissonTriangularSum X N ω = k}).toReal := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  rw [measureReal_def, lawOf_toMeasure]
  rw [Measure.map_apply_of_aemeasurable (hS N) (measurableSet_singleton k)]
  rfl

/-- Point-probability form of HDP Theorem 1.3.4. This is the substantive
Bernoulli triangular-array asymptotic: for each fixed `k`, the probability that
the row sum has value `k` converges to the corresponding Poisson mass. -/
theorem poissonLimit_point_probabilities
    [IsProbabilityMeasure μ]
    {X : ℕ → ℕ → Ω → ℕ} {p : ℕ → ℕ → ℝ≥0} {lam : ℝ≥0}
    (h : PoissonLimitTheoremHypotheses (μ := μ) X p lam) :
    ∀ k : ℕ,
      Tendsto
        (fun N : ℕ => (μ {ω | poissonTriangularSum X N ω = k}).toReal)
        atTop
        (𝓝 (poissonPointProbability lam k)) := by
  let Xfin : (N : ℕ) → Fin N → Ω → ℕ := fun N i ω => X N i ω
  let pfin : (N : ℕ) → Fin N → ℝ := fun N i => (p N i : ℝ)
  have hp_nonneg : ∀ N (i : Fin N), 0 ≤ pfin N i := by
    intro N i
    exact_mod_cast (p N i).2
  have hp_le_one : ∀ N (i : Fin N), pfin N i ≤ 1 := by
    intro N i
    exact_mod_cast h.parameter_le_one N i
  have hbern :
      ∀ N (i : Fin N) k,
        (μ {ω | Xfin N i ω = k}).toReal =
          PoissonLimitAux.bernoulliPMFReal (pfin N i) k := by
    intro N i k
    exact bernoulli_hasLaw_pointProbability_real
      (μ := μ) (X := X N i) (p := p N i)
      (hp := h.parameter_le_one N i)
      (h.bernoulli_law N i i.isLt) k
  have hmax : Tendsto (fun N : ℕ => PoissonLimitAux.rowMax pfin N) atTop (𝓝 0) := by
    refine (NNReal.tendsto_coe.mpr h.max_parameter_tendsto_zero).congr' ?_
    filter_upwards with N
    exact (poissonLimitAux_rowMax_eq_rowParameterMax p N).symm
  have hmean : Tendsto (fun N : ℕ => ∑ i : Fin N, pfin N i) atTop (𝓝 (lam : ℝ)) := by
    refine h.sum_parameter_tendsto.congr' ?_
    filter_upwards with N
    exact (poissonLimitAux_parameter_sum_eq p N).symm
  have hpoint :=
    PoissonLimitAux.point_probability_tendsto
      (Ω := fun _ : ℕ => Ω)
      (μ := fun _ : ℕ => μ)
      (X := Xfin)
      (p := pfin)
      (lam := (lam : ℝ))
      (by exact_mod_cast (lam.2 : 0 ≤ lam))
      hp_nonneg hp_le_one (fun N i => by simpa [Xfin] using h.measurable N i)
      h.independent_rows hbern hmax hmean
  intro k
  have hk := hpoint k
  simpa [Xfin, pfin, poissonLimitAux_rowSum_eq,
    poissonPointProbability_eq, PoissonLimitAux.poissonPMFReal] using hk

/-- A genuine Poisson-limit bridge: if the point probabilities of the row sums
converge to the Poisson point probabilities, then the row-sum laws converge in
distribution to the Poisson law. -/
theorem poisson_limit_of_point_probabilities [IsProbabilityMeasure μ]
    {X : ℕ → ℕ → Ω → ℕ} {lam : ℝ≥0}
    (hS : ∀ N, AEMeasurable (poissonTriangularSum X N) μ)
    (hpoint :
      ∀ k : ℕ,
        Tendsto
          (fun N : ℕ =>
            lawOf (μ := μ) (poissonTriangularSum X N) (hS N) ({k} : Set ℕ))
          atTop
          (𝓝 (poissonProbabilityMeasure lam ({k} : Set ℕ)))) :
    poissonLimitConclusion (μ := μ) X lam hS :=
  probabilityMeasure_nat_tendsto_of_singleton hpoint

/-- HDP Theorem 1.3.4, the Poisson limit theorem for triangular arrays of
independent Bernoulli variables. -/
theorem poissonLimitTheorem
    [IsProbabilityMeasure μ]
    {X : ℕ → ℕ → Ω → ℕ} {p : ℕ → ℕ → ℝ≥0} {lam : ℝ≥0}
    (h : PoissonLimitTheoremHypotheses (μ := μ) X p lam) :
    poissonLimitConclusion (μ := μ) X lam h.sum_aemeasurable := by
  apply poisson_limit_of_point_probabilities h.sum_aemeasurable
  intro k
  apply NNReal.tendsto_coe.mp
  have hreal := poissonLimit_point_probabilities (μ := μ) h k
  simpa [lawOf_poissonTriangularSum_singleton_real h.sum_aemeasurable,
    poissonProbabilityMeasure_singleton_real] using hreal

/-- The exact proposition stated by HDP Theorem 1.3.4. -/
def poissonLimitTheoremStatement [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℕ) (p : ℕ → ℕ → ℝ≥0) (lam : ℝ≥0) : Prop :=
  ∀ h : PoissonLimitTheoremHypotheses (μ := μ) X p lam,
    poissonLimitConclusion (μ := μ) X lam h.sum_aemeasurable

end BernoulliBinomialPoisson

end LeanFpAnalysis.HDP
