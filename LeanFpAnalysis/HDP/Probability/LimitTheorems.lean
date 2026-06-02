import LeanFpAnalysis.HDP.Probability.Inequalities
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic

/-!
# Limit Theorems

HDP Chapter 1, Section 1.3. The strong law is provided by mathlib and wrapped
in book-style notation. The Lindeberg-Levy CLT and the full Bernoulli
triangular-array Poisson limit theorem require substantial characteristic
function/asymptotic infrastructure not currently present in this library, so
this file records their exact hypotheses/conclusions as definitions rather than
pretending to prove them by assuming the conclusion.
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
  integrable_zero : Integrable (X 0) μ
  square_integrable_zero : MemLp (X 0) 2 μ
  independent : Pairwise ((· ⟂ᵢ[μ] ·) on X)
  identDistrib : ∀ i, IdentDistrib (X i) (X 0) μ μ
  mean_eq : μ[X 0] = m
  variance_eq : Var[X 0; μ] = σ ^ 2
  sigma_pos : 0 < σ
  normalized_aemeasurable : ∀ N, AEMeasurable (normalizedSum X m σ N) μ

/-- The exact proposition stated by HDP Theorem 1.3.2. It is kept as a
statement object until the characteristic-function/Taylor proof infrastructure
is formalized. -/
def lindebergLevyCentralLimitTheoremStatement [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (m σ : ℝ) : Prop :=
  ∀ h : LindebergLevyCLTHypotheses (μ := μ) X m σ,
    centralLimitConclusion (μ := μ) X m σ h.normalized_aemeasurable

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
  ProbabilityTheory.poissonPMFReal lam k

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
  change (ProbabilityTheory.poissonPMF lam).toMeasure {k} =
    ENNReal.ofReal
      (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ k / Nat.factorial k)
  rw [PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k)]
  rfl

/-- Row sum `S_N = ∑_{i < N} X_{N,i}` for the Poisson limit theorem. -/
def poissonTriangularSum (X : ℕ → ℕ → Ω → ℕ) (N : ℕ) (ω : Ω) : ℕ :=
  ∑ i ∈ Finset.range N, X N i ω

/-- Sum of the Bernoulli parameters in row `N`. -/
def rowParameterSum (p : ℕ → ℕ → ℝ≥0) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, (p N i : ℝ)

/-- Maximum Bernoulli parameter in row `N`. -/
def rowParameterMax (p : ℕ → ℕ → ℝ≥0) (N : ℕ) : ℝ≥0 :=
  (Finset.range N).sup (p N)

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

/-- The exact proposition stated by HDP Theorem 1.3.4. It is kept as a
statement object until the Bernoulli triangular-array point-probability
asymptotic is formalized. -/
def poissonLimitTheoremStatement [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℕ) (p : ℕ → ℕ → ℝ≥0) (lam : ℝ≥0) : Prop :=
  ∀ h : PoissonLimitTheoremHypotheses (μ := μ) X p lam,
    poissonLimitConclusion (μ := μ) X lam h.sum_aemeasurable

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

end BernoulliBinomialPoisson

end LeanFpAnalysis.HDP
