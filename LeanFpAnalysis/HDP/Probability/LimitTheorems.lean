import LeanFpAnalysis.HDP.Probability.Inequalities
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

open Filter MeasureTheory ProbabilityTheory
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

/-- HDP (1.5): for independent variables with a common variance `σ2`, the
variance of the sample mean is `σ2 / N`. -/
theorem variance_sampleMean_eq {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {σ2 : ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hvar : ∀ i, Var[X i; μ] = σ2) :
    Var[fun ω => (N : ℝ)⁻¹ * ∑ i : Fin N, X i ω; μ] = σ2 / (N : ℝ) := by
  classical
  have hsum_indep :
      Set.Pairwise (↑(Finset.univ : Finset (Fin N))) fun i j => X i ⟂ᵢ[μ] X j := by
    intro i _ j _ hij
    exact hindep hij
  have hsum :=
    ProbabilityTheory.IndepFun.variance_sum
      (μ := μ) (X := X) (s := (Finset.univ : Finset (Fin N)))
      (by intro i _; exact hX i) hsum_indep
  have hsum' :
      Var[(fun ω => ∑ i : Fin N, X i ω); μ] = ∑ i : Fin N, Var[X i; μ] := by
    simpa [Finset.sum_fn] using hsum
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

/-- The convergence-in-distribution conclusion of the Lindeberg-Levy CLT. -/
def centralLimitConclusion [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (m σ : ℝ)
    (hZ : ∀ N, AEMeasurable (normalizedSum X m σ N) μ) : Prop :=
  Tendsto
    (fun N : ℕ => lawOf (μ := μ) (normalizedSum X m σ N) (hZ N))
    atTop
    (𝓝 standardNormalProbability)

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

/-- Binomial distribution `Binom(N,p)`, represented as a PMF on `ℕ`. -/
def binomialNatPMF (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) : PMF ℕ :=
  (PMF.binomial p hp N).map fun i : Fin (N + 1) => (i : ℕ)

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
    ∀ N, Set.Pairwise (Set.Iio N) fun i j => X N i ⟂ᵢ[μ] X N j
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
