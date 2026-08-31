import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# HighamBench P17 definitions

Paper-scoped finite probability, product-error, and summation notation for
limited-precision stochastic rounding.
-/

namespace HighamBench

open scoped BigOperators

/-- The paper's standard error-growth function `gamma_n(u) = (1+u)^n-1`. -/
noncomputable def p17Gamma (n : ℕ) (u : ℝ) : ℝ :=
  (1 + u) ^ n - 1

/-- Binary unit roundoff `u_p = 2^(1-p)`, on the paper's domain `p > 0`.
The natural-power form is equal to the printed expression whenever `p` is
positive and makes its nonnegativity explicit. -/
noncomputable def p17UnitRoundoff (p : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ (p - 1)

/-- Exact finite sum. -/
noncomputable def p17ExactSum {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i, a i

/-- Componentwise condition number of summation. -/
noncomputable def p17SummationCondition {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  (∑ i, |a i|) / |p17ExactSum a|

/-- Effective expected sum after exposing the expected suffix-product factor
attached to each input in equation (4.4). -/
noncomputable def p17EffectiveExpectedSum {n : ℕ}
    (a factor : Fin n → ℝ) : ℝ :=
  ∑ i, a i * factor i

/-- A lightweight finite probability law, kept paper-scoped so the public
benchmark package remains independent of the evaluated formal library. -/
structure P17FiniteProbability (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  prob_sum : ∑ ω, prob ω = 1

/-- Probability of an event under a paper-scoped finite law. -/
noncomputable def p17EventProb {Ω : Type*} [Fintype Ω]
    (P : P17FiniteProbability Ω) (E : Set Ω) : ℝ := by
  classical
  exact ∑ ω, if ω ∈ E then P.prob ω else 0

/-- Expectation of a real random variable under a paper-scoped finite law. -/
noncomputable def p17Expectation {Ω : Type*} [Fintype Ω]
    (P : P17FiniteProbability Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.prob ω * X ω

/-- A random variable determined by the rounding errors preceding step `k`.
This finite-history formulation is the test-function semantics of conditional
expectation used in Lemma 3.2. -/
def p17HistoryMeasurable {m : ℕ} {Ω : Type*}
    (delta : Fin m → Ω → ℝ) (k : Fin m) (X : Ω → ℝ) : Prop :=
  ∀ ω₁ ω₂,
    (∀ j : Fin m, j.val < k.val → delta j ω₁ = delta j ω₂) →
      X ω₁ = X ω₂

/-- Finite-probability form of Theorem 3.6 with the sign conditions required
by its induction made explicit.

The test-function identity is the finite-space meaning of
`E(delta_k | delta_0, ..., delta_{k-1}) = beta_k`. The structure records no
product bound: that remains the conclusion of P17-T1. -/
structure P17CorrectedProductBiasRun
    (n : ℕ) (Ω : Type*) [Fintype Ω] where
  probability : P17FiniteProbability Ω
  operation_count_pos : 0 < n
  B : ℝ
  B_pos : 0 < B
  B_le_one : B ≤ 1
  delta : Fin n → Ω → ℝ
  beta : Fin n → Ω → ℝ
  rounding_factor_nonneg : ∀ k ω, 0 ≤ 1 + delta k ω
  beta_bound : ∀ k ω, |beta k ω| ≤ B
  beta_history : ∀ k, 0 < k.val → p17HistoryMeasurable delta k (beta k)
  conditional_mean : ∀ k X,
    p17HistoryMeasurable delta k X →
      p17Expectation probability (fun ω => X ω * delta k ω) =
        p17Expectation probability (fun ω => X ω * beta k ω)

/-- Expected accumulated relative-error product in corrected Theorem 3.6. -/
noncomputable def p17ExpectedErrorProduct
    {n : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17CorrectedProductBiasRun n Ω) : ℝ :=
  p17Expectation run.probability
    (fun ω => ∏ k : Fin n, (1 + run.delta k ω))

/-- Left-to-right recursive summation of `m+1` inputs using the `m` supplied
relative rounding errors. The first input is exact, as in the table preceding
equation (4.4). -/
noncomputable def p17RecursiveSum {m : ℕ}
    (a : Fin (m + 1) → ℝ) (delta : Fin m → ℝ) : ℝ :=
  Fin.foldl m
    (fun acc k => (acc + a k.succ) * (1 + delta k))
    (a 0)

/-- The accumulated value immediately before recursive-summation addition
`k`. -/
noncomputable def p17RecursiveSumBefore {m : ℕ}
    (a : Fin (m + 1) → ℝ) (delta : Fin m → ℝ) (k : Fin m) : ℝ :=
  Fin.foldl k.val
    (fun acc j =>
      let q : Fin m := ⟨j.val, Nat.lt_trans j.isLt k.isLt⟩
      (acc + a q.succ) * (1 + delta q))
    (a 0)

/-- The exact real addition rounded at recursive-summation step `k`. -/
noncomputable def p17RecursivePreRound {m : ℕ}
    (a : Fin (m + 1) → ℝ) (delta : Fin m → ℝ) (k : Fin m) : ℝ :=
  p17RecursiveSumBefore a delta k + a k.succ

/-- Analytic execution certificate for recursive summation under
limited-precision stochastic rounding `SR_{p,r}`.

The conditional-mean field is the finite test-function form of
`E(delta_k | delta_0,...,delta_{k-1}) = beta_k`. The truncation equation links
`beta_k` to the deterministic `p+r`-bit truncation of the actual pre-rounding
value instead of leaving it as an unrelated perturbation. -/
structure P17LimitedPrecisionRecursiveSumRun
    (m : ℕ) (Ω : Type*) [Fintype Ω] where
  probability : P17FiniteProbability Ω
  p : ℕ
  r : ℕ
  p_pos : 0 < p
  r_pos : 0 < r
  a : Fin (m + 1) → ℝ
  delta : Fin m → Ω → ℝ
  beta : Fin m → Ω → ℝ
  truncate : ℝ → ℝ
  delta_bound : ∀ k ω, |delta k ω| ≤ p17UnitRoundoff p
  rounding_factor_nonneg : ∀ k ω, 0 ≤ 1 + delta k ω
  beta_bound : ∀ k ω, |beta k ω| ≤ p17UnitRoundoff (p + r)
  truncation_equation : ∀ k ω,
    truncate (p17RecursivePreRound a (fun j => delta j ω) k) =
      p17RecursivePreRound a (fun j => delta j ω) k * (1 + beta k ω)
  delta_zero : ∀ k ω,
    p17RecursivePreRound a (fun j => delta j ω) k = 0 → delta k ω = 0
  beta_zero : ∀ k ω,
    p17RecursivePreRound a (fun j => delta j ω) k = 0 → beta k ω = 0
  beta_history : ∀ k, p17HistoryMeasurable delta k (beta k)
  conditional_mean : ∀ k X,
    p17HistoryMeasurable delta k X →
      p17Expectation probability (fun ω => X ω * delta k ω) =
        p17Expectation probability (fun ω => X ω * beta k ω)

/-- Expected output of the paper's limited-precision stochastic recursive
sum. -/
noncomputable def p17ExpectedRecursiveSum {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω) : ℝ :=
  p17Expectation run.probability
    (fun ω => p17RecursiveSum run.a (fun k => run.delta k ω))

/-- Product of the suffix of local factors affecting a tail input in equation
(4.4). -/
noncomputable def p17SuffixErrorProduct :
    (m : ℕ) → (Fin m → ℝ) → Fin m → ℝ
  | 0, _ => fun i => i.elim0
  | m + 1, delta =>
      Fin.lastCases (1 + delta (Fin.last m))
        (fun i =>
          p17SuffixErrorProduct m (fun j => delta j.castSucc) i *
            (1 + delta (Fin.last m)))

/-- The coefficient multiplying each exact input in the product expansion of
left-to-right recursive summation. The first input carries the full product;
input `i + 1` carries the suffix beginning at rounded addition `i`. -/
noncomputable def p17RecursiveCoefficient {m : ℕ}
    (error : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases (∏ k : Fin m, (1 + error k))
    (fun i => p17SuffixErrorProduct m error i)

/-- The mean-independent error `alpha_k = delta_k - beta_k` from Lemma 3.10. -/
noncomputable def p17Alpha
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω)
    (k : Fin m) (ω : Ω) : ℝ :=
  run.delta k ω - run.beta k ω

/-- The path-dependent coefficient remainder `B_i` in equations (3.8) and
(4.8), written as the exact difference between the `delta` and `alpha`
suffix coefficients. -/
noncomputable def p17CoefficientRemainder
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω)
    (i : Fin (m + 1)) (ω : Ω) : ℝ :=
  p17RecursiveCoefficient (fun k => run.delta k ω) i -
    p17RecursiveCoefficient (fun k => p17Alpha run k ω) i

/-- The mean-independent component `M` of the recursive-summation error in
equation (4.8). -/
noncomputable def p17CenteredSummationError
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω) (ω : Ω) : ℝ :=
  ∑ i : Fin (m + 1),
    run.a i *
      (p17RecursiveCoefficient (fun k => p17Alpha run k ω) i - 1)

/-- The path-dependent limited-precision remainder `A = sum_i a_i B_i` in
equations (4.8) and (4.10). -/
noncomputable def p17LimitedPrecisionRemainder
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω) (ω : Ω) : ℝ :=
  ∑ i : Fin (m + 1), run.a i * p17CoefficientRemainder run i ω

/-- Analytic execution certificate for the variance-based recursive-summation
bound in Theorem 4.3.

The first two added fields state the `alpha` conclusions of Lemma 3.10. The
coefficient-remainder field is its equation (3.9), uniformly enlarged to the
`m = n-1` radius used in equation (4.10). The covariance field is the exact
specialization of the variance result cited as reference [11, Lemma 3.1]. It
does not assume the second-moment bound for `M` or Theorem 4.3's final event. -/
structure P17VarianceRecursiveSumRun
    (m : ℕ) (Ω : Type*) [Fintype Ω]
    extends P17LimitedPrecisionRecursiveSumRun m Ω where
  alpha_bound : ∀ k ω,
    |p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω| ≤
      p17UnitRoundoff p
  alpha_mean_independent : ∀ k X,
    p17HistoryMeasurable
        (fun j ω => p17Alpha toP17LimitedPrecisionRecursiveSumRun j ω) k X →
      p17Expectation probability
        (fun ω => X ω *
          p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω) = 0
  alpha_product_covariance_bound : ∀ i j,
    0 ≤ p17Expectation probability (fun ω =>
        (p17RecursiveCoefficient
              (fun k => p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω) i - 1) *
          (p17RecursiveCoefficient
              (fun k => p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω) j - 1)) ∧
      p17Expectation probability (fun ω =>
          (p17RecursiveCoefficient
                (fun k => p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω) i - 1) *
            (p17RecursiveCoefficient
                (fun k => p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω) j - 1)) ≤
        p17Gamma m ((p17UnitRoundoff p) ^ 2)
  coefficient_remainder_bound : ∀ i ω,
    |p17CoefficientRemainder toP17LimitedPrecisionRecursiveSumRun i ω| ≤
      p17Gamma m
          (p17UnitRoundoff p + p17UnitRoundoff (p + r)) -
        p17Gamma m (p17UnitRoundoff p)

/-- Expected coefficient of each exact input in equation (4.4). The first
input carries the full product; input `i+1` carries the corresponding suffix
product. -/
noncomputable def p17ExpectedCoefficient
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω) : Fin (m + 1) → ℝ :=
  Fin.cases
    (p17Expectation run.probability
      (fun ω => ∏ k : Fin m, (1 + run.delta k ω)))
    (fun i =>
      p17Expectation run.probability
        (fun ω => p17SuffixErrorProduct m (fun k => run.delta k ω) i))

end HighamBench
