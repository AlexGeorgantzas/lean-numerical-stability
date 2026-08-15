import HighamBench.Core
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
