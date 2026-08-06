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
benchmark package does not import NumStability. -/
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

end HighamBench
