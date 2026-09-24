import NumStability.Algorithms.Summation.Recursive.Core
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open scoped BigOperators
open NumStability

/-- Unshifted Algorithm 3.1, with a relative error for each exponential,
recursive floating-point summation, and a final rounded logarithm. -/
structure BasicLogSumExpRun {n : ℕ} (x : Fin n → ℝ) (u : ℝ) where
  fp : FPModel
  unit_eq : fp.u = u
  expError : Fin n → ℝ
  expError_le : ∀ i, |expError i| ≤ u
  logError : ℝ
  logError_le : |logError| ≤ u

noncomputable def exactExpSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, Real.exp (x i)

noncomputable def exactLogSumExp {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.log (exactExpSum x)

noncomputable def computedExp {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : BasicLogSumExpRun x u) (i : Fin n) : ℝ :=
  Real.exp (x i) * (1 + run.expError i)

noncomputable def computedDenominator {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : BasicLogSumExpRun x u) : ℝ :=
  fl_recursiveSum run.fp n (computedExp run)

noncomputable def computedLogSumExp {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : BasicLogSumExpRun x u) : ℝ :=
  Real.log (computedDenominator run) * (1 + run.logError)

/-- The absolute error estimate immediately before Theorem 3.2 in
Blanchard--Higham--Higham. It is defined even when the exact log-sum-exp is
zero; the paper's displayed relative theorem divides by its absolute value.
The quadratic constant is uniform over all admissible local-error runs. -/
theorem target {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧
      ∀ (u : ℝ), 0 < u → u ≤ u₀ →
        ∀ (run : BasicLogSumExpRun x u),
          |computedLogSumExp run - exactLogSumExp x| ≤
            u * |exactLogSumExp x| + (n + 1 : ℝ) * u + C * u ^ 2 := by
  sorry

end HighamBenchCandidate
