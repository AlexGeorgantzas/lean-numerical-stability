-- Summation.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-- **Summation rounding error lemma** (Higham §3.1).

    For a sequence of values v : Fin n → ℝ, sequential floating-point
    summation (left-to-right, starting from 0) produces a result equal to
    a perturbation of the exact sum:

      fl_sum fp n v = ∑ i, v i * (1 + θ i)

    where each |θ i| ≤ gamma fp n.

    Intuition: the term v 0 passes through all n additions and accumulates
    up to n rounding errors; term v i passes through (n - i) additions.
    The worst case over all terms is γ(n), giving a uniform bound.

    Precondition: gammaValid fp n ensures the denominator of γ is positive. -/

lemma fl_sum_error (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ gamma fp n) ∧
      Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0 =
        ∑ i : Fin n, v i * (1 + θ i) := by
  sorry

end LeanFpAnalysis.FP
