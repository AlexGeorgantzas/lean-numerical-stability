-- Algorithms/RecursiveSum.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.Summation

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-- Floating-point recursive summation of `n` values.

    Computes `fl_add(... fl_add(fl_add(0, v 0), v 1) ..., v (n-1))`,
    left-to-right starting from the accumulator 0.

    This formalises the standard loop from Higham §4.1:
    ```
    s = 0
    for i = 1:n
      s = s + xᵢ
    end
    ``` -/
noncomputable def fl_recursiveSum (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0

/-- **Recursive summation backward error** (Higham §4.2).

    The computed recursive sum satisfies:
      `fl_recursiveSum fp n v = ∑ i, v i * (1 + θ i)`
    where each `|θ i| ≤ γ(n)`.

    Backward result: the computed sum is the *exact* sum of perturbed
    inputs `vᵢ * (1 + θᵢ)`.  This is a named wrapper around `fl_sum_error`. -/
theorem recursiveSum_backward_error (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ gamma fp n) ∧
      fl_recursiveSum fp n v = ∑ i : Fin n, v i * (1 + θ i) :=
  fl_sum_error fp n v hn

/-- **Recursive summation forward error bound** (Higham §4.2, equation 4.4).

    The absolute error of recursive summation satisfies:
      `|fl_recursiveSum fp n v - ∑ i, v i| ≤ γ(n) * ∑ i, |v i|`

    Proof: from the backward form `∑ vᵢ(1+θᵢ)`, the error equals
    `∑ vᵢθᵢ`; triangle inequality + `|θᵢ| ≤ γ(n)` close the bound. -/
theorem recursiveSum_forward_error_bound (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : gammaValid fp n) :
    |fl_recursiveSum fp n v - ∑ i : Fin n, v i| ≤
      gamma fp n * ∑ i : Fin n, |v i| := by
  obtain ⟨θ, hθ, hfold⟩ := recursiveSum_backward_error fp n v hn
  have herr : fl_recursiveSum fp n v - ∑ i : Fin n, v i =
      ∑ i : Fin n, v i * θ i := by
    rw [hfold, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [herr]
  calc |∑ i : Fin n, v i * θ i|
      ≤ ∑ i : Fin n, |v i * θ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |v i| * |θ i| := by
          apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
    _ ≤ ∑ i : Fin n, |v i| * gamma fp n :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hθ i) (abs_nonneg _)
    _ = gamma fp n * ∑ i : Fin n, |v i| := by
          rw [← Finset.sum_mul, mul_comm]

end LeanFpAnalysis.FP
