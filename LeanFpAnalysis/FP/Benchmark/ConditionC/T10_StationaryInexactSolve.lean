-- Benchmark/T10_StationaryInexactSolve.lean
-- Tier 3 (Novel reasoning) — Stationary iteration with inexact triangular solve

import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.ForwardSub
import LeanFpAnalysis.FP.Algorithms.StationaryIteration

/-!
# Task 10: Stationary iteration with inexact triangular solve

**Tier:** 3 (Novel reasoning)
**Higham ref:** §16, combining Theorem 16.6 with §8.5 backward error
**Difficulty:** Hard — requires composing stationary iteration framework with
               concrete backward error from triangular solve

## Task description

A stationary iterative method (Jacobi, Gauss-Seidel, SOR) splits A = M - N
and iterates x_{k+1} = M⁻¹(Nx_k + b). In practice, "M⁻¹" is computed
via triangular solve (e.g., for Gauss-Seidel, M is lower triangular).

The library's `normwise_forward_bound` takes an abstract perturbation ξ_k
at each step. This task requires instantiating ξ_k with the *concrete*
backward error from `forwardSub_backward_error`, showing that the abstract
bound applies with a specific μ derived from the triangular solve error.

## Expected approach

1. From `forwardSub_backward_error`, derive that each iteration's solve
   M x̂_{k+1} = Nx_k + b has backward error (M + ΔM)x̂_{k+1} = Nx_k + b,
   so ΔM·x̂_{k+1} is the perturbation ξ_k.
2. Bound ‖ξ_k‖∞ ≤ γ(n)·‖M‖∞·‖x̂_{k+1}‖∞ to get μ.
3. Plug into `normwise_forward_bound` to get the concrete convergence bound.

## Metrics
- **Pass criterion:** No `sorry` and `lake build` succeeds
- **Partial credit:** Correct statement with ≤ 4 sorry's in helper lemmas
-/

namespace LeanFpAnalysis.FP.Benchmark

open LeanFpAnalysis.FP
open scoped BigOperators

/-- **Stationary iteration perturbation from triangular solve.**

    When the splitting M is lower triangular and we solve Mx = r via
    forward substitution, the perturbation ξ_k in the stationary iteration
    framework satisfies ‖ξ_k‖∞ ≤ γ(n)·‖M‖∞·‖x̂_{k+1}‖∞.

    This connects the abstract `normwise_forward_bound` with the concrete
    triangular solve backward error. -/
theorem stationary_triangular_perturbation_bound (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (M : Fin n → Fin n → ℝ)
    (r : Fin n → ℝ)
    -- M is lower triangular with nonzero diagonal
    (hM_diag : ∀ i : Fin n, M i i ≠ 0)
    (hM_lower : ∀ i j : Fin n, i.val < j.val → M i j = 0)
    (hn : gammaValid fp n) :
    let x_hat := fl_forwardSub fp n M r
    ∃ ΔM : Fin n → Fin n → ℝ,
      (∀ i j, |ΔM i j| ≤ gamma fp n * |M i j|) ∧
      (∀ i, ∑ j : Fin n, (M i j + ΔM i j) * x_hat j = r i) ∧
      -- The perturbation ξ = ΔM·x̂ has bounded infinity norm:
      infNormVec hn_pos (fun i => ∑ j : Fin n, ΔM i j * x_hat j) ≤
        gamma fp n * infNorm hn_pos M *
          infNormVec hn_pos x_hat := by
  sorry

end LeanFpAnalysis.FP.Benchmark
