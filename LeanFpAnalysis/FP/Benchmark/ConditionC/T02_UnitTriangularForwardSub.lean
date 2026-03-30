-- Benchmark/T02_UnitTriangularForwardSub.lean
-- Tier 1 (Direct application) — Unit triangular forward substitution

import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.ForwardSub

/-!
# Task 2: Unit triangular forward substitution simplification

**Tier:** 1 (Direct application)
**Higham ref:** §8.1, specialization of Theorem 8.5
**Difficulty:** Easy — specialize `forwardSub_backward_error` to unit diagonal

## Task description

When L is *unit* lower triangular (L i i = 1 for all i), the backward error
bound for forward substitution simplifies: the diagonal entries of ΔL vanish,
and the bound becomes |ΔL i j| ≤ γ(n) * |L i j| with ΔL i i = 0.

Show that for unit lower triangular L, there exists a perturbation ΔL with
zero diagonal such that (L + ΔL)x̂ = b.

## Expected approach

1. Apply `forwardSub_backward_error` to get the general ΔL.
2. Construct ΔL' where ΔL' i i = 0 and ΔL' i j = ΔL i j for i ≠ j.
3. Use L i i = 1 to show (L + ΔL')x̂ = b still holds (the diagonal
   term contributes x̂ i in both cases).

## Metrics
- **Pass criterion:** No `sorry` and `lake build` succeeds
- **Partial credit:** Correct statement with ≤ 2 sorry's in helper lemmas
-/

namespace LeanFpAnalysis.FP.Benchmark

open LeanFpAnalysis.FP
open scoped BigOperators

/-- A lower triangular matrix is unit (diagonal entries all 1). -/
def IsUnitLowerTriangular (n : ℕ) (L : Fin n → Fin n → ℝ) : Prop :=
  (∀ i : Fin n, L i i = 1) ∧
  (∀ i j : Fin n, i.val < j.val → L i j = 0)

/-- **Unit triangular forward substitution backward error.**

    For unit lower triangular L, the computed solution x̂ = fl(L⁻¹b) satisfies
      (L + ΔL)x̂ = b
    where ΔL has zero diagonal and |ΔL i j| ≤ γ(n)|L i j| componentwise. -/
theorem unitForwardSub_backward_error (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hUnit : IsUnitLowerTriangular n L)
    (hn : gammaValid fp n) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i : Fin n, ΔL i i = 0) ∧
      (∀ i j, |ΔL i j| ≤ gamma fp n * |L i j|) ∧
      ∀ i, ∑ j : Fin n, (L i j + ΔL i j) * fl_forwardSub fp n L b j = b i := by
  sorry

end LeanFpAnalysis.FP.Benchmark
