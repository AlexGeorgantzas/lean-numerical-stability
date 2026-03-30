-- Benchmark/T01_SymmetricMatVec.lean
-- Tier 1 (Direct application) — Symmetric matrix-vector backward error

import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.MatVec

/-!
# Task 1: Symmetric matrix-vector backward error

**Tier:** 1 (Direct application)
**Higham ref:** §3.5, extending equation 3.10
**Difficulty:** Easy — direct use of `matVec_backward_error` plus symmetry constraint

## Task description

Given a symmetric matrix A (A i j = A j i), show that the computed
matrix-vector product ŷ = fl(Ax) satisfies a backward error bound
with a *symmetric* perturbation: ŷ = (A + ΔA)x where ΔA is also
symmetric and |ΔA| ≤ γ(n)|A| componentwise.

## Expected approach

1. Apply `matVec_backward_error` to get ΔA with |ΔA i j| ≤ γ(n)|A i j|.
2. Symmetrize: define ΔA_sym i j = (ΔA i j + ΔA j i) / 2.
3. Show |ΔA_sym i j| ≤ γ(n)|A i j| using symmetry of A and triangle inequality.
4. Show (A + ΔA_sym)x = ŷ by showing each row sum is unchanged.

## Metrics
- **Pass criterion:** No `sorry` and `lake build` succeeds
- **Partial credit:** Correct statement with ≤ 2 sorry's in helper lemmas
-/

namespace LeanFpAnalysis.FP.Benchmark

open LeanFpAnalysis.FP
open scoped BigOperators

/-- A matrix is symmetric. -/
def IsSymmetric (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, A i j = A j i

/-- **Symmetric matrix-vector backward error.**

    If A is symmetric, the computed fl(Ax) satisfies
      ŷ = (A + ΔA)x
    where ΔA is *also symmetric* and |ΔA i j| ≤ γ(n)|A i j|. -/
theorem symMatVec_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hSym : IsSymmetric n A)
    (hn : gammaValid fp n) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      IsSymmetric n ΔA ∧
      (∀ i j, |ΔA i j| ≤ gamma fp n * |A i j|) ∧
      ∀ i, fl_matVec fp n n A x i = ∑ j : Fin n, (A i j + ΔA i j) * x j := by
  sorry

end LeanFpAnalysis.FP.Benchmark
