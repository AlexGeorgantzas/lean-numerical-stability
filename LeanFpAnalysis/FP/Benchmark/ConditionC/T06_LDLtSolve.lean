-- Benchmark/T06_LDLtSolve.lean
-- Tier 2 (Composition) — LDLᵀ solve via indefinite factorization

import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.ForwardSub
import LeanFpAnalysis.FP.Algorithms.TriangularSolve

/-!
# Task 6: LDLᵀ solve backward stability

**Tier:** 2 (Composition)
**Higham ref:** §10.4, composing indefinite factorization with triangular solves
**Difficulty:** Medium — chain three backward error results

## Task description

For symmetric indefinite systems, we use the LDLᵀ factorization:
  A = LDLᵀ
Solving Ax = b becomes:
  1. Forward solve: Ly = b
  2. Diagonal solve: Dz = y  (trivial: zᵢ = yᵢ/dᵢᵢ)
  3. Back solve: Lᵀx = z

Show that the composed solve has backward error (A + ΔA)x̂ = b where
the bound on ΔA involves |L|, |D|, |Lᵀ| and the gamma factor.

## Expected approach

1. Apply `forwardSub_backward_error` for step 1: (L + ΔL)ŷ = b.
2. Model the diagonal solve with a single rounding per component.
3. Apply `backSub_backward_error` for step 3 (on Lᵀ): (Lᵀ + ΔLᵀ)x̂ = ẑ.
4. Compose the three perturbations into a single ΔA for the original system.

## Metrics
- **Pass criterion:** No `sorry` and `lake build` succeeds
- **Partial credit:** Correct statement with ≤ 3 sorry's in helper lemmas
-/

namespace LeanFpAnalysis.FP.Benchmark

open LeanFpAnalysis.FP
open scoped BigOperators

/-- Diagonal matrix as a function. -/
noncomputable def diagMatrix (n : ℕ) (d : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then d i else 0

/-- Floating-point diagonal solve: x̂ᵢ = fl(bᵢ / dᵢ). -/
noncomputable def fl_diagSolve (fp : FPModel) (n : ℕ)
    (d : Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fp.fl_div (b i) (d i)

/-- **LDLᵀ solve backward error.**

    The computed solution x̂ of LDLᵀx = b (via forward sub, diagonal solve,
    transposed back sub) satisfies (A + ΔA)x̂ = b where
    |ΔA i j| is bounded in terms of |L|, |D|, |Lᵀ| and γ(n). -/
theorem ldlt_solve_backward_error (fp : FPModel) (n : ℕ)
    (A L : Fin n → Fin n → ℝ) (d : Fin n → ℝ) (b : Fin n → ℝ)
    -- L is unit lower triangular
    (hL_unit : ∀ i : Fin n, L i i = 1)
    (hL_lower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    -- d entries are nonzero
    (hd_ne : ∀ i : Fin n, d i ≠ 0)
    -- A = LDLᵀ
    (hLDLt : ∀ i j : Fin n, A i j =
      ∑ k : Fin n, L i k * d k * L j k)
    (hn : gammaValid fp n) :
    let LT := fun i j : Fin n => L j i
    let y_hat := fl_forwardSub fp n L b
    let z_hat := fl_diagSolve fp n d y_hat
    let x_hat := fl_backSub fp n LT z_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        (3 * gamma fp n + 3 * gamma fp n ^ 2 + gamma fp n ^ 3) *
          ∑ k : Fin n, |L i k| * |d k| * |L j k|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  sorry

end LeanFpAnalysis.FP.Benchmark
