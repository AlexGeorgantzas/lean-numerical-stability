-- Benchmark/T04_PLUSolve.lean
-- Tier 2 (Composition) — PLU solve with row permutation

import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.ForwardSub
import LeanFpAnalysis.FP.Algorithms.TriangularSolve
import LeanFpAnalysis.FP.Algorithms.LU.LUSolve

/-!
# Task 4: PLU solve with row permutation

**Tier:** 2 (Composition)
**Higham ref:** §9.3-9.4, PA = LU with partial pivoting
**Difficulty:** Medium — compose permutation handling with `lu_solve_backward_error`

## Task description

In practice, LU factorization uses partial pivoting: PA = LU where P is a
permutation matrix. Solving Ax = b becomes:
  1. Permute: Pb
  2. Forward solve: Ly = Pb
  3. Back solve: Ux = y

Show that the computed solution x̂ satisfies a backward error bound
  (A + ΔA)x̂ = b
where the bound on ΔA accounts for the permutation and the LU solve errors.

## Expected approach

1. Model the permutation as a function σ : Fin n → Fin n (bijection).
2. Define the permuted system: (PA)x = Pb where PA i j = A (σ i) j.
3. Apply `lu_solve_backward_error` to the permuted system to get
   (PA + Δ(PA))x̂ = Pb.
4. Unpermute: define ΔA i j = Δ(PA) (σ⁻¹ i) j, yielding (A + ΔA)x̂ = b.
5. The componentwise bound transfers through the permutation.

## Metrics
- **Pass criterion:** No `sorry` and `lake build` succeeds
- **Partial credit:** Correct statement with ≤ 3 sorry's in helper lemmas
-/

namespace LeanFpAnalysis.FP.Benchmark

open LeanFpAnalysis.FP
open scoped BigOperators

/-- A permutation on Fin n. -/
structure Permutation (n : ℕ) where
  σ : Fin n → Fin n
  σ_inv : Fin n → Fin n
  left_inv : ∀ i, σ_inv (σ i) = i
  right_inv : ∀ i, σ (σ_inv i) = i

/-- Apply permutation to rows of a matrix. -/
noncomputable def permuteRows (n : ℕ) (P : Permutation n)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A (P.σ i) j

/-- Apply permutation to a vector. -/
noncomputable def permuteVec (n : ℕ) (P : Permutation n)
    (b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => b (P.σ i)

/-- **PLU solve backward error.**

    Given PA = L̂Û (computed LU of permuted A), the PLU solve
    x̂ = Û⁻¹(L̂⁻¹(Pb)) satisfies (A + ΔA)x̂ = b with componentwise
    bound on ΔA in terms of |L̂| and |Û|. -/
theorem plu_solve_backward_error (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (P : Permutation n)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n (permuteRows n P A) L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n) :
    let y_hat := fl_forwardSub fp n L_hat (permuteVec n P b)
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat (P.σ_inv i) k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  sorry

end LeanFpAnalysis.FP.Benchmark
