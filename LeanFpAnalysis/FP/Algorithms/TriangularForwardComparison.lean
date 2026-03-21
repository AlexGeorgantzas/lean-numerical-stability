-- Algorithms/TriangularForwardComparison.lean
--
-- Higham §8.2–8.3: Forward error bounds via comparison matrices.
--
-- Theorem 8.9: |x - x̂| ≤ γ(n) · M(T)⁻¹ · |T| · |x̂|  (componentwise)
-- Plus M-matrix utilities for lower triangular matrices.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.ForwardError
import LeanFpAnalysis.FP.Algorithms.ForwardSub
import LeanFpAnalysis.FP.Algorithms.TriangularForwardBound
import LeanFpAnalysis.FP.Algorithms.InverseBounds

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- Theorem 8.9: Forward error via comparison matrix
-- ============================================================

/-- **Theorem 8.9** (Higham §8.2, comparison matrix form).

    The forward error for forward substitution satisfies:
      |x_i - x̂_i| ≤ γ(n) · (M(L)⁻¹ · |L| · |x̂|)_i

    This strengthens `forwardSub_forward_error` by replacing |L⁻¹| with
    M(L)⁻¹ using Theorem 8.11 (|L⁻¹| ≤ M(L)⁻¹). The bound can be
    much tighter because M(L)⁻¹ ≥ |L⁻¹| with equality when L = M(L).

    Proof: `forwardSub_forward_error` gives
      |x_i - x̂_i| ≤ γ(n) · ∑_j |L_inv_ij| · (∑_k |L_jk| · |x̂_k|)
    Then replace |L_inv_ij| with M_inv_ij using `abs_inv_le_compMatrix_inv_lower`. -/
theorem forwardSub_forward_error_comparison (fp : FPModel) (n : ℕ)
    (L L_inv M_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsInverse n L L_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n L) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hn : gammaValid fp n) :
    let x_hat := fl_forwardSub fp n L b
    ∀ i, |x i - x_hat i| ≤
      gamma fp n * ∑ j : Fin n, M_inv i j * (∑ k : Fin n, |L j k| * |x_hat k|) := by
  intro x_hat
  have hfwd := forwardSub_forward_error fp n L L_inv x b hL hLT hInv.1 hTx hn
  have habs_bound := abs_inv_le_compMatrix_inv_lower n L L_inv M_inv hLT hL hInv
    hM_RInv hM_inv_lt
  -- M_inv has nonneg entries (M-matrix inverse)
  have hM_nn := lower_tri_mmatrix_inv_nonneg n (comparisonMatrix n L) M_inv
    (by intro i j hij; unfold comparisonMatrix
        simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hLT i j hij])
    (by intro i; simp [comparisonMatrix]; exact hL i)
    (by intro i j _; simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)])
    hM_RInv hM_inv_lt
  intro i
  calc |x i - x_hat i|
      ≤ gamma fp n * ∑ j : Fin n, |L_inv i j| *
          (∑ k : Fin n, |L j k| * |x_hat k|) := hfwd i
    _ ≤ gamma fp n * ∑ j : Fin n, M_inv i j *
          (∑ k : Fin n, |L j k| * |x_hat k|) := by
        apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn)
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg
          (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        exact habs_bound i j

-- ============================================================
-- M-matrix utilities for lower triangular matrices
-- ============================================================

/-- When L is a lower triangular M-matrix (positive diagonal, nonpositive off-diagonal),
    the comparison matrix equals L itself. -/
theorem comparisonMatrix_eq_self_mmatrix_lower (n : ℕ) (L : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag_pos : ∀ i : Fin n, 0 < L i i)
    (hL_offdiag : ∀ i j : Fin n, j.val < i.val → L i j ≤ 0) :
    comparisonMatrix n L = L := by
  funext i j
  unfold comparisonMatrix
  by_cases hij : i = j
  · subst hij; simp [abs_of_pos (hL_diag_pos i)]
  · simp [hij]
    by_cases hlt : j.val < i.val
    · have hle := hL_offdiag i j hlt
      rw [abs_of_nonpos hle]; ring
    · push_neg at hlt
      have : i.val < j.val := Nat.lt_of_le_of_ne (by omega) (fun h => hij (Fin.ext h))
      rw [hLT i j this, abs_zero, neg_zero]

/-- When L is a lower triangular M-matrix, its inverse has nonneg entries. -/
theorem mmatrix_inv_nonneg_lower (n : ℕ) (L L_inv : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag_pos : ∀ i : Fin n, 0 < L i i)
    (hL_offdiag : ∀ i j : Fin n, j.val < i.val → L i j ≤ 0)
    (hInv : IsInverse n L L_inv) :
    ∀ i j : Fin n, 0 ≤ L_inv i j := by
  have hInv_lt := inv_lower_tri n L L_inv hLT (fun i => ne_of_gt (hL_diag_pos i)) hInv.1
  exact lower_tri_mmatrix_inv_nonneg n L L_inv hLT hL_diag_pos hL_offdiag hInv.2 hInv_lt

-- ============================================================
-- Note on Corollary 8.10 (Higham §8.2)
-- ============================================================
-- Corollary 8.10 states: for M-matrix L with b ≥ 0, |x - x̂| ≤ ((n²+n+1)u + O(u²))|x|.
-- This requires the direct recurrence proof from Higham pp. 158–159, which analyzes the
-- forward substitution algorithm step-by-step rather than going through the backward
-- error route. The key difficulty is that for M-matrices, L⁻¹|L| = 2L⁻¹diag(L) - I ≠ I,
-- so Theorem 8.9's bound γ(n)·(L⁻¹|L||x̂|)_i does NOT simplify to γ(n)|x̂_i|.
-- The full recurrence proof is left as future work.

end LeanFpAnalysis.FP
