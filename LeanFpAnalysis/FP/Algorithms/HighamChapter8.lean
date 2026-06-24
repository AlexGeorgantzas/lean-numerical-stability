-- Algorithms/HighamChapter8.lean
--
-- Source-facing entry points for Higham Chapter 8, "Triangular Systems".
-- The detailed proofs remain in the focused triangular-system modules; this
-- file provides stable chapter labels and light wrappers around those results.

import LeanFpAnalysis.FP.Algorithms.TriangularSolve
import LeanFpAnalysis.FP.Algorithms.ForwardSub
import LeanFpAnalysis.FP.Algorithms.TriangularSolveCombined
import LeanFpAnalysis.FP.Algorithms.TriangularForwardBound
import LeanFpAnalysis.FP.Algorithms.InverseBounds
import LeanFpAnalysis.FP.Algorithms.TriangularForwardComparison
import LeanFpAnalysis.FP.Algorithms.MMatrix
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-! ## §8.1 Backward Error Analysis -/

/-- **Algorithm 8.1**: the repository's floating-point back-substitution routine. -/
noncomputable def higham8_1_backSub (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fl_backSub fp n U b

/-- **Lemma 8.2 / Lemma 8.4, row-spec form** for Algorithm 8.1. -/
theorem higham8_2_backSub_row_spec (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hn : gammaValid fp n) :
    BackSubRowSpec fp n U b (fl_backSub fp n U b) :=
  fl_backSub_satisfies_spec fp n U b hU hn

/-- **Lemma 8.2**, row-tight form used to prove Theorem 8.3. -/
theorem higham8_2_backSub_row_tight (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hn : gammaValid fp n)
    (i : Fin n) :
    ∃ (φ : Fin n → ℝ),
      |φ i| ≤ gamma fp (n - i.val) ∧
      (∀ j, i.val < j.val → |φ j| ≤ gamma fp (j.val - i.val)) ∧
      b i = Finset.sum (Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)
              (fun j => U i j * (1 + φ j) * fl_backSub fp n U b j) :=
  backSub_row_tight fp n U b hU hn i

/-- **Theorem 8.3**: Algorithm 8.1 with Higham's row-specific constants. -/
theorem higham8_3_backSub_backward_error (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i, |ΔU i i| ≤ gamma fp (n - i.val) * |U i i|) ∧
      (∀ i j, i.val < j.val →
        |ΔU i j| ≤ gamma fp (j.val - i.val) * |U i j|) ∧
      (∀ i j, j.val < i.val → ΔU i j = 0) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * fl_backSub fp n U b j = b i :=
  backSub_backward_error_algorithm_8_1 fp n U b hU hUT hn

/-- **Theorem 8.5**, upper-triangular back-substitution specialization. -/
theorem higham8_5_backSub_backward_error (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i j, |ΔU i j| ≤ gamma fp n * |U i j|) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * fl_backSub fp n U b j = b i :=
  backSub_backward_error fp n U b hU hUT hn

/-- **Theorem 8.5**, lower-triangular forward-substitution specialization. -/
theorem higham8_5_forwardSub_backward_error (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i j, |ΔL i j| ≤ gamma fp n * |L i j|) ∧
      ∀ i, ∑ j : Fin n, (L i j + ΔL i j) * fl_forwardSub fp n L b j = b i :=
  forwardSub_backward_error fp n L b hL hLT hn

/-! ## §8.2 Forward Error Analysis -/

/-- **Equation (8.3)**: the upper-triangular stress matrix `U(α)`. -/
noncomputable def higham8_3_stressUpper (n : ℕ) (α : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then 1
    else if i.val < j.val then -α
    else 0

/-- **Equation (8.4)**: the displayed inverse-entry formula for `U(α)`. -/
noncomputable def higham8_4_stressUpperInvFormula (n : ℕ) (α : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then 1
    else if i.val < j.val then α * (1 + α) ^ (j.val - i.val - 1)
    else 0

/-- **Lemma 8.6**: diagonal-dominance bound for `|U⁻¹||U|`. -/
theorem higham8_6_inv_abs_mul_bound_diagDom (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    ∀ i j : Fin n, i.val ≤ j.val →
      ∑ k : Fin n, |U_inv i k| * |U k j| ≤ 2 ^ (j.val - i.val) :=
  inv_abs_mul_bound_diagDom n U U_inv hDD hInv

/-- **Theorem 8.7**: componentwise forward error under condition (8.5). -/
theorem higham8_7_backSub_forward_error_diagDom (fp : FPModel) (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv)
    (hTx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hn : gammaValid fp n) :
    let x_hat := fl_backSub fp n U b
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      2 ^ (n - i.val) * gamma fp n *
          Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val ≤ j.val))
            ⟨i, by simp [Finset.mem_filter]⟩ (fun j => |x_hat j|) :=
  backSub_forward_error_diagDom fp n U U_inv x b hDD hInv hTx hn

/-- **Equation (8.6)**: lower-triangular analogue of condition (8.5). -/
def higham8_6_diagDominantLower (n : ℕ) (L : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, i.val < j.val → L i j = 0) ∧
  (∀ i : Fin n, L i i ≠ 0) ∧
  (∀ i j : Fin n, j.val < i.val → |L i j| ≤ |L i i|)

/-- Source condition preceding **Lemma 8.8**, as printed in the PDF:
`|u_ii| ≤ sum_{j=i+1}^n |u_ij|` for rows `i = 1:n-1`, together with upper
triangular shape.  The inequality direction is intentionally the source text's
direction. -/
def higham8_rowDominantUpperSource (n : ℕ) (U : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
  ∀ i : Fin n, i.val + 1 < n →
    |U i i| ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |U i j|

/-- **Theorem 8.10**, formalized with Higham's exact `μ` recurrence rather
than an informal `O(u^2)` abbreviation. -/
theorem higham8_10_forwardSub_forward_error_mu_bound (fp : FPModel) (n : ℕ)
    (L L_inv M_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsInverse n L L_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n L) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1)) :
    let x_hat := fl_forwardSub fp n L b
    let y := fun i => ∑ j : Fin n, M_inv i j * |b j|
    ∀ i : Fin n, |x i - x_hat i| ≤ mu fp n i.val * y i :=
  forwardSub_forward_error_mu_bound fp n L L_inv M_inv x b hL_diag hLT hInv
    hM_RInv hM_inv_lt hTx hn hn1

/-- **Corollary 8.11**, μ-form for lower triangular M-matrices and `b ≥ 0`. -/
theorem higham8_11_mmatrix_forwardSub_relative_error (fp : FPModel) (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag_pos : ∀ i : Fin n, 0 < L i i)
    (hL_offdiag : ∀ i j : Fin n, j.val < i.val → L i j ≤ 0)
    (hInv : IsInverse n L L_inv)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (h2n : gammaValid fp (2 * n)) :
    let x_hat := fl_forwardSub fp n L b
    (∀ i, 0 ≤ x i) ∧
    (∀ i, 0 ≤ x_hat i) ∧
    (∀ i, |x i - x_hat i| ≤ mu fp n i.val * |x i|) :=
  mmatrix_forwardSub_relative_error fp n L L_inv x b hLT hL_diag_pos
    hL_offdiag hInv hTx hb hn hn1 h2n

/-! ## §8.3 Bounds for the Inverse -/

/-- **Equation (8.7)**: Higham's comparison matrix. -/
noncomputable def higham8_7_comparisonMatrix (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  comparisonMatrix n A

/-- **Theorem 8.12**, first comparison-matrix inverse inequality. -/
theorem higham8_12_abs_inv_le_comparison_inv (n : ℕ)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    ∀ i j : Fin n, |U_inv i j| ≤ M_inv i j :=
  abs_inv_le_compMatrix_inv n U U_inv M_inv hUT hU_diag hInv hM_RInv hM_inv_ut

/-- **Algorithm 8.13**, output quantity: the comparison-inverse ∞-norm bound. -/
noncomputable def higham8_13_mu {n : ℕ} (M_inv : Fin n → Fin n → ℝ) : ℝ :=
  infNorm M_inv

/-- **Algorithm 8.13**, exact vector computed by solving `M(U)y = e`. -/
noncomputable def higham8_13_y {n : ℕ} (M_inv : Fin n → Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j : Fin n, M_inv i j

/-- **Algorithm 8.13**, exact recurrence for `y = M(U)⁻¹e`. -/
theorem higham8_13_comparison_inverse_row_recurrence (n : ℕ)
    (U M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (i : Fin n) :
    |U i i| * higham8_13_y M_inv i = 1 +
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
        |U i j| * higham8_13_y M_inv j :=
  compMatrix_inv_upper_row_eq_ones n U M_inv hUT hU_diag hM_RInv i

/-- **Algorithm 8.13**, certified upper-bound property.  If `M_inv` is the
inverse of the comparison matrix and dominates `|U_inv|`, its displayed
∞-norm is an upper bound for `‖U⁻¹‖∞`. -/
theorem higham8_13_inverse_bound_from_comparison {n : ℕ}
    (U_inv M_inv : Fin n → Fin n → ℝ)
    (habs : ∀ i j : Fin n, |U_inv i j| ≤ M_inv i j) :
    infNorm U_inv ≤ higham8_13_mu M_inv := by
  unfold higham8_13_mu
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |U_inv i j|
        ≤ ∑ j : Fin n, M_inv i j := by
          apply Finset.sum_le_sum
          intro j _
          exact habs i j
      _ = ∑ j : Fin n, |M_inv i j| := by
          apply Finset.sum_congr rfl
          intro j _
          exact (abs_of_nonneg ((abs_nonneg (U_inv i j)).trans (habs i j))).symm
      _ ≤ infNorm M_inv := row_sum_le_infNorm M_inv i
  · exact infNorm_nonneg M_inv

/-- **Theorem 8.14**, ∞-norm lower-bound part of (8.9). -/
theorem higham8_14_infNorm_lowerBound (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
      (fun k => |U k k|)) ≤ infNorm U_inv := by
  classical
  let α : ℝ :=
    Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩ (fun k : Fin n => |U k k|)
  rcases Finset.exists_mem_eq_inf'
      (s := Finset.univ) ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|) with
    ⟨k, _hk_mem, hα_eq⟩
  have hrow :
      1 / |U k k| ≤ ∑ j : Fin n, |U_inv k j| :=
    triInv_row_sum_lowerBound n U U_inv hDD.1 hDD.2.1 hInv k
  calc
    1 / α = 1 / |U k k| := by
      simpa [α] using congrArg (fun x : ℝ => 1 / x) hα_eq
    _ ≤ ∑ j : Fin n, |U_inv k j| := hrow
    _ ≤ infNorm U_inv := row_sum_le_infNorm U_inv k

/-- **Theorem 8.14**, ∞-norm part of the inverse-bound chain under (8.5). -/
theorem higham8_14_infNorm_upperBound (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    infNorm U_inv ≤
      2 ^ (n - 1) *
        (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
          (fun k => |U k k|)) :=
  triInv_infNorm_upperBound n U U_inv i0 hDD hInv

/-! ## Problems -/

/-- **Problem 8.8(a)**, constructive singular rank-one perturbation.

    If `A_inv` is a right inverse of `A` and the `(j,i)` entry of `A_inv` is
    nonzero, then adding `α e_i e_jᵀ` with `α = -(A_inv j i)⁻¹` makes `A`
    singular.  This formalizes the source's possible case
    `α_ij = -(e_jᵀ A⁻¹ e_i)⁻¹`. -/
theorem higham8_8_rankOne_singular_update (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n)
    (hRInv : IsRightInverse n A A_inv)
    (hentry : A_inv j i ≠ 0) :
    Matrix.det
      (Matrix.of A +
        Matrix.single i j (-(A_inv j i)⁻¹)) = 0 := by
  classical
  let x : Fin n → ℝ := fun k => A_inv k i
  have hx_ne : x ≠ 0 := by
    intro hx
    exact hentry (congr_fun hx j)
  have hAx : ∀ r : Fin n, Matrix.mulVec (Matrix.of A) x r =
      if r = i then 1 else 0 := by
    intro r
    simpa [Matrix.mulVec, dotProduct, x] using hRInv r i
  have hmul :
      Matrix.mulVec
        (Matrix.of A + Matrix.single i j (-(A_inv j i)⁻¹)) x = 0 := by
    ext r
    by_cases hri : r = i
    · subst r
      simp [Matrix.add_mulVec, Matrix.single_mulVec, hAx, x]
      field_simp [hentry]
      norm_num
    · simp [Matrix.add_mulVec, Matrix.single_mulVec, hAx, x, hri]
  exact
    (Matrix.exists_mulVec_eq_zero_iff
      (M := (Matrix.of A +
        Matrix.single i j (-(A_inv j i)⁻¹)))).mp
      ⟨x, hx_ne, hmul⟩

end LeanFpAnalysis.FP
