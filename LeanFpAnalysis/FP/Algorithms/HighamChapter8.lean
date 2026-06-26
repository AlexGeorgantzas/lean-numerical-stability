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
import LeanFpAnalysis.FP.Analysis.HighamChapter7
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

/-- Geometric helper for the closed-form tails in the stress-matrix inverse. -/
lemma higham8_geom_one_add_mul_sum (α : ℝ) :
    ∀ m : ℕ, 1 + α * ∑ r ∈ Finset.range m, (1 + α) ^ r = (1 + α) ^ m := by
  intro m
  induction m with
  | zero =>
      simp
  | succ m ihm =>
      rw [Finset.sum_range_succ]
      calc
        1 + α * (∑ r ∈ Finset.range m, (1 + α) ^ r + (1 + α) ^ m)
            = (1 + α * ∑ r ∈ Finset.range m, (1 + α) ^ r) + α * (1 + α) ^ m := by
                ring
        _ = (1 + α) ^ m + α * (1 + α) ^ m := by
                rw [ihm]
        _ = (1 + α) ^ (m + 1) := by
                rw [pow_succ']
                ring

/-- **Equation (8.4)** support: the explicit inverse formula has column sums
`(1 + α)^j`. -/
theorem higham8_4_stressUpperInvFormula_col_sum (n : ℕ) (α : ℝ) (j : Fin n) :
    ∑ i : Fin n, higham8_4_stressUpperInvFormula n α i j = (1 + α) ^ j.val := by
  induction n with
  | zero =>
      exact Fin.elim0 j
  | succ n ih =>
      cases j using Fin.cases with
      | zero =>
          rw [Fin.sum_univ_succ]
          simp [higham8_4_stressUpperInvFormula]
      | succ j =>
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ i : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α i.succ (Fin.succ j)) =
                ∑ i : Fin n, higham8_4_stressUpperInvFormula n α i j := by
            apply Finset.sum_congr rfl
            intro i _hi
            simp [higham8_4_stressUpperInvFormula]
          have hhead :
              higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) =
                α * (1 + α) ^ j.val := by
            have hzero : (0 : Fin (n + 1)) ≠ Fin.succ j := by
              intro h
              exact Fin.succ_ne_zero j h.symm
            simp [higham8_4_stressUpperInvFormula, hzero]
          calc
            higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) +
                ∑ i : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α i.succ (Fin.succ j)
                =
              α * (1 + α) ^ j.val +
                ∑ i : Fin n, higham8_4_stressUpperInvFormula n α i j := by
                  rw [hhead, htail]
            _ = α * (1 + α) ^ j.val + (1 + α) ^ j.val := by
                  rw [ih j]
            _ = (1 + α) ^ (Fin.succ j).val := by
                  rw [show (Fin.succ j).val = j.val + 1 by rfl, pow_succ']
                  ring

/-- **Equation (8.4)** support: the explicit inverse formula has row sums
`(1 + α)^(n - 1 - i)`. -/
theorem higham8_4_stressUpperInvFormula_row_sum (n : ℕ) (α : ℝ) (i : Fin n) :
    ∑ j : Fin n, higham8_4_stressUpperInvFormula n α i j =
      (1 + α) ^ (n - 1 - i.val) := by
  induction n with
  | zero =>
      exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ j : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α 0 j.succ) =
                α * ∑ j : Fin n, (1 + α) ^ j.val := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            have hzero : (0 : Fin (n + 1)) ≠ j.succ := by
              intro h
              exact Fin.succ_ne_zero j h.symm
            simp [higham8_4_stressUpperInvFormula, hzero]
          calc
            higham8_4_stressUpperInvFormula (n + 1) α 0 0 +
                ∑ j : Fin n, higham8_4_stressUpperInvFormula (n + 1) α 0 j.succ
                =
              1 + α * ∑ j : Fin n, (1 + α) ^ j.val := by
                  rw [htail]
                  simp [higham8_4_stressUpperInvFormula]
            _ = 1 + α * ∑ r ∈ Finset.range n, (1 + α) ^ r := by
                  rw [Fin.sum_univ_eq_sum_range]
            _ = (1 + α) ^ n := higham8_geom_one_add_mul_sum α n
            _ = (1 + α) ^ ((n + 1) - 1 - (0 : Fin (n + 1)).val) := by
                  simp
      | succ i =>
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ j : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α (Fin.succ i) j.succ) =
                ∑ j : Fin n, higham8_4_stressUpperInvFormula n α i j := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [higham8_4_stressUpperInvFormula]
          calc
            higham8_4_stressUpperInvFormula (n + 1) α (Fin.succ i) 0 +
                ∑ j : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α (Fin.succ i) j.succ
                =
              ∑ j : Fin n, higham8_4_stressUpperInvFormula n α i j := by
                  rw [htail]
                  simp [higham8_4_stressUpperInvFormula]
            _ = (1 + α) ^ (n - 1 - i.val) := ih i
            _ = (1 + α) ^ ((n + 1) - 1 - (Fin.succ i).val) := by
                  have hexp : n - 1 - i.val = n - (i.val + 1) := by
                    have hi : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
                    omega
                  simpa using congrArg (fun m : Nat => (1 + α) ^ m) hexp

/-- **Equation (8.4)**: the displayed inverse-entry formula is a genuine right
inverse of the stress matrix `U(α)`. -/
theorem higham8_4_stressUpperInvFormula_isRightInverse (n : ℕ) (α : ℝ) :
    IsRightInverse n (higham8_3_stressUpper n α) (higham8_4_stressUpperInvFormula n α) := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro i j
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α 0 k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ 0) = 0 := by
                apply Finset.sum_eq_zero
                intro k _hk
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
              rw [htail]
              simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
          | succ j =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α 0 k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)) =
                    -α * ∑ k : Fin n, higham8_4_stressUpperInvFormula n α k j := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _hk
                have hzero : (0 : Fin (n + 1)) ≠ k.succ := by
                  intro h
                  exact Fin.succ_ne_zero k h.symm
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula, hzero]
              have hzeroj : (0 : Fin (n + 1)) ≠ Fin.succ j := by
                intro h
                exact Fin.succ_ne_zero j h.symm
              calc
                higham8_3_stressUpper (n + 1) α 0 0 *
                    higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) +
                    ∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α 0 k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)
                    =
                  α * (1 + α) ^ j.val - α * ∑ k : Fin n,
                    higham8_4_stressUpperInvFormula n α k j := by
                      rw [htail]
                      simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula, hzeroj]
                      ring
                _ = α * (1 + α) ^ j.val - α * (1 + α) ^ j.val := by
                      rw [higham8_4_stressUpperInvFormula_col_sum n α j]
                _ = 0 := by ring
                _ = (if (0 : Fin (n + 1)) = Fin.succ j then 1 else 0) := by
                      simp [hzeroj]
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α (Fin.succ i) k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ 0) = 0 := by
                apply Finset.sum_eq_zero
                intro k _hk
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
              rw [htail]
              simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
          | succ j =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α (Fin.succ i) k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)) =
                    ∑ k : Fin n,
                      higham8_3_stressUpper n α i k *
                        higham8_4_stressUpperInvFormula n α k j := by
                apply Finset.sum_congr rfl
                intro k _hk
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
              calc
                higham8_3_stressUpper (n + 1) α (Fin.succ i) 0 *
                    higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) +
                    ∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α (Fin.succ i) k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)
                    =
                  ∑ k : Fin n,
                    higham8_3_stressUpper n α i k *
                      higham8_4_stressUpperInvFormula n α k j := by
                      rw [htail]
                      simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
                _ = (if i = j then 1 else 0) := ih i j
                _ = (if (Fin.succ i : Fin (n + 1)) = Fin.succ j then 1 else 0) := by
                      simp

/-- **Equation (8.4)**: the displayed inverse-entry formula is a genuine
two-sided inverse of the stress matrix `U(α)`. -/
theorem higham8_4_stressUpperInvFormula_isInverse (n : ℕ) (α : ℝ) :
    IsInverse n (higham8_3_stressUpper n α) (higham8_4_stressUpperInvFormula n α) := by
  have hRight := higham8_4_stressUpperInvFormula_isRightInverse n α
  exact ⟨ch7_isLeftInverse_of_isRightInverse hRight, hRight⟩

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

/-- Corrected source-facing condition for **Lemma 8.8**: `U` is upper
triangular with nonzero diagonal and the strict-upper absolute row sum is
bounded by the diagonal magnitude in each row. -/
def higham8_8_rowDiagDominantUpper (n : ℕ) (U : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
  (∀ i : Fin n, U i i ≠ 0) ∧
  (∀ i : Fin n,
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |U i j| ≤ |U i i|)

/-- **Lemma 8.8**, corrected theorem surface after the source audit.

If an upper-triangular matrix has nonzero diagonal and each strict-upper row
sum is bounded by the diagonal magnitude, then its Skeel condition number is
at most `2n - 1`. -/
theorem higham8_8_rowDiagDominantUpper_condSkeel_bound (n : ℕ) (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (hRD : higham8_8_rowDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    condSkeel n hn U U_inv ≤ 2 * (n : ℝ) - 1 := by
  rcases hRD with ⟨hUT, hDiag, hRow⟩
  rcases hInv with ⟨hLInv, hRInv⟩
  have hInv_ut := inv_upper_tri n U U_inv hUT hDiag hLInv
  let V : Fin n → Fin n → ℝ := fun a b => U a b / U a a
  let V_inv : Fin n → Fin n → ℝ := fun a b => U_inv a b * U b b
  have hVT : ∀ a b : Fin n, b.val < a.val → V a b = 0 := by
    intro a b hab
    simp [V, hUT a b hab]
  have hV_unit : ∀ a : Fin n, V a a = 1 := by
    intro a
    simp [V, hDiag a]
  have hV_row : ∀ a : Fin n,
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |V a j| ≤ 1 := by
    intro a
    calc
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |V a j|
          = (1 / |U a a|) *
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |U a j| := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              simp [V, div_eq_mul_inv, mul_comm]
      _ ≤ (1 / |U a a|) * |U a a| := by
            exact mul_le_mul_of_nonneg_left (hRow a) (one_div_nonneg.mpr (abs_nonneg _))
      _ = 1 := by
            rw [one_div, inv_mul_cancel₀]
            exact abs_ne_zero.mpr (hDiag a)
  have hVinv_ut : ∀ a b : Fin n, b.val < a.val → V_inv a b = 0 := by
    intro a b hab
    simp [V_inv, hInv_ut a b hab]
  have hVinv_diag : ∀ a : Fin n, V_inv a a = 1 := by
    intro a
    simp [V_inv, inv_diag_entry n U U_inv hUT hDiag hLInv hInv_ut a, hDiag a]
  have hVRInv : IsRightInverse n V V_inv := by
    intro a b
    unfold V V_inv
    have hsimp :
        ∑ k : Fin n, (U a k / U a a) * (U_inv k b * U b b) =
          (U b b / U a a) * ∑ k : Fin n, U a k * U_inv k b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      field_simp [hDiag a]
    rw [hsimp, hRInv a b]
    by_cases hab : a = b
    · subst hab
      simp [hDiag a]
    · simp [hab]
  have hVinv_le_one :=
    unitUpperTri_inv_entry_le_one_of_row_sum_le_one
      n V V_inv hVT hV_unit hV_row hVRInv hVinv_ut hVinv_diag
  let rowMass : Fin n → ℝ := fun j => ∑ k : Fin n, |U j k|
  have hrow_le_two_diag : ∀ j : Fin n, rowMass j ≤ 2 * |U j j| := by
    intro j
    unfold rowMass
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hrest_eq :
        ∑ k ∈ Finset.univ.erase j, |U j k| =
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val < k.val), |U j k| := by
      symm
      apply Finset.sum_subset
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
      · intro k hk hknot
        rw [Finset.mem_erase] at hk
        have hknot' : ¬ j.val < k.val := by
          intro hlt
          exact hknot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
        have hlt : k.val < j.val := by
          by_contra hge
          push_neg at hge
          exact hk.1 (Fin.ext (by omega))
        rw [hUT j k hlt, abs_zero]
    rw [hrest_eq]
    linarith [hRow j]
  let last : Fin n := ⟨n - 1, by omega⟩
  have hrow_last : rowMass last = |U last last| := by
    unfold rowMass
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ last)]
    suffices hrest : ∑ k ∈ Finset.univ.erase last, |U last k| = 0 by
      linarith
    apply Finset.sum_eq_zero
    intro k hk
    have hk_ne : k ≠ last := Finset.ne_of_mem_erase hk
    have hlt : k.val < last.val := by
      have hk_last : k.val ≠ n - 1 := by
        intro hk_eq
        apply hk_ne
        exact Fin.ext (by simpa [last] using hk_eq)
      show k.val < n - 1
      omega
    rw [hUT last k hlt, abs_zero]
  have hsum_upper :
      ∀ i : Fin n,
      ∑ j : Fin n, |U_inv i j| * rowMass j =
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val),
          |U_inv i j| * rowMass j := by
    intro i
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
    rw [hInv_ut i j hj, abs_zero, zero_mul]
  unfold condSkeel
  apply Finset.sup'_le
  intro i _
  change ∑ j : Fin n, |U_inv i j| * rowMass j ≤ 2 * (n : ℝ) - 1
  let S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => i.val ≤ j.val)
  have hlast_mem : last ∈ S := by
    simp [S, last]
    show i.val ≤ n - 1
    omega
  have hlast_term : |U_inv i last| * rowMass last ≤ 1 := by
    rw [hrow_last]
    calc
      |U_inv i last| * |U last last| = |V_inv i last| := by
        simp [V_inv, abs_mul, mul_comm]
      _ ≤ 1 := hVinv_le_one i last (by
        show i.val ≤ n - 1
        omega)
  have hrest_le :
      ∑ j ∈ S.erase last, |U_inv i j| * rowMass j ≤
        ∑ j ∈ S.erase last, (2 : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjS : j ∈ S := (Finset.mem_erase.mp hj).2
    have hij : i.val ≤ j.val := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
      exact hjS
    calc
      |U_inv i j| * rowMass j ≤ |U_inv i j| * (2 * |U j j|) := by
        exact mul_le_mul_of_nonneg_left (hrow_le_two_diag j) (abs_nonneg _)
      _ = 2 * |V_inv i j| := by
        ring_nf
        simp [V_inv, abs_mul, mul_comm]
      _ ≤ 2 := by
        have hle : |V_inv i j| ≤ 1 := hVinv_le_one i j hij
        nlinarith
  have hrest_subset :
      ∑ j ∈ S.erase last, (2 : ℝ) ≤ ∑ j ∈ Finset.univ.erase last, (2 : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro j hj
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩)
      (by
        intro j _ _
        positivity)
  calc
    ∑ j : Fin n, |U_inv i j| * rowMass j
        = ∑ j ∈ S, |U_inv i j| * rowMass j := by
            simpa [S] using hsum_upper i
    _ = |U_inv i last| * rowMass last +
          ∑ j ∈ S.erase last, |U_inv i j| * rowMass j := by
            rw [← Finset.add_sum_erase _ _ hlast_mem]
    _ ≤ 1 + ∑ j ∈ S.erase last, (2 : ℝ) := by
          exact add_le_add hlast_term hrest_le
    _ ≤ 1 + ∑ j ∈ Finset.univ.erase last, (2 : ℝ) := by
          simpa [add_comm] using add_le_add_left hrest_subset 1
    _ = 2 * (n : ℝ) - 1 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ last),
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
          ring

/-- The absolute value of the comparison matrix agrees entrywise with `|T|`. -/
private lemma comparisonMatrix_abs_apply (n : ℕ) (T : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    |comparisonMatrix n T i j| = |T i j| := by
  by_cases hij : i = j
  · subst hij
    simp [comparisonMatrix]
  · simp [comparisonMatrix, hij]

/-- Entrywise decomposition of `|M(T)|` as `2 diag(|t_ii|) - M(T)`. -/
private lemma comparisonMatrix_abs_eq_two_diag_sub (n : ℕ) (T : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    |comparisonMatrix n T i j| =
      2 * diagMatrix (fun k : Fin n => |T k k|) i j - comparisonMatrix n T i j := by
  by_cases hij : i = j
  · subst hij
    simp [comparisonMatrix, diagMatrix]
    ring
  · simp [comparisonMatrix, diagMatrix, hij]

/-- **Lemma 8.9**, explicit image vector
`(2 M(T)⁻¹ diag(|t_ii|) - I)|x|`. -/
noncomputable def higham8_9_comparisonImage (n : ℕ)
    (T M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 2 * ∑ j : Fin n, M_inv i j * |T j j| * |x j| - |x i|

/-- **Lemma 8.9**, equality part for the comparison matrix:
`cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_comparisonMatrix_condAtSolution_eq (n : ℕ) (hn : 0 < n)
    (T M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hM_nonneg : ∀ i j : Fin n, 0 ≤ M_inv i j)
    (hM_left : IsLeftInverse n (comparisonMatrix n T) M_inv) :
    ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x =
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have hdiagMul :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k =
          M_inv i k * |T k k| := by
    intro i k
    simpa [matMul] using
      matMul_diagMatrix_right M_inv (fun l : Fin n => |T l l|) i k
  have hleftEntry :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * comparisonMatrix n T j k = idMatrix n i k := by
    intro i k
    simpa [idMatrix] using hM_left i k
  have hcomparisonEntry :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k| =
          2 * (M_inv i k * |T k k|) - idMatrix n i k := by
    intro i k
    calc
      ∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k|
          = ∑ j : Fin n,
              (2 * (M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k) -
                M_inv i j * comparisonMatrix n T j k) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [comparisonMatrix_abs_eq_two_diag_sub n T j k]
              ring
      _ = 2 * ∑ j : Fin n, M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k -
            ∑ j : Fin n, M_inv i j * comparisonMatrix n T j k := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * (M_inv i k * |T k k|) - idMatrix n i k := by
            rw [hdiagMul i k, hleftEntry i k]
  have happly :
      ∀ i : Fin n,
        ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
            (fun _ => 0) x i =
          higham8_9_comparisonImage n T M_inv x i := by
    intro i
    unfold ch7AmplifiedRhsEF higham8_9_comparisonImage
    calc
      ∑ j : Fin n, |M_inv i j| *
          (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0)
          = ∑ j : Fin n, M_inv i j *
              ∑ k : Fin n, |comparisonMatrix n T j k| * |x k| := by
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_of_nonneg (hM_nonneg i j)]
              simp
      _ = ∑ k : Fin n,
            (∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k|) * |x k| := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ k : Fin n,
            (2 * (M_inv i k * |T k k|) - idMatrix n i k) * |x k| := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hcomparisonEntry i k]
      _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| -
            ∑ k : Fin n, idMatrix n i k * |x k| := by
            calc
              ∑ k : Fin n, (2 * (M_inv i k * |T k k|) - idMatrix n i k) * |x k|
                  = ∑ k : Fin n,
                      (2 * (M_inv i k * |T k k| * |x k|) -
                        idMatrix n i k * |x k|) := by
                        apply Finset.sum_congr rfl
                        intro k _
                        ring
              _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| -
                    ∑ k : Fin n, idMatrix n i k * |x k| := by
                      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| - |x i| := by
            simp [idMatrix]
  have hnonneg :
      ∀ i : Fin n, 0 ≤ higham8_9_comparisonImage n T M_inv x i := by
    intro i
    rw [← happly i]
    exact
      ch7AmplifiedRhsEF_nonneg n M_inv
        (fun a b => |comparisonMatrix n T a b|) (fun _ => 0) x
        (by
          intro a b
          exact abs_nonneg _)
        (by
          intro a
          simp)
        i
  have hforward :
      ch7ForwardBoundEF n hn M_inv (fun a b => |comparisonMatrix n T a b|)
          (fun _ => 0) x =
        infNormVec (higham8_9_comparisonImage n T M_inv x) := by
    unfold ch7ForwardBoundEF
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      rw [happly i, ← abs_of_nonneg (hnonneg i)]
      exact abs_le_infNormVec (higham8_9_comparisonImage n T M_inv x) i
    · apply infNormVec_le_of_abs_le
      · intro i
        rw [abs_of_nonneg (hnonneg i), ← happly i]
        exact
          Finset.le_sup'
            (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
              (fun _ => 0) x)
            (Finset.mem_univ i)
      · exact
          ch7ForwardBoundEF_nonneg n hn M_inv
            (fun a b => |comparisonMatrix n T a b|) (fun _ => 0) x
            (by
              intro a b
              exact abs_nonneg _)
            (by
              intro a
              simp)
  unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf
  rw [hforward]

/-- **Lemma 8.9**, inequality part:
`cond(T,x) ≤ cond(M(T),x)` once `|T⁻¹| ≤ M(T)⁻¹` and `M(T)⁻¹ ≥ 0` are known. -/
theorem higham8_9_condAtSolution_le_comparisonMatrix (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (habsInv : ∀ i j : Fin n, |T_inv i j| ≤ M_inv i j)
    (hM_nonneg : ∀ i j : Fin n, 0 ≤ M_inv i j) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := by
  have hnum :
      ch7ForwardBoundEF n hn T_inv (fun a b => |T a b|) (fun _ => 0) x ≤
        ch7ForwardBoundEF n hn M_inv (fun a b => |comparisonMatrix n T a b|)
          (fun _ => 0) x := by
    unfold ch7ForwardBoundEF
    apply Finset.sup'_le
    intro i _
    unfold ch7AmplifiedRhsEF
    calc
      ∑ j : Fin n, |T_inv i j| * (∑ k : Fin n, |T j k| * |x k| + 0)
          ≤ ∑ j : Fin n, M_inv i j * (∑ k : Fin n, |T j k| * |x k| + 0) := by
              apply Finset.sum_le_sum
              intro j _
              have hinner_nonneg : 0 ≤ ∑ k : Fin n, |T j k| * |x k| + 0 := by
                positivity
              exact mul_le_mul_of_nonneg_right (habsInv i j) hinner_nonneg
      _ = ∑ j : Fin n, M_inv i j *
            (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0) := by
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            have hsumEq :
                ∑ k : Fin n, |T j k| * |x k| =
                  ∑ k : Fin n, |comparisonMatrix n T j k| * |x k| := by
              apply Finset.sum_congr rfl
              intro k _
              rw [comparisonMatrix_abs_apply]
            rw [hsumEq]
      _ = ∑ j : Fin n, |M_inv i j| *
            (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hM_nonneg i j)]
      _ = ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
            (fun _ => 0) x i := by
            rfl
      _ ≤ Finset.sup' Finset.univ
            (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
            (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
              (fun _ => 0) x) := by
            exact
              Finset.le_sup'
                (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
                  (fun _ => 0) x)
                (Finset.mem_univ i)
  unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf
  exact div_le_div_of_nonneg_right hnum (infNormVec_nonneg x)

/-- **Lemma 8.9**, upper-triangular source wrapper:
`cond(T,x) ≤ cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_upperTriangular_condAtSolution_le_comparison_eq (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag : ∀ i : Fin n, T i i ≠ 0)
    (hInv : IsInverse n T T_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n T) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have habsInv :=
    abs_inv_le_compMatrix_inv n T T_inv M_inv
      hUT hT_diag hInv hM_RInv hM_inv_ut
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n T i i := by
    intro i
    simp [comparisonMatrix]
    exact hT_diag i
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n T i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n T i j = 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n T) M_inv
      hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  have hle :=
    higham8_9_condAtSolution_le_comparisonMatrix n hn T T_inv M_inv x habsInv hM_nonneg
  have heq :=
    higham8_9_comparisonMatrix_condAtSolution_eq n hn T M_inv x
      hM_nonneg (ch7_isLeftInverse_of_isRightInverse hM_RInv)
  calc
    ch7SkeelCondAtSolutionInf n hn T T_inv x
        ≤ ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := hle
    _ = infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := heq

/-- **Lemma 8.9**, lower-triangular source wrapper:
`cond(T,x) ≤ cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_lowerTriangular_condAtSolution_le_comparison_eq (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → T i j = 0)
    (hT_diag : ∀ i : Fin n, T i i ≠ 0)
    (hInv : IsInverse n T T_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n T) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have habsInv :=
    abs_inv_le_compMatrix_inv_lowerTri n T T_inv M_inv
      hLT hT_diag hInv hM_RInv hM_inv_lt
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n T i i := by
    intro i
    simp [comparisonMatrix]
    exact hT_diag i
  have hM_offdiag : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n T i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_lt : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n T i j = 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega), hLT i j hij]
  have hM_nonneg :=
    lower_tri_mmatrix_inv_nonneg n (comparisonMatrix n T) M_inv
      hM_lt hM_diag_pos hM_offdiag hM_RInv hM_inv_lt
  have hle :=
    higham8_9_condAtSolution_le_comparisonMatrix n hn T T_inv M_inv x habsInv hM_nonneg
  have heq :=
    higham8_9_comparisonMatrix_condAtSolution_eq n hn T M_inv x
      hM_nonneg (ch7_isLeftInverse_of_isRightInverse hM_RInv)
  calc
    ch7SkeelCondAtSolutionInf n hn T T_inv x
        ≤ ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := hle
    _ = infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := heq

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

/-- **Theorem 8.12**: the strict-upper row maximum used to define `W(U)`. -/
noncomputable def higham8_12_rowMaxStrictUpper (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  if h : i.val + 1 < n then
    Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val < j.val))
      (by
        refine ⟨⟨i.val + 1, h⟩, ?_⟩
        simp [Finset.mem_filter]
        exact Fin.lt_def.mpr (by simp))
      (fun j => |U i j|)
  else
    0

/-- The strict-upper row maximum is nonnegative. -/
lemma higham8_12_rowMaxStrictUpper_nonneg (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i : Fin n) :
    0 ≤ higham8_12_rowMaxStrictUpper n U i := by
  by_cases h : i.val + 1 < n
  · have hmem :
        (⟨i.val + 1, h⟩ : Fin n) ∈
          Finset.univ.filter (fun j : Fin n => i.val < j.val) := by
      simp [Finset.mem_filter]
      exact Fin.lt_def.mpr (by simp)
    have hs :
        |U i ⟨i.val + 1, h⟩| ≤
          Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val < j.val))
            ⟨⟨i.val + 1, h⟩, hmem⟩ (fun j => |U i j|) :=
      Finset.le_sup' (fun j => |U i j|) hmem
    simpa [higham8_12_rowMaxStrictUpper, h] using
      (le_trans (abs_nonneg _) hs)
  · simp [higham8_12_rowMaxStrictUpper, h]

/-- Any strict-upper entry is bounded by the corresponding row maximum. -/
lemma higham8_12_abs_le_rowMaxStrictUpper (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i j : Fin n) (hij : i.val < j.val) :
    |U i j| ≤ higham8_12_rowMaxStrictUpper n U i := by
  have hsucc : i.val + 1 < n := by omega
  have hs :
      |U i j| ≤
        Finset.sup' (Finset.univ.filter (fun k : Fin n => i.val < k.val))
          (by
            refine ⟨⟨i.val + 1, hsucc⟩, ?_⟩
            simp [Finset.mem_filter]
            exact Fin.lt_def.mpr (by simp))
          (fun k => |U i k|) :=
    Finset.le_sup' (fun k => |U i k|) (by
      show j ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val)
      exact Finset.mem_filter.mpr ⟨by simp, hij⟩)
  simpa [higham8_12_rowMaxStrictUpper, hsucc] using hs

/-- **Theorem 8.12**: Higham's row-max minorant `W(U)`. -/
noncomputable def higham8_12_WMatrix (n : ℕ)
    (U : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then |U i i|
    else if i.val < j.val then -(higham8_12_rowMaxStrictUpper n U i)
    else 0

/-- `W(U)` is upper triangular by construction. -/
lemma higham8_12_WMatrix_upper (n : ℕ) (U : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, j.val < i.val → higham8_12_WMatrix n U i j = 0 := by
  intro i j hij
  have hnotlt : ¬ i.val < j.val := by omega
  simp [higham8_12_WMatrix, hnotlt,
    show ¬ i = j from Fin.ne_of_val_ne (by omega)]

/-- The diagonal of `W(U)` is the absolute diagonal of `U`. -/
lemma higham8_12_WMatrix_diag (n : ℕ) (U : Fin n → Fin n → ℝ) (i : Fin n) :
    higham8_12_WMatrix n U i i = |U i i| := by
  simp [higham8_12_WMatrix]

/-- Strict-upper entries of `W(U)` are the negated row maxima. -/
lemma higham8_12_WMatrix_strictUpper (n : ℕ) (U : Fin n → Fin n → ℝ)
    {i j : Fin n} (hij : i.val < j.val) :
    higham8_12_WMatrix n U i j = -(higham8_12_rowMaxStrictUpper n U i) := by
  simp [higham8_12_WMatrix, hij, show ¬ i = j from Fin.ne_of_val_ne (by omega)]

/-- The comparison matrix dominates `W(U)` entrywise for upper-triangular `U`. -/
lemma higham8_12_WMatrix_le_comparisonMatrix (n : ℕ)
    (U : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    ∀ i j : Fin n, higham8_12_WMatrix n U i j ≤ comparisonMatrix n U i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [higham8_12_WMatrix, comparisonMatrix]
  · by_cases hlt : i.val < j.val
    · rw [higham8_12_WMatrix_strictUpper n U hlt]
      simpa [comparisonMatrix, hij] using
        (neg_le_neg (higham8_12_abs_le_rowMaxStrictUpper n U i j hlt))
    · have hji : j.val < i.val := by omega
      rw [higham8_12_WMatrix_upper n U i j hji]
      simp [comparisonMatrix, hij, hUT i j hji]

/-- The row maxima satisfy the source `β` bound when every strict-upper entry
is bounded by `β |u_ii|`. -/
lemma higham8_12_rowMaxStrictUpper_le_beta_mul_diag (n : ℕ)
    (U : Fin n → Fin n → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    ∀ i : Fin n, higham8_12_rowMaxStrictUpper n U i ≤ β * |U i i| := by
  intro i
  by_cases h : i.val + 1 < n
  · have hs :
        Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val < j.val))
          (by
            refine ⟨⟨i.val + 1, h⟩, ?_⟩
            simp [Finset.mem_filter]
            exact Fin.lt_def.mpr (by simp))
          (fun j => |U i j|) ≤ β * |U i i| := by
      apply Finset.sup'_le
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hβ_bound i j hj
    simpa [higham8_12_rowMaxStrictUpper, h] using hs
  · simpa [higham8_12_rowMaxStrictUpper, h] using
      (mul_nonneg hβ (abs_nonneg _))

/-- Under `β ≤ 1`, Higham's `W(U)` satisfies the repository's diagonal-dominant
upper-triangular condition (8.5). -/
theorem higham8_12_WMatrix_isDiagDominantUpper (n : ℕ)
    (U : Fin n → Fin n → ℝ) {β : ℝ}
    (hU_diag : ∀ i : Fin n, U i i ≠ 0) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    IsDiagDominantUpper n (higham8_12_WMatrix n U) := by
  refine ⟨higham8_12_WMatrix_upper n U, ?_, ?_⟩
  · intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_ne_zero.mpr (hU_diag i)
  · intro i j hij
    rw [higham8_12_WMatrix_diag, higham8_12_WMatrix_strictUpper n U hij]
    rw [abs_abs, abs_neg, abs_of_nonneg (higham8_12_rowMaxStrictUpper_nonneg n U i)]
    calc
      higham8_12_rowMaxStrictUpper n U i ≤ β * |U i i| :=
        higham8_12_rowMaxStrictUpper_le_beta_mul_diag n U hβ hβ_bound i
      _ ≤ |U i i| := by
        have hdiag_nonneg : 0 ≤ |U i i| := abs_nonneg _
        nlinarith

/-- **Theorem 8.14 support**: once `W(U)` is known to satisfy the source
`β ≤ 1` hypothesis, the existing diagonal-dominant inverse API gives the
rightmost `∞`-norm upper bound for `W(U)⁻¹`. -/
theorem higham8_14_WInv_infNorm_upperBound (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ) (i0 : Fin n) {β : ℝ}
    (hU_diag : ∀ i : Fin n, U i i ≠ 0) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|)
    (hInv : IsInverse n (higham8_12_WMatrix n U) W_inv) :
    infNorm W_inv ≤
      2 ^ (n - 1) *
        (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
          (fun k => |U k k|)) := by
  have hDD :=
    higham8_12_WMatrix_isDiagDominantUpper n U hU_diag hβ hβ1 hβ_bound
  simpa [higham8_12_WMatrix] using
    triInv_infNorm_upperBound n (higham8_12_WMatrix n U) W_inv i0 hDD hInv

/-- **Theorem 8.12**: the source `Z` minorant with diagonal `α` and strict
upper entries `-αβ`. -/
noncomputable def higham8_12_ZMatrix (n : ℕ) (α β : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => α * higham8_3_stressUpper n β i j

/-- Explicit inverse formula for the source `Z` matrix. -/
noncomputable def higham8_12_ZInvFormula (n : ℕ) (α β : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => (1 / α) * higham8_4_stressUpperInvFormula n β i j

/-- The explicit `Z` inverse formula has the same scaled column sums as the
stress-family inverse. -/
theorem higham8_12_ZInvFormula_col_sum (n : ℕ) (α β : ℝ) (j : Fin n) :
    ∑ i : Fin n, higham8_12_ZInvFormula n α β i j =
      (1 / α) * (1 + β) ^ j.val := by
  unfold higham8_12_ZInvFormula
  rw [← Finset.mul_sum, higham8_4_stressUpperInvFormula_col_sum]

/-- The explicit `Z` inverse formula has the same scaled row sums as the
stress-family inverse. -/
theorem higham8_12_ZInvFormula_row_sum (n : ℕ) (α β : ℝ) (i : Fin n) :
    ∑ j : Fin n, higham8_12_ZInvFormula n α β i j =
      (1 / α) * (1 + β) ^ (n - 1 - i.val) := by
  unfold higham8_12_ZInvFormula
  rw [← Finset.mul_sum, higham8_4_stressUpperInvFormula_row_sum]

/-- The explicit inverse formula is a genuine right inverse of the source `Z`
matrix. -/
theorem higham8_12_ZInvFormula_isRightInverse (n : ℕ) (α β : ℝ) (hα : α ≠ 0) :
    IsRightInverse n (higham8_12_ZMatrix n α β) (higham8_12_ZInvFormula n α β) := by
  intro i j
  calc
    ∑ k : Fin n, higham8_12_ZMatrix n α β i k * higham8_12_ZInvFormula n α β k j
        =
      ∑ k : Fin n,
        higham8_3_stressUpper n β i k * higham8_4_stressUpperInvFormula n β k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          unfold higham8_12_ZMatrix higham8_12_ZInvFormula
          field_simp [hα]
    _ = (if i = j then 1 else 0) :=
      higham8_4_stressUpperInvFormula_isRightInverse n β i j

/-- The explicit inverse formula is a genuine two-sided inverse of the source
`Z` matrix. -/
theorem higham8_12_ZInvFormula_isInverse (n : ℕ) (α β : ℝ) (hα : α ≠ 0) :
    IsInverse n (higham8_12_ZMatrix n α β) (higham8_12_ZInvFormula n α β) := by
  have hRight := higham8_12_ZInvFormula_isRightInverse n α β hα
  exact ⟨ch7_isLeftInverse_of_isRightInverse hRight, hRight⟩

/-- The explicit `Z` inverse formula is entrywise nonnegative for `α > 0` and
`β ≥ 0`. -/
lemma higham8_12_ZInvFormula_nonneg (n : ℕ) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ i j : Fin n, 0 ≤ higham8_12_ZInvFormula n α β i j := by
  intro i j
  unfold higham8_12_ZInvFormula
  have hscale : 0 ≤ 1 / α := one_div_nonneg.mpr hα.le
  by_cases hij : i = j
  · simpa [higham8_4_stressUpperInvFormula, hij] using hscale
  · by_cases hlt : i.val < j.val
    · have hpow : 0 ≤ (1 + β) ^ (j.val - i.val - 1) := by
        apply pow_nonneg
        linarith
      rw [higham8_4_stressUpperInvFormula, if_neg hij, if_pos hlt]
      exact mul_nonneg hscale (mul_nonneg hβ hpow)
    · simp [higham8_4_stressUpperInvFormula, hij, hlt]

/-- **Problem 8.5 / Theorem 8.14 support**: the scaled `Z` inverse has exact
∞-norm `(1 + β)^(n-1) / α` when `α > 0` and `β ≥ 0`. -/
theorem higham8_5_ZInvFormula_infNorm_eq (n : ℕ) (hn : 0 < n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    infNorm (higham8_12_ZInvFormula n α β) =
      (1 / α) * (1 + β) ^ (n - 1) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hnonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      have habs :
          ∑ j : Fin n, |higham8_12_ZInvFormula n α β i j| =
            ∑ j : Fin n, higham8_12_ZInvFormula n α β i j := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact abs_of_nonneg (hnonneg i j)
      rw [habs, higham8_12_ZInvFormula_row_sum]
      have hbase : 1 ≤ 1 + β := by linarith
      have hpow :
          (1 + β) ^ (n - 1 - i.val) ≤ (1 + β) ^ (n - 1) :=
        pow_le_pow_right₀ hbase (Nat.sub_le _ _)
      exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)
    · exact mul_nonneg (one_div_nonneg.mpr hα.le) (pow_nonneg (by linarith) _)
  · have hrow := row_sum_le_infNorm (higham8_12_ZInvFormula n α β) i0
    have habs :
        ∑ j : Fin n, |higham8_12_ZInvFormula n α β i0 j| =
          ∑ j : Fin n, higham8_12_ZInvFormula n α β i0 j := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact abs_of_nonneg (hnonneg i0 j)
    rw [habs, higham8_12_ZInvFormula_row_sum] at hrow
    simpa [i0] using hrow

/-- **Problem 8.5 / Theorem 8.14 support**: the scaled `Z` inverse has exact
1-norm `(1 + β)^(n-1) / α` when `α > 0` and `β ≥ 0`. -/
theorem higham8_5_ZInvFormula_oneNorm_eq (n : ℕ) (hn : 0 < n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    oneNorm (higham8_12_ZInvFormula n α β) =
      (1 / α) * (1 + β) ^ (n - 1) := by
  let jLast : Fin n := ⟨n - 1, by omega⟩
  have hnonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  apply le_antisymm
  · apply oneNorm_le_of_col_sum_le
    · intro j
      have habs :
          ∑ i : Fin n, |higham8_12_ZInvFormula n α β i j| =
            ∑ i : Fin n, higham8_12_ZInvFormula n α β i j := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact abs_of_nonneg (hnonneg i j)
      rw [habs, higham8_12_ZInvFormula_col_sum]
      have hbase : 1 ≤ 1 + β := by linarith
      have hpow : (1 + β) ^ j.val ≤ (1 + β) ^ (n - 1) := by
        have hj : j.val ≤ n - 1 := by omega
        exact pow_le_pow_right₀ hbase hj
      exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)
    · exact mul_nonneg (one_div_nonneg.mpr hα.le) (pow_nonneg (by linarith) _)
  · have hcol := col_sum_le_oneNorm (higham8_12_ZInvFormula n α β) jLast
    have habs :
        ∑ i : Fin n, |higham8_12_ZInvFormula n α β i jLast| =
          ∑ i : Fin n, higham8_12_ZInvFormula n α β i jLast := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact abs_of_nonneg (hnonneg i jLast)
    rw [habs, higham8_12_ZInvFormula_col_sum] at hcol
    simpa [jLast] using hcol

/-- **Problem 8.5 / Theorem 8.14 support**: the Euclidean operator norm of the
scaled `Z` inverse is bounded by the same explicit endpoint as the `1`- and
`∞`-norms. -/
theorem higham8_5_ZInvFormula_opNorm2_le (n : ℕ) (hn : 0 < n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
      (1 / α) * (1 + β) ^ (n - 1) := by
  let c : ℝ := (1 / α) * (1 + β) ^ (n - 1)
  have hbound :=
    problem7_10e_complexMatrixOp2_realRectToCMatrix_le_sqrt_one_mul_inf hn
      (higham8_12_ZInvFormula n α β)
  have hone := higham8_5_ZInvFormula_oneNorm_eq n hn hα hβ
  have hinf := higham8_5_ZInvFormula_infNorm_eq n hn hα hβ
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (one_div_nonneg.mpr hα.le) (pow_nonneg (by linarith) _)
  calc
    complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β))
        ≤ Real.sqrt
            (oneNorm (higham8_12_ZInvFormula n α β) *
              infNorm (higham8_12_ZInvFormula n α β)) := hbound
    _ = Real.sqrt (c * c) := by rw [hone, hinf]
    _ = c := by
      rw [show c * c = c ^ 2 by ring]
      simpa [abs_of_nonneg hc_nonneg] using (Real.sqrt_sq_eq_abs c)

/-- **Theorem 8.14 support**: under `β ≤ 1`, the exact `1`-norm of the scaled
`Z` inverse is bounded by `2^(n-1) / α`. -/
theorem higham8_14_ZInvFormula_oneNorm_upperBound (n : ℕ) (hn : 0 < n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    oneNorm (higham8_12_ZInvFormula n α β) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  rw [higham8_5_ZInvFormula_oneNorm_eq n hn hα hβ]
  have hpow : (1 + β) ^ (n - 1) ≤ (2 : ℝ) ^ (n - 1) := by
    have honeβ_nonneg : 0 ≤ 1 + β := by linarith
    have honeβ_le_two : 1 + β ≤ (2 : ℝ) := by linarith
    exact pow_le_pow_left₀ honeβ_nonneg honeβ_le_two (n - 1)
  exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)

/-- **Theorem 8.14 support**: under `β ≤ 1`, the exact `∞`-norm of the scaled
`Z` inverse is bounded by `2^(n-1) / α`. -/
theorem higham8_14_ZInvFormula_infNorm_upperBound (n : ℕ) (hn : 0 < n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    infNorm (higham8_12_ZInvFormula n α β) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  rw [higham8_5_ZInvFormula_infNorm_eq n hn hα hβ]
  have hpow : (1 + β) ^ (n - 1) ≤ (2 : ℝ) ^ (n - 1) := by
    have honeβ_nonneg : 0 ≤ 1 + β := by linarith
    have honeβ_le_two : 1 + β ≤ (2 : ℝ) := by linarith
    exact pow_le_pow_left₀ honeβ_nonneg honeβ_le_two (n - 1)
  exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)

/-- **Theorem 8.14 support**: under `β ≤ 1`, the Euclidean operator norm of
the scaled `Z` inverse is bounded by `2^(n-1) / α`. -/
theorem higham8_14_ZInvFormula_opNorm2_upperBound (n : ℕ) (hn : 0 < n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  have hendpoint := higham8_5_ZInvFormula_opNorm2_le n hn hα hβ
  have hpow : (1 + β) ^ (n - 1) ≤ (2 : ℝ) ^ (n - 1) := by
    have honeβ_nonneg : 0 ≤ 1 + β := by linarith
    have honeβ_le_two : 1 + β ≤ (2 : ℝ) := by linarith
    exact pow_le_pow_left₀ honeβ_nonneg honeβ_le_two (n - 1)
  have hscale :
      (1 / α) * (1 + β) ^ (n - 1) ≤ (1 / α) * (2 : ℝ) ^ (n - 1) :=
    mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)
  exact hendpoint.trans hscale

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
