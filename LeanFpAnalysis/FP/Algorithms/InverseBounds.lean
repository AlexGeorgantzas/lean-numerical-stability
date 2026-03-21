-- Algorithms/InverseBounds.lean
--
-- Higham §8.3: Bounds for the inverse of a triangular matrix.
-- Theorem 8.11 (first inequality): |U⁻¹| ≤ M(U)⁻¹.
-- Theorem 8.13: 1/min|u_ii| ≤ ‖U⁻¹‖_∞ ≤ 2^{n-1}/min|u_ii|
--               under diagonal dominance.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.ForwardError
import LeanFpAnalysis.FP.Algorithms.TriangularForwardBound

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- Comparison matrix M(U)
-- ============================================================

/-- The comparison matrix M(U): m_ij = |u_ii| if i = j, -|u_ij| if i ≠ j.
    For a nonsingular triangular matrix, M(U) is an M-matrix. -/
noncomputable def comparisonMatrix (n : ℕ) (U : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => if i = j then |U i j| else -|U i j|

-- ============================================================
-- M-matrix inverse nonnegativity (triangular case)
-- ============================================================

/-- The inverse of an upper triangular M-matrix has nonneg entries.

    An upper triangular M-matrix has positive diagonal and nonpositive
    off-diagonal entries. Its inverse (also upper triangular) has all
    nonneg entries.

    Proof: By induction on j - i using the right-inverse recurrence.
    For j > i: T_ii * T_inv_ij = -∑ T_ik * T_inv_kj.
    Since T_ik ≤ 0 (off-diagonal) and T_inv_kj ≥ 0 (IH), the sum ≤ 0,
    so T_ii * T_inv_ij ≥ 0. With T_ii > 0, T_inv_ij ≥ 0. -/
theorem upper_tri_mmatrix_inv_nonneg (n : ℕ) (T T_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hRInv : IsRightInverse n T T_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → T_inv i j = 0) :
    ∀ i j : Fin n, 0 ≤ T_inv i j := by
  suffices h : ∀ (d : ℕ), ∀ i j : Fin n, j.val - i.val ≤ d → i.val ≤ j.val →
      0 ≤ T_inv i j from
    fun i j => by
      by_cases hij : i.val ≤ j.val
      · exact h (j.val - i.val) i j (le_refl _) hij
      · push_neg at hij; rw [hInv_ut i j (by omega)]
  intro d
  induction d with
  | zero =>
    intro i j hdiff hij
    have heq : i = j := Fin.ext (by omega)
    subst heq
    -- Diagonal: T_ii * T_inv_ii = 1 from right inverse
    have hR := hRInv i i; simp at hR
    have hdiag : T i i * T_inv i i = 1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hR
      suffices ∑ k ∈ Finset.univ.erase i, T i k * T_inv k i = 0 by linarith
      apply Finset.sum_eq_zero; intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      by_cases hlt : k.val < i.val
      · rw [hUT i k (by omega), zero_mul]
      · rw [hInv_ut k i (by
          rcases Nat.lt_or_ge i.val k.val with h | h
          · exact h
          · exact absurd (Fin.ext (by omega)) hki), mul_zero]
    have : 0 < T_inv i i := by
      by_contra hc; push_neg at hc
      linarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hT_diag_pos i)) hc]
    linarith
  | succ d' ih =>
    intro i j hdiff hij
    by_cases heq : i.val = j.val
    · exact ih i j (by omega) (by omega)
    · have hij' : i.val < j.val := by omega
      have hrec := inv_recurrence n T T_inv hUT (fun k => ne_of_gt (hT_diag_pos k))
        hRInv hInv_ut i j hij'
      have hsum_neg : ∑ k ∈ Finset.univ.filter
          (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
          T i k * T_inv k j ≤ 0 := by
        apply Finset.sum_nonpos; intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact mul_nonpos_of_nonpos_of_nonneg (hT_offdiag i k (by omega))
          (ih k j (by omega) (by omega))
      have h_prod_nn : 0 ≤ T i i * T_inv i j := by linarith
      have h1 : 0 ≤ T i i * T_inv i j / T i i :=
        div_nonneg h_prod_nn (le_of_lt (hT_diag_pos i))
      rwa [mul_div_cancel_left₀ (T_inv i j) (ne_of_gt (hT_diag_pos i))] at h1

-- ============================================================
-- Theorem 8.11: |U⁻¹| ≤ M(U)⁻¹ (first inequality, componentwise)
-- ============================================================

/-- **Theorem 8.11, first inequality** (Higham §8.3).

    For a nonsingular upper triangular U with inverse U_inv, and M_inv the
    inverse of M(U), we have |U_inv_ij| ≤ M_inv_ij componentwise.

    Proof by induction on j - i using recurrences. -/
theorem abs_inv_le_compMatrix_inv (n : ℕ) (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    ∀ i j : Fin n, |U_inv i j| ≤ M_inv i j := by
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hInv.1
  -- M(U) is an upper triangular M-matrix, so its inverse has nonneg entries
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n U i i := by
    intro i; simp [comparisonMatrix]; exact hU_diag i
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n U i j ≤ 0 := by
    intro i j _; simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij; unfold comparisonMatrix
    simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_nn := upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
    hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  -- Now prove |U_inv_ij| ≤ M_inv_ij by induction on j - i
  suffices h : ∀ (d : ℕ), ∀ i j : Fin n, j.val - i.val ≤ d → i.val ≤ j.val →
      |U_inv i j| ≤ M_inv i j from
    fun i j => by
      by_cases hij : i.val ≤ j.val
      · exact h (j.val - i.val) i j (le_refl _) hij
      · push_neg at hij
        rw [hInv_ut i j (by omega), hM_inv_ut i j (by omega), abs_zero]
  intro d
  induction d with
  | zero =>
    intro i j hdiff hij
    have heq : i = j := Fin.ext (by omega)
    subst heq
    -- |U_inv_ii| = 1/|U_ii| = M_inv_ii
    rw [inv_diag_entry n U U_inv hUT hU_diag hInv.1 hInv_ut, abs_div, abs_one]
    -- M_inv_ii = 1/|U_ii| = 1/M(U)_ii from right inverse equation
    have hMR := hM_RInv i i; simp at hMR
    have hM_diag : comparisonMatrix n U i i * M_inv i i = 1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hMR
      suffices ∑ k ∈ Finset.univ.erase i, comparisonMatrix n U i k * M_inv k i = 0 by
        linarith
      apply Finset.sum_eq_zero; intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      by_cases hlt : k.val < i.val
      · rw [hM_ut i k (by omega), zero_mul]
      · rw [hM_inv_ut k i (by
          rcases Nat.lt_or_ge i.val k.val with h | h
          · exact h
          · exact absurd (Fin.ext (by omega)) hki), mul_zero]
    simp [comparisonMatrix] at hM_diag
    have : M_inv i i = 1 / |U i i| := by
      field_simp [ne_of_gt (abs_pos.mpr (hU_diag i))]; linarith
    rw [this]
  | succ d' ih =>
    intro i j hdiff hij
    by_cases heq : i.val = j.val
    · exact ih i j (by omega) (by omega)
    · have hij' : i.val < j.val := by omega
      -- Recurrence for U_inv: U_ii * U_inv_ij = -∑ U_ik * U_inv_kj
      have hrec_U := inv_recurrence n U U_inv hUT hU_diag hInv.2 hInv_ut i j hij'
      -- Similarly for M(U): M_ii * M_inv_ij + ∑ M_ik * M_inv_kj = 0
      have hrec_M := inv_recurrence n (comparisonMatrix n U) M_inv hM_ut
        (fun k => ne_of_gt (hM_diag_pos k)) hM_RInv hM_inv_ut i j hij'
      have hUii_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
      have hUii_ne : U i i ≠ 0 := hU_diag i
      -- From U recurrence: U_ii * U_inv_ij = -(∑ U_ik * U_inv_kj)
      have hU_prod : U i i * U_inv i j =
          -(∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            U i k * U_inv k j) := by linarith
      -- |U_inv_ij| = |U_ii * U_inv_ij| / |U_ii| = |∑...| / |U_ii|
      have habs_eq : |U_inv i j| =
          |∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            U i k * U_inv k j| / |U i i| := by
        have h1 : U_inv i j = -(∑ k ∈ Finset.univ.filter
            (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            U i k * U_inv k j) / U i i := by
          field_simp [hUii_ne]; linarith
        rw [h1, abs_div, abs_neg]
      -- comparisonMatrix n U i i = |U i i|
      have hM_ii : comparisonMatrix n U i i = |U i i| := by simp [comparisonMatrix]
      -- For i < k: comparisonMatrix n U i k = -|U i k|
      have hM_ik : ∀ k : Fin n, i.val < k.val →
          comparisonMatrix n U i k = -|U i k| := by
        intro k hik; unfold comparisonMatrix
        simp [show i ≠ k from Fin.ne_of_val_ne (by omega)]
      -- From M recurrence: |U_ii| * M_inv_ij = ∑ |U_ik| * M_inv_kj
      have hM_prod : |U i i| * M_inv i j =
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            |U i k| * M_inv k j := by
        -- hrec_M: M_ii * M_inv_ij + ∑ M_ik * M_inv_kj = 0
        -- Rewrite M_ik = -|U_ik| for i < k, M_ii = |U_ii|
        have hsum_rw : ∑ k ∈ Finset.univ.filter
            (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            comparisonMatrix n U i k * M_inv k j =
            -(∑ k ∈ Finset.univ.filter
            (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
            |U i k| * M_inv k j) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [hM_ik k hk.1]; ring
        rw [hM_ii] at hrec_M; rw [hsum_rw] at hrec_M; linarith
      -- |U_inv_ij| ≤ (∑ |U_ik| * |U_inv_kj|) / |U_ii|
      --            ≤ (∑ |U_ik| * M_inv_kj) / |U_ii|    (by IH)
      --            = M_inv_ij
      calc |U_inv i j|
          = |∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
              U i k * U_inv k j| / |U i i| := habs_eq
        _ ≤ (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
              |U i k * U_inv k j|) / |U i i| :=
            div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (le_of_lt hUii_pos)
        _ = (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
              |U i k| * |U_inv k j|) / |U i i| := by
            congr 1; apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
        _ ≤ (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
              |U i k| * M_inv k j) / |U i i| := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hUii_pos)
            apply Finset.sum_le_sum; intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            exact mul_le_mul_of_nonneg_left (ih k j (by omega) (by omega)) (abs_nonneg _)
        _ = M_inv i j := by
            rw [← hM_prod]; field_simp [ne_of_gt hUii_pos]

-- ============================================================
-- Theorem 8.13: Row sum bounds under diagonal dominance
-- ============================================================

/-- **Theorem 8.13, lower bound** (Higham §8.3).

    For a nonsingular upper triangular U, the row sum of |U⁻¹| at row i
    satisfies ∑_j |U_inv i j| ≥ 1/|U_ii|.

    In particular, max_i ∑_j |U_inv_ij| ≥ 1/min_k |U_kk|. -/
theorem inv_row_sum_lower (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv) :
    ∀ i : Fin n, 1 / |U i i| ≤ ∑ j : Fin n, |U_inv i j| := by
  intro i
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hInv.1
  have hdiag := inv_diag_entry n U U_inv hUT hU_diag hInv.1 hInv_ut
  calc 1 / |U i i|
      = |1 / U i i| := by rw [abs_div, abs_one]
    _ = |U_inv i i| := by rw [hdiag]
    _ ≤ ∑ j : Fin n, |U_inv i j| := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        linarith [abs_nonneg (U_inv i i),
          Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ.erase i) => abs_nonneg (U_inv i j))]

/-- **Theorem 8.13, upper bound** (Higham §8.3).

    Under diagonal dominance (|U_ii| ≥ |U_ij| for j > i), the row sum
    of |U⁻¹| at row i satisfies
      ∑_j |U_inv i j| ≤ 2^{n-1-i} / min_k |U_kk|.

    In particular, ‖U⁻¹‖_∞ ≤ 2^{n-1} / min_k |U_kk|.

    Proof: Write V = D⁻¹U where D = diag(U_ii). Then V is unit upper
    triangular with |V_ij| ≤ 1, and |U_inv_ij| = |V_inv_ij| / |U_jj|.
    So ∑_j |U_inv_ij| ≤ (1/min_k |U_kk|) · ∑_j |V_inv_ij|
       ≤ (1/min_k |U_kk|) · 2^{n-1-i}   by inv_row_sum_bound. -/
theorem inv_row_sum_upper (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    ∀ i : Fin n, ∑ j : Fin n, |U_inv i j| ≤
      2 ^ (n - 1 - i.val) *
        (1 / Finset.inf' Finset.univ ⟨i, Finset.mem_univ i⟩ (fun k => |U k k|)) := by
  obtain ⟨hUT, hU_diag, hU_dom⟩ := hDD
  obtain ⟨hLInv, _hRInv⟩ := hInv
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hLInv
  intro i
  -- Define V = D⁻¹U, V_inv = U_inv * D (same factoring as lemma_8_6)
  let V : Fin n → Fin n → ℝ := fun a b => U a b / U a a
  let V_inv : Fin n → Fin n → ℝ := fun a b => U_inv a b * U b b
  -- V properties
  have hVT : ∀ a b : Fin n, b.val < a.val → V a b = 0 := by
    intro a b hab; simp only [V, hUT a b hab, zero_div]
  have hV_unit : ∀ a : Fin n, V a a = 1 := by
    intro a; simp only [V]; exact div_self (hU_diag a)
  have hV_bound : ∀ a b : Fin n, a.val < b.val → |V a b| ≤ 1 := by
    intro a b hab; simp only [V, abs_div]
    exact (div_le_one (abs_pos.mpr (hU_diag a))).mpr (hU_dom a b hab)
  -- V_inv properties
  have hVinv_ut : ∀ a b : Fin n, b.val < a.val → V_inv a b = 0 := by
    intro a b hab; simp only [V_inv, hInv_ut a b hab, zero_mul]
  have hVinv_diag : ∀ a : Fin n, V_inv a a = 1 := by
    intro a; simp only [V_inv]
    rw [inv_diag_entry n U U_inv hUT hU_diag hLInv hInv_ut a]
    field_simp [hU_diag a]
  -- V_inv is a left inverse of V
  have hVLInv : IsLeftInverse n V V_inv := by
    intro a b; simp only [V, V_inv]
    have h := hLInv a b
    have hsimp : ∑ k : Fin n, U_inv a k * U k k * (U k b / U k k) =
        ∑ k : Fin n, U_inv a k * U k b := by
      apply Finset.sum_congr rfl; intro k _
      have hk := hU_diag k; field_simp [hk]
    rw [hsimp]; exact h
  -- Key: |U_inv i j| = |V_inv i j| / |U j j|
  have hconv : ∀ j : Fin n, |U_inv i j| = |V_inv i j| / |U j j| := by
    intro j; simp only [V_inv, abs_mul]
    rw [mul_div_cancel_right₀ _ (ne_of_gt (abs_pos.mpr (hU_diag j)))]
  -- Let α = min_k |U_kk|
  let α := Finset.inf' Finset.univ ⟨i, Finset.mem_univ i⟩ (fun k => |U k k|)
  have hα_pos : 0 < α := by
    rw [Finset.lt_inf'_iff]; intro k _; exact abs_pos.mpr (hU_diag k)
  -- Each |U_inv i j| / 1 ≤ |V_inv i j| / α
  -- ∑ |U_inv i j| = ∑ |V_inv i j| / |U j j| ≤ (1/α) ∑ |V_inv i j|
  have hle : ∑ j : Fin n, |U_inv i j| ≤
      (1 / α) * ∑ j : Fin n, |V_inv i j| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    rw [hconv j]
    -- Goal: |V_inv i j| / |U j j| ≤ 1 / α * |V_inv i j|
    rw [← sub_nonneg]
    have hUj_ne : |U j j| ≠ 0 := ne_of_gt (abs_pos.mpr (hU_diag j))
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    have : 1 / α * |V_inv i j| - |V_inv i j| / |U j j| =
        |V_inv i j| * (|U j j| - α) / (α * |U j j|) := by
      field_simp [hα_ne, hUj_ne]
    rw [this]
    apply div_nonneg
    · apply mul_nonneg (abs_nonneg _)
      linarith [Finset.inf'_le (fun k => |U k k|) (Finset.mem_univ j)]
    · exact le_of_lt (mul_pos hα_pos (abs_pos.mpr (hU_diag j)))
  -- ∑ |V_inv i j| ≤ 2^{n-1-i} (V_inv upper tri, then inv_row_sum_bound)
  have hV_sum : ∑ j : Fin n, |V_inv i j| ≤ 2 ^ (n - 1 - i.val) := by
    -- Split: j < i gives 0, j ≥ i bounded by inv_row_sum_bound
    have hsplit : ∑ j : Fin n, |V_inv i j| =
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val), |V_inv i j| := by
      symm; apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      rw [hVinv_ut i j hj, abs_zero]
    rw [hsplit]
    -- Need j.val ≤ n-1 for the last valid index
    by_cases hn : n = 0
    · subst hn; exact absurd i.isLt (by omega)
    · have hn' : 0 < n := by omega
      have hfilt_eq : Finset.univ.filter (fun j : Fin n => i.val ≤ j.val) =
          Finset.univ.filter (fun j : Fin n => i.val ≤ j.val ∧
            j.val ≤ (⟨n - 1, by omega⟩ : Fin n).val) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨h, by omega⟩, fun ⟨h, _⟩ => h⟩
      rw [hfilt_eq]
      exact inv_row_sum_bound n V V_inv hVT hV_unit hV_bound hVLInv hVinv_ut hVinv_diag
        (n - 1 - i.val) i ⟨n - 1, by omega⟩ (by simp) (by simp; omega)
  calc ∑ j : Fin n, |U_inv i j|
      ≤ (1 / α) * ∑ j : Fin n, |V_inv i j| := hle
    _ ≤ (1 / α) * 2 ^ (n - 1 - i.val) :=
        mul_le_mul_of_nonneg_left hV_sum (by positivity)
    _ = 2 ^ (n - 1 - i.val) * (1 / α) := by ring

end LeanFpAnalysis.FP
