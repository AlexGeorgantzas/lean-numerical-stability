-- Algorithms/TriangularForwardBound.lean
--
-- Higham §8.2: Lemma 8.6 (diagonal dominance bound on |U⁻¹||U|)
-- and Theorem 8.7 (componentwise forward error under diagonal dominance).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.ForwardError
import LeanFpAnalysis.FP.Algorithms.TriangularSolve

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- Definitions
-- ============================================================

/-- T_inv is a right inverse of T: T * T_inv = I. -/
def IsRightInverse (n : ℕ) (T T_inv : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, ∑ k : Fin n, T i k * T_inv k j = if i = j then 1 else 0

/-- Full inverse: both left and right inverse. -/
def IsInverse (n : ℕ) (T T_inv : Fin n → Fin n → ℝ) : Prop :=
  IsLeftInverse n T T_inv ∧ IsRightInverse n T T_inv

/-- Upper triangular with diagonal dominance:
    |U_ii| ≥ |U_ij| for all j > i (Higham condition (8.4)). -/
def IsDiagDominantUpper (n : ℕ) (U : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
  (∀ i : Fin n, U i i ≠ 0) ∧
  (∀ i j : Fin n, i.val < j.val → |U i j| ≤ |U i i|)

-- ============================================================
-- Properties of the inverse of an upper triangular matrix
-- ============================================================

/-- The left inverse of an upper triangular matrix is upper triangular.

    Proof by strong induction on j: for each j < i, the left inverse equation
    ∑_k U_inv_ik * U_kj = 0 reduces to U_inv_ij * U_jj = 0
    because all other terms vanish (by upper triangularity of U for k > j,
    and by induction hypothesis for k < j). Since U_jj ≠ 0, U_inv_ij = 0. -/
theorem inv_upper_tri (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsLeftInverse n U U_inv) :
    ∀ i j : Fin n, j.val < i.val → U_inv i j = 0 := by
  -- Prove: ∀ j_val < n, ∀ i with j_val < i, U_inv i j = 0
  -- by strong induction on j_val
  -- Strong induction on j.val: for all jv < n, U_inv i ⟨jv, _⟩ = 0 when jv < i.val
  suffices ∀ (jv : ℕ) (hjv : jv < n), ∀ i : Fin n, jv < i.val →
      U_inv i ⟨jv, hjv⟩ = 0 by
    intro i j hij; exact this j.val j.isLt i hij
  intro jv
  -- Strong induction: assume true for all jv' < jv
  exact Nat.strongRecOn jv (fun jv ih hjv i hi => by
    let j : Fin n := ⟨jv, hjv⟩
    have hij : i ≠ j := Fin.ne_of_val_ne (by simp [j]; omega)
    have h := hInv i j
    simp [hij] at h
    -- Isolate j-th term: U_inv_ij * U_jj = 0
    have : U_inv i j * U j j = 0 := by
      suffices ∑ k : Fin n, U_inv i k * U k j = U_inv i j * U j j by linarith
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      suffices ∑ k ∈ Finset.univ.erase j, U_inv i k * U k j = 0 by linarith
      apply Finset.sum_eq_zero; intro k hk
      have hk_ne := Finset.ne_of_mem_erase hk
      by_cases hklt : k.val < jv
      · -- k < j < i: U_inv_ik = 0 by strong IH
        have hki : k.val < i.val := by omega
        rw [ih k.val hklt (by omega) i hki, zero_mul]
      · -- k > j: U_kj = 0 by upper triangularity
        push_neg at hklt
        have : jv < k.val := by
          by_contra hc; push_neg at hc
          have := le_antisymm (by omega) hklt
          exact hk_ne (Fin.ext (by simp [j]; omega))
        rw [hUT k j (by simp [j]; exact this), mul_zero]
    exact (mul_eq_zero.mp this).elim id (fun h => absurd h (hU_diag _)))

/-- Diagonal entries of the inverse: (U_inv)_ii = 1 / U_ii. -/
theorem inv_diag_entry (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsLeftInverse n U U_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → U_inv i j = 0) :
    ∀ i : Fin n, U_inv i i = 1 / U i i := by
  intro i
  have h := hInv i i
  simp at h
  -- Isolate k = i term
  have honly : ∑ k : Fin n, U_inv i k * U k i = U_inv i i * U i i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    suffices ∑ k ∈ Finset.univ.erase i, U_inv i k * U k i = 0 by linarith
    apply Finset.sum_eq_zero; intro k hk
    have hki := Finset.ne_of_mem_erase hk
    by_cases hlt : k.val < i.val
    · rw [hInv_ut i k hlt, zero_mul]
    · push_neg at hlt
      rw [hUT k i (by omega), mul_zero]
  rw [honly] at h
  have hmul : U_inv i i * U i i = 1 := h
  have hne := hU_diag i
  field_simp [hne]
  linarith

/-- Recursive formula for off-diagonal entries from the right inverse equation.
    For j > i: U_ii * U_inv_ij = -∑_{k: i < k ≤ j} U_ik * U_inv_kj. -/
theorem inv_recurrence (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (_hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hRInv : IsRightInverse n U U_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → U_inv i j = 0) :
    ∀ i j : Fin n, i.val < j.val →
      U i i * U_inv i j +
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
        U i k * U_inv k j = 0 := by
  intro i j hij
  have hR := hRInv i j
  simp [show i ≠ j from Fin.ne_of_val_ne (by omega)] at hR
  -- ∑_k U_ik * U_inv_kj = 0. Split off k=i term.
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hR
  -- The remaining sum over k ≠ i: zero out terms outside {i < k ≤ j}
  have hrest : ∑ k ∈ Finset.univ.erase i, U i k * U_inv k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
        U i k * U_inv k j := by
    symm; apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
    · intro k hk hknot
      rw [Finset.mem_erase] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hknot
      push_neg at hknot
      by_cases hlt : k.val ≤ i.val
      · rw [hUT i k (by omega), zero_mul]
      · push_neg at hlt
        rw [hInv_ut k j (by omega), mul_zero]
  rw [hrest] at hR; linarith

-- ============================================================
-- Entry bound for inverse of unit upper triangular matrix
-- ============================================================

/-- Auxiliary: the sum ∑_{k: i≤k≤j} |V_inv k j| is bounded, where V_inv is
    the inverse of a unit upper triangular matrix with |V_ij| ≤ 1.
    Proved by the "double S" trick: S(i,j) = ∑_{k: i≤k≤j} |V_inv k j| ≤ 2^d.
    Then |V_inv i j| ≤ S(i+1,j) ≤ 2^{d-1}. -/
private theorem inv_sum_bound (n : ℕ) (V V_inv : Fin n → Fin n → ℝ)
    (hVT : ∀ i j : Fin n, j.val < i.val → V i j = 0)
    (hV_unit : ∀ i : Fin n, V i i = 1)
    (hV_bound : ∀ i j : Fin n, i.val < j.val → |V i j| ≤ 1)
    (hRInv : IsRightInverse n V V_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → V_inv i j = 0)
    (hInv_diag : ∀ i : Fin n, V_inv i i = 1) :
    ∀ (d : ℕ), ∀ (i j : Fin n), j.val - i.val = d → i.val ≤ j.val →
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val),
        |V_inv k j| ≤ 2 ^ d := by
  intro d
  induction d with
  | zero =>
    intro i j hdiff hij
    have heq : i = j := Fin.ext (by omega)
    subst heq
    -- Filter contains only k = i
    have : Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ i.val) = {i} := by
      ext k; simp [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨h1, h2⟩; exact Fin.ext (by omega)
      · intro h; subst h; exact ⟨le_refl _, le_refl _⟩
    rw [this, Finset.sum_singleton, hInv_diag, abs_one]; norm_num
  | succ d' ih =>
    intro i j hdiff hij
    -- Split: ∑_{k: i≤k≤j} = |V_inv i j| + ∑_{k: i+1≤k≤j}
    -- = |V_inv i j| + S(i+1, j)
    -- where S(i+1, j) ≤ 2^d' by IH.
    -- Also |V_inv i j| ≤ ∑_{k: i<k≤j} |V_inv k j| = S(i+1, j) ≤ 2^d'.
    -- Total: 2^d' + 2^d' = 2^{d'+1}.
    by_cases heq : i.val = j.val
    · -- i = j contradicts d' + 1 > 0
      omega
    · -- i < j
      have hij' : i.val < j.val := by omega
      -- Step 1: Split off k = i from the sum
      have hi_mem : i ∈ Finset.univ.filter
          (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val) := by
        simp [Finset.mem_filter]; omega
      rw [← Finset.add_sum_erase _ _ hi_mem]
      -- Step 2: The remaining sum is S(i+1, j)
      have hfilt_eq : (Finset.univ.filter
            (fun k : Fin n => i.val ≤ k.val ∧ k.val ≤ j.val)).erase i =
          Finset.univ.filter (fun k : Fin n => i.val + 1 ≤ k.val ∧ k.val ≤ j.val) := by
        ext k; simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hne, h1, h2⟩
          exact ⟨by omega, h2⟩
        · intro ⟨h1, h2⟩
          exact ⟨Fin.ne_of_val_ne (by omega), by omega, h2⟩
      rw [hfilt_eq]
      -- Step 3: The recurrence gives |V_inv i j| ≤ ∑_{k: i<k≤j} |V_inv k j|
      have hrec := inv_recurrence n V V_inv hVT
        (by intro i; rw [hV_unit]; exact one_ne_zero) hRInv hInv_ut i j hij'
      rw [hV_unit, one_mul] at hrec
      have hvinv_eq : V_inv i j = -(∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          i.val < k.val ∧ k.val ≤ j.val), V i k * V_inv k j) := by linarith
      -- |V_inv i j| ≤ ∑_{k: i<k≤j} |V_inv k j|
      have hvinv_bound : |V_inv i j| ≤
          ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            i.val < k.val ∧ k.val ≤ j.val), |V_inv k j| := by
        rw [hvinv_eq, abs_neg]
        calc |∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val < k.val ∧ k.val ≤ j.val), V i k * V_inv k j|
            ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val < k.val ∧ k.val ≤ j.val), |V i k * V_inv k j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val < k.val ∧ k.val ≤ j.val), |V i k| * |V_inv k j| := by
              apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
          _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              i.val < k.val ∧ k.val ≤ j.val), |V_inv k j| := by
              apply Finset.sum_le_sum; intro k hk
              simp [Finset.mem_filter] at hk
              calc |V i k| * |V_inv k j|
                  ≤ 1 * |V_inv k j| :=
                    mul_le_mul_of_nonneg_right (hV_bound i k hk.1) (abs_nonneg _)
                _ = |V_inv k j| := one_mul _
      -- The filter {i < k ≤ j} = {i+1 ≤ k ≤ j}
      have hfilt_eq2 : Finset.univ.filter (fun k : Fin n =>
            i.val < k.val ∧ k.val ≤ j.val) =
          Finset.univ.filter (fun k : Fin n =>
            i.val + 1 ≤ k.val ∧ k.val ≤ j.val) := by
        ext k; simp [Finset.mem_filter]; omega
      rw [hfilt_eq2] at hvinv_bound
      -- Step 4: Apply IH to get S(i+1, j) ≤ 2^d'
      have hi1_lt : i.val + 1 < n := by omega
      have hS : ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            i.val + 1 ≤ k.val ∧ k.val ≤ j.val), |V_inv k j| ≤ 2 ^ d' := by
        exact ih ⟨i.val + 1, hi1_lt⟩ j (by simp; omega) (by simp; omega)
      -- Combine: |V_inv i j| + S(i+1,j) ≤ 2^d' + 2^d' = 2^{d'+1}
      have : |V_inv i j| + ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            i.val + 1 ≤ k.val ∧ k.val ≤ j.val), |V_inv k j|
          ≤ 2 ^ d' + 2 ^ d' := add_le_add (le_trans hvinv_bound hS) hS
      linarith [show (2 : ℝ) ^ d' + 2 ^ d' = 2 ^ (d' + 1) by ring]

theorem unitUpperTri_inv_entry_bound (n : ℕ) (V V_inv : Fin n → Fin n → ℝ)
    (hVT : ∀ i j : Fin n, j.val < i.val → V i j = 0)
    (hV_unit : ∀ i : Fin n, V i i = 1)
    (hV_bound : ∀ i j : Fin n, i.val < j.val → |V i j| ≤ 1)
    (hRInv : IsRightInverse n V V_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → V_inv i j = 0)
    (hInv_diag : ∀ i : Fin n, V_inv i i = 1) :
    ∀ i j : Fin n, i.val < j.val →
      |V_inv i j| ≤ 2 ^ (j.val - i.val - 1) := by
  intro i j hij
  -- |V_inv i j| ≤ S(i+1, j) ≤ 2^{j-i-1} from inv_sum_bound
  have hi1_lt : i.val + 1 < n := by omega
  -- From the recurrence, |V_inv i j| ≤ ∑_{k: i<k≤j} |V_inv k j|
  have hrec := inv_recurrence n V V_inv hVT
    (by intro i; rw [hV_unit]; exact one_ne_zero) hRInv hInv_ut i j hij
  rw [hV_unit, one_mul] at hrec
  have hvinv_eq : V_inv i j = -(∑ k ∈ Finset.univ.filter (fun k : Fin n =>
      i.val < k.val ∧ k.val ≤ j.val), V i k * V_inv k j) := by linarith
  have hvinv_bound : |V_inv i j| ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
        i.val + 1 ≤ k.val ∧ k.val ≤ j.val), |V_inv k j| := by
    rw [hvinv_eq, abs_neg]
    calc |∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          i.val < k.val ∧ k.val ≤ j.val), V i k * V_inv k j|
        ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          i.val < k.val ∧ k.val ≤ j.val), |V i k| * |V_inv k j| := by
          calc _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
                i.val < k.val ∧ k.val ≤ j.val), |V i k * V_inv k j| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          i.val < k.val ∧ k.val ≤ j.val), |V_inv k j| := by
          apply Finset.sum_le_sum; intro k hk
          simp [Finset.mem_filter] at hk
          calc |V i k| * |V_inv k j|
              ≤ 1 * |V_inv k j| :=
                mul_le_mul_of_nonneg_right (hV_bound i k hk.1) (abs_nonneg _)
            _ = |V_inv k j| := one_mul _
      _ = ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          i.val + 1 ≤ k.val ∧ k.val ≤ j.val), |V_inv k j| := by
          congr 1
  -- Apply inv_sum_bound with i' = ⟨i+1, _⟩
  have hS := inv_sum_bound n V V_inv hVT hV_unit hV_bound hRInv hInv_ut hInv_diag
    (j.val - (i.val + 1)) ⟨i.val + 1, hi1_lt⟩ j (by simp) (by simp; omega)
  have hconv : ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
        i.val + 1 ≤ k.val ∧ k.val ≤ j.val), |V_inv k j| ≤
      2 ^ (j.val - i.val - 1) := by
    have : j.val - (i.val + 1) = j.val - i.val - 1 := by omega
    rw [this] at hS; exact hS
  linarith

-- ============================================================
-- Lemma 8.6: diagonal dominance bound on |U⁻¹||U|
-- ============================================================

/-- **Lemma 8.6** (Higham §8.2).

    If the upper triangular matrix U satisfies |U_ii| ≥ |U_ij| for all j > i,
    then W = |U⁻¹||U| satisfies w_ij ≤ 2^(j-i) for all j ≥ i.

    Proof: write V = D⁻¹U where D = diag(U_ii). Then V is unit upper triangular
    with |V_ij| ≤ 1, and |U⁻¹||U| = |V⁻¹||V|. Apply unitUpperTri_inv_entry_bound. -/
theorem lemma_8_6 (n : ℕ) (U U_inv : Fin n → Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    ∀ i j : Fin n, i.val ≤ j.val →
      ∑ k : Fin n, |U_inv i k| * |U k j| ≤ 2 ^ (j.val - i.val) := by
  sorry

-- ============================================================
-- Theorem 8.7: componentwise forward error under diagonal dominance
-- ============================================================

/-- **Theorem 8.7** (Higham §8.2).

    Under the conditions of Lemma 8.6, the computed solution x̂ to Ux = b
    obtained by back substitution satisfies:
      |x_i - x̂_i| ≤ 2^(n-i) · γ(n) · max_{j≥i} |x̂_j|    (0-based indexing)

    This bound shows that later components of x are always computed to high
    accuracy relative to the elements already computed. -/
theorem theorem_8_7 (fp : FPModel) (n : ℕ)
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
            ⟨i, by simp [Finset.mem_filter]⟩ (fun j => |x_hat j|) := by
  sorry

end LeanFpAnalysis.FP
