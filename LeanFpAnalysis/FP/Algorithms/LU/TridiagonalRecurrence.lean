-- Algorithms/LU/TridiagonalRecurrence.lean
--
-- Tridiagonal LU recurrence (Higham §9.5, eq 9.16, Algorithm 9.1).
--
-- For a tridiagonal matrix T with sub-diagonal a, diagonal d, super-diagonal c,
-- the LU factorization is computed via the simple recurrence:
--   û₁ = d₁
--   l̂ᵢ = fl(aᵢ / ûᵢ₋₁)         for i = 2,...,n
--   ûᵢ = fl(dᵢ - l̂ᵢ · cᵢ₋₁)    for i = 2,...,n
--
-- The resulting factors are:
--   L = unit lower bidiagonal with subdiag l̂
--   U = upper bidiagonal with diagonal û and superdiag c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination
import LeanFpAnalysis.FP.Algorithms.LU.Tridiagonal
import LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §9.5  Tridiagonal data structure
-- ============================================================

/-- **Tridiagonal data** representation.

    A tridiagonal matrix is fully determined by three vectors:
    - `a : Fin n → ℝ` — sub-diagonal (a₀ unused, a₁,...,aₙ₋₁)
    - `d : Fin n → ℝ` — main diagonal
    - `c : Fin n → ℝ` — super-diagonal (cₙ₋₁ unused, c₀,...,cₙ₋₂) -/
structure TridiagData (n : ℕ) where
  a : Fin n → ℝ
  d : Fin n → ℝ
  c : Fin n → ℝ

/-- Convert tridiagonal data to a full matrix. -/
noncomputable def tridiag_to_matrix {n : ℕ} (T : TridiagData n) :
    Fin n → Fin n → ℝ := fun i j =>
  if j.val = i.val then T.d i
  else if j.val + 1 = i.val then T.a i
  else if i.val + 1 = j.val then T.c i
  else 0

/-- The matrix from `tridiag_to_matrix` is tridiagonal. -/
lemma tridiag_to_matrix_isTridiagonal {n : ℕ} (T : TridiagData n) :
    IsTridiagonal n (tridiag_to_matrix T) := by
  intro i j hij
  unfold tridiag_to_matrix
  split_ifs with h1 h2 h3
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · rfl

-- ============================================================
-- §9.5  Tridiagonal LU recurrence (Algorithm 9.1)
-- ============================================================

/-- Auxiliary: compute the first `k` entries of û and l̂.

    Returns `(u_hat, l_hat)` defined on indices `< k`. -/
noncomputable def tridiag_lu_aux (fp : FPModel) {n : ℕ} (T : TridiagData n) :
    (k : ℕ) → k ≤ n → (Fin n → ℝ) × (Fin n → ℝ)
  | 0, _ => (fun _ => 0, fun _ => 0)
  | 1, h1 =>
    let u0 := T.d ⟨0, by omega⟩
    (Function.update (fun _ => 0) ⟨0, by omega⟩ u0,
     fun _ => 0)
  | k + 2, hk =>
    let (u_prev, l_prev) := tridiag_lu_aux fp T (k + 1) (by omega)
    let idx : Fin n := ⟨k + 1, by omega⟩
    let prev_idx : Fin n := ⟨k, by omega⟩
    let l_i := fp.fl_div (T.a idx) (u_prev prev_idx)
    let u_i := fp.fl_sub (T.d idx) (fp.fl_mul l_i (T.c prev_idx))
    (Function.update u_prev idx u_i,
     Function.update l_prev idx l_i)

/-- **Computed tridiag LU factors** (Algorithm 9.1).

    Returns `(l_hat, u_hat)` where:
    - L is unit lower bidiagonal: L_{ii} = 1, L_{i,i-1} = l_hat i
    - U is upper bidiagonal: U_{ii} = u_hat i, U_{i,i+1} = c_i -/
noncomputable def tridiag_lu (fp : FPModel) {n : ℕ} (T : TridiagData n) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  let (u_hat, l_hat) := tridiag_lu_aux fp T n (le_refl n)
  (l_hat, u_hat)

-- ============================================================
-- §9.5  Full matrix builders
-- ============================================================

/-- Build L from tridiag LU: L_{ii} = 1, L_{i,i-1} = l_hat i, else 0. -/
noncomputable def tridiag_L_matrix {n : ℕ} (l_hat : Fin n → ℝ) :
    Fin n → Fin n → ℝ := fun i j =>
  if j.val = i.val then 1
  else if j.val + 1 = i.val then l_hat i
  else 0

/-- Build U from tridiag LU: U_{ii} = u_hat i, U_{i,i+1} = c_i, else 0. -/
noncomputable def tridiag_U_matrix {n : ℕ} (u_hat : Fin n → ℝ)
    (c : Fin n → ℝ) : Fin n → Fin n → ℝ := fun i j =>
  if j.val = i.val then u_hat i
  else if i.val + 1 = j.val then c i
  else 0

/-- L from tridiag LU is unit lower triangular (diagonal = 1). -/
lemma tridiag_L_diag {n : ℕ} (l_hat : Fin n → ℝ) :
    ∀ i : Fin n, tridiag_L_matrix l_hat i i = 1 := by
  intro i; unfold tridiag_L_matrix; simp

/-- L from tridiag LU has zeros above diagonal. -/
lemma tridiag_L_upper_zero {n : ℕ} (l_hat : Fin n → ℝ) :
    ∀ i j : Fin n, i.val < j.val → tridiag_L_matrix l_hat i j = 0 := by
  intro i j hij; unfold tridiag_L_matrix
  split_ifs with h1 h2 <;> (first | omega | rfl)

/-- U from tridiag LU has zeros below diagonal. -/
lemma tridiag_U_lower_zero {n : ℕ} (u_hat : Fin n → ℝ) (c : Fin n → ℝ) :
    ∀ i j : Fin n, j.val < i.val → tridiag_U_matrix u_hat c i j = 0 := by
  intro i j hij; unfold tridiag_U_matrix
  split_ifs with h1 h2 <;> (first | omega | rfl)

-- ============================================================
-- §9.5  Bidiagonal LU structure predicate
-- ============================================================

/-- **Tridiag bidiagonal LU structure** predicate.

    For a tridiagonal matrix, the LU factors have bidiagonal form:
    - L is unit lower bidiagonal: L_{ii} = 1, L_{i,i-1} = l_i, rest 0
    - U is upper bidiagonal: U_{ii} = u_i, U_{i,i+1} = c_i, rest 0 -/
structure IsTridiagLU (n : ℕ) (L U : Fin n → Fin n → ℝ) : Prop where
  L_diag : ∀ i : Fin n, L i i = 1
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  L_lower_bidiag : ∀ i j : Fin n, j.val + 1 < i.val → L i j = 0
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  U_upper_bidiag : ∀ i j : Fin n, i.val + 1 < j.val → U i j = 0

/-- Multipliers bounded by 1 for bidiagonal L. -/
theorem tridiag_L_entries_bounded {n : ℕ}
    (L : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L (fun _ _ => 0))
    (hMult : ∀ i j : Fin n, j.val + 1 = i.val → |L i j| ≤ 1) :
    ∀ i j : Fin n, |L i j| ≤ 1 := by
  intro i j
  by_cases h_diag : j.val = i.val
  · rw [show j = i from Fin.ext (by omega)]; rw [hStruct.L_diag]; simp
  · by_cases h_sub : j.val + 1 = i.val
    · exact hMult i j h_sub
    · by_cases h_above : i.val < j.val
      · rw [hStruct.L_upper_zero i j h_above]; simp
      · have : j.val + 1 < i.val := by omega
        rw [hStruct.L_lower_bidiag i j this]; simp

-- ============================================================
-- §9.5  |L||U| ≤ 3|A| for tridiag bidiagonal (Theorem 9.12 core)
-- ============================================================

/-- **(|L||U|)_{ij}** has at most 3 nonzero terms for bidiagonal factors.

    For bidiagonal L and U from tridiag LU:
    - (|L||U|)_{ii} = |U_{ii}| + |L_{i,i-1}|·|U_{i-1,i}| ≤ 2 terms
    - (|L||U|)_{i,i+1} = |U_{i,i+1}| ≤ 1 term
    - (|L||U|)_{i,i-1} = |L_{i,i-1}|·|U_{i-1,i-1}| ≤ 1 term
    - (|L||U|)_{ij} = 0 for |i-j| > 1

    With |l_i| ≤ 1, each nonzero term ≤ corresponding |A_{ij}|,
    giving (|L||U|)_{ij} ≤ 3|A_{ij}| for diagonal entries. -/
theorem tridiag_bidiag_absLU_sparse {n : ℕ}
    (L U : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U) :
    ∀ i j : Fin n, (i.val + 1 < j.val ∨ j.val + 1 < i.val) →
      ∑ k : Fin n, |L i k| * |U k j| = 0 := by
  intro i j hij
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : k.val = i.val
  · -- k = i: L_{ii} = 1, need U_{ij} = 0
    have : |U k j| = 0 := by
      rw [abs_eq_zero]
      rcases hij with h | h
      · exact hStruct.U_upper_bidiag k j (by omega)
      · exact hStruct.U_lower_zero k j (by omega)
    rw [this, mul_zero]
  · by_cases hik1 : k.val + 1 = i.val
    · -- k = i-1: L_{i,i-1} may be nonzero, need U_{i-1,j} = 0
      have : |U k j| = 0 := by
        rw [abs_eq_zero]
        rcases hij with h | h
        · exact hStruct.U_upper_bidiag k j (by omega)
        · exact hStruct.U_lower_zero k j (by omega)
      rw [this, mul_zero]
    · -- k ≠ i, k ≠ i-1: L_{ik} = 0
      have : |L i k| = 0 := by
        rw [abs_eq_zero]
        by_cases h : i.val < k.val
        · exact hStruct.L_upper_zero i k h
        · exact hStruct.L_lower_bidiag i k (by omega)
      rw [this, zero_mul]

-- ============================================================
-- §9.5  Theorem 9.12: |L||U| ≤ 3|A| for tridiag diag-dominant
-- ============================================================

/-- **Off-diagonal growth for bidiagonal LU** (sub-diagonal case).

    For bidiagonal L,U with LU = A:
      (|L||U|)_{i+1,i} = |l_{i+1}| · |u_i| = |A_{i+1,i}| ≤ 3|A_{i+1,i}|

    The sub-diagonal of |L||U| exactly equals the sub-diagonal of |A|. -/
theorem tridiag_bidiag_growth_offdiag_sub {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j) :
    ∀ i j : Fin n, j.val + 1 = i.val →
      ∑ k : Fin n, |L i k| * |U k j| ≤ |A i j| := by
  intro i j hij
  -- Only k = j contributes (L_{ij} · U_{jj}), all others are zero
  have hLU_val := hLU_eq i j
  -- A_{ij} = ∑_k L_{ik} U_{kj}
  -- For bidiag: only k=j contributes to L_{ik}·U_{kj} (since L_{i,j} is the subdiag)
  -- and only k=j has U_{kj} nonzero (U is upper bidiag, so U_{kj}=0 for k>j)
  -- Also, for the abs sum, only k=j contributes since L_{ik}=0 for k≠i,i-1=j
  -- So ∑_k |L_{ik}|·|U_{kj}| = |L_{ij}|·|U_{jj}|
  -- And A_{ij} = L_{ij}·U_{jj}, so |A_{ij}| = |L_{ij}|·|U_{jj}| = ∑_k |L_{ik}|·|U_{kj}|
  calc ∑ k : Fin n, |L i k| * |U k j|
      ≤ |∑ k : Fin n, L i k * U k j| + (∑ k : Fin n, |L i k| * |U k j| -
          |∑ k : Fin n, L i k * U k j|) := by linarith
    _ ≤ |A i j| + (∑ k : Fin n, |L i k| * |U k j| -
          |∑ k : Fin n, L i k * U k j|) := by rw [hLU_val]
    _ ≤ |A i j| := by
        suffices ∑ k : Fin n, |L i k| * |U k j| ≤
            |∑ k : Fin n, L i k * U k j| by linarith
        -- For bidiagonal: only k = j has both L_{ik} ≠ 0 and U_{kj} ≠ 0
        -- So the sum has exactly one nonzero term: L_{ij}·U_{jj}
        -- Hence |sum| = |single term| = sum of |single term|
        have hsum_eq : ∑ k : Fin n, L i k * U k j = L i j * U j j := by
          apply Finset.sum_eq_single j
          · intro k _ hkj
            by_cases hki : k.val = i.val
            · -- k = i: U_{ij} = 0 since j < i
              have : U k j = 0 := hStruct.U_lower_zero k j (by omega)
              rw [this, mul_zero]
            · by_cases hki1 : k.val + 1 = i.val
              · -- k = i-1 = j: contradiction with hkj
                exfalso; exact hkj (Fin.ext (by omega))
              · -- k ≠ i, k ≠ i-1: L_{ik} = 0
                by_cases h : i.val < k.val
                · rw [hStruct.L_upper_zero i k h, zero_mul]
                · rw [hStruct.L_lower_bidiag i k (by omega), zero_mul]
          · intro h; exact absurd (Finset.mem_univ j) h
        have habs_eq : ∑ k : Fin n, |L i k| * |U k j| = |L i j| * |U j j| := by
          apply Finset.sum_eq_single j
          · intro k _ hkj
            by_cases hki : k.val = i.val
            · have : U k j = 0 := hStruct.U_lower_zero k j (by omega)
              rw [this, abs_zero, mul_zero]
            · by_cases hki1 : k.val + 1 = i.val
              · exfalso; exact hkj (Fin.ext (by omega))
              · by_cases h : i.val < k.val
                · rw [hStruct.L_upper_zero i k h, abs_zero, zero_mul]
                · rw [hStruct.L_lower_bidiag i k (by omega), abs_zero, zero_mul]
          · intro h; exact absurd (Finset.mem_univ j) h
        rw [habs_eq, hsum_eq, abs_mul]

/-- **Off-diagonal growth for bidiagonal LU** (super-diagonal case).

    For bidiagonal L,U:
      (|L||U|)_{i,i+1} = |U_{i,i+1}| = |A_{i,i+1}| ≤ 3|A_{i,i+1}| -/
theorem tridiag_bidiag_growth_offdiag_super {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j) :
    ∀ i j : Fin n, i.val + 1 = j.val →
      ∑ k : Fin n, |L i k| * |U k j| ≤ |A i j| := by
  intro i j hij
  -- Only k = i contributes: L_{ii}·U_{ij} = 1·U_{ij}
  have hsum_eq : ∑ k : Fin n, L i k * U k j = L i i * U i j := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      by_cases h : i.val < k.val
      · rw [hStruct.L_upper_zero i k h, zero_mul]
      · -- k < i: U_{kj} = 0 since k < i and j = i+1, so k+1 < j
        have : U k j = 0 := by
          by_cases hkj : k.val = j.val
          · exfalso; omega
          · by_cases hkj2 : k.val + 1 = j.val
            · -- k = i: contradiction
              exfalso; exact hki (Fin.ext (by omega))
            · exact hStruct.U_upper_bidiag k j (by omega)
        rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have habs_eq : ∑ k : Fin n, |L i k| * |U k j| = |L i i| * |U i j| := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      by_cases h : i.val < k.val
      · rw [hStruct.L_upper_zero i k h, abs_zero, zero_mul]
      · have : U k j = 0 := by
          by_cases hkj : k.val = j.val
          · exfalso; omega
          · by_cases hkj2 : k.val + 1 = j.val
            · exfalso; exact hki (Fin.ext (by omega))
            · exact hStruct.U_upper_bidiag k j (by omega)
        rw [this, abs_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [habs_eq, hStruct.L_diag, abs_one, one_mul]
  rw [← hLU_eq, hsum_eq, hStruct.L_diag, one_mul]

/-- **Theorem 9.12 off-diagonal bound** (Higham §9.5).

    Combining sub- and super-diagonal cases: for all off-diagonal entries
    within the tridiagonal band, (|L||U|)_{ij} ≤ |A_{ij}| ≤ 3|A_{ij}|.
    Outside the band, both sides are 0. -/
theorem tridiag_bidiag_growth_offdiag {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j) :
    ∀ i j : Fin n, i ≠ j →
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| := by
  intro i j hij
  by_cases h_far : i.val + 1 < j.val ∨ j.val + 1 < i.val
  · rw [tridiag_bidiag_absLU_sparse L U hStruct i j h_far]
    exact mul_nonneg (by linarith) (abs_nonneg _)
  · push_neg at h_far
    by_cases h_sub : j.val + 1 = i.val
    · have h1 := tridiag_bidiag_growth_offdiag_sub L U A hStruct hLU_eq i j h_sub
      linarith [abs_nonneg (A i j)]
    · have h_super : i.val + 1 = j.val := by
        have : i.val ≠ j.val := fun h => hij (Fin.ext h)
        omega
      have h1 := tridiag_bidiag_growth_offdiag_super L U A hStruct hLU_eq i j h_super
      linarith [abs_nonneg (A i j)]

-- ============================================================
-- §9.5  Helper: super-diagonal of U equals super-diagonal of A
-- ============================================================

/-- For bidiagonal LU = A, the super-diagonal of U equals the super-diagonal of A:
    U_{i,i+1} = A_{i,i+1}. -/
private theorem tridiag_LU_super_eq {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j) :
    ∀ i j : Fin n, i.val + 1 = j.val → U i j = A i j := by
  intro i j hij
  have hsum : ∑ k : Fin n, L i k * U k j = L i i * U i j := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      by_cases h : i.val < k.val
      · rw [hStruct.L_upper_zero i k h, zero_mul]
      · have hk_lt_i : k.val < i.val := by
          have : k.val ≤ i.val := Nat.le_of_not_lt h
          rcases Nat.eq_or_lt_of_le this with h2 | h2
          · exfalso; exact hki (Fin.ext h2)
          · exact h2
        exact mul_eq_zero_of_right _ (hStruct.U_upper_bidiag k j (by omega))
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [← hLU_eq, hsum, hStruct.L_diag, one_mul]

-- ============================================================
-- §9.5  Helper: diagonal relation A_{ii} = U_{ii} + l_i · U_{i-1,i}
-- ============================================================

/-- For bidiagonal LU = A with i > 0:
    A i i = U i i + L i (i-1) * U (i-1) i.
    For i = 0: A 0 0 = U 0 0. -/
private theorem tridiag_LU_diag_rel {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j) :
    ∀ i : Fin n,
      A i i = U i i + (if h : 0 < i.val then
        L i ⟨i.val - 1, by omega⟩ * U ⟨i.val - 1, by omega⟩ i
      else 0) := by
  intro i
  have hsum := hLU_eq i i
  have hsum2 : ∑ k : Fin n, L i k * U k i =
      L i i * U i i + ∑ k ∈ Finset.univ.erase i, L i k * U k i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hrest : ∑ k ∈ Finset.univ.erase i, L i k * U k i =
      if h : 0 < i.val then
        L i ⟨i.val - 1, by omega⟩ * U ⟨i.val - 1, by omega⟩ i
      else 0 := by
    split
    · rename_i hi
      have hn : i.val - 1 < n := by omega
      let im1 : Fin n := ⟨i.val - 1, hn⟩
      have him1_ne : im1 ≠ i := by
        intro h; have := congr_arg Fin.val h; simp [im1] at this; omega
      have him1_mem : im1 ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨him1_ne, Finset.mem_univ _⟩
      have : ∑ k ∈ Finset.univ.erase i, L i k * U k i = L i im1 * U im1 i := by
        apply Finset.sum_eq_single_of_mem im1 him1_mem
        intro k hk hk_ne
        have hk_ne_i : k.val ≠ i.val := by
          intro h; exact ((Finset.mem_erase.mp hk).1) (Fin.ext h)
        by_cases h2 : i.val < k.val
        · rw [hStruct.L_upper_zero i k h2, zero_mul]
        · have hk_lt : k.val < i.val := by omega
          have hk_ne_im1 : k.val ≠ i.val - 1 := by
            intro h3; exact hk_ne (Fin.ext (by simp [im1]; omega))
          rw [hStruct.L_lower_bidiag i k (by omega), zero_mul]
      rw [this]
    · rename_i hi
      push_neg at hi
      have hi0 : i.val = 0 := Nat.eq_zero_of_le_zero hi
      apply Finset.sum_eq_zero
      intro k hk
      have hk_ne_i : k.val ≠ i.val := by
        intro h; exact ((Finset.mem_erase.mp hk).1) (Fin.ext h)
      by_cases h2 : i.val < k.val
      · rw [hStruct.L_upper_zero i k h2, zero_mul]
      · exfalso; omega
  rw [← hsum, hsum2, hrest, hStruct.L_diag, one_mul]

-- ============================================================
-- §9.5  Helper: column diag dominance gives off-diag ≤ diag
-- ============================================================

/-- From column diagonal dominance: each individual off-diagonal entry
    satisfies |A k i| ≤ |A i i| for k ≠ i. -/
private theorem col_diag_dom_offdiag_le {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hColDom : IsDiagDominant n A) :
    ∀ i k : Fin n, k ≠ i → |A k i| ≤ |A i i| := by
  intro i k hki
  have hdom := hColDom i
  -- |A k i| is one term of ∑_{m≠i} |A m i| which is ≤ |A i i|
  have hterm : |A k i| ≤ ∑ m : Fin n, if m = i then 0 else |A m i| := by
    have hk_val : (fun m : Fin n => if m = i then (0 : ℝ) else |A m i|) k = |A k i| := by
      simp [hki]
    rw [← hk_val]
    apply Finset.single_le_sum (f := fun m => if m = i then 0 else |A m i|)
    · intro m _; split_ifs <;> simp [abs_nonneg]
    · exact Finset.mem_univ k
  linarith

-- ============================================================
-- §9.5  Helper: ∑_k |L i k| * |U k i| ≤ ∑_k |U k i| when |L| ≤ 1
-- ============================================================

/-- When |L i k| ≤ 1 for all k, the weighted column sum is bounded by
    the unweighted column sum. -/
private theorem abs_LU_le_abs_U_col {n : ℕ}
    (L U : Fin n → Fin n → ℝ)
    (hL_bound : ∀ i j : Fin n, |L i j| ≤ 1)
    (i : Fin n) :
    ∑ k : Fin n, |L i k| * |U k i| ≤ ∑ k : Fin n, |U k i| := by
  apply Finset.sum_le_sum
  intro k _
  calc |L i k| * |U k i| ≤ 1 * |U k i| :=
        mul_le_mul_of_nonneg_right (hL_bound i k) (abs_nonneg _)
    _ = |U k i| := one_mul _

-- ============================================================
-- §9.5  Helper: column sum of |U| for bidiagonal U
-- ============================================================

/-- For upper bidiagonal U, the column sum ∑_k |U k i| has at most 2 terms:
    |U i i| and |U (i-1) i| (if i > 0). -/
private theorem bidiag_U_col_sum {n : ℕ}
    (U : Fin n → Fin n → ℝ)
    (hU_lower : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_upper : ∀ i j : Fin n, i.val + 1 < j.val → U i j = 0)
    (i : Fin n) :
    ∑ k : Fin n, |U k i| =
      |U i i| + (if h : 0 < i.val then |U ⟨i.val - 1, by omega⟩ i| else 0) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  split
  · rename_i hi
    have hn : i.val - 1 < n := by omega
    let im1 : Fin n := ⟨i.val - 1, hn⟩
    have him1_ne : im1 ≠ i := by
      intro h; have := congr_arg Fin.val h; simp [im1] at this; omega
    have him1_mem : im1 ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨him1_ne, Finset.mem_univ _⟩
    have : ∑ k ∈ Finset.univ.erase i, |U k i| = |U im1 i| := by
      apply Finset.sum_eq_single_of_mem im1 him1_mem
      intro k hk hk_ne
      have hk_ne_i : k.val ≠ i.val := by
        intro h; exact ((Finset.mem_erase.mp hk).1) (Fin.ext h)
      rw [abs_eq_zero]
      by_cases h2 : i.val < k.val
      · exact hU_lower k i h2
      · have hk_lt : k.val < i.val := by omega
        have hk_ne_im1 : k.val ≠ i.val - 1 := by
          intro h3; exact hk_ne (Fin.ext (by simp [im1]; omega))
        exact hU_upper k i (by omega)
    rw [this]
  · rename_i hi
    push_neg at hi
    have hi0 : i.val = 0 := Nat.eq_zero_of_le_zero hi
    apply Finset.sum_eq_zero
    intro k hk
    have hk_ne_i : k.val ≠ i.val := by
      intro h; exact ((Finset.mem_erase.mp hk).1) (Fin.ext h)
    rw [abs_eq_zero]
    by_cases h2 : i.val < k.val
    · exact hU_lower k i h2
    · exfalso; omega

-- ============================================================
-- §9.5  Theorem 9.12: full |L||U| ≤ 3|A| bound
-- ============================================================

set_option maxHeartbeats 400000 in
/-- **Theorem 9.12** (Higham §9.5): For tridiagonal diagonally-dominant A
    with bidiagonal LU factorization LU = A and |L_{ij}| ≤ 1,
    the growth factor satisfies rho ≤ 3, i.e.,
      (|L||U|)_{ij} = sum_k |L_{ik}| |U_{kj}| ≤ 3 |A_{ij}| for all i,j.

    Off-diagonal (i != j): from `tridiag_bidiag_growth_offdiag`.
    Diagonal (i = j): Use |L| ≤ 1 to bound by sum_k |U_{ki}|,
    decompose via bidiagonal sparsity into |U_{ii}| + |U_{i-1,i}|,
    then use LU = A relations and column diagonal dominance:
      |U_{i-1,i}| = |A_{i-1,i}| ≤ |A_{ii}| and
      |U_{ii}| ≤ |A_{ii}| + |A_{i-1,i}| ≤ 2|A_{ii}|,
    giving the bound 3|A_{ii}|. -/
theorem tridiag_growth_bound_3 {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hL_bound : ∀ i j : Fin n, |L i j| ≤ 1)
    (_hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| := by
  intro i j
  by_cases hij : i = j
  · -- Diagonal case: i = j
    subst hij
    -- Step 1: ∑_k |L i k| * |U k i| ≤ ∑_k |U k i|
    have h_le_col := abs_LU_le_abs_U_col L U hL_bound i
    -- Step 2: Decompose ∑_k |U k i|
    have h_col := bidiag_U_col_sum U hStruct.U_lower_zero hStruct.U_upper_bidiag i
    -- Step 3: Get the diagonal relation
    have h_diag := tridiag_LU_diag_rel L U A hStruct hLU_eq i
    -- Now case split on whether i > 0
    by_cases hi0 : 0 < i.val
    · -- i > 0: both terms present
      have hn : i.val - 1 < n := by omega
      let im1 : Fin n := ⟨i.val - 1, hn⟩
      -- U (i-1) i = A (i-1) i (super-diagonal relation)
      have h_super : U im1 i = A im1 i :=
        tridiag_LU_super_eq L U A hStruct hLU_eq im1 i (by simp [im1]; omega)
      -- Column dominance: |A (i-1) i| ≤ |A i i|
      have h_dom : |A im1 i| ≤ |A i i| := by
        apply col_diag_dom_offdiag_le A hColDom i im1
        intro h; have := congr_arg Fin.val h; simp [im1] at this; omega
      -- Diagonal relation with the specific im1 index
      have h_diag_simp : A i i = U i i +
          L i ⟨i.val - 1, by omega⟩ * U ⟨i.val - 1, by omega⟩ i := by
        have := h_diag; simp [hi0] at this; exact this
      -- Convert the ⟨i.val - 1, by omega⟩ to im1
      have h_Aii : A i i = U i i + L i im1 * U im1 i := by
        convert h_diag_simp using 3
      -- |U i i| ≤ |A i i| + |A (i-1) i|
      have h_Uii_eq : U i i = A i i - L i im1 * U im1 i := by linarith
      have h_Uii_bound : |U i i| ≤ |A i i| + |A im1 i| := by
        rw [h_Uii_eq]
        -- Need |a - b| ≤ |a| + |b| where a = A i i, b = L i im1 * U im1 i
        -- Use: |a - b| ≤ |a| + |b| via abs_le
        have hLU_abs : |L i im1 * U im1 i| ≤ |A im1 i| := by
          rw [abs_mul]
          calc |L i im1| * |U im1 i| ≤ 1 * |U im1 i| :=
                mul_le_mul_of_nonneg_right (hL_bound i im1) (abs_nonneg _)
            _ = |U im1 i| := one_mul _
            _ = |A im1 i| := by rw [h_super]
        rw [abs_le]; constructor
        · -- Need -(|A i i| + |A im1 i|) ≤ A i i - L*U
          -- From: -|A i i| ≤ A i i and -(L*U) ≥ -|L*U| ≥ -|A im1 i|
          have := neg_abs_le (A i i)
          have := le_abs_self (L i im1 * U im1 i)
          linarith
        · -- Need A i i - L*U ≤ |A i i| + |A im1 i|
          -- From: A i i ≤ |A i i| and -(L*U) ≤ |L*U| ≤ |A im1 i|
          have := le_abs_self (A i i)
          have := neg_abs_le (L i im1 * U im1 i)
          linarith
      -- Column sum decomposition
      have h_col_simp : ∑ k : Fin n, |U k i| = |U i i| + |U im1 i| := by
        rw [h_col]; simp only [hi0, dite_true]; rfl
      calc ∑ k : Fin n, |L i k| * |U k i|
          ≤ ∑ k : Fin n, |U k i| := h_le_col
        _ = |U i i| + |U im1 i| := h_col_simp
        _ = |U i i| + |A im1 i| := by rw [h_super]
        _ ≤ (|A i i| + |A im1 i|) + |A im1 i| := by linarith
        _ = |A i i| + 2 * |A im1 i| := by ring
        _ ≤ |A i i| + 2 * |A i i| := by linarith
        _ = 3 * |A i i| := by ring
    · -- i = 0: only one term
      push_neg at hi0
      have hi_zero : i.val = 0 := Nat.eq_zero_of_le_zero hi0
      have h_col_simp : ∑ k : Fin n, |U k i| = |U i i| := by
        rw [h_col]; simp [show ¬(0 < i.val) by omega]
      -- A i i = U i i
      have h_Aii : A i i = U i i := by
        have := h_diag; simp [show ¬(0 < i.val) by omega] at this; linarith
      calc ∑ k : Fin n, |L i k| * |U k i|
          ≤ ∑ k : Fin n, |U k i| := h_le_col
        _ = |U i i| := h_col_simp
        _ = |A i i| := by rw [h_Aii]
        _ ≤ 3 * |A i i| := by linarith [abs_nonneg (A i i)]
  · -- Off-diagonal: use existing theorem
    exact tridiag_bidiag_growth_offdiag L U A hStruct hLU_eq i j hij

end LeanFpAnalysis.FP
