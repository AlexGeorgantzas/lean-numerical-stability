-- Algorithms/LU/TridiagonalCondCh15Closure.lean
--
-- Honest closures of the Chapter-15 tridiagonal condition-number theorems,
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed., §15.6
-- (pp. 299-300).
--
-- The wrappers in `TridiagonalCondCh15` (`H15_Theorem15_7`, `H15_Theorem15_8`)
-- discharge their conclusions from hypotheses that are *target-equivalent to the
-- crux* rather than from Higham's printed hypotheses:
--   * `H15_Theorem15_7` assumes `hSignCoherent` (all inverse-factor products
--     `U⁻¹_{ik} L⁻¹_{kj}` are nonnegative), which is essentially the conclusion.
--   * `H15_Theorem15_8` assumes `hRowSumBound`
--     (`∑ₗ∑ₖ |U⁻¹_{ik}||U_{kl}| ≤ 2n−1`), the structural crux.
--
-- This IMPORT-ONLY module re-exposes the two theorems from the PRINTED
-- hypotheses, DERIVING the crux:
--
--   * `H15_Theorem15_8_of_rowDiagDominant` — FULL closure of Theorem 15.8 from
--     row diagonal dominance of `A` (with `A = LU` bidiagonal, nonzero pivots,
--     and `U⁻¹` given by the explicit bidiagonal-inverse product formula).
--     Row dominance of `A` propagates through the LU recurrence to give
--     `|U_{i,i+1}| ≤ |U_{ii}|` (i.e. `IsDiagDominantUpper U`), from which the
--     `(2n−1)` row-sum bound is derived via `unit_bidiag_row_sum_bound`.
--
-- The private helper lemmas from `TridiagonalRecurrence` that establish the
-- row-dominance propagation (`tridiag_LU_super_eq`, `tridiag_LU_sub_eq`,
-- `tridiag_LU_diag_rel`, `row_diag_dom_offdiag_le`, `row_diag_dom_two_offdiag_le`,
-- `tridiag_rowDom_U_super_le_diag`) are `private`, so their proofs are reproduced
-- here (prefixed `c15_`) to make the derivation self-contained.

import LeanFpAnalysis.FP.Algorithms.LU.TridiagonalCondCh15

namespace LeanFpAnalysis.FP.Ch15Closure

open scoped BigOperators
open LeanFpAnalysis.FP

-- ============================================================
-- Row-dominance propagation helpers (reproduced from the
-- `private` lemmas in `TridiagonalRecurrence`)
-- ============================================================

/-- For bidiagonal `LU = A`, the super-diagonal of `U` equals that of `A`. -/
private theorem c15_LU_super_eq {n : ℕ}
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

/-- For bidiagonal `LU = A`, the sub-diagonal relation `L_{i,i-1} U_{i-1,i-1}`. -/
private theorem c15_LU_sub_eq {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j) :
    ∀ i j : Fin n, j.val + 1 = i.val → L i j * U j j = A i j := by
  intro i j hij
  have hsum : ∑ k : Fin n, L i k * U k j = L i j * U j j := by
    apply Finset.sum_eq_single j
    · intro k _ hkj
      by_cases hki : k.val = i.val
      · rw [show U k j = 0 from hStruct.U_lower_zero k j (by omega), mul_zero]
      · by_cases hsub : k.val + 1 = i.val
        · exfalso
          exact hkj (Fin.ext (by omega))
        · by_cases habove : i.val < k.val
          · rw [hStruct.L_upper_zero i k habove, zero_mul]
          · rw [hStruct.L_lower_bidiag i k (by omega), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [← hLU_eq, hsum]

/-- Diagonal relation `A_{ii} = U_{ii} + L_{i,i-1} U_{i-1,i}` for bidiagonal LU. -/
private theorem c15_LU_diag_rel {n : ℕ}
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

/-- Row diagonal dominance: each off-diagonal entry is bounded by the diagonal. -/
private theorem c15_row_offdiag_le {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hRowDom : IsRowDiagDominant n A) :
    ∀ i j : Fin n, j ≠ i → |A i j| ≤ |A i i| := by
  intro i j hji
  have hdom := hRowDom i
  have hterm : |A i j| ≤ ∑ m : Fin n, if m = i then 0 else |A i m| := by
    have hj_val : (fun m : Fin n => if m = i then (0 : ℝ) else |A i m|) j =
        |A i j| := by
      simp [hji]
    rw [← hj_val]
    apply Finset.single_le_sum (f := fun m => if m = i then 0 else |A i m|)
    · intro m _
      split_ifs <;> simp [abs_nonneg]
    · exact Finset.mem_univ j
  exact le_trans hterm (by simpa [eq_comm] using hdom)

/-- Row diagonal dominance: two distinct off-diagonal entries sum ≤ diagonal. -/
private theorem c15_row_two_offdiag_le {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hRowDom : IsRowDiagDominant n A)
    {i j k : Fin n} (hji : j ≠ i) (hki : k ≠ i) (hjk : j ≠ k) :
    |A i j| + |A i k| ≤ |A i i| := by
  let f : Fin n → ℝ := fun m => if m = i then 0 else |A i m|
  have hpair_sum :
      ∑ m ∈ ({j, k} : Finset (Fin n)), f m = |A i j| + |A i k| := by
    simp [f, hji, hki, hjk]
  have hpair_le :
      ∑ m ∈ ({j, k} : Finset (Fin n)), f m ≤ ∑ m : Fin n, f m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (by intro x _; exact Finset.mem_univ x)
    intro x _ _hx_pair
    unfold f
    split_ifs <;> simp [abs_nonneg]
  rw [← hpair_sum]
  exact le_trans hpair_le (by simpa [f, eq_comm] using hRowDom i)

/-- **Row-dominance propagation** (Higham §15.6 proof of Theorem 15.8; also
    §9.5 Theorem 9.13).  For a row-diagonally-dominant tridiagonal `A = LU`
    with bidiagonal factors, the super-diagonal of `U` is bounded by the pivot:
    `|U_{i,i+1}| ≤ |U_{ii}|`.  This is the derived crux that makes the
    normalized bidiagonal factor `V = diag(U)⁻¹ U` satisfy `|V| ≤ 1`. -/
private theorem c15_tridiag_rowDom_U_super_le_diag {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hRowDom : IsRowDiagDominant n A) :
    ∀ i j : Fin n, i.val + 1 = j.val → |U i j| ≤ |U i i| := by
  classical
  have hbyVal :
      ∀ t : ℕ, ∀ ht : t < n, ∀ j : Fin n, t + 1 = j.val →
        |U ⟨t, ht⟩ j| ≤ |U ⟨t, ht⟩ ⟨t, ht⟩| := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro ht j hij
        let i : Fin n := ⟨t, ht⟩
        have hsuper : U i j = A i j :=
          c15_LU_super_eq L U A hStruct hLU_eq i j (by simpa [i] using hij)
        by_cases ht0 : t = 0
        · subst ht0
          have hdiag := c15_LU_diag_rel L U A hStruct hLU_eq i
          have hAii : A i i = U i i := by
            have hnot : ¬ 0 < i.val := by simp [i]
            simpa [hnot] using hdiag
          have hji : j ≠ i := by
            intro h
            have hval := congr_arg Fin.val h
            simp [i] at hval
            omega
          calc |U i j|
              = |A i j| := by rw [hsuper]
            _ ≤ |A i i| := c15_row_offdiag_le A hRowDom i j hji
            _ = |U i i| := by rw [hAii]
        · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
          have him1_lt : t - 1 < n := by omega
          let im1 : Fin n := ⟨t - 1, him1_lt⟩
          have him1_succ : im1.val + 1 = i.val := by
            simp [im1, i]
            omega
          have hprev : |U im1 i| ≤ |U im1 im1| := by
            exact ih (t - 1) (by omega) him1_lt i (by simpa [im1, i] using him1_succ)
          have hsub : L i im1 * U im1 im1 = A i im1 :=
            c15_LU_sub_eq L U A hStruct hLU_eq i im1
              (by simpa [im1, i] using him1_succ)
          have hq_abs_le : |L i im1 * U im1 i| ≤ |A i im1| := by
            calc |L i im1 * U im1 i|
                = |L i im1| * |U im1 i| := abs_mul _ _
              _ ≤ |L i im1| * |U im1 im1| :=
                  mul_le_mul_of_nonneg_left hprev (abs_nonneg _)
              _ = |L i im1 * U im1 im1| := (abs_mul _ _).symm
              _ = |A i im1| := by rw [hsub]
          have hdiag := c15_LU_diag_rel L U A hStruct hLU_eq i
          have hdiag_simp :
              A i i = U i i + L i im1 * U im1 i := by
            have htmp : A i i =
                U i i + L i ⟨i.val - 1, by omega⟩ *
                  U ⟨i.val - 1, by omega⟩ i := by
              have : 0 < i.val := by simpa [i] using htpos
              simpa [this] using hdiag
            simpa [im1, i] using htmp
          have him1_ne_i : im1 ≠ i := by
            intro h
            have := congr_arg Fin.val h
            simp [im1, i] at this
            omega
          have hj_ne_i : j ≠ i := by
            intro h
            have hval := congr_arg Fin.val h
            simp [i] at hval
            omega
          have him1_ne_j : im1 ≠ j := by
            intro h
            have hval := congr_arg Fin.val h
            simp [im1] at hval
            omega
          have hpair :
              |A i im1| + |A i j| ≤ |A i i| :=
            c15_row_two_offdiag_le A hRowDom him1_ne_i hj_ne_i him1_ne_j
          have hq_plus :
              |L i im1 * U im1 i| + |A i j| ≤ |A i i| := by
            linarith
          have htri : |A i i| ≤ |U i i| + |L i im1 * U im1 i| := by
            rw [hdiag_simp]
            exact abs_add_le (U i i) (L i im1 * U im1 i)
          calc |U i j|
              = |A i j| := by rw [hsuper]
            _ ≤ |U i i| := by linarith
  intro i j hij
  exact hbyVal i.val i.isLt j hij

/-- The bidiagonal `U` factor of a row-diagonally-dominant tridiagonal
    `A = LU` is diagonally dominant in the upper-triangular sense
    (`IsDiagDominantUpper`).  All the content is `c15_tridiag_rowDom_U_super_le_diag`
    plus the bidiagonal sparsity of `U`. -/
private theorem c15_bidiag_U_isDiagDominantUpper {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hRowDom : IsRowDiagDominant n A)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0) :
    IsDiagDominantUpper n U := by
  refine ⟨hStruct.U_lower_zero, hU_diag, ?_⟩
  intro i j hij
  by_cases hsuper : i.val + 1 = j.val
  · exact c15_tridiag_rowDom_U_super_le_diag L U A hStruct hLU_eq hRowDom i j hsuper
  · rw [hStruct.U_upper_bidiag i j (by omega), abs_zero]
    exact abs_nonneg _

-- ============================================================
-- Bidiagonal-inverse magnitude bound and the (2n−1) row-sum bound
-- ============================================================

/-- For an upper-bidiagonal `U` with `IsDiagDominantUpper`, every explicit
    inverse entry is bounded: `|U⁻¹_{ik}| ≤ 1/|U_{kk}|` for `i ≤ k`.
    The product `∏_{i≤p<k} |e_p|/|u_p|` of superdiagonal-to-pivot ratios is
    at most `1` because each ratio is `≤ 1` (diagonal dominance). -/
private theorem c15_upperBidiagInv_abs_le {n : ℕ} (U : Fin n → Fin n → ℝ)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hDD : IsDiagDominantUpper n U) :
    ∀ i k : Fin n, i.val ≤ k.val →
      |upperBidiagInvEntry (fun m => U m m)
          (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0) i k|
        ≤ 1 / |U k k| := by
  intro i k hik
  unfold upperBidiagInvEntry
  rw [if_neg (by omega : ¬ k.val < i.val), abs_mul, Finset.abs_prod]
  have hprod_le :
      (∏ p ∈ Finset.univ.filter (fun p : Fin n => i.val ≤ p.val ∧ p.val < k.val),
        |(-(if h : p.val + 1 < n then U p ⟨p.val + 1, h⟩ else 0)) / U p p|) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p _; exact abs_nonneg _
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hp1 : p.val + 1 < n := by omega
      rw [dif_pos hp1, abs_div, abs_neg, div_le_one (abs_pos.mpr (hU_diag p))]
      exact hDD.2.2 p ⟨p.val + 1, hp1⟩ (by show p.val < p.val + 1; omega)
  calc (∏ p ∈ Finset.univ.filter (fun p : Fin n => i.val ≤ p.val ∧ p.val < k.val),
          |(-(if h : p.val + 1 < n then U p ⟨p.val + 1, h⟩ else 0)) / U p p|)
        * |1 / U k k|
      ≤ 1 * |1 / U k k| := mul_le_mul_of_nonneg_right hprod_le (abs_nonneg _)
    _ = 1 / |U k k| := by rw [one_mul, abs_div, abs_one]

/-- **Derived crux for Theorem 15.8.**  For a bidiagonal `U` that is diagonally
    dominant (`IsDiagDominantUpper`), with `U⁻¹` given by the explicit
    bidiagonal-inverse product formula, the row sums of `|U⁻¹||U|` are bounded
    by `2n − 1`.  The proof normalizes `V = diag(U)⁻¹ U` and
    `V_inv = U⁻¹ diag(U)` (so `|V_inv||V| = |U⁻¹||U|` entrywise) and feeds the
    unit-bidiagonal bound `unit_bidiag_row_sum_bound`. -/
private theorem c15_bidiag_rowSum_bound {n : ℕ} (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hU_bidiag : ∀ i j : Fin n, i.val + 1 < j.val → U i j = 0)
    (hDD : IsDiagDominantUpper n U)
    (hU_inv_ut : ∀ i k : Fin n, k.val < i.val → U_inv i k = 0)
    (hU_inv_eq : ∀ i k : Fin n, i.val ≤ k.val →
      U_inv i k = upperBidiagInvEntry (fun m => U m m)
        (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0) i k) :
    ∀ i : Fin n,
      ∑ l : Fin n, ∑ k : Fin n, |U_inv i k| * |U k l| ≤ 2 * (n : ℝ) - 1 := by
  intro i
  -- Normalized unit bidiagonal factor and its (scaled) inverse.
  let V : Fin n → Fin n → ℝ := fun a b => U a b / U a a
  let V_inv : Fin n → Fin n → ℝ := fun a b => U_inv a b * U b b
  have hVT : ∀ a b : Fin n, b.val < a.val → V a b = 0 := by
    intro a b hab; simp only [V, hDD.1 a b hab, zero_div]
  have hV_unit : ∀ a : Fin n, V a a = 1 := by
    intro a; simp only [V]; exact div_self (hU_diag a)
  have hV_bidiag : ∀ a b : Fin n, a.val + 1 < b.val → V a b = 0 := by
    intro a b hab; simp only [V, hU_bidiag a b hab, zero_div]
  have hV_bound : ∀ a b : Fin n, |V a b| ≤ 1 := by
    intro a b
    by_cases hba : b.val < a.val
    · simp only [V, hDD.1 a b hba, zero_div, abs_zero]; norm_num
    · by_cases hab : a.val < b.val
      · simp only [V, abs_div]
        exact (div_le_one (abs_pos.mpr (hU_diag a))).mpr (hDD.2.2 a b hab)
      · have hba' : b = a := Fin.ext (by omega)
        subst hba'
        simp only [V]; rw [div_self (hU_diag b), abs_one]
  have hVinv_bound : ∀ a b : Fin n, |V_inv a b| ≤ 1 := by
    intro a b
    by_cases hba : b.val < a.val
    · simp only [V_inv, hU_inv_ut a b hba, zero_mul, abs_zero]; norm_num
    · push_neg at hba
      simp only [V_inv, abs_mul, hU_inv_eq a b hba]
      have hbnd := c15_upperBidiagInv_abs_le U hU_diag hDD a b hba
      have hb_ne : |U b b| ≠ 0 := ne_of_gt (abs_pos.mpr (hU_diag b))
      exact le_trans (mul_le_mul_of_nonneg_right hbnd (abs_nonneg _))
        (le_of_eq (one_div_mul_cancel hb_ne))
  have hconv : ∀ k l : Fin n, |U_inv i k| * |U k l| = |V_inv i k| * |V k l| := by
    intro k l
    simp only [V, V_inv]
    have hk := hU_diag k
    rw [show U_inv i k * U k k = U k k * U_inv i k from mul_comm _ _, abs_mul, abs_div]
    have hkpos : (0 : ℝ) < |U k k| := abs_pos.mpr hk
    field_simp [ne_of_gt hkpos]
  have hbound := unit_bidiag_row_sum_bound n hn V V_inv hVT hV_unit hV_bidiag
    hV_bound hVinv_bound i
  calc ∑ l : Fin n, ∑ k : Fin n, |U_inv i k| * |U k l|
      = ∑ l : Fin n, ∑ k : Fin n, |V_inv i k| * |V k l| := by
        apply Finset.sum_congr rfl; intro l _
        apply Finset.sum_congr rfl; intro k _
        exact hconv k l
    _ ≤ 2 * (n : ℝ) - 1 := hbound

-- ============================================================
-- §15.6  Theorem 15.8 — honest closure from row diagonal dominance
-- ============================================================

/-- **Theorem 15.8** (Higham §15.6, p. 300) — HONEST closure.

    "Suppose the nonsingular, row diagonally dominant tridiagonal matrix
    `A ∈ ℝⁿˣⁿ` has the LU factorization `A = LU`. Then, if `y ≥ 0`,
    `‖ |U⁻¹||L⁻¹| y ‖∞ ≤ (2n − 1) ‖ |A⁻¹| y ‖∞`."

    Unlike `H15_Theorem15_8`, this statement takes the PRINTED hypothesis
    `IsRowDiagDominant n A` (together with the bidiagonal LU structure
    `IsTridiagLU`, the product `A = LU`, nonzero pivots, and the explicit
    bidiagonal inverse formula for `U⁻¹`) and DERIVES the row-sum crux
    `∑ₗ∑ₖ |U⁻¹_{ik}||U_{kl}| ≤ 2n−1` internally, via row-dominance propagation
    (`c15_bidiag_U_isDiagDominantUpper`) and `unit_bidiag_row_sum_bound`.  The
    hypotheses `hU_inv_ut`/`hU_inv_eq` merely pin `U_inv` to be *the* inverse of
    the bidiagonal `U` (a structural identity true for every nonsingular
    bidiagonal matrix, independent of dominance); they are not the crux. -/
theorem H15_Theorem15_8_of_rowDiagDominant (n : ℕ) (hn : 0 < n)
    (A L U A_inv L_inv U_inv : Fin n → Fin n → ℝ)
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hStruct : IsTridiagLU n L U)
    (hLU : ∀ i j, ∑ k : Fin n, L i k * U k j = A i j)
    (hRowDom : IsRowDiagDominant n A)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hLInv : IsLeftInverse n L L_inv)
    (hAInv : IsRightInverse n A A_inv)
    (hU_inv_ut : ∀ i k : Fin n, k.val < i.val → U_inv i k = 0)
    (hU_inv_eq : ∀ i k : Fin n, i.val ≤ k.val →
      U_inv i k = upperBidiagInvEntry (fun m => U m m)
        (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0) i k) :
    infNormVec (fun i => ∑ j : Fin n,
      (∑ k : Fin n, |U_inv i k| * |L_inv k j|) * y j) ≤
    (2 * (n : ℝ) - 1) * infNormVec (fun i => ∑ j : Fin n,
      |A_inv i j| * y j) := by
  have hDD : IsDiagDominantUpper n U :=
    c15_bidiag_U_isDiagDominantUpper L U A hStruct hLU hRowDom hU_diag
  have hRowSum := c15_bidiag_rowSum_bound hn U U_inv hU_diag
    hStruct.U_upper_bidiag hDD hU_inv_ut hU_inv_eq
  exact LeanFpAnalysis.FP.Ch15.H15_Theorem15_8 n hn A L U A_inv L_inv U_inv y hy
    hLU hLInv hAInv hRowSum

end LeanFpAnalysis.FP.Ch15Closure
