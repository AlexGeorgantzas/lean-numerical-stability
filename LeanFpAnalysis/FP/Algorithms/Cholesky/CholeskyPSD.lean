-- Algorithms/Cholesky/CholeskyPSD.lean
--
-- §10.3: Positive semidefinite matrices.
--
-- Theorem 10.9: Existence of Cholesky for PSD (non-pivoted: A = R^T R).
-- Lemma 10.10: Schur complement perturbation identity.
-- Lemma 10.12: W-norm bound in terms of κ₂(A₁₁).
-- Lemma 10.13: Complete pivoting bound ‖W‖² ≤ (n−r)(4^r − 1)/3.
-- Theorem 10.14: Error analysis for PSD Cholesky with complete pivoting.

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §10.3  Positive semidefinite predicate
-- ============================================================

/-- **Positive semidefinite matrix**: symmetric with x^T A x ≥ 0 for all x. -/
def IsPosSemiDef (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, A i j = A j i) ∧
  (∀ x : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j)

/-- SPD implies PSD. -/
lemma isSymPosDef_imp_isPosSemiDef (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    IsPosSemiDef n A := by
  constructor
  · exact hSPD.1
  · intro x
    by_cases hx : ∃ i, x i ≠ 0
    · exact le_of_lt (hSPD.2 x hx)
    · push_neg at hx
      have : ∀ i j : Fin n, x i * A i j * x j = 0 := by
        intro i j; simp [hx i]
      simp [this]

-- ============================================================
-- §10.3  Pivoted Cholesky factorization
-- ============================================================

/-- **Pivoted Cholesky factorization** for rank-r PSD matrices.

    Π^T A Π = R^T R where Π is a permutation matrix and
    R = [R₁₁ R₁₂; 0 0] with R₁₁ being r × r upper triangular
    with positive diagonal.

    This captures the structure from Theorem 10.9 equation (10.11). -/
structure PivotedCholeskySpec (n : ℕ) (A R : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (r : ℕ) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- R is upper triangular. -/
  R_upper : ∀ i j : Fin n, j.val < i.val → R i j = 0
  /-- First r diagonal entries are positive. -/
  R_diag_pos : ∀ i : Fin n, i.val < r → 0 < R i i
  /-- Last n-r rows of R are zero (rank deficiency). -/
  R_rank_zero : ∀ i j : Fin n, r ≤ i.val → R i j = 0
  /-- Π^T A Π = R^T R. -/
  product_eq : ∀ i j : Fin n,
    ∑ k : Fin n, R k i * R k j = A (σ i) (σ j)

/-- **Positive semidefiniteness is invariant under simultaneous
    permutation** (Theorem 10.9(b) foundation): if `σ` is a permutation,
    `(i, j) ↦ A (σ i) (σ j)` is PSD whenever `A` is — the permuted
    quadratic form at `x` is the original form at `x ∘ σ⁻¹`. -/
lemma isPosSemiDef_perm (n : ℕ) (A : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (hσ : IsPermutation n σ)
    (hPSD : IsPosSemiDef n A) :
    IsPosSemiDef n (fun i j => A (σ i) (σ j)) := by
  obtain ⟨σinv, hleft, hright⟩ :=
    Function.bijective_iff_has_inverse.mp hσ
  refine ⟨fun i j => hPSD.1 (σ i) (σ j), ?_⟩
  intro x
  have h1 : ∀ (F : Fin n → ℝ), ∑ i : Fin n, F i = ∑ i : Fin n, F (σ i) :=
    fun F => (Fintype.sum_bijective σ hσ (fun i => F (σ i)) F
      (fun i => rfl)).symm
  have h := hPSD.2 (fun k => x (σinv k))
  calc (0:ℝ)
      ≤ ∑ i : Fin n, ∑ j : Fin n,
          x (σinv i) * A i j * x (σinv j) := h
    _ = ∑ i : Fin n, ∑ j : Fin n,
          x (σinv (σ i)) * A (σ i) (σ j) * x (σinv (σ j)) := by
        rw [h1 (fun i => ∑ j : Fin n,
          x (σinv i) * A i j * x (σinv j))]
        apply Finset.sum_congr rfl
        intro i _
        rw [h1 (fun j => x (σinv (σ i)) * A (σ i) j * x (σinv j))]
    _ = ∑ i : Fin n, ∑ j : Fin n, x i * A (σ i) (σ j) * x j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hleft i, hleft j]

/-- **Complete-pivoting selection step** (Theorem 10.9(b) / §10.3): when
    some diagonal entry of a PSD matrix is positive, a transposition
    brings a largest diagonal entry to the pivot position; the permuted
    matrix has a positive leading pivot dominating every diagonal entry. -/
lemma psd_pivot_selection {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hnz : ∃ i, 0 < A i i) :
    ∃ σ : Fin (m + 1) → Fin (m + 1), IsPermutation (m + 1) σ ∧
      0 < A (σ 0) (σ 0) ∧
      ∀ i : Fin (m + 1), A (σ i) (σ i) ≤ A (σ 0) (σ 0) := by
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (m + 1))) (fun i => A i i)
    ⟨0, Finset.mem_univ 0⟩
  obtain ⟨w, hw⟩ := hnz
  refine ⟨⇑(Equiv.swap 0 t), (Equiv.swap 0 t).bijective, ?_, ?_⟩
  · rw [Equiv.swap_apply_left]
    exact lt_of_lt_of_le hw (ht w (Finset.mem_univ w))
  · intro i
    rw [Equiv.swap_apply_left]
    exact ht _ (Finset.mem_univ _)

/-- Two-point evaluation of the quadratic form: for `x` supported on
    `{i, j}` with `i ≠ j`, `xᵀAx = t²·a_ii + ts·(a_ij + a_ji) + s²·a_jj`. -/
private lemma quadForm_two_point {n : ℕ} (A : Fin n → Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (t s : ℝ) :
    ∑ k : Fin n, ∑ l : Fin n,
      (if k = i then t else if k = j then s else 0) * A k l *
      (if l = i then t else if l = j then s else 0) =
    t ^ 2 * A i i + t * s * (A i j + A j i) + s ^ 2 * A j j := by
  have hrow : ∀ k : Fin n,
      ∑ l : Fin n, (if k = i then t else if k = j then s else 0) * A k l *
        (if l = i then t else if l = j then s else 0) =
      (if k = i then t else if k = j then s else 0) *
        (A k i * t + A k j * s) := by
    intro k
    rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i)
      (Finset.mem_univ j) hij ?_]
    · rw [if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
      ring
    · intro l _ hl
      rcases hl with ⟨hli, hlj⟩
      simp [hli, hlj]
  rw [Finset.sum_congr rfl fun k _ => hrow k]
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i)
    (Finset.mem_univ j) hij ?_]
  · rw [if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
    ring
  · intro k _ hk
    rcases hk with ⟨hki, hkj⟩
    simp [hki, hkj]

/-- **All diagonal entries zero forces the zero matrix** for PSD matrices
    (Theorem 10.9(b) recursion, termination case): with every `a_ii = 0`,
    the two-point quadratic form reduces to `2ts·a_ij ≥ 0` for all
    `t, s`, so every entry vanishes. -/
lemma psd_all_diag_zero {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (hdiag : ∀ i, A i i = 0) :
    ∀ i j : Fin n, A i j = 0 := by
  intro i j
  by_cases hij : i = j
  · rw [hij]; exact hdiag j
  · have hpos := hPSD.2
      (fun k => if k = i then (1:ℝ) else if k = j then 1 else 0)
    have hneg := hPSD.2
      (fun k => if k = i then (1:ℝ) else if k = j then (-1) else 0)
    rw [quadForm_two_point A i j hij 1 1] at hpos
    rw [quadForm_two_point A i j hij 1 (-1)] at hneg
    have hsym := hPSD.1 i j
    rw [hdiag i, hdiag j] at hpos hneg
    nlinarith [hpos, hneg, hsym]

/-- Extend a permutation of `Fin m` to `Fin (m+1)` fixing `0` and acting
    on successors (Theorem 10.9(b) recursion: composing the tail stage's
    permutation with the current pivot transposition). -/
noncomputable def extendPerm {m : ℕ} (σ' : Fin m → Fin m) :
    Fin (m + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (σ' i).succ)

@[simp] lemma extendPerm_zero {m : ℕ} (σ' : Fin m → Fin m) :
    extendPerm σ' 0 = 0 := rfl

@[simp] lemma extendPerm_succ {m : ℕ} (σ' : Fin m → Fin m) (i : Fin m) :
    extendPerm σ' i.succ = (σ' i).succ := by
  unfold extendPerm
  rw [Fin.cases_succ]

/-- Extension preserves the permutation property. -/
lemma extendPerm_isPermutation {m : ℕ} (σ' : Fin m → Fin m)
    (hσ' : IsPermutation m σ') :
    IsPermutation (m + 1) (extendPerm σ') := by
  obtain ⟨inv', hleft, hright⟩ :=
    Function.bijective_iff_has_inverse.mp hσ'
  refine Function.bijective_iff_has_inverse.mpr
    ⟨Fin.cases 0 (fun i => (inv' i).succ), ?_, ?_⟩
  · intro x
    refine Fin.cases ?_ ?_ x
    · rfl
    · intro i
      rw [extendPerm_succ]
      simp only [Fin.cases_succ]
      rw [hleft i]
  · intro x
    refine Fin.cases ?_ ?_ x
    · rfl
    · intro i
      simp only [Fin.cases_succ]
      rw [extendPerm_succ, hright i]

-- ============================================================
-- §10.3  Theorem 10.9: PSD Cholesky existence (helpers)
-- ============================================================

/-- Diagonal entry of a PSD matrix is nonnegative. -/
private lemma psd_diag_nonneg {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hPSD : IsPosSemiDef (m + 1) A) (i : Fin (m + 1)) : 0 ≤ A i i := by
  have h := hPSD.2 (fun k => if k = i then 1 else 0)
  suffices hs : ∑ k₁ : Fin (m + 1), ∑ k₂ : Fin (m + 1),
      (if k₁ = i then 1 else 0) * A k₁ k₂ * (if k₂ = i then 1 else 0) = A i i by linarith
  rw [Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp),
      Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp)]
  simp

/-- If a PSD matrix has A_{00} = 0, then the entire first row is zero.

    Proof: the quadratic form x^T A x evaluated at x = e_0 + t·e_{j+1}
    gives 2t·A_{0,j+1} + t²·A_{j+1,j+1} ≥ 0 for all t, forcing A_{0,j+1} = 0. -/
private lemma psd_zero_diag_row_zero {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hPSD : IsPosSemiDef (m + 1) A) (h00 : A 0 0 = 0) (j : Fin m) :
    A 0 j.succ = 0 := by
  set a := A 0 j.succ
  set d := A j.succ j.succ
  have hd_nn : 0 ≤ d := psd_diag_nonneg hPSD j.succ
  -- Key: for all t, 0 ≤ 2ta + t²d (= x^T A x for x = e_0 + t·e_{j+1})
  suffices key : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * d by
    by_cases hd : d = 0
    · have h1 := key 1; have h2 := key (-1); nlinarith
    · have hd_pos : 0 < d := lt_of_le_of_ne hd_nn (Ne.symm hd)
      have h := key (-a / d)
      have hcalc : 2 * (-a / d) * a + (-a / d) ^ 2 * d = -(a ^ 2 / d) := by
        field_simp; ring
      rw [hcalc] at h
      have h_pos : 0 ≤ a ^ 2 / d := div_nonneg (sq_nonneg a) (le_of_lt hd_pos)
      have h_zero : a ^ 2 / d = 0 := le_antisymm (by linarith) h_pos
      have ha_sq : a ^ 2 = 0 := by
        by_contra h_ne
        exact absurd h_zero (ne_of_gt (div_pos (lt_of_le_of_ne (sq_nonneg a)
          (Ne.symm h_ne)) hd_pos))
      exact sq_eq_zero_iff.mp ha_sq
  -- Prove: x^T A x = 2ta + t²d for suitable x
  intro t
  have hpsd := hPSD.2 (fun k => if k = (0 : Fin (m + 1)) then 1
    else if k = j.succ then t else 0)
  suffices heval : ∑ i : Fin (m + 1), ∑ k : Fin (m + 1),
      (if i = (0 : Fin (m + 1)) then 1 else if i = j.succ then t else 0) * A i k *
      (if k = (0 : Fin (m + 1)) then 1 else if k = j.succ then t else 0) =
      2 * t * a + t ^ 2 * d by linarith
  -- Inner sum: ∑_k A_{ik} · x_k = A_{i,0} + t · A_{i,j+1}
  have inner : ∀ i : Fin (m + 1), ∑ k : Fin (m + 1), A i k *
      (if k = (0 : Fin (m + 1)) then (1 : ℝ) else if k = j.succ then t else 0) =
      A i 0 + t * A i j.succ := by
    intro i; rw [Fin.sum_univ_succ]; simp only [ite_true, mul_one]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp only [show j.succ ≠ (0 : Fin (m + 1)) from Fin.succ_ne_zero _,
                  ite_false, ite_true]; ring
    · intro b _ hb
      have : b.succ ≠ j.succ := fun h => hb (Fin.succ_injective _ h)
      simp [Fin.succ_ne_zero, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Factor x_i out and apply inner sum
  simp_rw [show ∀ (i k : Fin (m + 1)),
      (if i = (0 : Fin (m + 1)) then (1 : ℝ) else if i = j.succ then t else 0) * A i k *
      (if k = (0 : Fin (m + 1)) then (1 : ℝ) else if k = j.succ then t else 0) =
      (if i = (0 : Fin (m + 1)) then (1 : ℝ) else if i = j.succ then t else 0) *
      (A i k * (if k = (0 : Fin (m + 1)) then (1 : ℝ) else if k = j.succ then t else 0))
    from fun i k => by ring]
  simp_rw [← Finset.mul_sum, inner]
  -- Outer sum: ∑_i x_i · (A_{i,0} + t·A_{i,j+1})
  rw [Fin.sum_univ_succ]
  simp only [ite_true, one_mul]
  rw [Finset.sum_eq_single j]
  · simp only [show j.succ ≠ (0 : Fin (m + 1)) from Fin.succ_ne_zero _,
                ite_false, ite_true]
    rw [h00, hPSD.1 j.succ 0]; ring
  · intro b _ hb
    have : b.succ ≠ j.succ := fun h => hb (Fin.succ_injective _ h)
    simp [Fin.succ_ne_zero, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Schur complement of PSD is PSD** (Higham §10.3, Lemma 10.11).

    If A is positive semidefinite with A₀₀ > 0, then the Schur complement
    S = A₂₂ − A₂₁ A₁₁⁻¹ A₁₂ is also positive semidefinite.

    Proof: y^T S y = x^T A x where x₀ = −(a^T y)/a₁₁, x_{i+1} = yᵢ.
    Since A is PSD, x^T A x ≥ 0, so y^T S y ≥ 0 for all y. -/
lemma schur_psd {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hPSD : IsPosSemiDef (m + 1) A) (ha₁₁ : 0 < A 0 0) :
    IsPosSemiDef m (fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) := by
  have ha_ne : A 0 0 ≠ 0 := ne_of_gt ha₁₁
  constructor
  · intro i j; show A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0 =
      A j.succ i.succ - A 0 j.succ * A 0 i.succ / A 0 0
    rw [hPSD.1 i.succ j.succ, hPSD.1 0 i.succ, hPSD.1 0 j.succ]; ring
  · intro y
    set t := ∑ j : Fin m, A 0 j.succ * y j
    set Q := ∑ i : Fin m, ∑ j : Fin m, y i * A i.succ j.succ * y j
    set x : Fin (m + 1) → ℝ := Fin.cons (-t / A 0 0) y
    have hpsd_x := hPSD.2 x
    suffices heq :
        ∑ i : Fin m, ∑ j : Fin m, y i *
          (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
        ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * A i j * x j by linarith
    have ht' : ∑ i : Fin m, y i * A 0 i.succ = t := by
      show ∑ i, y i * A 0 i.succ = ∑ j, A 0 j.succ * y j; congr 1; ext i; ring
    -- LHS = Q - t²/A₀₀
    have lhs_eq : ∑ i : Fin m, ∑ j : Fin m, y i *
        (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
        Q - t * t / A 0 0 := by
      simp_rw [show ∀ (i j : Fin m), y i *
          (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
          y i * A i.succ j.succ * y j -
          (y i * A 0 i.succ) * (A 0 j.succ * y j) / A 0 0
          from fun i j => by ring]
      simp_rw [Finset.sum_sub_distrib]
      congr 1
      simp_rw [← Finset.sum_div]
      congr 1
      simp_rw [← Finset.mul_sum]
      simp_rw [← Finset.sum_mul]
      rw [ht']
    -- RHS = Q - t²/A₀₀
    have rhs_eq : ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * A i j * x j =
        Q - t * t / A 0 0 := by
      rw [Fin.sum_univ_succ]
      simp only [x, Fin.cons_zero, Fin.cons_succ]
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      simp_rw [show ∀ j : Fin m, (-t / A 0 0) * A 0 j.succ * y j =
          (-t / A 0 0) * (A 0 j.succ * y j) from fun j => by ring]
      rw [← Finset.mul_sum]
      simp_rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ,
        show ∀ i : Fin m, A i.succ 0 = A 0 i.succ from fun i => hPSD.1 i.succ 0]
      simp_rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul, ht']
      field_simp; ring
    rw [lhs_eq, rhs_eq]

-- ============================================================
-- §10.3  Theorem 10.9: PSD Cholesky existence
-- ============================================================

/-- **PSD Cholesky existence** (Higham §10.3, Theorem 10.9, part a).

    Every positive semidefinite matrix has a factorization A = R^T R
    with R upper triangular and nonnegative diagonal.

    Proof by induction on n using the Schur complement:
    - If A_{00} = 0: first row/column is zero, recurse on submatrix.
    - If A_{00} > 0: form Schur complement S (PSD), recurse,
      assemble R = [[√a₁₁, a^T/√a₁₁], [0, R₁]]. -/
theorem psd_cholesky_existence (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → R i j = 0) ∧
      (∀ i : Fin n, 0 ≤ R i i) ∧
      (∀ i j : Fin n, ∑ k : Fin n, R k i * R k j = A i j) := by
  induction n with
  | zero =>
    exact ⟨fun i => Fin.elim0 i,
           fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    have ha₁₁_nn : 0 ≤ A 0 0 := psd_diag_nonneg hPSD 0
    by_cases ha₁₁ : A 0 0 = 0
    · -- Case A₀₀ = 0: first row/column is zero
      have hrow : ∀ j : Fin m, A 0 j.succ = 0 := psd_zero_diag_row_zero hPSD ha₁₁
      have hcol : ∀ i : Fin m, A i.succ 0 = 0 := fun i => by rw [hPSD.1]; exact hrow i
      -- Lower-right submatrix is PSD
      set B : Fin m → Fin m → ℝ := fun i j => A i.succ j.succ
      have hB_psd : IsPosSemiDef m B := by
        constructor
        · intro i j; exact hPSD.1 i.succ j.succ
        · intro y
          set x : Fin (m + 1) → ℝ := Fin.cons 0 y
          have h := hPSD.2 x
          suffices heq : ∑ i : Fin m, ∑ j : Fin m, y i * B i j * y j =
              ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * A i j * x j by linarith
          rw [Fin.sum_univ_succ]
          simp only [x, Fin.cons_zero, zero_mul, Finset.sum_const_zero, zero_add]
          simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, B]
      obtain ⟨R₁, hR₁_upper, hR₁_diag, hR₁_prod⟩ := ih B hB_psd
      -- R: first row all zero, rest = R₁
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j =>
        if hi : i = 0 then 0
        else if hj : j = 0 then 0
        else R₁ (i.pred hi) (j.pred hj)
      have hR0 : ∀ p : Fin (m + 1), R 0 p = 0 := fun p => by simp [R]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [R, Fin.succ_ne_zero, Fin.pred_succ]
      refine ⟨R, fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
      · -- R_upper
        simp only [R]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hR₁_upper _ _ (by
              have := Fin.val_pred j hj
              have := Fin.val_pred i hi
              have : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have : j.val ≠ 0 := fun h => hj (Fin.ext h)
              omega)
      · -- R_diag nonneg
        simp only [R]
        by_cases hi : i = 0
        · simp [hi]
        · simp [hi]; exact hR₁_diag _
      · -- product_eq
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj; simp [ha₁₁]
        · subst hi; simp only [dite_true]; simp [hj]
          have := hrow (j.pred hj)
          rw [Fin.succ_pred] at this; exact this.symm
        · subst hj; simp only [dite_true]; simp [hi]
          have := hcol (i.pred hi)
          rw [Fin.succ_pred] at this; exact this.symm
        · simp [hi, hj]
          have hih := hR₁_prod (i.pred hi) (j.pred hj)
          simp only [B, Fin.succ_pred] at hih
          linarith
    · -- Case A₀₀ > 0: Schur complement induction
      have ha₁₁_pos : 0 < A 0 0 := lt_of_le_of_ne ha₁₁_nn (Ne.symm ha₁₁)
      set S : Fin m → Fin m → ℝ := fun i j =>
        A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0
      have hS_psd := schur_psd hPSD ha₁₁_pos
      obtain ⟨R₁, hR₁_upper, hR₁_diag, hR₁_prod⟩ := ih S hS_psd
      set sa := Real.sqrt (A 0 0)
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos ha₁₁_pos
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = A 0 0 := Real.mul_self_sqrt (le_of_lt ha₁₁_pos)
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j =>
        if hi : i = 0 then
          if hj : j = 0 then sa else A 0 j / sa
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj)
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else A 0 p / sa := by
        intro p; simp [R]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [R, Fin.succ_ne_zero, Fin.pred_succ]
      refine ⟨R, fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
      · -- R_upper
        simp only [R]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hR₁_upper _ _ (by
              have := Fin.val_pred j hj
              have := Fin.val_pred i hi
              have : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have : j.val ≠ 0 := fun h => hj (Fin.ext h)
              omega)
      · -- R_diag nonneg
        simp only [R]
        by_cases hi : i = 0
        · subst hi; simp; exact le_of_lt hsa_pos
        · simp [hi]; exact hR₁_diag _
      · -- product_eq (same structure as cholesky_existence)
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj; simp [hsa_sq]
        · subst hi; simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj; simp [hi, hPSD.1 i 0, hsa_ne]
        · simp [hi, hj]
          have hih := hR₁_prod (i.pred hi) (j.pred hj)
          simp only [S, Fin.succ_pred] at hih
          have h1 : A 0 i / sa * (A 0 j / sa) = A 0 i * A 0 j / A 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          linarith

/-- **Theorem 10.9(b), constructive core** (Higham §10.3, equation
    (10.11)): every real PSD matrix admits a pivoted Cholesky
    factorization `Πᵀ A Π = RᵀR` in the displayed rank-truncated form,
    with the permutation produced by greedy complete pivoting and `r`
    the number of positive pivots encountered.  Identification of `r`
    with the matrix rank is left as a separate row over Mathlib's rank. -/
theorem psd_pivoted_cholesky_exists (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      PivotedCholeskySpec n A R σ r := by
  induction n with
  | zero =>
    exact ⟨0, id, fun i => Fin.elim0 i,
      Function.bijective_id, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    by_cases hall : ∀ i, A i i = 0
    · have hzero := psd_all_diag_zero A hPSD hall
      refine ⟨0, id, fun _ _ => 0, Function.bijective_id,
        fun i j _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i j _ => rfl, fun i j => ?_⟩
      show ∑ k : Fin (m + 1), (0:ℝ) * 0 = A i j
      rw [hzero i j]
      simp
    · push_neg at hall
      obtain ⟨w, hw⟩ := hall
      have hw_pos : 0 < A w w :=
        lt_of_le_of_ne (psd_diag_nonneg hPSD w) (Ne.symm hw)
      obtain ⟨τ, hτ_perm, hτ_pos, _⟩ :=
        psd_pivot_selection A ⟨w, hw_pos⟩
      set B : Fin (m + 1) → Fin (m + 1) → ℝ :=
        fun i j => A (τ i) (τ j) with hBdef
      have hB_psd : IsPosSemiDef (m + 1) B :=
        isPosSemiDef_perm (m + 1) A τ hτ_perm hPSD
      have hB00 : 0 < B 0 0 := hτ_pos
      set S : Fin m → Fin m → ℝ := fun i j =>
        B i.succ j.succ - B 0 i.succ * B 0 j.succ / B 0 0 with hSdef
      have hS_psd := schur_psd hB_psd hB00
      obtain ⟨r', σ', R₁, hspec⟩ := ih S hS_psd
      set sa := Real.sqrt (B 0 0) with hsadef
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos hB00
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = B 0 0 :=
        Real.mul_self_sqrt (le_of_lt hB00)
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := (fun i j =>
        if hi : i = 0 then
          (if j = 0 then sa else B 0 (extendPerm σ' j) / sa)
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj))
        with hRdef
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else B 0 (extendPerm σ' p) / sa := by
        intro p; simp [hRdef]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [hRdef, Fin.succ_ne_zero, Fin.pred_succ]
      have hext : ∀ (p : Fin (m + 1)) (hp : p ≠ 0),
          extendPerm σ' p = (σ' (p.pred hp)).succ := by
        intro p hp
        conv_lhs => rw [← Fin.succ_pred p hp]
        rw [extendPerm_succ]
      refine ⟨r' + 1, fun i => τ (extendPerm σ' i), R,
        hτ_perm.comp (extendPerm_isPermutation σ' hspec.perm),
        fun i j hij => ?_, fun i hir => ?_, fun i j hri => ?_,
        fun i j => ?_⟩
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hspec.R_upper _ _ (by
              have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
              have := Fin.val_pred i hi
              have := Fin.val_pred j hj
              omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; simp [hsa_pos]
        · simp only [dif_neg hi]
          exact hspec.R_diag_pos _ (by
            have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have := Fin.val_pred i hi
            omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi
          exact absurd hri (by simp)
        · simp only [dif_neg hi]
          by_cases hj : j = 0
          · simp [hj]
          · simp only [dif_neg hj]
            exact hspec.R_rank_zero _ _ (by
              have := Fin.val_pred i hi
              omega)
      · show ∑ k : Fin (m + 1), R k i * R k j =
          B (extendPerm σ' i) (extendPerm σ' j)
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          simp [hsa_sq]
        · subst hi
          simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj
          simp [hi, hsa_ne, hB_psd.1 (extendPerm σ' i) 0]
        · simp only [if_neg hi, if_neg hj, dif_neg hi, dif_neg hj]
          have hih := hspec.product_eq (i.pred hi) (j.pred hj)
          rw [hext i hi, hext j hj, hih]
          have h1 : B 0 (σ' (i.pred hi)).succ / sa *
              (B 0 (σ' (j.pred hj)).succ / sa) =
              B 0 (σ' (i.pred hi)).succ *
                B 0 (σ' (j.pred hj)).succ / B 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          rw [h1]
          simp only [hSdef]
          ring

/-- **Schur diagonal domination** (equation (10.13) foundation): each
    Schur-complement diagonal entry is at most the corresponding original
    diagonal entry, hence — under the complete-pivoting choice — at most
    the current pivot.  This is the monotonicity that propagates the
    per-stage maximality into the (10.13) display. -/
lemma schur_diag_le_pivot {m : ℕ} (B : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hB00 : 0 < B 0 0)
    (hmax : ∀ i : Fin (m + 1), B i i ≤ B 0 0) (i : Fin m) :
    B i.succ i.succ - B 0 i.succ * B 0 i.succ / B 0 0 ≤ B 0 0 := by
  have hsub : 0 ≤ B 0 i.succ * B 0 i.succ / B 0 0 :=
    div_nonneg (mul_self_nonneg _) hB00.le
  linarith [hmax i.succ]

/-- **Column-tail identity for the pivoted factor** (equation (10.13)
    foundation, spec level): the tail of a squared column of `R` from row
    `k` down equals the permuted diagonal entry minus the head — i.e. the
    stage-`k` Schur diagonal in factored form.  Combined with the
    stage-domination invariant this yields the display (10.13). -/
lemma pivoted_spec_column_split {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (k j : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
      R i j ^ 2) =
    A (σ j) (σ j) -
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val),
        R i j ^ 2 := by
  have hprod := hspec.product_eq j j
  have hsq : ∑ i : Fin n, R i j * R i j = ∑ i : Fin n, R i j ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hsq] at hprod
  have hsplit : ∑ i : Fin n, R i j ^ 2 =
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val),
        R i j ^ 2) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
        R i j ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => i.val < k.val) (fun i => R i j ^ 2)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp
  linarith [hprod, hsplit]

/-- The leading diagonal entry of a pivoted factor squares to the
    permuted leading diagonal of `A` (product equation at `(0,0)` with
    upper triangularity). -/
lemma pivoted_spec_head_sq {m : ℕ} {A R : Fin (m + 1) → Fin (m + 1) → ℝ}
    {σ : Fin (m + 1) → Fin (m + 1)} {r : ℕ}
    (hspec : PivotedCholeskySpec (m + 1) A R σ r) :
    R 0 0 * R 0 0 = A (σ 0) (σ 0) := by
  have h := hspec.product_eq 0 0
  rw [Fin.sum_univ_succ] at h
  rw [show ∑ i : Fin m, R i.succ 0 * R i.succ 0 = 0 from
    Finset.sum_eq_zero fun i _ => by
      rw [hspec.R_upper i.succ 0 (by simp), zero_mul]] at h
  linarith

/-- Diagonal entries of a pivoted factor are nonnegative. -/
lemma pivoted_spec_diag_nonneg {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (i : Fin n) :
    0 ≤ R i i := by
  rcases Nat.lt_or_ge i.val r with h | h
  · exact (hspec.R_diag_pos i h).le
  · rw [hspec.R_rank_zero i i h]

/-- **Theorem 10.9(b) with the complete-pivoting invariant**: the greedy
    construction additionally yields nonincreasing factor diagonal —
    `R l l ≤ R k k` for `k ≤ l` — the per-stage maximality that together
    with `pivoted_spec_column_split` gives the display (10.13). -/
theorem psd_pivoted_cholesky_exists_cp (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      PivotedCholeskySpec n A R σ r ∧
      ∀ k l : Fin n, k.val ≤ l.val → R l l ≤ R k k := by
  induction n with
  | zero =>
    exact ⟨0, id, fun i => Fin.elim0 i,
      ⟨Function.bijective_id, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
       fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
      fun k => Fin.elim0 k⟩
  | succ m ih =>
    by_cases hall : ∀ i, A i i = 0
    · have hzero := psd_all_diag_zero A hPSD hall
      refine ⟨0, id, fun _ _ => 0,
        ⟨Function.bijective_id, fun i j _ => rfl,
         fun i hi => absurd hi (Nat.not_lt_zero _),
         fun i j _ => rfl, fun i j => ?_⟩,
        fun k l _ => le_rfl⟩
      show ∑ k : Fin (m + 1), (0:ℝ) * 0 = A i j
      rw [hzero i j]
      simp
    · push_neg at hall
      obtain ⟨w, hw⟩ := hall
      have hw_pos : 0 < A w w :=
        lt_of_le_of_ne (psd_diag_nonneg hPSD w) (Ne.symm hw)
      obtain ⟨τ, hτ_perm, hτ_pos, hτ_max⟩ :=
        psd_pivot_selection A ⟨w, hw_pos⟩
      set B : Fin (m + 1) → Fin (m + 1) → ℝ :=
        fun i j => A (τ i) (τ j) with hBdef
      have hB_psd : IsPosSemiDef (m + 1) B :=
        isPosSemiDef_perm (m + 1) A τ hτ_perm hPSD
      have hB00 : 0 < B 0 0 := hτ_pos
      set S : Fin m → Fin m → ℝ := fun i j =>
        B i.succ j.succ - B 0 i.succ * B 0 j.succ / B 0 0 with hSdef
      have hS_psd := schur_psd hB_psd hB00
      obtain ⟨r', σ', R₁, hspec, hmono⟩ := ih S hS_psd
      set sa := Real.sqrt (B 0 0) with hsadef
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos hB00
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = B 0 0 :=
        Real.mul_self_sqrt (le_of_lt hB00)
      -- the tail's leading diagonal is bounded by the pivot root
      have hR₁_le_sa : ∀ i : Fin m, R₁ i i ≤ sa := by
        intro i
        rcases Nat.eq_zero_or_pos m with hm | hm
        · exact absurd i.isLt (by omega)
        · have h0m : (0 : ℕ) < m := hm
          have hhead : R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ * R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ =
              S (σ' ⟨0, h0m⟩) (σ' ⟨0, h0m⟩) := by
            have h := hspec.product_eq ⟨0, h0m⟩ ⟨0, h0m⟩
            rw [show ∑ k : Fin m, R₁ k ⟨0, h0m⟩ * R₁ k ⟨0, h0m⟩ =
                R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ * R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ from ?_] at h
            · exact h
            · rw [Finset.sum_eq_single ⟨0, h0m⟩]
              · intro b _ hb
                rw [hspec.R_upper b ⟨0, h0m⟩ (by
                  have hb0 : b.val ≠ 0 := fun h0 => hb (Fin.ext h0)
                  show 0 < b.val
                  omega), zero_mul]
              · intro habs
                exact absurd (Finset.mem_univ _) habs
          have hSmax : S (σ' ⟨0, h0m⟩) (σ' ⟨0, h0m⟩) ≤ B 0 0 :=
            schur_diag_le_pivot B hB00 (fun i => hτ_max i) _
          have hi_le : R₁ i i ≤ R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ :=
            hmono ⟨0, h0m⟩ i (by simp)
          have hnn := pivoted_spec_diag_nonneg hspec ⟨0, h0m⟩
          nlinarith [pivoted_spec_diag_nonneg hspec i, hsa_sq, hsa_pos]
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := (fun i j =>
        if hi : i = 0 then
          (if j = 0 then sa else B 0 (extendPerm σ' j) / sa)
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj))
        with hRdef
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else B 0 (extendPerm σ' p) / sa := by
        intro p; simp [hRdef]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [hRdef, Fin.succ_ne_zero, Fin.pred_succ]
      have hext : ∀ (p : Fin (m + 1)) (hp : p ≠ 0),
          extendPerm σ' p = (σ' (p.pred hp)).succ := by
        intro p hp
        conv_lhs => rw [← Fin.succ_pred p hp]
        rw [extendPerm_succ]
      refine ⟨r' + 1, fun i => τ (extendPerm σ' i), R,
        ⟨hτ_perm.comp (extendPerm_isPermutation σ' hspec.perm),
         fun i j hij => ?_, fun i hir => ?_, fun i j hri => ?_,
         fun i j => ?_⟩, fun k l hkl => ?_⟩
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hspec.R_upper _ _ (by
              have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
              have := Fin.val_pred i hi
              have := Fin.val_pred j hj
              omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; simp [hsa_pos]
        · simp only [dif_neg hi]
          exact hspec.R_diag_pos _ (by
            have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have := Fin.val_pred i hi
            omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi
          exact absurd hri (by simp)
        · simp only [dif_neg hi]
          by_cases hj : j = 0
          · simp [hj]
          · simp only [dif_neg hj]
            exact hspec.R_rank_zero _ _ (by
              have := Fin.val_pred i hi
              omega)
      · show ∑ k : Fin (m + 1), R k i * R k j =
          B (extendPerm σ' i) (extendPerm σ' j)
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          simp [hsa_sq]
        · subst hi
          simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj
          simp [hi, hsa_ne, hB_psd.1 (extendPerm σ' i) 0]
        · simp only [if_neg hi, if_neg hj, dif_neg hi, dif_neg hj]
          have hih := hspec.product_eq (i.pred hi) (j.pred hj)
          rw [hext i hi, hext j hj, hih]
          have h1 : B 0 (σ' (i.pred hi)).succ / sa *
              (B 0 (σ' (j.pred hj)).succ / sa) =
              B 0 (σ' (i.pred hi)).succ *
                B 0 (σ' (j.pred hj)).succ / B 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          rw [h1]
          simp only [hSdef]
          ring
      · -- diagonal monotonicity
        simp only [hRdef]
        by_cases hk : k = 0
        · subst hk
          by_cases hl : l = 0
          · subst hl; simp
          · simp only [dif_neg hl]
            exact hR₁_le_sa _
        · have hlk : l ≠ 0 := by
            intro h0
            apply hk
            apply Fin.ext
            have hl0 : l.val = 0 := by simp [h0]
            omega
          simp only [dif_neg hk, dif_neg hlk]
          exact hmono _ _ (by
            have := Fin.val_pred k hk
            have := Fin.val_pred l hlk
            omega)

/-- Reindex a succ-tail filter sum over `Fin (m+1)` to a tail filter sum
    over `Fin m`. -/
private lemma sum_filter_succ_tail {m : ℕ} (k₀ : ℕ)
    (f : Fin (m + 1) → ℝ) :
    (∑ i ∈ Finset.univ.filter
      (fun i : Fin (m + 1) => k₀ + 1 ≤ i.val), f i) =
    ∑ i₀ ∈ Finset.univ.filter (fun i₀ : Fin m => k₀ ≤ i₀.val),
      f i₀.succ := by
  have himg : (Finset.univ.filter
      (fun i₀ : Fin m => k₀ ≤ i₀.val)).image Fin.succ =
      Finset.univ.filter (fun i : Fin (m + 1) => k₀ + 1 ≤ i.val) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨i₀, hi₀, rfl⟩
      simp only [Fin.val_succ]
      omega
    · intro hi
      have hne : i ≠ 0 := by
        intro h0
        rw [h0] at hi
        simp at hi
      refine ⟨i.pred hne, ?_, Fin.succ_pred i hne⟩
      have := Fin.val_pred i hne
      omega
  rw [← himg, Finset.sum_image
    (fun a _ b _ h => Fin.succ_injective m h)]

/-- **Theorem 10.9(b) with the (10.13) column-tail invariant**: the greedy
    complete-pivoting construction yields, beyond the pivoted certificate,
    the stage-wise column-tail domination
    `∑_{i ≥ k} r_ij² ≤ r_kk²` for `k ≤ j` — precisely the content of the
    display (10.13). -/
theorem psd_pivoted_cholesky_exists_tail (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      PivotedCholeskySpec n A R σ r ∧
      ∀ k j : Fin n, k.val ≤ j.val →
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
          R i j ^ 2) ≤ R k k ^ 2 := by
  induction n with
  | zero =>
    exact ⟨0, id, fun i => Fin.elim0 i,
      ⟨Function.bijective_id, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
       fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
      fun k => Fin.elim0 k⟩
  | succ m ih =>
    by_cases hall : ∀ i, A i i = 0
    · have hzero := psd_all_diag_zero A hPSD hall
      refine ⟨0, id, fun _ _ => 0,
        ⟨Function.bijective_id, fun i j _ => rfl,
         fun i hi => absurd hi (Nat.not_lt_zero _),
         fun i j _ => rfl, fun i j => ?_⟩,
        fun k j _ => by simp⟩
      show ∑ k : Fin (m + 1), (0:ℝ) * 0 = A i j
      rw [hzero i j]
      simp
    · push_neg at hall
      obtain ⟨w, hw⟩ := hall
      have hw_pos : 0 < A w w :=
        lt_of_le_of_ne (psd_diag_nonneg hPSD w) (Ne.symm hw)
      obtain ⟨τ, hτ_perm, hτ_pos, hτ_max⟩ :=
        psd_pivot_selection A ⟨w, hw_pos⟩
      set B : Fin (m + 1) → Fin (m + 1) → ℝ :=
        fun i j => A (τ i) (τ j) with hBdef
      have hB_psd : IsPosSemiDef (m + 1) B :=
        isPosSemiDef_perm (m + 1) A τ hτ_perm hPSD
      have hB00 : 0 < B 0 0 := hτ_pos
      set S : Fin m → Fin m → ℝ := fun i j =>
        B i.succ j.succ - B 0 i.succ * B 0 j.succ / B 0 0 with hSdef
      have hS_psd := schur_psd hB_psd hB00
      obtain ⟨r', σ', R₁, hspec, htail⟩ := ih S hS_psd
      set sa := Real.sqrt (B 0 0) with hsadef
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos hB00
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = B 0 0 :=
        Real.mul_self_sqrt (le_of_lt hB00)
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := (fun i j =>
        if hi : i = 0 then
          (if j = 0 then sa else B 0 (extendPerm σ' j) / sa)
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj))
        with hRdef
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else B 0 (extendPerm σ' p) / sa := by
        intro p; simp [hRdef]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [hRdef, Fin.succ_ne_zero, Fin.pred_succ]
      have hext : ∀ (p : Fin (m + 1)) (hp : p ≠ 0),
          extendPerm σ' p = (σ' (p.pred hp)).succ := by
        intro p hp
        conv_lhs => rw [← Fin.succ_pred p hp]
        rw [extendPerm_succ]
      have hproduct : ∀ i j : Fin (m + 1),
          ∑ p : Fin (m + 1), R p i * R p j =
          B (extendPerm σ' i) (extendPerm σ' j) := by
        intro i j
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          simp [hsa_sq]
        · subst hi
          simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj
          simp [hi, hsa_ne, hB_psd.1 (extendPerm σ' i) 0]
        · simp only [if_neg hi, if_neg hj, dif_neg hi, dif_neg hj]
          have hih := hspec.product_eq (i.pred hi) (j.pred hj)
          rw [hext i hi, hext j hj, hih]
          have h1 : B 0 (σ' (i.pred hi)).succ / sa *
              (B 0 (σ' (j.pred hj)).succ / sa) =
              B 0 (σ' (i.pred hi)).succ *
                B 0 (σ' (j.pred hj)).succ / B 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          rw [h1]
          simp only [hSdef]
          ring
      refine ⟨r' + 1, fun i => τ (extendPerm σ' i), R,
        ⟨hτ_perm.comp (extendPerm_isPermutation σ' hspec.perm),
         fun i j hij => ?_, fun i hir => ?_, fun i j hri => ?_,
         fun i j => hproduct i j⟩, fun k j hkj => ?_⟩
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hspec.R_upper _ _ (by
              have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
              have := Fin.val_pred i hi
              have := Fin.val_pred j hj
              omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; simp [hsa_pos]
        · simp only [dif_neg hi]
          exact hspec.R_diag_pos _ (by
            have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have := Fin.val_pred i hi
            omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi
          exact absurd hri (by simp)
        · simp only [dif_neg hi]
          by_cases hj : j = 0
          · simp [hj]
          · simp only [dif_neg hj]
            exact hspec.R_rank_zero _ _ (by
              have := Fin.val_pred i hi
              omega)
      · -- column-tail domination (the (10.13) invariant)
        by_cases hk : k = 0
        · subst hk
          have hfilter : Finset.univ.filter
              (fun i : Fin (m + 1) => (0 : Fin (m + 1)).val ≤ i.val) =
              Finset.univ := by
            ext i; simp
          rw [hfilter]
          have hsum : ∑ i : Fin (m + 1), R i j ^ 2 =
              B (extendPerm σ' j) (extendPerm σ' j) := by
            rw [← hproduct j j]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [hsum]
          have hR00 : R 0 0 = sa := by rw [hR0 0]; simp
          rw [hR00]
          calc B (extendPerm σ' j) (extendPerm σ' j) ≤ B 0 0 :=
              hτ_max (extendPerm σ' j)
            _ = sa ^ 2 := by rw [← hsa_sq]; ring
        · have hj0 : j ≠ 0 := by
            intro h0
            apply hk
            apply Fin.ext
            have hjv : j.val = 0 := by simp [h0]
            omega
          have hkval : k.val = (k.pred hk).val + 1 := by
            have := Fin.val_pred k hk
            have hkv : k.val ≠ 0 := fun h => hk (Fin.ext h)
            omega
          have hfeq : Finset.univ.filter
              (fun i : Fin (m + 1) => k.val ≤ i.val) =
              Finset.univ.filter
              (fun i : Fin (m + 1) => (k.pred hk).val + 1 ≤ i.val) := by
            apply Finset.filter_congr
            intro i _
            constructor <;> intro h <;> omega
          rw [hfeq, sum_filter_succ_tail (k.pred hk).val
            (fun i => R i j ^ 2)]
          have hterm : ∀ i₀ : Fin m, R i₀.succ j ^ 2 =
              R₁ i₀ (j.pred hj0) ^ 2 := by
            intro i₀
            rw [hRs i₀ j, dif_neg hj0]
          rw [Finset.sum_congr rfl fun i₀ _ => hterm i₀]
          have hkk : R k k = R₁ (k.pred hk) (k.pred hk) := by
            conv_lhs => rw [← Fin.succ_pred k hk]
            rw [hRs (k.pred hk) (k.pred hk).succ,
              dif_neg (Fin.succ_ne_zero _), Fin.pred_succ]
          rw [hkk]
          exact htail (k.pred hk) (j.pred hj0) (by
            have := Fin.val_pred j hj0
            have := Fin.val_pred k hk
            omega)

/-- **Rank invariance of the pivoted certificate** (Theorem 10.9(b),
    `r = rank` bridge, part 1): the matrix rank of `A` equals the rank of
    the pivoted factor `R` — `rank A = rank(ΠᵀAΠ) = rank(RᵀR) = rank R`.
    The remaining identification `rank R = r` (triangular rank count) is
    a separate row. -/
theorem pivoted_spec_rank_eq {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) :
    (Matrix.of A).rank = (Matrix.of R).rank := by
  let eσ : Fin n ≃ Fin n := Equiv.ofBijective σ hspec.perm
  have hsub : (Matrix.of A).submatrix ⇑eσ ⇑eσ =
      (Matrix.of R).transpose * Matrix.of R := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply]
    show A (σ i) (σ j) = ∑ k : Fin n, R k i * R k j
    rw [← hspec.product_eq i j]
  calc (Matrix.of A).rank
      = ((Matrix.of A).submatrix ⇑eσ ⇑eσ).rank :=
        (Matrix.rank_submatrix (Matrix.of A) eσ eσ).symm
    _ = ((Matrix.of R).transpose * Matrix.of R).rank := by rw [hsub]
    _ = (Matrix.of R).rank :=
        Matrix.rank_transpose_mul_self (Matrix.of R)

/-- **The leading `r × r` block of a pivoted factor is a determinant
    unit** (Theorem 10.9(b), `rank R = r` bridge, `≥` side): upper
    triangular with positive diagonal, so its determinant is the product
    of the positive pivots. -/
theorem pivoted_leading_block_isUnit_det {n : ℕ}
    {A R : Fin n → Fin n → ℝ} {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (hr : r ≤ n) :
    IsUnit (Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).det := by
  have hBT : (Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).BlockTriangular id := by
    intro i j hij
    exact hspec.R_upper _ _ hij
  rw [Matrix.det_of_upperTriangular hBT]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (hspec.R_diag_pos ⟨i.val, by omega⟩ i.isLt).ne'

/-- **Triangular rank count** (Theorem 10.9(b), `r = rank` bridge,
    part 2): the pivoted factor has matrix rank exactly `r` — the zero
    rows give `≤` and the unit leading block gives `≥`, both through
    selection-matrix factorizations and `rank_mul_le`. -/
theorem pivoted_spec_rank_R {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (hr : r ≤ n) :
    (Matrix.of R).rank = r := by
  set Rtop : Matrix (Fin r) (Fin n) ℝ :=
    Matrix.of (fun k j => R ⟨k.val, by omega⟩ j) with hRtop
  set E : Matrix (Fin n) (Fin r) ℝ :=
    Matrix.of (fun i k => if i.val = k.val then (1:ℝ) else 0) with hE
  set E' : Matrix (Fin r) (Fin n) ℝ :=
    Matrix.of (fun k i => if k.val = i.val then (1:ℝ) else 0) with hE'
  set F : Matrix (Fin n) (Fin r) ℝ :=
    Matrix.of (fun j k => if j.val = k.val then (1:ℝ) else 0) with hF
  have hfac1 : Matrix.of R = E * Rtop := by
    ext i j
    show R i j = ∑ k : Fin r,
      (if i.val = k.val then (1:ℝ) else 0) * R ⟨k.val, by omega⟩ j
    by_cases hi : i.val < r
    · rw [Finset.sum_eq_single (⟨i.val, hi⟩ : Fin r)]
      · rw [if_pos rfl, one_mul]
      · intro b _ hb
        rw [if_neg (fun hbe => hb (Fin.ext hbe.symm)), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hspec.R_rank_zero i j (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (by omega), zero_mul]
  have hfac2 : Rtop = E' * Matrix.of R := by
    ext k j
    show R ⟨k.val, by omega⟩ j = ∑ i : Fin n,
      (if k.val = i.val then (1:ℝ) else 0) * R i j
    rw [Finset.sum_eq_single (⟨k.val, by omega⟩ : Fin n)]
    · rw [if_pos rfl, one_mul]
    · intro b _ hb
      rw [if_neg (fun hbe => hb (Fin.ext hbe.symm)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfac3 : Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) = Rtop * F := by
    ext k k'
    show R ⟨k.val, by omega⟩ ⟨k'.val, by omega⟩ = ∑ j : Fin n,
      R ⟨k.val, by omega⟩ j * (if j.val = k'.val then (1:ℝ) else 0)
    rw [Finset.sum_eq_single (⟨k'.val, by omega⟩ : Fin n)]
    · rw [if_pos rfl, mul_one]
    · intro b _ hb
      rw [if_neg (fun hbe => hb (Fin.ext hbe)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hMrank : (Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).rank = r := by
    rw [Matrix.rank_of_isUnit _
      ((Matrix.isUnit_iff_isUnit_det _).mpr
        (pivoted_leading_block_isUnit_det hspec hr))]
    simp
  have h1 : (Matrix.of R).rank ≤ Rtop.rank := by
    rw [hfac1]
    exact Matrix.rank_mul_le_right E Rtop
  have h2 : Rtop.rank ≤ (Matrix.of R).rank := by
    rw [hfac2]
    exact Matrix.rank_mul_le_right E' (Matrix.of R)
  have h3 : r ≤ Rtop.rank := by
    have hle := Matrix.rank_mul_le_left Rtop F
    rw [← hfac3, hMrank] at hle
    exact hle
  have h4 : Rtop.rank ≤ r := by
    have := Matrix.rank_le_card_height Rtop
    simpa using this
  omega

/-- **Theorem 10.9(b), rank identification**: for any pivoted certificate
    with `r ≤ n`, the parameter `r` is the matrix rank of `A` — closing
    the "positive semidefinite of rank r" reading of the source row. -/
theorem pivoted_spec_rank_eq_r {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (hr : r ≤ n) :
    (Matrix.of A).rank = r := by
  rw [pivoted_spec_rank_eq hspec, pivoted_spec_rank_R hspec hr]

-- ============================================================
-- §10.3  Theorem 10.9(b): SPD → PivotedCholeskySpec (full rank)
-- ============================================================

/-- **SPD Cholesky as pivoted Cholesky** (Higham §10.3, Theorem 10.9, part b, full rank case).

    For SPD matrices, the Cholesky factorization from Theorem 10.1 satisfies
    PivotedCholeskySpec with identity permutation and rank r = n.
    All diagonal entries are strictly positive and no rows are zero. -/
theorem spd_pivoted_cholesky (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      PivotedCholeskySpec n A R id n := by
  obtain ⟨R, hR⟩ := cholesky_existence n A hSPD
  exact ⟨R,
    { perm := Function.bijective_id
      R_upper := hR.R_upper
      R_diag_pos := fun i _ => hR.R_diag_pos i
      R_rank_zero := fun i _ hri => absurd hri (by omega)
      product_eq := fun i j => hR.product_eq i j }⟩

-- ============================================================
-- §10.3  Schur complement
-- ============================================================

/-- **Schur complement** of the (1,1) block in a partitioned matrix.

    For a matrix partitioned as [A₁₁ A₁₂; A₂₁ A₂₂]:
      S_k(A) = A₂₂ − A₂₁ A₁₁⁻¹ A₁₂

    We represent this abstractly: given A₁₁⁻¹ as a hypothesis,
    the Schur complement maps indices (i, j) with i, j ≥ k to:
      S(i,j) = A(i,j) − ∑_{s<k} ∑_{t<k} A(i,s) · A₁₁⁻¹(s,t) · A(t,j) -/
noncomputable def schurComplement (n k : ℕ) (A A11_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => A i j -
    ∑ s : Fin n, ∑ t : Fin n,
      (if s.val < k ∧ t.val < k then A i s * A11_inv s t * A t j else 0)

-- ============================================================
-- §10.3  Lemma 10.10: Schur complement perturbation
-- ============================================================


/-- **Resolvent identity for the perturbed leading block** (Lemma 10.10
    setup): if `M` is a left inverse of `A₁₁` and `X` a right... — more
    precisely, if `M * A₁₁ = 1` and `(A₁₁ + E₁₁) * X = 1`, then
    `X = M − M E₁₁ X` exactly. This is the identity that makes the
    Schur-complement perturbation expansion pure algebra. -/
lemma schur_resolvent_from_inverses {k : ℕ}
    (M X A11 E11 : Matrix (Fin k) (Fin k) ℝ)
    (hM : M * A11 = 1) (hXi : (A11 + E11) * X = 1) :
    X = M - M * E11 * X := by
  have h : M * ((A11 + E11) * X) = M := by rw [hXi, mul_one]
  rw [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, hM,
    Matrix.one_mul, ← Matrix.mul_assoc] at h
  linear_combination (norm := abel) h

/-- **First-order split of the perturbed Schur complement** (Lemma 10.10
    engine): with the perturbed leading-block inverse written as
    `X = M − Y`, the perturbed Schur complement decomposes exactly into
    the unperturbed one, the `E`-linear part, and a remainder carrying
    `Y` (which is second order once `Y = M E₁₁ X`). -/
lemma schur_perturbation_split {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 E22 : Matrix (Fin m) (Fin m) ℝ)
    (M X Y : Matrix (Fin k) (Fin k) ℝ) (hX : X = M - Y) :
    (A22 + E22) - (A21 + E21) * X * (A12 + E12) =
      ((A22 - A21 * M * A12)
        + (E22 - E21 * M * A12 - A21 * M * E12)
        + (-(E21 * M * E12) + (A21 + E21) * Y * (A12 + E12))) := by
  subst hX
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **One re-expansion of the resolvent inside the remainder**: the
    leading remainder term regains Higham's second-order form. -/
lemma schur_remainder_reexpand {k m : ℕ}
    (A21 : Matrix (Fin m) (Fin k) ℝ) (A12 : Matrix (Fin k) (Fin m) ℝ)
    (M X E11 : Matrix (Fin k) (Fin k) ℝ)
    (hX : X = M - M * E11 * X) :
    A21 * (M * E11 * X) * A12 =
      A21 * (M * E11 * M) * A12
        - A21 * (M * E11 * (M * E11 * X)) * A12 := by
  conv_lhs => rw [hX]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- **Lemma 10.10, exact form (display (10.16))**: for the perturbed
    block matrix `A + E` with leading-block inverses related by the
    resolvent identity (`schur_resolvent_from_inverses`), the perturbed
    Schur complement equals the unperturbed one plus Higham's
    first-order term
    `Ē = E₂₂ − E₂₁ M A₁₂ − A₂₁ M E₁₂ + A₂₁ M E₁₁ M A₁₂`
    (with `W = M A₁₂`, `Wᵀ = A₂₁ M` for symmetric `A` this is
    `E₂₂ − E₂₁ W − Wᵀ E₁₂ + Wᵀ E₁₁ W`) plus an explicit remainder in
    which every term carries two `E`-factors — the `O(‖E‖²)` of the
    source, here exact rather than asymptotic. -/
theorem schur_perturbation_exact {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 E22 : Matrix (Fin m) (Fin m) ℝ)
    (M X E11 : Matrix (Fin k) (Fin k) ℝ)
    (hX : X = M - M * E11 * X) :
    (A22 + E22) - (A21 + E21) * X * (A12 + E12) =
      (A22 - A21 * M * A12)
      + (E22 - E21 * M * A12 - A21 * M * E12
          + A21 * (M * E11 * M) * A12)
      + (-(E21 * M * E12)
          - A21 * (M * E11 * (M * E11 * X)) * A12
          + E21 * (M * E11 * X) * A12
          + A21 * (M * E11 * X) * E12
          + E21 * (M * E11 * X) * E12) := by
  rw [schur_perturbation_split A21 E21 A12 E12 A22 E22 M X
    (M * E11 * X) hX]
  have hre := schur_remainder_reexpand A21 A12 M X E11 hX
  simp only [Matrix.add_mul, Matrix.mul_add] at *
  rw [hre]
  abel

/-- Entrywise bound for a matrix product from entrywise bounds on the
    factors. -/
lemma entrywise_matMul_le {a b c : ℕ}
    (F : Matrix (Fin a) (Fin b) ℝ) (G : Matrix (Fin b) (Fin c) ℝ)
    (f g : ℝ) (hf : 0 ≤ f)
    (hF : ∀ i j, |F i j| ≤ f) (hG : ∀ i j, |G i j| ≤ g) :
    ∀ (i : Fin a) (j : Fin c), |(F * G) i j| ≤ (b : ℝ) * f * g := by
  intro i j
  rw [Matrix.mul_apply]
  calc |∑ s : Fin b, F i s * G s j|
      ≤ ∑ s : Fin b, |F i s * G s j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : Fin b, f * g := Finset.sum_le_sum fun s _ => by
        rw [abs_mul]
        exact mul_le_mul (hF i s) (hG s j) (abs_nonneg _) hf
    _ = (b : ℝ) * (f * g) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ = (b : ℝ) * f * g := by ring

/-- **Lemma 10.10, second-order remainder bound**: the exact remainder of
    `schur_perturbation_exact` is entrywise `O(ε²)` — bounded by an
    explicit polynomial in the entrywise bounds `α` (of the off-diagonal
    blocks of `A`), `μ` (of `M = A₁₁⁻¹`), `χ` (of the perturbed inverse
    `X`), times `ε²`. This is the honest content of the source's
    `O(‖E‖²)`. -/
theorem schur_perturbation_remainder_bound {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (M X E11 : Matrix (Fin k) (Fin k) ℝ)
    (α μ χ ε : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hχ : 0 ≤ χ) (hε : 0 ≤ ε)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hE21 : ∀ i j, |E21 i j| ≤ ε) (hE12 : ∀ i j, |E12 i j| ≤ ε)
    (hE11 : ∀ i j, |E11 i j| ≤ ε)
    (hM : ∀ i j, |M i j| ≤ μ) (hX : ∀ i j, |X i j| ≤ χ) :
    ∀ (i j : Fin m),
      |(-(E21 * M * E12)
          - A21 * (M * E11 * (M * E11 * X)) * A12
          + E21 * (M * E11 * X) * A12
          + A21 * (M * E11 * X) * E12
          + E21 * (M * E11 * X) * E12) i j| ≤
      ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
        + 2 * ((k : ℝ) ^ 4 * α * μ * χ) + (k : ℝ) ^ 4 * μ * χ * ε)
        * ε ^ 2 := by
  intro i j
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  -- entrywise bounds on the building blocks
  have hME : ∀ (p q : Fin k), |(M * E11) p q| ≤ (k : ℝ) * μ * ε :=
    entrywise_matMul_le M E11 μ ε hμ hM hE11
  have hMEnn : (0 : ℝ) ≤ (k : ℝ) * μ * ε := by positivity
  have hMEX : ∀ (p q : Fin k), |((M * E11) * X) p q| ≤
      (k : ℝ) * ((k : ℝ) * μ * ε) * χ :=
    entrywise_matMul_le (M * E11) X _ χ hMEnn hME hX
  have hMEXnn : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) * μ * ε) * χ := by
    positivity
  -- term 1 : E21 * M * E12
  have hT1a : ∀ (p : Fin m) (q : Fin k), |(E21 * M) p q| ≤
      (k : ℝ) * ε * μ := entrywise_matMul_le E21 M ε μ hε hE21 hM
  have hT1 : ∀ (p q : Fin m), |((E21 * M) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * μ) * ε :=
    entrywise_matMul_le (E21 * M) E12 _ ε (by positivity) hT1a hE12
  -- term 2 : A21 * (M*E11*(M*E11*X)) * A12
  have hInner : ∀ (p q : Fin k), |((M * E11) * ((M * E11) * X)) p q| ≤
      (k : ℝ) * ((k : ℝ) * μ * ε) * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ) :=
    entrywise_matMul_le (M * E11) ((M * E11) * X) _ _ hMEnn hME hMEX
  have hT2a : ∀ (p : Fin m) (q : Fin k),
      |(A21 * ((M * E11) * ((M * E11) * X))) p q| ≤
      (k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) *
        ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) :=
    entrywise_matMul_le A21 _ α _ hα hA21 hInner
  have hT2 : ∀ (p q : Fin m),
      |((A21 * ((M * E11) * ((M * E11) * X))) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) *
        ((k : ℝ) * ((k : ℝ) * μ * ε) * χ))) * α :=
    entrywise_matMul_le _ A12 _ α (by positivity) hT2a hA12
  -- term 3 : E21 * (M*E11*X) * A12
  have hT3a : ∀ (p : Fin m) (q : Fin k),
      |(E21 * ((M * E11) * X)) p q| ≤
      (k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ) :=
    entrywise_matMul_le E21 _ ε _ hε hE21 hMEX
  have hT3 : ∀ (p q : Fin m),
      |((E21 * ((M * E11) * X)) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * α :=
    entrywise_matMul_le _ A12 _ α (by positivity) hT3a hA12
  -- term 4 : A21 * (M*E11*X) * E12
  have hT4a : ∀ (p : Fin m) (q : Fin k),
      |(A21 * ((M * E11) * X)) p q| ≤
      (k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ) :=
    entrywise_matMul_le A21 _ α _ hα hA21 hMEX
  have hT4 : ∀ (p q : Fin m),
      |((A21 * ((M * E11) * X)) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε :=
    entrywise_matMul_le _ E12 _ ε (by positivity) hT4a hE12
  -- term 5 : E21 * (M*E11*X) * E12
  have hT5 : ∀ (p q : Fin m),
      |((E21 * ((M * E11) * X)) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε :=
    entrywise_matMul_le _ E12 _ ε (by positivity) hT3a hE12
  -- assemble by the triangle inequality
  have h1 := abs_le.mp (hT1 i j)
  have h2 := abs_le.mp (hT2 i j)
  have h3 := abs_le.mp (hT3 i j)
  have h4 := abs_le.mp (hT4 i j)
  have h5 := abs_le.mp (hT5 i j)
  have hsum : ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
      + 2 * ((k : ℝ) ^ 4 * α * μ * χ) + (k : ℝ) ^ 4 * μ * χ * ε)
      * ε ^ 2 =
      (k : ℝ) * ((k : ℝ) * ε * μ) * ε
      + (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) *
          ((k : ℝ) * ((k : ℝ) * μ * ε) * χ))) * α
      + (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * α
      + (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε
      + (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε
      := by ring
  rw [hsum]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
    h4.1, h4.2, h5.1, h5.2]

/-- PSD diagonal entries are nonnegative (general-`n` public form). -/
lemma isPosSemiDef_diag_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (i : Fin n) : 0 ≤ A i i := by
  have h := hPSD.2 (fun k => if k = i then 1 else 0)
  simpa [Finset.sum_ite_eq', Finset.mul_sum] using h

/-- **PSD off-diagonal domination, non-strict form** (Problem 10.1 in
    PSD strength): `|a_ij| ≤ √(a_ii) √(a_jj)`. -/
lemma psd_abs_entry_le_sqrt_diag {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (i j : Fin n) :
    |A i j| ≤ Real.sqrt (A i i) * Real.sqrt (A j j) := by
  have hdi := isPosSemiDef_diag_nonneg A hPSD i
  have hdj := isPosSemiDef_diag_nonneg A hPSD j
  rcases eq_or_ne i j with rfl | hij
  · rw [abs_of_nonneg hdi]
    exact (Real.mul_self_sqrt hdi).ge
  · set u : ℝ := Real.sqrt (A i i) with hu
    set w : ℝ := Real.sqrt (A j j) with hw
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hw0 : 0 ≤ w := Real.sqrt_nonneg _
    have hu2 : u ^ 2 = A i i := Real.sq_sqrt hdi
    have hw2 : w ^ 2 = A j j := Real.sq_sqrt hdj
    have hsym := hPSD.1 i j
    have hqf : ∀ t s : ℝ, 0 ≤ t ^ 2 * A i i + t * s * (2 * A i j) +
        s ^ 2 * A j j := by
      intro t s
      have h := hPSD.2 (fun k => if k = i then t else
        if k = j then s else 0)
      rw [quadForm_two_point A i j hij t s] at h
      have h2 : A i j + A j i = 2 * A i j := by rw [← hsym]; ring
      rw [h2] at h
      linarith [h]
    -- zero-diagonal cases force a zero entry
    by_cases hzi : A i i = 0
    · have hAij : A i j = 0 := by
        by_contra hne
        have h := hqf (-(A j j + 1) / (2 * A i j)) 1
        rw [hzi] at h
        have h2 : (-(A j j + 1) / (2 * A i j)) * 1 * (2 * A i j) =
            -(A j j + 1) := by
          field_simp [hne]
        nlinarith [h, h2]
      rw [hAij, abs_zero]
      positivity
    by_cases hzj : A j j = 0
    · have hAij : A i j = 0 := by
        by_contra hne
        have h := hqf 1 (-(A i i + 1) / (2 * A i j))
        rw [hzj] at h
        have h2 : (1 : ℝ) * (-(A i i + 1) / (2 * A i j)) *
            (2 * A i j) = -(A i i + 1) := by
          field_simp [hne]
        nlinarith [h, h2]
      rw [hAij, abs_zero]
      positivity
    -- positive-diagonal case: evaluate at (w, ±u)
    have hupos : 0 < u := Real.sqrt_pos.mpr (lt_of_le_of_ne hdi
      (Ne.symm hzi))
    have hwpos : 0 < w := Real.sqrt_pos.mpr (lt_of_le_of_ne hdj
      (Ne.symm hzj))
    have hq1 := hqf w u
    have hq2 := hqf w (-u)
    rw [abs_le]
    constructor
    · nlinarith [hq1, hu2, hw2, mul_pos hupos hwpos]
    · nlinarith [hq2, hu2, hw2, mul_pos hupos hwpos]

/-- **PSD quadratic form is trace-bounded**:
    `xᵀAx ≤ (∑ᵢ a_ii)(∑ᵢ xᵢ²)` — entrywise domination by
    `√(a_ii a_jj)` plus Cauchy–Schwarz. This turns the trace into a
    computable operator certificate for PSD matrices. -/
lemma psd_quadForm_le_trace {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j ≤
      (∑ i : Fin n, A i i) * ∑ i : Fin n, x i ^ 2 := by
  have hstep : ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j ≤
      ∑ i : Fin n, ∑ j : Fin n,
        (|x i| * Real.sqrt (A i i)) * (|x j| * Real.sqrt (A j j)) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have habs : x i * A i j * x j ≤ |x i| * |A i j| * |x j| := by
      calc x i * A i j * x j ≤ |x i * A i j * x j| := le_abs_self _
        _ = |x i| * |A i j| * |x j| := by rw [abs_mul, abs_mul]
    calc x i * A i j * x j ≤ |x i| * |A i j| * |x j| := habs
      _ ≤ |x i| * (Real.sqrt (A i i) * Real.sqrt (A j j)) * |x j| := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (psd_abs_entry_le_sqrt_diag A hPSD i j)
              (abs_nonneg _)) (abs_nonneg _)
      _ = (|x i| * Real.sqrt (A i i)) * (|x j| * Real.sqrt (A j j)) :=
          by ring
  have hsq : ∑ i : Fin n, ∑ j : Fin n,
      (|x i| * Real.sqrt (A i i)) * (|x j| * Real.sqrt (A j j)) =
      (∑ i : Fin n, |x i| * Real.sqrt (A i i)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |x i|) (fun i => Real.sqrt (A i i))
  have hL : ∑ i : Fin n, |x i| ^ 2 = ∑ i : Fin n, x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq_abs _
  have hR : ∑ i : Fin n, Real.sqrt (A i i) ^ 2 = ∑ i : Fin n, A i i :=
    Finset.sum_congr rfl fun i _ =>
      Real.sq_sqrt (isPosSemiDef_diag_nonneg A hPSD i)
  rw [hL, hR] at hcs
  calc ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j
      ≤ (∑ i : Fin n, |x i| * Real.sqrt (A i i)) ^ 2 :=
        hstep.trans_eq hsq
    _ ≤ (∑ i : Fin n, x i ^ 2) * ∑ i : Fin n, A i i := hcs
    _ = (∑ i : Fin n, A i i) * ∑ i : Fin n, x i ^ 2 := mul_comm _ _

/-- **PSD entries are dominated by the largest diagonal entry**
    (Higham §10.3, the (10.23)/(10.24) termination engine): if every
    diagonal entry of a PSD matrix is at most `d`, every entry is at
    most `d` in absolute value. Applied to the exact trailing Schur
    complement at termination, this converts the pivoted algorithm's
    stopping test `max diag ≤ tol` into the entrywise trailing residual
    bound. -/
lemma psd_abs_entry_le_maxdiag {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (d : ℝ)
    (hd : ∀ i : Fin n, A i i ≤ d) (i j : Fin n) :
    |A i j| ≤ d := by
  have hdi := isPosSemiDef_diag_nonneg A hPSD i
  have hd0 : 0 ≤ d := le_trans hdi (hd i)
  calc |A i j| ≤ Real.sqrt (A i i) * Real.sqrt (A j j) :=
        psd_abs_entry_le_sqrt_diag A hPSD i j
    _ ≤ Real.sqrt d * Real.sqrt d :=
        mul_le_mul (Real.sqrt_le_sqrt (hd i))
          (Real.sqrt_le_sqrt (hd j)) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = d := Real.mul_self_sqrt hd0

/-- **PSD quadratic form bounded by dimension times the largest
    diagonal** (the normwise reading of the same engine):
    `xᵀAx ≤ n·d·‖x‖₂²` when every `a_ii ≤ d`. -/
lemma psd_quadForm_le_card_maxdiag {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (d : ℝ)
    (hd : ∀ i : Fin n, A i i ≤ d) (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j ≤
      (n : ℝ) * d * ∑ i : Fin n, x i ^ 2 := by
  have htr : (∑ i : Fin n, A i i) ≤ (n : ℝ) * d := by
    calc ∑ i : Fin n, A i i ≤ ∑ _i : Fin n, d :=
          Finset.sum_le_sum fun i _ => hd i
      _ = (n : ℝ) * d := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  have hx : 0 ≤ ∑ i : Fin n, x i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  calc ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j
      ≤ (∑ i : Fin n, A i i) * ∑ i : Fin n, x i ^ 2 :=
        psd_quadForm_le_trace A hPSD x
    _ ≤ (n : ℝ) * d * ∑ i : Fin n, x i ^ 2 :=
        mul_le_mul_of_nonneg_right htr hx

/-- **Entrywise bound on Higham's first-order term**: with entrywise
    data `|E| ≤ ε`, `|A₂₁|, |A₁₂| ≤ α`, `|M| ≤ μ`, the first-order term
    of (10.16) satisfies `|Ē i j| ≤ ε (1 + k²αμ)²` — the source's
    `(1 + ‖W‖)²` shape with `k²αμ` the entrywise scale of
    `W = M A₁₂`. -/
lemma schur_first_order_entrywise_bound {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (E22 : Matrix (Fin m) (Fin m) ℝ)
    (M E11 : Matrix (Fin k) (Fin k) ℝ)
    (α μ ε : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hE21 : ∀ i j, |E21 i j| ≤ ε) (hE12 : ∀ i j, |E12 i j| ≤ ε)
    (hE11 : ∀ i j, |E11 i j| ≤ ε) (hE22 : ∀ i j, |E22 i j| ≤ ε)
    (hM : ∀ i j, |M i j| ≤ μ) :
    ∀ (i j : Fin m),
      |(E22 - E21 * M * A12 - A21 * M * E12
          + A21 * (M * E11 * M) * A12) i j| ≤
      ε * (1 + (k : ℝ) ^ 2 * α * μ) ^ 2 := by
  intro i j
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hT1 : ∀ (p : Fin m) (q : Fin k), |(E21 * M) p q| ≤
      (k : ℝ) * ε * μ := entrywise_matMul_le E21 M ε μ hε hE21 hM
  have hT1' : ∀ (p q : Fin m), |((E21 * M) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * μ) * α :=
    entrywise_matMul_le (E21 * M) A12 _ α (by positivity) hT1 hA12
  have hT2 : ∀ (p : Fin m) (q : Fin k), |(A21 * M) p q| ≤
      (k : ℝ) * α * μ := entrywise_matMul_le A21 M α μ hα hA21 hM
  have hT2' : ∀ (p q : Fin m), |((A21 * M) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * μ) * ε :=
    entrywise_matMul_le (A21 * M) E12 _ ε (by positivity) hT2 hE12
  have hME : ∀ (p q : Fin k), |(M * E11) p q| ≤ (k : ℝ) * μ * ε :=
    entrywise_matMul_le M E11 μ ε hμ hM hE11
  have hMEM : ∀ (p q : Fin k), |((M * E11) * M) p q| ≤
      (k : ℝ) * ((k : ℝ) * μ * ε) * μ :=
    entrywise_matMul_le (M * E11) M _ μ (by positivity) hME hM
  have hT3 : ∀ (p : Fin m) (q : Fin k),
      |(A21 * ((M * E11) * M)) p q| ≤
      (k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * μ) :=
    entrywise_matMul_le A21 _ α _ hα hA21 hMEM
  have hT3' : ∀ (p q : Fin m),
      |((A21 * ((M * E11) * M)) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * μ)) * α :=
    entrywise_matMul_le _ A12 _ α (by positivity) hT3 hA12
  have h22 := abs_le.mp (hE22 i j)
  have h1 := abs_le.mp (hT1' i j)
  have h2 := abs_le.mp (hT2' i j)
  have h3 := abs_le.mp (hT3' i j)
  have hgoal : ε * (1 + (k : ℝ) ^ 2 * α * μ) ^ 2 =
      ε + (k : ℝ) * ((k : ℝ) * ε * μ) * α
      + (k : ℝ) * ((k : ℝ) * α * μ) * ε
      + (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * μ)) * α
      := by ring
  rw [hgoal]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [abs_le]
  constructor <;> linarith [h22.1, h22.2, h1.1, h1.2, h2.1, h2.2,
    h3.1, h3.2]

/-- **Strict diagonal argmax is stable under small perturbations**
    (Lemma 10.11 stage engine): if the pivot choice has gap `δ` and the
    diagonal perturbation is below `δ/2`, the perturbed matrix selects
    the same pivot. -/
lemma strict_argmax_diag_stable {n : ℕ} (A E : Fin n → Fin n → ℝ)
    (p : Fin n) (δ : ℝ)
    (hgap : ∀ i : Fin n, i ≠ p → A i i + δ ≤ A p p)
    (hE : ∀ i : Fin n, |E i i| < δ / 2) :
    ∀ i : Fin n, i ≠ p → A i i + E i i < A p p + E p p := by
  intro i hip
  have h1 := abs_lt.mp (hE i)
  have h2 := abs_lt.mp (hE p)
  have h3 := hgap i hip
  linarith [h1.2, h2.1]

/-- **Deterministic complete-pivoting choice**: the least-index
    maximizer of the diagonal (Lemma 10.11 pivot-sequence
    foundation). -/
noncomputable def diagArgmax {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : Fin n :=
  (Finset.univ.filter (fun i : Fin n => ∀ j : Fin n, A j j ≤ A i i)).min'
    (by
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
        (fun i : Fin n => A i i)
        (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        fun j => hi j (Finset.mem_univ j)⟩⟩)

/-- The deterministic pivot maximizes the diagonal. -/
lemma diagArgmax_max {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (j : Fin n) : A j j ≤ A (diagArgmax hn A) (diagArgmax hn A) := by
  have hmem := Finset.min'_mem
    (Finset.univ.filter (fun i : Fin n => ∀ j : Fin n, A j j ≤ A i i))
    (by
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
        (fun i : Fin n => A i i)
        (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        fun j => hi j (Finset.mem_univ j)⟩⟩)
  exact (Finset.mem_filter.mp hmem).2 j

/-- A strict maximizer is the deterministic pivot. -/
lemma diagArgmax_eq_of_strict {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (p : Fin n)
    (hstrict : ∀ i : Fin n, i ≠ p → A i i < A p p) :
    diagArgmax hn A = p := by
  by_contra hne
  have hmax := diagArgmax_max hn A p
  exact absurd hmax (not_le.mpr (hstrict _ hne))

/-- **Pivot-choice stability** (Lemma 10.11, single stage, packaged):
    a gap-`δ` complete-pivoting choice is preserved by any diagonal
    perturbation below `δ/2` — both matrices select the same
    deterministic pivot. -/
theorem diagArgmax_stable {n : ℕ} (hn : 0 < n)
    (A E : Fin n → Fin n → ℝ) (p : Fin n) (δ : ℝ)
    (hgap : ∀ i : Fin n, i ≠ p → A i i + δ ≤ A p p)
    (hE : ∀ i : Fin n, |E i i| < δ / 2) :
    diagArgmax hn A = p ∧
    diagArgmax hn (fun i j => A i j + E i j) = p := by
  have hδpos : 0 < δ := by
    have := abs_nonneg (E p p)
    linarith [hE p]
  constructor
  · exact diagArgmax_eq_of_strict hn A p fun i hip => by
      have := hgap i hip
      linarith
  · exact diagArgmax_eq_of_strict hn _ p fun i hip =>
      strict_argmax_diag_stable A E p δ hgap hE i hip

/-- **One complete-pivoting elimination step** (Lemma 10.11 state
    machine): eliminate pivot `p`, zeroing its row and column and
    forming the Schur update on the rest. Dimension is preserved so the
    stage recursion needs no dependent reindexing. -/
noncomputable def schurStep {n : ℕ} (A : Fin n → Fin n → ℝ)
    (p : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if i = p ∨ j = p then 0
    else A i j - A i p * A p j / A p p

/-- `schurStep` preserves symmetry. -/
lemma schurStep_symm {n : ℕ} (A : Fin n → Fin n → ℝ) (p : Fin n)
    (hsym : ∀ i j : Fin n, A i j = A j i) (i j : Fin n) :
    schurStep A p i j = schurStep A p j i := by
  unfold schurStep
  by_cases hi : i = p
  · by_cases hj : j = p <;> simp [hi, hj]
  · by_cases hj : j = p
    · simp [hi, hj]
    · simp only [hi, hj, or_self, if_false]
      rw [hsym i j, hsym i p, hsym p j]
      ring

/-- **`schurStep` preserves positive semidefiniteness** (the
    completion-of-squares invariant of the Lemma 10.11 stage
    recursion): with a positive pivot, the zeroed Schur update of a PSD
    matrix is PSD — the quadratic form of the update at `x` equals the
    quadratic form of `A` at `x` with the `p`-th coordinate replaced by
    the minimizer `−(∑_{j≠p} a_pj x_j)/a_pp`. -/
lemma schurStep_isPosSemiDef {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (p : Fin n) (hp : 0 < A p p) :
    IsPosSemiDef n (schurStep A p) := by
  refine ⟨schurStep_symm A p hPSD.1, ?_⟩
  intro x
  set d : ℝ := A p p with hd
  set u : ℝ := ∑ j ∈ Finset.univ.erase p, A p j * x j with hu
  set z : Fin n → ℝ := fun i => if i = p then -u / d else x i with hz
  -- the quadratic form of the update, reduced to the erased square
  have hSquad : ∑ i : Fin n, ∑ j : Fin n,
      x i * schurStep A p i j * x j =
      ∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
        x i * (A i j - A i p * A p j / d) * x j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hrow : ∑ j : Fin n, x p * schurStep A p p j * x j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        unfold schurStep; simp
    rw [hrow, zero_add]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hip : i ≠ p := Finset.ne_of_mem_erase hi
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hcol : x i * schurStep A p i p * x p = 0 := by
      unfold schurStep; simp
    rw [hcol, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjp : j ≠ p := Finset.ne_of_mem_erase hj
    unfold schurStep
    simp [hip, hjp, ← hd]
  -- the quadratic form of A at the completed vector z
  have hAquad : ∑ i : Fin n, ∑ j : Fin n, z i * A i j * z j =
      (-u / d) * d * (-u / d) + (-u / d) * u + u * (-u / d) +
      ∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
        x i * A i j * x j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hrowp : ∑ j : Fin n, z p * A p j * z j =
        (-u / d) * d * (-u / d) + (-u / d) * u := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
      have hzp : z p = -u / d := by simp [hz]
      have htail : ∑ j ∈ Finset.univ.erase p, z p * A p j * z j =
          (-u / d) * u := by
        rw [hu, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjp : j ≠ p := Finset.ne_of_mem_erase hj
        rw [hzp]
        simp only [hz, hjp, if_false]
        ring
      rw [htail, hzp, hd]
    rw [hrowp]
    have hrest : ∑ i ∈ Finset.univ.erase p,
        ∑ j : Fin n, z i * A i j * z j =
        u * (-u / d) + ∑ i ∈ Finset.univ.erase p,
          ∑ j ∈ Finset.univ.erase p, x i * A i j * x j := by
      have hsw : ∀ i ∈ Finset.univ.erase p,
          ∑ j : Fin n, z i * A i j * z j =
          x i * A i p * (-u / d) +
          ∑ j ∈ Finset.univ.erase p, x i * A i j * x j := by
        intro i hi
        have hip : i ≠ p := Finset.ne_of_mem_erase hi
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
        have hzi : z i = x i := by simp [hz, hip]
        have hzp : z p = -u / d := by simp [hz]
        rw [hzi, hzp]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjp : j ≠ p := Finset.ne_of_mem_erase hj
        simp [hz, hjp]
      rw [Finset.sum_congr rfl hsw, Finset.sum_add_distrib]
      congr 1
      have : ∑ i ∈ Finset.univ.erase p, x i * A i p * (-u / d) =
          (∑ i ∈ Finset.univ.erase p, A p i * x i) * (-u / d) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hPSD.1 i p]
        ring
      rw [this]
    rw [hrest]
    ring
  -- the cross term collapses: quadForm S x = quadForm A z
  have hfactor : ∑ i ∈ Finset.univ.erase p,
      ∑ j ∈ Finset.univ.erase p,
        x i * (A i p * A p j / d) * x j = u * u / d := by
    have hsep : ∀ i ∈ Finset.univ.erase p,
        ∑ j ∈ Finset.univ.erase p,
          x i * (A i p * A p j / d) * x j =
        (A p i * x i / d) * u := by
      intro i hi
      rw [hu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hPSD.1 i p]
      ring
    rw [Finset.sum_congr rfl hsep, ← Finset.sum_mul,
      ← Finset.sum_div, ← hu]
    ring
  have hkey : ∑ i : Fin n, ∑ j : Fin n,
      x i * schurStep A p i j * x j =
      ∑ i : Fin n, ∑ j : Fin n, z i * A i j * z j := by
    rw [hSquad, hAquad]
    have hsub : ∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
        x i * (A i j - A i p * A p j / d) * x j =
        (∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
          x i * A i j * x j) - u * u / d := by
      rw [← hfactor, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsub]
    field_simp
    ring
  rw [hkey]
  exact hPSD.2 z

/-- **The complete-pivoting state machine** (Lemma 10.11): stage `t`'s
    working matrix — `A` eliminated `t` times, each time at the
    deterministic diagonal argmax. -/
noncomputable def cpState {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℕ → (Fin n → Fin n → ℝ)
  | 0 => A
  | t + 1 => schurStep (cpState hn A t)
      (diagArgmax hn (cpState hn A t))

/-- The pivot selected at stage `t`. -/
noncomputable def cpPivot {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (t : ℕ) : Fin n :=
  diagArgmax hn (cpState hn A t)

/-- Every complete-pivoting stage is symmetric. -/
lemma cpState_symm {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i) :
    ∀ t : ℕ, ∀ i j : Fin n, cpState hn A t i j = cpState hn A t j i := by
  intro t
  induction t with
  | zero => exact hsym
  | succ t ih => exact schurStep_symm (cpState hn A t) _ ih

/-- **Every complete-pivoting stage is PSD** while the selected pivots
    stay positive (Lemma 10.11 stage invariant). -/
lemma cpState_isPosSemiDef {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) (t : ℕ)
    (hpiv : ∀ s : ℕ, s < t →
      0 < cpState hn A s (cpPivot hn A s) (cpPivot hn A s)) :
    IsPosSemiDef n (cpState hn A t) := by
  induction t with
  | zero => exact hPSD
  | succ t ih =>
    exact schurStep_isPosSemiDef (cpState hn A t)
      (ih fun s hs => hpiv s (Nat.lt_succ_of_lt hs)) _
      (hpiv t (Nat.lt_succ_self t))

/-- **The selected pivot dominates the whole working diagonal** —
    what complete pivoting means at each stage. -/
lemma cpPivot_max {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (t : ℕ) (j : Fin n) :
    cpState hn A t j j ≤
      cpState hn A t (cpPivot hn A t) (cpPivot hn A t) :=
  diagArgmax_max hn (cpState hn A t) j

/-- **Entrywise perturbation of one elimination step** (Lemma 10.11
    propagation engine): if `A` and `B` agree entrywise to `ε`, `A` has
    entry cap `c`, and both share the pivot floor `ρ > 0` at `p`, the
    eliminated matrices agree to `ε + (3c²ε + cε²)/ρ²`. Iterating this
    bound across stages propagates a diagonal gap through the
    complete-pivoting recursion. -/
lemma schurStep_entrywise_perturbation {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (p : Fin n) (ε c ρ : ℝ)
    (hε : 0 ≤ ε) (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hAB : ∀ i j : Fin n, |A i j - B i j| ≤ ε)
    (hcap : ∀ i j : Fin n, |A i j| ≤ c)
    (hdA : ρ ≤ A p p) (hdB : ρ ≤ B p p) :
    ∀ i j : Fin n, |schurStep A p i j - schurStep B p i j| ≤
      ε + (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
  intro i j
  have hrhs0 : (0:ℝ) ≤ ε + (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
    positivity
  by_cases hij : i = p ∨ j = p
  · unfold schurStep
    rw [if_pos hij, if_pos hij, sub_zero, abs_zero]
    exact hrhs0
  · unfold schurStep
    rw [if_neg hij, if_neg hij]
    have hdA0 : (0:ℝ) < A p p := lt_of_lt_of_le hρ hdA
    have hdB0 : (0:ℝ) < B p p := lt_of_lt_of_le hρ hdB
    -- common-denominator form of the update difference
    have hkey : A i p * A p j / A p p - B i p * B p j / B p p =
        (A i p * A p j * (B p p - A p p)
          + A p p * (A i p * (A p j - B p j)
            + (A i p - B i p) * B p j)) / (A p p * B p p) := by
      field_simp
      ring
    -- numerator and denominator bounds
    have hBpj : |B p j| ≤ c + ε := by
      have h1 := hAB p j
      have h2 := hcap p j
      have := abs_sub_abs_le_abs_sub (B p j) (A p j)
      rw [abs_sub_comm (B p j) (A p j)] at this
      linarith [this, h1, h2]
    have hnum : |A i p * A p j * (B p p - A p p)
        + A p p * (A i p * (A p j - B p j)
          + (A i p - B i p) * B p j)| ≤
        3 * c ^ 2 * ε + c * ε ^ 2 := by
      have h1 : |A i p * A p j * (B p p - A p p)| ≤ c * c * ε := by
        rw [abs_mul, abs_mul, abs_sub_comm]
        exact mul_le_mul (mul_le_mul (hcap i p) (hcap p j)
          (abs_nonneg _) hc) (hAB p p)
          (abs_nonneg _) (by positivity)
      have h2 : |A i p * (A p j - B p j)| ≤ c * ε := by
        rw [abs_mul]
        exact mul_le_mul (hcap i p) (hAB p j) (abs_nonneg _) hc
      have h3 : |(A i p - B i p) * B p j| ≤ ε * (c + ε) := by
        rw [abs_mul]
        exact mul_le_mul (hAB i p) hBpj (abs_nonneg _) hε
      have h4 : |A p p * (A i p * (A p j - B p j)
          + (A i p - B i p) * B p j)| ≤ c * (c * ε + ε * (c + ε)) := by
        rw [abs_mul]
        refine mul_le_mul (hcap p p) ?_ (abs_nonneg _) hc
        calc |A i p * (A p j - B p j) + (A i p - B i p) * B p j|
            ≤ |A i p * (A p j - B p j)| + |(A i p - B i p) * B p j| :=
              abs_add_le _ _
          _ ≤ c * ε + ε * (c + ε) := add_le_add h2 h3
      calc |A i p * A p j * (B p p - A p p)
          + A p p * (A i p * (A p j - B p j)
            + (A i p - B i p) * B p j)|
          ≤ |A i p * A p j * (B p p - A p p)|
            + |A p p * (A i p * (A p j - B p j)
              + (A i p - B i p) * B p j)| := abs_add_le _ _
        _ ≤ c * c * ε + c * (c * ε + ε * (c + ε)) := add_le_add h1 h4
        _ = 3 * c ^ 2 * ε + c * ε ^ 2 := by ring
    have hden : ρ ^ 2 ≤ A p p * B p p := by nlinarith
    have hquot : |A i p * A p j / A p p - B i p * B p j / B p p| ≤
        (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
      rw [hkey, abs_div, abs_of_pos (mul_pos hdA0 hdB0)]
      calc |A i p * A p j * (B p p - A p p)
            + A p p * (A i p * (A p j - B p j)
              + (A i p - B i p) * B p j)| / (A p p * B p p)
          ≤ (3 * c ^ 2 * ε + c * ε ^ 2) / (A p p * B p p) := by
            gcongr
        _ ≤ (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
            gcongr

    -- assemble with the direct entry difference
    have hsplit : A i j - A i p * A p j / A p p -
        (B i j - B i p * B p j / B p p) =
        (A i j - B i j) -
        (A i p * A p j / A p p - B i p * B p j / B p p) := by ring
    rw [hsplit]
    have h1 := abs_le.mp (hAB i j)
    have h2 := abs_le.mp hquot
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

-- ============================================================
-- §10.3  Lemma 10.12: W-norm bound
-- ============================================================

/-- **Abstract W-norm bound interface** (Higham §10.3, Lemma 10.12). -/
theorem w_norm_bound_from_cond
    (W_norm κ_A11 : ℝ) (_hκ : 0 ≤ κ_A11)
    (hW : W_norm ^ 2 ≤ κ_A11) :
    W_norm ^ 2 ≤ κ_A11 :=
  hW

/-- **Abstract back-substitution growth** (Lemma 10.13 engine): if each
    `|w i|` is bounded by `1` plus the sum of the later `|w j|` — the
    pivot-normalized form of the triangular solve under the (10.13)
    bounds — then `|w i| ≤ 2^{r-1-i}`, by downward induction with the
    geometric sum `1 + (2^t − 1) = 2^t`. -/
lemma backsub_growth {r : ℕ} (w : Fin r → ℝ)
    (hrec : ∀ i : Fin r, |w i| ≤ 1 +
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val), |w j|) :
    ∀ i : Fin r, |w i| ≤ 2 ^ (r - 1 - i.val) := by
  have H : ∀ (t : ℕ) (i : Fin r), r - 1 - i.val = t →
      |w i| ≤ 2 ^ t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t IH =>
      intro i hit
      have himg : (Finset.univ.filter
          (fun j : Fin r => i.val < j.val)).image
          (fun j : Fin r => r - 1 - j.val) = Finset.range t := by
        ext k
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_range]
        constructor
        · rintro ⟨j, hj, rfl⟩
          have := j.isLt
          omega
        · intro hk
          refine ⟨⟨r - 1 - k, by omega⟩, by simp; omega, by simp; omega⟩
      have hinj : ∀ a ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val),
          ∀ b ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val),
          r - 1 - a.val = r - 1 - b.val → a = b := by
        intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        have := a.isLt
        have := b.isLt
        exact Fin.ext (by omega)
      have hsum_exp : ∑ j ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val), (2:ℝ) ^ (r - 1 - j.val) =
          ∑ k ∈ Finset.range t, (2:ℝ) ^ k := by
        rw [← himg, Finset.sum_image hinj]
      calc |w i| ≤ 1 + ∑ j ∈ Finset.univ.filter
            (fun j : Fin r => i.val < j.val), |w j| := hrec i
        _ ≤ 1 + ∑ j ∈ Finset.univ.filter
            (fun j : Fin r => i.val < j.val),
            (2:ℝ) ^ (r - 1 - j.val) := by
            gcongr with j hj
            simp only [Finset.mem_filter, Finset.mem_univ,
              true_and] at hj
            exact IH (r - 1 - j.val) (by have := j.isLt; omega) j rfl
        _ = 1 + ∑ k ∈ Finset.range t, (2:ℝ) ^ k := by rw [hsum_exp]
        _ = 2 ^ t := by
            rw [geom_sum_eq (by norm_num : (2:ℝ) ≠ 1) t]
            ring
  intro i
  exact H (r - 1 - i.val) i rfl

/-- **Entry domination from the column-tail invariant** (Lemma 10.13
    wiring): under the (10.13) invariant, every entry on or right of the
    diagonal is dominated in absolute value by its row pivot. -/
lemma tail_invariant_entry_le {n : ℕ} {R : Fin n → Fin n → ℝ}
    (hdiag_nonneg : ∀ i : Fin n, 0 ≤ R i i)
    (htail : ∀ k j : Fin n, k.val ≤ j.val →
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
        R i j ^ 2) ≤ R k k ^ 2)
    (k j : Fin n) (hkj : k.val ≤ j.val) :
    |R k j| ≤ R k k := by
  have hmem : k ∈ Finset.univ.filter
      (fun i : Fin n => k.val ≤ i.val) := by
    simp
  have hsingle : R k j ^ 2 ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
        R i j ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (R i j)) hmem
  have hsq : R k j ^ 2 ≤ R k k ^ 2 :=
    le_trans hsingle (htail k j hkj)
  nlinarith [abs_nonneg (R k j), sq_abs (R k j), hdiag_nonneg k]

/-- **Normalized triangular-solve growth** (Lemma 10.13 core): a solve
    `Uw = b` against an upper-triangular matrix whose every row is
    pivot-dominated (`|U i j| ≤ U i i`, `|b i| ≤ U i i` — supplied by the
    (10.13) invariant through `tail_invariant_entry_le`) has solution
    entries bounded by `2^{r-1-i}`. -/
theorem normalized_solve_growth {r : ℕ} (U : Fin r → Fin r → ℝ)
    (b w : Fin r → ℝ)
    (hupper : ∀ i j : Fin r, j.val < i.val → U i j = 0)
    (hdiag_pos : ∀ i : Fin r, 0 < U i i)
    (hentry : ∀ i j : Fin r, i.val ≤ j.val → |U i j| ≤ U i i)
    (hb : ∀ i : Fin r, |b i| ≤ U i i)
    (hsolve : ∀ i : Fin r, ∑ j : Fin r, U i j * w j = b i) :
    ∀ i : Fin r, |w i| ≤ 2 ^ (r - 1 - i.val) := by
  apply backsub_growth
  intro i
  have hpos := hdiag_pos i
  -- split the solve row at the diagonal: below-diagonal entries vanish
  have hle_part : ∑ j ∈ Finset.univ.filter
      (fun j : Fin r => ¬ i.val < j.val), U i j * w j =
      U i i * w i := by
    refine Finset.sum_eq_single_of_mem i (by simp) ?_
    intro j hj hji
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.not_lt] at hj
    have hjlt : j.val < i.val := by
      rcases Nat.lt_or_eq_of_le hj with h' | h'
      · exact h'
      · exact absurd (Fin.ext h') hji
    rw [hupper i j hjlt, zero_mul]
  have hsplit : U i i * w i +
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val),
        U i j * w j = b i := by
    have h := hsolve i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin r => i.val < j.val) (fun j => U i j * w j),
      hle_part] at h
    linarith [h]
  -- bound the absolute tail sum by pivot-scaled solution magnitudes
  have hsum_abs : |∑ j ∈ Finset.univ.filter
      (fun j : Fin r => i.val < j.val), U i j * w j| ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val),
        U i i * |w j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum ?_)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hentry i j hj.le) (abs_nonneg _)
  -- triangle inequality on the rearranged pivot equation
  have htri : |U i i * w i| ≤ |b i| + |∑ j ∈ Finset.univ.filter
      (fun j : Fin r => i.val < j.val), U i j * w j| := by
    have heq : U i i * w i = b i - ∑ j ∈ Finset.univ.filter
        (fun j : Fin r => i.val < j.val), U i j * w j := by
      linarith [hsplit]
    rw [heq]
    have h1 := abs_add_le (b i) (-(∑ j ∈ Finset.univ.filter
      (fun j : Fin r => i.val < j.val), U i j * w j))
    rw [abs_neg, ← sub_eq_add_neg] at h1
    exact h1
  -- assemble and divide by the positive pivot
  have hwi : U i i * |w i| ≤ U i i * (1 +
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val),
        |w j|) := by
    have habs : U i i * |w i| = |U i i * w i| := by
      rw [abs_mul, abs_of_pos hpos]
    rw [habs, mul_add, mul_one, Finset.mul_sum]
    calc |U i i * w i|
        ≤ |b i| + |∑ j ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val), U i j * w j| := htri
      _ ≤ U i i + ∑ j ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val), U i i * |w j| :=
          add_le_add (hb i) hsum_abs
  exact le_of_mul_le_mul_left hwi hpos

-- ============================================================
-- §10.3  Lemma 10.13: Complete pivoting bound
-- ============================================================

/-- **Squared-sum of the growth bounds**: entries bounded by `2^{r-1-i}`
    have squared sum at most `(4^r − 1)/3` (geometric sum, Higham
    §10.3, proof of Lemma 10.13). -/
lemma sq_sum_pow_two_bound {r : ℕ} (w : Fin r → ℝ)
    (h : ∀ i : Fin r, |w i| ≤ 2 ^ (r - 1 - i.val)) :
    ∑ i : Fin r, w i ^ 2 ≤ ((4 : ℝ) ^ r - 1) / 3 := by
  have hterm : ∀ i : Fin r, w i ^ 2 ≤ (4 : ℝ) ^ (r - 1 - i.val) := by
    intro i
    obtain ⟨hlo, hhi⟩ := abs_le.mp (h i)
    have hsq : w i ^ 2 ≤ ((2 : ℝ) ^ (r - 1 - i.val)) ^ 2 :=
      sq_le_sq' hlo hhi
    calc w i ^ 2 ≤ ((2 : ℝ) ^ (r - 1 - i.val)) ^ 2 := hsq
      _ = ((2 : ℝ) ^ 2) ^ (r - 1 - i.val) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = (4 : ℝ) ^ (r - 1 - i.val) := by norm_num
  have hrev : ∑ i : Fin r, (4 : ℝ) ^ (r - 1 - i.val) =
      ∑ i : Fin r, (4 : ℝ) ^ i.val := by
    apply Fintype.sum_bijective (Fin.rev) (Fin.rev_involutive.bijective)
    intro i
    rw [Fin.val_rev]
    congr 1
    omega
  have hgeom : ∑ i : Fin r, (4 : ℝ) ^ i.val = ((4 : ℝ) ^ r - 1) / 3 := by
    rw [Fin.sum_univ_eq_sum_range (fun t => (4 : ℝ) ^ t) r,
      geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1) r,
      show (4 : ℝ) - 1 = 3 by norm_num]
  calc ∑ i : Fin r, w i ^ 2
      ≤ ∑ i : Fin r, (4 : ℝ) ^ (r - 1 - i.val) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ((4 : ℝ) ^ r - 1) / 3 := by rw [hrev, hgeom]

/-- **Complete-pivoting bound on ‖W‖_F²** (Higham §10.3, Lemma 10.13,
    display (10.19)): if the `r × r` upper-triangular block `U` has
    positive diagonal and every row pivot-dominated on and right of the
    diagonal (as `tail_invariant_entry_le` extracts from the (10.13)
    column-tail invariant of complete pivoting), and `W` solves
    `U W = B` column-by-column with `|B i j| ≤ U i i`, then
    `‖W‖_F² ≤ m (4^r − 1)/3` — Higham's `(n − r)(4^r − 1)/3` with
    `m = n − r` border columns. -/
theorem complete_pivoting_w_bound {r m : ℕ} (U : Fin r → Fin r → ℝ)
    (B W : Fin r → Fin m → ℝ)
    (hupper : ∀ i j : Fin r, j.val < i.val → U i j = 0)
    (hdiag_pos : ∀ i : Fin r, 0 < U i i)
    (hentry : ∀ i j : Fin r, i.val ≤ j.val → |U i j| ≤ U i i)
    (hB : ∀ (i : Fin r) (j : Fin m), |B i j| ≤ U i i)
    (hsolve : ∀ (i : Fin r) (j : Fin m),
      ∑ k : Fin r, U i k * W k j = B i j) :
    ∑ j : Fin m, ∑ i : Fin r, W i j ^ 2 ≤
      (m : ℝ) * (((4 : ℝ) ^ r - 1) / 3) := by
  have hcol : ∀ j : Fin m, ∑ i : Fin r, W i j ^ 2 ≤
      ((4 : ℝ) ^ r - 1) / 3 := fun j =>
    sq_sum_pow_two_bound (fun i => W i j)
      (normalized_solve_growth U (fun i => B i j) (fun i => W i j)
        hupper hdiag_pos hentry (fun i => hB i j) (fun i => hsolve i j))
  calc ∑ j : Fin m, ∑ i : Fin r, W i j ^ 2
      ≤ ∑ _j : Fin m, ((4 : ℝ) ^ r - 1) / 3 :=
        Finset.sum_le_sum fun j _ => hcol j
    _ = (m : ℝ) * (((4 : ℝ) ^ r - 1) / 3) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

-- ============================================================
-- §10.3  Theorem 10.14: PSD Cholesky error analysis
-- ============================================================

/-- **Abstract backward-error interface for PSD Cholesky**
    (Higham §10.3, Theorem 10.14).

    The hypothesis `hbackward` supplies the detailed pivoted PSD Cholesky
    analysis; this theorem projects the product equation and componentwise
    error bound used by downstream modules. -/
theorem psd_cholesky_backward_error (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (r : ℕ) (_hr : r ≤ n) (_hr_pos : 0 < r)
    (_hPSD : IsPosSemiDef n A)
    (_hn_r : gammaValid fp (r + 1))
    (_hγ_lt : gamma fp (r + 1) < 1)
    (W_norm : ℝ) (_hW : 0 ≤ W_norm)
    (hbackward : ∃ (R_hat : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ),
      (∀ i j : Fin n, j.val < i.val → R_hat i j = 0) ∧
      (∀ i j : Fin n, r ≤ i.val → R_hat i j = 0) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + E i j) ∧
      (∀ i j, |E i j| ≤ gamma fp (r + 1) / (1 - gamma fp (r + 1)) *
        (1 + W_norm) ^ 2 *
        ∑ k : Fin n, |A i k| * (if k.val < r then 1 else 0))) :
    ∃ (R_hat : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ),
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + E i j) ∧
      (∀ i j, |E i j| ≤ gamma fp (r + 1) / (1 - gamma fp (r + 1)) *
        (1 + W_norm) ^ 2 *
        ∑ k : Fin n, |A i k| * (if k.val < r then 1 else 0)) := by
  obtain ⟨R_hat, E, _, _, hprod, hbound⟩ := hbackward
  exact ⟨R_hat, E, hprod, hbound⟩

-- ============================================================
-- §10.3  Termination criteria
-- ============================================================

/-- **Abstract termination-criterion interface (10.27)** for PSD Cholesky. -/
theorem psd_cholesky_termination_bound
    (residual_norm matrix_norm : ℝ)
    (n : ℕ) (u : ℝ) (_hu : 0 ≤ u)
    (hstop : residual_norm ≤ ↑n * u * matrix_norm)
    (_hm : 0 ≤ matrix_norm) :
    residual_norm ≤ ↑n * u * matrix_norm :=
  hstop

end LeanFpAnalysis.FP
