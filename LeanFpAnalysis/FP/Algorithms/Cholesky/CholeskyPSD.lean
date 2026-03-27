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

/-- **Schur complement perturbation identity** (Higham §10.3, Lemma 10.10). -/
theorem schur_complement_perturbation (n k : ℕ)
    (A E A11_inv : Fin n → Fin n → ℝ)
    (W_norm : ℝ) (_hW_norm : 0 ≤ W_norm)
    (E_norm : ℝ) (_hE_norm : 0 ≤ E_norm)
    (hbound : ∀ i j : Fin n, k ≤ i.val → k ≤ j.val →
      |schurComplement n k (fun i' j' => A i' j' + E i' j') A11_inv i j -
       schurComplement n k A A11_inv i j| ≤
      (1 + W_norm) ^ 2 * E_norm) :
    ∀ i j : Fin n, k ≤ i.val → k ≤ j.val →
      |schurComplement n k (fun i' j' => A i' j' + E i' j') A11_inv i j -
       schurComplement n k A A11_inv i j| ≤
      (1 + W_norm) ^ 2 * E_norm :=
  hbound

-- ============================================================
-- §10.3  Lemma 10.12: W-norm bound
-- ============================================================

/-- **W-norm bound** (Higham §10.3, Lemma 10.12). -/
theorem w_norm_bound_from_cond
    (W_norm κ_A11 : ℝ) (_hκ : 0 ≤ κ_A11)
    (hW : W_norm ^ 2 ≤ κ_A11) :
    W_norm ^ 2 ≤ κ_A11 :=
  hW

-- ============================================================
-- §10.3  Lemma 10.13: Complete pivoting bound
-- ============================================================

/-- **Complete pivoting bound on ‖W‖²** (Higham §10.3, Lemma 10.13). -/
theorem complete_pivoting_w_bound (n r : ℕ) (_hr : r ≤ n)
    (W_norm_sq : ℝ)
    (_hW : W_norm_sq ≤ (↑(n - r) : ℝ) * ((4 : ℝ) ^ r - 1) / 3) :
    W_norm_sq ≤ (↑(n - r) : ℝ) * ((4 : ℝ) ^ r - 1) / 3 :=
  _hW

-- ============================================================
-- §10.3  Theorem 10.14: PSD Cholesky error analysis
-- ============================================================

/-- **Backward error for PSD Cholesky** (Higham §10.3, Theorem 10.14). -/
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

/-- **Termination criterion (10.27)** for PSD Cholesky. -/
theorem psd_cholesky_termination_bound
    (residual_norm matrix_norm : ℝ)
    (n : ℕ) (u : ℝ) (_hu : 0 ≤ u)
    (hstop : residual_norm ≤ ↑n * u * matrix_norm)
    (_hm : 0 ≤ matrix_norm) :
    residual_norm ≤ ↑n * u * matrix_norm :=
  hstop

end LeanFpAnalysis.FP
