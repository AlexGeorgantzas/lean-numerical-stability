import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis

/-!
# CholeskyPSD (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Cholesky.CholeskyPSD`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

namespace NumStability

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

/-- **The computed stopping test certifies the exact trailing Schur
    complement** (displays (10.23)/(10.24) for the algorithm as run):
    under the pivot-agreement hypotheses, if the computed working
    diagonal at stage `r` passes the termination test
    `max_i S̃_ii ≤ tol`, then EVERY entry of the exact stage-`r` Schur
    complement is at most `tol + h r` in absolute value — the
    `η`-reading for the Theorem 10.14 certificate: exact trailing
    smallness from a computed test plus the accumulated budget. -/
theorem fl_cp_termination_trailing_bound (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
            (1 + fp.u)) ≤ h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (tol : ℝ)
    (hterm : ∀ i : Fin n, fl_cpState fp hn A r i i ≤ tol) :
    ∀ i j : Fin n, |cpState hn A r i j| ≤ tol + h r := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  -- the exact stage-r state is PSD
  have hSr : IsPosSemiDef n (cpState hn A r) :=
    cpState_isPosSemiDef hn A hPSD r fun s hs =>
      lt_of_lt_of_le hρ0 (hfloor s hs)
  -- the computed and exact stage-r states are h r-close
  have hagree := fl_cpPivot_sequence_agrees fp hn A r δ ρ c hδ hδρ hc
    h hh0 hhstep hhhalf hgap hfloor hcap r le_rfl
  have hdiff := hagree.1
  -- exact trailing diagonal from the computed test
  have hdiag : ∀ i : Fin n, cpState hn A r i i ≤ tol + h r := by
    intro i
    have h1 := hdiff i i
    have h2 := abs_le.mp h1
    have h3 := hterm i
    linarith [h2.2]
  exact psd_abs_entry_le_maxdiag (cpState hn A r) hSr (tol + h r)
    hdiag

/-- **Computed factor rows are pivot-dominated** (the `c`-discharge for
    Theorem 10.14's domination hypothesis, one stage): if the exact
    working matrix is PSD with maximal pivot and floor `ρ`, and the
    computed working matrix is `ht`-close (`ht ≤ ρ/4`), then every
    computed off-pivot factor entry `fl(S̃_pj / √S̃_pp)` is bounded by
    `(1 + 4ht/ρ)(1+u)/(1−u)²` times the computed pivot entry
    `fl(√S̃_pp)` — the computed form of the (10.13) invariant, with the
    domination constant explicit. -/
theorem fl_factor_row_dominated (fp : FPModel) {n : ℕ}
    (S Stilde : Fin n → Fin n → ℝ) (p : Fin n) (ρ ht : ℝ)
    (hPSD : IsPosSemiDef n S)
    (hmax : ∀ j : Fin n, S j j ≤ S p p)
    (hfloorS : ρ ≤ S p p) (hρ : 0 < ρ)
    (hht : 0 ≤ ht) (hht2 : ht ≤ ρ / 4)
    (hclose : ∀ i j : Fin n, |S i j - Stilde i j| ≤ ht)
    (hu1 : fp.u < 1) :
    ∀ j : Fin n,
      |fp.fl_div (Stilde p j) (fp.fl_sqrt (Stilde p p))| ≤
      (1 + 4 * ht / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
        |fp.fl_sqrt (Stilde p p)| := by
  intro j
  have hu0 := fp.u_nonneg
  have h1u : (0:ℝ) < 1 - fp.u := by linarith
  -- the computed pivot is well above zero
  have hSpp : ρ ≤ S p p := hfloorS
  have hStpp : ρ / 2 ≤ Stilde p p := by
    have h1 := abs_le.mp (hclose p p)
    linarith [h1.2]
  have hStpp0 : (0:ℝ) < Stilde p p := by linarith
  have hsq0 : (0:ℝ) < Real.sqrt (Stilde p p) :=
    Real.sqrt_pos.mpr hStpp0
  obtain ⟨δa, hδa, hsqrt⟩ := fp.model_sqrt (Stilde p p) hStpp0.le
  have ha := abs_le.mp hδa
  have h1a : (0:ℝ) < 1 + δa := by linarith [ha.1]
  have hfs0 : fp.fl_sqrt (Stilde p p) ≠ 0 := by
    rw [hsqrt]; positivity
  obtain ⟨δb, hδb, hdiv⟩ := fp.model_div (Stilde p j)
    (fp.fl_sqrt (Stilde p p)) hfs0
  have hb := abs_le.mp hδb
  -- numerator control through the exact PSD structure
  have hnum : |Stilde p j| ≤ Stilde p p * (1 + 4 * ht / ρ) := by
    have h1 : |Stilde p j| ≤ |S p j| + ht := by
      have h := hclose p j
      have h2 := abs_sub_abs_le_abs_sub (Stilde p j) (S p j)
      rw [abs_sub_comm (Stilde p j) (S p j)] at h2
      linarith
    have h2 : |S p j| ≤ S p p := by
      calc |S p j| ≤ Real.sqrt (S p p) * Real.sqrt (S j j) :=
            psd_abs_entry_le_sqrt_diag S hPSD p j
        _ ≤ Real.sqrt (S p p) * Real.sqrt (S p p) :=
            mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (hmax j)) (Real.sqrt_nonneg _)
        _ = S p p := Real.mul_self_sqrt (by linarith)
    have h3 : S p p ≤ Stilde p p + ht := by
      have h := abs_le.mp (hclose p p)
      linarith [h.1]
    have h4 : Stilde p p + 2 * ht ≤
        Stilde p p * (1 + 4 * ht / ρ) := by
      rw [mul_add, mul_one]
      have : Stilde p p * (4 * ht / ρ) ≥ 2 * ht := by
        rw [ge_iff_le, show Stilde p p * (4 * ht / ρ) =
          Stilde p p * 4 * ht / ρ by ring, le_div_iff₀ hρ]
        nlinarith
      linarith
    linarith
  -- assemble through the model factors
  rw [hdiv, hsqrt]
  rw [abs_mul, abs_div, abs_mul, abs_of_pos hsq0, abs_of_pos h1a]
  have h1b : |1 + δb| ≤ 1 + fp.u := by
    rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
  have hda : (1:ℝ) - fp.u ≤ 1 + δa := by linarith [ha.1]
  have hsqSt : Real.sqrt (Stilde p p) * Real.sqrt (Stilde p p) =
      Stilde p p := Real.mul_self_sqrt hStpp0.le
  -- |S̃ p j| / (√·(1+δa)) · |1+δb| ≤ target
  calc |Stilde p j| / (Real.sqrt (Stilde p p) * (1 + δa)) *
        |1 + δb|
      ≤ (Stilde p p * (1 + 4 * ht / ρ)) /
          (Real.sqrt (Stilde p p) * (1 - fp.u)) * (1 + fp.u) := by
        refine mul_le_mul ?_ h1b (abs_nonneg _) (by positivity)
        refine div_le_div₀ (by positivity) hnum (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hda (Real.sqrt_nonneg _)
    _ = (1 + 4 * ht / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
          (Real.sqrt (Stilde p p) * (1 - fp.u)) := by
        field_simp
        nlinarith [hsqSt]
    _ ≤ (1 + 4 * ht / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
          (Real.sqrt (Stilde p p) * (1 + δa)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hda (Real.sqrt_nonneg _)) ?_
        positivity

/-- **All computed factor rows are pivot-dominated across the run**
    (Theorem 10.14 `c`-discharge, composed): under the no-tie data and
    the rounding budget (bounded by `ρ/4`), at every stage `t < r` of
    the factor-form floating-point run, every computed off-pivot factor
    entry is at most `(1 + 4·h t/ρ)(1+u)/(1−u)²` times the computed
    pivot entry — the computed (10.13) invariant for the whole run,
    with per-stage explicit constants. -/
theorem fl_cpFactor_rows_dominated (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) ≤
        h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hht4 : ∀ t : ℕ, t < r → h t ≤ ρ / 4)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ t : ℕ, t < r → ∀ j : Fin n,
      |fp.fl_div (fl_cpStateFactor fp hn A t (cpPivot hn A t) j)
        (fp.fl_sqrt (fl_cpStateFactor fp hn A t
          (cpPivot hn A t) (cpPivot hn A t)))| ≤
      (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
        |fp.fl_sqrt (fl_cpStateFactor fp hn A t
          (cpPivot hn A t) (cpPivot hn A t))| := by
  intro t htr j
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu1 : fp.u < 1 := by
    unfold gammaValid at h5
    push_cast at h5
    nlinarith [fp.u_nonneg]
  -- stage data from the agreement induction and the exact invariants
  have hagree := fl_cpPivotFactor_sequence_agrees fp hn A r δ ρ c
    hδ hδρ hc h5 h hh0 hhstep hhhalf hgap hfloor hcap t
    (Nat.le_of_lt htr)
  have hclose := hagree.1
  have hSPSD : IsPosSemiDef n (cpState hn A t) :=
    cpState_isPosSemiDef hn A hPSD t fun s hs =>
      lt_of_lt_of_le hρ0 (hfloor s (lt_trans hs htr))
  have hht0 : 0 ≤ h t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · rw [hh0]
    · have h1 := hhhalf t htr
      -- nonnegativity via the budget recurrence from stage t-1
      obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht0.ne'
      have ht'r : t' < r := lt_trans (Nat.lt_succ_self t') htr
      have hstep := hhstep t' ht'r
      have haux : ∀ s : ℕ, s ≤ t' → 0 ≤ h s := by
        intro s
        induction s with
        | zero => intro _; rw [hh0]
        | succ s ihs =>
          intro hsr
          have hs' : s < r := by omega
          have h0 := ihs (by omega)
          have hst := hhstep s hs'
          have h1' : (0:ℝ) ≤
              (3 * c ^ 2 * h s + c * h s ^ 2) / (ρ / 2) ^ 2 := by
            positivity
          have h2' : (0:ℝ) ≤
              fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
              (1 + fp.u) * gamma fp 5 *
                ((c + δ / 2) ^ 2 / (ρ / 2)) := by
            have hγ := gamma_nonneg fp h5
            have hu0 := fp.u_nonneg
            refine add_nonneg (by positivity)
              (mul_nonneg (mul_nonneg (by positivity) hγ)
                (by positivity))
          linarith
      have h0 := haux t' le_rfl
      have h1' : (0:ℝ) ≤
          (3 * c ^ 2 * h t' + c * h t' ^ 2) / (ρ / 2) ^ 2 := by
        positivity
      have h2' : (0:ℝ) ≤
          fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2)) := by
        have hγ := gamma_nonneg fp h5
        have hu0 := fp.u_nonneg
        refine add_nonneg (by positivity)
          (mul_nonneg (mul_nonneg (by positivity) hγ)
            (by positivity))
      linarith
  exact fl_factor_row_dominated fp (cpState hn A t)
    (fl_cpStateFactor fp hn A t) (cpPivot hn A t) ρ (h t)
    hSPSD (cpPivot_max hn A t) (hfloor t htr) hρ0 hht0
    (hht4 t htr) hclose hu1 j

/-- **Theorem 10.14 for the algorithm as run, fully composed**: under
    the exact trace's no-tie data, the rounding budget (capped at
    `ρ/4`), `u ≤ 1/8`, commutative rounded multiplication, and `A` PSD
    symmetric, the computed pivoted factorization satisfies the
    componentwise backward-error bound
    `|∑_{t<r} r̃ᵗᵢr̃ᵗⱼ + S̃ᵣᵢⱼ − aᵢⱼ| ≤ r(u·cS + (2u+u²)·cR²)` with the
    explicit caps `cS = c + δ/2` and
    `cR = 2(1+u)²/(1−u)²·√(c + δ/2)` discharged from the agreement
    machinery — no cap hypotheses remain. -/
theorem higham10_14_as_run_backward_error (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5) (hu8 : fp.u ≤ 1 / 8)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hPSD : IsPosSemiDef n A)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) ≤
        h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hht4 : ∀ t : ℕ, t < r → h t ≤ ρ / 4)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ i j : Fin n,
      |(∑ t ∈ Finset.range r,
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) i *
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) j) +
        fl_cpStateFactor fp hn A r i j - A i j| ≤
      (r : ℝ) * (fp.u * (c + δ / 2) + (2 * fp.u + fp.u ^ 2) *
        (2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
          Real.sqrt (c + δ / 2)) ^ 2) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu0 := fp.u_nonneg
  have hu1 : fp.u < 1 := by linarith
  have h1u : (0:ℝ) < 1 - fp.u := by linarith
  have hcδ : (0:ℝ) ≤ c + δ / 2 := by linarith
  -- stage data shared by all discharges
  have hagree := fl_cpPivotFactor_sequence_agrees fp hn A r δ ρ c
    hδ hδρ hc h5 h hh0 hhstep hhhalf hgap hfloor hcap
  have hstage : ∀ t : ℕ, t < r →
      fl_cpPivotFactor fp hn A t = cpPivot hn A t := by
    intro t htr
    exact ((hagree (t + 1) (Nat.succ_le_of_lt htr)).2 t
      (Nat.lt_succ_self t)).symm
  have hclose : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j - fl_cpStateFactor fp hn A t i j| ≤ h t :=
    fun t htr => (hagree t (Nat.le_of_lt htr)).1
  have hSfloor : ∀ t : ℕ, t < r → ρ / 2 ≤
      fl_cpStateFactor fp hn A t (cpPivot hn A t) (cpPivot hn A t) := by
    intro t htr
    have h1 := abs_le.mp (hclose t htr (cpPivot hn A t)
      (cpPivot hn A t))
    have h2 := hfloor t htr
    have h3 := hhhalf t htr
    linarith [h1.1, hδρ]
  -- pivot positivity for the fl states
  have hpos : ∀ t : ℕ, t < r →
      0 < fl_cpStateFactor fp hn A t (fl_cpPivotFactor fp hn A t)
        (fl_cpPivotFactor fp hn A t) := by
    intro t htr
    rw [hstage t htr]
    linarith [hSfloor t htr]
  -- state cap
  have hcapS : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |fl_cpStateFactor fp hn A t i j| ≤ c + δ / 2 := by
    intro t htr i j
    have h1 := hclose t htr i j
    have h2 := hcap t htr i j
    have h3 := abs_sub_abs_le_abs_sub
      (fl_cpStateFactor fp hn A t i j) (cpState hn A t i j)
    rw [abs_sub_comm (fl_cpStateFactor fp hn A t i j)
      (cpState hn A t i j)] at h3
    have h4 := hhhalf t htr
    linarith
  -- row cap: pivot entry via the sqrt model, off-pivot via domination
  have hcapR : ∀ t : ℕ, t < r → ∀ i : Fin n,
      |fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
        (fl_cpPivotFactor fp hn A t) i| ≤
      2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
        Real.sqrt (c + δ / 2) := by
    intro t htr i
    have hp := hstage t htr
    have hSp := hSfloor t htr
    have hSpos : (0:ℝ) < fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t) := by linarith
    -- the computed pivot entry
    obtain ⟨δa, hδa, hsqrt⟩ := fp.model_sqrt
      (fl_cpStateFactor fp hn A t (cpPivot hn A t) (cpPivot hn A t))
      hSpos.le
    have ha := abs_le.mp hδa
    have hsqle : Real.sqrt (fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t)) ≤
        Real.sqrt (c + δ / 2) := by
      apply Real.sqrt_le_sqrt
      have := hcapS t htr (cpPivot hn A t) (cpPivot hn A t)
      calc fl_cpStateFactor fp hn A t (cpPivot hn A t)
            (cpPivot hn A t)
          ≤ |fl_cpStateFactor fp hn A t (cpPivot hn A t)
            (cpPivot hn A t)| := le_abs_self _
        _ ≤ c + δ / 2 := this
    have hpivot_cap : |fp.fl_sqrt (fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t))| ≤
        (1 + fp.u) * Real.sqrt (c + δ / 2) := by
      rw [hsqrt, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h1a : |1 + δa| ≤ 1 + fp.u := by
        rw [abs_le]
        constructor <;> linarith [ha.1, ha.2]
      calc Real.sqrt _ * |1 + δa|
          ≤ Real.sqrt (c + δ / 2) * (1 + fp.u) :=
            mul_le_mul hsqle h1a (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = (1 + fp.u) * Real.sqrt (c + δ / 2) := mul_comm _ _
    -- exact-state invariants at stage t for the domination lemma
    have hSPSD : IsPosSemiDef n (cpState hn A t) :=
      cpState_isPosSemiDef hn A hPSD t fun s hs =>
        lt_of_lt_of_le hρ0 (hfloor s (lt_trans hs htr))
    have hht0 : 0 ≤ h t := by
      have h1 := abs_nonneg (cpState hn A t (cpPivot hn A t)
        (cpPivot hn A t) - fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t))
      exact le_trans h1 (hclose t htr _ _)
    have hdom := fl_factor_row_dominated fp (cpState hn A t)
      (fl_cpStateFactor fp hn A t) (cpPivot hn A t) ρ (h t)
      hSPSD (cpPivot_max hn A t) (hfloor t htr) hρ0 hht0
      (hht4 t htr) (hclose t htr) hu1 i
    have hconst : (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) ≤
        2 * (1 + fp.u) / (1 - fp.u) ^ 2 := by
      have h1 : 4 * h t / ρ ≤ 1 := by
        rw [div_le_one hρ0]
        linarith [hht4 t htr]
      have h2 : (0:ℝ) ≤ (1 + fp.u) / (1 - fp.u) ^ 2 := by positivity
      have h1' : 1 + 4 * h t / ρ ≤ 2 := by linarith
      calc (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2)
          ≤ 2 * ((1 + fp.u) / (1 - fp.u) ^ 2) :=
            mul_le_mul_of_nonneg_right h1' h2
        _ = 2 * (1 + fp.u) / (1 - fp.u) ^ 2 := by ring
    unfold fl_cpRowOf
    rw [hp]
    by_cases hip : i = cpPivot hn A t
    · rw [if_pos hip]
      refine hpivot_cap.trans ?_
      have hge1 : (1:ℝ) ≤ 2 * (1 + fp.u) / (1 - fp.u) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      calc (1 + fp.u) * Real.sqrt (c + δ / 2)
          ≤ (2 * (1 + fp.u) / (1 - fp.u) ^ 2) *
            ((1 + fp.u) * Real.sqrt (c + δ / 2)) := by
            nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + fp.u)
              (Real.sqrt_nonneg (c + δ / 2)), hge1]
        _ = 2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
            Real.sqrt (c + δ / 2) := by ring
    · rw [if_neg hip]
      refine (hdom).trans ?_
      calc (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
            |fp.fl_sqrt (fl_cpStateFactor fp hn A t
              (cpPivot hn A t) (cpPivot hn A t))|
          ≤ (2 * (1 + fp.u) / (1 - fp.u) ^ 2) *
            ((1 + fp.u) * Real.sqrt (c + δ / 2)) := by
            refine mul_le_mul hconst hpivot_cap (abs_nonneg _) ?_
            positivity
        _ = 2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
            Real.sqrt (c + δ / 2) := by ring
  exact fl_cpFactor_gram_backward_error fp hn A r hmul hPSD.1 hu8
    hpos (c + δ / 2)
    (2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 * Real.sqrt (c + δ / 2))
    hcapS hcapR

end NumStability
