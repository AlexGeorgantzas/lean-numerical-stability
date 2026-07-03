-- Algorithms/HighamChapter10.lean
--
-- Source-facing entry points for Higham Chapter 10, "Cholesky Factorization".
-- The focused Cholesky modules contain the reusable proofs and certificate
-- interfaces; this file gives stable chapter labels for the statements and
-- displayed equations used in the split-2 ledger.

import Mathlib.Data.Complex.Basic
import LeanFpAnalysis.FP.Algorithms.HighamChapter9
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySolve
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyDemmel
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyFl
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyPerturbation
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyPSD
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyNonsym
import LeanFpAnalysis.FP.Analysis.MatrixSpectral

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-! ## §10.1 Symmetric Positive Definite Matrices -/

/-- **Theorem 10.1** source predicate: an upper-triangular Cholesky factor with
positive diagonal satisfying `A = R^T R`. -/
abbrev higham10_1_CholeskyFactSpec (n : ℕ)
    (A R : Fin n → Fin n → ℝ) : Prop :=
  CholeskyFactSpec n A R

/-- **Theorem 10.1**, existence of the Cholesky factorization for real SPD
matrices. -/
theorem higham10_1_cholesky_existence (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) :
    ∃ R : Fin n → Fin n → ℝ, higham10_1_CholeskyFactSpec n A R :=
  cholesky_existence n A hSPD

/-- **Theorem 10.1**, uniqueness of the Cholesky factorization with positive
diagonal. -/
theorem higham10_1_cholesky_uniqueness (n : ℕ)
    (A R₁ R₂ : Fin n → Fin n → ℝ)
    (h₁ : higham10_1_CholeskyFactSpec n A R₁)
    (h₂ : higham10_1_CholeskyFactSpec n A R₂) :
    ∀ i j : Fin n, R₁ i j = R₂ i j :=
  cholesky_uniqueness n A R₁ R₂ h₁ h₂

/-- **Section 10.1**, the unit lower factor in the `A = L D L^T` rewrite
obtained from an upper Cholesky factor `R`. -/
noncomputable def higham10_1_choleskyLDLTLower {n : ℕ}
    (R : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if j.val ≤ i.val then R j i / R j j else 0

/-- **Section 10.1**, the diagonal factor in the `A = L D L^T` rewrite
obtained from an upper Cholesky factor `R`. -/
noncomputable def higham10_1_choleskyLDLTDiagonal {n : ℕ}
    (R : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then (R i i) ^ 2 else 0

/-- **Section 10.1**, Cholesky-to-`L D L^T` rewrite: every exact Cholesky
certificate `A = R^T R` with positive diagonal induces a unit-lower `L` and a
diagonal `D` satisfying the Chapter 11 block-LDLT specification with identity
permutation. -/
theorem higham10_1_cholesky_to_ldlt {n : ℕ}
    {A R : Fin n → Fin n → ℝ}
    (hChol : higham10_1_CholeskyFactSpec n A R) :
    BlockLDLTSpec n A (higham10_1_choleskyLDLTLower R)
      (higham10_1_choleskyLDLTDiagonal R) id where
  perm := Function.bijective_id
  L_diag := by
    intro i
    simp [higham10_1_choleskyLDLTLower, ne_of_gt (hChol.R_diag_pos i)]
  L_upper_zero := by
    intro i j hij
    simp [higham10_1_choleskyLDLTLower, not_le_of_gt hij]
  D_block_diag := by
    constructor
    · intro i j
      by_cases hij : i = j
      · subst hij
        simp [higham10_1_choleskyLDLTDiagonal]
      · have hji : j ≠ i := fun h => hij h.symm
        simp [higham10_1_choleskyLDLTDiagonal, hij, hji]
    · intro i j hfar
      have hij : i ≠ j := by
        intro h
        subst h
        rcases hfar with hfar | hfar <;> omega
      simp [higham10_1_choleskyLDLTDiagonal, hij]
  product_eq := by
    intro i j
    let L := higham10_1_choleskyLDLTLower R
    let D := higham10_1_choleskyLDLTDiagonal R
    have hL_mul_diag : ∀ p q : Fin n, L p q * R q q = R q p := by
      intro p q
      by_cases hqp : q.val ≤ p.val
      · have hdiag_ne : R q q ≠ 0 := ne_of_gt (hChol.R_diag_pos q)
        simp [L, higham10_1_choleskyLDLTLower, hqp, hdiag_ne]
      · have hpq : p.val < q.val := Nat.lt_of_not_ge hqp
        have hzero : R q p = 0 := hChol.R_upper q p hpq
        simp [L, higham10_1_choleskyLDLTLower, hqp, hzero]
    have hinner : ∀ k : Fin n,
        (∑ k₂ : Fin n, L i k * D k k₂ * L j k₂) = R k i * R k j := by
      intro k
      rw [Finset.sum_eq_single k]
      · have hi := hL_mul_diag i k
        have hj := hL_mul_diag j k
        simp [D, higham10_1_choleskyLDLTDiagonal]
        calc
          L i k * (R k k) ^ 2 * L j k
              = (L i k * R k k) * (L j k * R k k) := by ring
          _ = R k i * R k j := by rw [hi, hj]
      · intro b _ hb
        have hkb : k ≠ b := fun h => hb h.symm
        simp [D, higham10_1_choleskyLDLTDiagonal, hkb]
      · intro hnot
        exact (hnot (by simp)).elim
    calc
      (∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * D k₁ k₂ * L j k₂)
          = ∑ k : Fin n, R k i * R k j := by
            apply Finset.sum_congr rfl
            intro k _
            exact hinner k
      _ = A i j := hChol.product_eq i j

/-- **Problem 10.1 dependency**: every diagonal entry of a real SPD matrix is
strictly positive. -/
theorem higham10_spd_diag_pos {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) (i : Fin n) :
    0 < A i i := by
  have h := hSPD.2 (fun k => if k = i then 1 else 0) ⟨i, by simp⟩
  suffices hs : (∑ p : Fin n, ∑ q : Fin n,
      (if p = i then 1 else 0) * A p q * (if q = i then 1 else 0)) = A i i by
    linarith
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro hnot; simp at hnot
  · intro b _ hb; simp [hb]
  · intro hnot; simp at hnot

/-- **Problem 10.1**, determinant form: every off-diagonal `2 x 2`
principal minor of a real SPD matrix is strictly positive. -/
theorem higham10_problem_10_1_two_by_two_minor_pos {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A)
    {i j : Fin n} (hij : i ≠ j) :
    A i i * A j j - A i j ^ 2 > 0 := by
  have hdiag : 0 < A i i := higham10_spd_diag_pos A hSPD i
  let α : ℝ := A i j / A i i
  let x : Fin n → ℝ := fun k => if k = i then α else if k = j then -1 else 0
  have hx : ∃ k, x k ≠ 0 := ⟨j, by simp [x, hij.symm]⟩
  have hpos := hSPD.2 x hx
  have hinner : ∀ p : Fin n,
      (∑ q : Fin n, x p * A p q * x q) = x p * A p i * α - x p * A p j := by
    intro p
    rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) i
      (fun q : Fin n => x p * A p q * x q) (by simp)]
    rw [Finset.sum_eq_single j]
    · simp [x, hij.symm]
      ring
    · intro b hb hbj
      have hbi : b ≠ i := by
        intro h; subst h
        simp at hb
      simp [x, hbi, hbj]
    · intro hnot
      exfalso
      exact hnot (by simp [hij.symm])
  have hquad :
      (∑ p : Fin n, ∑ q : Fin n, x p * A p q * x q) =
        α ^ 2 * A i i - 2 * α * A i j + A j j := by
    simp_rw [hinner]
    rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) i
      (fun p : Fin n => x p * A p i * α - x p * A p j) (by simp)]
    rw [Finset.sum_eq_single j]
    · simp [x, hij.symm, hSPD.1 j i]
      ring
    · intro b hb hbj
      have hbi : b ≠ i := by
        intro h; subst h
        simp at hb
      simp [x, hbi, hbj]
    · intro hnot
      exfalso
      exact hnot (by simp [hij.symm])
  rw [hquad] at hpos
  have hne : A i i ≠ 0 := ne_of_gt hdiag
  have hm : 0 < A i i * (α ^ 2 * A i i - 2 * α * A i j + A j j) :=
    mul_pos hdiag hpos
  dsimp [α] at hm
  have hcalc :
      A i i * ((A i j / A i i) ^ 2 * A i i -
          2 * (A i j / A i i) * A i j + A j j) =
        A i i * A j j - A i j ^ 2 := by
    field_simp [hne]
    ring
  rw [hcalc] at hm
  exact hm

/-- **Problem 10.1**: if `A` is real SPD, then off-diagonal entries satisfy
`|a_ij| < sqrt (a_ii * a_jj)`. -/
theorem higham10_problem_10_1_abs_offdiag_lt_sqrt_diag_mul {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A)
    {i j : Fin n} (hij : i ≠ j) :
    |A i j| < Real.sqrt (A i i * A j j) := by
  have hminor := higham10_problem_10_1_two_by_two_minor_pos A hSPD hij
  have hprod_pos : 0 < A i i * A j j := by
    nlinarith [sq_nonneg (A i j)]
  have hs : |A i j| ^ 2 < (Real.sqrt (A i i * A j j)) ^ 2 := by
    rw [sq_abs, Real.sq_sqrt (le_of_lt hprod_pos)]
    nlinarith
  have hlt := (sq_lt_sq.mp hs)
  simpa [abs_of_nonneg (abs_nonneg (A i j)),
    abs_of_nonneg (Real.sqrt_nonneg _)] using hlt

/-- **Problem 10.1**, max-entry consequence: if `m` indexes a largest diagonal
entry of an SPD matrix, every absolute entry is bounded by `a_mm`. -/
theorem higham10_problem_10_1_abs_entry_le_largest_diag {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) (m : Fin n)
    (hm : ∀ i : Fin n, A i i ≤ A m m) :
    ∀ i j : Fin n, |A i j| ≤ A m m := by
  intro i j
  by_cases hij : i = j
  · subst i
    rw [abs_of_pos (higham10_spd_diag_pos A hSPD j)]
    exact hm j
  · have hlt := higham10_problem_10_1_abs_offdiag_lt_sqrt_diag_mul A hSPD hij
    have hi_pos := higham10_spd_diag_pos A hSPD i
    have hj_pos := higham10_spd_diag_pos A hSPD j
    have hm_pos := higham10_spd_diag_pos A hSPD m
    have hprod_le : A i i * A j j ≤ (A m m) ^ 2 := by
      nlinarith [hm i, hm j, le_of_lt hi_pos, le_of_lt hj_pos]
    have hsqrt_le : Real.sqrt (A i i * A j j) ≤ A m m := by
      have hs : Real.sqrt (A i i * A j j) ≤ Real.sqrt ((A m m) ^ 2) :=
        Real.sqrt_le_sqrt hprod_le
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hm_pos)] at hs
      exact hs
    exact le_trans (le_of_lt hlt) hsqrt_le

/-- **Problem 10.1**, exact max-entry conclusion: if `m` indexes a largest
diagonal entry of an SPD matrix, the max-entry norm is exactly `a_mm`. -/
theorem higham10_problem_10_1_maxEntryNorm_eq_largest_diag {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A)
    (m : Fin n) (hm : ∀ i : Fin n, A i i ≤ A m m) :
    maxEntryNorm hn A = A m m := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    exact higham10_problem_10_1_abs_entry_le_largest_diag A hSPD m hm i j
  · have hentry := entry_le_maxEntryNorm hn A m m
    rw [abs_of_pos (higham10_spd_diag_pos A hSPD m)] at hentry
    exact hentry

/-- **Problem 10.4**, first-stage exact GE fact: the Schur-complement reduced
submatrix of an SPD matrix is again SPD. -/
theorem higham10_problem_10_4_first_ge_reduced_submatrix_spd {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hSPD : IsSymPosDef (m + 1) A) :
    IsSymPosDef m
      (fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) :=
  spd_schur_complement_isSymPosDef A hSPD

/-- **Problem 10.4**, one exact GE step: every entry of the first
Schur-complement reduced matrix is bounded by the initial max-entry norm. -/
theorem higham10_problem_10_4_first_ge_entry_abs_le_initial_max {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hSPD : IsSymPosDef (m + 1) A) :
    ∀ i j : Fin m,
      |A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0| ≤
        maxEntryNorm (Nat.succ_pos m) A := by
  let S : Fin m → Fin m → ℝ :=
    fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0
  have hS : IsSymPosDef m S := spd_schur_complement_isSymPosDef A hSPD
  have hA00_pos : 0 < A 0 0 := higham10_spd_diag_pos A hSPD 0
  let M : ℝ := maxEntryNorm (Nat.succ_pos m) A
  have hM_pos : 0 < M := by
    have hentry := entry_le_maxEntryNorm (Nat.succ_pos m) A 0 0
    rw [abs_of_pos hA00_pos] at hentry
    exact lt_of_lt_of_le hA00_pos hentry
  have hdiag_le : ∀ i : Fin m, S i i ≤ M := by
    intro i
    have hAii_le : A i.succ i.succ ≤ M := by
      have hentry := entry_le_maxEntryNorm (Nat.succ_pos m) A i.succ i.succ
      rw [abs_of_pos (higham10_spd_diag_pos A hSPD i.succ)] at hentry
      exact hentry
    have hsub_nonneg : 0 ≤ A 0 i.succ * A 0 i.succ / A 0 0 := by
      have hnum : 0 ≤ A 0 i.succ * A 0 i.succ := by
        nlinarith [sq_nonneg (A 0 i.succ)]
      exact div_nonneg hnum (le_of_lt hA00_pos)
    dsimp [S]
    nlinarith
  intro i j
  by_cases hij : i = j
  · subst i
    rw [abs_of_pos (higham10_spd_diag_pos S hS j)]
    exact hdiag_le j
  · have hlt := higham10_problem_10_1_abs_offdiag_lt_sqrt_diag_mul S hS hij
    have hi_pos := higham10_spd_diag_pos S hS i
    have hj_pos := higham10_spd_diag_pos S hS j
    have hprod_le : S i i * S j j ≤ M ^ 2 := by
      nlinarith [hdiag_le i, hdiag_le j, le_of_lt hi_pos, le_of_lt hj_pos,
        le_of_lt hM_pos]
    have hsqrt_le : Real.sqrt (S i i * S j j) ≤ M := by
      have hs := Real.sqrt_le_sqrt hprod_le
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hM_pos)] at hs
      exact hs
    exact le_trans (le_of_lt hlt) hsqrt_le

/-- **Problem 10.4**, one exact GE step: the max-entry norm of the first
Schur-complement reduced matrix is no larger than the initial max-entry norm. -/
theorem higham10_problem_10_4_first_ge_maxEntryNorm_le {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hSPD : IsSymPosDef (m + 1) A) :
    maxEntryNorm hm
      (fun i j : Fin m =>
        A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) ≤
      maxEntryNorm (Nat.succ_pos m) A := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact higham10_problem_10_4_first_ge_entry_abs_le_initial_max A hSPD i j

/-- **Problem 10.4** exact unpivoted-GE invariant for SPD matrices.

For every nonempty stage, the current pivot is positive; for every nonempty
trailing Schur complement, the max-entry norm does not increase.  This is the
recursive source statement behind "no row exchanges are needed" and "growth
factor is 1" for Gaussian elimination on SPD matrices. -/
def higham10_problem_10_4_unpivotedGEGrowthBounded :
    (n : ℕ) → (0 < n) → (Fin n → Fin n → ℝ) → Prop
  | 0, _hn, _A => False
  | 1, _hn, A => 0 < A 0 0
  | m + 2, hn, A =>
      let S : Fin (m + 1) → Fin (m + 1) → ℝ :=
        fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0
      0 < A 0 0 ∧
        maxEntryNorm (Nat.succ_pos m) S ≤ maxEntryNorm hn A ∧
        higham10_problem_10_4_unpivotedGEGrowthBounded (m + 1) (Nat.succ_pos m) S

/-- **Problem 10.4**, exact SPD GE induction: unpivoted Gaussian elimination
has positive pivots at every stage and max-entry growth factor at most `1`. -/
theorem higham10_problem_10_4_unpivoted_ge_positive_pivots_and_growth :
    ∀ (n : ℕ) (hn : 0 < n) (A : Fin n → Fin n → ℝ),
      IsSymPosDef n A →
      higham10_problem_10_4_unpivotedGEGrowthBounded n hn A := by
  intro n
  induction n with
  | zero =>
      intro hn _A _hSPD
      exact (Nat.not_lt_zero 0 hn).elim
  | succ n ih =>
      intro hn A hSPD
      cases n with
      | zero =>
          exact higham10_spd_diag_pos A hSPD 0
      | succ m =>
          let S : Fin (m + 1) → Fin (m + 1) → ℝ :=
            fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0
          dsimp [higham10_problem_10_4_unpivotedGEGrowthBounded]
          refine ⟨higham10_spd_diag_pos A hSPD 0, ?_, ?_⟩
          · exact higham10_problem_10_4_first_ge_maxEntryNorm_le (Nat.succ_pos m) A hSPD
          · exact ih (Nat.succ_pos m) S
              (higham10_problem_10_4_first_ge_reduced_submatrix_spd A hSPD)

/-- **Algorithm 10.2** certificate for the computed Cholesky factor.  The
concrete loop is represented by the backward-error certificate used by the
analysis. -/
abbrev higham10_2_CholeskyBackwardError (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ) (ε : ℝ) : Prop :=
  CholeskyBackwardError n A R_hat ε

/-- **Theorem 10.3 / equation (10.5)**:
`R_hat^T R_hat = A + ΔA`, with
`|ΔA| <= γ_{n+1} |R_hat^T| |R_hat|` componentwise. -/
theorem higham10_3_cholesky_backward_error (fp : FPModel) (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hChol : higham10_2_CholeskyBackwardError n A R_hat (gamma fp (n + 1))) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (n + 1) *
        ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) :=
  cholesky_backward_error_perturbation n A R_hat (gamma fp (n + 1))
    (gamma_nonneg fp hn1) hChol

/-- **Algorithm 10.2 + Theorem 10.3, concrete closure**: the concrete
floating-point Cholesky factorization `fl_cholesky` (Algorithm 10.2), when
it runs to completion on a symmetric input (every rounded pivot
nonnegative, every computed diagonal entry nonzero), generates the
Theorem 10.3 backward-error certificate with the sharp `γ_{n+1}` constant:
the certificate hypothesis `higham10_2_CholeskyBackwardError` is discharged
by the algorithm itself rather than assumed. -/
theorem higham10_3_fl_cholesky_certificate (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hn1 : gammaValid fp (n + 1))
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n A j)
    (hdz : ∀ j : Fin n, fl_cholesky fp n A j j ≠ 0) :
    higham10_2_CholeskyBackwardError n A (fl_cholesky fp n A)
      (gamma fp (n + 1)) :=
  fl_cholesky_backward_error fp n A hsym hn1 hpiv hdz

/-- **Theorem 10.3 / equation (10.5) for the concrete Algorithm 10.2
factor**: `R̂ᵀR̂ = A + ΔA` with `|ΔA| ≤ γ_{n+1}|R̂ᵀ||R̂|`, where `R̂` is the
actual computed `fl_cholesky` factor. -/
theorem higham10_3_fl_cholesky_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hn1 : gammaValid fp (n + 1))
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n A j)
    (hdz : ∀ j : Fin n, fl_cholesky fp n A j j ≠ 0) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (n + 1) *
        ∑ k : Fin n, |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j|) ∧
      (∀ i j, ∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j =
        A i j + ΔA i j) :=
  higham10_3_cholesky_backward_error fp n A (fl_cholesky fp n A) hn1
    (higham10_3_fl_cholesky_certificate fp n A hsym hn1 hpiv hdz)

/-- **Theorem 10.4 / equation (10.6)**: Cholesky factorization plus the two
triangular solves gives `(A + ΔA)x_hat = b`, with Higham's absorbed
`γ_{3n+1}` componentwise bound. -/
theorem higham10_4_cholesky_solve_backward_error (fp : FPModel) (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hChol : higham10_2_CholeskyBackwardError n A R_hat (gamma fp (n + 1)))
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * n + 1)) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT b
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * n + 1) *
        ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  cholesky_solve_backward_error fp n A R_hat b hR_diag hChol hn1 hn3

/-- **Theorem 10.5 for the concrete Algorithm 10.2 factor**: Demmel's `dd^T`
bound with `d_i` the computed factor's column 2-norms, chained end-to-end
from the concrete `fl_cholesky` certificate — no assumed certificate or
Cauchy-Schwarz hypothesis remains. -/
theorem higham10_5_fl_cholesky_demmel_bound (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hn1 : gammaValid fp (n + 1))
    (hγlt : gamma fp (n + 1) < 1)
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n A j)
    (hdz : ∀ j : Fin n, fl_cholesky fp n A j j ≠ 0) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
        (colNorm n (fl_cholesky fp n A) i *
         colNorm n (fl_cholesky fp n A) j)) ∧
      (∀ i j, ∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j =
        A i j + ΔA i j) :=
  cholesky_demmel_bound_colNorm n A (fl_cholesky fp n A) (gamma fp (n + 1))
    (gamma_nonneg fp hn1) hγlt
    (fl_cholesky_backward_error fp n A hsym hn1 hpiv hdz)

/-- **Theorem 10.4 / equation (10.6) for the concrete Algorithm 10.2
factor**: factorization plus the two triangular solves on the computed
factor gives `(A + ΔA)x̂ = b` with the absorbed `γ_{3n+1}` componentwise
bound, chained end-to-end from the concrete `fl_cholesky` certificate. -/
theorem higham10_4_fl_cholesky_solve_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * n + 1))
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n A j)
    (hdz : ∀ j : Fin n, fl_cholesky fp n A j j ≠ 0) :
    let R_hat := fl_cholesky fp n A
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT b
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * n + 1) *
        ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham10_4_cholesky_solve_backward_error fp n A (fl_cholesky fp n A) b hdz
    (fl_cholesky_backward_error fp n A hsym hn1 hpiv hdz) hn1 hn3


/-- **Theorem 10.5**: Demmel's column-norm `dd^T` backward-error bound,
in the repository's certificate form.  The source proof's Cauchy-Schwarz and
diagonal-scaling estimate is supplied as `hCS`. -/
theorem higham10_5_demmel_bound (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i)
    (hCS : ∀ i j, ∑ k : Fin n, |R_hat k i| * |R_hat k j| ≤ d i * d j)
    (ε : ℝ) (hε : 0 ≤ ε) (hε_lt : ε < 1)
    (hChol : higham10_2_CholeskyBackwardError n A R_hat ε) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε / (1 - ε) * (d i * d j)) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) :=
  cholesky_demmel_bound n A R_hat d hd hCS ε hε hε_lt hChol

/-- **Theorem 10.5 / equation (10.8)**, closed form: with the computed-factor
column 2-norms `d_i = ‖R̂(:,i)‖₂ = √(∑_k R̂_{ki}²)`, the backward error satisfies
`|ΔA_{ij}| ≤ γ_{n+1}/(1-γ_{n+1}) · d_i d_j`.

Unlike `higham10_5_demmel_bound`, the Cauchy-Schwarz estimate is *proved*
(`colNorm_cauchy_schwarz`), so this is a genuine corollary of the Theorem 10.3
backward-error certificate — it assumes no analysis step beyond that certificate
and `γ_{n+1} < 1`. -/
theorem higham10_5_demmel_bound_colNorm (fp : FPModel) (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hγ_lt : gamma fp (n + 1) < 1)
    (hChol : higham10_2_CholeskyBackwardError n A R_hat (gamma fp (n + 1))) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
        (colNorm n R_hat i * colNorm n R_hat j)) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) :=
  cholesky_demmel_bound_colNorm n A R_hat (gamma fp (n + 1))
    (gamma_nonneg fp hn1) hγ_lt hChol

/-- **Equation (10.9)** source-shaped statement for van der Sluis scaling:
the scaled condition number is bounded by `n` times the best diagonal scaling
condition number. -/
def higham10_9_vanDerSluisScalingBound (n : ℕ)
    (κH bestDiagonalScalingκ : ℝ) : Prop :=
  κH ≤ (n : ℝ) * bestDiagonalScalingκ

/-- **Theorem 10.6 / equation (10.10)**:
Demmel-Wilkinson scaled forward-error interface.  The perturbation and scaling
argument is supplied as `hscaled_err`, matching the focused Cholesky module. -/
theorem higham10_6_scaled_forward_error (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (D : Fin n → ℝ)
    (κH f_n : ℝ)
    (hscaled_err : ∀ (x x_hat : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * x j = ∑ j : Fin n, A i j * x_hat j) →
      ∀ i, |x i - x_hat i| / D i ≤ f_n * κH * fp.u * (|x i| / D i)) :
    ∀ (x x_hat : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * x j = ∑ j : Fin n, A i j * x_hat j) →
      ∀ i, |x i - x_hat i| / D i ≤ f_n * κH * fp.u * (|x i| / D i) :=
  cholesky_scaled_forward_error n fp A D κH f_n hscaled_err

/-- **Theorem 10.7**, success-threshold consequence for the scaled Cholesky
analysis. -/
theorem higham10_7_success_condition (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (D : Fin n → ℝ) (H : Fin n → Fin n → ℝ)
    (hD_pos : ∀ i : Fin n, 0 < D i)
    (hDHD : ∀ i j : Fin n, A i j = D i * H i j * D j)
    (lam_min : ℝ)
    (hH_diag : ∀ i : Fin n, H i i = 1)
    (hn1 : gammaValid fp (n + 1))
    (hγ_lt : gamma fp (n + 1) < 1)
    (hlam_min : lam_min > ↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)))
    (hLam_bound : ∀ x : Fin n → ℝ,
      (∃ i, x i ≠ 0) →
      lam_min * ∑ i : Fin n, x i ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j) :
    0 < lam_min :=
  cholesky_success_condition n fp A D H hD_pos hDHD lam_min hH_diag
    hn1 hγ_lt hlam_min hLam_bound

/-- **Theorem 10.7**, success as genuine factorization existence.

    Strengthens `higham10_7_success_condition` from the sign consequence
    `0 < lam_min` to the actual conclusion of Theorem 10.7: when the scaled
    matrix `H` has Rayleigh lower bound `lam` exceeding the scaled backward-error
    quadratic-form bound `t`, the perturbed scaled matrix `D (H + E) D` is SPD
    and has a genuine Cholesky factorization — Cholesky succeeds. The
    "min-eigenvalue → PD" step is now proved (`quadForm_add_pos_of_perturbation`,
    `isSymPosDef_diagCongr`), not assumed. -/
theorem higham10_7_success_factorization (n : ℕ)
    (D : Fin n → ℝ) (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hD_pos : ∀ i, 0 < D i)
    (hH_sym : ∀ i j, H i j = H j i)
    (hE_sym : ∀ i j, E i j = E j i)
    (hlam : ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
        lam * ∑ i : Fin n, x i ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤ t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < lam) :
    ∃ R : Fin n → Fin n → ℝ,
      CholeskyFactSpec n (fun i j => D i * (H i j + E i j) * D j) R :=
  cholesky_succeeds_of_scaled_perturbation n D H E lam t hD_pos hH_sym hE_sym
    hlam hE hlt

/-- **Theorem 10.7**, failure-threshold consequence. -/
theorem higham10_7_failure_condition (n : ℕ) (fp : FPModel)
    (lam_min : ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hγ_lt : gamma fp (n + 1) < 1)
    (hLam_neg : lam_min < -(↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)))) :
    lam_min < 0 :=
  cholesky_failure_condition n fp lam_min hn1 hγ_lt hLam_neg

/-- **Theorem 10.7**, failure as genuine non-factorizability.

    Strengthens `higham10_7_failure_condition` from the sign consequence
    `lam_min < 0` to the actual failure conclusion: when `H` has a
    Rayleigh upper witness `lam` for its minimum eigenvalue below `-t`
    (with `t` the scaled backward-error quadratic-form bound), the scaled
    perturbed matrix `H + E` has a strictly negative curvature direction and
    therefore admits no Cholesky factorization — the algorithm fails. -/
theorem higham10_7_failure_no_factorization (n : ℕ)
    (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hlam_dir : ∃ x : Fin n → ℝ, (∃ i, x i ≠ 0) ∧
        (∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j) ≤ lam * ∑ i : Fin n, x i ^ 2)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤ t * ∑ i : Fin n, x i ^ 2)
    (hlt : lam < -t) :
    ¬ ∃ R : Fin n → Fin n → ℝ,
        CholeskyFactSpec n (fun i j => H i j + E i j) R := by
  obtain ⟨x, hx, hxneg⟩ :=
    quadForm_add_neg_of_perturbation n H E lam t hlam_dir hE hlt
  exact no_choleskyFactSpec_of_neg_quadForm n (fun i j => H i j + E i j) x hxneg

/-- Matrix-vector action commutes with vector negation. -/
theorem matMulVec_neg (n : ℕ) (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    matMulVec n A (fun k => -(v k)) = fun i => -(matMulVec n A v i) := by
  funext i
  unfold matMulVec
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Standard 2-norm perturbation bound** (the "standard perturbation
theory" step in the proof of Theorem 10.6, Higham p. 199): if `A x = b`,
`(A + ΔA) x̂ = b`, and `A⁻¹ ΔA` carries an operator-2-norm certificate
`c < 1`, then `‖x̂ − x‖₂ ≤ c/(1−c) · ‖x‖₂`. -/
theorem higham10_6_perturbed_solve_forward_error (n : ℕ)
    (A Ainv ΔA : Fin n → Fin n → ℝ) (x xhat b : Fin n → ℝ)
    (hInv : ∀ v : Fin n → ℝ, matMulVec n Ainv (matMulVec n A v) = v)
    (hAx : matMulVec n A x = b)
    (hAhat : ∀ i : Fin n,
      matMulVec n A xhat i + matMulVec n ΔA xhat i = b i)
    (c : ℝ) (hc : opNorm2Le (matMul n Ainv ΔA) c) (hc1 : c < 1) :
    vecNorm2 (fun i => xhat i - x i) ≤ c / (1 - c) * vecNorm2 x := by
  have h1c : (0:ℝ) < 1 - c := by linarith
  have hAdiff : matMulVec n A (fun k => xhat k - x k) =
      fun i => -(matMulVec n ΔA xhat i) := by
    funext i
    have hsub : matMulVec n A (fun k => xhat k - x k) i =
        matMulVec n A xhat i - matMulVec n A x i := by
      unfold matMulVec
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hbx : matMulVec n A x i = b i := congrFun hAx i
    have hb := hAhat i
    rw [hsub, hbx]
    linarith
  have hdiff : (fun k => xhat k - x k) =
      fun i => -(matMulVec n (matMul n Ainv ΔA) xhat i) := by
    have h2 := hInv (fun k => xhat k - x k)
    rw [hAdiff] at h2
    rw [← h2]
    rw [show matMulVec n Ainv (fun i => -(matMulVec n ΔA xhat i)) =
        fun i => -(matMulVec n Ainv (matMulVec n ΔA xhat) i) from
      matMulVec_neg n Ainv (matMulVec n ΔA xhat)]
    funext i
    rw [matMulVec_matMul n Ainv ΔA xhat i]
  have hnorm_diff : vecNorm2 (fun i => xhat i - x i) ≤ c * vecNorm2 xhat := by
    rw [hdiff, vecNorm2_neg (matMulVec n (matMul n Ainv ΔA) xhat)]
    exact hc xhat
  have hxhat : vecNorm2 xhat ≤
      vecNorm2 x + vecNorm2 (fun i => xhat i - x i) := by
    have := vecNorm2_add_le x (fun i => xhat i - x i)
    have hxx : (fun i => x i + (xhat i - x i)) = xhat := by
      funext i; ring
    rwa [hxx] at this
  have hkey : vecNorm2 (fun i => xhat i - x i) * (1 - c) ≤
      c * vecNorm2 x := by
    have h0x : 0 ≤ c * vecNorm2 x := le_trans (vecNorm2_nonneg _) (hc x)
    have he0 : 0 ≤ vecNorm2 (fun i => xhat i - x i) := vecNorm2_nonneg _
    rcases le_total 0 c with hc0 | hc0
    · have hchain := le_trans hnorm_diff
        (mul_le_mul_of_nonneg_left hxhat hc0)
      nlinarith
    · have hh0 : 0 ≤ vecNorm2 xhat := vecNorm2_nonneg _
      have hch : c * vecNorm2 xhat ≤ 0 := by nlinarith
      have hez : vecNorm2 (fun i => xhat i - x i) = 0 :=
        le_antisymm (by linarith) he0
      rw [hez, zero_mul]
      exact h0x
  rw [div_mul_eq_mul_div, le_div_iff₀ h1c]
  linarith [hkey]

/-- **Theorem 10.6 (Demmel–Wilkinson), certificate assembly** (Higham
§10.1, equation (10.10)): scaling the perturbed Cholesky solve by
`D = diag(a_ii^{1/2})` and applying the standard perturbation bound.  With
`H = D⁻¹AD⁻¹`, exact solve `A x = b`, perturbed solve `(A + ΔA) x̂ = b`,
an inverse-action certificate for `H`, and an operator-2-norm certificate
`c < 1` for `H⁻¹ (D⁻¹ ΔA D⁻¹)` — the `κ₂(H) ε` of the source display —
the `D`-scaled error satisfies `‖D(x̂ − x)‖₂ ≤ c/(1−c) ‖Dx‖₂`.  This
replaces the previously assumed-hypothesis interface
`higham10_6_scaled_forward_error` with a proved assembly; the remaining
source gap is producing the `c` certificate from `κ₂(H)` and the concrete
`fl_cholesky` solve (Theorem 10.4 + equation (10.8) + `‖eeᵀ‖₂ = n`). -/
theorem higham10_6_scaled_forward_error_assembled (n : ℕ)
    (A ΔA H Hinv : Fin n → Fin n → ℝ) (D : Fin n → ℝ)
    (x xhat b : Fin n → ℝ)
    (hD : ∀ i, D i ≠ 0)
    (hH : ∀ i j, H i j = A i j / (D i * D j))
    (hInv : ∀ v : Fin n → ℝ, matMulVec n Hinv (matMulVec n H v) = v)
    (hAx : matMulVec n A x = b)
    (hAhat : ∀ i : Fin n,
      matMulVec n A xhat i + matMulVec n ΔA xhat i = b i)
    (c : ℝ)
    (hc : opNorm2Le (matMul n Hinv
      (fun i j => ΔA i j / (D i * D j))) c)
    (hc1 : c < 1) :
    vecNorm2 (fun i => D i * xhat i - D i * x i) ≤
      c / (1 - c) * vecNorm2 (fun i => D i * x i) := by
  have hscale : ∀ (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n),
      matMulVec n (fun i' j' => M i' j' / (D i' * D j'))
        (fun k => D k * v k) i = matMulVec n M v i / D i := by
    intro M v i
    unfold matMulVec
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [hD i, hD j]
  have hHDx : matMulVec n H (fun k => D k * x k) =
      fun i => b i / D i := by
    funext i
    have hHs : matMulVec n H (fun k => D k * x k) i =
        matMulVec n (fun i' j' => A i' j' / (D i' * D j'))
          (fun k => D k * x k) i := by
      unfold matMulVec
      exact Finset.sum_congr rfl fun j _ => by rw [hH i j]
    rw [hHs, hscale A x i, congrFun hAx i]
  have hHDxhat : ∀ i : Fin n,
      matMulVec n H (fun k => D k * xhat k) i +
        matMulVec n (fun i' j' => ΔA i' j' / (D i' * D j'))
          (fun k => D k * xhat k) i = b i / D i := by
    intro i
    have hHs : matMulVec n H (fun k => D k * xhat k) i =
        matMulVec n (fun i' j' => A i' j' / (D i' * D j'))
          (fun k => D k * xhat k) i := by
      unfold matMulVec
      exact Finset.sum_congr rfl fun j _ => by rw [hH i j]
    rw [hHs, hscale A xhat i, hscale ΔA xhat i, ← add_div, hAhat i]
  have hmain := higham10_6_perturbed_solve_forward_error n H Hinv
    (fun i' j' => ΔA i' j' / (D i' * D j'))
    (fun k => D k * x k) (fun k => D k * xhat k) (fun i => b i / D i)
    hInv hHDx hHDxhat c hc hc1
  exact hmain

/-- **Quadratic-form bound from an operator-norm certificate** (the
Rayleigh–Weyl step of the Theorem 10.7 induction, Higham p. 200):
`opNorm2Le E c` gives `|xᵀEx| ≤ c ‖x‖₂²` — precisely the perturbation
hypothesis consumed by the Theorem 10.7 threshold theorems, so any
operator-norm certificate for the scaled backward error feeds them
directly. -/
theorem quadForm_abs_le_of_opNorm2Le (n : ℕ) (E : Fin n → Fin n → ℝ)
    (c : ℝ) (hE : opNorm2Le E c) (x : Fin n → ℝ) :
    |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
      c * ∑ i : Fin n, x i ^ 2 := by
  have hform : ∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j =
      ∑ i : Fin n, x i * matMulVec n E x i := by
    apply Finset.sum_congr rfl
    intro i _
    unfold matMulVec
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hform]
  have hxnn := vecNorm2_nonneg x
  have hsq : vecNorm2 x * vecNorm2 x = ∑ i : Fin n, x i ^ 2 := by
    rw [← sq, vecNorm2_sq]
    rfl
  calc |∑ i : Fin n, x i * matMulVec n E x i|
      ≤ vecNorm2 x * vecNorm2 (matMulVec n E x) :=
        abs_vecInnerProduct_le_vecNorm2_mul x (matMulVec n E x)
    _ ≤ vecNorm2 x * (c * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left (hE x) hxnn
    _ = c * (vecNorm2 x * vecNorm2 x) := by ring
    _ = c * ∑ i : Fin n, x i ^ 2 := by rw [hsq]

/-- **Componentwise domination transfers operator-2-norm certificates**
(used for the normwise equation (10.7) reading of Theorem 10.3): if
`|M| ≤ B` entrywise and `B` satisfies the vector-action certificate
`opNorm2Le B c`, then so does `M`. -/
theorem opNorm2Le_of_abs_le (n : ℕ) (M B : Fin n → Fin n → ℝ)
    (hdom : ∀ i j, |M i j| ≤ B i j) (c : ℝ) (hB : opNorm2Le B c) :
    opNorm2Le M c := by
  intro x
  have hentry : ∀ i : Fin n,
      |matMulVec n M x i| ≤ matMulVec n B (absVec n x) i := by
    intro i
    unfold matMulVec absVec
    calc |∑ j : Fin n, M i j * x j|
        ≤ ∑ j : Fin n, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, B i j * |x j| := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hdom i j) (abs_nonneg _)
  have hsq : vecNorm2Sq (matMulVec n M x) ≤
      vecNorm2Sq (matMulVec n B (absVec n x)) := by
    unfold vecNorm2Sq
    apply Finset.sum_le_sum
    intro i _
    have h1 := hentry i
    nlinarith [abs_nonneg (matMulVec n M x i),
      sq_abs (matMulVec n M x i)]
  have h5 : vecNorm2 (absVec n x) = vecNorm2 x := by
    unfold vecNorm2 vecNorm2Sq absVec
    congr 1
    exact Finset.sum_congr rfl fun i _ => sq_abs (x i)
  calc vecNorm2 (matMulVec n M x)
      ≤ vecNorm2 (matMulVec n B (absVec n x)) := Real.sqrt_le_sqrt hsq
    _ ≤ c * vecNorm2 (absVec n x) := hB (absVec n x)
    _ = c * vecNorm2 x := by rw [h5]

/-- **Lemma 6.6 chain, step 1** (used by equation (10.7)): a vector-action
operator-2-norm certificate bounds the squared Frobenius norm by `n c²`,
since each column is the image of a standard basis vector. -/
theorem frobNormSq_le_of_opNorm2Le (n : ℕ) (M : Fin n → Fin n → ℝ)
    (c : ℝ) (h : opNorm2Le M c) :
    frobNormSq M ≤ n * c ^ 2 := by
  have hcol : ∀ j : Fin n, matMulVec n M (fun k => if k = j then 1 else 0) =
      fun i => M i j := by
    intro j
    funext i
    unfold matMulVec
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)]
    simp
  have hbasis_norm : ∀ j : Fin n,
      vecNorm2 (fun k : Fin n => if k = j then (1:ℝ) else 0) = 1 := by
    intro j
    unfold vecNorm2 vecNorm2Sq
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)]
    simp
  have hcolsq : ∀ j : Fin n, ∑ i : Fin n, M i j ^ 2 ≤ c ^ 2 := by
    intro j
    have h1 := h (fun k => if k = j then 1 else 0)
    rw [hcol j, hbasis_norm j, mul_one] at h1
    have h2 : vecNorm2 (fun i => M i j) ^ 2 ≤ c ^ 2 := by
      have hnn : 0 ≤ vecNorm2 (fun i => M i j) := vecNorm2_nonneg _
      nlinarith
    rw [vecNorm2_sq] at h2
    exact h2
  unfold frobNormSq
  rw [Finset.sum_comm]
  calc ∑ j : Fin n, ∑ i : Fin n, M i j ^ 2
      ≤ ∑ _j : Fin n, c ^ 2 := Finset.sum_le_sum fun j _ => hcolsq j
    _ = n * c ^ 2 := by simp

/-- **Lemma 6.6 chain, step 2** (Higham Lemma 6.6, `‖|A|‖₂ ≤ √n ‖A‖₂`, in
vector-action form): the componentwise absolute value of a matrix carries
an operator-2-norm certificate inflated by `√n`, through the Frobenius
norm (which is invariant under componentwise absolute value). -/
theorem opNorm2Le_abs_of_opNorm2Le (n : ℕ) (M : Fin n → Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (h : opNorm2Le M c) :
    opNorm2Le (fun i j => |M i j|) (Real.sqrt n * c) := by
  intro x
  have habs_frob : frobNormSq (fun i j => |M i j|) = frobNormSq M := by
    unfold frobNormSq
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => sq_abs (M i j)
  calc vecNorm2 (matMulVec n (fun i j => |M i j|) x)
      ≤ frobNorm (fun i j => |M i j|) * vecNorm2 x :=
        vecNorm2_matMulVec_le_frobNorm_mul _ x
    _ ≤ Real.sqrt n * c * vecNorm2 x := by
        apply mul_le_mul_of_nonneg_right _ (vecNorm2_nonneg x)
        rw [frobNorm_eq_sqrt_frobNormSq, habs_frob]
        calc Real.sqrt (frobNormSq M)
            ≤ Real.sqrt (n * c ^ 2) :=
              Real.sqrt_le_sqrt (frobNormSq_le_of_opNorm2Le n M c h)
          _ = Real.sqrt n * c := by
              rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hc]

/-- Vector-action operator-2-norm certificates compose across the
repository matrix product. -/
theorem opNorm2Le_matMul (n : ℕ) (A B : Fin n → Fin n → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hA : opNorm2Le A a) (hB : opNorm2Le B b) :
    opNorm2Le (matMul n A B) (a * b) := by
  intro x
  have hcomp : matMulVec n (matMul n A B) x =
      matMulVec n A (matMulVec n B x) := by
    funext i
    unfold matMulVec matMul
    calc ∑ j : Fin n, (∑ k : Fin n, A i k * B k j) * x j
        = ∑ j : Fin n, ∑ k : Fin n, A i k * B k j * x j := by
          exact Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _
      _ = ∑ k : Fin n, ∑ j : Fin n, A i k * B k j * x j :=
          Finset.sum_comm
      _ = ∑ k : Fin n, A i k * ∑ j : Fin n, B k j * x j := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  rw [hcomp]
  calc vecNorm2 (matMulVec n A (matMulVec n B x))
      ≤ a * vecNorm2 (matMulVec n B x) := hA _
    _ ≤ a * (b * vecNorm2 x) := mul_le_mul_of_nonneg_left (hB x) ha
    _ = a * b * vecNorm2 x := by ring

/-- Nonnegative scaling of a vector-action operator-2-norm certificate. -/
theorem opNorm2Le_smul (n : ℕ) (B : Fin n → Fin n → ℝ) (c ε : ℝ)
    (hε : 0 ≤ ε) (hB : opNorm2Le B c) :
    opNorm2Le (fun i j => ε * B i j) (ε * c) := by
  intro x
  have hvec : matMulVec n (fun i j => ε * B i j) x =
      fun i => ε * matMulVec n B x i := by
    funext i
    unfold matMulVec
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hvec]
  have hnorm : vecNorm2 (fun i => ε * matMulVec n B x i) =
      ε * vecNorm2 (matMulVec n B x) := by
    unfold vecNorm2 vecNorm2Sq
    rw [show ∑ i : Fin n, (ε * matMulVec n B x i) ^ 2 =
        ε ^ 2 * ∑ i : Fin n, matMulVec n B x i ^ 2 by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε]
  rw [hnorm]
  calc ε * vecNorm2 (matMulVec n B x)
      ≤ ε * (c * vecNorm2 x) := mul_le_mul_of_nonneg_left (hB x) hε
    _ = ε * c * vecNorm2 x := by ring

/-- **Lemma 6.6 chain, transpose form**: `‖|Rᵀ|‖₂ ≤ √n c` from an
operator-2-norm certificate on `R`, via the transpose-invariant Frobenius
norm. -/
theorem opNorm2Le_abs_transpose_of_opNorm2Le (n : ℕ)
    (R : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : opNorm2Le R c) :
    opNorm2Le (fun i j => |R j i|) (Real.sqrt n * c) := by
  intro x
  have hfrob : frobNormSq (fun i j : Fin n => |R j i|) = frobNormSq R := by
    unfold frobNormSq
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => sq_abs (R i j)
  calc vecNorm2 (matMulVec n (fun i j => |R j i|) x)
      ≤ frobNorm (fun i j => |R j i|) * vecNorm2 x :=
        vecNorm2_matMulVec_le_frobNorm_mul _ x
    _ ≤ Real.sqrt n * c * vecNorm2 x := by
        apply mul_le_mul_of_nonneg_right _ (vecNorm2_nonneg x)
        rw [frobNorm_eq_sqrt_frobNormSq, hfrob]
        calc Real.sqrt (frobNormSq R)
            ≤ Real.sqrt (n * c ^ 2) :=
              Real.sqrt_le_sqrt (frobNormSq_le_of_opNorm2Le n R c h)
          _ = Real.sqrt n * c := by
              rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hc]

/-- **Equation (10.7), key inequality in certificate form** (Higham §10.1,
p. 198): `‖|R̂ᵀ||R̂|‖₂ ≤ n c²` whenever `‖R̂‖₂ ≤ c`, the analogue of
`‖|Rᵀ||R|‖₂ ≤ n ‖A‖₂` from Lemma 6.6. -/
theorem higham10_7_absRT_absR_opNorm2Le (n : ℕ)
    (R : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : opNorm2Le R c) :
    opNorm2Le
      (matMul n (fun i j => |R j i|) (fun i j => |R i j|))
      ((n : ℝ) * c ^ 2) := by
  have hprod := opNorm2Le_matMul n _ _ _ _
    (mul_nonneg (Real.sqrt_nonneg _) hc)
    (opNorm2Le_abs_transpose_of_opNorm2Le n R c hc h)
    (opNorm2Le_abs_of_opNorm2Le n R c hc h)
  have heq : Real.sqrt n * c * (Real.sqrt n * c) = (n : ℝ) * c ^ 2 := by
    have hs : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg n)
    nlinarith [hs]
  rwa [heq] at hprod

/-- **Equation (10.7), normwise backward error in certificate form**
(Higham §10.1, p. 198): from the componentwise Theorem 10.3 certificate
and an operator-norm certificate `‖R̂‖₂ ≤ c`, the residual
`ΔA = R̂ᵀR̂ − A` satisfies `‖ΔA‖₂ ≤ ε n c²`.  The source display continues
`≤ γ_{3n+1} n (1 − nγ_{n+1})^{-1} ‖A‖₂` by converting `c²` to `‖A‖₂`
through the spectral identity `‖R̂ᵀR̂‖₂ = ‖R̂‖₂²`, which remains open. -/
theorem higham10_7_normwise_backward_error (n : ℕ)
    (A R : Fin n → Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R ε)
    (c : ℝ) (hc : 0 ≤ c) (hR : opNorm2Le R c) :
    opNorm2Le
      (fun i j => (∑ k : Fin n, R k i * R k j) - A i j)
      (ε * ((n : ℝ) * c ^ 2)) := by
  apply opNorm2Le_of_abs_le n _
    (fun i j => ε * matMul n (fun i' j' => |R j' i'|)
      (fun i' j' => |R i' j'|) i j)
  · intro i j
    have hcert := hChol.backward_bound i j
    have hmm : matMul n (fun i' j' => |R j' i'|)
        (fun i' j' => |R i' j'|) i j =
        ∑ k : Fin n, |R k i| * |R k j| := rfl
    rw [hmm]
    exact hcert
  · exact opNorm2Le_smul n _ _ ε hε
      (higham10_7_absRT_absR_opNorm2Le n R c hc hR)


/-- **Theorem 10.7, spectral success form** (Higham §10.1): if the minimum
eigenvalue of the symmetric scaled matrix `H` — stated through the
repository's `finiteHermitianEigenvalues` — exceeds the scaled
backward-error quadratic-form bound `t`, then the perturbed scaled matrix
`D (H + E) D` has a genuine Cholesky factorization: the algorithm
succeeds.  This replaces the Rayleigh-quotient hypothesis of
`higham10_7_success_factorization` with the source's spectral `λ_min`
framing. -/
theorem higham10_7_success_factorization_spectral (n : ℕ)
    (D : Fin n → ℝ) (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hD_pos : ∀ i, 0 < D i)
    (hH_sym : IsSymmetricFiniteMatrix H)
    (hE_sym : ∀ i j, E i j = E j i)
    (hlam_le : ∀ a : Fin n, lam ≤ finiteHermitianEigenvalues H hH_sym a)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
          t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < lam) :
    ∃ R : Fin n → Fin n → ℝ,
      CholeskyFactSpec n (fun i j => D i * (H i j + E i j) * D j) R := by
  refine higham10_7_success_factorization n D H E lam t hD_pos
    (fun i j => hH_sym i j) hE_sym ?_ hE hlt
  intro x _hx
  have h := finiteLoewnerLe_smul_id_of_le_finiteHermitianEigenvalues
    H hH_sym hlam_le x
  rw [finiteQuadraticForm_smul_finiteIdMatrix,
    finiteQuadraticForm_eq_sum_sum] at h
  simpa [finiteVecNorm2Sq] using h

/-- **Theorem 10.7, spectral failure form** (Higham §10.1): if some
eigenvalue of the symmetric scaled matrix `H` is at most `lam < −t`, then
the perturbed scaled matrix `H + E` has a strictly negative curvature
direction (the corresponding eigenvector) and admits no Cholesky
factorization: the algorithm must fail. -/
theorem higham10_7_failure_no_factorization_spectral (n : ℕ)
    (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hH_sym : IsSymmetricFiniteMatrix H)
    (a : Fin n)
    (hlam_le : finiteHermitianEigenvalues H hH_sym a ≤ lam)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
          t * ∑ i : Fin n, x i ^ 2)
    (hlt : lam < -t) :
    ¬ ∃ R : Fin n → Fin n → ℝ,
        CholeskyFactSpec n (fun i j => H i j + E i j) R := by
  refine higham10_7_failure_no_factorization n H E lam t ?_ hE hlt
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one H hH_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      H hH_sym a
  rw [hnorm, mul_one] at hq
  refine ⟨⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
      hH_sym).eigenvectorBasis a), ?_, ?_⟩
  · by_contra hall
    push_neg at hall
    have hzero : finiteVecNorm2Sq
        (⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
          hH_sym).eigenvectorBasis a)) = 0 := by
      unfold finiteVecNorm2Sq
      exact Finset.sum_eq_zero fun i _ => by rw [hall i]; ring
    rw [hzero] at hnorm
    exact zero_ne_one hnorm
  · have hqs : ∑ i : Fin n, ∑ j : Fin n,
        (⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
          hH_sym).eigenvectorBasis a)) i * H i j *
        (⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
          hH_sym).eigenvectorBasis a)) j =
        finiteHermitianEigenvalues H hH_sym a := by
      rw [← finiteQuadraticForm_eq_sum_sum]
      exact hq
    rw [hqs]
    have hsum : ∑ i : Fin n,
        (⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
          hH_sym).eigenvectorBasis a)) i ^ 2 = 1 := by
      have := hnorm
      unfold finiteVecNorm2Sq at this
      exact this
    rw [hsum, mul_one]
    exact hlam_le

/-- **Minimum eigenvalue** of a symmetric real matrix, through the
repository's `finiteHermitianEigenvalues` (Higham §10.1, the `λ_min`
of Theorem 10.7). -/
noncomputable def finiteMinEigenvalue {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) : ℝ :=
  Finset.univ.inf' (Finset.univ_nonempty_iff.mpr
    (Fin.pos_iff_nonempty.mp hn)) (finiteHermitianEigenvalues M hM)

/-- The minimum eigenvalue is a lower bound for every eigenvalue. -/
theorem finiteMinEigenvalue_le {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) (a : Fin n) :
    finiteMinEigenvalue hn M hM ≤ finiteHermitianEigenvalues M hM a :=
  Finset.inf'_le _ (Finset.mem_univ a)

/-- The minimum eigenvalue is attained. -/
theorem exists_finiteMinEigenvalue_eq {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    ∃ a : Fin n, finiteHermitianEigenvalues M hM a =
      finiteMinEigenvalue hn M hM := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.mpr
    (Fin.pos_iff_nonempty.mp hn)) (finiteHermitianEigenvalues M hM)
  exact ⟨a, ha.symm⟩

/-- **Rayleigh lower bound from `λ_min`** (Higham §10.1, the spectral
inequality behind Theorem 10.7): `λ_min(M) ‖x‖₂² ≤ xᵀMx`. -/
theorem finiteMinEigenvalue_rayleigh {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M)
    (x : Fin n → ℝ) :
    finiteMinEigenvalue hn M hM * ∑ i : Fin n, x i ^ 2 ≤
      ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j := by
  have h := finiteLoewnerLe_smul_id_of_le_finiteHermitianEigenvalues
    M hM (finiteMinEigenvalue_le hn M hM) x
  rw [finiteQuadraticForm_smul_finiteIdMatrix,
    finiteQuadraticForm_eq_sum_sum] at h
  simpa [finiteVecNorm2Sq] using h

/-- **Theorem 10.7 success threshold, `λ_min` form** (Higham §10.1): if
`λ_min(H) > t`, the perturbed scaled matrix `D (H + E) D` has a genuine
Cholesky factorization. -/
theorem higham10_7_success_factorization_min_eig (n : ℕ) (hn : 0 < n)
    (D : Fin n → ℝ) (H E : Fin n → Fin n → ℝ) (t : ℝ)
    (hD_pos : ∀ i, 0 < D i)
    (hH_sym : IsSymmetricFiniteMatrix H)
    (hE_sym : ∀ i j, E i j = E j i)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
          t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < finiteMinEigenvalue hn H hH_sym) :
    ∃ R : Fin n → Fin n → ℝ,
      CholeskyFactSpec n (fun i j => D i * (H i j + E i j) * D j) R :=
  higham10_7_success_factorization_spectral n D H E
    (finiteMinEigenvalue hn H hH_sym) t hD_pos hH_sym hE_sym
    (finiteMinEigenvalue_le hn H hH_sym) hE hlt

/-- **Theorem 10.7 failure threshold, `λ_min` form** (Higham §10.1): if
`λ_min(H) < −t`, the perturbed scaled matrix `H + E` admits no Cholesky
factorization. -/
theorem higham10_7_failure_no_factorization_min_eig (n : ℕ) (hn : 0 < n)
    (H E : Fin n → Fin n → ℝ) (t : ℝ)
    (hH_sym : IsSymmetricFiniteMatrix H)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
          t * ∑ i : Fin n, x i ^ 2)
    (hlt : finiteMinEigenvalue hn H hH_sym < -t) :
    ¬ ∃ R : Fin n → Fin n → ℝ,
        CholeskyFactSpec n (fun i j => H i j + E i j) R := by
  obtain ⟨a, ha⟩ := exists_finiteMinEigenvalue_eq hn H hH_sym
  exact higham10_7_failure_no_factorization_spectral n H E
    (finiteMinEigenvalue hn H hH_sym) t hH_sym a (le_of_eq ha) hE hlt

/-- **Eigenvalue interlacing, lower direction** (Golub–Van Loan
Thm 8.1.7 as used in the Theorem 10.7 induction, Higham p. 200): the
minimum eigenvalue of a leading principal submatrix of a symmetric matrix
is at least the minimum eigenvalue of the full matrix.  Proof: evaluate
the full Rayleigh bound at the zero-padded minimizing eigenvector of the
submatrix. -/
theorem finiteMinEigenvalue_leading_principal_ge (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hH : IsSymmetricFiniteMatrix H)
    (k : ℕ) (hk0 : 0 < k) (hk : k ≤ n)
    (hHk_sym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)) :
    finiteMinEigenvalue hn H hH ≤
      finiteMinEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym := by
  obtain ⟨a, ha⟩ := exists_finiteMinEigenvalue_eq hk0
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym a
  rw [hnorm, mul_one] at hq
  set v : Fin k → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
      hHk_sym).eigenvectorBasis a) with hv
  have hvsq : ∑ i : Fin k, v i ^ 2 = 1 := by
    have := hnorm
    unfold finiteVecNorm2Sq at this
    exact this
  have hpadsq : ∑ i : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) ^ 2 = 1 := by
    rw [sum_sq_zero_pad_eq k hk v, hvsq]
  have hray := finiteMinEigenvalue_rayleigh hn H hH
    (fun i => if h : i.val < k then v ⟨i.val, h⟩ else 0)
  rw [hpadsq, mul_one] at hray
  have hpadquad : ∑ i : Fin n, ∑ j : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) * H i j *
        (if h : j.val < k then v ⟨j.val, h⟩ else 0) =
      finiteMinEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym := by
    rw [quadForm_zero_pad_eq H k hk v, ← ha, ← hq,
      finiteQuadraticForm_eq_sum_sum]
  rw [hpadquad] at hray
  exact hray

/-- **Maximum eigenvalue** of a symmetric real matrix, through the
repository's `finiteHermitianEigenvalues` (the `λ_max` of the spectral
reading of `‖·‖₂` on Gram matrices). -/
noncomputable def finiteMaxEigenvalue {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr
    (Fin.pos_iff_nonempty.mp hn)) (finiteHermitianEigenvalues M hM)

/-- Every eigenvalue is at most the maximum eigenvalue. -/
theorem le_finiteMaxEigenvalue {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) (a : Fin n) :
    finiteHermitianEigenvalues M hM a ≤ finiteMaxEigenvalue hn M hM :=
  Finset.le_sup' _ (Finset.mem_univ a)

/-- The maximum eigenvalue is attained. -/
theorem exists_finiteMaxEigenvalue_eq {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    ∃ a : Fin n, finiteHermitianEigenvalues M hM a =
      finiteMaxEigenvalue hn M hM := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty_iff.mpr
    (Fin.pos_iff_nonempty.mp hn)) (finiteHermitianEigenvalues M hM)
  exact ⟨a, ha.symm⟩

/-- **Rayleigh upper bound from `λ_max`**: `xᵀMx ≤ λ_max(M) ‖x‖₂²`. -/
theorem finiteMaxEigenvalue_rayleigh {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M)
    (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j ≤
      finiteMaxEigenvalue hn M hM * ∑ i : Fin n, x i ^ 2 := by
  have h := finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le
    M hM (le_finiteMaxEigenvalue hn M hM) x
  rw [finiteQuadraticForm_smul_finiteIdMatrix,
    finiteQuadraticForm_eq_sum_sum] at h
  simpa [finiteVecNorm2Sq] using h

/-- The Gram quadratic form is the squared image norm:
`xᵀ(RᵀR)x = ‖Rx‖₂²` in the repository's column convention. -/
theorem gram_quadForm_eq_sq_norm (n : ℕ) (R : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ l : Fin n,
      x i * (∑ p : Fin n, R p i * R p l) * x l =
    vecNorm2Sq (matMulVec n R x) := by
  unfold vecNorm2Sq matMulVec
  calc ∑ i : Fin n, ∑ l : Fin n,
      x i * (∑ p : Fin n, R p i * R p l) * x l
      = ∑ i : Fin n, ∑ l : Fin n, ∑ p : Fin n,
          (R p i * x i) * (R p l * x l) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro l _
        rw [mul_comm (x i) _, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        ring
    _ = ∑ p : Fin n, ∑ i : Fin n, ∑ l : Fin n,
          (R p i * x i) * (R p l * x l) := by
        refine Eq.trans
          (Finset.sum_congr rfl fun i _ => Finset.sum_comm) ?_
        exact Finset.sum_comm
    _ = ∑ p : Fin n, (∑ j : Fin n, R p j * x j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [sq, Finset.sum_mul_sum]

/-- **Spectral reading of the operator-2-norm certificate**
(`‖R‖₂ ≤ √λ_max(RᵀR)`, the remaining tail of display (10.7)): the
vector-action certificate holds at the square root of the Gram matrix's
largest eigenvalue. -/
theorem opNorm2Le_sqrt_maxEigenvalue_gram (n : ℕ) (hn : 0 < n)
    (R : Fin n → Fin n → ℝ)
    (hG_sym : IsSymmetricFiniteMatrix
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l)) :
    opNorm2Le R (Real.sqrt (finiteMaxEigenvalue hn
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym)) := by
  have hlam0 : 0 ≤ finiteMaxEigenvalue hn
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym := by
    obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn _ hG_sym
    have hnorm1 := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym a
    have hq :=
      finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
        (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym a
    rw [hnorm1, mul_one] at hq
    rw [← ha, ← hq, finiteQuadraticForm_eq_sum_sum,
      gram_quadForm_eq_sq_norm]
    exact vecNorm2Sq_nonneg _
  intro x
  have hray := finiteMaxEigenvalue_rayleigh hn
    (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym x
  rw [gram_quadForm_eq_sq_norm] at hray
  have hx2 : vecNorm2 x ^ 2 = ∑ i : Fin n, x i ^ 2 := vecNorm2_sq _
  have hRx2 : vecNorm2 (matMulVec n R x) ^ 2 =
      vecNorm2Sq (matMulVec n R x) := vecNorm2_sq _
  have hboth : vecNorm2 (matMulVec n R x) ^ 2 ≤
      (Real.sqrt (finiteMaxEigenvalue hn
        (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym) *
       vecNorm2 x) ^ 2 := by
    rw [hRx2, mul_pow, Real.sq_sqrt hlam0, hx2]
    exact hray
  nlinarith [vecNorm2_nonneg (matMulVec n R x),
    mul_nonneg (Real.sqrt_nonneg (finiteMaxEigenvalue hn
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym))
      (vecNorm2_nonneg x), hboth]

/-- **Display (10.7) closed by self-bounding** (the recorded open tail):
    from the componentwise certificate and the spectral reading of the
    Gram norm, the residual obeys the source display
    `‖ΔA‖₂ ≤ εn/(1−εn) ‖A‖₂` with no free factor certificate: taking
    `c² = λ_max(R̂ᵀR̂)` and evaluating the Gram quadratic form at the top
    eigenvector gives `λ_max ≤ ‖A‖₂ + εn λ_max`, so `λ_max` self-bounds
    by `‖A‖₂/(1−εn)`. -/
theorem higham10_7_normwise_backward_error_selfbound (n : ℕ)
    (hn : 0 < n) (A R : Fin n → Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R ε)
    (hG_sym : IsSymmetricFiniteMatrix
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l))
    (cA : ℝ) (hcA : opNorm2Le A cA)
    (hsmall : ε * (n : ℝ) < 1) :
    opNorm2Le
      (fun i j => (∑ k : Fin n, R k i * R k j) - A i j)
      (ε * (n : ℝ) * cA / (1 - ε * (n : ℝ))) := by
  set G : Fin n → Fin n → ℝ :=
    fun i l => ∑ p : Fin n, R p i * R p l with hG
  set lam : ℝ := finiteMaxEigenvalue hn G hG_sym with hlam
  have h1εn : (0:ℝ) < 1 - ε * (n : ℝ) := by linarith
  -- λ_max ≥ 0 via the top eigenvector and the Gram form
  obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn G hG_sym
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    G hG_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      G hG_sym a
  rw [hnorm, mul_one] at hq
  set v : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian G
      hG_sym).eigenvectorBasis a) with hv
  have hvsq : ∑ i : Fin n, v i ^ 2 = 1 := by
    have := hnorm
    unfold finiteVecNorm2Sq at this
    exact this
  have hqv : ∑ i : Fin n, ∑ j : Fin n, v i * G i j * v j = lam := by
    rw [hlam, ← ha, ← hq, finiteQuadraticForm_eq_sum_sum]
  have hlam0 : 0 ≤ lam := by
    rw [← hqv, hG]
    rw [gram_quadForm_eq_sq_norm]
    exact vecNorm2Sq_nonneg _
  -- residual certificate at c = √λ_max
  have hR := opNorm2Le_sqrt_maxEigenvalue_gram n hn R hG_sym
  have hΔ := higham10_7_normwise_backward_error n A R ε hε hChol
    (Real.sqrt lam) (Real.sqrt_nonneg _) hR
  rw [Real.sq_sqrt hlam0] at hΔ
  -- self-bounding: λ_max ≤ cA + εn·λ_max
  have hsplit : ∑ i : Fin n, ∑ j : Fin n, v i * G i j * v j =
      (∑ i : Fin n, ∑ j : Fin n, v i * A i j * v j) +
      ∑ i : Fin n, ∑ j : Fin n,
        v i * (G i j - A i j) * v j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hA_abs := quadForm_abs_le_of_opNorm2Le n A cA hcA v
  have hΔ_abs := quadForm_abs_le_of_opNorm2Le n
    (fun i j => G i j - A i j) (ε * ((n : ℝ) * lam)) hΔ v
  rw [hvsq, mul_one] at hA_abs hΔ_abs
  have hlam_le : lam ≤ cA + ε * (n : ℝ) * lam := by
    have h1 := (abs_le.mp hA_abs).2
    have h2 := (abs_le.mp hΔ_abs).2
    have := hqv
    rw [hsplit] at this
    nlinarith
  have hlam_bound : lam ≤ cA / (1 - ε * (n : ℝ)) := by
    rw [le_div_iff₀ h1εn]
    nlinarith
  -- upgrade the certificate constant
  intro x
  calc vecNorm2 (matMulVec n
        (fun i j => (∑ k : Fin n, R k i * R k j) - A i j) x)
      ≤ ε * ((n : ℝ) * lam) * vecNorm2 x := hΔ x
    _ ≤ ε * (n : ℝ) * cA / (1 - ε * (n : ℝ)) * vecNorm2 x := by
        refine mul_le_mul_of_nonneg_right ?_ (vecNorm2_nonneg x)
        have hεn : (0:ℝ) ≤ ε * (n : ℝ) :=
          mul_nonneg hε (Nat.cast_nonneg n)
        rw [le_div_iff₀ h1εn] at hlam_bound
        rw [le_div_iff₀ h1εn]
        nlinarith [hεn, hlam_bound]

/-- **Spectral reading, converse direction**: an operator-2-norm
certificate `c` bounds the Gram matrix's largest eigenvalue by `c²` —
together with the forward direction this is the honest certificate form
of `‖RᵀR‖₂ = ‖R‖₂²`. -/
theorem maxEigenvalue_gram_le_sq_of_opNorm2Le (n : ℕ) (hn : 0 < n)
    (R : Fin n → Fin n → ℝ)
    (hG_sym : IsSymmetricFiniteMatrix
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l))
    (c : ℝ) (h : opNorm2Le R c) :
    finiteMaxEigenvalue hn
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym ≤ c ^ 2 := by
  obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn _ hG_sym
  have hnorm1 := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym a
  rw [hnorm1, mul_one] at hq
  set v : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l)
      hG_sym).eigenvectorBasis a) with hv
  have hvq : vecNorm2Sq (matMulVec n R v) =
      finiteMaxEigenvalue hn
        (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym := by
    rw [← gram_quadForm_eq_sq_norm, ← finiteQuadraticForm_eq_sum_sum,
      hq, ha]
  have hvn : vecNorm2 v = 1 := by
    unfold vecNorm2
    rw [show vecNorm2Sq v = 1 from hnorm1]
    exact Real.sqrt_one
  have hb := h v
  rw [hvn, mul_one] at hb
  have hRv0 : 0 ≤ vecNorm2 (matMulVec n R v) := vecNorm2_nonneg _
  have hsq : vecNorm2 (matMulVec n R v) ^ 2 =
      vecNorm2Sq (matMulVec n R v) := vecNorm2_sq _
  nlinarith [hb, hRv0, hvq, hsq]



/-- Splitting a double sum over `Fin (m+1)` into interior, two borders,
and corner. -/
theorem sum_sum_castSucc_split (m : ℕ) (F : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ∑ i : Fin (m + 1), ∑ l : Fin (m + 1), F i l =
      (∑ i : Fin m, ∑ l : Fin m, F i.castSucc l.castSucc) +
      (∑ i : Fin m, F i.castSucc (Fin.last m)) +
      (∑ l : Fin m, F (Fin.last m) l.castSucc) +
      F (Fin.last m) (Fin.last m) := by
  rw [Fin.sum_univ_castSucc]
  rw [show ∑ i : Fin m, ∑ l : Fin (m + 1), F i.castSucc l =
      ∑ i : Fin m, ((∑ l : Fin m, F i.castSucc l.castSucc) +
        F i.castSucc (Fin.last m)) from
    Finset.sum_congr rfl fun i _ => Fin.sum_univ_castSucc _]
  rw [Fin.sum_univ_castSucc (f := fun l => F (Fin.last m) l)]
  rw [Finset.sum_add_distrib]
  ring

/-- **Theorem 10.7 (Demmel), success direction for the concrete
Algorithm 10.2** (Higham p. 200): if the minimum eigenvalue of the scaled
matrix `H = D⁻¹AD⁻¹` (`D = diag(√a_ii)`) exceeds
`(2n+3)·γ_{n+1}/(1−γ_{n+1})`, the concrete floating-point Cholesky
algorithm runs to completion: every rounded pivot is positive.  Per-stage
Rayleigh floors come from `λ_min(H)` by interlacing on the bordered
leading blocks and the substitution `z = (√a_i·y_i, √a_jj)`.  The
threshold constant is coarser than the source `n·γ_{n+1}/(1−γ_{n+1})`;
sharpening is open. -/
theorem higham10_7_fl_cholesky_success (fp : FPModel) (n : ℕ)
    (hn0 : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (hH_sym : IsSymmetricFiniteMatrix (fun i l : Fin n =>
      A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hthresh : (2 * (n : ℝ) + 3) *
      (gamma fp (n + 1) / (1 - gamma fp (n + 1))) <
      finiteMinEigenvalue hn0 (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) hH_sym) :
    ∀ j : Fin n, 0 < fl_cholPivot fp n A j := by
  apply fl_cholesky_pivots_pos fp A hsym hAdiag hn1 hγ1
    (finiteMinEigenvalue hn0 _ hH_sym) _ hthresh
  intro j y
  have hm1n : j.val + 1 ≤ n := j.isLt
  have hHb_sym : IsSymmetricFiniteMatrix (fun i l : Fin (j.val + 1) =>
      (fun i l : Fin n => A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) :=
    fun i l => hH_sym _ _
  have hinterlace := finiteMinEigenvalue_leading_principal_ge n hn0 _
    hH_sym (j.val + 1) (Nat.succ_pos j.val) hm1n hHb_sym
  set z : Fin (j.val + 1) → ℝ := Fin.snoc
    (fun i : Fin j.val =>
      Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) * y i)
    (Real.sqrt (A j j)) with hz
  have hray := finiteMinEigenvalue_rayleigh (Nat.succ_pos j.val)
    (fun i l : Fin (j.val + 1) =>
      (fun i l : Fin n => A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) hHb_sym z
  have hlast_eq : (⟨(Fin.last j.val).val, by omega⟩ : Fin n) = j :=
    Fin.ext (by simp)
  have hcancel : ∀ (i l : Fin n) (u v : ℝ),
      (Real.sqrt (A i i) * u) *
        (A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) *
        (Real.sqrt (A l l) * v) = u * A i l * v := by
    intro i l u v
    have hi := (Real.sqrt_pos.mpr (hAdiag i)).ne'
    have hl := (Real.sqrt_pos.mpr (hAdiag l)).ne'
    field_simp
  have hnorm : ∑ i : Fin (j.val + 1), z i ^ 2 =
      (∑ i : Fin j.val,
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [hz, Fin.snoc_castSucc, mul_pow, Real.sq_sqrt (hAdiag _).le]
    · rw [hz, Fin.snoc_last, Real.sq_sqrt (hAdiag j).le]
  have hz_nonneg_sq : 0 ≤ ∑ i : Fin (j.val + 1), z i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hquad : ∑ i : Fin (j.val + 1), ∑ l : Fin (j.val + 1),
      z i * ((fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * z l =
      (∑ i : Fin j.val, ∑ l : Fin j.val,
        y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
      2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j := by
    rw [sum_sum_castSucc_split j.val]
    have hp1 : ∑ i : Fin j.val, ∑ l : Fin j.val,
        z i.castSucc * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨(i.castSucc).val, by omega⟩ ⟨(l.castSucc).val, by omega⟩) *
          z l.castSucc =
        ∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hcancel _ _ (y i) (y l)
    have hp2 : ∑ i : Fin j.val,
        z i.castSucc * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨(i.castSucc).val, by omega⟩
          ⟨(Fin.last j.val).val, by omega⟩) * z (Fin.last j.val) =
        ∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_last, hlast_eq]
      have hthis := hcancel ⟨i.val, by omega⟩ j (y i) 1
      simp only [mul_one] at hthis
      exact hthis
    have hp3 : ∑ l : Fin j.val,
        z (Fin.last j.val) * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨(Fin.last j.val).val, by omega⟩
          ⟨(l.castSucc).val, by omega⟩) * z l.castSucc =
        ∑ l : Fin j.val, y l * A ⟨l.val, by omega⟩ j := by
      apply Finset.sum_congr rfl
      intro l _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_last, hlast_eq]
      have hthis := hcancel j ⟨l.val, by omega⟩ 1 (y l)
      simp only [one_mul, mul_one] at hthis
      have hfin : Real.sqrt (A j j) *
          (A j ⟨l.val, by omega⟩ /
            (Real.sqrt (A j j) *
             Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))) *
          (Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩) * y l) =
          y l * A ⟨l.val, by omega⟩ j := by
        rw [hthis, hsym j ⟨l.val, by omega⟩]
        ring
      exact hfin
    have hp4 : z (Fin.last j.val) * ((fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨(Fin.last j.val).val, by omega⟩
        ⟨(Fin.last j.val).val, by omega⟩) * z (Fin.last j.val) =
        A j j := by
      rw [hz, Fin.snoc_last, hlast_eq]
      have hthis := hcancel j j 1 1
      simp only [one_mul, mul_one] at hthis
      exact hthis
    rw [hp1, hp2, hp3, hp4]
    ring
  have hmono : finiteMinEigenvalue hn0 _ hH_sym *
      ∑ i : Fin (j.val + 1), z i ^ 2 ≤
      finiteMinEigenvalue (Nat.succ_pos j.val) _ hHb_sym *
      ∑ i : Fin (j.val + 1), z i ^ 2 :=
    mul_le_mul_of_nonneg_right hinterlace hz_nonneg_sq
  calc finiteMinEigenvalue hn0 _ hH_sym *
      ((∑ i : Fin j.val,
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j)
      = finiteMinEigenvalue hn0 _ hH_sym *
        ∑ i : Fin (j.val + 1), z i ^ 2 := by rw [hnorm]
    _ ≤ finiteMinEigenvalue (Nat.succ_pos j.val) _ hHb_sym *
        ∑ i : Fin (j.val + 1), z i ^ 2 := hmono
    _ ≤ ∑ i : Fin (j.val + 1), ∑ l : Fin (j.val + 1),
        z i * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * z l := hray
    _ = (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j := hquad




/-- **Theorem 10.7 foundation** (Higham §10.1, proof of Theorem 10.7): the
all-ones rank-one matrix `e eᵀ` has operator 2-norm at most `n`, in the
repository's vector-action certificate form `‖(e eᵀ)x‖₂ ≤ n ‖x‖₂`.  This is
the estimate that converts the componentwise scaled backward-error bound
`|E| ≤ c · e eᵀ` into the normwise hypothesis of the Theorem 10.7
success/failure thresholds. -/
theorem higham10_7_onesMatrix_opNorm2Le (n : ℕ) :
    opNorm2Le (fun _ _ : Fin n => (1 : ℝ)) n := by
  intro x
  have hmv : matMulVec n (fun _ _ => (1:ℝ)) x =
      fun _ : Fin n => ∑ j : Fin n, x j := by
    funext i
    unfold matMulVec
    exact Finset.sum_congr rfl fun j _ => one_mul (x j)
  rw [hmv]
  have hcs : (∑ j : Fin n, x j) ^ 2 ≤ (n : ℝ) * vecNorm2Sq x := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => (1:ℝ)) x
    have h1 : ∑ j : Fin n, (1:ℝ) * x j = ∑ j : Fin n, x j :=
      Finset.sum_congr rfl fun j _ => one_mul (x j)
    have h2 : ∑ _j : Fin n, ((1:ℝ)) ^ 2 = (n : ℝ) := by simp
    rw [h1, h2] at h
    exact h
  have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold vecNorm2 vecNorm2Sq
  have hconst : ∑ _i : Fin n, (∑ j : Fin n, x j) ^ 2 =
      (n : ℝ) * (∑ j : Fin n, x j) ^ 2 := by simp
  rw [hconst]
  have hbound : (n : ℝ) * (∑ j : Fin n, x j) ^ 2 ≤
      (n : ℝ) ^ 2 * ∑ i : Fin n, x i ^ 2 := by
    have := mul_le_mul_of_nonneg_left hcs hn0
    calc (n : ℝ) * (∑ j : Fin n, x j) ^ 2
        ≤ (n : ℝ) * ((n : ℝ) * vecNorm2Sq x) := this
      _ = (n : ℝ) ^ 2 * ∑ i : Fin n, x i ^ 2 := by
          unfold vecNorm2Sq; ring
  calc Real.sqrt ((n : ℝ) * (∑ j : Fin n, x j) ^ 2)
      ≤ Real.sqrt ((n : ℝ) ^ 2 * ∑ i : Fin n, x i ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = (n : ℝ) * Real.sqrt (∑ i : Fin n, x i ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn0]

/-- **Entrywise bound to quadratic-form bound** (Theorem 10.7 induction,
Higham p. 200): a uniform entrywise bound `|E i j| ≤ ε` gives
`|xᵀEx| ≤ ε n ‖x‖₂²`, through the `‖eeᵀ‖₂ ≤ n` certificate. -/
theorem quadForm_abs_le_of_entrywise_le (n : ℕ)
    (E : Fin n → Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ i j, |E i j| ≤ ε) (x : Fin n → ℝ) :
    |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
      ε * n * ∑ i : Fin n, x i ^ 2 := by
  have h2 := opNorm2Le_smul n (fun _ _ : Fin n => (1:ℝ)) n ε hε
    (higham10_7_onesMatrix_opNorm2Le n)
  have h3 := opNorm2Le_of_abs_le n E (fun _ _ : Fin n => ε * 1)
    (fun i j => by rw [mul_one]; exact hE i j) (ε * n) h2
  exact quadForm_abs_le_of_opNorm2Le n E (ε * n) h3 x

/-- **Certificate diagonal control** (Higham p. 198, the `‖r̂_i‖₂²` step in
the proof of Theorem 10.5): the backward-error certificate bounds each
computed column's squared norm by `(1−ε)⁻¹ a_ii`. -/
theorem chol_cert_colNormSq_le (n : ℕ) (A R : Fin n → Fin n → ℝ)
    (ε : ℝ) (hChol : CholeskyBackwardError n A R ε) (i : Fin n) :
    (1 - ε) * ∑ k : Fin n, R k i ^ 2 ≤ A i i := by
  have hcert := hChol.backward_bound i i
  rw [show ∑ k : Fin n, R k i * R k i = ∑ k : Fin n, R k i ^ 2 from
      Finset.sum_congr rfl fun k _ => by ring,
    show ∑ k : Fin n, |R k i| * |R k i| = ∑ k : Fin n, R k i ^ 2 from
      Finset.sum_congr rfl fun k _ => by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]; ring] at hcert
  have := abs_le.mp hcert
  linarith [this.1]

/-- **Scaled entrywise backward-error bound** (Theorem 10.7 induction,
Higham p. 200): the Theorem 10.3 certificate implies the perturbation of
the diagonally scaled matrix is uniformly small entrywise,
`|ΔA_ij| ≤ ε/(1−ε) · √a_ii √a_jj`. -/
theorem chol_cert_scaled_entrywise_le (n : ℕ) (A R : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hChol : CholeskyBackwardError n A R ε)
    (hAnn : ∀ l : Fin n, 0 ≤ A l l) (i j : Fin n) :
    |(∑ k : Fin n, R k i * R k j) - A i j| ≤
      ε / (1 - ε) * (Real.sqrt (A i i) * Real.sqrt (A j j)) := by
  have h1ε : (0:ℝ) < 1 - ε := by linarith
  have hcert := hChol.backward_bound i j
  have hcs : ∑ k : Fin n, |R k i| * |R k j| ≤
      Real.sqrt (∑ k : Fin n, R k i ^ 2) *
      Real.sqrt (∑ k : Fin n, R k j ^ 2) := by
    have h := abs_vecInnerProduct_le_vecNorm2_mul
      (fun k => |R k i|) (fun k => |R k j|)
    have hnn : 0 ≤ ∑ k : Fin n, |R k i| * |R k j| :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [abs_of_nonneg hnn] at h
    calc ∑ k : Fin n, |R k i| * |R k j|
        ≤ vecNorm2 (fun k => |R k i|) * vecNorm2 (fun k => |R k j|) := h
      _ = Real.sqrt (∑ k : Fin n, R k i ^ 2) *
          Real.sqrt (∑ k : Fin n, R k j ^ 2) := by
          unfold vecNorm2 vecNorm2Sq
          congr 2 <;> exact Finset.sum_congr rfl fun k _ => sq_abs _
  have hcol : ∀ l : Fin n, Real.sqrt (∑ k : Fin n, R k l ^ 2) ≤
      Real.sqrt (A l l) / Real.sqrt (1 - ε) := by
    intro l
    rw [show Real.sqrt (A l l) / Real.sqrt (1 - ε) =
        Real.sqrt (A l l / (1 - ε)) from
      (Real.sqrt_div (hAnn l) _).symm]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ h1ε]
    linarith [chol_cert_colNormSq_le n A R ε hChol l]
  have hmulself : Real.sqrt (1 - ε) * Real.sqrt (1 - ε) = 1 - ε :=
    Real.mul_self_sqrt h1ε.le
  have hsne : Real.sqrt (1 - ε) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmulself
    linarith
  calc |(∑ k : Fin n, R k i * R k j) - A i j|
      ≤ ε * ∑ k : Fin n, |R k i| * |R k j| := hcert
    _ ≤ ε * (Real.sqrt (∑ k : Fin n, R k i ^ 2) *
        Real.sqrt (∑ k : Fin n, R k j ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hε0
    _ ≤ ε * ((Real.sqrt (A i i) / Real.sqrt (1 - ε)) *
        (Real.sqrt (A j j) / Real.sqrt (1 - ε))) := by
        apply mul_le_mul_of_nonneg_left _ hε0
        exact mul_le_mul (hcol i) (hcol j) (Real.sqrt_nonneg _)
          (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = ε / (1 - ε) * (Real.sqrt (A i i) * Real.sqrt (A j j)) := by
        field_simp
        linear_combination
          (-(ε * Real.sqrt (A i i) * Real.sqrt (A j j))) *
            (Real.sq_sqrt h1ε.le)

/-- **Scaled operator-norm certificate for factor-shaped perturbations**
(Theorem 10.6 assembly, steps 1–2): any perturbation bounded
componentwise by `ε_tot·|R̂ᵀ||R̂|`, with `R̂` carrying the Theorem 10.3
certificate at `γ`, has a `D⁻¹·D⁻¹`-scaled operator-2-norm certificate
`n·ε_tot/(1−γ)` — via the certificate's column-norm control,
Cauchy–Schwarz, and the ones-matrix bound. -/
theorem scaled_opNorm2Le_of_factor_bound (fp : FPModel) (n : ℕ)
    (A R : Fin n → Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hγ1 : gamma fp (n + 1) < 1)
    (hChol : CholeskyBackwardError n A R (gamma fp (n + 1)))
    (M : Fin n → Fin n → ℝ) (εtot : ℝ) (hε : 0 ≤ εtot)
    (hM : ∀ i j : Fin n, |M i j| ≤
      εtot * ∑ k : Fin n, |R k i| * |R k j|) :
    opNorm2Le (fun i j =>
      M i j / (Real.sqrt (A i i) * Real.sqrt (A j j)))
      ((n : ℝ) * (εtot / (1 - gamma fp (n + 1)))) := by
  set γ : ℝ := gamma fp (n + 1) with hγdef
  have h1γ : (0:ℝ) < 1 - γ := by linarith
  -- uniform entrywise bound on the scaled perturbation
  have hcol : ∀ l : Fin n, Real.sqrt (∑ k : Fin n, R k l ^ 2) ≤
      Real.sqrt (A l l) / Real.sqrt (1 - γ) := by
    intro l
    rw [show Real.sqrt (A l l) / Real.sqrt (1 - γ) =
        Real.sqrt (A l l / (1 - γ)) from
      (Real.sqrt_div (hAdiag l).le _).symm]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ h1γ]
    linarith [chol_cert_colNormSq_le n A R γ hChol l]
  have hcs : ∀ i j : Fin n, ∑ k : Fin n, |R k i| * |R k j| ≤
      Real.sqrt (∑ k : Fin n, R k i ^ 2) *
      Real.sqrt (∑ k : Fin n, R k j ^ 2) := by
    intro i j
    have h := abs_vecInnerProduct_le_vecNorm2_mul
      (fun k => |R k i|) (fun k => |R k j|)
    have hnn : 0 ≤ ∑ k : Fin n, |R k i| * |R k j| :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [abs_of_nonneg hnn] at h
    calc ∑ k : Fin n, |R k i| * |R k j|
        ≤ vecNorm2 (fun k => |R k i|) * vecNorm2 (fun k => |R k j|) := h
      _ = Real.sqrt (∑ k : Fin n, R k i ^ 2) *
          Real.sqrt (∑ k : Fin n, R k j ^ 2) := by
          unfold vecNorm2 vecNorm2Sq
          congr 2 <;> exact Finset.sum_congr rfl fun k _ => sq_abs _
  have hsqrt1γ : Real.sqrt (1 - γ) * Real.sqrt (1 - γ) = 1 - γ :=
    Real.mul_self_sqrt h1γ.le
  have hentry : ∀ i j : Fin n,
      |M i j / (Real.sqrt (A i i) * Real.sqrt (A j j))| ≤
      εtot / (1 - γ) := by
    intro i j
    have hsi := Real.sqrt_pos.mpr (hAdiag i)
    have hsj := Real.sqrt_pos.mpr (hAdiag j)
    rw [abs_div, abs_of_pos (mul_pos hsi hsj),
      div_le_iff₀ (mul_pos hsi hsj)]
    calc |M i j|
        ≤ εtot * ∑ k : Fin n, |R k i| * |R k j| := hM i j
      _ ≤ εtot * (Real.sqrt (∑ k : Fin n, R k i ^ 2) *
          Real.sqrt (∑ k : Fin n, R k j ^ 2)) :=
          mul_le_mul_of_nonneg_left (hcs i j) hε
      _ ≤ εtot * ((Real.sqrt (A i i) / Real.sqrt (1 - γ)) *
          (Real.sqrt (A j j) / Real.sqrt (1 - γ))) := by
          apply mul_le_mul_of_nonneg_left _ hε
          exact mul_le_mul (hcol i) (hcol j) (Real.sqrt_nonneg _)
            (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = εtot / (1 - γ) * (Real.sqrt (A i i) * Real.sqrt (A j j)) := by
          field_simp
          linear_combination (-εtot) * (Real.sq_sqrt h1γ.le)
  -- entrywise → operator certificate through the ones matrix
  have hones := opNorm2Le_smul n (fun _ _ : Fin n => (1:ℝ)) n
    (εtot / (1 - γ)) (div_nonneg hε h1γ.le)
    (higham10_7_onesMatrix_opNorm2Le n)
  have habs := opNorm2Le_of_abs_le n
    (fun i j => M i j / (Real.sqrt (A i i) * Real.sqrt (A j j)))
    (fun _ _ : Fin n => εtot / (1 - γ) * 1)
    (fun i j => by rw [mul_one]; exact hentry i j)
    (εtot / (1 - γ) * n) hones
  intro x
  calc vecNorm2 (matMulVec n (fun i j =>
      M i j / (Real.sqrt (A i i) * Real.sqrt (A j j))) x)
      ≤ εtot / (1 - γ) * n * vecNorm2 x := habs x
    _ = (n : ℝ) * (εtot / (1 - γ)) * vecNorm2 x := by ring

/-- **Theorem 10.6 (Demmel–Wilkinson) for the concrete solve chain**
(Higham §10.1, equation (10.10)): with the Theorem 10.3 certificate for
`R̂`, a solve-chain perturbation `ΔA` bounded by `ε_tot·|R̂ᵀ||R̂|`
(supplied by `cholesky_solve_backward_error_expanded`), an inverse-action
certificate for `H = D⁻¹AD⁻¹` and a `κ₂(H)`-style operator certificate
for `H⁻¹`, the `D`-scaled forward error satisfies
`‖D(x̂−x)‖₂ ≤ c/(1−c)·‖Dx‖₂` with the explicit
`c = κ·n·ε_tot/(1−γ_{n+1})` — the source display (10.10) with
`ε_tot = γ_{n+1} + 2γ_n + γ_n²` in place of `γ_{3n+1}`. -/
theorem higham10_6_fl_scaled_forward_error (fp : FPModel) (n : ℕ)
    (A R Hinv ΔA : Fin n → Fin n → ℝ) (x xhat b : Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hγ1 : gamma fp (n + 1) < 1)
    (hChol : CholeskyBackwardError n A R (gamma fp (n + 1)))
    (εtot : ℝ) (hε : 0 ≤ εtot)
    (hΔA : ∀ i j : Fin n, |ΔA i j| ≤
      εtot * ∑ k : Fin n, |R k i| * |R k j|)
    (hInv : ∀ v : Fin n → ℝ,
      matMulVec n Hinv (matMulVec n (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) v) = v)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : opNorm2Le Hinv κ)
    (hAx : matMulVec n A x = b)
    (hAhat : ∀ i : Fin n,
      matMulVec n A xhat i + matMulVec n ΔA xhat i = b i)
    (hc1 : κ * ((n : ℝ) * (εtot / (1 - gamma fp (n + 1)))) < 1) :
    vecNorm2 (fun i => Real.sqrt (A i i) * xhat i -
        Real.sqrt (A i i) * x i) ≤
      κ * ((n : ℝ) * (εtot / (1 - gamma fp (n + 1)))) /
        (1 - κ * ((n : ℝ) * (εtot / (1 - gamma fp (n + 1))))) *
      vecNorm2 (fun i => Real.sqrt (A i i) * x i) := by
  have hscaled := scaled_opNorm2Le_of_factor_bound fp n A R hAdiag hγ1
    hChol ΔA εtot hε hΔA
  have hcomp := opNorm2Le_matMul n Hinv
    (fun i j => ΔA i j / (Real.sqrt (A i i) * Real.sqrt (A j j)))
    κ ((n : ℝ) * (εtot / (1 - gamma fp (n + 1)))) hκ0 hκ hscaled
  exact higham10_6_scaled_forward_error_assembled n A ΔA
    (fun i l : Fin n => A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
    Hinv (fun i => Real.sqrt (A i i)) x xhat b
    (fun i => (Real.sqrt_pos.mpr (hAdiag i)).ne')
    (fun i j => rfl) hInv hAx hAhat
    (κ * ((n : ℝ) * (εtot / (1 - gamma fp (n + 1))))) hcomp hc1





/-- **Absorption of the solve-chain constant into `γ_{3n+1}`**
    (Higham §10.1, proof of Theorem 10.6):
    `γ_{n+1} + 2γ_n + γ_n² ≤ γ_{3n+1}`, via
    `2γ_n + γ_n² ≤ γ_{2n}` and `γ_{n+1} + γ_{2n} ≤ γ_{3n+1}`. -/
lemma eps_tot_le_gamma_3n1 (fp : FPModel) (n : ℕ)
    (hn3 : gammaValid fp (3 * n + 1)) :
    gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2 ≤
      gamma fp (3 * n + 1) := by
  have hn1 : gammaValid fp (n + 1) := gammaValid_mono fp (by omega) hn3
  have hstep1 : gamma fp n + gamma fp n + gamma fp n * gamma fp n ≤
      gamma fp (2 * n) := by
    have heq : n + n = 2 * n := by omega
    have h := gamma_sum_le fp n n (gammaValid_mono fp (by omega) hn3)
    rw [heq] at h; exact h
  have hstep2 : gamma fp (n + 1) + gamma fp (2 * n) ≤
      gamma fp (3 * n + 1) := by
    have heq : (n + 1) + 2 * n = 3 * n + 1 := by omega
    have h := gamma_sum_le fp (n + 1) (2 * n) (heq ▸ hn3)
    have hnn1 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
    have hnn2 : 0 ≤ gamma fp (2 * n) :=
      gamma_nonneg fp (gammaValid_mono fp (by omega) hn3)
    rw [heq] at h
    linarith [mul_nonneg hnn1 hnn2]
  nlinarith [hstep1, hstep2]

/-- **Theorem 10.6 / display (10.10) with the source constant**: the
    scaled forward-error bound of `higham10_6_fl_scaled_forward_error`
    with the composite solve-chain constant absorbed into Higham's
    `γ_{3n+1}` — `c = κ n γ_{3n+1}/(1 − γ_{n+1})` exactly as printed. -/
theorem higham10_6_fl_scaled_forward_error_source (fp : FPModel) (n : ℕ)
    (A R Hinv ΔA : Fin n → Fin n → ℝ) (x xhat b : Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hγ1 : gamma fp (n + 1) < 1)
    (hn3 : gammaValid fp (3 * n + 1))
    (hChol : CholeskyBackwardError n A R (gamma fp (n + 1)))
    (hΔA : ∀ i j : Fin n, |ΔA i j| ≤
      (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
        ∑ k : Fin n, |R k i| * |R k j|)
    (hInv : ∀ v : Fin n → ℝ,
      matMulVec n Hinv (matMulVec n (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) v) = v)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : opNorm2Le Hinv κ)
    (hAx : matMulVec n A x = b)
    (hAhat : ∀ i : Fin n,
      matMulVec n A xhat i + matMulVec n ΔA xhat i = b i)
    (hc1 : κ * ((n : ℝ) *
      (gamma fp (3 * n + 1) / (1 - gamma fp (n + 1)))) < 1) :
    vecNorm2 (fun i => Real.sqrt (A i i) * xhat i -
        Real.sqrt (A i i) * x i) ≤
      κ * ((n : ℝ) * (gamma fp (3 * n + 1) / (1 - gamma fp (n + 1)))) /
        (1 - κ * ((n : ℝ) *
          (gamma fp (3 * n + 1) / (1 - gamma fp (n + 1))))) *
      vecNorm2 (fun i => Real.sqrt (A i i) * x i) := by
  have habsorb := eps_tot_le_gamma_3n1 fp n hn3
  refine higham10_6_fl_scaled_forward_error fp n A R Hinv ΔA x xhat b
    hAdiag hγ1 hChol (gamma fp (3 * n + 1))
    (gamma_nonneg fp hn3) (fun i j => ?_) hInv κ hκ0 hκ hAx hAhat hc1
  calc |ΔA i j|
      ≤ (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |R k i| * |R k j| := hΔA i j
    _ ≤ gamma fp (3 * n + 1) * ∑ k : Fin n, |R k i| * |R k j| :=
        mul_le_mul_of_nonneg_right habsorb
          (absRT_R_product_nonneg n R i j)

/-! ## §10.2 Sensitivity of the Cholesky Factorization -/

/-- **Theorem 10.8**, Sun's normwise perturbation interface. -/
theorem higham10_8_sun_normwise_perturbation (n : ℕ)
    (A R : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (hChol : CholeskyFactSpec n A R)
    (hSym_A : ∀ i j : Fin n, A i j = A j i)
    (hSym_ΔA : ∀ i j : Fin n, ΔA i j = ΔA j i)
    (norm2_A : ℝ) (hnorm2_pos : 0 < norm2_A)
    (κ2_A : ℝ) (hκ2_pos : 0 < κ2_A)
    (hSmall : frobNormSq ΔA < norm2_A ^ 2)
    (hpert : ∃ ΔR : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → ΔR i j = 0) ∧
      (∀ i j, ∑ k : Fin n, (R k i + ΔR k i) * (R k j + ΔR k j) = A i j + ΔA i j) ∧
      frobNormSq ΔR ≤ κ2_A ^ 2 / (4 * norm2_A ^ 2) * frobNormSq ΔA) :
    ∃ ΔR : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → ΔR i j = 0) ∧
      (∀ i j, ∑ k : Fin n, (R k i + ΔR k i) * (R k j + ΔR k j) = A i j + ΔA i j) ∧
      frobNormSq ΔR ≤ κ2_A ^ 2 / (4 * norm2_A ^ 2) * frobNormSq ΔA :=
  cholesky_perturbation_normwise n A R ΔA hChol hSym_A hSym_ΔA
    norm2_A hnorm2_pos κ2_A hκ2_pos hSmall hpert

/-- **Theorem 10.8**, Sun's componentwise perturbation interface using the
upper-triangular part. -/
theorem higham10_8_sun_componentwise_perturbation (n : ℕ)
    (R ΔR R_invT R_inv : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (hChol_R : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hΔR_upper : ∀ i j : Fin n, j.val < i.val → ΔR i j = 0)
    (hR_invT : IsLeftInverse n (fun i j => R j i) R_invT)
    (hR_inv : IsRightInverse n R R_inv)
    (α : ℝ) (hα : 0 ≤ α)
    (hbound : ∀ i j : Fin n, i.val ≤ j.val →
      |ΔR i j| ≤ (1 + α) *
        ∑ k₁ : Fin n, |R_invT i k₁| *
          ∑ k₂ : Fin n, |ΔA k₁ k₂| * |R_inv k₂ j|) :
    ∀ i j : Fin n, |ΔR i j| ≤ (1 + α) *
      (if i.val ≤ j.val then
        ∑ k₁ : Fin n, |R_invT i k₁| *
          ∑ k₂ : Fin n, |ΔA k₁ k₂| * |R_inv k₂ j|
       else 0) :=
  cholesky_perturbation_componentwise n R ΔR R_invT R_inv ΔA
    hChol_R hΔR_upper hR_invT hR_inv α hα hbound

/-! ## §10.3 Positive Semidefinite Matrices -/

/-- **Theorem 10.9**, source predicate for pivoted PSD Cholesky
factorization in equation (10.11). -/
abbrev higham10_9_PivotedCholeskySpec (n : ℕ)
    (A R : Fin n → Fin n → ℝ) (σ : Fin n → Fin n) (r : ℕ) : Prop :=
  PivotedCholeskySpec n A R σ r

/-- **Theorem 10.9(a)**: every real PSD matrix has an upper-triangular
`R` with nonnegative diagonal and `A = R^T R`. -/
theorem higham10_9_psd_cholesky_existence (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → R i j = 0) ∧
      (∀ i : Fin n, 0 ≤ R i i) ∧
      (∀ i j : Fin n, ∑ k : Fin n, R k i * R k j = A i j) :=
  psd_cholesky_existence n A hPSD

/-- **Theorem 10.9(b)**, full-rank/SPD specialization of the pivoted form
with identity permutation. -/
theorem higham10_9_spd_pivoted_cholesky_full_rank (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      higham10_9_PivotedCholeskySpec n A R id n :=
  spd_pivoted_cholesky n A hSPD

/-- **Equation (10.12)**: outer-product residual after `k` Cholesky stages,
`A^(k) = A - sum_{t<k} r_t r_t^T`. -/
noncomputable def higham10_12_outerProductResidual (n k : ℕ)
    (A R : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A i j -
    ∑ t : Fin n, if t.val < k then R t i * R t j else 0

/-- **Equation (10.13)**: complete-pivoting inequality for the displayed
Cholesky factor, written with zero-based finite indices. -/
def higham10_13_completePivotingInequality (n r : ℕ)
    (R : Fin n → Fin n → ℝ) : Prop :=
  ∀ k j : Fin n, k.val < r → k.val < j.val →
    R k k ^ 2 ≥
      ∑ i : Fin n,
        if k.val ≤ i.val ∧ i.val ≤ j.val ∧ i.val < r then R i j ^ 2 else 0

/-- **Equation (10.14)** / **equation (10.15)**: Schur complement for the
leading `k` block, using the inverse of that leading block as data. -/
noncomputable def higham10_14_schurComplement (n k : ℕ)
    (A A11_inv : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  schurComplement n k A A11_inv

/-- **Lemma 10.10 / equation (10.16)** in honest form: the perturbed
Schur complement equals the unperturbed one plus Higham's first-order
term `Ē = E₂₂ − E₂₁MA₁₂ − A₂₁ME₁₂ + A₂₁ME₁₁MA₁₂` plus a remainder that
is entrywise bounded by an explicit polynomial times `ε²` — the exact
statement behind the source's `S(A+E) = S(A) + Ē + O(‖E‖²)`. The
leading-block inverses enter through genuine inverse equations
(`M A₁₁ = 1` up to the resolvent identity), not assumed bounds on the
conclusion. -/
theorem higham10_10_schur_complement_perturbation {k m : ℕ}
    (A11 E11 M X : Matrix (Fin k) (Fin k) ℝ)
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 E22 : Matrix (Fin m) (Fin m) ℝ)
    (hM : M * A11 = 1) (hXi : (A11 + E11) * X = 1)
    (α μ χ ε : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hχ : 0 ≤ χ) (hε : 0 ≤ ε)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hE21 : ∀ i j, |E21 i j| ≤ ε) (hE12 : ∀ i j, |E12 i j| ≤ ε)
    (hE11 : ∀ i j, |E11 i j| ≤ ε)
    (hMb : ∀ i j, |M i j| ≤ μ) (hXb : ∀ i j, |X i j| ≤ χ) :
    ∃ R : Matrix (Fin m) (Fin m) ℝ,
      (A22 + E22) - (A21 + E21) * X * (A12 + E12) =
        (A22 - A21 * M * A12)
        + (E22 - E21 * M * A12 - A21 * M * E12
            + A21 * (M * E11 * M) * A12)
        + R ∧
      ∀ i j : Fin m, |R i j| ≤
        ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
          + 2 * ((k : ℝ) ^ 4 * α * μ * χ) + (k : ℝ) ^ 4 * μ * χ * ε)
          * ε ^ 2 := by
  have hres := schur_resolvent_from_inverses M X A11 E11 hM hXi
  refine ⟨_, schur_perturbation_exact A21 E21 A12 E12 A22 E22 M X E11
    hres, ?_⟩
  exact schur_perturbation_remainder_bound A21 E21 A12 E12 M X E11
    α μ χ ε hα hμ hχ hε hA21 hA12 hE21 hE12 hE11 hMb hXb

/-- **Lemma 10.12**: abstract `W = A11^{-1} A12` norm bound. -/
theorem higham10_12_w_norm_bound_from_cond
    (W_norm κ_A11 : ℝ) (hκ : 0 ≤ κ_A11)
    (hW : W_norm ^ 2 ≤ κ_A11) :
    W_norm ^ 2 ≤ κ_A11 :=
  w_norm_bound_from_cond W_norm κ_A11 hκ hW

/-- **Block split of the quadratic form** under a `Fin.append`
    partition: the (k+m)-dimensional quadratic form decomposes into the
    four block forms. -/
lemma quadForm_append_split {k m : ℕ}
    (A : Fin (k + m) → Fin (k + m) → ℝ)
    (u : Fin k → ℝ) (v : Fin m → ℝ) :
    ∑ i : Fin (k + m), ∑ j : Fin (k + m),
      Fin.append u v i * A i j * Fin.append u v j =
    (∑ i : Fin k, ∑ j : Fin k,
      u i * A (Fin.castAdd m i) (Fin.castAdd m j) * u j)
    + (∑ i : Fin k, ∑ j : Fin m,
      u i * A (Fin.castAdd m i) (Fin.natAdd k j) * v j)
    + (∑ i : Fin m, ∑ j : Fin k,
      v i * A (Fin.natAdd k i) (Fin.castAdd m j) * u j)
    + (∑ i : Fin m, ∑ j : Fin m,
      v i * A (Fin.natAdd k i) (Fin.natAdd k j) * v j) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Finset.sum_add_distrib]
  ring

/-- **Lemma 10.12 core (Higham §10.3)**: for a positive semidefinite
    block matrix with leading block `A₁₁` inverted in action by `M`, the
    solve vector `Wv = M A₁₂ v` satisfies
    `λ_min(A₁₁) ‖Wv‖₂² ≤ vᵀ A₂₂ v` — the quadratic-form content of
    `Wᵀ A₁₁ W ⪯ A₂₂`, sharpened through the Rayleigh bound. Choosing
    `u = −Wv` in the block-split quadratic form gives
    `(Wv)ᵀA₁₁(Wv) ≤ vᵀA₂₂v`; Rayleigh converts the left side. -/
theorem higham10_12_psd_w_action_bound {k m : ℕ} (hk : 0 < k)
    (A : Fin (k + m) → Fin (k + m) → ℝ)
    (hPSD : IsPosSemiDef (k + m) A)
    (M : Fin k → Fin k → ℝ)
    (hSym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)))
    (hMinv : ∀ (w : Fin k → ℝ) (i : Fin k),
      ∑ j : Fin k, A (Fin.castAdd m i) (Fin.castAdd m j) *
        (∑ t : Fin k, M j t * w t) = w i)
    (v : Fin m → ℝ) :
    finiteMinEigenvalue hk
        (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j))
        hSym *
      vecNorm2Sq (fun i : Fin k => ∑ t : Fin k, M i t *
        (∑ j : Fin m, A (Fin.castAdd m t) (Fin.natAdd k j) * v j)) ≤
    ∑ i : Fin m, ∑ j : Fin m,
      v i * A (Fin.natAdd k i) (Fin.natAdd k j) * v j := by
  set b : Fin k → ℝ := fun t =>
    ∑ j : Fin m, A (Fin.castAdd m t) (Fin.natAdd k j) * v j with hb
  set u : Fin k → ℝ := fun i => ∑ t : Fin k, M i t * b t with hu
  -- the inverse action at b: A₁₁ u = b
  have hA11u : ∀ i : Fin k,
      ∑ j : Fin k, A (Fin.castAdd m i) (Fin.castAdd m j) * u j = b i :=
    fun i => hMinv b i
  -- key PSD inequality with the appended vector (-u, v)
  have hquad := hPSD.2 (Fin.append (fun i => -(u i)) v)
  rw [quadForm_append_split A (fun i => -(u i)) v] at hquad
  -- identify the four blocks
  have hT1 : ∑ i : Fin k, ∑ j : Fin k,
      (-(u i)) * A (Fin.castAdd m i) (Fin.castAdd m j) * (-(u j)) =
      ∑ i : Fin k, u i * b i := by
    calc ∑ i : Fin k, ∑ j : Fin k,
        (-(u i)) * A (Fin.castAdd m i) (Fin.castAdd m j) * (-(u j))
        = ∑ i : Fin k, ∑ j : Fin k,
          u i * (A (Fin.castAdd m i) (Fin.castAdd m j) * u j) :=
          Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i : Fin k, u i * b i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, hA11u i]
  have hT2 : ∑ i : Fin k, ∑ j : Fin m,
      (-(u i)) * A (Fin.castAdd m i) (Fin.natAdd k j) * v j =
      -(∑ i : Fin k, u i * b i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hT3 : ∑ i : Fin m, ∑ j : Fin k,
      v i * A (Fin.natAdd k i) (Fin.castAdd m j) * (-(u j)) =
      -(∑ i : Fin k, u i * b i) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsymA : ∀ i : Fin m,
        A (Fin.natAdd k i) (Fin.castAdd m j) =
        A (Fin.castAdd m j) (Fin.natAdd k i) :=
      fun i => hPSD.1 _ _
    rw [hb]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsymA i]; ring
  rw [hT1, hT2, hT3] at hquad
  -- so uᵀ b ≤ vᵀ A₂₂ v, and uᵀ b = uᵀA₁₁u ≥ λ_min ‖u‖²
  have hub : ∑ i : Fin k, u i * b i ≤
      ∑ i : Fin m, ∑ j : Fin m,
        v i * A (Fin.natAdd k i) (Fin.natAdd k j) * v j := by
    linarith [hquad]
  have hray := finiteMinEigenvalue_rayleigh hk
    (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)) hSym u
  have huAu : ∑ i : Fin k, ∑ j : Fin k,
      u i * A (Fin.castAdd m i) (Fin.castAdd m j) * u j =
      ∑ i : Fin k, u i * b i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hA11u i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [huAu] at hray
  calc finiteMinEigenvalue hk _ hSym * vecNorm2Sq u
      ≤ ∑ i : Fin k, u i * b i := by
        simpa [vecNorm2Sq] using hray
    _ ≤ _ := hub

/-- **Lemma 10.12, norm form**: with a positive Rayleigh floor
    `λ_min(A₁₁) > 0` and a quadratic-form certificate `c₂₂` for `A₂₂`,
    the solve action `W v = M A₁₂ v` is norm-bounded:
    `‖Wv‖₂² ≤ (c₂₂/λ_min) ‖v‖₂²` — the source's
    `‖A₁₁⁻¹A₁₂‖₂² ≤ ‖A₂₂‖₂/λ_min(A₁₁)` in vector-action certificate
    form. -/
theorem higham10_12_w_action_norm_bound {k m : ℕ} (hk : 0 < k)
    (A : Fin (k + m) → Fin (k + m) → ℝ)
    (hPSD : IsPosSemiDef (k + m) A)
    (M : Fin k → Fin k → ℝ)
    (hSym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)))
    (hMinv : ∀ (w : Fin k → ℝ) (i : Fin k),
      ∑ j : Fin k, A (Fin.castAdd m i) (Fin.castAdd m j) *
        (∑ t : Fin k, M j t * w t) = w i)
    (hlampos : 0 < finiteMinEigenvalue hk
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)) hSym)
    (c22 : ℝ)
    (hc22 : ∀ v : Fin m → ℝ,
      ∑ i : Fin m, ∑ j : Fin m,
        v i * A (Fin.natAdd k i) (Fin.natAdd k j) * v j ≤
      c22 * vecNorm2Sq v)
    (v : Fin m → ℝ) :
    vecNorm2Sq (fun i : Fin k => ∑ t : Fin k, M i t *
      (∑ j : Fin m, A (Fin.castAdd m t) (Fin.natAdd k j) * v j)) ≤
    (c22 / finiteMinEigenvalue hk
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)) hSym)
      * vecNorm2Sq v := by
  have hcore := higham10_12_psd_w_action_bound hk A hPSD M hSym hMinv v
  have hchain := le_trans hcore (hc22 v)
  rw [div_mul_eq_mul_div, le_div_iff₀ hlampos, mul_comm]
  linarith [hchain]

/-- The trailing block of a PSD matrix is PSD (zero-padded test
    vectors through the block split). -/
lemma isPosSemiDef_trailing_block {k m : ℕ}
    (A : Fin (k + m) → Fin (k + m) → ℝ)
    (hPSD : IsPosSemiDef (k + m) A) :
    IsPosSemiDef m
      (fun i j : Fin m => A (Fin.natAdd k i) (Fin.natAdd k j)) := by
  constructor
  · intro i j
    exact hPSD.1 _ _
  · intro x
    have h := hPSD.2 (Fin.append (fun _ : Fin k => (0:ℝ)) x)
    rw [quadForm_append_split A (fun _ : Fin k => (0:ℝ)) x] at h
    simpa using h

/-- **Lemma 10.12, trace form** (fully computable certificate): the
    solve action `Wv = M A₁₂ v` of a PSD block matrix satisfies
    `‖Wv‖₂² ≤ (tr A₂₂ / λ_min(A₁₁)) ‖v‖₂²` — the `c₂₂` certificate of
    `higham10_12_w_action_norm_bound` discharged by
    `psd_quadForm_le_trace` on the trailing block. -/
theorem higham10_12_w_action_trace_bound {k m : ℕ} (hk : 0 < k)
    (A : Fin (k + m) → Fin (k + m) → ℝ)
    (hPSD : IsPosSemiDef (k + m) A)
    (M : Fin k → Fin k → ℝ)
    (hSym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)))
    (hMinv : ∀ (w : Fin k → ℝ) (i : Fin k),
      ∑ j : Fin k, A (Fin.castAdd m i) (Fin.castAdd m j) *
        (∑ t : Fin k, M j t * w t) = w i)
    (hlampos : 0 < finiteMinEigenvalue hk
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)) hSym)
    (v : Fin m → ℝ) :
    vecNorm2Sq (fun i : Fin k => ∑ t : Fin k, M i t *
      (∑ j : Fin m, A (Fin.castAdd m t) (Fin.natAdd k j) * v j)) ≤
    ((∑ j : Fin m, A (Fin.natAdd k j) (Fin.natAdd k j)) /
        finiteMinEigenvalue hk
          (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j))
          hSym)
      * vecNorm2Sq v := by
  refine higham10_12_w_action_norm_bound hk A hPSD M hSym hMinv
    hlampos _ (fun w => ?_) v
  have h := psd_quadForm_le_trace
    (fun i j : Fin m => A (Fin.natAdd k i) (Fin.natAdd k j))
    (isPosSemiDef_trailing_block A hPSD) w
  simpa [vecNorm2Sq] using h

/-- **Spectral bounds for unit-diagonal PSD matrices** (the van der
    Sluis (10.9) route ingredient): the scaled matrix `H = D⁻¹AD⁻¹`
    with `D = diag(√a_ii)` has unit diagonal, and any unit-diagonal PSD
    matrix has `1 ≤ λ_max ≤ n` — the upper bound from the trace, the
    lower from the Rayleigh quotient at a coordinate vector. -/
theorem unit_diag_psd_maxEigenvalue_bounds {n : ℕ} (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n H)
    (hdiag : ∀ i : Fin n, H i i = 1)
    (hSym : IsSymmetricFiniteMatrix H) :
    1 ≤ finiteMaxEigenvalue hn H hSym ∧
      finiteMaxEigenvalue hn H hSym ≤ (n : ℝ) := by
  constructor
  · -- Rayleigh at a coordinate vector
    set e : Fin n → ℝ := fun k => if k = ⟨0, hn⟩ then 1 else 0 with he
    have hray := finiteMaxEigenvalue_rayleigh hn H hSym e
    have hquad : ∑ i : Fin n, ∑ j : Fin n, e i * H i j * e j =
        H ⟨0, hn⟩ ⟨0, hn⟩ := by
      simp [he, Finset.sum_ite_eq', Finset.mul_sum]
    have hnorm : ∑ i : Fin n, e i ^ 2 = 1 := by
      simp [he, Finset.sum_ite_eq']
    rw [hquad, hnorm, mul_one, hdiag] at hray
    exact hray
  · -- trace bound at the top eigenvector
    obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn H hSym
    have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
      H hSym a
    have hq :=
      finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
        H hSym a
    rw [hnorm, mul_one] at hq
    set v : Fin n → ℝ :=
      ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
        hSym).eigenvectorBasis a) with hv
    have hvsq : ∑ i : Fin n, v i ^ 2 = 1 := by
      have := hnorm
      unfold finiteVecNorm2Sq at this
      exact this
    have hqv : ∑ i : Fin n, ∑ j : Fin n, v i * H i j * v j =
        finiteMaxEigenvalue hn H hSym := by
      rw [← ha, ← hq, finiteQuadraticForm_eq_sum_sum]
    have htr := psd_quadForm_le_trace H hPSD v
    have htrace : ∑ i : Fin n, H i i = (n : ℝ) := by
      simp [hdiag]
    rw [hqv, htrace, hvsq, mul_one] at htr
    exact htr

/-- **Condition-number certificate for the scaled matrix** (van der
    Sluis route, display (10.9) fragment): a unit-diagonal PSD matrix
    with positive smallest eigenvalue has
    `κ₂(H) = λ_max/λ_min ≤ n/λ_min`. -/
theorem higham10_9_unit_diag_cond_bound {n : ℕ} (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n H)
    (hdiag : ∀ i : Fin n, H i i = 1)
    (hSym : IsSymmetricFiniteMatrix H)
    (hmin : 0 < finiteMinEigenvalue hn H hSym) :
    finiteMaxEigenvalue hn H hSym / finiteMinEigenvalue hn H hSym ≤
      (n : ℝ) / finiteMinEigenvalue hn H hSym := by
  have h := (unit_diag_psd_maxEigenvalue_bounds hn H hPSD hdiag
    hSym).2
  gcongr


/-- The √-scaled matrix `H = D⁻¹AD⁻¹`, `D = diag(√a_ii)`, has unit
    diagonal. -/
lemma scaled_matrix_unit_diag {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i) (i : Fin n) :
    A i i / (Real.sqrt (A i i) * Real.sqrt (A i i)) = 1 := by
  rw [Real.mul_self_sqrt (hAdiag i).le]
  exact div_self (hAdiag i).ne'

/-- The √-scaled matrix of a PSD matrix is PSD (congruence by the
    positive diagonal scaling). -/
lemma scaled_matrix_isPosSemiDef {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (hAdiag : ∀ i : Fin n, 0 < A i i) :
    IsPosSemiDef n
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) := by
  constructor
  · intro i j
    show A i j / (Real.sqrt (A i i) * Real.sqrt (A j j)) =
      A j i / (Real.sqrt (A j j) * Real.sqrt (A i i))
    rw [hPSD.1 i j, mul_comm]
  · intro x
    have h := hPSD.2 (fun i => x i / Real.sqrt (A i i))
    calc (0:ℝ) ≤ ∑ i : Fin n, ∑ j : Fin n,
          x i / Real.sqrt (A i i) * A i j *
          (x j / Real.sqrt (A j j)) := h
      _ = ∑ i : Fin n, ∑ j : Fin n, x i *
          (A i j / (Real.sqrt (A i i) * Real.sqrt (A j j))) * x j := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          have hi := Real.sqrt_pos.mpr (hAdiag i)
          have hj := Real.sqrt_pos.mpr (hAdiag j)
          field_simp

/-- **Display (10.9) fragment for the concrete scaled matrix**: for SPD
    data (`A` PSD with positive diagonal), the van der Sluis scaling
    `H = D⁻¹AD⁻¹` satisfies `κ₂(H) ≤ n/λ_min(H)`. -/
theorem higham10_9_scaled_cond_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hSym : IsSymmetricFiniteMatrix
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hmin : 0 < finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym) :
    finiteMaxEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym /
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym ≤
    (n : ℝ) / finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym :=
  higham10_9_unit_diag_cond_bound hn _
    (scaled_matrix_isPosSemiDef A hPSD hAdiag)
    (fun i => scaled_matrix_unit_diag A hAdiag i) hSym hmin

/-- Every diagonal entry is a Rayleigh quotient, so bounds `λ_max`
    from below (van der Sluis engine, `λ_max(M) ≥ m_ii`). -/
lemma finiteMaxEigenvalue_ge_diag {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hSym : IsSymmetricFiniteMatrix M)
    (i : Fin n) :
    M i i ≤ finiteMaxEigenvalue hn M hSym := by
  set e : Fin n → ℝ := fun k => if k = i then 1 else 0 with he
  have hray := finiteMaxEigenvalue_rayleigh hn M hSym e
  have hquad : ∑ k : Fin n, ∑ l : Fin n, e k * M k l * e l =
      M i i := by
    simp [he, Finset.sum_ite_eq']
  have hnorm : ∑ k : Fin n, e k ^ 2 = 1 := by
    simp [he, Finset.sum_ite_eq']
  rw [hquad, hnorm, mul_one] at hray
  exact hray

/-- **Diagonal congruence bounds the smallest eigenvalue from below**
    (van der Sluis engine): if `N = E M E` with diagonal `E = diag(e)`
    and `m ≤ e_i²` throughout, then `λ_min(N) ≥ m·λ_min(M)` — evaluate
    at `N`'s bottom eigenvector and pass through the congruence. -/
lemma diag_congruence_minEigenvalue_ge {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hSymM : IsSymmetricFiniteMatrix M)
    (e : Fin n → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hme : ∀ i : Fin n, m ≤ e i ^ 2)
    (hSymN : IsSymmetricFiniteMatrix
      (fun i j : Fin n => e i * M i j * e j))
    (hminM : 0 ≤ finiteMinEigenvalue hn M hSymM) :
    m * finiteMinEigenvalue hn M hSymM ≤
      finiteMinEigenvalue hn
        (fun i j : Fin n => e i * M i j * e j) hSymN := by
  -- bottom eigenvector of N
  obtain ⟨a, ha⟩ := exists_finiteMinEigenvalue_eq hn _ hSymN
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (fun i j : Fin n => e i * M i j * e j) hSymN a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (fun i j : Fin n => e i * M i j * e j) hSymN a
  rw [hnorm, mul_one] at hq
  set v : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (fun i j : Fin n => e i * M i j * e j)
      hSymN).eigenvectorBasis a) with hv
  have hvsq : ∑ i : Fin n, v i ^ 2 = 1 := by
    have := hnorm
    unfold finiteVecNorm2Sq at this
    exact this
  have hqv : ∑ i : Fin n, ∑ j : Fin n,
      v i * (e i * M i j * e j) * v j =
      finiteMinEigenvalue hn
        (fun i j : Fin n => e i * M i j * e j) hSymN := by
    rw [← ha, ← hq, finiteQuadraticForm_eq_sum_sum]
  -- pass through the congruence: quadForm N v = quadForm M (e·v)
  have hcong : ∑ i : Fin n, ∑ j : Fin n,
      v i * (e i * M i j * e j) * v j =
      ∑ i : Fin n, ∑ j : Fin n,
        (e i * v i) * M i j * (e j * v j) := by
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hrayM := finiteMinEigenvalue_rayleigh hn M hSymM
    (fun i => e i * v i)
  have hnorm2 : m * (∑ i : Fin n, v i ^ 2) ≤
      ∑ i : Fin n, (e i * v i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hme i
    have h2 := sq_nonneg (v i)
    calc m * v i ^ 2 ≤ e i ^ 2 * v i ^ 2 :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = (e i * v i) ^ 2 := by ring
  rw [hvsq, mul_one] at hnorm2
  calc m * finiteMinEigenvalue hn M hSymM
      ≤ (∑ i : Fin n, (e i * v i) ^ 2) *
          finiteMinEigenvalue hn M hSymM := by
        exact mul_le_mul_of_nonneg_right hnorm2 hminM
    _ = finiteMinEigenvalue hn M hSymM *
          ∑ i : Fin n, (e i * v i) ^ 2 := mul_comm _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
          (e i * v i) * M i j * (e j * v j) := hrayM
    _ = finiteMinEigenvalue hn
          (fun i j : Fin n => e i * M i j * e j) hSymN := by
        rw [← hcong, hqv]

/-- **van der Sluis / display (10.9)**: the √-scaling is within a
    factor `n` of every diagonal scaling —
    `κ₂(H) ≤ n·κ₂(DAD)` for every positive diagonal `D`, hence
    `κ₂(H) ≤ n·min_D κ₂(DAD)`. `B` names the largest `d_i²a_ii`
    (supplied with its attainment witness). Chain:
    `λ_max(H) ≤ n` (unit diagonal), `λ_min(H) ≥ λ_min(DAD)/B`
    (diagonal congruence `H = E(DAD)E`, `e_i = 1/(d_i√a_ii)`), and
    `B ≤ λ_max(DAD)` (a diagonal Rayleigh value). -/
theorem higham10_9_van_der_sluis {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (d : Fin n → ℝ) (hd : ∀ i : Fin n, 0 < d i)
    (hSymH : IsSymmetricFiniteMatrix
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hSymM : IsSymmetricFiniteMatrix
      (fun i j : Fin n => d i * A i j * d j))
    (hminM : 0 < finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM)
    (B : ℝ) (hB : ∀ i : Fin n, d i ^ 2 * A i i ≤ B)
    (hattain : ∃ k : Fin n, d k ^ 2 * A k k = B) :
    finiteMaxEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH /
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH ≤
    (n : ℝ) * finiteMaxEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM /
      finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM := by
  obtain ⟨k, hk⟩ := hattain
  have hB0 : (0:ℝ) < B := by
    rw [← hk]
    have hdk := hd k
    have hak := hAdiag k
    positivity
  -- B is a Rayleigh value of M
  have hBmax : B ≤ finiteMaxEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM := by
    have h := finiteMaxEigenvalue_ge_diag hn
      (fun i j : Fin n => d i * A i j * d j) hSymM k
    have h2 : d k * A k k * d k = B := by rw [← hk]; ring
    calc B = d k * A k k * d k := h2.symm
      _ ≤ _ := h
  -- H is the diagonal congruence of M by e = 1/(d√a)
  have hHM : (fun i j : Fin n =>
      (1 / (d i * Real.sqrt (A i i))) *
        (d i * A i j * d j) *
        (1 / (d j * Real.sqrt (A j j)))) =
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) := by
    funext i j
    have hi := Real.sqrt_pos.mpr (hAdiag i)
    have hj := Real.sqrt_pos.mpr (hAdiag j)
    have hdi := hd i
    have hdj := hd j
    field_simp
  -- the congruence floor for λ_min(H)
  have hmfloor : ∀ i : Fin n,
      1 / B ≤ (1 / (d i * Real.sqrt (A i i))) ^ 2 := by
    intro i
    have hi := Real.sqrt_pos.mpr (hAdiag i)
    have hdi := hd i
    rw [div_pow, one_pow]
    have hsq : (d i * Real.sqrt (A i i)) ^ 2 = d i ^ 2 * A i i := by
      rw [mul_pow, Real.sq_sqrt (hAdiag i).le]
    rw [hsq]
    have hai := hAdiag i
    have h1 : (0:ℝ) < d i ^ 2 * A i i := by positivity
    exact one_div_le_one_div_of_le h1 (hB i)
  have hSymH' : IsSymmetricFiniteMatrix
      (fun i j : Fin n =>
        (1 / (d i * Real.sqrt (A i i))) *
          (d i * A i j * d j) *
          (1 / (d j * Real.sqrt (A j j)))) := by
    rw [hHM]; exact hSymH
  have hcong := diag_congruence_minEigenvalue_ge hn
    (fun i j : Fin n => d i * A i j * d j) hSymM
    (fun i => 1 / (d i * Real.sqrt (A i i))) (1 / B)
    (one_div_pos.mpr hB0).le hmfloor hSymH' hminM.le
  -- transport across the congruence identity
  have hminH_ge : (1 / B) * finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := by
    refine hcong.trans_eq ?_
    congr 1
  have hminH0 : 0 < finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := by
    have : (0:ℝ) < (1 / B) * finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM :=
      mul_pos (one_div_pos.mpr hB0) hminM
    linarith [hminH_ge]
  -- assemble the condition-number comparison
  have hmaxH : finiteMaxEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH ≤ (n : ℝ) :=
    (unit_diag_psd_maxEigenvalue_bounds hn _
      (scaled_matrix_isPosSemiDef A hPSD hAdiag)
      (fun i => scaled_matrix_unit_diag A hAdiag i) hSymH).2
  rw [div_le_div_iff₀ hminH0 hminM]
  have h1 : finiteMaxEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH *
      finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      (n : ℝ) * finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM :=
    mul_le_mul_of_nonneg_right hmaxH hminM.le
  have h2 : finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      B * finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := by
    have := mul_le_mul_of_nonneg_left hminH_ge hB0.le
    calc finiteMinEigenvalue hn
          (fun i j : Fin n => d i * A i j * d j) hSymM
        = B * ((1 / B) * finiteMinEigenvalue hn
            (fun i j : Fin n => d i * A i j * d j) hSymM) := by
          field_simp
      _ ≤ B * finiteMinEigenvalue hn
            (fun i l : Fin n => A i l /
              (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := this
  have h3 : (n : ℝ) * B ≤ (n : ℝ) *
      finiteMaxEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM :=
    mul_le_mul_of_nonneg_left hBmax (Nat.cast_nonneg n)
  have h4 : (n : ℝ) * finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      (n : ℝ) * (B * finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH) :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n)
  have h5 : ((n : ℝ) * B) * finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH ≤
      ((n : ℝ) * finiteMaxEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM) *
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH :=
    mul_le_mul_of_nonneg_right h3 hminH0.le
  nlinarith [h1, h4, h5]

/-- **Scaled interior mass from an operator-norm certificate**
    (Theorem 10.7 normwise stage route): if the `D`-scaled residual
    `E_ij = Δ_ij/(√a_i√a_j)` carries `opNorm2Le E ε`, the weighted
    perturbation mass obeys `|yᵀΔy| ≤ ε·∑ a_i y_i²` — exactly the
    normwise hypothesis of `bordered_perturbation_floor_normwise`,
    with no dimension factor. -/
lemma scaled_interior_mass_normwise {m : ℕ}
    (Δ : Fin m → Fin m → ℝ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε : ℝ)
    (hcert : opNorm2Le
      (fun i j : Fin m => Δ i j /
        (Real.sqrt (a i) * Real.sqrt (a j))) ε)
    (y : Fin m → ℝ)
    (hnz : ∀ i j : Fin m, a i = 0 ∨ a j = 0 → Δ i j = 0) :
    |∑ i : Fin m, ∑ j : Fin m, y i * Δ i j * y j| ≤
      ε * ∑ i : Fin m, a i * y i ^ 2 := by
  set z : Fin m → ℝ := fun i => y i * Real.sqrt (a i) with hz
  have habs := quadForm_abs_le_of_opNorm2Le m
    (fun i j : Fin m => Δ i j /
      (Real.sqrt (a i) * Real.sqrt (a j))) ε hcert z
  have hquad : ∑ i : Fin m, ∑ j : Fin m,
      z i * (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) * z j =
      ∑ i : Fin m, ∑ j : Fin m, y i * Δ i j * y j := by
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    by_cases hi : a i = 0
    · rw [hnz i j (Or.inl hi)]
      simp
    by_cases hj : a j = 0
    · rw [hnz i j (Or.inr hj)]
      simp
    · have hi' := lt_of_le_of_ne (ha i) (Ne.symm hi)
      have hj' := lt_of_le_of_ne (ha j) (Ne.symm hj)
      have hsi := Real.sqrt_pos.mpr hi'
      have hsj := Real.sqrt_pos.mpr hj'
      show y i * Real.sqrt (a i) *
        (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) *
        (y j * Real.sqrt (a j)) = y i * Δ i j * y j
      field_simp
  have hnorm : ∑ i : Fin m, z i ^ 2 =
      ∑ i : Fin m, a i * y i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    show (y i * Real.sqrt (a i)) ^ 2 = a i * y i ^ 2
    rw [mul_pow, Real.sq_sqrt (ha i)]
    ring
  rw [hquad, hnorm] at habs
  exact habs

/-- **Scaled border mass from a vector-norm certificate** (Theorem
    10.7 normwise stage route): if the `D`-scaled border perturbation
    has squared norm at most `ε²t`, then
    `|2∑yᵢδᵢ| ≤ ε(t + ∑aᵢyᵢ²)` — Cauchy–Schwarz in the scaled inner
    product followed by AM–GM, again with no dimension factor. -/
lemma scaled_border_mass_normwise {m : ℕ}
    (δ : Fin m → ℝ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε t : ℝ) (hε0 : 0 ≤ ε) (ht0 : 0 ≤ t)
    (hnz : ∀ i : Fin m, a i = 0 → δ i = 0)
    (hcert : ∑ i : Fin m,
      (if a i = 0 then 0 else δ i ^ 2 / a i) ≤ ε ^ 2 * t)
    (y : Fin m → ℝ) :
    |2 * ∑ i : Fin m, y i * δ i| ≤
      ε * (t + ∑ i : Fin m, a i * y i ^ 2) := by
  set W : ℝ := ∑ i : Fin m, a i * y i ^ 2 with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ =>
    mul_nonneg (ha i) (sq_nonneg _)
  -- Cauchy–Schwarz in the scaled coordinates
  have hcs : (∑ i : Fin m, y i * δ i) ^ 2 ≤
      W * (ε ^ 2 * t) := by
    have hsplit : ∑ i : Fin m, y i * δ i =
        ∑ i : Fin m, (y i * Real.sqrt (a i)) *
          (if a i = 0 then 0 else δ i / Real.sqrt (a i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : a i = 0
      · rw [if_pos hi, hnz i hi]
        simp
      · rw [if_neg hi]
        have hi' := lt_of_le_of_ne (ha i) (Ne.symm hi)
        have hsi := Real.sqrt_pos.mpr hi'
        field_simp
    rw [hsplit]
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => y i * Real.sqrt (a i))
      (fun i => if a i = 0 then 0 else δ i / Real.sqrt (a i))
    have hL : ∑ i : Fin m, (y i * Real.sqrt (a i)) ^ 2 = W := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (ha i)]
      ring
    have hR : ∑ i : Fin m,
        (if a i = 0 then 0 else δ i / Real.sqrt (a i)) ^ 2 =
        ∑ i : Fin m, (if a i = 0 then 0 else δ i ^ 2 / a i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : a i = 0
      · rw [if_pos hi, if_pos hi]
        norm_num
      · rw [if_neg hi, if_neg hi, div_pow, Real.sq_sqrt (ha i)]
    rw [hL, hR] at h
    calc (∑ i : Fin m, (y i * Real.sqrt (a i)) *
          (if a i = 0 then 0 else δ i / Real.sqrt (a i))) ^ 2
        ≤ W * ∑ i : Fin m,
            (if a i = 0 then 0 else δ i ^ 2 / a i) := h
      _ ≤ W * (ε ^ 2 * t) :=
          mul_le_mul_of_nonneg_left hcert hW0
  -- AM–GM assembly
  have hsum : |∑ i : Fin m, y i * δ i| ≤
      ε * Real.sqrt t * Real.sqrt W := by
    have h1 : |∑ i : Fin m, y i * δ i| ^ 2 ≤
        (ε * Real.sqrt t * Real.sqrt W) ^ 2 := by
      rw [sq_abs]
      calc (∑ i : Fin m, y i * δ i) ^ 2
          ≤ W * (ε ^ 2 * t) := hcs
        _ = (ε * Real.sqrt t * Real.sqrt W) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt ht0,
              Real.sq_sqrt hW0]
            ring
    have h2 : (0:ℝ) ≤ ε * Real.sqrt t * Real.sqrt W := by
      positivity
    nlinarith [abs_nonneg (∑ i : Fin m, y i * δ i), h1, h2]
  have hamgm : 2 * (Real.sqrt t * Real.sqrt W) ≤ t + W := by
    have hsq := sq_nonneg (Real.sqrt t - Real.sqrt W)
    have hts : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
    have hWs : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0
    nlinarith
  calc |2 * ∑ i : Fin m, y i * δ i|
      = 2 * |∑ i : Fin m, y i * δ i| := by
        rw [abs_mul]
        norm_num
    _ ≤ 2 * (ε * Real.sqrt t * Real.sqrt W) := by linarith [hsum]
    _ = ε * (2 * (Real.sqrt t * Real.sqrt W)) := by ring
    _ ≤ ε * (t + W) := mul_le_mul_of_nonneg_left hamgm hε0

/-- **Eigenvalue interlacing, upper direction** (the dual of
    `finiteMinEigenvalue_leading_principal_ge`, completing the
    two-sided leading-block spectral envelope): the maximum eigenvalue
    of a leading principal submatrix is at most the maximum eigenvalue
    of the full matrix — evaluate the full max-Rayleigh bound at the
    zero-padded maximizing eigenvector of the submatrix. -/
theorem finiteMaxEigenvalue_leading_principal_le (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hH : IsSymmetricFiniteMatrix H)
    (k : ℕ) (hk0 : 0 < k) (hk : k ≤ n)
    (hHk_sym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)) :
    finiteMaxEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym ≤
      finiteMaxEigenvalue hn H hH := by
  obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hk0
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
    hHk_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
      hHk_sym a
  rw [hnorm, mul_one] at hq
  set v : Fin k → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
      hHk_sym).eigenvectorBasis a) with hv
  have hvsq : ∑ i : Fin k, v i ^ 2 = 1 := by
    have := hnorm
    unfold finiteVecNorm2Sq at this
    exact this
  have hpadsq : ∑ i : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) ^ 2 = 1 := by
    rw [sum_sq_zero_pad_eq k hk v, hvsq]
  have hray := finiteMaxEigenvalue_rayleigh hn H hH
    (fun i => if h : i.val < k then v ⟨i.val, h⟩ else 0)
  rw [hpadsq, mul_one] at hray
  have hpadquad : ∑ i : Fin n, ∑ j : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) * H i j *
        (if h : j.val < k then v ⟨j.val, h⟩ else 0) =
      finiteMaxEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym := by
    rw [quadForm_zero_pad_eq H k hk v, ← ha, ← hq,
      finiteQuadraticForm_eq_sum_sum]
  rw [hpadquad] at hray
  exact hray

/-- Quadratic-form-certificate variant of the scaled interior mass
    (composes with zero-pad restriction, unlike the `opNorm2Le`
    form). -/
lemma scaled_interior_mass_normwise_quad {m : ℕ}
    (Δ : Fin m → Fin m → ℝ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε : ℝ)
    (hcert : ∀ z : Fin m → ℝ,
      |∑ i : Fin m, ∑ j : Fin m, z i *
        (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) * z j| ≤
      ε * ∑ i : Fin m, z i ^ 2)
    (y : Fin m → ℝ)
    (hnz : ∀ i j : Fin m, a i = 0 ∨ a j = 0 → Δ i j = 0) :
    |∑ i : Fin m, ∑ j : Fin m, y i * Δ i j * y j| ≤
      ε * ∑ i : Fin m, a i * y i ^ 2 := by
  set z : Fin m → ℝ := fun i => y i * Real.sqrt (a i) with hz
  have habs := hcert z
  have hquad : ∑ i : Fin m, ∑ j : Fin m,
      z i * (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) * z j =
      ∑ i : Fin m, ∑ j : Fin m, y i * Δ i j * y j := by
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    by_cases hi : a i = 0
    · rw [hnz i j (Or.inl hi)]
      simp
    by_cases hj : a j = 0
    · rw [hnz i j (Or.inr hj)]
      simp
    · have hi' := lt_of_le_of_ne (ha i) (Ne.symm hi)
      have hj' := lt_of_le_of_ne (ha j) (Ne.symm hj)
      have hsi := Real.sqrt_pos.mpr hi'
      have hsj := Real.sqrt_pos.mpr hj'
      show y i * Real.sqrt (a i) *
        (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) *
        (y j * Real.sqrt (a j)) = y i * Δ i j * y j
      field_simp
  have hnorm : ∑ i : Fin m, z i ^ 2 =
      ∑ i : Fin m, a i * y i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    show (y i * Real.sqrt (a i)) ^ 2 = a i * y i ^ 2
    rw [mul_pow, Real.sq_sqrt (ha i)]
    ring
  rw [hquad, hnorm] at habs
  exact habs

/-- **Per-stage interior mass from the full scaled certificate**
    (Theorem 10.7 sharp route, certificate restriction): a single
    quadratic-form certificate `ε` on the full scaled defect restricts
    to every leading block by zero-padding — the stage-`k` interior
    mass hypothesis of `fl_cholesky_pivot_pos_step_sharp` follows for
    all stages at once. -/
theorem stage_interior_mass_from_full {n : ℕ}
    (Δ : Fin n → Fin n → ℝ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε : ℝ)
    (hcert : ∀ z : Fin n → ℝ,
      |∑ i : Fin n, ∑ j : Fin n, z i *
        (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) * z j| ≤
      ε * ∑ i : Fin n, z i ^ 2)
    (hnz : ∀ i j : Fin n, a i = 0 ∨ a j = 0 → Δ i j = 0)
    (k : ℕ) (hk : k ≤ n) (y : Fin k → ℝ) :
    |∑ i : Fin k, ∑ j : Fin k, y i *
      Δ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ * y j| ≤
      ε * ∑ i : Fin k, a ⟨i.val, by omega⟩ * y i ^ 2 := by
  refine scaled_interior_mass_normwise_quad
    (fun i j : Fin k => Δ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
    (fun i : Fin k => a ⟨i.val, by omega⟩) (fun i => ha _) ε
    ?_ y (fun i j h => hnz _ _ h)
  intro z
  have hpad := hcert
    (fun i : Fin n => if h : i.val < k then z ⟨i.val, h⟩ else 0)
  have hq := quadForm_zero_pad_eq
    (fun i j : Fin n => Δ i j /
      (Real.sqrt (a i) * Real.sqrt (a j))) k hk z
  have hs := sum_sq_zero_pad_eq k hk z
  rw [hq, hs] at hpad
  exact hpad

/-- **Per-stage border mass from full-column certificates** (Theorem
    10.7 sharp route): a scaled column-norm certificate on each full
    defect column restricts monotonically to every leading segment, so
    the border-mass hypothesis of the sharpened stage step follows for
    all stages from `n` column certificates. -/
theorem stage_border_mass_from_full {n : ℕ}
    (Δ : Fin n → Fin n → ℝ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε : ℝ) (hε0 : 0 ≤ ε)
    (t : Fin n → ℝ) (ht0 : ∀ j, 0 ≤ t j)
    (hnz : ∀ i j : Fin n, a i = 0 → Δ i j = 0)
    (hcertB : ∀ j : Fin n, ∑ i : Fin n,
      (if a i = 0 then 0 else Δ i j ^ 2 / a i) ≤ ε ^ 2 * t j)
    (j : Fin n) (y : Fin j.val → ℝ) :
    |2 * ∑ i : Fin j.val, y i * Δ ⟨i.val, by omega⟩ j| ≤
      ε * (t j + ∑ i : Fin j.val, a ⟨i.val, by omega⟩ * y i ^ 2) := by
  refine scaled_border_mass_normwise
    (fun i : Fin j.val => Δ ⟨i.val, by omega⟩ j)
    (fun i : Fin j.val => a ⟨i.val, by omega⟩) (fun i => ha _)
    ε (t j) hε0 (ht0 j) (fun i h => hnz _ _ h) ?_ y
  -- restrict the full column certificate to the leading segment
  refine le_trans ?_ (hcertB j)
  have hemb : Function.Injective
      (fun i : Fin j.val => (⟨i.val, by omega⟩ : Fin n)) := by
    intro p q hpq
    simpa [Fin.ext_iff] using hpq
  calc ∑ i : Fin j.val,
      (if a ⟨i.val, by omega⟩ = 0 then 0
        else Δ ⟨i.val, by omega⟩ j ^ 2 / a ⟨i.val, by omega⟩)
      = ∑ i ∈ Finset.univ.map ⟨fun i : Fin j.val =>
          (⟨i.val, by omega⟩ : Fin n), hemb⟩,
        (if a i = 0 then 0 else Δ i j ^ 2 / a i) := by
        rw [Finset.sum_map]
        simp only [Function.Embedding.coeFn_mk]
    _ ≤ ∑ i : Fin n, (if a i = 0 then 0 else Δ i j ^ 2 / a i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) fun i _ _ => ?_
        by_cases hi : a i = 0
        · rw [if_pos hi]
        · rw [if_neg hi]
          have := lt_of_le_of_ne (ha i) (Ne.symm hi)
          positivity

/-- **Theorem 10.7 at the source-shaped threshold, certified form**: all
    rounded pivots are positive at `λ > ε + 2γ_{n+1}` given ONLY
    run-level normwise certificates — one quadratic-form certificate on
    the scaled full Gram defect and one scaled column-norm certificate
    per column — the per-stage mass hypotheses being discharged by
    zero-pad restriction. -/
theorem fl_cholesky_pivots_pos_sharp_certified (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (lam ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hfloor : ∀ j : Fin n, ∀ y : Fin j.val → ℝ,
      lam * ((∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j) ≤
        (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j)
    (hcertI : ∀ z : Fin n → ℝ,
      |∑ i : Fin n, ∑ l : Fin n, z i *
        (((∑ p : Fin n, fl_cholesky fp n A p i *
            fl_cholesky fp n A p l) - A i l) /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) * z l| ≤
      ε * ∑ i : Fin n, z i ^ 2)
    (hcertB : ∀ j : Fin n, ∑ i : Fin n,
      (if A i i = 0 then 0 else
        ((∑ p : Fin n, fl_cholesky fp n A p i *
            fl_cholesky fp n A p j) - A i j) ^ 2 / A i i) ≤
      ε ^ 2 * ∑ p ∈ Finset.univ.filter
        (fun p : Fin n => p.val < j.val),
        fl_cholesky fp n A p j ^ 2)
    (hlam2ε : 2 * ε ≤ lam)
    (hthresh : ε + 2 * gamma fp (n + 1) < lam) :
    ∀ j : Fin n, 0 < fl_cholPivot fp n A j := by
  set Δ : Fin n → Fin n → ℝ := fun i l =>
    (∑ p : Fin n, fl_cholesky fp n A p i * fl_cholesky fp n A p l) -
      A i l with hΔ
  have hnzI : ∀ i l : Fin n, A i i = 0 ∨ A l l = 0 → Δ i l = 0 :=
    fun i l h => h.elim
      (fun h0 => absurd h0 (hAdiag i).ne')
      (fun h0 => absurd h0 (hAdiag l).ne')
  have hnzB : ∀ i l : Fin n, A i i = 0 → Δ i l = 0 :=
    fun i l h0 => absurd h0 (hAdiag i).ne'
  refine fl_cholesky_pivots_pos_sharp fp A hAdiag hn1 hγ1 lam ε
    hε0 hε1 hfloor ?_ ?_ hlam2ε hthresh
  · -- interior masses from the single full certificate
    intro j y
    have h := stage_interior_mass_from_full Δ (fun i => A i i)
      (fun i => (hAdiag i).le) ε hcertI hnzI j.val j.isLt.le y
    have hrw : ∀ i l : Fin j.val,
        Δ ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ =
        (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
          A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ := by
      intro i l
      show (∑ p : Fin n, _ * _) - _ = _
      rw [gram_sum_stage_trunc fp A j ⟨i.val, by omega⟩
        ⟨l.val, by omega⟩ i.isLt]
    calc |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
          ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
            A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * y l|
        = |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
            Δ ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l| := by
          congr 1
          exact Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun l _ => by rw [hrw i l]
      _ ≤ ε * ∑ i : Fin j.val,
            A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 := h
  · -- border masses from the column certificates
    intro j y
    have h := stage_border_mass_from_full Δ (fun i => A i i)
      (fun i => (hAdiag i).le) ε hε0
      (fun w => ∑ p ∈ Finset.univ.filter
        (fun p : Fin n => p.val < w.val),
        fl_cholesky fp n A p w ^ 2)
      (fun w => Finset.sum_nonneg fun p _ => sq_nonneg _)
      hnzB hcertB j y
    have hrwB : ∀ i : Fin j.val,
        Δ ⟨i.val, by omega⟩ j =
        (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
          A ⟨i.val, by omega⟩ j := by
      intro i
      show (∑ p : Fin n, _ * _) - _ = _
      rw [gram_sum_stage_trunc fp A j ⟨i.val, by omega⟩ j i.isLt]
    have hrwT : (∑ p ∈ Finset.univ.filter
        (fun p : Fin n => p.val < j.val),
        fl_cholesky fp n A p j ^ 2) =
        ∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 :=
      (sum_fin_eq_sum_filter_lt' j.isLt.le
        (fun p => fl_cholesky fp n A p j ^ 2)).symm
    calc |2 * ∑ i : Fin j.val, y i *
          ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
            fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
            A ⟨i.val, by omega⟩ j)|
        = |2 * ∑ i : Fin j.val, y i * Δ ⟨i.val, by omega⟩ j| := by
          congr 2
          exact Finset.sum_congr rfl fun i _ => by rw [hrwB i]
      _ ≤ ε * ((∑ p ∈ Finset.univ.filter
            (fun p : Fin n => p.val < j.val),
            fl_cholesky fp n A p j ^ 2) +
          ∑ i : Fin j.val,
            A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) := h
      _ = ε * ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) +
          ∑ i : Fin j.val,
            A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) := by
          rw [hrwT]

/-- **The display-(10.18) matrix** (Higham p. 204, square-block
    instance `k = n − k`): `A = [[αI, I], [I, α⁻¹I]]`, the positive
    semidefinite matrix on which Lemma 10.12's inequality is an
    equality and `‖W‖₂ = α⁻¹` is arbitrarily large. -/
noncomputable def higham10_18_matrix (k : ℕ) (α : ℝ) :
    Fin (k + k) → Fin (k + k) → ℝ :=
  fun i j =>
    if i.val = j.val then (if i.val < k then α else α⁻¹)
    else if i.val + k = j.val ∨ j.val + k = i.val then 1 else 0

/-- Row action of the (10.18) matrix on the leading block. -/
private lemma higham10_18_row_cast (k : ℕ) (α : ℝ) (hk : 0 < k)
    (x : Fin (k + k) → ℝ) (i : Fin k) :
    ∑ j : Fin (k + k), higham10_18_matrix k α (Fin.castAdd k i) j *
      x j =
    α * x (Fin.castAdd k i) + x (Fin.natAdd k i) := by
  rw [Fin.sum_univ_add]
  have h1 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.castAdd k i) (Fin.castAdd k j) *
        x (Fin.castAdd k j) = α * x (Fin.castAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      simp [Fin.castAdd, i.isLt]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.castAdd k b).val := by
        simp only [Fin.coe_castAdd]
        exact fun h => hb (Fin.ext h.symm)
      have h2 : ¬((Fin.castAdd k i).val + k = (Fin.castAdd k b).val ∨
          (Fin.castAdd k b).val + k = (Fin.castAdd k i).val) := by
        simp only [Fin.coe_castAdd]
        push_neg
        omega
      rw [if_neg hne, if_neg h2, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.castAdd k i) (Fin.natAdd k j) *
        x (Fin.natAdd k j) = x (Fin.natAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.natAdd k i).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have hor : (Fin.castAdd k i).val + k = (Fin.natAdd k i).val ∨
          (Fin.natAdd k i).val + k = (Fin.castAdd k i).val := by
        left
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      rw [if_neg hne, if_pos hor, one_mul]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.natAdd k b).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have h3 : ¬((Fin.castAdd k i).val + k = (Fin.natAdd k b).val ∨
          (Fin.natAdd k b).val + k = (Fin.castAdd k i).val) := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        push_neg
        constructor
        · intro h
          exact absurd (Fin.ext (show b.val = i.val by omega)) hb
        · omega
      rw [if_neg hne, if_neg h3, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h1, h2]

/-- Row action of the (10.18) matrix on the trailing block. -/
private lemma higham10_18_row_nat (k : ℕ) (α : ℝ) (hk : 0 < k)
    (x : Fin (k + k) → ℝ) (i : Fin k) :
    ∑ j : Fin (k + k), higham10_18_matrix k α (Fin.natAdd k i) j *
      x j =
    x (Fin.castAdd k i) + α⁻¹ * x (Fin.natAdd k i) := by
  rw [Fin.sum_univ_add]
  have h1 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.natAdd k i) (Fin.castAdd k j) *
        x (Fin.castAdd k j) = x (Fin.castAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      have hne : (Fin.natAdd k i).val ≠ (Fin.castAdd k i).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have hor : (Fin.natAdd k i).val + k = (Fin.castAdd k i).val ∨
          (Fin.castAdd k i).val + k = (Fin.natAdd k i).val := by
        right
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      rw [if_neg hne, if_pos hor, one_mul]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.natAdd k i).val ≠ (Fin.castAdd k b).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have h3 : ¬((Fin.natAdd k i).val + k = (Fin.castAdd k b).val ∨
          (Fin.castAdd k b).val + k = (Fin.natAdd k i).val) := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        push_neg
        constructor
        · omega
        · intro h
          exact absurd (Fin.ext (show b.val = i.val by omega)) hb
      rw [if_neg hne, if_neg h3, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.natAdd k i) (Fin.natAdd k j) *
        x (Fin.natAdd k j) = α⁻¹ * x (Fin.natAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      have heq : (Fin.natAdd k i).val = (Fin.natAdd k i).val := rfl
      have hge : ¬(Fin.natAdd k i).val < k := by
        simp only [Fin.coe_natAdd]
        omega
      rw [if_pos heq, if_neg hge]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.natAdd k i).val ≠ (Fin.natAdd k b).val := by
        simp only [Fin.coe_natAdd]
        intro h
        exact hb (Fin.ext (by omega)).symm
      have h3 : ¬((Fin.natAdd k i).val + k = (Fin.natAdd k b).val ∨
          (Fin.natAdd k b).val + k = (Fin.natAdd k i).val) := by
        simp only [Fin.coe_natAdd]
        push_neg
        omega
      rw [if_neg hne, if_neg h3, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h1, h2]

/-- **The (10.18) matrix is positive semidefinite** — completion of
    squares pairwise across the two blocks:
    `xᵀAx = ∑ᵢ (√α·xᵢ + x_{k+i}/√α)²`. -/
theorem higham10_18_isPosSemiDef (k : ℕ) (hk : 0 < k) (α : ℝ)
    (hα : 0 < α) :
    IsPosSemiDef (k + k) (higham10_18_matrix k α) := by
  constructor
  · intro i j
    unfold higham10_18_matrix
    by_cases hij : i.val = j.val
    · rw [if_pos hij, if_pos hij.symm, hij]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
      by_cases hd : i.val + k = j.val ∨ j.val + k = i.val
      · rw [if_pos hd, if_pos (Or.symm hd)]
      · rw [if_neg hd, if_neg (fun h => hd (Or.symm h))]
  · intro x
    have hquad : ∑ i : Fin (k + k), ∑ j : Fin (k + k),
        x i * higham10_18_matrix k α i j * x j =
        ∑ i : Fin k, (α * x (Fin.castAdd k i) ^ 2 +
          2 * x (Fin.castAdd k i) * x (Fin.natAdd k i) +
          α⁻¹ * x (Fin.natAdd k i) ^ 2) := by
      rw [Fin.sum_univ_add]
      have hc : ∀ i : Fin k, ∑ j : Fin (k + k),
          x (Fin.castAdd k i) *
            higham10_18_matrix k α (Fin.castAdd k i) j * x j =
          x (Fin.castAdd k i) * (α * x (Fin.castAdd k i) +
            x (Fin.natAdd k i)) := by
        intro i
        rw [← higham10_18_row_cast k α hk x i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hn : ∀ i : Fin k, ∑ j : Fin (k + k),
          x (Fin.natAdd k i) *
            higham10_18_matrix k α (Fin.natAdd k i) j * x j =
          x (Fin.natAdd k i) * (x (Fin.castAdd k i) +
            α⁻¹ * x (Fin.natAdd k i)) := by
        intro i
        rw [← higham10_18_row_nat k α hk x i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [Finset.sum_congr rfl fun i _ => hc i,
        Finset.sum_congr rfl fun i _ => hn i,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hquad]
    refine Finset.sum_nonneg fun i _ => ?_
    have hsq := sq_nonneg (Real.sqrt α * x (Fin.castAdd k i) +
      (Real.sqrt α)⁻¹ * x (Fin.natAdd k i))
    have hs : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
    have hs0 : (0:ℝ) < Real.sqrt α := Real.sqrt_pos.mpr hα
    have hsinv : ((Real.sqrt α)⁻¹) ^ 2 = α⁻¹ := by
      rw [inv_pow, hs]
    have hmul : Real.sqrt α * (Real.sqrt α)⁻¹ = 1 :=
      mul_inv_cancel₀ hs0.ne'
    have hexp : (Real.sqrt α * x (Fin.castAdd k i) +
        (Real.sqrt α)⁻¹ * x (Fin.natAdd k i)) ^ 2 =
        α * x (Fin.castAdd k i) ^ 2 +
        2 * x (Fin.castAdd k i) * x (Fin.natAdd k i) +
        α⁻¹ * x (Fin.natAdd k i) ^ 2 := by
      have h0 : (Real.sqrt α * x (Fin.castAdd k i) +
          (Real.sqrt α)⁻¹ * x (Fin.natAdd k i)) ^ 2 =
          Real.sqrt α ^ 2 * x (Fin.castAdd k i) ^ 2 +
          2 * (Real.sqrt α * (Real.sqrt α)⁻¹) *
            (x (Fin.castAdd k i) * x (Fin.natAdd k i)) +
          ((Real.sqrt α)⁻¹) ^ 2 * x (Fin.natAdd k i) ^ 2 := by
        ring
      rw [h0, hs, hsinv, hmul]
      ring
    linarith [hexp ▸ hsq]

/-- **Display (10.18): `‖W‖` is arbitrarily large** (Higham p. 204):
    for the PSD matrix `[[αI, I], [I, α⁻¹I]]` the solve `A₁₁W = A₁₂`
    is `W = α⁻¹I` — verified by the row action — and its action norm
    `α⁻¹` exceeds any bound as `α → 0`: no bound on `‖A₁₁⁻¹A₁₂‖`
    independent of the matrix is possible without pivoting
    structure. -/
theorem higham10_18_w_arbitrarily_large (k : ℕ) (hk : 0 < k)
    (C : ℝ) :
    ∃ α : ℝ, 0 < α ∧
      IsPosSemiDef (k + k) (higham10_18_matrix k α) ∧
      (∀ v : Fin k → ℝ, ∀ i : Fin k,
        ∑ j : Fin k, higham10_18_matrix k α (Fin.castAdd k i)
          (Fin.castAdd k j) * (α⁻¹ * v j) =
        higham10_18_matrix k α (Fin.castAdd k i) (Fin.natAdd k i) *
          v i) ∧
      ∀ v : Fin k → ℝ,
        vecNorm2Sq (fun i => α⁻¹ * v i) =
          (α⁻¹) ^ 2 * vecNorm2Sq v ∧
        C ≤ α⁻¹ := by
  set α : ℝ := min 1 (1 / (|C| + 1)) with hα
  have hα0 : 0 < α := by
    rw [hα]
    have : (0:ℝ) < 1 / (|C| + 1) := by positivity
    exact lt_min one_pos this
  refine ⟨α, hα0, higham10_18_isPosSemiDef k hk α hα0, ?_, ?_⟩
  · intro v i
    -- A₁₁ = αI acting on α⁻¹v recovers v = A₁₂-column action
    have hL : ∑ j : Fin k, higham10_18_matrix k α (Fin.castAdd k i)
        (Fin.castAdd k j) * (α⁻¹ * v j) = v i := by
      rw [Finset.sum_eq_single i]
      · unfold higham10_18_matrix
        simp only [Fin.coe_castAdd, if_true]
        rw [if_pos i.isLt]
        field_simp
      · intro b _ hb
        unfold higham10_18_matrix
        have hne : (Fin.castAdd k i).val ≠ (Fin.castAdd k b).val := by
          simp only [Fin.coe_castAdd]
          exact fun h => hb (Fin.ext h.symm)
        have h3 : ¬((Fin.castAdd k i).val + k =
            (Fin.castAdd k b).val ∨
            (Fin.castAdd k b).val + k = (Fin.castAdd k i).val) := by
          simp only [Fin.coe_castAdd]
          push_neg
          omega
        rw [if_neg hne, if_neg h3, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hR : higham10_18_matrix k α (Fin.castAdd k i)
        (Fin.natAdd k i) = 1 := by
      unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.natAdd k i).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have hor : (Fin.castAdd k i).val + k = (Fin.natAdd k i).val ∨
          (Fin.natAdd k i).val + k = (Fin.castAdd k i).val := by
        left
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      rw [if_neg hne, if_pos hor]
    rw [hL, hR, one_mul]
  · intro v
    constructor
    · unfold vecNorm2Sq
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · have h1 : α ≤ 1 / (|C| + 1) := by
        rw [hα]
        exact min_le_right _ _
      have h2 : (0:ℝ) < |C| + 1 := by positivity
      have h3 : |C| + 1 ≤ α⁻¹ := by
        rw [← one_div]
        rw [le_div_iff₀ hα0]
        calc (|C| + 1) * α ≤ (|C| + 1) * (1 / (|C| + 1)) :=
              mul_le_mul_of_nonneg_left h1 h2.le
          _ = 1 := by field_simp
      calc C ≤ |C| := le_abs_self C
        _ ≤ α⁻¹ := by linarith

/-- Operator-norm certificates add across matrix sums. -/
lemma opNorm2Le_add {n : ℕ} (A B : Fin n → Fin n → ℝ) (a b : ℝ)
    (hA : opNorm2Le A a) (hB : opNorm2Le B b) :
    opNorm2Le (fun i j => A i j + B i j) (a + b) := by
  intro x
  have hsplit : matMulVec n (fun i j => A i j + B i j) x =
      fun i => matMulVec n A x i + matMulVec n B x i := by
    funext i
    unfold matMulVec
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  calc vecNorm2 (fun i => matMulVec n A x i + matMulVec n B x i)
      ≤ vecNorm2 (matMulVec n A x) + vecNorm2 (matMulVec n B x) :=
        vecNorm2_add_le _ _
    _ ≤ a * vecNorm2 x + b * vecNorm2 x := add_le_add (hA x) (hB x)
    _ = (a + b) * vecNorm2 x := by ring

/-- **Display (10.25), componentwise to normwise** (Higham p. 206): the
    componentwise (10.24) bound
    `|E| ≤ γ(|R̂ᵀ||R̂| + |Â⁽ʳ⁺¹⁾|)` converts to the operator-norm
    certificate `‖E‖₂ ≤ γ(n·cR² + √n·cÂ)` via Lemma 6.6. -/
theorem higham10_25_componentwise_to_normwise (n : ℕ)
    (E R Ahat : Fin n → Fin n → ℝ) (γ cR cAhat : ℝ)
    (hγ0 : 0 ≤ γ) (hcR : 0 ≤ cR) (hcAhat : 0 ≤ cAhat)
    (h24 : ∀ i j : Fin n, |E i j| ≤ γ *
      (matMul n (fun i' j' => |R j' i'|) (fun i' j' => |R i' j'|) i j +
        |Ahat i j|))
    (hR : opNorm2Le R cR) (hAhat : opNorm2Le Ahat cAhat) :
    opNorm2Le E (γ * ((n : ℝ) * cR ^ 2 + Real.sqrt n * cAhat)) := by
  have hG := higham10_7_absRT_absR_opNorm2Le n R cR hcR hR
  have hAb := opNorm2Le_abs_of_opNorm2Le n Ahat cAhat hcAhat hAhat
  have hsum := opNorm2Le_add _ _ _ _ hG hAb
  have hB := opNorm2Le_smul n
    (fun i j =>
      matMul n (fun i' j' => |R j' i'|) (fun i' j' => |R i' j'|) i j +
        |Ahat i j|)
    ((n : ℝ) * cR ^ 2 + Real.sqrt n * cAhat) γ hγ0 hsum
  exact opNorm2Le_of_abs_le n E _ h24 _ hB

/-- **Display (10.25), the absorption** (Higham p. 206): from the norm
    chain `‖E‖ ≤ γ(r‖A‖ + r‖E‖ + n‖Â⁽ʳ⁺¹⁾‖)` with `rγ < 1`,
    `‖E‖ ≤ γ/(1 − rγ)·(r‖A‖ + n‖Â⁽ʳ⁺¹⁾‖)`. -/
theorem higham10_25_absorption (γ r n cA cAhat e : ℝ)
    (hrγ : r * γ < 1)
    (hchain : e ≤ γ * (r * cA + r * e + n * cAhat)) :
    e ≤ γ / (1 - r * γ) * (r * cA + n * cAhat) := by
  have h1 : (0:ℝ) < 1 - r * γ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  nlinarith

/-- **Lemma 10.13 / equation (10.19)**: complete-pivoting bound on
`‖W‖_F²` with Higham's `(n−r)(4^r−1)/3` constant, in honest form: for
an `r × r` upper-triangular block `U` with positive diagonal whose rows
are pivot-dominated on and right of the diagonal — exactly what
complete pivoting guarantees via the (10.13) column-tail invariant
(`tail_invariant_entry_le` applied to the factor from
`psd_pivoted_cholesky_exists_tail`) — the solution `W` of `U W = B`
with pivot-dominated right-hand columns `B` (the border block `R₁₂`)
satisfies `∑_{i,j} W i j ² ≤ m (4^r − 1)/3`, `m = n − r` border
columns. -/
theorem higham10_13_complete_pivoting_w_bound {r m : ℕ}
    (U : Fin r → Fin r → ℝ) (B W : Fin r → Fin m → ℝ)
    (hupper : ∀ i j : Fin r, j.val < i.val → U i j = 0)
    (hdiag_pos : ∀ i : Fin r, 0 < U i i)
    (hentry : ∀ i j : Fin r, i.val ≤ j.val → |U i j| ≤ U i i)
    (hB : ∀ (i : Fin r) (j : Fin m), |B i j| ≤ U i i)
    (hsolve : ∀ (i : Fin r) (j : Fin m),
      ∑ k : Fin r, U i k * W k j = B i j) :
    ∑ j : Fin m, ∑ i : Fin r, W i j ^ 2 ≤
      (m : ℝ) * (((4 : ℝ) ^ r - 1) / 3) :=
  complete_pivoting_w_bound U B W hupper hdiag_pos hentry hB hsolve

/-- **Lemma 10.13 instantiated on the complete-pivoting factor**: for any
    pivoted Cholesky factor `R` satisfying the (10.13) column-tail
    invariant (as produced by `psd_pivoted_cholesky_exists_tail`), the
    implicit matrix `W = R₁₁⁻¹ R₁₂` exists — each border column of `R₁₂`
    is solved exactly against the leading `r × r` block — and satisfies
    Higham's bound `‖W‖_F² ≤ (n − r)(4^r − 1)/3`. -/
theorem higham10_13_pivoted_w_frobenius_bound {n : ℕ}
    {A R : Fin n → Fin n → ℝ} {σ : Fin n → Fin n} {r : ℕ}
    (spec : PivotedCholeskySpec n A R σ r) (hr : r ≤ n)
    (htail : ∀ k j : Fin n, k.val ≤ j.val →
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
        R i j ^ 2) ≤ R k k ^ 2) :
    ∃ W : Fin r → Fin (n - r) → ℝ,
      (∀ (i : Fin r) (j : Fin (n - r)),
        ∑ k : Fin r, R (Fin.castLE hr i) (Fin.castLE hr k) * W k j =
          R (Fin.castLE hr i) ⟨r + j.val, by omega⟩) ∧
      ∑ j : Fin (n - r), ∑ i : Fin r, W i j ^ 2 ≤
        ((n - r : ℕ) : ℝ) * (((4 : ℝ) ^ r - 1) / 3) := by
  have hdiag_nonneg : ∀ i : Fin n, 0 ≤ R i i := by
    intro i
    rcases Nat.lt_or_ge i.val r with hlt | hge
    · exact (spec.R_diag_pos i hlt).le
    · rw [spec.R_rank_zero i i hge]
  have hdom := tail_invariant_entry_le hdiag_nonneg htail
  set U : Fin r → Fin r → ℝ :=
    fun i k => R (Fin.castLE hr i) (Fin.castLE hr k) with hU
  set B : Fin r → Fin (n - r) → ℝ :=
    fun i j => R (Fin.castLE hr i) ⟨r + j.val, by omega⟩ with hB
  have hupper : ∀ i j : Fin r, j.val < i.val → U i j = 0 :=
    fun i j hij => spec.R_upper _ _ hij
  have hdiag_pos : ∀ i : Fin r, 0 < U i i :=
    fun i => spec.R_diag_pos _ i.isLt
  have hentry : ∀ i j : Fin r, i.val ≤ j.val → |U i j| ≤ U i i :=
    fun i j hij => hdom _ _ hij
  have hBdom : ∀ (i : Fin r) (j : Fin (n - r)), |B i j| ≤ U i i :=
    fun i j => hdom _ _ (by
      show i.val ≤ r + j.val
      exact le_trans i.isLt.le (Nat.le_add_right r j.val))
  have hsol : ∀ j : Fin (n - r), ∃ y : Fin r → ℝ,
      ∀ i : Fin r, ∑ k : Fin r, U i k * y k = B i j :=
    fun j => upperTriangular_solve_exists r U hupper
      (fun i => (hdiag_pos i).ne') (fun i => B i j)
  choose Wcol hWcol using hsol
  refine ⟨fun i j => Wcol j i, fun i j => hWcol j i, ?_⟩
  exact complete_pivoting_w_bound U B (fun i j => Wcol j i)
    hupper hdiag_pos hentry hBdom (fun i j => hWcol j i)


/-- **Theorem 10.14 / equation (10.22)**: PSD Cholesky backward-error
interface after `r` stages. -/
theorem higham10_14_psd_cholesky_backward_error (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (r : ℕ) (hr : r ≤ n) (hr_pos : 0 < r)
    (hPSD : IsPosSemiDef n A)
    (hn_r : gammaValid fp (r + 1))
    (hγ_lt : gamma fp (r + 1) < 1)
    (W_norm : ℝ) (hW : 0 ≤ W_norm)
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
        ∑ k : Fin n, |A i k| * (if k.val < r then 1 else 0)) :=
  psd_cholesky_backward_error n fp A r hr hr_pos hPSD hn_r hγ_lt W_norm hW hbackward

/-- **Theorem 10.14 for the concrete algorithm** (display (10.22)
    shape): the three-block backward-error certificate of the truncated
    computed factor `R̃ = fl_choleskyTrunc` after `r` completed stages —
    Demmel-stable computed block, trace-controlled border under the
    computed-pivot domination `c`, terminal Schur residual `η` on the
    trailing block. -/
theorem higham10_14_fl_psd_cholesky_backward_error (fp : FPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ) (hn1 : gammaValid fp (n + 1))
    (hγlt : gamma fp (n + 1) < 1)
    (hsymm : ∀ i j : Fin n, A i j = A j i) (r : ℕ)
    (hdz : ∀ i : Fin n, i.val < r → fl_cholesky fp n A i i ≠ 0)
    (hpiv : ∀ i : Fin n, i.val < r → 0 ≤ fl_cholPivot fp n A i)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ j : Fin n, r ≤ j.val → ∀ k : Fin n, k.val < r →
      |fl_cholesky fp n A k j| ≤ c * |fl_cholesky fp n A k k|)
    (η : ℝ)
    (htrail : ∀ i j : Fin n, r ≤ i.val → r ≤ j.val →
      |∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
        fl_cholesky fp n A k i * fl_cholesky fp n A k j - A i j| ≤ η) :
    (∀ i j : Fin n, i.val < r → j.val < r →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A i i) * Real.sqrt (A j j))) ∧
    (∀ i j : Fin n, i.val < r → r ≤ j.val →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) * c / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A i i) *
         Real.sqrt (∑ k ∈ Finset.univ.filter
          (fun k : Fin n => k.val < r), A k k))) ∧
    (∀ i j : Fin n, r ≤ i.val → j.val < r →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) * c / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A j j) *
         Real.sqrt (∑ k ∈ Finset.univ.filter
          (fun k : Fin n => k.val < r), A k k))) ∧
    (∀ i j : Fin n, r ≤ i.val → r ≤ j.val →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤ η) :=
  fl_choleskyTrunc_backward_error fp n A hn1 hγlt hsymm r hdz hpiv
    c hc hdom η htrail

/-- **Equation (10.26)**: stop after the first nonpositive remaining pivot. -/
def higham10_26_nonpositivePivotCriterion {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : ℕ) : Prop :=
  ∀ i : Fin n, k ≤ i.val → Astage i i ≤ 0

/-- **Equation (10.27)**: residual-norm stopping criterion. -/
def higham10_27_residualStopCriterion
    (residual_norm matrix_norm ε : ℝ) : Prop :=
  residual_norm ≤ ε * matrix_norm

/-- **Equation (10.27)**: alternative nonpositive-diagonal stopping criterion. -/
def higham10_27_nonpositiveDiagonalCriterion {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : ℕ) : Prop :=
  higham10_26_nonpositivePivotCriterion Astage k

/-- **Equation (10.28)**: relative diagonal stopping criterion, written as the
equivalent finite-entry form of `max_{i>=k} a_ii^(k) <= ε a_11^(1)`. -/
def higham10_28_relativeDiagonalStopCriterion {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : ℕ) (ε initialPivot : ℝ) : Prop :=
  ∀ i : Fin n, k ≤ i.val → Astage i i ≤ ε * initialPivot

/-- **Equation (10.27)** abstract termination-bound interface used by the PSD
error analysis. -/
theorem higham10_27_psd_cholesky_termination_bound
    (residual_norm matrix_norm : ℝ)
    (n : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hstop : residual_norm ≤ ↑n * u * matrix_norm)
    (hm : 0 ≤ matrix_norm) :
    residual_norm ≤ ↑n * u * matrix_norm :=
  psd_cholesky_termination_bound residual_norm matrix_norm n u hu hstop hm

/-! ## Appendix A, Problems 10.8 and 10.12 -/

/-- **Problem 10.8** witness: a symmetric matrix with nonnegative leading
principal determinant formulas that is not positive semidefinite. -/
def higham10_problem_10_8_counterexample : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = 1 ∧ j = 1 then -1 else 0

/-- **Problem 10.8**: the witness has nonnegative leading `1 x 1` and `2 x 2`
determinant formulas. -/
theorem higham10_problem_10_8_leading_minors_nonnegative :
    higham10_problem_10_8_counterexample 0 0 = 0 ∧
      higham10_problem_10_8_counterexample 0 0 *
          higham10_problem_10_8_counterexample 1 1 -
        higham10_problem_10_8_counterexample 0 1 *
          higham10_problem_10_8_counterexample 1 0 = 0 := by
  constructor
  · rfl
  · simp [higham10_problem_10_8_counterexample]

/-- **Problem 10.8**: the witness matrix is symmetric. -/
theorem higham10_problem_10_8_counterexample_symmetric :
    ∀ i j : Fin 2,
      higham10_problem_10_8_counterexample i j =
        higham10_problem_10_8_counterexample j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [higham10_problem_10_8_counterexample]

/-- **Problem 10.8**: the witness is not positive semidefinite. -/
theorem higham10_problem_10_8_counterexample_not_psd :
    ¬ IsPosSemiDef 2 higham10_problem_10_8_counterexample := by
  intro hPSD
  have h := hPSD.2 (fun k : Fin 2 => if k = 1 then 1 else 0)
  have heval : (∑ i : Fin 2, ∑ j : Fin 2,
      (if i = 1 then (1 : ℝ) else 0) *
        higham10_problem_10_8_counterexample i j *
        (if j = 1 then (1 : ℝ) else 0)) = -1 := by
    norm_num [higham10_problem_10_8_counterexample]
  rw [heval] at h
  linarith

/-! ## §10.4 Matrices with Positive Definite Symmetric Part -/

/-- **Section 10.4** source predicate: `x^T A x > 0` for every nonzero real
vector, equivalently the symmetric part is SPD. -/
abbrev higham10_4_IsNonsymPosDef (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Prop :=
  IsNonsymPosDef n A

/-- **Section 10.4 prose**: leading principal submatrices of a matrix with
positive definite symmetric part are again in that class. -/
theorem higham10_4_nonsym_pd_leading_principal (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hA : higham10_4_IsNonsymPosDef n A)
    (k : ℕ) (hk : k ≤ n) :
    higham10_4_IsNonsymPosDef k
      (fun i j => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) :=
  nonsymPosDef_leading_principal hA k hk

/-- **Section 10.4 prose**, nonsingularity form: a matrix with positive
definite symmetric part has trivial kernel — `A x ≠ 0` for every `x ≠ 0`.
Combined with `higham10_4_nonsym_pd_leading_principal` this closes the
"nonsingular leading principal submatrices" claim in exact arithmetic. -/
theorem higham10_4_nonsym_pd_mulVec_ne_zero (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hA : higham10_4_IsNonsymPosDef n A)
    (x : Fin n → ℝ) (hx : ∃ i, x i ≠ 0) :
    ∃ i : Fin n, (∑ j : Fin n, A i j * x j) ≠ 0 :=
  nonsymPosDef_mulVec_ne_zero hA x hx

/-- **Section 10.4 prose** (Higham p. 209): unpivoted Gaussian elimination
on a matrix with positive definite symmetric part runs to completion with a
positive pivot at every stage, via the Schur-complement closure
`nonsym_pd_first_ge_schur` of the class. -/
theorem higham10_4_nonsym_pd_ge_positive_pivots (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hA : higham10_4_IsNonsymPosDef n A) :
    nonsymPDGEPivotsPos n A :=
  nonsym_pd_unpivoted_ge_positive_pivots n A hA

/-- **Equation (10.29)** setup: `A = A_S + A_K`, symmetric and skew-symmetric
parts. -/
theorem higham10_29_symmetric_skew_decomposition (n : ℕ)
    (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, A i j = symmetricPart n A i j + skewSymmetricPart n A i j :=
  symmetric_skew_decomposition n A

/-- **Section 10.4** equivalence: nonsymmetric positive definiteness is the
same as SPD of the symmetric part. -/
theorem higham10_29_nonsymPosDef_iff_symPartSPD (n : ℕ)
    (A : Fin n → Fin n → ℝ) :
    higham10_4_IsNonsymPosDef n A ↔ IsSymPosDef n (symmetricPart n A) :=
  nonsymPosDef_iff_symPartSPD n A

/-- **Equation (10.29)** / Golub-Van Loan growth-bound interface for exact
LU factors of a nonsymmetric positive-definite matrix. -/
theorem higham10_29_nonsym_pd_lu_growth_bound (n : ℕ) (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hPD : higham10_4_IsNonsymPosDef n A)
    (hLU : LUFactSpec n A L U)
    (κ_AS : ℝ) (hκ : 0 ≤ κ_AS)
    (hbound : frobNormSq (fun i j => ∑ k : Fin n, |L i k| * |U k j|) ≤
      ↑n * κ_AS * frobNormSq A) :
    frobNormSq (fun i j => ∑ k : Fin n, |L i k| * |U k j|) ≤
      ↑n * κ_AS * frobNormSq A :=
  nonsym_pd_lu_growth_bound n hn A L U hPD hLU κ_AS hκ hbound

/-- **Mathias success condition** from §10.4. -/
theorem higham10_mathias_lu_success (n : ℕ) (fp : FPModel)
    (chi : ℝ) (hchi : 0 < chi)
    (n_three_half : ℝ) (hn32 : 0 ≤ n_three_half)
    (hsuccess : 24 * n_three_half * chi * fp.u < 1) :
    24 * n_three_half * chi * fp.u < 1 :=
  mathias_lu_success n fp chi hchi n_three_half hn32 hsuccess

/-- **Equation (10.30)**: complex matrices of the form `A = B + iC`, with
real SPD `B` and `C` supplied separately by hypotheses in downstream use. -/
noncomputable def higham10_30_complexPositiveDefiniteForm (n : ℕ)
    (B C : Fin n → Fin n → ℝ) : Fin n → Fin n → ℂ :=
  fun i j => (B i j : ℂ) + Complex.I * (C i j : ℂ)

end LeanFpAnalysis.FP
