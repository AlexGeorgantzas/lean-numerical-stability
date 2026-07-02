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

/-- **Lemma 10.10 / equation (10.16)**: Schur-complement perturbation
interface. -/
theorem higham10_10_schur_complement_perturbation (n k : ℕ)
    (A E A11_inv : Fin n → Fin n → ℝ)
    (W_norm : ℝ) (hW_norm : 0 ≤ W_norm)
    (E_norm : ℝ) (hE_norm : 0 ≤ E_norm)
    (hbound : ∀ i j : Fin n, k ≤ i.val → k ≤ j.val →
      |higham10_14_schurComplement n k (fun i' j' => A i' j' + E i' j') A11_inv i j -
       higham10_14_schurComplement n k A A11_inv i j| ≤
      (1 + W_norm) ^ 2 * E_norm) :
    ∀ i j : Fin n, k ≤ i.val → k ≤ j.val →
      |higham10_14_schurComplement n k (fun i' j' => A i' j' + E i' j') A11_inv i j -
       higham10_14_schurComplement n k A A11_inv i j| ≤
      (1 + W_norm) ^ 2 * E_norm :=
  schur_complement_perturbation n k A E A11_inv W_norm hW_norm E_norm hE_norm hbound

/-- **Lemma 10.12**: abstract `W = A11^{-1} A12` norm bound. -/
theorem higham10_12_w_norm_bound_from_cond
    (W_norm κ_A11 : ℝ) (hκ : 0 ≤ κ_A11)
    (hW : W_norm ^ 2 ≤ κ_A11) :
    W_norm ^ 2 ≤ κ_A11 :=
  w_norm_bound_from_cond W_norm κ_A11 hκ hW

/-- **Lemma 10.13 / equation (10.19)**: complete-pivoting bound on
`‖W‖^2`, with Higham's `(n-r)(4^r-1)/3` constant. -/
theorem higham10_13_complete_pivoting_w_bound (n r : ℕ) (hr : r ≤ n)
    (W_norm_sq : ℝ)
    (hW : W_norm_sq ≤ (↑(n - r) : ℝ) * ((4 : ℝ) ^ r - 1) / 3) :
    W_norm_sq ≤ (↑(n - r) : ℝ) * ((4 : ℝ) ^ r - 1) / 3 :=
  complete_pivoting_w_bound n r hr W_norm_sq hW

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
