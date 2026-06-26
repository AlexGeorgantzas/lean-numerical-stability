-- Algorithms/HighamChapter9.lean
--
-- Source-facing entry points for Higham Chapter 9, "LU Factorization and
-- Linear Equations".  The detailed proofs remain in the focused LU modules;
-- this file provides stable chapter labels and light wrappers around those
-- results.

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import LeanFpAnalysis.FP.Algorithms.HighamChapter8
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination
import LeanFpAnalysis.FP.Algorithms.LU.LUSolve
import LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor
import LeanFpAnalysis.FP.Algorithms.LU.BlockLU
import LeanFpAnalysis.FP.Algorithms.LU.Tridiagonal
import LeanFpAnalysis.FP.Algorithms.LU.TridiagonalRecurrence
import LeanFpAnalysis.FP.Algorithms.LU.SpecialMatrices
import LeanFpAnalysis.FP.Algorithms.LU.Doolittle
import LeanFpAnalysis.FP.Algorithms.LU.TridiagonalCond

namespace LeanFpAnalysis.FP

open scoped BigOperators
open ComplexConjugate

/-! ## §9.1 Gaussian elimination and pivoting strategies -/

/-- **Section 9.1**, partial-pivoting first-stage choice: among the active
rows `i >= k`, row `r` has maximal absolute value in column `k`. -/
def higham9_1_partialPivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r : Fin n) : Prop :=
  k.val ≤ r.val ∧
    ∀ i : Fin n, k.val ≤ i.val → |Astage i k| ≤ |Astage r k|

/-- **Section 9.1**, complete-pivoting first-stage choice: among the active
submatrix `i,j >= k`, entry `(r,s)` has maximal absolute value. -/
def higham9_1_completePivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s : Fin n) : Prop :=
  k.val ≤ r.val ∧ k.val ≤ s.val ∧
    ∀ i j : Fin n, k.val ≤ i.val → k.val ≤ j.val →
      |Astage i j| ≤ |Astage r s|

/-- **Section 9.1**, rook-pivoting accepted pivot: the selected entry is
maximal in both its active column and its active row. -/
def higham9_1_rookPivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s : Fin n) : Prop :=
  k.val ≤ r.val ∧ k.val ≤ s.val ∧
    (∀ i : Fin n, k.val ≤ i.val → |Astage i s| ≤ |Astage r s|) ∧
    (∀ j : Fin n, k.val ≤ j.val → |Astage r j| ≤ |Astage r s|)

/-- **Section 9.1**, partial-pivoting row choice exists on the finite active
column. -/
theorem higham9_1_exists_partialPivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n) :
    ∃ r : Fin n, higham9_1_partialPivotChoice Astage k r := by
  classical
  let active : Finset (Fin n) := Finset.univ.filter fun i => k.val ≤ i.val
  have hactive : active.Nonempty := by
    refine ⟨k, ?_⟩
    simp [active]
  obtain ⟨r, hr_mem, hr_max⟩ :=
    Finset.exists_max_image active (fun i : Fin n => |Astage i k|) hactive
  refine ⟨r, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hr_mem).2
  · intro i hi
    exact hr_max i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

/-- **Section 9.1**, complete-pivoting entry choice exists on the finite
active submatrix. -/
theorem higham9_1_exists_completePivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n) :
    ∃ r s : Fin n, higham9_1_completePivotChoice Astage k r s := by
  classical
  let active : Finset (Fin n × Fin n) :=
    Finset.univ.filter fun p => k.val ≤ p.1.val ∧ k.val ≤ p.2.val
  have hactive : active.Nonempty := by
    refine ⟨(k, k), ?_⟩
    simp [active]
  obtain ⟨p, hp_mem, hp_max⟩ :=
    Finset.exists_max_image active
      (fun p : Fin n × Fin n => |Astage p.1 p.2|)
      hactive
  refine ⟨p.1, p.2, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hp_mem).2.1
  · exact (Finset.mem_filter.mp hp_mem).2.2
  · intro i j hi hj
    exact hp_max (i, j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), ⟨hi, hj⟩⟩)

/-- A complete-pivoting maximum is also an accepted rook-pivoting entry. -/
theorem higham9_1_rookPivotChoice_of_completePivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s : Fin n)
    (hchoice : higham9_1_completePivotChoice Astage k r s) :
    higham9_1_rookPivotChoice Astage k r s := by
  refine ⟨hchoice.1, hchoice.2.1, ?_, ?_⟩
  · intro i hi
    exact hchoice.2.2 i s hi hchoice.2.1
  · intro j hj
    exact hchoice.2.2 r j hchoice.1 hj

/-- **Section 9.1**, an accepted rook-pivoting entry exists by taking a
complete-pivoting maximum. -/
theorem higham9_1_exists_rookPivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n) :
    ∃ r s : Fin n, higham9_1_rookPivotChoice Astage k r s := by
  obtain ⟨r, s, hchoice⟩ :=
    higham9_1_exists_completePivotChoice Astage k
  exact ⟨r, s, higham9_1_rookPivotChoice_of_completePivotChoice
    Astage k r s hchoice⟩

/-- A partial-pivoting maximum is nonzero if the active column contains a
nonzero entry. -/
theorem higham9_1_partialPivotChoice_pivot_ne_zero_of_exists {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r : Fin n)
    (hchoice : higham9_1_partialPivotChoice Astage k r)
    (hactive : ∃ i : Fin n, k.val ≤ i.val ∧ Astage i k ≠ 0) :
    Astage r k ≠ 0 := by
  rcases hactive with ⟨i, hi, hne⟩
  intro hr
  have hle : |Astage i k| ≤ 0 := by
    simpa [hr] using hchoice.2 i hi
  have hzero : |Astage i k| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact hne (abs_eq_zero.mp hzero)

/-- A complete-pivoting maximum is nonzero if the active submatrix contains a
nonzero entry. -/
theorem higham9_1_completePivotChoice_pivot_ne_zero_of_exists {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s : Fin n)
    (hchoice : higham9_1_completePivotChoice Astage k r s)
    (hactive : ∃ i j : Fin n, k.val ≤ i.val ∧ k.val ≤ j.val ∧
      Astage i j ≠ 0) :
    Astage r s ≠ 0 := by
  rcases hactive with ⟨i, j, hi, hj, hne⟩
  intro hrs
  have hle : |Astage i j| ≤ 0 := by
    simpa [hrs] using hchoice.2.2 i j hi hj
  have hzero : |Astage i j| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact hne (abs_eq_zero.mp hzero)

/-- A partial-pivoting row with a nonzero selected pivot exists whenever the
active column contains a nonzero entry. -/
theorem higham9_1_exists_partialPivotChoice_pivot_ne_zero {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive : ∃ i : Fin n, k.val ≤ i.val ∧ Astage i k ≠ 0) :
    ∃ r : Fin n,
      higham9_1_partialPivotChoice Astage k r ∧ Astage r k ≠ 0 := by
  obtain ⟨r, hchoice⟩ := higham9_1_exists_partialPivotChoice Astage k
  exact ⟨r, hchoice,
    higham9_1_partialPivotChoice_pivot_ne_zero_of_exists
      Astage k r hchoice hactive⟩

/-- A complete-pivoting entry with a nonzero selected pivot exists whenever the
active submatrix contains a nonzero entry. -/
theorem higham9_1_exists_completePivotChoice_pivot_ne_zero {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive : ∃ i j : Fin n, k.val ≤ i.val ∧ k.val ≤ j.val ∧
      Astage i j ≠ 0) :
    ∃ r s : Fin n,
      higham9_1_completePivotChoice Astage k r s ∧ Astage r s ≠ 0 := by
  obtain ⟨r, s, hchoice⟩ := higham9_1_exists_completePivotChoice Astage k
  exact ⟨r, s, hchoice,
    higham9_1_completePivotChoice_pivot_ne_zero_of_exists
      Astage k r s hchoice hactive⟩

/-- **Section 9.1**, a nonsingular active matrix has at least one nonzero
entry.  This is the determinant side condition needed to start a
complete-pivoting trace. -/
theorem higham9_1_exists_entry_ne_zero_of_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∃ i j : Fin (m + 1), A i j ≠ 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hzero :
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = 0 := by
    ext i j
    exact hnone i j
  rw [hzero] at hdet
  have hdet_zero :
      Matrix.det (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = 0 := by
    rw [Matrix.det_zero]
    exact ⟨0⟩
  exact hdet hdet_zero

/-- **Section 9.1**, a nonsingular matrix admits a nonzero first complete
pivot.  The active submatrix is the full matrix at `k = 0`. -/
theorem higham9_1_exists_first_completePivotChoice_pivot_ne_zero_of_det_ne_zero
    {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∃ r s : Fin (m + 1),
      higham9_1_completePivotChoice A 0 r s ∧ A r s ≠ 0 := by
  obtain ⟨i, j, hij⟩ :=
    higham9_1_exists_entry_ne_zero_of_det_ne_zero A hdet
  exact higham9_1_exists_completePivotChoice_pivot_ne_zero A 0
    ⟨i, j, Nat.zero_le i.val, Nat.zero_le j.val, hij⟩

/-- Partial pivoting gives multipliers bounded by one in absolute value. -/
theorem higham9_1_partialPivot_multiplier_abs_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r i : Fin n)
    (hchoice : higham9_1_partialPivotChoice Astage k r)
    (hpivot : Astage r k ≠ 0)
    (hi : k.val ≤ i.val) :
    |Astage i k / Astage r k| ≤ 1 := by
  have hcol : |Astage i k| ≤ |Astage r k| := hchoice.2 i hi
  have hden_pos : 0 < |Astage r k| := abs_pos.mpr hpivot
  rw [abs_div, div_le_iff₀ hden_pos]
  simpa using hcol

/-- Complete pivoting gives column multipliers bounded by one for the selected
pivot column. -/
theorem higham9_1_completePivot_column_multiplier_abs_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s i : Fin n)
    (hchoice : higham9_1_completePivotChoice Astage k r s)
    (hpivot : Astage r s ≠ 0)
    (hi : k.val ≤ i.val) :
    |Astage i s / Astage r s| ≤ 1 := by
  have hcol : |Astage i s| ≤ |Astage r s| :=
    hchoice.2.2 i s hi hchoice.2.1
  have hden_pos : 0 < |Astage r s| := abs_pos.mpr hpivot
  rw [abs_div, div_le_iff₀ hden_pos]
  simpa using hcol

/-- Complete pivoting bounds every active entry by the selected pivot, hence
any active entry divided by the pivot has absolute value at most one. -/
theorem higham9_1_completePivot_active_entry_ratio_abs_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s i j : Fin n)
    (hchoice : higham9_1_completePivotChoice Astage k r s)
    (hpivot : Astage r s ≠ 0)
    (hi : k.val ≤ i.val) (hj : k.val ≤ j.val) :
    |Astage i j / Astage r s| ≤ 1 := by
  have hentry : |Astage i j| ≤ |Astage r s| :=
    hchoice.2.2 i j hi hj
  have hden_pos : 0 < |Astage r s| := abs_pos.mpr hpivot
  rw [abs_div, div_le_iff₀ hden_pos]
  simpa using hentry

/-- Rook pivoting gives column multipliers bounded by one for the accepted
pivot column. -/
theorem higham9_1_rookPivot_column_multiplier_abs_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s i : Fin n)
    (hchoice : higham9_1_rookPivotChoice Astage k r s)
    (hpivot : Astage r s ≠ 0)
    (hi : k.val ≤ i.val) :
    |Astage i s / Astage r s| ≤ 1 := by
  have hcol : |Astage i s| ≤ |Astage r s| := hchoice.2.2.1 i hi
  have hden_pos : 0 < |Astage r s| := abs_pos.mpr hpivot
  rw [abs_div, div_le_iff₀ hden_pos]
  simpa using hcol

/-- Rook pivoting gives row-side entry ratios bounded by one for the accepted
pivot row. -/
theorem higham9_1_rookPivot_row_multiplier_abs_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s j : Fin n)
    (hchoice : higham9_1_rookPivotChoice Astage k r s)
    (hpivot : Astage r s ≠ 0)
    (hj : k.val ≤ j.val) :
    |Astage r j / Astage r s| ≤ 1 := by
  have hrow : |Astage r j| ≤ |Astage r s| := hchoice.2.2.2 j hj
  have hden_pos : 0 < |Astage r s| := abs_pos.mpr hpivot
  rw [abs_div, div_le_iff₀ hden_pos]
  simpa using hrow

/-- First-stage partial pivoting can choose a nonzero pivot with all active
column multipliers bounded by one whenever the active column is nonzero. -/
theorem higham9_1_exists_partialPivot_nonzero_and_multiplier_bound {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive : ∃ i : Fin n, k.val ≤ i.val ∧ Astage i k ≠ 0) :
    ∃ r : Fin n,
      higham9_1_partialPivotChoice Astage k r ∧
      Astage r k ≠ 0 ∧
      ∀ i : Fin n, k.val ≤ i.val → |Astage i k / Astage r k| ≤ 1 := by
  obtain ⟨r, hchoice, hpivot⟩ :=
    higham9_1_exists_partialPivotChoice_pivot_ne_zero Astage k hactive
  exact ⟨r, hchoice, hpivot, fun i hi =>
    higham9_1_partialPivot_multiplier_abs_le_one Astage k r i
      hchoice hpivot hi⟩

/-- First-stage complete pivoting can choose a nonzero pivot with active
column and whole-active-submatrix ratios bounded by one whenever the active
submatrix is nonzero. -/
theorem higham9_1_exists_completePivot_nonzero_and_ratio_bounds {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive : ∃ i j : Fin n, k.val ≤ i.val ∧ k.val ≤ j.val ∧
      Astage i j ≠ 0) :
    ∃ r s : Fin n,
      higham9_1_completePivotChoice Astage k r s ∧
      Astage r s ≠ 0 ∧
      (∀ i : Fin n, k.val ≤ i.val → |Astage i s / Astage r s| ≤ 1) ∧
      (∀ i j : Fin n, k.val ≤ i.val → k.val ≤ j.val →
        |Astage i j / Astage r s| ≤ 1) := by
  obtain ⟨r, s, hchoice, hpivot⟩ :=
    higham9_1_exists_completePivotChoice_pivot_ne_zero Astage k hactive
  exact ⟨r, s, hchoice, hpivot,
    (fun i hi =>
      higham9_1_completePivot_column_multiplier_abs_le_one Astage k r s i
        hchoice hpivot hi),
    (fun i j hi hj =>
      higham9_1_completePivot_active_entry_ratio_abs_le_one Astage k r s i j
        hchoice hpivot hi hj)⟩

/-- A complete-pivoting maximum supplies an accepted rook pivot with nonzero
pivot and row/column active ratios bounded by one whenever the active
submatrix is nonzero. -/
theorem higham9_1_exists_rookPivot_nonzero_and_ratio_bounds {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive : ∃ i j : Fin n, k.val ≤ i.val ∧ k.val ≤ j.val ∧
      Astage i j ≠ 0) :
    ∃ r s : Fin n,
      higham9_1_rookPivotChoice Astage k r s ∧
      Astage r s ≠ 0 ∧
      (∀ i : Fin n, k.val ≤ i.val → |Astage i s / Astage r s| ≤ 1) ∧
      (∀ j : Fin n, k.val ≤ j.val → |Astage r j / Astage r s| ≤ 1) := by
  obtain ⟨r, s, hcomplete, hpivot⟩ :=
    higham9_1_exists_completePivotChoice_pivot_ne_zero Astage k hactive
  have hrook : higham9_1_rookPivotChoice Astage k r s :=
    higham9_1_rookPivotChoice_of_completePivotChoice Astage k r s hcomplete
  exact ⟨r, s, hrook, hpivot,
    (fun i hi =>
      higham9_1_rookPivot_column_multiplier_abs_le_one Astage k r s i
        hrook hpivot hi),
    (fun j hj =>
      higham9_1_rookPivot_row_multiplier_abs_le_one Astage k r s j
        hrook hpivot hj)⟩

/-! ## §9.2 LU Factorization -/

/-- **Algorithm 9.2**: Doolittle's method certificate for the computed factors. -/
abbrev higham9_2_DoolittleLU (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (fp : FPModel) : Prop :=
  DoolittleLU n A L_hat U_hat fp

/-- **Equation (9.2a)**, source row-permuted matrix `PA` represented by the
permutation map `sigma`.  The entry `(i,j)` is `A (sigma i) j`. -/
def higham9_2_rowPermutedMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j => A (sigma i) j

/-- **Theorem 9.7 / partial-pivoting growth support**, the first row swap that
moves the selected partial-pivot row into leading position.  This is the
source row-permutation step preceding the first Schur-complement update. -/
def higham9_7_firstPivotRowSwap {m : ℕ} (r : Fin (m + 1)) :
    Fin (m + 1) → Fin (m + 1) :=
  fun i => if i = 0 then r else if i = r then 0 else i

/-- **Theorem 9.7 / partial-pivoting growth support**, the first-pivot row
swap is its own inverse. -/
theorem higham9_7_firstPivotRowSwap_involutive {m : ℕ}
    (r : Fin (m + 1)) :
    Function.Involutive (higham9_7_firstPivotRowSwap r) := by
  intro i
  unfold higham9_7_firstPivotRowSwap
  by_cases hi0 : i = 0
  · subst i
    by_cases hr0 : r = 0
    · simp [hr0]
    · simp [hr0]
  · by_cases hir : i = r
    · subst i
      simp [hi0]
    · simp [hi0, hir]

/-- **Theorem 9.7 / partial-pivoting growth support**, the first-pivot row
swap is a permutation of the active row type. -/
theorem higham9_7_firstPivotRowSwap_isPermutation {m : ℕ}
    (r : Fin (m + 1)) :
    Function.Bijective (higham9_7_firstPivotRowSwap r) := by
  constructor
  · intro x y hxy
    have h := congrArg (higham9_7_firstPivotRowSwap r) hxy
    simpa [higham9_7_firstPivotRowSwap_involutive r x,
      higham9_7_firstPivotRowSwap_involutive r y] using h
  · intro y
    exact ⟨higham9_7_firstPivotRowSwap r y,
      higham9_7_firstPivotRowSwap_involutive r y⟩

/-- **Theorem 9.7 / partial-pivoting growth support**, permuting the rows by
the first-pivot row swap preserves nonsingularity. -/
theorem higham9_7_firstPivotRowSwap_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (r : Fin (m + 1))
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
  classical
  let e : Equiv.Perm (Fin (m + 1)) :=
    Equiv.ofBijective (higham9_7_firstPivotRowSwap r)
      (higham9_7_firstPivotRowSwap_isPermutation r)
  have hdet_eq :
      Matrix.det
        (Matrix.of (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
        ((Equiv.Perm.sign e : ℤ) : ℝ) *
          Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) := by
    have hperm :=
      Matrix.det_permute (R := ℝ) e
        (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    simpa [e, higham9_2_rowPermutedMatrix, Matrix.of_apply] using hperm
  rw [hdet_eq]
  have hsign : ((Equiv.Perm.sign e : ℤ) : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with hs | hs <;> simp [hs]
  exact mul_ne_zero hsign hdet

/-- **Theorem 9.7 / partial-pivoting growth support**, entrywise first-step
doubling bound.  After moving a partial-pivoting maximum into the leading row,
every entry of the first Schur complement is bounded by twice the original
max-entry norm.  This is the local one-step inequality behind the source
`rho_n^p <= 2^(n-1)` growth argument; it does not construct the full recursive
partial-pivoting trace. -/
theorem higham9_7_partialPivot_firstSchurComplement_entry_abs_le_two {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (r : Fin (m + 1))
    (hchoice : higham9_1_partialPivotChoice A 0 r)
    (hpivot : A r 0 ≠ 0) (i j : Fin m) :
    |luFirstSchurComplement
        (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) i j| ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  let sigma := higham9_7_firstPivotRowSwap r
  let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ := higham9_2_rowPermutedMatrix A sigma
  have hentry : |Aperm i.succ j.succ| ≤ maxEntryNorm (Nat.succ_pos m) A := by
    exact entry_le_maxEntryNorm (Nat.succ_pos m) A (sigma i.succ) j.succ
  have hpivot_row : |Aperm 0 j.succ| ≤ maxEntryNorm (Nat.succ_pos m) A := by
    simpa [Aperm, higham9_2_rowPermutedMatrix, sigma, higham9_7_firstPivotRowSwap] using
      (entry_le_maxEntryNorm (Nat.succ_pos m) A r j.succ)
  have hratio : |Aperm i.succ 0 / Aperm 0 0| ≤ 1 := by
    have hraw :=
      higham9_1_partialPivot_multiplier_abs_le_one A 0 r (sigma i.succ)
        hchoice hpivot (Nat.zero_le _)
    simpa [Aperm, higham9_2_rowPermutedMatrix, sigma, higham9_7_firstPivotRowSwap] using hraw
  have hterm :
      |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| ≤
        maxEntryNorm (Nat.succ_pos m) A := by
    calc
      |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0|
          = |Aperm i.succ 0 / Aperm 0 0| * |Aperm 0 j.succ| := by
            rw [abs_div, abs_mul, abs_div]
            ring
      _ ≤ 1 * |Aperm 0 j.succ| :=
            mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
      _ ≤ 1 * maxEntryNorm (Nat.succ_pos m) A :=
            mul_le_mul_of_nonneg_left hpivot_row zero_le_one
      _ = maxEntryNorm (Nat.succ_pos m) A := by ring
  unfold luFirstSchurComplement
  calc
    |Aperm i.succ j.succ - Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0|
        ≤ |Aperm i.succ j.succ| +
            |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (Aperm i.succ j.succ)
              (-(Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0))
    _ ≤ maxEntryNorm (Nat.succ_pos m) A + maxEntryNorm (Nat.succ_pos m) A :=
        add_le_add hentry hterm
    _ = 2 * maxEntryNorm (Nat.succ_pos m) A := by ring

/-- **Theorem 9.7 / partial-pivoting growth support**, max-entry first-step
doubling bound for the Schur complement after the first partial-pivoting row
swap. -/
theorem higham9_7_partialPivot_firstSchurComplement_maxEntryNorm_le_two {m : ℕ}
    (hm : 0 < m) (A : Fin (m + 1) → Fin (m + 1) → ℝ) (r : Fin (m + 1))
    (hchoice : higham9_1_partialPivotChoice A 0 r)
    (hpivot : A r 0 ≠ 0) :
    maxEntryNorm hm
        (luFirstSchurComplement
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact higham9_7_partialPivot_firstSchurComplement_entry_abs_le_two A r
    hchoice hpivot i j

/-- **Theorem 9.7 / partial-pivoting growth support**, iterating the
one-step doubling recurrence for active-stage max-entry bounds. -/
theorem higham9_7_partialPivot_stageMax_le_pow_two (stageMax : ℕ → ℝ) :
    ∀ k : ℕ,
      (∀ t : ℕ, t < k → stageMax (t + 1) ≤ 2 * stageMax t) →
      stageMax k ≤ (2 : ℝ) ^ k * stageMax 0 := by
  intro k
  induction k with
  | zero =>
      intro _hstep
      simp
  | succ k ih =>
      intro hstep
      have hprev : ∀ t : ℕ, t < k → stageMax (t + 1) ≤ 2 * stageMax t := by
        intro t ht
        exact hstep t (Nat.lt_trans ht (Nat.lt_succ_self k))
      have hlast : stageMax (k + 1) ≤ 2 * stageMax k :=
        hstep k (Nat.lt_succ_self k)
      calc
        stageMax (Nat.succ k)
            = stageMax (k + 1) := rfl
        _ ≤ 2 * stageMax k := hlast
        _ ≤ 2 * ((2 : ℝ) ^ k * stageMax 0) :=
            mul_le_mul_of_nonneg_left (ih hprev) (by norm_num)
        _ = (2 : ℝ) ^ Nat.succ k * stageMax 0 := by
            rw [pow_succ]
            ring

/-- **Theorem 9.7 / partial-pivoting growth support**, source-shaped
`rho_n^p <= 2^(n-1)` consequence from explicit stage bounds.

The theorem deliberately keeps the algorithmic trace as hypotheses: a future
recursive GEPP formalization must supply the stage max sequence, the per-stage
doubling facts, and the final upper-factor bound. -/
theorem higham9_7_partialPivot_growthFactorEntry_le_pow_two_of_stage_bounds
    {n : ℕ} (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A) (stageMax : ℕ → ℝ)
    (hstep : ∀ t : ℕ, t < n - 1 → stageMax (t + 1) ≤ 2 * stageMax t)
    (hinit : stageMax 0 ≤ maxEntryNorm hn A)
    (hfinal : maxEntryNorm hn U ≤ stageMax (n - 1)) :
    growthFactorEntry hn A U hAmax ≤ (2 : ℝ) ^ (n - 1) := by
  have hstage :
      stageMax (n - 1) ≤ (2 : ℝ) ^ (n - 1) * stageMax 0 :=
    higham9_7_partialPivot_stageMax_le_pow_two stageMax (n - 1) hstep
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (n - 1) :=
    pow_nonneg (by norm_num) (n - 1)
  have hU :
      maxEntryNorm hn U ≤ (2 : ℝ) ^ (n - 1) * maxEntryNorm hn A := by
    calc
      maxEntryNorm hn U ≤ stageMax (n - 1) := hfinal
      _ ≤ (2 : ℝ) ^ (n - 1) * stageMax 0 := hstage
      _ ≤ (2 : ℝ) ^ (n - 1) * maxEntryNorm hn A :=
          mul_le_mul_of_nonneg_left hinit hpow_nonneg
  unfold growthFactorEntry
  rw [div_le_iff₀ hAmax]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hU

/-- **Theorem 9.7 / partial-pivoting GEPP `U` trace**, a recursive exact
partial-pivoting trace that exposes the final upper-factor rows.  Each step
moves a first-column partial-pivot row into leading position, stores the pivot
row in the first row of `U`, and recursively computes the upper factor of the
first Schur complement. -/
inductive higham9_7_PartialPivotGEPPUTrace :
    (n : ℕ) → (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Prop
  | done {A U : Fin 0 → Fin 0 → ℝ} :
      higham9_7_PartialPivotGEPPUTrace 0 A U
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {r : Fin (m + 1)} {U₁ : Fin m → Fin m → ℝ}
      (hchoice : higham9_1_partialPivotChoice A 0 r)
      (hpivot : A r 0 ≠ 0)
      (hnext :
        higham9_7_PartialPivotGEPPUTrace m
          (luFirstSchurComplement
            (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) U₁) :
      higham9_7_PartialPivotGEPPUTrace (m + 1) A
        (luFirstStepU
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) U₁)

/-- **Theorem 9.7 / partial-pivoting GEPP `U` trace**, the exposed `U` rows
are upper triangular along the recursive trace. -/
theorem higham9_7_PartialPivotGEPPUTrace_upper_zero :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotGEPPUTrace n A U →
      ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro i
      exact Fin.elim0 i
  | step _hchoice _hpivot _hnext ih =>
      intro i j hij
      by_cases hi : i = 0
      · subst i
        exact (Nat.not_lt_zero _ hij).elim
      · by_cases hj : j = 0
        · subst j
          simp [luFirstStepU, hi]
        · have hpred : (j.pred hj).val < (i.pred hi).val := by
            have hival := Fin.val_pred i hi
            have hjval := Fin.val_pred j hj
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
            omega
          have hrec := ih (i.pred hi) (j.pred hj) hpred
          simpa [luFirstStepU, hi, hj] using hrec

/-- **Theorem 9.7 / partial-pivoting GEPP `U` trace**, the final upper factor
of any explicit nonsingular partial-pivoting trace satisfies the source
max-entry bound `|U_ij| <= 2^(n-1) max |A|`. -/
theorem higham9_7_PartialPivotGEPPUTrace_entry_abs_le_pow_two :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotGEPPUTrace n A U →
      ∀ (hn : 0 < n) (i j : Fin n),
        |U i j| ≤ (2 : ℝ) ^ (n - 1) * maxEntryNorm hn A := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro hn
      omega
  | step hchoice hpivot hnext ih =>
      rename_i m A r U₁
      intro hn i j
      let sigma := higham9_7_firstPivotRowSwap r
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
        higham9_2_rowPermutedMatrix A sigma
      by_cases hi : i = 0
      · subst i
        have hrow : |Aperm 0 j| ≤ maxEntryNorm (Nat.succ_pos m) A := by
          simpa [Aperm, higham9_2_rowPermutedMatrix, sigma,
            higham9_7_firstPivotRowSwap] using
            entry_le_maxEntryNorm (Nat.succ_pos m) A r j
        have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ m := by
          simpa using
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le m)
        have hM_nonneg : 0 ≤ maxEntryNorm (Nat.succ_pos m) A :=
          maxEntryNorm_nonneg (Nat.succ_pos m) A
        have hrow_pow :
            |Aperm 0 j| ≤ (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
          calc
            |Aperm 0 j| ≤ maxEntryNorm (Nat.succ_pos m) A := hrow
            _ = (1 : ℝ) * maxEntryNorm (Nat.succ_pos m) A := by ring
            _ ≤ (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A :=
                mul_le_mul_of_nonneg_right hpow_ge_one hM_nonneg
        simpa [Aperm, luFirstStepU] using hrow_pow
      · by_cases hj : j = 0
        · subst j
          have hnonneg :
              0 ≤ (2 : ℝ) ^ ((m + 1) - 1) *
                  maxEntryNorm (Nat.succ_pos m) A :=
            mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((m + 1) - 1))
              (maxEntryNorm_nonneg (Nat.succ_pos m) A)
          simpa [Aperm, luFirstStepU, hi] using hnonneg
        · have hm : 0 < m := by
            by_contra hm0
            have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
            subst hmzero
            have hival : i.val = 0 := by omega
            exact hi (Fin.ext hival)
          have hrec := ih hm (i.pred hi) (j.pred hj)
          let S : Fin m → Fin m → ℝ :=
            luFirstSchurComplement Aperm
          have hS_bound :
              maxEntryNorm hm S ≤ 2 * maxEntryNorm (Nat.succ_pos m) A := by
            simpa [S, Aperm, sigma] using
              higham9_7_partialPivot_firstSchurComplement_maxEntryNorm_le_two
                hm A r hchoice hpivot
          have hcoef_nonneg : 0 ≤ (2 : ℝ) ^ (m - 1) :=
            pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (m - 1)
          have hpow : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
            have hmidx : m = (m - 1) + 1 := by omega
            calc
              (2 : ℝ) ^ m = (2 : ℝ) ^ ((m - 1) + 1) :=
                congrArg (fun k : ℕ => (2 : ℝ) ^ k) hmidx
              _ = (2 : ℝ) ^ (m - 1) * 2 := by
                exact pow_succ (2 : ℝ) (m - 1)
          have hpow_step :
              (2 : ℝ) ^ (m - 1) * (2 * maxEntryNorm (Nat.succ_pos m) A) =
                (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
            rw [hpow]
            ring
          have htail :
              |U₁ (i.pred hi) (j.pred hj)| ≤
                (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
            calc
              |U₁ (i.pred hi) (j.pred hj)|
                  ≤ (2 : ℝ) ^ (m - 1) * maxEntryNorm hm S := by
                      simpa [S] using hrec
              _ ≤ (2 : ℝ) ^ (m - 1) *
                    (2 * maxEntryNorm (Nat.succ_pos m) A) :=
                  mul_le_mul_of_nonneg_left hS_bound hcoef_nonneg
              _ = (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := hpow_step
          simpa [Aperm, luFirstStepU, hi, hj] using htail

/-- **Theorem 9.7**, trace-level GEPP growth theorem.  Any explicit recursive
partial-pivoting upper-factor trace satisfies Higham's standard
`rho_n^p <= 2^(n-1)` max-entry growth bound. -/
theorem higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U) :
    growthFactorEntry hn A U hAmax ≤ (2 : ℝ) ^ (n - 1) := by
  apply growthFactorEntry_le_of_entry_bound_factor hn A U ((2 : ℝ) ^ (n - 1)) hAmax
  exact higham9_7_PartialPivotGEPPUTrace_entry_abs_le_pow_two htrace hn

/-- **Theorem 9.7 / Wilkinson growth witness**, the source family with unit
diagonal, `-1` below the diagonal, and a final column of ones.  In Lean's
zero-based indexing, the final source column is `j = n - 1`. -/
noncomputable def higham9_7_wilkinsonGrowthMatrix {n : ℕ} :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if j.val = i.val ∨ j.val = n - 1 then 1
    else if j.val < i.val then -1
    else 0

/-- **Theorem 9.7 / Wilkinson growth witness**, the exact unit lower factor
for the displayed Wilkinson matrix. -/
noncomputable def higham9_7_wilkinsonGrowthL {n : ℕ} :
    Fin n → Fin n → ℝ :=
  fun i j => if j.val = i.val then 1 else if j.val < i.val then -1 else 0

/-- **Theorem 9.7 / Wilkinson growth witness**, the exact upper factor.  The
final column contains the powers `2^i`, so its last entry is `2^(n-1)`. -/
noncomputable def higham9_7_wilkinsonGrowthU {n : ℕ} :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if j.val = n - 1 then (2 : ℝ) ^ i.val
    else if j.val = i.val then 1
    else 0

/-- **Theorem 9.7 / scaled Wilkinson active-stage upper factor**, the upper
factor for a reduced active stage whose final column has value `scale`. -/
noncomputable def higham9_7_wilkinsonGrowthStageU (scale : ℝ) {n : ℕ} :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if j.val = n - 1 then scale * (2 : ℝ) ^ i.val
    else if j.val = i.val then 1
    else 0

/-- The scaled active-stage upper factor with scale one is the displayed
Wilkinson witness upper factor. -/
theorem higham9_7_wilkinsonGrowthStageU_one {n : ℕ} :
    higham9_7_wilkinsonGrowthStageU 1 (n := n) =
      higham9_7_wilkinsonGrowthU (n := n) := by
  ext i j
  simp [higham9_7_wilkinsonGrowthStageU, higham9_7_wilkinsonGrowthU]

/-- **Theorem 9.7 / Wilkinson growth witness**, active-stage version of the
displayed family.  The parameter `scale` is the value in the final active
column; a no-pivot Schur step doubles it. -/
noncomputable def higham9_7_wilkinsonGrowthStageMatrix (scale : ℝ) {n : ℕ} :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if j.val = n - 1 then scale
    else if j.val = i.val then 1
    else if j.val < i.val then -1
    else 0

/-- The initial scaled-stage matrix with scale one is the displayed Wilkinson
growth witness. -/
theorem higham9_7_wilkinsonGrowthStageMatrix_one {n : ℕ} :
    higham9_7_wilkinsonGrowthStageMatrix 1 (n := n) =
      higham9_7_wilkinsonGrowthMatrix (n := n) := by
  funext i j
  unfold higham9_7_wilkinsonGrowthStageMatrix higham9_7_wilkinsonGrowthMatrix
  by_cases hlast : j.val = n - 1
  · simp [hlast]
  · simp [hlast]

/-- **Theorem 9.7 / no-interchange support**, at every nontrivial Wilkinson
stage the leading row is an admissible partial-pivoting choice.  Thus the
source's "no interchanges" claim reduces to iterating these displayed stage
matrices. -/
theorem higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero {m : ℕ}
    (scale : ℝ) :
    higham9_1_partialPivotChoice
      (higham9_7_wilkinsonGrowthStageMatrix scale (n := m + 2)) 0 0 := by
  constructor
  · simp
  · intro i _hi
    unfold higham9_7_wilkinsonGrowthStageMatrix
    by_cases hi0 : i.val = 0
    · simp [hi0]
    · have h0i_ne : ¬ (0 : ℕ) = i.val := by omega
      have h0_lt_i : (0 : ℕ) < i.val := by omega
      simp [h0i_ne, h0_lt_i]

/-- **Theorem 9.7 / reduced-matrix support**, the first no-pivot Schur
complement of a Wilkinson active-stage matrix is the next active-stage matrix
with doubled final column. -/
theorem higham9_7_wilkinsonGrowthStage_firstSchurComplement {m : ℕ}
    (scale : ℝ) :
    luFirstSchurComplement
        (higham9_7_wilkinsonGrowthStageMatrix scale (n := m + 2)) =
      higham9_7_wilkinsonGrowthStageMatrix (2 * scale) (n := m + 1) := by
  funext i j
  unfold luFirstSchurComplement higham9_7_wilkinsonGrowthStageMatrix
  by_cases hlast : j.succ.val = m + 2 - 1
  · have hlast_m : j.val = m := by
      have hj : j.succ.val = j.val + 1 := rfl
      omega
    simp [hlast_m]
    ring
  · have hlast_m : ¬ j.val = m := by
      intro hjlast
      have hj : j.succ.val = j.val + 1 := rfl
      exact hlast (by omega)
    simp [hlast_m]

/-- The power-of-two stage form of the Wilkinson Schur-complement doubling
identity. -/
theorem higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement {m t : ℕ} :
    luFirstSchurComplement
        (higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ t) (n := m + 2)) =
      higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ (t + 1)) (n := m + 1) := by
  rw [higham9_7_wilkinsonGrowthStage_firstSchurComplement]
  rw [pow_succ]
  ring_nf

/-- **Theorem 9.7 / no-interchange GEPP trace**, a compact exact-arithmetic
trace predicate for partial pivoting when every active step chooses row zero.
This records the source "no row interchanges" route without modeling floating
point arithmetic. -/
inductive higham9_7_PartialPivotNoInterchangeTrace :
    ℕ → (n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | done {t : ℕ} {A : Fin 0 → Fin 0 → ℝ} :
      higham9_7_PartialPivotNoInterchangeTrace t 0 A
  | step {t m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      (hchoice : higham9_1_partialPivotChoice A 0 0)
      (hpivot : A 0 0 ≠ 0)
      (hnext :
        higham9_7_PartialPivotNoInterchangeTrace (t + 1) m
          (luFirstSchurComplement A)) :
      higham9_7_PartialPivotNoInterchangeTrace t (m + 1) A

/-- **Theorem 9.7 / no-interchange support**, row zero is a valid
partial-pivoting choice for every nonempty scaled Wilkinson active stage. -/
theorem higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero_succ {m : ℕ}
    (scale : ℝ) :
    higham9_1_partialPivotChoice
      (higham9_7_wilkinsonGrowthStageMatrix scale (n := m + 1)) 0 0 := by
  cases m with
  | zero =>
      constructor
      · simp
      · intro i _hi
        fin_cases i
        simp
  | succ m =>
      simpa using
        higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero (m := m) scale

/-- **Theorem 9.7 / no-interchange support**, the row-zero pivot in every
power-of-two scaled Wilkinson active stage is nonzero. -/
theorem higham9_7_wilkinsonGrowthStage_pivot_zero_ne_zero {m t : ℕ} :
    higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ t)
      (0 : Fin (m + 1)) 0 ≠ 0 := by
  cases m with
  | zero =>
      simp [higham9_7_wilkinsonGrowthStageMatrix]
  | succ m =>
      simp [higham9_7_wilkinsonGrowthStageMatrix]

/-- **Theorem 9.7 / no-interchange support**, the Schur-complement doubling
identity, including the `1 by 1` terminal step. -/
theorem higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement_succ
    {m t : ℕ} :
    luFirstSchurComplement
        (higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ t) (n := m + 1)) =
      higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ (t + 1)) (n := m) := by
  cases m with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ m =>
      simpa using
        higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement (m := m) (t := t)

/-- **Theorem 9.7 / Wilkinson no-interchange GEPP trace**, every power-of-two
scaled active-stage matrix follows the no-row-interchange partial-pivoting
trace.  This closes the source trace for the displayed Wilkinson growth family;
the separate extremal characterization remains open. -/
theorem higham9_7_wilkinsonGrowthStage_noInterchangeTrace :
    ∀ n t : ℕ,
      higham9_7_PartialPivotNoInterchangeTrace t n
        (higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ t) (n := n))
  | 0, t => higham9_7_PartialPivotNoInterchangeTrace.done
  | m + 1, t =>
      by
        refine higham9_7_PartialPivotNoInterchangeTrace.step
          (higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero_succ
            (m := m) ((2 : ℝ) ^ t))
          (higham9_7_wilkinsonGrowthStage_pivot_zero_ne_zero (m := m) (t := t))
          ?_
        rw [higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement_succ]
        exact higham9_7_wilkinsonGrowthStage_noInterchangeTrace m (t + 1)

/-- **Theorem 9.7 / Wilkinson no-interchange GEPP trace**, source-facing
version for the displayed initial matrix. -/
theorem higham9_7_wilkinsonGrowth_noInterchangeTrace (n : ℕ) :
    higham9_7_PartialPivotNoInterchangeTrace 0 n
      (higham9_7_wilkinsonGrowthMatrix (n := n)) := by
  simpa [higham9_7_wilkinsonGrowthStageMatrix_one] using
    higham9_7_wilkinsonGrowthStage_noInterchangeTrace n 0

/-- Uniform max-entry bound for a scaled Wilkinson active-stage matrix. -/
theorem higham9_7_wilkinsonGrowthStage_entry_abs_le_scale {n : ℕ}
    {scale : ℝ} (hscale_nonneg : 0 ≤ scale) (hscale_one : 1 ≤ scale)
    (i j : Fin n) :
    |higham9_7_wilkinsonGrowthStageMatrix scale i j| ≤ scale := by
  unfold higham9_7_wilkinsonGrowthStageMatrix
  by_cases hlast : j.val = n - 1
  · simp [hlast, abs_of_nonneg hscale_nonneg]
  · by_cases hdiag : j.val = i.val
    · have hilast : i.val ≠ n - 1 := by
        intro hi
        exact hlast (hdiag.trans hi)
      simp [hdiag, hilast]
      exact hscale_one
    · by_cases hlt : j.val < i.val
      · simp [hlast, hdiag, hlt]
        exact hscale_one
      · simp [hlast, hdiag, hlt, hscale_nonneg]

/-- A scaled Wilkinson active-stage matrix has max-entry norm equal to its
final-column scale whenever that scale is at least one. -/
theorem higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_scale {n : ℕ}
    (hn : 0 < n) {scale : ℝ}
    (hscale_nonneg : 0 ≤ scale) (hscale_one : 1 ≤ scale) :
    maxEntryNorm hn
        (higham9_7_wilkinsonGrowthStageMatrix scale (n := n)) =
      scale := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    exact higham9_7_wilkinsonGrowthStage_entry_abs_le_scale
      hscale_nonneg hscale_one i j
  · let last : Fin n := ⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩
    have hentry :
        |higham9_7_wilkinsonGrowthStageMatrix scale
            (⟨0, hn⟩ : Fin n) last| = scale := by
      simp [higham9_7_wilkinsonGrowthStageMatrix, last,
        abs_of_nonneg hscale_nonneg]
    have hle :=
      entry_le_maxEntryNorm hn
        (higham9_7_wilkinsonGrowthStageMatrix scale (n := n))
        (⟨0, hn⟩ : Fin n) last
    simpa [hentry] using hle

/-- At Wilkinson stage `t`, the active matrix has max-entry norm `2^t`. -/
theorem higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_pow {n t : ℕ}
    (hn : 0 < n) :
    maxEntryNorm hn
        (higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ t) (n := n)) =
      (2 : ℝ) ^ t := by
  exact higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_scale hn
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) t)
    (by
      have hpow : (2 : ℝ) ^ 0 ≤ (2 : ℝ) ^ t :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le t)
      simpa using hpow)

/-- The lower factor row of the Wilkinson witness satisfies the final-column
power identity `2^i - sum_{k<i} 2^k = 1`. -/
theorem higham9_7_wilkinsonGrowthL_two_pow_sum {n : ℕ} (i : Fin n) :
    (∑ k : Fin n, higham9_7_wilkinsonGrowthL i k * (2 : ℝ) ^ k.val) = 1 := by
  induction n with
  | zero =>
      exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [Fin.sum_univ_succ]
          simp [higham9_7_wilkinsonGrowthL]
      | succ i =>
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ k : Fin n,
                  higham9_7_wilkinsonGrowthL (Fin.succ i) k.succ *
                    (2 : ℝ) ^ k.succ.val) =
                2 *
                  (∑ k : Fin n,
                    higham9_7_wilkinsonGrowthL i k * (2 : ℝ) ^ k.val) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            by_cases hki : k.val = i.val
            · simp [higham9_7_wilkinsonGrowthL, hki, pow_succ]
              ring
            · by_cases hklt : k.val < i.val
              · simp [higham9_7_wilkinsonGrowthL, hki, hklt, pow_succ]
                ring
              · simp [higham9_7_wilkinsonGrowthL, hki, hklt, pow_succ]
          calc
            higham9_7_wilkinsonGrowthL (Fin.succ i) 0 *
                  (2 : ℝ) ^ (0 : Fin (n + 1)).val +
                (∑ x : Fin n,
                  higham9_7_wilkinsonGrowthL (Fin.succ i) x.succ *
                    (2 : ℝ) ^ x.succ.val)
                = (-1 : ℝ) + 2 * 1 := by
                    rw [htail, ih i]
                    simp [higham9_7_wilkinsonGrowthL]
            _ = 1 := by norm_num

/-- **Theorem 9.7 / scaled Wilkinson active-stage witness**, exact LU
certificate for every scaled active-stage matrix.  This is the algebraic
certificate behind the source no-interchange stage recurrence; the executable
partial-pivoting trace remains recorded separately. -/
theorem higham9_7_wilkinsonGrowthStage_lu (n : ℕ) (scale : ℝ) :
    LUFactSpec n (higham9_7_wilkinsonGrowthStageMatrix scale (n := n))
      (higham9_7_wilkinsonGrowthL (n := n))
      (higham9_7_wilkinsonGrowthStageU scale (n := n)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp [higham9_7_wilkinsonGrowthL]
  · intro i j hij
    have hne : j.val ≠ i.val := by omega
    have hnotlt : ¬ j.val < i.val := by omega
    simp [higham9_7_wilkinsonGrowthL, hne, hnotlt]
  · intro i j hij
    have hnotlast : j.val ≠ n - 1 := by
      intro hlast
      have hle : i.val ≤ n - 1 := Nat.le_sub_one_of_lt i.isLt
      omega
    have hne : j.val ≠ i.val := by omega
    simp [higham9_7_wilkinsonGrowthStageU, hnotlast, hne]
  · intro i j
    by_cases hlast : j.val = n - 1
    · calc
        (∑ k : Fin n,
            higham9_7_wilkinsonGrowthL i k *
              higham9_7_wilkinsonGrowthStageU scale k j)
            = scale * ∑ k : Fin n,
                higham9_7_wilkinsonGrowthL i k * (2 : ℝ) ^ k.val := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _
                simp [higham9_7_wilkinsonGrowthStageU, hlast, mul_assoc,
                  mul_comm]
        _ = scale * 1 := by rw [higham9_7_wilkinsonGrowthL_two_pow_sum i]
        _ = higham9_7_wilkinsonGrowthStageMatrix scale i j := by
            simp [higham9_7_wilkinsonGrowthStageMatrix, hlast]
    · have hsum :
          (∑ k : Fin n,
              higham9_7_wilkinsonGrowthL i k *
                higham9_7_wilkinsonGrowthStageU scale k j) =
            higham9_7_wilkinsonGrowthL i j := by
        calc
          (∑ k : Fin n,
              higham9_7_wilkinsonGrowthL i k *
                higham9_7_wilkinsonGrowthStageU scale k j)
              = ∑ k : Fin n,
                  if k = j then higham9_7_wilkinsonGrowthL i j else 0 := by
                  apply Finset.sum_congr rfl
                  intro k _
                  by_cases hkj : k = j
                  · subst hkj
                    simp [higham9_7_wilkinsonGrowthStageU, hlast]
                  · have hjk : j.val ≠ k.val := by
                      intro hv
                      exact hkj (Fin.ext hv.symm)
                    simp [higham9_7_wilkinsonGrowthStageU, hlast, hjk, hkj]
          _ = higham9_7_wilkinsonGrowthL i j := by simp
      rw [hsum]
      simp [higham9_7_wilkinsonGrowthStageMatrix, higham9_7_wilkinsonGrowthL,
        hlast]

/-- Every entry of the scaled active-stage upper factor is bounded by
`scale * 2^(n-1)` whenever `scale >= 1`. -/
theorem higham9_7_wilkinsonGrowthStageU_entry_abs_le_scale_pow {n : ℕ}
    {scale : ℝ} (hscale_nonneg : 0 ≤ scale) (hscale_one : 1 ≤ scale)
    (i j : Fin n) :
    |higham9_7_wilkinsonGrowthStageU scale i j| ≤
      scale * (2 : ℝ) ^ (n - 1) := by
  unfold higham9_7_wilkinsonGrowthStageU
  by_cases hlast : j.val = n - 1
  · simp [hlast, abs_of_nonneg (mul_nonneg hscale_nonneg
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i.val))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (Nat.le_sub_one_of_lt i.isLt)) hscale_nonneg
  · by_cases hdiag : j.val = i.val
    · have hilast : i.val ≠ n - 1 := by
        intro hi
        exact hlast (hdiag.trans hi)
      simp [hdiag, hilast]
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (n - 1) := by
        simpa using
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le (n - 1))
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ scale * (2 : ℝ) ^ (n - 1) :=
          mul_le_mul hscale_one hpow (by norm_num) hscale_nonneg
    · simp [hlast, hdiag, hscale_nonneg]

/-- The scaled active-stage upper factor has max-entry norm
`scale * 2^(n-1)` whenever `scale >= 1`. -/
theorem higham9_7_wilkinsonGrowthStageU_maxEntryNorm_eq_scale_pow {n : ℕ}
    (hn : 0 < n) {scale : ℝ}
    (hscale_nonneg : 0 ≤ scale) (hscale_one : 1 ≤ scale) :
    maxEntryNorm hn (higham9_7_wilkinsonGrowthStageU scale (n := n)) =
      scale * (2 : ℝ) ^ (n - 1) := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    exact higham9_7_wilkinsonGrowthStageU_entry_abs_le_scale_pow
      hscale_nonneg hscale_one i j
  · let last : Fin n := ⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩
    have hentry :
        |higham9_7_wilkinsonGrowthStageU scale last last| =
          scale * (2 : ℝ) ^ (n - 1) := by
      simp [higham9_7_wilkinsonGrowthStageU, last,
        abs_of_nonneg (mul_nonneg hscale_nonneg
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n - 1)))]
    have hle :=
      entry_le_maxEntryNorm hn
        (higham9_7_wilkinsonGrowthStageU scale (n := n)) last last
    simpa [hentry] using hle

/-- **Theorem 9.7 / scaled active-stage growth**, every scaled active-stage
Wilkinson matrix has exact max-entry growth `2^(n-1)` for its scaled upper
factor, provided the scale is at least one. -/
theorem higham9_7_wilkinsonGrowthStage_growthFactorEntry_eq_pow {n : ℕ}
    (hn : 0 < n) {scale : ℝ}
    (hscale_nonneg : 0 ≤ scale) (hscale_one : 1 ≤ scale) :
    growthFactorEntry hn
        (higham9_7_wilkinsonGrowthStageMatrix scale (n := n))
        (higham9_7_wilkinsonGrowthStageU scale (n := n))
        (by
          rw [higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_scale hn
            hscale_nonneg hscale_one]
          linarith) =
      (2 : ℝ) ^ (n - 1) := by
  have hscale_pos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale_one
  unfold growthFactorEntry
  rw [higham9_7_wilkinsonGrowthStageU_maxEntryNorm_eq_scale_pow hn
      hscale_nonneg hscale_one,
    higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_scale hn
      hscale_nonneg hscale_one]
  field_simp [ne_of_gt hscale_pos]

/-- **Theorem 9.7 / Wilkinson growth witness**, exact LU certificate for the
displayed matrix family.  This is the algebraic witness behind the source
statement that the final column doubles under the no-interchange GEPP route;
the recursive no-interchange trace is closed separately by
`higham9_7_wilkinsonGrowth_noInterchangeTrace`. -/
theorem higham9_7_wilkinsonGrowth_lu (n : ℕ) :
    LUFactSpec n (higham9_7_wilkinsonGrowthMatrix (n := n))
      (higham9_7_wilkinsonGrowthL (n := n))
      (higham9_7_wilkinsonGrowthU (n := n)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp [higham9_7_wilkinsonGrowthL]
  · intro i j hij
    have hne : j.val ≠ i.val := by omega
    have hnotlt : ¬ j.val < i.val := by omega
    simp [higham9_7_wilkinsonGrowthL, hne, hnotlt]
  · intro i j hij
    have hnotlast : j.val ≠ n - 1 := by
      intro hlast
      have hle : i.val ≤ n - 1 := Nat.le_sub_one_of_lt i.isLt
      omega
    have hne : j.val ≠ i.val := by omega
    simp [higham9_7_wilkinsonGrowthU, hnotlast, hne]
  · intro i j
    by_cases hlast : j.val = n - 1
    · calc
        (∑ k : Fin n,
            higham9_7_wilkinsonGrowthL i k *
              higham9_7_wilkinsonGrowthU k j)
            = ∑ k : Fin n,
                higham9_7_wilkinsonGrowthL i k * (2 : ℝ) ^ k.val := by
                apply Finset.sum_congr rfl
                intro k _
                simp [higham9_7_wilkinsonGrowthU, hlast]
        _ = 1 := higham9_7_wilkinsonGrowthL_two_pow_sum i
        _ = higham9_7_wilkinsonGrowthMatrix i j := by
            simp [higham9_7_wilkinsonGrowthMatrix, hlast]
    · have hsum :
          (∑ k : Fin n,
              higham9_7_wilkinsonGrowthL i k *
                higham9_7_wilkinsonGrowthU k j) =
            higham9_7_wilkinsonGrowthL i j := by
        calc
          (∑ k : Fin n,
              higham9_7_wilkinsonGrowthL i k *
                higham9_7_wilkinsonGrowthU k j)
              = ∑ k : Fin n,
                  if k = j then higham9_7_wilkinsonGrowthL i j else 0 := by
                  apply Finset.sum_congr rfl
                  intro k _
                  by_cases hkj : k = j
                  · subst hkj
                    simp [higham9_7_wilkinsonGrowthU, hlast]
                  · have hjk : j.val ≠ k.val := by
                      intro hv
                      exact hkj (Fin.ext hv.symm)
                    simp [higham9_7_wilkinsonGrowthU, hlast, hjk, hkj]
          _ = higham9_7_wilkinsonGrowthL i j := by simp
      rw [hsum]
      simp [higham9_7_wilkinsonGrowthMatrix, higham9_7_wilkinsonGrowthL, hlast]

/-- Every entry of the Wilkinson growth witness has absolute value at most
one. -/
theorem higham9_7_wilkinsonGrowthMatrix_entry_abs_le_one {n : ℕ}
    (i j : Fin n) :
    |higham9_7_wilkinsonGrowthMatrix i j| ≤ 1 := by
  unfold higham9_7_wilkinsonGrowthMatrix
  by_cases hmain : j.val = i.val ∨ j.val = n - 1
  · simp [hmain]
  · by_cases hlt : j.val < i.val
    · simp [hmain, hlt]
    · simp [hmain, hlt]

/-- The Wilkinson growth witness has source max-entry norm one. -/
theorem higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_eq_one {n : ℕ}
    (hn : 0 < n) :
    maxEntryNorm hn (higham9_7_wilkinsonGrowthMatrix (n := n)) = 1 := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    exact higham9_7_wilkinsonGrowthMatrix_entry_abs_le_one i j
  · have hentry :
        |higham9_7_wilkinsonGrowthMatrix (⟨0, hn⟩ : Fin n) ⟨0, hn⟩| = 1 := by
      simp [higham9_7_wilkinsonGrowthMatrix]
    have hle :=
      entry_le_maxEntryNorm hn (higham9_7_wilkinsonGrowthMatrix (n := n))
        (⟨0, hn⟩ : Fin n) ⟨0, hn⟩
    simpa [hentry] using hle

/-- The Wilkinson growth witness has positive source max-entry norm. -/
theorem higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_pos {n : ℕ}
    (hn : 0 < n) :
    0 < maxEntryNorm hn (higham9_7_wilkinsonGrowthMatrix (n := n)) := by
  simp [higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_eq_one hn]

/-- Every entry of the upper factor is bounded by the final-column value
`2^(n-1)`. -/
theorem higham9_7_wilkinsonGrowthU_entry_abs_le_pow {n : ℕ}
    (i j : Fin n) :
    |higham9_7_wilkinsonGrowthU i j| ≤ (2 : ℝ) ^ (n - 1) := by
  unfold higham9_7_wilkinsonGrowthU
  by_cases hlast : j.val = n - 1
  · simp [hlast, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i.val)]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.le_sub_one_of_lt i.isLt)
  · by_cases hdiag : j.val = i.val
    · have hilast : i.val ≠ n - 1 := by
        intro hi
        exact hlast (hdiag.trans hi)
      simp [hdiag, hilast]
      have hpow : (2 : ℝ) ^ 0 ≤ (2 : ℝ) ^ (n - 1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le (n - 1))
      simpa using hpow
    · simp [hlast, hdiag]

/-- The exact upper factor of the Wilkinson witness has max-entry norm
`2^(n-1)`. -/
theorem higham9_7_wilkinsonGrowthU_maxEntryNorm_eq_pow {n : ℕ}
    (hn : 0 < n) :
    maxEntryNorm hn (higham9_7_wilkinsonGrowthU (n := n)) =
      (2 : ℝ) ^ (n - 1) := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    exact higham9_7_wilkinsonGrowthU_entry_abs_le_pow i j
  · let last : Fin n := ⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩
    have hentry :
        |higham9_7_wilkinsonGrowthU last last| = (2 : ℝ) ^ (n - 1) := by
      simp [higham9_7_wilkinsonGrowthU, last,
        abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n - 1))]
    have hle :=
      entry_le_maxEntryNorm hn (higham9_7_wilkinsonGrowthU (n := n)) last last
    simpa [hentry] using hle

/-- **Theorem 9.7 / Wilkinson growth witness**, the displayed family attains
the max-entry growth value `2^(n-1)` for the exact upper factor above. -/
theorem higham9_7_wilkinsonGrowth_growthFactorEntry_eq_pow {n : ℕ}
    (hn : 0 < n) :
    growthFactorEntry hn (higham9_7_wilkinsonGrowthMatrix (n := n))
        (higham9_7_wilkinsonGrowthU (n := n))
        (higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_pos hn) =
      (2 : ℝ) ^ (n - 1) := by
  unfold growthFactorEntry
  rw [higham9_7_wilkinsonGrowthU_maxEntryNorm_eq_pow hn,
    higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_eq_one hn]
  ring

/-- **Theorem 9.7**, source-facing Wilkinson attainability package.  The
displayed Wilkinson family has an exact LU certificate, follows the closed
no-interchange partial-pivoting trace, and attains the bound `2^(n-1)`. -/
theorem higham9_7_wilkinsonGrowth_attains_partialPivoting_bound {n : ℕ}
    (hn : 0 < n) :
    ∃ A L U : Fin n → Fin n → ℝ,
    ∃ hAmax : 0 < maxEntryNorm hn A,
      LUFactSpec n A L U ∧
      higham9_7_PartialPivotNoInterchangeTrace 0 n A ∧
      growthFactorEntry hn A U hAmax = (2 : ℝ) ^ (n - 1) := by
  refine ⟨higham9_7_wilkinsonGrowthMatrix (n := n),
    higham9_7_wilkinsonGrowthL (n := n),
    higham9_7_wilkinsonGrowthU (n := n),
    higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_pos hn, ?_, ?_, ?_⟩
  · exact higham9_7_wilkinsonGrowth_lu n
  · exact higham9_7_wilkinsonGrowth_noInterchangeTrace n
  · exact higham9_7_wilkinsonGrowth_growthFactorEntry_eq_pow hn

/-- **Equation (9.2a)**, source-facing exact permuted LU certificate
`PA = LU`. -/
abbrev higham9_2_PermutedLUFactSpec (n : ℕ)
    (A L U : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n) : Prop :=
  PermutedLUFactSpec n A L U sigma

/-- **Equation (9.2a)**, a source `PA = LU` certificate is an ordinary exact LU
certificate for the row-permuted matrix. -/
theorem higham9_2_permutedLUFactSpec_to_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hLU : higham9_2_PermutedLUFactSpec n A L U sigma) :
    LUFactSpec n (higham9_2_rowPermutedMatrix A sigma) L U where
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  product_eq := by
    intro i j
    simpa [higham9_2_rowPermutedMatrix] using hLU.product_eq i j

/-- **Equation (9.2a)**, determinant-pivot product for an explicit
row-permuted LU certificate `PA = LU`. -/
theorem higham9_2_permutedLUFactSpec_det_eq_pivot_product {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hLU : higham9_2_PermutedLUFactSpec n A L U sigma) :
    Matrix.det
        (Matrix.of (higham9_2_rowPermutedMatrix A sigma) :
          Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i :=
  (higham9_2_permutedLUFactSpec_to_LUFactSpec hLU).det_eq_prod_U_diag

/-- **Equation (9.2a)**, nonsingularity consequence for an explicit
row-permuted LU certificate. -/
theorem higham9_2_permutedLUFactSpec_det_ne_zero_iff_pivots_ne_zero {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hLU : higham9_2_PermutedLUFactSpec n A L U sigma) :
    Matrix.det
        (Matrix.of (higham9_2_rowPermutedMatrix A sigma) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0 ↔
      ∀ i : Fin n, U i i ≠ 0 :=
  (higham9_2_permutedLUFactSpec_to_LUFactSpec hLU).det_ne_zero_iff_U_diag_ne_zero

/-- **Theorem 9.3 / equation (9.2a)**, source-facing permuted LU backward-error
certificate. -/
abbrev higham9_2_PermutedLUBackwardError (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n)
    (ε : ℝ) : Prop :=
  PermutedLUBackwardError n A L_hat U_hat sigma ε

/-- **Theorem 9.3 / equation (9.2a)**, a pivoted backward-error certificate is
an ordinary LU backward-error certificate for the row-permuted matrix `PA`. -/
theorem higham9_2_permutedLUBackwardError_to_LUBackwardError {n : ℕ}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    {ε : ℝ}
    (hLU : higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma ε) :
    LUBackwardError n (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat ε where
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  backward_bound := by
    intro i j
    simpa [higham9_2_rowPermutedMatrix] using hLU.backward_bound i j

/-- **Equation (9.2a)**, row permutations preserve Higham's max-entry norm. -/
theorem higham9_2_rowPermutedMatrix_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) {sigma : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) :
    maxEntryNorm hn (higham9_2_rowPermutedMatrix A sigma) = maxEntryNorm hn A := by
  classical
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hsigma
  apply le_antisymm
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne
          (fun j => |higham9_2_rowPermutedMatrix A sigma i j|)) ≤
      maxEntryNorm hn A
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [higham9_2_rowPermutedMatrix] using
      entry_le_maxEntryNorm hn A (sigma i) j
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |A i j|)) ≤
      maxEntryNorm hn (higham9_2_rowPermutedMatrix A sigma)
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have hsigma_symm : sigma (eSigma.symm i) = i := by
      change eSigma (eSigma.symm i) = i
      exact Equiv.apply_symm_apply eSigma i
    simpa [higham9_2_rowPermutedMatrix, hsigma_symm] using
      entry_le_maxEntryNorm hn (higham9_2_rowPermutedMatrix A sigma)
        (eSigma.symm i) j

/-- **Equation (9.2a)**, row permutations preserve the matrix infinity norm. -/
theorem higham9_2_rowPermutedMatrix_infNorm {n : ℕ}
    (A : Fin n → Fin n → ℝ) {sigma : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) :
    infNorm (higham9_2_rowPermutedMatrix A sigma) = infNorm A := by
  classical
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hsigma
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      simpa [higham9_2_rowPermutedMatrix] using row_sum_le_infNorm A (sigma i)
    · exact infNorm_nonneg A
  · apply infNorm_le_of_row_sum_le
    · intro i
      have hsigma_symm : sigma (eSigma.symm i) = i := by
        change eSigma (eSigma.symm i) = i
        exact Equiv.apply_symm_apply eSigma i
      simpa [higham9_2_rowPermutedMatrix, hsigma_symm] using
        row_sum_le_infNorm (higham9_2_rowPermutedMatrix A sigma) (eSigma.symm i)
    · exact infNorm_nonneg (higham9_2_rowPermutedMatrix A sigma)

/-- **Equation (9.1)**, determinant-pivot product for an exact LU
certificate: if `A = L U` with unit lower triangular `L` and upper triangular
`U`, then `det(A)` is the product of the diagonal pivots of `U`.  Theorem 9.1's
existence/uniqueness direction remains a separate determinant-integrated LU
target. -/
theorem higham9_1_det_eq_pivot_product {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i :=
  hLU.det_eq_prod_U_diag

/-- **Equation (9.1)**, nonzero-pivot consequence of the determinant product:
an exact LU certificate is nonsingular exactly when all diagonal pivots of `U`
are nonzero. -/
theorem higham9_1_det_ne_zero_iff_pivots_ne_zero {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 ↔
      ∀ i : Fin n, U i i ≠ 0 :=
  hLU.det_ne_zero_iff_U_diag_ne_zero

/-- **Theorem 9.1 support**, first Schur complement for the exact no-pivot LU
existence induction. -/
noncomputable abbrev higham9_1_firstSchurComplement {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) : Fin m → Fin m → ℝ :=
  luFirstSchurComplement A

/-- **Theorem 9.1 support**, one exact no-pivot LU construction step.
If the first pivot is nonzero and the first Schur complement has an exact
unit-lower/upper LU certificate, then the original matrix has an exact
unit-lower/upper LU certificate.  This is the local induction step toward the
source existence theorem from nonsingular leading principal submatrices. -/
theorem higham9_1_lu_exists_of_firstSchurComplement {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpivot : A 0 0 ≠ 0)
    {L₁ U₁ : Fin m → Fin m → ℝ}
    (hS : LUFactSpec m (higham9_1_firstSchurComplement A) L₁ U₁) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → ℝ,
      LUFactSpec (m + 1) A L U :=
  LUFactSpec.of_firstSchurComplement hpivot hS

/-- Sum truncation over a leading `Fin k` prefix when all later terms vanish.
This is the small finite-sum adapter used to pass exact LU certificates to
leading principal blocks. -/
private lemma sum_fin_eq_sum_castLE_of_eq_zero {n k : ℕ} (hk : k ≤ n)
    (f : Fin n → ℝ) (hzero : ∀ r : Fin n, k ≤ r.val → f r = 0) :
    (∑ r : Fin n, f r) = ∑ r : Fin k, f (Fin.castLE hk r) := by
  classical
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  have hsmall :
      (∑ x ∈ Finset.range k,
        if hx : x < k then f (Fin.castLE hk ⟨x, hx⟩) else 0) =
        ∑ x ∈ Finset.range k, if hx : x < n then f ⟨x, hx⟩ else 0 := by
    apply Finset.sum_congr rfl
    intro x hxmem
    have hxk : x < k := by
      simpa [Finset.mem_range] using hxmem
    have hxn : x < n := Nat.lt_of_lt_of_le hxk hk
    simp [hxk, hxn, Fin.castLE]
  rw [hsmall]
  symm
  apply Finset.sum_subset
    (by
      intro x hx
      have hxk : x < k := by
        simpa [Finset.mem_range] using hx
      simp [Finset.mem_range, Nat.lt_of_lt_of_le hxk hk])
    (by
      intro x hx_n hx_not_k
      have hxn : x < n := by
        simpa [Finset.mem_range] using hx_n
      have hxge : k ≤ x := by
        exact Nat.le_of_not_gt (by simpa [Finset.mem_range] using hx_not_k)
      simp [hxn, hzero ⟨x, hxn⟩ hxge])

/-- **Theorem 9.1 / Problem 9.2 support**, leading-principal determinant
product for an exact LU certificate.  If a full exact `LUFactSpec` is already
available, then every leading principal block determinant is the product of the
corresponding leading pivots.  This is only the determinant side of Higham's
Theorem 9.1; the existence and uniqueness of the exact LU certificate from
nonzero leading principal minors remains a separate target. -/
theorem higham9_1_leadingPrincipalBlock_det_eq_pivot_product {n k : ℕ}
    (hk : k ≤ n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (fun i j : Fin k => A (Fin.castLE hk i) (Fin.castLE hk j)) =
      ∏ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i) := by
  classical
  let Aₖ : Fin k → Fin k → ℝ :=
    fun i j => A (Fin.castLE hk i) (Fin.castLE hk j)
  let Lₖ : Fin k → Fin k → ℝ :=
    fun i j => L (Fin.castLE hk i) (Fin.castLE hk j)
  let Uₖ : Fin k → Fin k → ℝ :=
    fun i j => U (Fin.castLE hk i) (Fin.castLE hk j)
  have hLUₖ : LUFactSpec k Aₖ Lₖ Uₖ := by
    refine
      { L_diag := ?_
        L_upper_zero := ?_
        U_lower_zero := ?_
        product_eq := ?_ }
    · intro i
      simp [Lₖ, hLU.L_diag]
    · intro i j hij
      exact hLU.L_upper_zero (Fin.castLE hk i) (Fin.castLE hk j) (by simpa using hij)
    · intro i j hij
      exact hLU.U_lower_zero (Fin.castLE hk i) (Fin.castLE hk j) (by simpa using hij)
    · intro i j
      have hsum :
          (∑ r : Fin n,
              L (Fin.castLE hk i) r * U r (Fin.castLE hk j)) =
            ∑ r : Fin k,
              L (Fin.castLE hk i) (Fin.castLE hk r) *
                U (Fin.castLE hk r) (Fin.castLE hk j) := by
        apply sum_fin_eq_sum_castLE_of_eq_zero hk
        intro r hr
        have hj_lt_r : (Fin.castLE hk j).val < r.val := by
          have hj_lt_k : j.val < k := j.isLt
          simpa using Nat.lt_of_lt_of_le hj_lt_k hr
        simp [hLU.U_lower_zero r (Fin.castLE hk j) hj_lt_r]
      have hprod := hLU.product_eq (Fin.castLE hk i) (Fin.castLE hk j)
      calc
        (∑ r : Fin k, Lₖ i r * Uₖ r j)
            = ∑ r : Fin k,
                L (Fin.castLE hk i) (Fin.castLE hk r) *
                  U (Fin.castLE hk r) (Fin.castLE hk j) := by
              simp [Lₖ, Uₖ]
        _ = ∑ r : Fin n,
              L (Fin.castLE hk i) r * U r (Fin.castLE hk j) := hsum.symm
        _ = A (Fin.castLE hk i) (Fin.castLE hk j) := hprod
        _ = Aₖ i j := by simp [Aₖ]
  simpa [Aₖ, Uₖ] using hLUₖ.det_eq_prod_U_diag

/-- **Theorem 9.1 / Problem 9.2 support**, nonzero leading determinant
consequence for an exact LU certificate: a leading principal block is
nonsingular exactly when its corresponding leading pivots are nonzero. -/
theorem higham9_1_leadingPrincipalBlock_det_ne_zero_iff_pivots_ne_zero {n k : ℕ}
    (hk : k ≤ n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (fun i j : Fin k => A (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0 ↔
      ∀ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i) ≠ 0 := by
  rw [higham9_1_leadingPrincipalBlock_det_eq_pivot_product hk hLU]
  simpa using
    (Finset.prod_ne_zero_iff :
      (∏ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i)) ≠ 0 ↔
        ∀ i ∈ (Finset.univ : Finset (Fin k)),
          U (Fin.castLE hk i) (Fin.castLE hk i) ≠ 0)

/-- **Algorithm 9.2**, dense square executable-loop certificate.  This records
that the stored factors come from the literal rounded Doolittle row and column
folds, together with the visible residual-compression budgets needed to produce
the compact `DoolittleLU` recurrence certificate. -/
abbrev higham9_2_DoolittleDenseLoopCertificate (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (fp : FPModel) : Prop :=
  DoolittleDenseLoopCertificate n A L_hat U_hat fp

/-- **Algorithm 9.2**, dense square absolute-budget certificate.  This is the
implementation-facing layer immediately below
`higham9_2_DoolittleDenseLoopCertificate`: absolute residual budgets are kept
explicit until separate dominance hypotheses compress them to the relative
Doolittle recurrence budget. -/
abbrev higham9_2_DoolittleDenseLoopAbsBudgetCertificate (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (fp : FPModel)
    (BU BL : Fin n → Fin n → ℝ) : Prop :=
  DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp BU BL

/-- **Algorithm 9.2**, dense-loop handoff: a literal dense Doolittle loop
certificate with visible compression budgets produces the compact source-facing
`DoolittleLU` certificate used by Theorem 9.3. -/
theorem higham9_2_denseLoopCertificate_to_DoolittleLU {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hn : gammaValid fp n) :
    higham9_2_DoolittleLU n A L_hat U_hat fp :=
  DoolittleDenseLoopCertificate.to_DoolittleLU hC (gamma_nonneg fp hn)

/-- **Algorithm 9.2**, absolute-budget handoff: explicit upper/lower absolute
budgets plus their dominance proofs produce the compact source-facing
`DoolittleLU` certificate. -/
theorem higham9_2_absBudgetCertificate_to_DoolittleLU {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    {BU BL : Fin n → Fin n → ℝ}
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp BU BL)
    (hn : gammaValid fp n) :
    higham9_2_DoolittleLU n A L_hat U_hat fp :=
  DoolittleDenseLoopAbsBudgetCertificate.to_DoolittleLU hC (gamma_nonneg fp hn)

/-- **Theorem 9.3**, pivoted certificate form: if Gaussian elimination with
row pivoting has produced a backward-error certificate for `PA`, then the
standard `gamma_n` perturbation theorem applies to the row-permuted source
matrix.  This is a certificate adapter only; it does not construct the pivot
trace or prove that a particular loop produced the certificate. -/
theorem higham9_3_permuted_lu_backward_error_gamma {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hn : gammaValid fp n)
    (hLU :
      higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n)) :
    ∃ ΔPA : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPA i j| ≤
          gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L_hat i k * U_hat k j =
          higham9_2_rowPermutedMatrix A sigma i j + ΔPA i j) :=
  lu_backward_error_gamma fp n (higham9_2_rowPermutedMatrix A sigma)
    L_hat U_hat hn
    (higham9_2_permutedLUBackwardError_to_LUBackwardError hLU)

/-- **Equation (9.2b)**, source column-permuted matrix `AQ` represented by the
permutation map `tau`. -/
def higham9_2_colPermutedMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) (tau : Fin n → Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j => A i (tau j)

/-- **Equation (9.2b)**, source row-and-column permuted matrix `PAQ`. -/
def higham9_2_rowColPermutedMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n) :
    Fin n → Fin n → ℝ :=
  higham9_2_rowPermutedMatrix (higham9_2_colPermutedMatrix A tau) sigma

/-- **Equation (9.2b)**, column permutations preserve Higham's max-entry norm. -/
theorem higham9_2_colPermutedMatrix_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) {tau : Fin n → Fin n}
    (htau : IsPermutation n tau) :
    maxEntryNorm hn (higham9_2_colPermutedMatrix A tau) = maxEntryNorm hn A := by
  classical
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau htau
  apply le_antisymm
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne
          (fun j => |higham9_2_colPermutedMatrix A tau i j|)) ≤
      maxEntryNorm hn A
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [higham9_2_colPermutedMatrix] using
      entry_le_maxEntryNorm hn A i (tau j)
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |A i j|)) ≤
      maxEntryNorm hn (higham9_2_colPermutedMatrix A tau)
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have htau_symm : tau (eTau.symm j) = j := by
      change eTau (eTau.symm j) = j
      exact Equiv.apply_symm_apply eTau j
    simpa [higham9_2_colPermutedMatrix, htau_symm] using
      entry_le_maxEntryNorm hn (higham9_2_colPermutedMatrix A tau)
        i (eTau.symm j)

/-- **Equation (9.2b)**, column permutations preserve the matrix infinity norm. -/
theorem higham9_2_colPermutedMatrix_infNorm {n : ℕ}
    (A : Fin n → Fin n → ℝ) {tau : Fin n → Fin n}
    (htau : IsPermutation n tau) :
    infNorm (higham9_2_colPermutedMatrix A tau) = infNorm A := by
  classical
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau htau
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      have hrow :
          (∑ j : Fin n, |higham9_2_colPermutedMatrix A tau i j|) =
            ∑ j : Fin n, |A i j| := by
        simpa [higham9_2_colPermutedMatrix, eTau] using
          (Equiv.sum_comp eTau (fun j : Fin n => |A i j|))
      rw [hrow]
      exact row_sum_le_infNorm A i
    · exact infNorm_nonneg A
  · apply infNorm_le_of_row_sum_le
    · intro i
      have hrow :
          (∑ j : Fin n, |higham9_2_colPermutedMatrix A tau i j|) =
            ∑ j : Fin n, |A i j| := by
        simpa [higham9_2_colPermutedMatrix, eTau] using
          (Equiv.sum_comp eTau (fun j : Fin n => |A i j|))
      rw [← hrow]
      exact row_sum_le_infNorm (higham9_2_colPermutedMatrix A tau) i
    · exact infNorm_nonneg (higham9_2_colPermutedMatrix A tau)

/-- **Equation (9.2b)**, row/column permutations preserve Higham's
max-entry norm. -/
theorem higham9_2_rowColPermutedMatrix_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) (htau : IsPermutation n tau) :
    maxEntryNorm hn (higham9_2_rowColPermutedMatrix A sigma tau) =
      maxEntryNorm hn A := by
  calc
    maxEntryNorm hn (higham9_2_rowColPermutedMatrix A sigma tau) =
        maxEntryNorm hn (higham9_2_colPermutedMatrix A tau) := by
          simpa [higham9_2_rowColPermutedMatrix] using
            higham9_2_rowPermutedMatrix_maxEntryNorm hn
              (higham9_2_colPermutedMatrix A tau) hsigma
    _ = maxEntryNorm hn A :=
        higham9_2_colPermutedMatrix_maxEntryNorm hn A htau

/-- **Equation (9.2b)**, row/column permutations preserve the matrix
infinity norm. -/
theorem higham9_2_rowColPermutedMatrix_infNorm {n : ℕ}
    (A : Fin n → Fin n → ℝ) {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) (htau : IsPermutation n tau) :
    infNorm (higham9_2_rowColPermutedMatrix A sigma tau) = infNorm A := by
  calc
    infNorm (higham9_2_rowColPermutedMatrix A sigma tau) =
        infNorm (higham9_2_colPermutedMatrix A tau) := by
          simpa [higham9_2_rowColPermutedMatrix] using
            higham9_2_rowPermutedMatrix_infNorm
              (higham9_2_colPermutedMatrix A tau) hsigma
    _ = infNorm A :=
        higham9_2_colPermutedMatrix_infNorm A htau

/-- **Equation (9.2b)**, the first-pivot row/column swaps preserve the
max-entry norm. -/
theorem higham9_2_rowColPermutedMatrix_firstPivotRowSwap_maxEntryNorm {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (r s : Fin (m + 1)) :
    maxEntryNorm (Nat.succ_pos m)
        (higham9_2_rowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s)) =
      maxEntryNorm (Nat.succ_pos m) A := by
  let hne : (Finset.univ : Finset (Fin (m + 1))).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.succ_pos m⟩⟩
  apply le_antisymm
  · change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne
          (fun j =>
            |higham9_2_rowColPermutedMatrix A
              (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s) i j|)) ≤
      maxEntryNorm (Nat.succ_pos m) A
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
      higham9_2_colPermutedMatrix] using
      entry_le_maxEntryNorm (Nat.succ_pos m) A
        (higham9_7_firstPivotRowSwap r i) (higham9_7_firstPivotRowSwap s j)
  · change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |A i j|)) ≤
      maxEntryNorm (Nat.succ_pos m)
        (higham9_2_rowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s))
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have hri :
        higham9_7_firstPivotRowSwap r (higham9_7_firstPivotRowSwap r i) = i :=
      higham9_7_firstPivotRowSwap_involutive r i
    have hsj :
        higham9_7_firstPivotRowSwap s (higham9_7_firstPivotRowSwap s j) = j :=
      higham9_7_firstPivotRowSwap_involutive s j
    simpa [higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
      higham9_2_colPermutedMatrix, hri, hsj] using
      entry_le_maxEntryNorm (Nat.succ_pos m)
        (higham9_2_rowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s))
        (higham9_7_firstPivotRowSwap r i) (higham9_7_firstPivotRowSwap s j)

/-- **Section 9.1 / complete-pivoting support**, after moving a first complete
pivot to `(0,0)`, row zero is a valid first-column partial pivot. -/
theorem higham9_1_completePivot_rowColPermuted_partialPivotChoice_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) {r s : Fin (m + 1)}
    (hchoice : higham9_1_completePivotChoice A 0 r s) :
    higham9_1_partialPivotChoice
      (higham9_2_rowColPermutedMatrix A
        (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s))
      0 0 := by
  refine ⟨le_rfl, ?_⟩
  intro i _hi
  simpa [higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
    higham9_2_colPermutedMatrix, higham9_7_firstPivotRowSwap] using
    hchoice.2.2 (higham9_7_firstPivotRowSwap r i) s
      (Nat.zero_le _) hchoice.2.1

/-- **Theorem 9.8 / complete-pivoting support**, the first complete-pivoting
Schur complement has max-entry norm at most twice the original max-entry norm. -/
theorem higham9_8_completePivot_firstSchurComplement_maxEntryNorm_le_two {m : ℕ}
    (hm : 0 < m) (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    {r s : Fin (m + 1)}
    (hchoice : higham9_1_completePivotChoice A 0 r s)
    (hpivot : A r s ≠ 0) :
    maxEntryNorm hm
        (luFirstSchurComplement
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s))) ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  let B : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_2_rowColPermutedMatrix A
      (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s)
  have hpartial :
      higham9_1_partialPivotChoice B 0 0 := by
    simpa [B] using
      higham9_1_completePivot_rowColPermuted_partialPivotChoice_zero A hchoice
  have hpivB : B 0 0 ≠ 0 := by
    simpa [B, higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
      higham9_2_colPermutedMatrix, higham9_7_firstPivotRowSwap] using hpivot
  have hpartial_bound :=
    higham9_7_partialPivot_firstSchurComplement_maxEntryNorm_le_two
      hm B (0 : Fin (m + 1)) hpartial hpivB
  have hBmax :
      maxEntryNorm (Nat.succ_pos m) B = maxEntryNorm (Nat.succ_pos m) A := by
    simpa [B] using
      higham9_2_rowColPermutedMatrix_firstPivotRowSwap_maxEntryNorm A r s
  calc
    maxEntryNorm hm (luFirstSchurComplement B)
        ≤ 2 * maxEntryNorm (Nat.succ_pos m) B := by
          simpa [B, higham9_7_firstPivotRowSwap, higham9_2_rowPermutedMatrix] using
            hpartial_bound
    _ = 2 * maxEntryNorm (Nat.succ_pos m) A := by rw [hBmax]

/-- **Equation (9.2b) / complete-pivoting first step**, row and column swaps
moving a chosen first complete pivot to `(0,0)` preserve nonsingularity. -/
theorem higham9_2_firstPivotRowColSwap_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (r s : Fin (m + 1))
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of
        (higham9_2_rowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r)
          (higham9_7_firstPivotRowSwap s)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
  classical
  let sigma := higham9_7_firstPivotRowSwap r
  let tau := higham9_7_firstPivotRowSwap s
  let B : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_2_rowPermutedMatrix A sigma
  have hB_det :
      Matrix.det (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
    simpa [B, sigma] using higham9_7_firstPivotRowSwap_det_ne_zero A r hdet
  let eTau : Equiv.Perm (Fin (m + 1)) :=
    Equiv.ofBijective tau (higham9_7_firstPivotRowSwap_isPermutation s)
  have hdet_eq :
      Matrix.det
        (Matrix.of
          (higham9_2_rowColPermutedMatrix A sigma tau) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
        ((Equiv.Perm.sign eTau : ℤ) : ℝ) *
          Matrix.det (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) := by
    have hperm :=
      Matrix.det_permute' eTau
        (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    simpa [B, sigma, tau, eTau, higham9_2_rowColPermutedMatrix,
      higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix, Matrix.of_apply]
      using hperm
  rw [hdet_eq]
  exact mul_ne_zero (by simp) hB_det

/-- **Equation (9.2b)**, source-facing exact complete-pivoting certificate
`PAQ = LU`, represented as a row-permuted LU certificate for `AQ` together
with an explicit column permutation condition. -/
abbrev higham9_2_CompletePermutedLUFactSpec (n : ℕ)
    (A L U : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n) : Prop :=
  IsPermutation n tau ∧
    PermutedLUFactSpec n (higham9_2_colPermutedMatrix A tau) L U sigma

/-- **Equation (9.2b)**, a source `PAQ = LU` certificate is an ordinary exact
LU certificate for the row-and-column permuted matrix. -/
theorem higham9_2_completePermutedLUFactSpec_to_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hLU : higham9_2_CompletePermutedLUFactSpec n A L U sigma tau) :
    LUFactSpec n (higham9_2_rowColPermutedMatrix A sigma tau) L U := by
  simpa [higham9_2_rowColPermutedMatrix] using
    (higham9_2_permutedLUFactSpec_to_LUFactSpec hLU.2)

/-- **Equation (9.2b)**, determinant-pivot product for an explicit
complete-pivoting certificate `PAQ = LU`. -/
theorem higham9_2_completePermutedLUFactSpec_det_eq_pivot_product {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hLU : higham9_2_CompletePermutedLUFactSpec n A L U sigma tau) :
    Matrix.det
        (Matrix.of (higham9_2_rowColPermutedMatrix A sigma tau) :
          Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i :=
  (higham9_2_completePermutedLUFactSpec_to_LUFactSpec hLU).det_eq_prod_U_diag

/-- **Equation (9.2b)**, nonsingularity consequence for an explicit
complete-pivoting certificate `PAQ = LU`. -/
theorem higham9_2_completePermutedLUFactSpec_det_ne_zero_iff_pivots_ne_zero {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hLU : higham9_2_CompletePermutedLUFactSpec n A L U sigma tau) :
    Matrix.det
        (Matrix.of (higham9_2_rowColPermutedMatrix A sigma tau) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0 ↔
      ∀ i : Fin n, U i i ≠ 0 :=
  (higham9_2_completePermutedLUFactSpec_to_LUFactSpec hLU).det_ne_zero_iff_U_diag_ne_zero

/-- **Theorem 9.3 / equation (9.2b)**, source-facing complete-pivoting
backward-error certificate. -/
abbrev higham9_2_CompletePermutedLUBackwardError (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n)
    (ε : ℝ) : Prop :=
  IsPermutation n tau ∧
    PermutedLUBackwardError n (higham9_2_colPermutedMatrix A tau)
      L_hat U_hat sigma ε

/-- **Theorem 9.3 / equation (9.2b)**, a complete-pivoting backward-error
certificate is an ordinary LU backward-error certificate for `PAQ`. -/
theorem higham9_2_completePermutedLUBackwardError_to_LUBackwardError {n : ℕ}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    {ε : ℝ}
    (hLU :
      higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau ε) :
    LUBackwardError n (higham9_2_rowColPermutedMatrix A sigma tau)
      L_hat U_hat ε := by
  simpa [higham9_2_rowColPermutedMatrix] using
    (higham9_2_permutedLUBackwardError_to_LUBackwardError hLU.2)

/-- **Theorem 9.3**, complete-pivoting certificate form: if a backward-error
certificate is supplied for `PAQ`, then the standard `gamma_n` perturbation
theorem applies to the row-and-column permuted source matrix.  This is a
certificate adapter only; it does not construct the complete-pivoting trace. -/
theorem higham9_3_complete_permuted_lu_backward_error_gamma {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hn : gammaValid fp n)
    (hLU :
      higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau (gamma fp n)) :
    ∃ ΔPAQ : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPAQ i j| ≤
          gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L_hat i k * U_hat k j =
          higham9_2_rowColPermutedMatrix A sigma tau i j + ΔPAQ i j) :=
  lu_backward_error_gamma fp n (higham9_2_rowColPermutedMatrix A sigma tau)
    L_hat U_hat hn
    (higham9_2_completePermutedLUBackwardError_to_LUBackwardError hLU)

/-- **Equation (9.2b)**, right-inverse transport through row and column
permutations.

If `A_inv` is a visible right inverse of `A`, then the source `PAQ` matrix
`A(sigma i, tau j)` has right inverse `(i,j) ↦ A_inv(tau i, sigma j)`. -/
theorem higham9_2_rowColPermutedMatrix_right_inverse {n : ℕ}
    {A A_inv : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) (htau : IsPermutation n tau)
    (hRight : IsRightInverse n A A_inv) :
    IsRightInverse n (higham9_2_rowColPermutedMatrix A sigma tau)
      (fun i j => A_inv (tau i) (sigma j)) := by
  classical
  intro i j
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau htau
  have hsum :
      (∑ k : Fin n, A (sigma i) (tau k) * A_inv (tau k) (sigma j)) =
        ∑ k : Fin n, A (sigma i) k * A_inv k (sigma j) := by
    simpa [eTau] using
      (Equiv.sum_comp eTau
        (fun k : Fin n => A (sigma i) k * A_inv k (sigma j)))
  calc
    ∑ k : Fin n,
        higham9_2_rowColPermutedMatrix A sigma tau i k *
          (fun i j => A_inv (tau i) (sigma j)) k j
        = ∑ k : Fin n, A (sigma i) (tau k) * A_inv (tau k) (sigma j) := by
            simp [higham9_2_rowColPermutedMatrix,
              higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix]
    _ = ∑ k : Fin n, A (sigma i) k * A_inv k (sigma j) := hsum
    _ = (if sigma i = sigma j then 1 else 0) := hRight (sigma i) (sigma j)
    _ = (if i = j then 1 else 0) := by
        by_cases hij : i = j
        · simp [hij]
        · have hsig_ne : sigma i ≠ sigma j := by
            intro hsig
            exact hij (hsigma.1 hsig)
          simp [hij, hsig_ne]

/-- **Algorithm 9.2**, literal floating-point upper-entry update. -/
noncomputable def higham9_2_flDoolittleUEntry (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (k j : Fin n) : ℝ :=
  flDoolittleUEntry fp n A L_hat U_hat k j

/-- **Algorithm 9.2**, literal floating-point lower-entry numerator update. -/
noncomputable def higham9_2_flDoolittleLNumerator (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  flDoolittleLNumerator fp n A L_hat U_hat i k

/-- **Algorithm 9.2**, literal floating-point lower-entry update. -/
noncomputable def higham9_2_flDoolittleLEntry (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  flDoolittleLEntry fp n A L_hat U_hat i k

/-- **Algorithm 9.2**, exact-target gap handoff: source-visible gaps for the
literal rounded Doolittle upper and lower targets produce the dense square
absolute-budget certificate used by the Chapter 9 Doolittle backward-error
surface.  The gap hypotheses remain explicit; this theorem does not construct
the full rectangular executable trace. -/
theorem higham9_2_absBudgetCertificate_of_literal_doolittle_exact_target_gaps
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j +
        doolittleUExactTargetResidualBudget fp n A L_hat U_hat k j ≤
        |doolittleUExactTarget n A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k +
        doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
        doolittleLExactTargetNumeratorResidualBudget
          fp n A L_hat U_hat i k) +
        doolittleLExactTargetEntryResidualBudget
          fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|) :
    higham9_2_DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp
      (doolittleUAbsBudget fp n A L_hat U_hat)
      (doolittleLAbsBudget fp n A L_hat U_hat) := by
  exact
    DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_exact_target_gaps
      hL_diag hL_upper_zero hU_lower_zero
      (by
        intro k j hkj
        simpa [higham9_2_flDoolittleUEntry] using hU_entry_eq k j hkj)
      (by
        intro i k hki
        simpa [higham9_2_flDoolittleLEntry] using hL_entry_eq i k hki)
      hU_diag hn hU_gap hL_gap hL_num_gap

/-- **Algorithm 9.2**, rectangular row embedding.  Under the source hypothesis
`m >= n`, the pivot row index `k : Fin n` is also a valid row index of the
rectangular `m x n` input. -/
def higham9_2_rectRow {m n : ℕ} (hmn : n ≤ m) (k : Fin n) : Fin m :=
  ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩

/-- **Algorithm 9.2**, rectangular exact prefix dot product appearing in
equations (9.3) and (9.4). -/
noncomputable def higham9_2_rectPrefixDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) : ℝ :=
  ∑ s : Fin n, (if s.val < k.val then L i s * U s j else 0)

/-- **Algorithm 9.2**, exact rectangular upper-entry update for equation
(9.3). -/
noncomputable def higham9_2_rectDoolittleUUpdate {m n : ℕ} (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) : ℝ :=
  A (higham9_2_rectRow hmn k) j -
    higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k

/-- **Algorithm 9.2**, exact rectangular lower-entry update for equation
(9.4). -/
noncomputable def higham9_2_rectDoolittleLUpdate {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  (A i k - higham9_2_rectPrefixDot L U i k k) / U k k

/-- **Equation (9.3)** source identity for the rectangular Doolittle upper
update: the exact assignment restores the displayed prefix-sum equation. -/
theorem higham9_2_rectDoolittleUUpdate_source_identity {m n : ℕ}
    (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) :
    higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k +
      higham9_2_rectDoolittleUUpdate hmn A L U k j =
        A (higham9_2_rectRow hmn k) j := by
  unfold higham9_2_rectDoolittleUUpdate
  ring

/-- **Equation (9.3)** in source orientation: if the stored upper entry is the
rectangular Doolittle update, then `a_kj` is the prefix dot product plus
`u_kj`. -/
theorem higham9_2_rectDoolittleU_source_identity {m n : ℕ}
    (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n)
    (hU :
      U k j = higham9_2_rectDoolittleUUpdate hmn A L U k j) :
    A (higham9_2_rectRow hmn k) j =
      higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k +
        U k j := by
  rw [hU]
  symm
  exact higham9_2_rectDoolittleUUpdate_source_identity hmn A L U k j

/-- **Equation (9.4)** source identity for the rectangular Doolittle lower
update: after division by a nonzero pivot and multiplication back by the same
pivot, the exact assignment restores the displayed prefix-sum equation. -/
theorem higham9_2_rectDoolittleLUpdate_source_identity {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n)
    (hUkk : U k k ≠ 0) :
    higham9_2_rectPrefixDot L U i k k +
      higham9_2_rectDoolittleLUpdate A L U i k * U k k =
        A i k := by
  unfold higham9_2_rectDoolittleLUpdate
  rw [div_mul_cancel₀ _ hUkk]
  ring

/-- **Equation (9.4)** in source orientation: if the stored lower entry is the
rectangular Doolittle update and the pivot is nonzero, then `a_ik` is the prefix
dot product plus `l_ik u_kk`. -/
theorem higham9_2_rectDoolittleL_source_identity {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n)
    (hUkk : U k k ≠ 0)
    (hL : L i k = higham9_2_rectDoolittleLUpdate A L U i k) :
    A i k =
      higham9_2_rectPrefixDot L U i k k + L i k * U k k := by
  rw [hL]
  symm
  exact higham9_2_rectDoolittleLUpdate_source_identity A L U i k hUkk

/-- **Algorithm 9.2 / Theorem 9.1 support**, exact-LU upper recurrence.
Every exact unit-lower/upper `LUFactSpec` satisfies the Doolittle upper-entry
formula used in equation (9.3).  This is the converse direction of the source
identity above, restricted to the square exact-LU certificate surface. -/
theorem higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) (k j : Fin n) :
    U k j = higham9_2_rectDoolittleUUpdate (Nat.le_refl n) A L U k j := by
  classical
  have hprod := hLU.product_eq k j
  have hsum :
      (∑ s : Fin n, L k s * U s j) =
        higham9_2_rectPrefixDot L U k j k + U k j := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun s : Fin n => s.val < k.val)
      (fun s : Fin n => L k s * U s j)]
    congr 1
    · simp [higham9_2_rectPrefixDot, Finset.sum_filter]
    · rw [Finset.sum_eq_single k]
      · simp [hLU.L_diag k]
      · intro s hs hsk
        have hnotlt : ¬ s.val < k.val := by
          exact (Finset.mem_filter.mp hs).2
        have hle : k.val ≤ s.val := Nat.le_of_not_gt hnotlt
        have hne_val : k.val ≠ s.val := by
          intro hval
          exact hsk (Fin.ext hval.symm)
        have hk_lt_s : k.val < s.val := lt_of_le_of_ne hle hne_val
        rw [hLU.L_upper_zero k s hk_lt_s, zero_mul]
      · intro hk_not_mem
        exact (hk_not_mem (by simp)).elim
  have hA :
      A k j = higham9_2_rectPrefixDot L U k j k + U k j := by
    rw [← hprod, hsum]
  unfold higham9_2_rectDoolittleUUpdate
  simp [higham9_2_rectRow, hA]

/-- **Algorithm 9.2 / Theorem 9.1 support**, exact-LU lower recurrence.
Every exact unit-lower/upper `LUFactSpec` with a nonzero pivot satisfies the
Doolittle lower-entry formula used in equation (9.4).  This is a local
dependency for uniqueness/existence work; it does not construct the factorization. -/
theorem higham9_2_rectDoolittleLUpdate_eq_of_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) (i k : Fin n)
    (hUkk : U k k ≠ 0) :
    L i k = higham9_2_rectDoolittleLUpdate A L U i k := by
  classical
  have hprod := hLU.product_eq i k
  have hsum :
      (∑ s : Fin n, L i s * U s k) =
        higham9_2_rectPrefixDot L U i k k + L i k * U k k := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun s : Fin n => s.val < k.val)
      (fun s : Fin n => L i s * U s k)]
    congr 1
    · simp [higham9_2_rectPrefixDot, Finset.sum_filter]
    · rw [Finset.sum_eq_single k]
      · intro s hs hsk
        have hnotlt : ¬ s.val < k.val := by
          exact (Finset.mem_filter.mp hs).2
        have hle : k.val ≤ s.val := Nat.le_of_not_gt hnotlt
        have hne_val : k.val ≠ s.val := by
          intro hval
          exact hsk (Fin.ext hval.symm)
        have hk_lt_s : k.val < s.val := lt_of_le_of_ne hle hne_val
        rw [hLU.U_lower_zero s k hk_lt_s, mul_zero]
      · intro hk_not_mem
        exact (hk_not_mem (by simp)).elim
  have hA :
      A i k = higham9_2_rectPrefixDot L U i k k + L i k * U k k := by
    rw [← hprod, hsum]
  unfold higham9_2_rectDoolittleLUpdate
  rw [hA]
  field_simp [hUkk]
  ring

/-- **Theorem 9.1 support**, uniqueness of an exact LU certificate once the
pivots are nonzero.  The proof follows the Doolittle recurrences column by
column: previous columns of `L` and rows of `U` determine the next row of `U`,
then the nonzero pivot determines the next column of `L`.  This is still only
the uniqueness half of Theorem 9.1; it does not construct factors from leading
principal minors. -/
theorem higham9_1_lu_unique_of_pivots_ne_zero {n : ℕ}
    {A L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ}
    (hLU₁ : LUFactSpec n A L₁ U₁)
    (hLU₂ : LUFactSpec n A L₂ U₂)
    (hU₁diag : ∀ k : Fin n, U₁ k k ≠ 0) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  classical
  have hstage :
      ∀ t : ℕ, t ≤ n →
        ∀ k : Fin n, k.val < t →
          (∀ j : Fin n, U₁ k j = U₂ k j) ∧
            (∀ i : Fin n, L₁ i k = L₂ i k) := by
    intro t
    induction t with
    | zero =>
        intro _ k hk
        exact (Nat.not_lt_zero _ hk).elim
    | succ t ih =>
        intro ht k hk
        have ht_le : t ≤ n := Nat.le_trans (Nat.le_succ t) ht
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | hk_eq
        · exact ih ht_le k hk_lt
        · have ht_lt_n : t < n := Nat.lt_of_succ_le ht
          let kk : Fin n := ⟨t, ht_lt_n⟩
          have hk_eq_fin : k = kk := Fin.ext hk_eq
          subst k
          have hprev :
              ∀ s : Fin n, s.val < kk.val →
                (∀ j : Fin n, U₁ s j = U₂ s j) ∧
                  (∀ i : Fin n, L₁ i s = L₂ i s) := by
            intro s hs
            exact ih ht_le s hs
          have hUeq : ∀ j : Fin n, U₁ kk j = U₂ kk j := by
            intro j
            have hrec₁ :=
              higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec hLU₁ kk j
            have hrec₂ :=
              higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec hLU₂ kk j
            have hprefix :
                higham9_2_rectPrefixDot L₁ U₁ kk j kk =
                  higham9_2_rectPrefixDot L₂ U₂ kk j kk := by
              unfold higham9_2_rectPrefixDot
              apply Finset.sum_congr rfl
              intro s _
              by_cases hs : s.val < kk.val
              · have hp := hprev s hs
                simp [hs, hp.2 kk, hp.1 j]
              · simp [hs]
            rw [hrec₁, hrec₂]
            unfold higham9_2_rectDoolittleUUpdate
            simp [higham9_2_rectRow, hprefix]
          have hU₂diag : U₂ kk kk ≠ 0 := by
            rw [← hUeq kk]
            exact hU₁diag kk
          have hLeq : ∀ i : Fin n, L₁ i kk = L₂ i kk := by
            intro i
            have hrec₁ :=
              higham9_2_rectDoolittleLUpdate_eq_of_LUFactSpec hLU₁ i kk
                (hU₁diag kk)
            have hrec₂ :=
              higham9_2_rectDoolittleLUpdate_eq_of_LUFactSpec hLU₂ i kk
                hU₂diag
            have hprefix :
                higham9_2_rectPrefixDot L₁ U₁ i kk kk =
                  higham9_2_rectPrefixDot L₂ U₂ i kk kk := by
              unfold higham9_2_rectPrefixDot
              apply Finset.sum_congr rfl
              intro s _
              by_cases hs : s.val < kk.val
              · have hp := hprev s hs
                simp [hs, hp.2 i, hp.1 kk]
              · simp [hs]
            rw [hrec₁, hrec₂]
            unfold higham9_2_rectDoolittleLUpdate
            simp [hprefix, hUeq kk]
          exact ⟨hUeq, hLeq⟩
  constructor
  · funext i j
    exact (hstage n (Nat.le_refl n) j j.isLt).2 i
  · funext i j
    exact (hstage n (Nat.le_refl n) i i.isLt).1 j

/-- **Algorithm 9.2**, printed leading flop-count polynomial
`n^2 (m - n/3)`, represented over `ℚ`.  The rational codomain records the
source expression itself; this declaration is not an exact integer operation
count for a fully specified executable loop. -/
def higham9_2_doolittleSourceFlopPolynomial (m n : ℕ) : ℚ :=
  (n : ℚ) ^ 2 * ((m : ℚ) - (n : ℚ) / 3)

/-- **Algorithm 9.2**, algebraic expansion of the printed leading flop-count
polynomial. -/
theorem higham9_2_doolittleSourceFlopPolynomial_eq (m n : ℕ) :
    higham9_2_doolittleSourceFlopPolynomial m n =
      (m : ℚ) * (n : ℚ) ^ 2 - (n : ℚ) ^ 3 / 3 := by
  unfold higham9_2_doolittleSourceFlopPolynomial
  ring

/-- **Algorithm 9.2**, the one-column specialization of the printed cost
expression is rational.  This documents why the source expression is treated as
a leading polynomial rather than as a literal natural-number loop count. -/
theorem higham9_2_doolittleSourceFlopPolynomial_one (m : ℕ) :
    higham9_2_doolittleSourceFlopPolynomial m 1 = (m : ℚ) - 1 / 3 := by
  simp [higham9_2_doolittleSourceFlopPolynomial]

/-- **Equation (9.5)**: finite prefix of the rank-one GE updates, written with
an explicit natural-number step count.  Terms beyond the rectangular column
range contribute zero, so this definition is total in `steps`. -/
noncomputable def higham9_5_rectPrefixRange {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (steps : ℕ) : ℝ :=
  ∑ r ∈ Finset.range steps,
    if h : r < n then L i ⟨r, h⟩ * U ⟨r, h⟩ j else 0

/-- **Equation (9.5)**: the reduced matrix entry obtained from the original
entry after `steps` exact no-pivot GE rank-one updates. -/
noncomputable def higham9_5_rectGEReducedEntry {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (steps : ℕ) (i : Fin m) (j : Fin n) : ℝ :=
  A i j - higham9_5_rectPrefixRange L U i j steps

/-- **Equation (9.5)** starts from the original matrix before any rank-one
updates. -/
theorem higham9_5_rectGEReducedEntry_zero {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    higham9_5_rectGEReducedEntry A L U 0 i j = A i j := by
  simp [higham9_5_rectGEReducedEntry, higham9_5_rectPrefixRange]

/-- **Equation (9.5)** as a one-step exact GE recurrence: moving from `s`
completed updates to `s+1` subtracts the displayed `l_is u_sj` term. -/
theorem higham9_5_rectGEReducedEntry_succ_of_lt {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (steps : ℕ) (hsteps : steps < n) (i : Fin m) (j : Fin n) :
    higham9_5_rectGEReducedEntry A L U (steps + 1) i j =
      higham9_5_rectGEReducedEntry A L U steps i j -
        L i ⟨steps, hsteps⟩ * U ⟨steps, hsteps⟩ j := by
  unfold higham9_5_rectGEReducedEntry higham9_5_rectPrefixRange
  rw [Finset.sum_range_succ]
  simp [hsteps]
  ring

/-- The natural-number prefix used in equation (9.5) agrees with the masked
`Fin n` prefix used in the source-facing Doolittle recurrences. -/
theorem higham9_5_rectPrefixRange_eq_rectPrefixDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) :
    higham9_5_rectPrefixRange L U i j k.val =
      higham9_2_rectPrefixDot L U i j k := by
  unfold higham9_5_rectPrefixRange higham9_2_rectPrefixDot
  rw [finMaskedPrefixSum_eq_finSum k (fun s : Fin n => L i s * U s j)]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro s _
  have hsn : s.val < n := Nat.lt_trans s.isLt k.isLt
  simp [hsn]

/-- **Equation (9.5)** in closed form: after `k.val` exact GE rank-one updates,
the reduced entry is the original entry minus the Doolittle prefix dot product
through columns/rows preceding `k`. -/
theorem higham9_5_rectGEReducedEntry_eq_rectPrefixDot {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) :
    higham9_5_rectGEReducedEntry A L U k.val i j =
      A i j - higham9_2_rectPrefixDot L U i j k := by
  simp [higham9_5_rectGEReducedEntry,
    higham9_5_rectPrefixRange_eq_rectPrefixDot L U i j k]

/-- **Equation (9.5)** specialized to the upper-row Doolittle assignment: the
exact Doolittle upper update is precisely the corresponding no-pivot GE reduced
matrix entry. -/
theorem higham9_5_rectGEReducedEntry_eq_DoolittleUUpdate {m n : ℕ}
    (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) :
    higham9_5_rectGEReducedEntry A L U k.val
        (higham9_2_rectRow hmn k) j =
      higham9_2_rectDoolittleUUpdate hmn A L U k j := by
  simp [higham9_5_rectGEReducedEntry_eq_rectPrefixDot,
    higham9_2_rectDoolittleUUpdate]

/-- **Equation (9.5)** specialized to the lower-column Doolittle assignment:
the reduced entry is the lower numerator before division by the pivot. -/
theorem higham9_5_rectGEReducedEntry_eq_DoolittleLNumerator {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) :
    higham9_5_rectGEReducedEntry A L U k.val i k =
      A i k - higham9_2_rectPrefixDot L U i k k := by
  simp [higham9_5_rectGEReducedEntry_eq_rectPrefixDot]

/-- **Equation (9.5)** in the lower-column source orientation: with a nonzero
pivot, the exact GE reduced entry equals `l_ik u_kk` for the Doolittle lower
update. -/
theorem higham9_5_rectGEReducedEntry_eq_DoolittleLUpdate_mul_pivot {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n)
    (hUkk : U k k ≠ 0) :
    higham9_5_rectGEReducedEntry A L U k.val i k =
      higham9_2_rectDoolittleLUpdate A L U i k * U k k := by
  rw [higham9_5_rectGEReducedEntry_eq_DoolittleLNumerator]
  unfold higham9_2_rectDoolittleLUpdate
  rw [div_mul_cancel₀ _ hUkk]

/-! ## §9.3 Error Analysis -/

/-- **Theorem 9.3**, Doolittle-certified form:
`L_hat U_hat = A + ΔA`, with `|ΔA| ≤ γ_n |L_hat||U_hat|`. -/
theorem higham9_3_doolittle_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hD : higham9_2_DoolittleLU n A L_hat U_hat fp) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  doolittle_backward_error n fp A L_hat U_hat hn hD

/-- **Theorem 9.3**, dense executable-loop certificate form: the literal dense
Doolittle loop certificate feeds the standard componentwise backward-error
theorem.  The remaining compression hypotheses are exactly the visible fields
of `higham9_2_DoolittleDenseLoopCertificate`; they are not hidden inside this
wrapper. -/
theorem higham9_3_denseLoopCertificate_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_3_doolittle_backward_error n fp A L_hat U_hat hn
    (higham9_2_denseLoopCertificate_to_DoolittleLU hC hn)

/-- **Theorem 9.3**, absolute-budget executable-loop form: absolute residual
budgets for the literal Doolittle folds, once dominated by the source relative
budgets, feed the standard componentwise backward-error theorem. -/
theorem higham9_3_absBudgetCertificate_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp BU BL) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_3_doolittle_backward_error n fp A L_hat U_hat hn
    (higham9_2_absBudgetCertificate_to_DoolittleLU hC hn)

/-- **Theorem 9.3**, generic LU backward-error-certificate form. -/
theorem higham9_3_lu_backward_error_gamma (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n)) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  lu_backward_error_gamma fp n A L_hat U_hat hn hLU

/-- **Theorem 9.4**: LU factorization plus two triangular solves, with
Higham's absorbed `γ_{3n}` componentwise bound. -/
theorem higham9_4_lu_solve_backward_error (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * n) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  lu_solve_backward_error_tight fp n A L_hat U_hat b hL_diag hU_diag hLU hn hn3

/-- **Problem 9.4**, row-pivoted analogue of Theorem 9.4.

If the LU backward-error certificate is for `P A`, the triangular solves use
the permuted right-hand side `P b`.  Unpermuting the perturbation rows gives a
backward error for the original system `A x = b`, with the componentwise bound
recorded in source pivoted-row coordinates. -/
theorem higham_problem9_4_permuted_lu_solve_backward_error
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA (sigma i) j| ≤ gamma fp (3 * n) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  classical
  let bP : Fin n → ℝ := fun i => b (sigma i)
  let Aperm : Fin n → Fin n → ℝ := higham9_2_rowPermutedMatrix A sigma
  obtain ⟨ΔPA, hΔPA_bound, hΔPA_eq⟩ :=
    lu_solve_backward_error_tight fp n Aperm L_hat U_hat bP
      hL_diag hU_diag
      (higham9_2_permutedLUBackwardError_to_LUBackwardError hLU) hn hn3
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hLU.perm
  let ΔA : Fin n → Fin n → ℝ := fun i j => ΔPA (eSigma.symm i) j
  refine ⟨ΔA, ?_, ?_⟩
  · intro i j
    simpa [ΔA, eSigma] using hΔPA_bound i j
  · intro i
    have hrow := hΔPA_eq (eSigma.symm i)
    have hsigma_symm : sigma (eSigma.symm i) = i := by
      change eSigma (eSigma.symm i) = i
      exact Equiv.apply_symm_apply eSigma i
    calc
      ∑ j : Fin n, (A i j + ΔA i j) *
          (fl_backSub fp n U_hat (fl_forwardSub fp n L_hat bP)) j
          = ∑ j : Fin n, (Aperm (eSigma.symm i) j + ΔPA (eSigma.symm i) j) *
              (fl_backSub fp n U_hat (fl_forwardSub fp n L_hat bP)) j := by
            apply Finset.sum_congr rfl
            intro j _
            simp [Aperm, higham9_2_rowPermutedMatrix, ΔA, hsigma_symm]
      _ = bP (eSigma.symm i) := hrow
      _ = b i := by simp [bP, hsigma_symm]

/-- **Problem 9.4**, complete-pivoted analogue of Theorem 9.4.

For a complete-pivoting certificate `P A Q`, the triangular solves compute the
permuted unknown `z`; the returned original-order vector is
`x_j = z_(Q^{-1} j)`.  The perturbation is unpermuted in both rows and columns,
while the componentwise bound is recorded in the source `P A Q` coordinates. -/
theorem higham_problem9_4_complete_permuted_lu_solve_backward_error
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma tau : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau
      (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let z_hat := fl_backSub fp n U_hat y_hat
    let x_hat : Fin n → ℝ :=
      fun j => z_hat ((Equiv.ofBijective tau hLU.1).symm j)
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA (sigma i) (tau j)| ≤ gamma fp (3 * n) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  classical
  let bP : Fin n → ℝ := fun i => b (sigma i)
  let B : Fin n → Fin n → ℝ := higham9_2_rowColPermutedMatrix A sigma tau
  obtain ⟨ΔB, hΔB_bound, hΔB_eq⟩ :=
    lu_solve_backward_error_tight fp n B L_hat U_hat bP
      hL_diag hU_diag
      (higham9_2_completePermutedLUBackwardError_to_LUBackwardError hLU) hn hn3
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hLU.2.perm
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau hLU.1
  let z_hat := fl_backSub fp n U_hat (fl_forwardSub fp n L_hat bP)
  let x_hat : Fin n → ℝ := fun j => z_hat (eTau.symm j)
  let ΔA : Fin n → Fin n → ℝ := fun i j => ΔB (eSigma.symm i) (eTau.symm j)
  refine ⟨ΔA, ?_, ?_⟩
  · intro i j
    simpa [ΔA, eSigma, eTau] using hΔB_bound i j
  · intro i
    have hrow := hΔB_eq (eSigma.symm i)
    have hsigma_symm : sigma (eSigma.symm i) = i := by
      change eSigma (eSigma.symm i) = i
      exact Equiv.apply_symm_apply eSigma i
    let f : Fin n → ℝ := fun j => (A i j + ΔA i j) * x_hat j
    calc
      ∑ j : Fin n, (A i j + ΔA i j) * x_hat j
          = ∑ j : Fin n, f (eTau j) := by
              simpa [f] using (Equiv.sum_comp eTau f).symm
      _ = ∑ j : Fin n, (B (eSigma.symm i) j + ΔB (eSigma.symm i) j) *
            z_hat j := by
          apply Finset.sum_congr rfl
          intro j _
          simp [f, B, higham9_2_rowColPermutedMatrix,
            higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix,
            ΔA, x_hat, z_hat, eTau, hsigma_symm]
      _ = bP (eSigma.symm i) := hrow
      _ = b i := by simp [bP, hsigma_symm]

/-- **Equation (9.8)**: nonnegative computed factors give
`|L_hat||U_hat| ≤ |A|/(1-ε)`. -/
theorem higham9_8_nonneg_factor_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε_lt : ε < 1) (hε_nn : 0 ≤ ε)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j| / (1 - ε) :=
  nonneg_factor_bound n A L_hat U_hat ε hε_lt hε_nn hLU hL_nn hU_nn

/-- **Equation (9.9)**: LU solve bound specialized by the nonnegative-factor
correction from (9.8), giving `γ_{3n}/(1-γ_n)` times `|A|`. -/
theorem higham9_9_nonneg_lu_solve_backward_error (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hγ_lt : gamma fp n < 1)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        (gamma fp (3 * n) / (1 - gamma fp n)) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_tight fp n A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hW :=
    nonneg_factor_bound n A L_hat U_hat (gamma fp n) hγ_lt
      (gamma_nonneg fp hn) hLU hL_nn hU_nn i j
  have hγ3 : 0 ≤ gamma fp (3 * n) := gamma_nonneg fp hn3
  calc
    |ΔA i j| ≤ gamma fp (3 * n) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * n) * (|A i j| / (1 - gamma fp n)) :=
        mul_le_mul_of_nonneg_left hW hγ3
    _ = (gamma fp (3 * n) / (1 - gamma fp n)) * |A i j| := by
        ring

/-! ## §9.4 Growth Factor -/

/-- **Theorem 9.5**, repository `∞`-norm Wilkinson form:
`‖ΔA‖∞ ≤ γ_{3n} n ‖U_hat‖∞`. -/
theorem higham9_5_wilkinson_normwise_infNorm_tight (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤ gamma fp (3 * n) * ↑n * infNorm U_hat) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  wilkinson_normwise_infNorm_tight fp n hn_pos A L_hat U_hat b
    hL_diag hU_diag hLU hn hn3 hL_bound

/-- **Theorem 9.5**, source-shaped bound after supplying the bridge from
Higham's growth factor to the repository `∞`-norm of `U_hat`. -/
theorem higham9_5_wilkinson_source_bound_of_growth_bridge (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (ρ : ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1)
    (hU_growth : infNorm U_hat ≤ ↑n * ρ * infNorm A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤ (↑n) ^ 2 * gamma fp (3 * n) * ρ * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    wilkinson_normwise_infNorm_tight fp n hn_pos A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3 hL_bound
  refine ⟨ΔA, ?_, hΔA_eq⟩
  have hγn : 0 ≤ gamma fp (3 * n) * (n : ℝ) :=
    mul_nonneg (gamma_nonneg fp hn3) (Nat.cast_nonneg' n)
  calc
    infNorm ΔA ≤ gamma fp (3 * n) * ↑n * infNorm U_hat := hΔA_bound
    _ ≤ gamma fp (3 * n) * ↑n * (↑n * ρ * infNorm A) :=
        mul_le_mul_of_nonneg_left hU_growth hγn
    _ = (↑n) ^ 2 * gamma fp (3 * n) * ρ * infNorm A := by
        ring

/-- **Theorem 9.5**, source-shaped max-entry growth-factor form.

This removes the free norm-growth bridge hypothesis from
`higham9_5_wilkinson_source_bound_of_growth_bridge`: a bound on Higham's
max-entry growth factor for the final `U_hat` implies the required
`∞`-norm bridge by elementary row-sum/max-entry inequalities. -/
theorem higham9_5_wilkinson_source_bound_of_entry_growth (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (ρ : ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (hρ : 0 ≤ ρ)
    (hρU : growthFactorEntry hn_pos A U_hat hAmax ≤ ρ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤ (↑n) ^ 2 * gamma fp (3 * n) * ρ * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_growth_bridge fp n hn_pos A L_hat U_hat b ρ
    hL_diag hU_diag hLU hn hn3 hL_bound
    (infNorm_le_card_mul_growthFactorEntry_bound hn_pos A U_hat ρ hAmax hρ hρU)

/-- **Theorem 9.5 / equation (9.10)**, source-shaped GEPP normwise
backward-error bound for an explicit partial-pivoting `U` trace.  This
instantiates the max-entry growth hypothesis in
`higham9_5_wilkinson_source_bound_of_entry_growth` from the local exact
Theorem 9.7 trace bound `rho_n^p <= 2^(n-1)`. -/
theorem higham9_5_wilkinson_source_bound_of_PartialPivotGEPPUTrace
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_entry_growth fp n hn_pos A L_hat U_hat b
    ((2 : ℝ) ^ (n - 1)) hAmax
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n - 1))
    (higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two
      hn_pos A U_hat hAmax htrace)
    hL_diag hU_diag hLU hn hn3 hL_bound

/-- **Theorem 9.5 / equation (9.10)**, row-pivoted GEPP certificate form.

If a supplied row-pivoted backward-error certificate computes the same `U_hat`
as an explicit recursive partial-pivoting trace, then Wilkinson's normwise
source bound applies to the original system after permuting the right-hand side.
The theorem deliberately keeps the GEPP trace, pivoted certificate, nonzero
pivots, and multiplier bound as visible hypotheses; it does not construct them
from a concrete floating-point implementation. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  classical
  let bP : Fin n → ℝ := fun i => b (sigma i)
  let Aperm : Fin n → Fin n → ℝ := higham9_2_rowPermutedMatrix A sigma
  have hApermmax : 0 < maxEntryNorm hn_pos Aperm := by
    simpa [Aperm, higham9_2_rowPermutedMatrix_maxEntryNorm hn_pos A hLU.perm]
      using hAmax
  have hgrowth :
      growthFactorEntry hn_pos Aperm U_hat hApermmax ≤
        (2 : ℝ) ^ (n - 1) := by
    have htrace_growth :
        growthFactorEntry hn_pos A U_hat hAmax ≤ (2 : ℝ) ^ (n - 1) :=
      higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two
        hn_pos A U_hat hAmax htrace
    unfold growthFactorEntry at htrace_growth ⊢
    simpa [Aperm, higham9_2_rowPermutedMatrix_maxEntryNorm hn_pos A hLU.perm]
      using htrace_growth
  have hL_diag : ∀ i : Fin n, L_hat i i ≠ 0 := by
    intro i
    rw [hLU.L_diag i]
    norm_num
  obtain ⟨ΔPA, hΔPA_bound, hΔPA_eq⟩ :=
    higham9_5_wilkinson_source_bound_of_entry_growth fp n hn_pos Aperm
      L_hat U_hat bP ((2 : ℝ) ^ (n - 1)) hApermmax
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n - 1))
      hgrowth hL_diag hU_diag
      (higham9_2_permutedLUBackwardError_to_LUBackwardError hLU) hn hn3 hL_bound
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hLU.perm
  let ΔA : Fin n → Fin n → ℝ := fun i j => ΔPA (eSigma.symm i) j
  refine ⟨ΔA, ?_, ?_⟩
  · have hrow_eq :
        higham9_2_rowPermutedMatrix ΔA sigma = ΔPA := by
      funext i j
      have hsigma_left : eSigma.symm (sigma i) = i := by
        change eSigma.symm (eSigma i) = i
        exact Equiv.symm_apply_apply eSigma i
      simp [ΔA, higham9_2_rowPermutedMatrix, hsigma_left]
    have hΔnorm : infNorm ΔA = infNorm ΔPA := by
      have hpermΔ := higham9_2_rowPermutedMatrix_infNorm ΔA hLU.perm
      rw [hrow_eq] at hpermΔ
      exact hpermΔ.symm
    have hAperm_inf : infNorm Aperm = infNorm A := by
      simpa [Aperm] using higham9_2_rowPermutedMatrix_infNorm A hLU.perm
    calc
      infNorm ΔA = infNorm ΔPA := hΔnorm
      _ ≤ (↑n) ^ 2 * gamma fp (3 * n) *
            (2 : ℝ) ^ (n - 1) * infNorm Aperm := hΔPA_bound
      _ = (↑n) ^ 2 * gamma fp (3 * n) *
            (2 : ℝ) ^ (n - 1) * infNorm A := by
          rw [hAperm_inf]
  · intro i
    have hrow := hΔPA_eq (eSigma.symm i)
    have hsigma_symm : sigma (eSigma.symm i) = i := by
      change eSigma (eSigma.symm i) = i
      exact Equiv.apply_symm_apply eSigma i
    calc
      ∑ j : Fin n, (A i j + ΔA i j) *
          (fl_backSub fp n U_hat (fl_forwardSub fp n L_hat bP)) j
          = ∑ j : Fin n, (Aperm (eSigma.symm i) j + ΔPA (eSigma.symm i) j) *
              (fl_backSub fp n U_hat (fl_forwardSub fp n L_hat bP)) j := by
            apply Finset.sum_congr rfl
            intro j _
            simp [Aperm, higham9_2_rowPermutedMatrix, ΔA, hsigma_symm]
      _ = bP (eSigma.symm i) := hrow
      _ = b i := by simp [bP, hsigma_symm]

/-- **Theorem 9.8**, product lower-bound form:
`1 ≤ ρ^n α^n β^n`, with max-entry norms for `α` and `β`. -/
theorem higham9_8_growth_factor_product_lower_bound {n : ℕ} (hn : 0 < n)
    (A A_inv U : Fin n → Fin n → ℝ) (hA : 0 < maxEntryNorm hn A)
    (det_A det_Ainv : ℝ)
    (hdet_prod : |det_A| * |det_Ainv| = 1)
    (hdet : |det_A| ≤ ∏ k : Fin n, |U k k|)
    (hdet_inv : |det_Ainv| ≤ (maxEntryNorm hn A_inv) ^ n) :
    1 ≤ (growthFactorEntry hn A U hA) ^ n *
        (maxEntryNorm hn A) ^ n * (maxEntryNorm hn A_inv) ^ n :=
  growth_factor_product_lower_bound hn A A_inv U hA det_A det_Ainv
    hdet_prod hdet hdet_inv

/-- **Theorem 9.8**, real max-entry proof of `θ ≤ n`.
For `α = maxEntry(A)` and `β = maxEntry(A⁻¹)`, a row inverse identity
`∑ⱼ aᵢⱼ (A⁻¹)ⱼᵢ = 1` implies `(αβ)⁻¹ ≤ n`. -/
theorem higham9_8_theta_le_card_real {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (i : Fin n)
    (hA : 0 < maxEntryNorm hn A)
    (hAinv : 0 < maxEntryNorm hn A_inv)
    (hrow : ∑ j : Fin n, A i j * A_inv j i = 1) :
    1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv) ≤ n :=
  theta_le_card_of_inverse_row_identity hn A A_inv i hA hAinv hrow

/-- **Theorem 9.8**, real max-entry `ρ ≥ θ` bridge.
If the final pivot supplies Higham's inverse-entry witness
`|u|⁻¹ ≤ β` and `|u|` is bounded by the largest entry reached in `U`,
then `growthFactorEntry A U ≥ (αβ)⁻¹`. -/
theorem higham9_8_growth_factor_ge_theta_real {n : ℕ} (hn : 0 < n)
    (A A_inv U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hAinv : 0 < maxEntryNorm hn A_inv)
    (u : ℝ) (hu_pos : 0 < |u|)
    (hu_entry : |u| ≤ maxEntryNorm hn U)
    (hu_inv_le : |u|⁻¹ ≤ maxEntryNorm hn A_inv) :
    1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv) ≤
      growthFactorEntry hn A U hA :=
  growthFactorEntry_ge_inverse_entry_theta hn A A_inv U hA hAinv
    u hu_pos hu_entry hu_inv_le

/-- **Theorem 9.8**, final-pivot inverse-entry identity for an exact no-pivot
LU certificate.

If `A = L U` with `L` unit lower triangular and `U` upper triangular, and
`A_inv` is a right inverse of `A`, then the final pivot `u_nn` and the final
diagonal entry of `A_inv` satisfy `u_nn * (A_inv)_nn = 1`.  This is the
local algebraic content of Higham's displayed identity (9.11) before adding
row/column permutations. -/
theorem higham9_8_finalPivot_mul_inverse_entry_eq_one {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLU : LUFactSpec (m + 1) A L U)
    (hRight : IsRightInverse (m + 1) A A_inv) :
    U (Fin.last m) (Fin.last m) *
      A_inv (Fin.last m) (Fin.last m) = 1 := by
  classical
  let n := m + 1
  let last : Fin n := Fin.last m
  let Y : Fin n → Fin n → ℝ := matMul n U A_inv
  have hLU_product : matMul n L U = A := by
    ext i j
    exact hLU.product_eq i j
  have hYRight : IsRightInverse n L Y := by
    intro i j
    have hassoc := congrFun (congrFun (matMul_assoc n L U A_inv) i) j
    have hright := hRight i j
    calc
      ∑ k : Fin n, L i k * Y k j
          = matMul n L Y i j := rfl
      _ = matMul n (matMul n L U) A_inv i j := by
            simpa [Y] using hassoc.symm
      _ = matMul n A A_inv i j := by rw [hLU_product]
      _ = ∑ k : Fin n, A i k * A_inv k j := rfl
      _ = if i = j then 1 else 0 := hright
  have hLT_transpose :
      ∀ i j : Fin n, j.val < i.val →
        finiteTranspose L i j = 0 := by
    intro i j hji
    exact hLU.L_upper_zero j i (by simpa [finiteTranspose] using hji)
  have hL_diag_ne : ∀ i : Fin n, finiteTranspose L i i ≠ 0 := by
    intro i
    simp [finiteTranspose, hLU.L_diag i]
  have hYLeftT :
      IsLeftInverse n (finiteTranspose L) (finiteTranspose Y) :=
    isLeftInverse_finiteTranspose_of_isRightInverse hYRight
  have hYt_upper :
      ∀ i j : Fin n, j.val < i.val →
        finiteTranspose Y i j = 0 :=
    inv_upper_tri n (finiteTranspose L) (finiteTranspose Y)
      hLT_transpose hL_diag_ne hYLeftT
  have hYt_diag :
      ∀ i : Fin n, finiteTranspose Y i i =
        1 / finiteTranspose L i i :=
    inv_diag_entry n (finiteTranspose L) (finiteTranspose Y)
      hLT_transpose hL_diag_ne hYLeftT hYt_upper
  have hY_last_diag : Y last last = 1 := by
    have h := hYt_diag last
    simpa [finiteTranspose, hLU.L_diag last] using h
  have hY_last_last :
      Y last last =
        U last last * A_inv last last := by
    unfold Y matMul
    exact Finset.sum_eq_single last
      (fun k _ hk => by
        have hk_val_ne : k.val ≠ last.val := by
          intro hval
          exact hk (Fin.ext hval)
        have hk_lt : k.val < last.val := by
          have hlast_val : last.val = m := by simp [last]
          have hk_le : k.val ≤ m := Nat.le_of_lt_succ k.isLt
          have hk_ne_m : k.val ≠ m := by
            intro hkm
            exact hk_val_ne (by simpa [hlast_val] using hkm)
          have hk_lt_m : k.val < m := lt_of_le_of_ne hk_le hk_ne_m
          simpa [hlast_val] using hk_lt_m
        rw [hLU.U_lower_zero last k (by simpa [last] using hk_lt), zero_mul])
      (fun hnot => (hnot (Finset.mem_univ last)).elim)
  rw [hY_last_last] at hY_last_diag
  exact hY_last_diag

/-- **Theorem 9.8**, final-pivot inverse-entry max-entry witness for an exact
no-pivot LU certificate.

This discharges the witness hypothesis of
`higham9_8_growth_factor_ge_theta_real` directly from `A = L U` and
`A A_inv = I`, for the unpermuted exact-LU case. -/
theorem higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLU : LUFactSpec (m + 1) A L U)
    (hRight : IsRightInverse (m + 1) A A_inv) :
    |U (Fin.last m) (Fin.last m)|⁻¹ ≤
      maxEntryNorm (Nat.succ_pos m) A_inv := by
  classical
  let last : Fin (m + 1) := Fin.last m
  let u : ℝ := U last last
  have hprod :
      u * A_inv last last = 1 := by
    simpa [u, last] using
      higham9_8_finalPivot_mul_inverse_entry_eq_one A A_inv L U hLU hRight
  have hu_ne : u ≠ 0 := by
    intro hu
    rw [hu] at hprod
    norm_num at hprod
  have hentry_eq : A_inv last last = u⁻¹ := by
    field_simp [hu_ne]
    simpa [mul_comm] using hprod
  calc
    |U (Fin.last m) (Fin.last m)|⁻¹
        = |u|⁻¹ := by simp [u, last]
    _ = |u⁻¹| := by rw [abs_inv]
    _ = |A_inv last last| := by rw [← hentry_eq]
    _ ≤ maxEntryNorm (Nat.succ_pos m) A_inv :=
        entry_le_maxEntryNorm (Nat.succ_pos m) A_inv last last

/-- **Theorem 9.8**, unpermuted exact-LU lower bound `rho >= theta`.

For an exact no-pivot LU certificate and a visible right inverse of `A`, the
final-pivot identity proves Higham's inverse-entry witness and therefore
`growthFactorEntry(A,U) >= (alpha beta)^{-1}`.  The remaining fully general
source theorem still needs the row/column-permuted `P A Q = L U` trace. -/
theorem higham9_8_growth_factor_ge_theta_of_lu_right_inverse {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLU : LUFactSpec (m + 1) A L U)
    (hRight : IsRightInverse (m + 1) A A_inv)
    (hA : 0 < maxEntryNorm (Nat.succ_pos m) A)
    (hAinv : 0 < maxEntryNorm (Nat.succ_pos m) A_inv) :
    1 / (maxEntryNorm (Nat.succ_pos m) A *
        maxEntryNorm (Nat.succ_pos m) A_inv) ≤
      growthFactorEntry (Nat.succ_pos m) A U hA := by
  classical
  let last : Fin (m + 1) := Fin.last m
  let u : ℝ := U last last
  have hprod :
      u * A_inv last last = 1 := by
    simpa [u, last] using
      higham9_8_finalPivot_mul_inverse_entry_eq_one A A_inv L U hLU hRight
  have hu_ne : u ≠ 0 := by
    intro hu
    rw [hu] at hprod
    norm_num at hprod
  have hu_pos : 0 < |u| := abs_pos.mpr hu_ne
  have hu_entry :
      |u| ≤ maxEntryNorm (Nat.succ_pos m) U := by
    simpa [u, last] using
      entry_le_maxEntryNorm (Nat.succ_pos m) U last last
  have hu_inv_le :
      |u|⁻¹ ≤ maxEntryNorm (Nat.succ_pos m) A_inv := by
    simpa [u, last] using
      higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm
        A A_inv L U hLU hRight
  exact higham9_8_growth_factor_ge_theta_real (Nat.succ_pos m) A A_inv U
    hA hAinv u hu_pos hu_entry hu_inv_le

/-- **Theorem 9.8 / equation (9.11)**, final-pivot identity for an explicit
complete-pivoting certificate `P A Q = L U`.

For a source `PAQ = LU` certificate and a visible right inverse of the original
matrix `A`, the final pivot satisfies
`u_nn * (A_inv)_(tau n, sigma n) = 1`. -/
theorem higham9_8_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec
    {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (sigma tau : Fin (m + 1) → Fin (m + 1))
    (hLU : higham9_2_CompletePermutedLUFactSpec (m + 1) A L U sigma tau)
    (hRight : IsRightInverse (m + 1) A A_inv) :
    U (Fin.last m) (Fin.last m) *
      A_inv (tau (Fin.last m)) (sigma (Fin.last m)) = 1 := by
  classical
  let B : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_2_rowColPermutedMatrix A sigma tau
  let B_inv : Fin (m + 1) → Fin (m + 1) → ℝ :=
    fun i j => A_inv (tau i) (sigma j)
  have hBRight : IsRightInverse (m + 1) B B_inv :=
    higham9_2_rowColPermutedMatrix_right_inverse hLU.2.perm hLU.1 hRight
  have hBLU : LUFactSpec (m + 1) B L U :=
    higham9_2_completePermutedLUFactSpec_to_LUFactSpec hLU
  simpa [B, B_inv] using
    higham9_8_finalPivot_mul_inverse_entry_eq_one B B_inv L U hBLU hBRight

/-- **Theorem 9.8**, final-pivot inverse-entry max-entry witness for an
explicit complete-pivoting certificate `P A Q = L U`. -/
theorem higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm_of_completePermutedLUFactSpec
    {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (sigma tau : Fin (m + 1) → Fin (m + 1))
    (hLU : higham9_2_CompletePermutedLUFactSpec (m + 1) A L U sigma tau)
    (hRight : IsRightInverse (m + 1) A A_inv) :
    |U (Fin.last m) (Fin.last m)|⁻¹ ≤
      maxEntryNorm (Nat.succ_pos m) A_inv := by
  classical
  let last : Fin (m + 1) := Fin.last m
  let u : ℝ := U last last
  have hprod :
      u * A_inv (tau last) (sigma last) = 1 := by
    simpa [u, last] using
      higham9_8_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec
        A A_inv L U sigma tau hLU hRight
  have hu_ne : u ≠ 0 := by
    intro hu
    rw [hu] at hprod
    norm_num at hprod
  have hentry_eq : A_inv (tau last) (sigma last) = u⁻¹ := by
    field_simp [hu_ne]
    simpa [mul_comm] using hprod
  calc
    |U (Fin.last m) (Fin.last m)|⁻¹
        = |u|⁻¹ := by simp [u, last]
    _ = |u⁻¹| := by rw [abs_inv]
    _ = |A_inv (tau last) (sigma last)| := by rw [← hentry_eq]
    _ ≤ maxEntryNorm (Nat.succ_pos m) A_inv :=
        entry_le_maxEntryNorm (Nat.succ_pos m) A_inv (tau last) (sigma last)

/-- **Theorem 9.8**, complete-pivoting exact-LU lower bound `rho >= theta`.

This closes the equation (9.11) inverse-entry instantiation for an explicit
`P A Q = L U` certificate.  It still does not construct the complete-pivoting
trace that produces such a certificate. -/
theorem higham9_8_growth_factor_ge_theta_of_completePermutedLUFactSpec_right_inverse
    {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (sigma tau : Fin (m + 1) → Fin (m + 1))
    (hLU : higham9_2_CompletePermutedLUFactSpec (m + 1) A L U sigma tau)
    (hRight : IsRightInverse (m + 1) A A_inv)
    (hA : 0 < maxEntryNorm (Nat.succ_pos m) A)
    (hAinv : 0 < maxEntryNorm (Nat.succ_pos m) A_inv) :
    1 / (maxEntryNorm (Nat.succ_pos m) A *
        maxEntryNorm (Nat.succ_pos m) A_inv) ≤
      growthFactorEntry (Nat.succ_pos m) A U hA := by
  classical
  let last : Fin (m + 1) := Fin.last m
  let u : ℝ := U last last
  have hprod :
      u * A_inv (tau last) (sigma last) = 1 := by
    simpa [u, last] using
      higham9_8_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec
        A A_inv L U sigma tau hLU hRight
  have hu_ne : u ≠ 0 := by
    intro hu
    rw [hu] at hprod
    norm_num at hprod
  have hu_pos : 0 < |u| := abs_pos.mpr hu_ne
  have hu_entry :
      |u| ≤ maxEntryNorm (Nat.succ_pos m) U := by
    simpa [u, last] using
      entry_le_maxEntryNorm (Nat.succ_pos m) U last last
  have hu_inv_le :
      |u|⁻¹ ≤ maxEntryNorm (Nat.succ_pos m) A_inv := by
    simpa [u, last] using
      higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm_of_completePermutedLUFactSpec
        A A_inv L U sigma tau hLU hRight
  exact higham9_8_growth_factor_ge_theta_real (Nat.succ_pos m) A A_inv U
    hA hAinv u hu_pos hu_entry hu_inv_le

/-! ## Equation (9.12), sine matrix lower-bound witness -/

/-- **Equation (9.12)**, the real sine matrix
`S_n = sqrt(2/(n+1)) * (sin(i*j*pi/(n+1)))`, with the source's one-based
indices represented by `i.val + 1` and `j.val + 1`.  This is the matrix used in
the complete-pivoting lower-bound discussion and Problem 9.11; the sine
orthogonality/inverse certificate is proved below, while the complete-pivoting
growth witness remains a separate open target. -/
noncomputable def higham9_12_sineMatrix (n : ℕ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    Real.sqrt (2 / ((n : ℝ) + 1)) *
      Real.sin ((((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) * Real.pi) /
        ((n : ℝ) + 1))

/-- **Equation (9.12)**, the sine matrix is symmetric. -/
theorem higham9_12_sineMatrix_symm {n : ℕ} (i j : Fin n) :
    higham9_12_sineMatrix n i j = higham9_12_sineMatrix n j i := by
  unfold higham9_12_sineMatrix
  congr 2
  ring

/-- **Equation (9.12)**, every entry of the sine lower-bound witness has
absolute value at most the source scale factor `sqrt(2/(n+1))`. -/
theorem higham9_12_sineMatrix_entry_abs_le_scale (n : ℕ) (i j : Fin n) :
    |higham9_12_sineMatrix n i j| ≤ Real.sqrt (2 / ((n : ℝ) + 1)) := by
  unfold higham9_12_sineMatrix
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_sin_le_one _)

/-- **Equation (9.12)**, max-entry norm of the sine lower-bound witness is
bounded by the source scale factor `sqrt(2/(n+1))`. -/
theorem higham9_12_sineMatrix_maxEntryNorm_le_scale {n : ℕ} (hn : 0 < n) :
    maxEntryNorm hn (higham9_12_sineMatrix n) ≤
      Real.sqrt (2 / ((n : ℝ) + 1)) := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact higham9_12_sineMatrix_entry_abs_le_scale n i j

/-- **Equation (9.12)**, the first sine-matrix entry is strictly positive.
This supplies the nonzero max-entry side condition used by the local theta
arithmetic. -/
theorem higham9_12_sineMatrix_zero_zero_pos {n : ℕ} (hn : 0 < n) :
    0 < higham9_12_sineMatrix n ⟨0, hn⟩ ⟨0, hn⟩ := by
  unfold higham9_12_sineMatrix
  have hden_pos : 0 < (n : ℝ) + 1 := by positivity
  have hscale_pos : 0 < Real.sqrt (2 / ((n : ℝ) + 1)) := by
    exact Real.sqrt_pos.2 (by positivity)
  have hangle_pos : 0 < Real.pi / ((n : ℝ) + 1) :=
    div_pos Real.pi_pos hden_pos
  have hangle_lt_pi : Real.pi / ((n : ℝ) + 1) < Real.pi := by
    have hn1 : 1 < (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_lt_succ hn
    rw [div_lt_iff₀ hden_pos]
    nlinarith [Real.pi_pos, hn1]
  have hsin_pos : 0 < Real.sin (Real.pi / ((n : ℝ) + 1)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle_pos hangle_lt_pi
  have harg :
      (((((0 + 1 : ℕ) : ℝ) * ((0 + 1 : ℕ) : ℝ) * Real.pi) /
          ((n : ℝ) + 1))) =
        Real.pi / ((n : ℝ) + 1) := by
    norm_num
  rw [harg]
  exact mul_pos hscale_pos hsin_pos

/-- **Equation (9.12)**, the sine witness has positive max-entry norm for
nonempty matrices. -/
theorem higham9_12_sineMatrix_maxEntryNorm_pos {n : ℕ} (hn : 0 < n) :
    0 < maxEntryNorm hn (higham9_12_sineMatrix n) := by
  have hentry_pos := higham9_12_sineMatrix_zero_zero_pos hn
  have hentry_le :=
    entry_le_maxEntryNorm hn (higham9_12_sineMatrix n) ⟨0, hn⟩ ⟨0, hn⟩
  have habs_pos : 0 < |higham9_12_sineMatrix n ⟨0, hn⟩ ⟨0, hn⟩| :=
    abs_pos.mpr (ne_of_gt hentry_pos)
  exact lt_of_lt_of_le habs_pos hentry_le

/-- **Equation (9.12)** support, even sine-root power:
`exp(i * (2q*pi/N))^N = 1`. -/
theorem higham9_12_sineRoot_pow_even (N q : ℕ) (hN : 0 < N) :
    (Complex.exp ((((((2 * q : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I))) ^ N = 1 := by
  rw [← Complex.exp_nat_mul]
  rw [show (N : ℂ) *
        ((((((2 * q : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)) =
        (q : ℂ) * (2 * Real.pi * Complex.I) by
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
          norm_num [Complex.ext_iff]
          field_simp [hNR]]
  simp

/-- **Equation (9.12)** support, odd sine-root power:
`exp(i * ((2q+1)*pi/N))^N = -1`. -/
theorem higham9_12_sineRoot_pow_odd (N q : ℕ) (hN : 0 < N) :
    (Complex.exp ((((((2 * q + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I))) ^ N = -1 := by
  rw [← Complex.exp_nat_mul]
  rw [show (N : ℂ) *
        ((((((2 * q + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)) =
        (q : ℂ) * (2 * Real.pi * Complex.I) + (Real.pi : ℂ) * Complex.I by
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
          norm_num [Complex.ext_iff]
          field_simp [hNR]]
  rw [Complex.exp_add, Complex.exp_pi_mul_I]
  simp

/-- **Equation (9.12)** support, a nonzero sine root with frequency
`0 < m < 2N` is not `1`. -/
theorem higham9_12_sineRoot_ne_one (N m : ℕ) (hN : 0 < N)
    (hmpos : 0 < m) (hmlt : m < 2 * N) :
    Complex.exp (((((m : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I)) ≠ 1 := by
  intro h
  have h' : Complex.exp (((((m : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I)) = Complex.exp 0 := by
    simpa using h
  rw [Complex.exp_eq_exp_iff_exists_int] at h'
  rcases h' with ⟨z, hz⟩
  have him := congrArg Complex.im hz
  have hm_real : ((m : ℝ) * Real.pi / (N : ℝ)) =
      (z : ℝ) * (2 * Real.pi) := by
    simpa [Complex.ext_iff, mul_assoc, mul_comm, mul_left_comm] using him
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hz_eq : (z : ℝ) = (m : ℝ) / (2 * (N : ℝ)) := by
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
    field_simp [hNR, hpi] at hm_real ⊢
    nlinarith
  have hz_pos : 0 < (z : ℝ) := by
    rw [hz_eq]
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hdenR : 0 < (2 : ℝ) * (N : ℝ) := by positivity
    exact div_pos hmR hdenR
  have hz_int_pos : 0 < z := by
    exact_mod_cast hz_pos
  have hz_ge_one : 1 ≤ z := by omega
  have hz_cast_ge_one : (1 : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast hz_ge_one
  have hz_lt_one : (z : ℝ) < 1 := by
    rw [hz_eq]
    have hmRlt : (m : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hmlt
    have hdenR : 0 < (2 : ℝ) * (N : ℝ) := by positivity
    rw [div_lt_one hdenR]
    simpa [mul_assoc] using hmRlt
  linarith

/-- **Equation (9.12)** support, shifted geometric sum for an even nonzero
frequency.  The sum is over `r = 1, ..., N-1`, represented as
`Fin (N-1)` with exponent `r.val + 1`. -/
theorem higham9_12_shifted_geometric_sum_even (N q : ℕ) (hN : 1 < N)
    (hqlt : 2 * q < 2 * N) (hqpos : 0 < q) :
    let ζ : ℂ := Complex.exp ((((((2 * q : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I))
    (∑ r : Fin (N - 1), ζ ^ (r.val + 1)) = -1 := by
  classical
  let ζ : ℂ := Complex.exp ((((((2 * q : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
      Complex.I))
  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN
  have hζpow : ζ ^ N = 1 := by
    simpa [ζ] using higham9_12_sineRoot_pow_even N q hNpos
  have hζne : ζ ≠ 1 := by
    have hmpos : 0 < 2 * q := Nat.mul_pos (by norm_num) hqpos
    simpa [ζ] using higham9_12_sineRoot_ne_one N (2 * q) hNpos hmpos hqlt
  have hgeom := geom_sum_eq hζne N
  have hsumN : (∑ i ∈ Finset.range N, ζ ^ i) = 0 := by
    rw [hζpow] at hgeom
    simpa [hζne] using hgeom
  have hNpred : N - 1 + 1 = N :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hNpos)
  have hsplit :
      (∑ i ∈ Finset.range N, ζ ^ i) =
        (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) + 1 := by
    rw [← hNpred]
    simpa [pow_zero, add_comm] using
      (Finset.sum_range_succ' (fun i : ℕ => ζ ^ i) (N - 1))
  have hshift_range : (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) = -1 := by
    have hzero : (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) + 1 = 0 := by
      simpa [hsplit] using hsumN
    calc
      (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1))
          = ((∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) + 1) - 1 := by ring
      _ = 0 - 1 := by rw [hzero]
      _ = -1 := by ring
  change (∑ r : Fin (N - 1), ζ ^ (r.val + 1)) = -1
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ζ ^ (i + 1)) (N - 1)]
  exact hshift_range

/-- **Equation (9.12)** support, real part of a shifted sine-root power. -/
theorem higham9_12_sineRoot_shifted_pow_re_eq_cos (N m K : ℕ) (hN : 0 < N)
    (r : Fin K) :
    let ζ : ℂ := Complex.exp (((((m : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I))
    (ζ ^ (r.val + 1)).re =
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * (m : ℝ) * Real.pi) / (N : ℝ)) := by
  let ζ : ℂ := Complex.exp (((((m : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
      Complex.I))
  let x : ℝ :=
    (((r.val + 1 : ℕ) : ℝ) * (m : ℝ) * Real.pi) / (N : ℝ)
  change (ζ ^ (r.val + 1)).re = Real.cos x
  unfold ζ
  rw [← Complex.exp_nat_mul]
  rw [show ((r.val + 1 : ℕ) : ℂ) *
        ((((m : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I) =
        ((x : ℂ) * Complex.I) by
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
          norm_num [Complex.ext_iff]
          field_simp [hNR]
          dsimp [x]
          simp [Nat.cast_add]
          field_simp [hNR]]
  rw [Complex.exp_ofReal_mul_I]
  rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- **Equation (9.12)** support, finite cosine sum for an even positive
frequency `2q` with `0 < 2q < 2N`:
`sum_{r=1}^{N-1} cos(r*2q*pi/N) = -1`. -/
theorem higham9_12_cos_sum_even (N q : ℕ) (hN : 1 < N)
    (hqlt : 2 * q < 2 * N) (hqpos : 0 < q) :
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((2 * q : ℕ) : ℝ) * Real.pi) /
        (N : ℝ))) = -1 := by
  classical
  let ζ : ℂ := Complex.exp ((((((2 * q : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
      Complex.I))
  have hcomplex :
      (∑ r : Fin (N - 1), ζ ^ (r.val + 1)) = -1 := by
    simpa [ζ] using higham9_12_shifted_geometric_sum_even N q hN hqlt hqpos
  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN
  calc
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((2 * q : ℕ) : ℝ) * Real.pi) /
        (N : ℝ)))
        = ∑ r : Fin (N - 1), (ζ ^ (r.val + 1)).re := by
          apply Finset.sum_congr rfl
          intro r _
          exact (higham9_12_sineRoot_shifted_pow_re_eq_cos
            N (2 * q) (N - 1) hNpos r).symm
    _ = (∑ r : Fin (N - 1), ζ ^ (r.val + 1)).re := by simp
    _ = -1 := by rw [hcomplex]; norm_num

private theorem higham9_12_inv_sub_one_re_of_normSq_eq_one {z : ℂ}
    (hzunit : Complex.normSq z = 1) (hzne : z ≠ 1) :
    ((z - 1)⁻¹).re = -1 / 2 := by
  rw [Complex.inv_re]
  have hnorm_sub : Complex.normSq (z - 1) = 2 - 2 * z.re := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    norm_num
    rw [Complex.normSq_apply] at hzunit
    nlinarith
  have hden : 2 - 2 * z.re ≠ 0 := by
    intro h
    have hzre : z.re = 1 := by linarith
    have hzim_sq : z.im * z.im = 0 := by
      rw [Complex.normSq_apply] at hzunit
      nlinarith
    have hzim : z.im = 0 := by
      exact mul_self_eq_zero.mp hzim_sq
    apply hzne
    rw [Complex.ext_iff]
    constructor <;> simp [hzre, hzim]
  rw [Complex.sub_re]
  norm_num
  rw [hnorm_sub]
  have hden1 : 1 - z.re ≠ 0 := by
    intro h
    apply hden
    nlinarith
  field_simp [hden, hden1]
  ring

/-- **Equation (9.12)** support, the shifted odd-frequency geometric sum has
zero real part. -/
theorem higham9_12_shifted_geometric_sum_odd_re (N q : ℕ) (hN : 1 < N)
    (hqlt : 2 * q + 1 < 2 * N) :
    let ζ : ℂ := Complex.exp ((((((2 * q + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I))
    ((∑ r : Fin (N - 1), ζ ^ (r.val + 1)).re) = 0 := by
  classical
  let ζ : ℂ := Complex.exp ((((((2 * q + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
      Complex.I))
  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN
  have hζpow : ζ ^ N = -1 := by
    simpa [ζ] using higham9_12_sineRoot_pow_odd N q hNpos
  have hζne : ζ ≠ 1 := by
    have hmpos : 0 < 2 * q + 1 := by omega
    simpa [ζ] using higham9_12_sineRoot_ne_one N (2 * q + 1) hNpos hmpos hqlt
  have hgeom := geom_sum_eq hζne N
  have hsumN : (∑ i ∈ Finset.range N, ζ ^ i) = (-2 : ℂ) / (ζ - 1) := by
    rw [hζpow] at hgeom
    calc
      (∑ i ∈ Finset.range N, ζ ^ i) = ((-1 : ℂ) - 1) / (ζ - 1) := by
        simpa using hgeom
      _ = (-2 : ℂ) / (ζ - 1) := by norm_num
  have hNpred : N - 1 + 1 = N :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hNpos)
  have hsplit :
      (∑ i ∈ Finset.range N, ζ ^ i) =
        (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) + 1 := by
    rw [← hNpred]
    simpa [pow_zero, add_comm] using
      (Finset.sum_range_succ' (fun i : ℕ => ζ ^ i) (N - 1))
  have hshift_range :
      (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) =
        (-2 : ℂ) / (ζ - 1) - 1 := by
    calc
      (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1))
          = ((∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) + 1) - 1 := by ring
      _ = (∑ i ∈ Finset.range N, ζ ^ i) - 1 := by rw [← hsplit]
      _ = (-2 : ℂ) / (ζ - 1) - 1 := by rw [hsumN]
  have hshift_fin :
      (∑ r : Fin (N - 1), ζ ^ (r.val + 1)) =
        (-2 : ℂ) / (ζ - 1) - 1 := by
    change (∑ r : Fin (N - 1), ζ ^ (r.val + 1)) =
      (-2 : ℂ) / (ζ - 1) - 1
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ζ ^ (i + 1)) (N - 1)]
    exact hshift_range
  have hζ_normSq : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hinv_re : ((ζ - 1)⁻¹).re = -1 / 2 :=
    higham9_12_inv_sub_one_re_of_normSq_eq_one hζ_normSq hζne
  change ((∑ r : Fin (N - 1), ζ ^ (r.val + 1)).re) = 0
  rw [hshift_fin]
  rw [div_eq_mul_inv]
  rw [Complex.sub_re, Complex.mul_re, hinv_re]
  have hminus_re : ((-2 : ℂ).re) = -2 := by norm_num
  have hminus_im : ((-2 : ℂ).im) = 0 := by norm_num
  have hone_re : ((1 : ℂ).re) = 1 := by norm_num
  rw [hminus_re, hminus_im, hone_re]
  have hprod : (-2 : ℝ) * (-1 / 2) = 1 := by norm_num
  rw [hprod, zero_mul]
  rw [sub_zero]
  exact sub_self (1 : ℝ)

/-- **Equation (9.12)** support, finite cosine sum for an odd positive
frequency `2q+1` with `2q+1 < 2N`:
`sum_{r=1}^{N-1} cos(r*(2q+1)*pi/N) = 0`. -/
theorem higham9_12_cos_sum_odd (N q : ℕ) (hN : 1 < N)
    (hqlt : 2 * q + 1 < 2 * N) :
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((2 * q + 1 : ℕ) : ℝ) * Real.pi) /
        (N : ℝ))) = 0 := by
  classical
  let ζ : ℂ := Complex.exp ((((((2 * q + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
      Complex.I))
  have hcomplex_re :
      ((∑ r : Fin (N - 1), ζ ^ (r.val + 1)).re) = 0 := by
    simpa [ζ] using higham9_12_shifted_geometric_sum_odd_re N q hN hqlt
  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN
  calc
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((2 * q + 1 : ℕ) : ℝ) * Real.pi) /
        (N : ℝ)))
        = ∑ r : Fin (N - 1), (ζ ^ (r.val + 1)).re := by
          apply Finset.sum_congr rfl
          intro r _
          exact (higham9_12_sineRoot_shifted_pow_re_eq_cos
            N (2 * q + 1) (N - 1) hNpos r).symm
    _ = (∑ r : Fin (N - 1), ζ ^ (r.val + 1)).re := by simp
    _ = 0 := hcomplex_re

/-- **Equation (9.12)** support, finite cosine sum for any positive frequency
`m` with `m < 2N`, split by parity. -/
theorem higham9_12_cos_sum_pos_lt_two_mul (N m : ℕ) (hN : 1 < N)
    (hmpos : 0 < m) (hmlt : m < 2 * N) :
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * (m : ℝ) * Real.pi) / (N : ℝ))) =
      if Even m then -1 else 0 := by
  classical
  by_cases hEven : Even m
  · rw [if_pos hEven]
    rcases hEven with ⟨q, hq⟩
    have hm_eq : m = 2 * q := by simpa [two_mul] using hq
    rw [hm_eq] at hmlt ⊢
    have hqpos : 0 < q := by omega
    simpa using higham9_12_cos_sum_even N q hN hmlt hqpos
  · rw [if_neg hEven]
    have hOdd : Odd m := Nat.not_even_iff_odd.mp hEven
    rcases hOdd with ⟨q, hq⟩
    have hm_eq : m = 2 * q + 1 := by
      simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
    rw [hm_eq] at hmlt ⊢
    simpa [Nat.cast_add, Nat.cast_mul] using higham9_12_cos_sum_odd N q hN hmlt

/-- **Equation (9.12)** support, positive frequencies below `2N` with the
same parity have the same finite cosine sum. -/
theorem higham9_12_cos_sum_eq_of_mod_two_eq (N m k : ℕ) (hN : 1 < N)
    (hmpos : 0 < m) (hmlt : m < 2 * N)
    (hkpos : 0 < k) (hklt : k < 2 * N)
    (hpar : m % 2 = k % 2) :
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * (m : ℝ) * Real.pi) / (N : ℝ))) =
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * (k : ℝ) * Real.pi) / (N : ℝ))) := by
  classical
  rw [higham9_12_cos_sum_pos_lt_two_mul N m hN hmpos hmlt,
    higham9_12_cos_sum_pos_lt_two_mul N k hN hkpos hklt]
  have hEven_iff : Even m ↔ Even k := by
    rw [Nat.even_iff, Nat.even_iff, hpar]
  by_cases hm : Even m
  · have hk : Even k := hEven_iff.mp hm
    simp [hm, hk]
  · have hk : ¬ Even k := by
      intro hk
      exact hm (hEven_iff.mpr hk)
    simp [hm, hk]

/-- **Equation (9.12)**, unscaled discrete sine orthogonality:
for `0 < p,q < N`,
`sum_{r=1}^{N-1} sin(r*p*pi/N) sin(r*q*pi/N)` is `N/2` on the
diagonal and `0` off the diagonal. -/
theorem higham9_12_sine_product_sum (N p q : ℕ) (hN : 1 < N)
    (hp : 0 < p) (hpN : p < N) (hq : 0 < q) (hqN : q < N) :
    (∑ r : Fin (N - 1),
      Real.sin ((((r.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)) *
        Real.sin ((((r.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ))) =
      if p = q then (N : ℝ) / 2 else 0 := by
  classical
  let X : Fin (N - 1) → ℝ :=
    fun r => (((r.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)
  let Y : Fin (N - 1) → ℝ :=
    fun r => (((r.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ)
  let S : ℝ := ∑ r : Fin (N - 1), Real.sin (X r) * Real.sin (Y r)
  have htwo :
      2 * S =
        (∑ r : Fin (N - 1), Real.cos (X r - Y r)) -
          (∑ r : Fin (N - 1), Real.cos (X r + Y r)) := by
    calc
      2 * S = ∑ r : Fin (N - 1), 2 * (Real.sin (X r) * Real.sin (Y r)) := by
        simp [S, Finset.mul_sum]
      _ = ∑ r : Fin (N - 1), (Real.cos (X r - Y r) - Real.cos (X r + Y r)) := by
        apply Finset.sum_congr rfl
        intro r _
        calc
          2 * (Real.sin (X r) * Real.sin (Y r))
              = 2 * Real.sin (X r) * Real.sin (Y r) := by ring
          _ = Real.cos (X r - Y r) - Real.cos (X r + Y r) :=
              Real.two_mul_sin_mul_sin (X r) (Y r)
      _ = (∑ r : Fin (N - 1), Real.cos (X r - Y r)) -
          (∑ r : Fin (N - 1), Real.cos (X r + Y r)) := by
        rw [Finset.sum_sub_distrib]
  by_cases hpq : p = q
  · subst q
    have hdiff :
        (∑ r : Fin (N - 1), Real.cos (X r - Y r)) = (N : ℝ) - 1 := by
      simp [X, Y]
      have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN
      rw [Nat.cast_sub (Nat.succ_le_iff.mpr hNpos)]
      norm_num
    have hsum_arg :
        (∑ r : Fin (N - 1), Real.cos (X r + Y r)) =
          (∑ r : Fin (N - 1),
            Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((2 * p : ℕ) : ℝ) * Real.pi) /
              (N : ℝ))) := by
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.lt_trans Nat.zero_lt_one hN)
      dsimp [X, Y]
      field_simp [hNR]
      simp [Nat.cast_mul]
      ring
    have hsum :
        (∑ r : Fin (N - 1), Real.cos (X r + Y r)) = -1 := by
      rw [hsum_arg]
      have hp2lt : 2 * p < 2 * N := by omega
      exact higham9_12_cos_sum_even N p hN hp2lt hp
    have htwoN : 2 * S = (N : ℝ) := by
      rw [htwo, hdiff, hsum]
      norm_num
    have hS : S = (N : ℝ) / 2 := by nlinarith
    simpa [S, X, Y] using hS
  · have hoff : S = 0 := by
      have hlt_or_gt : p < q ∨ q < p := lt_or_gt_of_ne hpq
      rcases hlt_or_gt with hpq_lt | hqp_lt
      · have hdiff_arg :
            (∑ r : Fin (N - 1), Real.cos (X r - Y r)) =
              (∑ r : Fin (N - 1),
                Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((q - p : ℕ) : ℝ) * Real.pi) /
                  (N : ℝ))) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [← Real.cos_neg]
          congr 1
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.lt_trans Nat.zero_lt_one hN)
          have hsub : ((q - p : ℕ) : ℝ) = (q : ℝ) - (p : ℝ) :=
            Nat.cast_sub hpq_lt.le
          dsimp [X, Y]
          field_simp [hNR]
          rw [hsub]
          ring
        have hsum_arg :
            (∑ r : Fin (N - 1), Real.cos (X r + Y r)) =
              (∑ r : Fin (N - 1),
                Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((p + q : ℕ) : ℝ) * Real.pi) /
                  (N : ℝ))) := by
          apply Finset.sum_congr rfl
          intro r _
          congr 1
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.lt_trans Nat.zero_lt_one hN)
          dsimp [X, Y]
          field_simp [hNR]
          simp [Nat.cast_add]
        have hbounds :
            0 < q - p ∧ q - p < 2 * N ∧ 0 < p + q ∧ p + q < 2 * N := by
          omega
        have hpar : (q - p) % 2 = (p + q) % 2 := by omega
        have heq :=
          higham9_12_cos_sum_eq_of_mod_two_eq N (q - p) (p + q) hN
            hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2 hpar
        have hdiff_eq_sum :
            (∑ r : Fin (N - 1), Real.cos (X r - Y r)) =
              (∑ r : Fin (N - 1), Real.cos (X r + Y r)) := by
          rw [hdiff_arg, hsum_arg]
          exact heq
        have htwo0 : 2 * S = 0 := by
          rw [htwo, hdiff_eq_sum]
          ring
        nlinarith
      · have hdiff_arg :
            (∑ r : Fin (N - 1), Real.cos (X r - Y r)) =
              (∑ r : Fin (N - 1),
                Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((p - q : ℕ) : ℝ) * Real.pi) /
                  (N : ℝ))) := by
          apply Finset.sum_congr rfl
          intro r _
          congr 1
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.lt_trans Nat.zero_lt_one hN)
          have hsub : ((p - q : ℕ) : ℝ) = (p : ℝ) - (q : ℝ) :=
            Nat.cast_sub hqp_lt.le
          dsimp [X, Y]
          field_simp [hNR]
          rw [hsub]
        have hsum_arg :
            (∑ r : Fin (N - 1), Real.cos (X r + Y r)) =
              (∑ r : Fin (N - 1),
                Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((p + q : ℕ) : ℝ) * Real.pi) /
                  (N : ℝ))) := by
          apply Finset.sum_congr rfl
          intro r _
          congr 1
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.lt_trans Nat.zero_lt_one hN)
          dsimp [X, Y]
          field_simp [hNR]
          simp [Nat.cast_add]
        have hbounds :
            0 < p - q ∧ p - q < 2 * N ∧ 0 < p + q ∧ p + q < 2 * N := by
          omega
        have hpar : (p - q) % 2 = (p + q) % 2 := by omega
        have heq :=
          higham9_12_cos_sum_eq_of_mod_two_eq N (p - q) (p + q) hN
            hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2 hpar
        have hdiff_eq_sum :
            (∑ r : Fin (N - 1), Real.cos (X r - Y r)) =
              (∑ r : Fin (N - 1), Real.cos (X r + Y r)) := by
          rw [hdiff_arg, hsum_arg]
          exact heq
        have htwo0 : 2 * S = 0 := by
          rw [htwo, hdiff_eq_sum]
          ring
        nlinarith
    simpa [S, X, Y, hpq] using hoff

/-- **Equation (9.12)**, the scaled sine matrix is its own inverse:
`S_n * S_n = I` entrywise. -/
theorem higham9_12_sineMatrix_mul_self {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    (∑ k : Fin n, higham9_12_sineMatrix n i k * higham9_12_sineMatrix n k j) =
      if i = j then 1 else 0 := by
  classical
  let c : ℝ := Real.sqrt (2 / ((n : ℝ) + 1))
  let N : ℕ := n + 1
  let p : ℕ := i.val + 1
  let q : ℕ := j.val + 1
  have hNgt : 1 < N := by
    dsimp [N]
    omega
  have hp_pos : 0 < p := by dsimp [p]; omega
  have hq_pos : 0 < q := by dsimp [q]; omega
  have hp_lt : p < N := by
    dsimp [p, N]
    omega
  have hq_lt : q < N := by
    dsimp [q, N]
    omega
  have hprod_sum :
      (∑ k : Fin n,
        Real.sin ((((k.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)) *
          Real.sin ((((k.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ))) =
        if p = q then (N : ℝ) / 2 else 0 := by
    simpa [N, p, q, Nat.add_sub_cancel] using
      higham9_12_sine_product_sum N p q hNgt hp_pos hp_lt hq_pos hq_lt
  have hscale_sq : c * c = 2 / ((n : ℝ) + 1) := by
    dsimp [c]
    rw [← pow_two, Real.sq_sqrt]
    positivity
  have hmain :
      (∑ k : Fin n, higham9_12_sineMatrix n i k * higham9_12_sineMatrix n k j) =
        c * c *
          (∑ k : Fin n,
            Real.sin ((((k.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)) *
              Real.sin ((((k.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ))) := by
    calc
      (∑ k : Fin n, higham9_12_sineMatrix n i k * higham9_12_sineMatrix n k j)
          = ∑ k : Fin n,
              c * Real.sin ((((k.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)) *
                (c * Real.sin ((((k.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ))) := by
            apply Finset.sum_congr rfl
            intro k _
            unfold higham9_12_sineMatrix
            dsimp [c, p, q, N]
            congr 2 <;> (norm_num [Nat.cast_add]; try ring_nf)
      _ = c * c *
          (∑ k : Fin n,
            Real.sin ((((k.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)) *
              Real.sin ((((k.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
  by_cases hij : i = j
  · subst j
    have hpq : p = q := by dsimp [p, q]
    rw [if_pos rfl]
    rw [hmain, hprod_sum, if_pos hpq, hscale_sq]
    dsimp [N]
    have hnR : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hnR]
    norm_num [Nat.cast_add]
  · have hpq : p ≠ q := by
      intro hpq
      apply hij
      apply Fin.ext
      dsimp [p, q] at hpq
      omega
    rw [if_neg hij]
    rw [hmain, hprod_sum, if_neg hpq]
    ring

/-- **Equation (9.12)**, inverse formula for the sine matrix:
the scaled sine matrix is both a left and right inverse of itself. -/
theorem higham9_12_sineMatrix_inverse_formula {n : ℕ} (hn : 0 < n) :
    IsLeftInverse n (higham9_12_sineMatrix n) (higham9_12_sineMatrix n) ∧
      IsRightInverse n (higham9_12_sineMatrix n) (higham9_12_sineMatrix n) := by
  exact ⟨fun i j => higham9_12_sineMatrix_mul_self hn i j,
    fun i j => higham9_12_sineMatrix_mul_self hn i j⟩

/-- **Problem 9.11 / equation (9.12)**, conditional theta lower bound.
If a matrix and the inverse candidate used in `theta(A) = 1/(alpha(A) beta(A))`
both have max-entry norm at most the sine-matrix scale `sqrt(2/(n+1))`, then
`theta(A) >= (n+1)/2`. -/
theorem higham9_12_theta_ge_half_succ_of_maxEntryNorm_le_scale {n : ℕ}
    (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hApos : 0 < maxEntryNorm hn A)
    (hAinvpos : 0 < maxEntryNorm hn A_inv)
    (hA_bound :
      maxEntryNorm hn A ≤ Real.sqrt (2 / ((n : ℝ) + 1)))
    (hAinv_bound :
      maxEntryNorm hn A_inv ≤ Real.sqrt (2 / ((n : ℝ) + 1))) :
    ((n : ℝ) + 1) / 2 ≤
      1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv) := by
  let c : ℝ := 2 / ((n : ℝ) + 1)
  have hn1_pos : 0 < (n : ℝ) + 1 := by positivity
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hA_bound' : maxEntryNorm hn A ≤ Real.sqrt c := by
    simpa [c] using hA_bound
  have hAinv_bound' : maxEntryNorm hn A_inv ≤ Real.sqrt c := by
    simpa [c] using hAinv_bound
  have hprod_le_sqrt :
      maxEntryNorm hn A * maxEntryNorm hn A_inv ≤
        Real.sqrt c * Real.sqrt c := by
    exact mul_le_mul hA_bound' hAinv_bound' (le_of_lt hAinvpos) (Real.sqrt_nonneg c)
  have hsqrt_mul : Real.sqrt c * Real.sqrt c = c := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hcpos)
  have hprod_le :
      maxEntryNorm hn A * maxEntryNorm hn A_inv ≤ c := by
    simpa [hsqrt_mul] using hprod_le_sqrt
  have hinv :
      c⁻¹ ≤ (maxEntryNorm hn A * maxEntryNorm hn A_inv)⁻¹ :=
    inv_anti₀ (mul_pos hApos hAinvpos) hprod_le
  have hhalf : ((n : ℝ) + 1) / 2 = 1 / c := by
    dsimp [c]
    field_simp [hn1_pos.ne']
  rw [hhalf]
  simpa [one_div] using hinv

/-- **Problem 9.11 / equation (9.12)**, the same conditional theta witness in
the doubled form used by the lower-bound consequence: `n + 1 <= 2*theta(A)`. -/
theorem higham9_12_two_theta_ge_succ_of_maxEntryNorm_le_scale {n : ℕ}
    (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hApos : 0 < maxEntryNorm hn A)
    (hAinvpos : 0 < maxEntryNorm hn A_inv)
    (hA_bound :
      maxEntryNorm hn A ≤ Real.sqrt (2 / ((n : ℝ) + 1)))
    (hAinv_bound :
      maxEntryNorm hn A_inv ≤ Real.sqrt (2 / ((n : ℝ) + 1))) :
    (n : ℝ) + 1 ≤
      2 * (1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv)) := by
  have hhalf :=
    higham9_12_theta_ge_half_succ_of_maxEntryNorm_le_scale hn A A_inv
      hApos hAinvpos hA_bound hAinv_bound
  linarith

/-- **Problem 9.11 / equation (9.12)**, theta arithmetic instantiated for the
sine witness as both matrix and inverse candidate.

This proves the source denominator bound from the entrywise scale and the
positive `(0,0)` entry; the self-inverse certificate is
`higham9_12_sineMatrix_inverse_formula`. -/
theorem higham9_12_sineMatrix_theta_candidate_ge_half_succ {n : ℕ}
    (hn : 0 < n) :
    ((n : ℝ) + 1) / 2 ≤
      1 / (maxEntryNorm hn (higham9_12_sineMatrix n) *
        maxEntryNorm hn (higham9_12_sineMatrix n)) := by
  exact higham9_12_theta_ge_half_succ_of_maxEntryNorm_le_scale hn
    (higham9_12_sineMatrix n) (higham9_12_sineMatrix n)
    (higham9_12_sineMatrix_maxEntryNorm_pos hn)
    (higham9_12_sineMatrix_maxEntryNorm_pos hn)
    (higham9_12_sineMatrix_maxEntryNorm_le_scale hn)
    (higham9_12_sineMatrix_maxEntryNorm_le_scale hn)

/-- **Problem 9.11 / equation (9.12)**, doubled theta arithmetic instantiated
for the sine witness as both matrix and inverse candidate. -/
theorem higham9_12_sineMatrix_two_theta_candidate_ge_succ {n : ℕ}
    (hn : 0 < n) :
    (n : ℝ) + 1 ≤
      2 * (1 / (maxEntryNorm hn (higham9_12_sineMatrix n) *
        maxEntryNorm hn (higham9_12_sineMatrix n))) := by
  have hhalf := higham9_12_sineMatrix_theta_candidate_ge_half_succ hn
  linarith

/-! ## Equation (9.13), Fourier/Vandermonde matrix lower-bound witness -/

/-- **Equation (9.13)**, the complex Vandermonde/Fourier matrix
`V_n = (exp(-2*pi*i*(r-1)*(s-1)/n))`.  The source's one-based indices are
represented by `r.val` and `s.val`, since `Fin` indices are zero-based.
The inverse formula `V_n^{-1} = n^{-1} V_nᴴ` and the resulting growth lower
bound is represented below by a scaled-adjoint two-sided inverse; the growth
lower bound remains a separate open target. -/
noncomputable def higham9_13_fourierVandermonde (n : ℕ) :
    Fin n → Fin n → ℂ :=
  fun r s =>
    Complex.exp
      ((((-2 : ℝ) * Real.pi * (r.val : ℝ) * (s.val : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I)

/-- **Equation (9.13)**, the Fourier/Vandermonde matrix is symmetric because
the exponent depends on the product `(r-1)*(s-1)`. -/
theorem higham9_13_fourierVandermonde_symm {n : ℕ} (r s : Fin n) :
    higham9_13_fourierVandermonde n r s =
      higham9_13_fourierVandermonde n s r := by
  unfold higham9_13_fourierVandermonde
  congr 2
  ring_nf

/-- **Equation (9.13)**, the first row of the Fourier/Vandermonde matrix is
identically `1`. -/
theorem higham9_13_fourierVandermonde_firstRow {n : ℕ} (hn : 0 < n)
    (s : Fin n) :
    higham9_13_fourierVandermonde n ⟨0, hn⟩ s = 1 := by
  simp [higham9_13_fourierVandermonde]

/-- **Equation (9.13)**, the first column of the Fourier/Vandermonde matrix is
identically `1`. -/
theorem higham9_13_fourierVandermonde_firstCol {n : ℕ} (hn : 0 < n)
    (r : Fin n) :
    higham9_13_fourierVandermonde n r ⟨0, hn⟩ = 1 := by
  simp [higham9_13_fourierVandermonde]

/-- **Equation (9.13)**, every Fourier/Vandermonde entry has complex norm
`1`. This is the unit-circle part of the roots-of-unity example, not the
complete inverse-formula or growth lower-bound argument by itself. -/
theorem higham9_13_fourierVandermonde_norm {n : ℕ} (r s : Fin n) :
    ‖higham9_13_fourierVandermonde n r s‖ = 1 := by
  unfold higham9_13_fourierVandermonde
  rw [Complex.norm_exp_ofReal_mul_I]

/-- **Equation (9.13)**, unit-circle entries give
`conj(v_rs) * v_rs = 1`.  This is the diagonal-entry part of the Fourier
orthogonality calculation, not the off-diagonal roots-of-unity cancellation. -/
theorem higham9_13_fourierVandermonde_conj_mul_self {n : ℕ} (r s : Fin n) :
    conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r s = 1 := by
  have hnormSq :
      Complex.normSq (higham9_13_fourierVandermonde n r s) = 1 := by
    rw [Complex.normSq_eq_norm_sq, higham9_13_fourierVandermonde_norm]
    norm_num
  have hmul := Complex.normSq_eq_conj_mul_self
    (z := higham9_13_fourierVandermonde n r s)
  rw [← hmul, hnormSq]
  norm_num

/-- **Equation (9.13)**, diagonal column Gram identity:
each Fourier/Vandermonde column has squared norm `n`.  This is the diagonal
part of the full Gram calculation below. -/
theorem higham9_13_fourierVandermonde_column_norm_sq {n : ℕ} (s : Fin n) :
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r s) = (n : ℂ) := by
  calc
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r s)
        = ∑ _r : Fin n, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro r _
          exact higham9_13_fourierVandermonde_conj_mul_self r s
    _ = (n : ℂ) := by simp

/-- **Equation (9.13)**, diagonal row Gram identity:
each Fourier/Vandermonde row has squared norm `n`. -/
theorem higham9_13_fourierVandermonde_row_norm_sq {n : ℕ} (r : Fin n) :
    (∑ s : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r s) = (n : ℂ) := by
  calc
    (∑ s : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r s)
        = ∑ _s : Fin n, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro s _
          exact higham9_13_fourierVandermonde_conj_mul_self r s
    _ = (n : ℂ) := by simp

/-- **Equation (9.13)**, the scalar Fourier root used for a nonzero column
difference has `n`th power `1`. -/
theorem higham9_13_fourierRoot_pow_card (n k : ℕ) (hn : 0 < n) :
    (Complex.exp (((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I))) ^ n = 1 := by
  rw [← Complex.exp_nat_mul]
  rw [show (n : ℂ) *
        ((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I) =
        (-(k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
          norm_num [Complex.ext_iff]
          field_simp [hnR]]
  simpa using Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))

/-- **Equation (9.13)**, a nonzero Fourier root with `0 < k < n` is not `1`.
This supplies the nontrivial denominator for the geometric-sum cancellation. -/
theorem higham9_13_fourierRoot_ne_one (n k : ℕ) (hn : 0 < n)
    (hkpos : 0 < k) (hklt : k < n) :
    Complex.exp (((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I)) ≠ 1 := by
  intro h
  have h' : Complex.exp (((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I)) = Complex.exp 0 := by
    simpa using h
  rw [Complex.exp_eq_exp_iff_exists_int] at h'
  rcases h' with ⟨m, hm⟩
  have him := congrArg Complex.im hm
  have hm_real : ((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ)) =
      (m : ℝ) * (2 * Real.pi) := by
    simpa [Complex.ext_iff, mul_assoc, mul_comm, mul_left_comm] using him
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hm_eq : (m : ℝ) = - (k : ℝ) / (n : ℝ) := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    field_simp [hnR, hpi] at hm_real ⊢
    nlinarith
  have hm_lt_zero : (m : ℝ) < 0 := by
    rw [hm_eq]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hnegk : - (k : ℝ) < 0 := by linarith
    exact div_neg_of_neg_of_pos hnegk hnRpos
  have hm_int_lt_zero : m < 0 := by
    exact_mod_cast hm_lt_zero
  have hm_le_neg_one : m ≤ -1 := by omega
  have hm_cast_le_neg_one : (m : ℝ) ≤ -1 := by
    exact_mod_cast hm_le_neg_one
  have hm_gt_neg_one : -1 < (m : ℝ) := by
    rw [hm_eq]
    have hkltR : (k : ℝ) < n := by exact_mod_cast hklt
    have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [lt_div_iff₀ hnRpos]
    nlinarith
  linarith

/-- **Equation (9.13)**, roots-of-unity cancellation for a nonzero column
difference. -/
theorem higham9_13_fourierRoot_geometric_sum_zero (n k : ℕ) (hn : 0 < n)
    (hkpos : 0 < k) (hklt : k < n) :
    (∑ r : Fin n,
      (Complex.exp (((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I))) ^ r.val) = 0 := by
  let ζ : ℂ :=
    Complex.exp (((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) *
      Complex.I))
  have hζpow : ζ ^ n = 1 := by
    simpa [ζ] using higham9_13_fourierRoot_pow_card n k hn
  have hζne : ζ ≠ 1 := by
    simpa [ζ] using higham9_13_fourierRoot_ne_one n k hn hkpos hklt
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ζ ^ i) n]
  have hgeom := geom_sum_eq hζne n
  rw [hζpow] at hgeom
  simpa [ζ, hζne] using hgeom

/-- **Equation (9.13)**, each off-diagonal column Gram term for ordered
columns is a power of the corresponding nontrivial Fourier root. -/
theorem higham9_13_fourierVandermonde_conj_mul_eq_pow_of_col_lt {n : ℕ}
    {s t : Fin n} (hst : s.val < t.val) (r : Fin n) :
    conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r t =
      (Complex.exp (((((-2 : ℝ) * Real.pi * ((t.val - s.val : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I))) ^ r.val := by
  unfold higham9_13_fourierVandermonde
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  have hsub : ((t.val - s.val : ℕ) : ℝ) = (t.val : ℝ) - (s.val : ℝ) := by
    exact Nat.cast_sub hst.le
  norm_num [Complex.ext_iff, hsub]
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le s.val) s.isLt)
  field_simp [hnR]
  ring

/-- **Equation (9.13)**, off-diagonal column orthogonality for ordered
columns of the Fourier/Vandermonde matrix. -/
theorem higham9_13_fourierVandermonde_column_orthogonal_of_lt {n : ℕ}
    {s t : Fin n} (hst : s.val < t.val) :
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r t) = 0 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le t.val) t.isLt
  have hkpos : 0 < t.val - s.val := Nat.sub_pos_of_lt hst
  have hklt : t.val - s.val < n :=
    lt_of_le_of_lt (Nat.sub_le t.val s.val) t.isLt
  calc
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r t)
        = ∑ r : Fin n,
            (Complex.exp (((((-2 : ℝ) * Real.pi *
                ((t.val - s.val : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ) *
              Complex.I))) ^ r.val := by
          apply Finset.sum_congr rfl
          intro r _
          exact higham9_13_fourierVandermonde_conj_mul_eq_pow_of_col_lt hst r
    _ = 0 := higham9_13_fourierRoot_geometric_sum_zero n (t.val - s.val) hn hkpos hklt

/-- **Equation (9.13)**, off-diagonal column orthogonality of the
Fourier/Vandermonde matrix.  Together with
`higham9_13_fourierVandermonde_column_norm_sq`, this is the column Gram
calculation behind the source inverse formula. -/
theorem higham9_13_fourierVandermonde_column_orthogonal {n : ℕ}
    {s t : Fin n} (hst : s ≠ t) :
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r t) = 0 := by
  have hval : s.val ≠ t.val := by
    intro h
    exact hst (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact higham9_13_fourierVandermonde_column_orthogonal_of_lt hlt
  · have hswap :=
      higham9_13_fourierVandermonde_column_orthogonal_of_lt (n := n) (s := t) (t := s) hgt
    calc
      (∑ r : Fin n,
        conj (higham9_13_fourierVandermonde n r s) *
          higham9_13_fourierVandermonde n r t)
          = conj (∑ r : Fin n,
              conj (higham9_13_fourierVandermonde n r t) *
                higham9_13_fourierVandermonde n r s) := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro r _
            simp [map_mul, mul_comm]
      _ = 0 := by simp [hswap]

/-- **Equation (9.13)**, the full column Gram calculation:
`V_n^H V_n` has diagonal entries `n` and off-diagonal entries `0`. -/
theorem higham9_13_fourierVandermonde_column_gram {n : ℕ} (s t : Fin n) :
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r t) =
      if s = t then (n : ℂ) else 0 := by
  by_cases hst : s = t
  · subst t
    simp [higham9_13_fourierVandermonde_column_norm_sq]
  · simp [hst, higham9_13_fourierVandermonde_column_orthogonal hst]

/-- **Equation (9.13)**, off-diagonal row orthogonality, derived from the
column calculation and symmetry of the Fourier/Vandermonde matrix. -/
theorem higham9_13_fourierVandermonde_row_orthogonal {n : ℕ}
    {r q : Fin n} (hrq : r ≠ q) :
    (∑ s : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n q s) = 0 := by
  calc
    (∑ s : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n q s)
        = ∑ s : Fin n,
            conj (higham9_13_fourierVandermonde n s r) *
              higham9_13_fourierVandermonde n s q := by
          apply Finset.sum_congr rfl
          intro s _
          rw [higham9_13_fourierVandermonde_symm r s,
            higham9_13_fourierVandermonde_symm q s]
    _ = 0 := higham9_13_fourierVandermonde_column_orthogonal hrq

/-- **Equation (9.13)**, the full row Gram calculation:
`V_n V_n^H` has diagonal entries `n` and off-diagonal entries `0`. -/
theorem higham9_13_fourierVandermonde_row_gram {n : ℕ} (r q : Fin n) :
    (∑ s : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n q s) =
      if r = q then (n : ℂ) else 0 := by
  by_cases hrq : r = q
  · subst q
    simp [higham9_13_fourierVandermonde_row_norm_sq]
  · simp [hrq, higham9_13_fourierVandermonde_row_orthogonal hrq]

/-- **Equation (9.13)**, the source inverse candidate `n^{-1} V_nᴴ`,
written entrywise with zero-based `Fin` indices. -/
noncomputable def higham9_13_fourierVandermondeScaledAdjoint (n : ℕ) :
    Fin n → Fin n → ℂ :=
  fun s r => ((n : ℂ)⁻¹) * conj (higham9_13_fourierVandermonde n r s)

/-- **Equation (9.13)**, the scaled adjoint is a left inverse of the
Fourier/Vandermonde matrix: `(n^{-1} V_nᴴ) V_n = I`. -/
theorem higham9_13_scaledAdjoint_mul_fourierVandermonde {n : ℕ} (s t : Fin n) :
    (∑ r : Fin n,
      higham9_13_fourierVandermondeScaledAdjoint n s r *
        higham9_13_fourierVandermonde n r t) =
      if s = t then 1 else 0 := by
  unfold higham9_13_fourierVandermondeScaledAdjoint
  calc
    (∑ r : Fin n,
      (((n : ℂ)⁻¹) * conj (higham9_13_fourierVandermonde n r s)) *
        higham9_13_fourierVandermonde n r t)
        = ((n : ℂ)⁻¹) * (∑ r : Fin n,
            conj (higham9_13_fourierVandermonde n r s) *
              higham9_13_fourierVandermonde n r t) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = ((n : ℂ)⁻¹) * (if s = t then (n : ℂ) else 0) := by
          rw [higham9_13_fourierVandermonde_column_gram]
    _ = if s = t then 1 else 0 := by
          by_cases hst : s = t
          · subst t
            have hnNat : n ≠ 0 :=
              Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le s.val) s.isLt)
            have hn : (n : ℂ) ≠ 0 := by exact_mod_cast hnNat
            simp [hn]
          · simp [hst]

/-- **Equation (9.13)**, the scaled adjoint is a right inverse of the
Fourier/Vandermonde matrix: `V_n (n^{-1} V_nᴴ) = I`. -/
theorem higham9_13_fourierVandermonde_mul_scaledAdjoint {n : ℕ} (r q : Fin n) :
    (∑ s : Fin n,
      higham9_13_fourierVandermonde n r s *
        higham9_13_fourierVandermondeScaledAdjoint n s q) =
      if r = q then 1 else 0 := by
  unfold higham9_13_fourierVandermondeScaledAdjoint
  calc
    (∑ s : Fin n,
      higham9_13_fourierVandermonde n r s *
        (((n : ℂ)⁻¹) * conj (higham9_13_fourierVandermonde n q s)))
        = ((n : ℂ)⁻¹) * (∑ s : Fin n,
            conj (higham9_13_fourierVandermonde n q s) *
              higham9_13_fourierVandermonde n r s) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ = ((n : ℂ)⁻¹) * (if q = r then (n : ℂ) else 0) := by
          rw [higham9_13_fourierVandermonde_row_gram]
    _ = if r = q then 1 else 0 := by
          by_cases hrq : r = q
          · subst q
            have hnNat : n ≠ 0 :=
              Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le r.val) r.isLt)
            have hn : (n : ℂ) ≠ 0 := by exact_mod_cast hnNat
            simp [hn]
          · have hqr : q ≠ r := fun h => hrq h.symm
            simp [hrq, hqr]

/-- **Equation (9.13)**, entrywise formalization of the source inverse formula
`V_n^{-1} = n^{-1} V_nᴴ`: the displayed scaled adjoint is both a left and a
right inverse of `V_n`. -/
theorem higham9_13_fourierVandermonde_inverse_formula (n : ℕ) :
    (∀ s t : Fin n,
      (∑ r : Fin n,
        higham9_13_fourierVandermondeScaledAdjoint n s r *
          higham9_13_fourierVandermonde n r t) =
        if s = t then 1 else 0) ∧
    (∀ r q : Fin n,
      (∑ s : Fin n,
        higham9_13_fourierVandermonde n r s *
          higham9_13_fourierVandermondeScaledAdjoint n s q) =
        if r = q then 1 else 0) := by
  exact ⟨higham9_13_scaledAdjoint_mul_fourierVandermonde,
    higham9_13_fourierVandermonde_mul_scaledAdjoint⟩

/-- **Equation (9.13)**, complex max-entry norm used for the
Fourier/Vandermonde lower-bound witness:
`max_{i,j} ‖A i j‖`.  The repository's standard Chapter 9 max-entry growth
factor is real-valued, so this local complex analogue records the source
quantity for the complex example without introducing a complex pivoting API. -/
noncomputable def higham9_13_complexMaxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℂ) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
      (fun j => ‖A i j‖))

/-- Every complex entry norm is bounded by
`higham9_13_complexMaxEntryNorm`. -/
lemma higham9_13_entry_norm_le_complexMaxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ higham9_13_complexMaxEntryNorm hn A := by
  apply le_trans
  · exact Finset.le_sup' (fun j => ‖A i j‖) (Finset.mem_univ j)
  · exact Finset.le_sup' (fun i => Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => ‖A i j‖))
      (Finset.mem_univ i)

/-- The complex max-entry norm is nonnegative. -/
lemma higham9_13_complexMaxEntryNorm_nonneg {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℂ) :
    0 ≤ higham9_13_complexMaxEntryNorm hn A := by
  let i0 : Fin n := ⟨0, hn⟩
  exact le_trans (norm_nonneg (A i0 i0))
    (higham9_13_entry_norm_le_complexMaxEntryNorm hn A i0 i0)

/-- Complex max-entry norm bound from a uniform entrywise norm bound. -/
lemma higham9_13_complexMaxEntryNorm_le_of_entry_le_bound {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℂ) (M : ℝ)
    (hentry : ∀ i j : Fin n, ‖A i j‖ ≤ M) :
    higham9_13_complexMaxEntryNorm hn A ≤ M := by
  unfold higham9_13_complexMaxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact hentry i j

/-- Complex max-entry norm monotonicity when every entry is bounded by another
matrix's complex max-entry norm, possibly at different indices. -/
lemma higham9_13_complexMaxEntryNorm_le_of_entry_le_max {n : ℕ}
    (hn : 0 < n) (A B : Fin n → Fin n → ℂ)
    (hentry : ∀ i j : Fin n, ‖A i j‖ ≤ higham9_13_complexMaxEntryNorm hn B) :
    higham9_13_complexMaxEntryNorm hn A ≤ higham9_13_complexMaxEntryNorm hn B :=
  higham9_13_complexMaxEntryNorm_le_of_entry_le_bound hn A
    (higham9_13_complexMaxEntryNorm hn B) hentry

/-- **Theorem 9.8 / equation (9.13)**, complex max-entry `theta <= n` core
estimate.  If a row of `A * A_inv` has diagonal entry `1`, then
`1 <= n * alpha(A) * beta(A)` with complex entry norms. -/
theorem higham9_13_inverse_row_identity_le_card_mul_complexMaxEntryNorm
    {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℂ) (i : Fin n)
    (hrow : ∑ j : Fin n, A i j * A_inv j i = 1) :
    1 ≤ (n : ℝ) * higham9_13_complexMaxEntryNorm hn A *
      higham9_13_complexMaxEntryNorm hn A_inv := by
  have h_norm :
      ‖∑ j : Fin n, A i j * A_inv j i‖ ≤
        ∑ j : Fin n, ‖A i j * A_inv j i‖ := by
    simpa using
      (norm_sum_le (s := (Finset.univ : Finset (Fin n)))
        (f := fun j : Fin n => A i j * A_inv j i))
  have h_terms : ∀ j : Fin n,
      ‖A i j * A_inv j i‖ ≤
        higham9_13_complexMaxEntryNorm hn A *
          higham9_13_complexMaxEntryNorm hn A_inv := by
    intro j
    rw [norm_mul]
    exact mul_le_mul
      (higham9_13_entry_norm_le_complexMaxEntryNorm hn A i j)
      (higham9_13_entry_norm_le_complexMaxEntryNorm hn A_inv j i)
      (norm_nonneg _)
      (le_trans (norm_nonneg _) (higham9_13_entry_norm_le_complexMaxEntryNorm hn A i j))
  have h_sum :
      ∑ j : Fin n, ‖A i j * A_inv j i‖ ≤
        ∑ _j : Fin n,
          higham9_13_complexMaxEntryNorm hn A *
            higham9_13_complexMaxEntryNorm hn A_inv :=
    Finset.sum_le_sum (fun j _ => h_terms j)
  calc
    1 = ‖∑ j : Fin n, A i j * A_inv j i‖ := by rw [hrow, norm_one]
    _ ≤ ∑ j : Fin n, ‖A i j * A_inv j i‖ := h_norm
    _ ≤ ∑ _j : Fin n,
          higham9_13_complexMaxEntryNorm hn A *
            higham9_13_complexMaxEntryNorm hn A_inv := h_sum
    _ = (n : ℝ) * higham9_13_complexMaxEntryNorm hn A *
          higham9_13_complexMaxEntryNorm hn A_inv := by
        simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- **Theorem 9.8 / equation (9.13)**, complex max-entry `theta <= n`.
This is the complex analogue of `higham9_8_theta_le_card_real`; the remaining
growth lower-bound rows still need the complete-pivoting trace/final-pivot
witness. -/
theorem higham9_8_theta_le_card_complex {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℂ) (i : Fin n)
    (hA : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hAinv : 0 < higham9_13_complexMaxEntryNorm hn A_inv)
    (hrow : ∑ j : Fin n, A i j * A_inv j i = 1) :
    1 / (higham9_13_complexMaxEntryNorm hn A *
      higham9_13_complexMaxEntryNorm hn A_inv) ≤ n := by
  have hmain :=
    higham9_13_inverse_row_identity_le_card_mul_complexMaxEntryNorm
      hn A A_inv i hrow
  have hprod :
      0 < higham9_13_complexMaxEntryNorm hn A *
        higham9_13_complexMaxEntryNorm hn A_inv :=
    mul_pos hA hAinv
  rw [div_le_iff₀ hprod]
  simpa [mul_assoc] using hmain

/-- **Equation (9.13)**, the Fourier/Vandermonde witness has
`max_{r,s} ‖(V_n)_{rs}‖ = 1`. -/
theorem higham9_13_fourierVandermonde_complexMaxEntryNorm_eq_one {n : ℕ}
    (hn : 0 < n) :
    higham9_13_complexMaxEntryNorm hn (higham9_13_fourierVandermonde n) = 1 := by
  apply le_antisymm
  · unfold higham9_13_complexMaxEntryNorm
    apply Finset.sup'_le
    intro r _
    apply Finset.sup'_le
    intro s _
    rw [higham9_13_fourierVandermonde_norm]
  · have hentry :=
      higham9_13_entry_norm_le_complexMaxEntryNorm hn
        (higham9_13_fourierVandermonde n) ⟨0, hn⟩ ⟨0, hn⟩
    simpa [higham9_13_fourierVandermonde_norm] using hentry

/-- **Equation (9.13)**, every entry of the scaled adjoint
`n⁻¹ V_nᴴ` has norm `1/n`. -/
theorem higham9_13_fourierVandermondeScaledAdjoint_norm {n : ℕ} (s r : Fin n) :
    ‖higham9_13_fourierVandermondeScaledAdjoint n s r‖ = ((n : ℝ)⁻¹) := by
  unfold higham9_13_fourierVandermondeScaledAdjoint
  rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_conj,
    higham9_13_fourierVandermonde_norm]
  ring

/-- **Equation (9.13)**, the inverse candidate `n⁻¹ V_nᴴ` has
`max_{r,s} ‖(n⁻¹ V_nᴴ)_{rs}‖ = 1/n`. -/
theorem higham9_13_fourierVandermondeScaledAdjoint_complexMaxEntryNorm_eq_inv
    {n : ℕ} (hn : 0 < n) :
    higham9_13_complexMaxEntryNorm hn
        (higham9_13_fourierVandermondeScaledAdjoint n) =
      ((n : ℝ)⁻¹) := by
  apply le_antisymm
  · unfold higham9_13_complexMaxEntryNorm
    apply Finset.sup'_le
    intro s _
    apply Finset.sup'_le
    intro r _
    rw [higham9_13_fourierVandermondeScaledAdjoint_norm]
  · have hentry :=
      higham9_13_entry_norm_le_complexMaxEntryNorm hn
        (higham9_13_fourierVandermondeScaledAdjoint n) ⟨0, hn⟩ ⟨0, hn⟩
    simpa [higham9_13_fourierVandermondeScaledAdjoint_norm] using hentry

/-- **Equation (9.13)**, the Fourier/Vandermonde witness has source theta
quantity exactly `n`: with `α = max |V_n| = 1` and
`β = max |V_n⁻¹| = 1/n`, `(αβ)⁻¹ = n`.  The separate pivoting/growth bridge
from this theta witness to `rho_n(V_n) >= n` remains recorded in the report. -/
theorem higham9_13_fourierVandermonde_theta_eq_card {n : ℕ} (hn : 0 < n) :
    1 /
        (higham9_13_complexMaxEntryNorm hn (higham9_13_fourierVandermonde n) *
          higham9_13_complexMaxEntryNorm hn
            (higham9_13_fourierVandermondeScaledAdjoint n)) =
      (n : ℝ) := by
  rw [higham9_13_fourierVandermonde_complexMaxEntryNorm_eq_one hn,
    higham9_13_fourierVandermondeScaledAdjoint_complexMaxEntryNorm_eq_inv hn]
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  field_simp [hnR]

/-- Complex max-entry growth factor for the source complex example in
Theorem 9.8/equation (9.13).  This mirrors `growthFactorEntry` using complex
entry norms and is kept local to the Fourier/Vandermonde lower-bound branch,
since the repository's main LU growth API is real-valued. -/
noncomputable def higham9_13_complexGrowthFactorEntry {n : ℕ} (hn : 0 < n)
    (A U : Fin n → Fin n → ℂ) : ℝ :=
  higham9_13_complexMaxEntryNorm hn U / higham9_13_complexMaxEntryNorm hn A

/-- **Theorem 9.8**, complex max-entry bridge `rho >= theta`.

If a final pivot `u` has inverse equal to an entry of a visible inverse
candidate and `u` is bounded by the largest entry reached by elimination, then
the complex max-entry growth factor is at least `(alpha beta)^{-1}`.  This is
the complex analogue of `growthFactorEntry_ge_inverse_entry_theta`; it does
not construct the complete-pivoting trace that supplies such a pivot witness. -/
theorem higham9_8_complexGrowthFactorEntry_ge_inverse_entry_theta {n : ℕ}
    (hn : 0 < n)
    (A A_inv U : Fin n → Fin n → ℂ)
    (hA : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hAinv : 0 < higham9_13_complexMaxEntryNorm hn A_inv)
    (u : ℂ) (hu_pos : 0 < ‖u‖)
    (hu_entry : ‖u‖ ≤ higham9_13_complexMaxEntryNorm hn U)
    (hu_inv_entry : ∃ i j : Fin n, u⁻¹ = A_inv i j) :
    1 / (higham9_13_complexMaxEntryNorm hn A *
      higham9_13_complexMaxEntryNorm hn A_inv) ≤
      higham9_13_complexGrowthFactorEntry hn A U := by
  obtain ⟨i, j, hu_inv_entry⟩ := hu_inv_entry
  have hu_inv_le :
      ‖u‖⁻¹ ≤ higham9_13_complexMaxEntryNorm hn A_inv := by
    calc
      ‖u‖⁻¹ = ‖u⁻¹‖ := by rw [norm_inv]
      _ = ‖A_inv i j‖ := by rw [hu_inv_entry]
      _ ≤ higham9_13_complexMaxEntryNorm hn A_inv :=
          higham9_13_entry_norm_le_complexMaxEntryNorm hn A_inv i j
  have hbeta_inv_le_u :
      (higham9_13_complexMaxEntryNorm hn A_inv)⁻¹ ≤ ‖u‖ :=
    inv_le_of_inv_le₀ hu_pos hu_inv_le
  have hbeta_inv_le_U :
      (higham9_13_complexMaxEntryNorm hn A_inv)⁻¹ ≤
        higham9_13_complexMaxEntryNorm hn U :=
    le_trans hbeta_inv_le_u hu_entry
  have hdiv :
      (higham9_13_complexMaxEntryNorm hn A_inv)⁻¹ /
          higham9_13_complexMaxEntryNorm hn A ≤
        higham9_13_complexMaxEntryNorm hn U /
          higham9_13_complexMaxEntryNorm hn A :=
    div_le_div_of_nonneg_right hbeta_inv_le_U (le_of_lt hA)
  have htheta :
      1 / (higham9_13_complexMaxEntryNorm hn A *
        higham9_13_complexMaxEntryNorm hn A_inv) =
        (higham9_13_complexMaxEntryNorm hn A_inv)⁻¹ /
          higham9_13_complexMaxEntryNorm hn A := by
    field_simp [ne_of_gt hA, ne_of_gt hAinv]
  calc
    1 / (higham9_13_complexMaxEntryNorm hn A *
        higham9_13_complexMaxEntryNorm hn A_inv)
        = (higham9_13_complexMaxEntryNorm hn A_inv)⁻¹ /
          higham9_13_complexMaxEntryNorm hn A := htheta
    _ ≤ higham9_13_complexMaxEntryNorm hn U /
          higham9_13_complexMaxEntryNorm hn A := hdiv
    _ = higham9_13_complexGrowthFactorEntry hn A U := rfl

/-- **Equation (9.13)**, Fourier/Vandermonde growth lower-bound bridge.

For the source matrix `V_n`, the already-proved theta identity turns the
complex Theorem 9.8 bridge into `n <= rho`, once a pivoting trace supplies a
final-pivot inverse-entry witness.  The later complete-pivoting construction
theorems discharge that witness for nonsingular inputs. -/
theorem higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card
    {n : ℕ} (hn : 0 < n)
    (U : Fin n → Fin n → ℂ) (u : ℂ)
    (hu_pos : 0 < ‖u‖)
    (hu_entry : ‖u‖ ≤ higham9_13_complexMaxEntryNorm hn U)
    (hu_inv_entry :
      ∃ i j : Fin n, u⁻¹ =
        higham9_13_fourierVandermondeScaledAdjoint n i j) :
    (n : ℝ) ≤
      higham9_13_complexGrowthFactorEntry hn
        (higham9_13_fourierVandermonde n) U := by
  have hA :
      0 < higham9_13_complexMaxEntryNorm hn
        (higham9_13_fourierVandermonde n) := by
    rw [higham9_13_fourierVandermonde_complexMaxEntryNorm_eq_one hn]
    norm_num
  have hAinv :
      0 < higham9_13_complexMaxEntryNorm hn
        (higham9_13_fourierVandermondeScaledAdjoint n) := by
    rw [higham9_13_fourierVandermondeScaledAdjoint_complexMaxEntryNorm_eq_inv hn]
    exact inv_pos.mpr (by exact_mod_cast hn)
  have htheta :=
    higham9_8_complexGrowthFactorEntry_ge_inverse_entry_theta hn
      (higham9_13_fourierVandermonde n)
      (higham9_13_fourierVandermondeScaledAdjoint n) U
      hA hAinv u hu_pos hu_entry hu_inv_entry
  rw [higham9_13_fourierVandermonde_theta_eq_card hn] at htheta
  exact htheta

/-- Complex right-inverse predicate for the local complex complete-pivoting
certificate branch of Theorem 9.8/equation (9.13). -/
def higham9_8_ComplexIsRightInverse (n : ℕ)
    (T T_inv : Fin n → Fin n → ℂ) : Prop :=
  ∀ i j : Fin n, ∑ k : Fin n, T i k * T_inv k j = if i = j then 1 else 0

/-- Complex left-inverse predicate for the local complex complete-pivoting
certificate branch of Theorem 9.8/equation (9.13). -/
def higham9_8_ComplexIsLeftInverse (n : ℕ)
    (T T_inv : Fin n → Fin n → ℂ) : Prop :=
  ∀ i j : Fin n, ∑ k : Fin n, T_inv i k * T k j = if i = j then 1 else 0

/-- Complex row/column permutation used for the certificate-level version of
equation (9.13). -/
def higham9_2_complexRowColPermutedMatrix {n : ℕ}
    (A : Fin n → Fin n → ℂ) (sigma tau : Fin n → Fin n) :
    Fin n → Fin n → ℂ :=
  fun i j => A (sigma i) (tau j)

/-- Complex transpose in the repository's function-shaped matrix style. -/
def higham9_8_complexFiniteTranspose {ι κ : Type*} (M : ι → κ → ℂ) :
    κ → ι → ℂ :=
  fun j i => M i j

/-- Complex LU certificate used only for the complex Fourier/Vandermonde
complete-pivoting bridge.  It mirrors the real `LUFactSpec` surface but avoids
claiming that the real-valued LU trace infrastructure has been generalized. -/
structure higham9_8_ComplexLUFactSpec (n : ℕ)
    (A L U : Fin n → Fin n → ℂ) : Prop where
  L_diag : ∀ i : Fin n, L i i = 1
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  product_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j

/-- Complex `PAQ = LU` certificate for equation (9.13).  This is a certificate
surface, not a construction of the complex complete-pivoting trace. -/
structure higham9_8_ComplexCompletePermutedLUFactSpec (n : ℕ)
    (A L U : Fin n → Fin n → ℂ) (sigma tau : Fin n → Fin n) : Prop where
  row_perm : IsPermutation n sigma
  col_perm : IsPermutation n tau
  L_diag : ∀ i : Fin n, L i i = 1
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  product_eq :
    ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j =
      higham9_2_complexRowColPermutedMatrix A sigma tau i j

/-- Complex complete-pivoting first-stage choice, ordered by complex entry
norms.  This is the complex analogue of `higham9_1_completePivotChoice` used
only for the equation (9.13) Fourier/Vandermonde branch. -/
def higham9_8_complexCompletePivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℂ) (k r s : Fin n) : Prop :=
  k.val ≤ r.val ∧ k.val ≤ s.val ∧
    ∀ i j : Fin n, k.val ≤ i.val → k.val ≤ j.val →
      ‖Astage i j‖ ≤ ‖Astage r s‖

/-- A complex complete-pivoting maximum exists on the finite active submatrix. -/
theorem higham9_8_exists_complexCompletePivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℂ) (k : Fin n) :
    ∃ r s : Fin n, higham9_8_complexCompletePivotChoice Astage k r s := by
  classical
  let active : Finset (Fin n × Fin n) :=
    Finset.univ.filter fun p => k.val ≤ p.1.val ∧ k.val ≤ p.2.val
  have hactive : active.Nonempty := by
    refine ⟨(k, k), ?_⟩
    simp [active]
  obtain ⟨p, hp_mem, hp_max⟩ :=
    Finset.exists_max_image active
      (fun p : Fin n × Fin n => ‖Astage p.1 p.2‖)
      hactive
  refine ⟨p.1, p.2, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hp_mem).2.1
  · exact (Finset.mem_filter.mp hp_mem).2.2
  · intro i j hi hj
    exact hp_max (i, j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), ⟨hi, hj⟩⟩)

/-- A complex complete-pivoting maximum is nonzero if the active submatrix
contains a nonzero entry. -/
theorem higham9_8_complexCompletePivotChoice_pivot_ne_zero_of_exists {n : ℕ}
    (Astage : Fin n → Fin n → ℂ) (k r s : Fin n)
    (hchoice : higham9_8_complexCompletePivotChoice Astage k r s)
    (hactive : ∃ i j : Fin n, k.val ≤ i.val ∧ k.val ≤ j.val ∧
      Astage i j ≠ 0) :
    Astage r s ≠ 0 := by
  rcases hactive with ⟨i, j, hi, hj, hne⟩
  intro hrs
  have hle : ‖Astage i j‖ ≤ 0 := by
    simpa [hrs] using hchoice.2.2 i j hi hj
  have hzero : ‖Astage i j‖ = 0 :=
    le_antisymm hle (norm_nonneg _)
  exact hne (norm_eq_zero.mp hzero)

/-- A complex active matrix with nonzero determinant has at least one nonzero
entry. -/
theorem higham9_8_complex_exists_entry_ne_zero_of_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0) :
    ∃ i j : Fin (m + 1), A i j ≠ 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hzero :
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = 0 := by
    ext i j
    exact hnone i j
  rw [hzero] at hdet
  have hdet_zero :
      Matrix.det (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = 0 := by
    rw [Matrix.det_zero]
    exact ⟨0⟩
  exact hdet hdet_zero

/-- A nonsingular complex matrix admits a nonzero first complete pivot. -/
theorem higham9_8_exists_first_complexCompletePivotChoice_pivot_ne_zero_of_det_ne_zero
    {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0) :
    ∃ r s : Fin (m + 1),
      higham9_8_complexCompletePivotChoice A 0 r s ∧ A r s ≠ 0 := by
  obtain ⟨i, j, hij⟩ :=
    higham9_8_complex_exists_entry_ne_zero_of_det_ne_zero A hdet
  obtain ⟨r, s, hchoice⟩ :=
    higham9_8_exists_complexCompletePivotChoice A 0
  exact ⟨r, s, hchoice,
    higham9_8_complexCompletePivotChoice_pivot_ne_zero_of_exists
      A 0 r s hchoice
      ⟨i, j, Nat.zero_le i.val, Nat.zero_le j.val, hij⟩⟩

/-- Complex first Schur complement after a no-pivot first step. -/
noncomputable def higham9_8_complexFirstSchurComplement {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ) :
    Fin m → Fin m → ℂ :=
  fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0

/-- Explicit complex lower factor for one exact no-pivot LU construction step. -/
noncomputable def higham9_8_complexLUFirstStepL {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (L₁ : Fin m → Fin m → ℂ) : Fin (m + 1) → Fin (m + 1) → ℂ :=
  fun i j =>
    if hi : i = 0 then
      if _hj : j = 0 then 1 else 0
    else
      if hj : j = 0 then A i 0 / A 0 0 else L₁ (i.pred hi) (j.pred hj)

/-- Explicit complex upper factor for one exact no-pivot LU construction step. -/
noncomputable def higham9_8_complexLUFirstStepU {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (U₁ : Fin m → Fin m → ℂ) : Fin (m + 1) → Fin (m + 1) → ℂ :=
  fun i j =>
    if hi : i = 0 then A 0 j
    else
      if hj : j = 0 then 0 else U₁ (i.pred hi) (j.pred hj)

/-- One exact complex no-pivot LU construction step. -/
theorem higham9_8_complexLUFactSpec_of_firstSchurComplement_explicit {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℂ}
    (hpivot : A 0 0 ≠ 0)
    {L₁ U₁ : Fin m → Fin m → ℂ}
    (hS :
      higham9_8_ComplexLUFactSpec m
        (higham9_8_complexFirstSchurComplement A) L₁ U₁) :
    higham9_8_ComplexLUFactSpec (m + 1) A
      (higham9_8_complexLUFirstStepL A L₁)
      (higham9_8_complexLUFirstStepU A U₁) := by
  classical
  let L : Fin (m + 1) → Fin (m + 1) → ℂ :=
    higham9_8_complexLUFirstStepL A L₁
  let U : Fin (m + 1) → Fin (m + 1) → ℂ :=
    higham9_8_complexLUFirstStepU A U₁
  change higham9_8_ComplexLUFactSpec (m + 1) A L U
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      simp [L, higham9_8_complexLUFirstStepL]
    · simp [L, higham9_8_complexLUFirstStepL, hi, hS.L_diag]
  · intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := by
        intro h
        subst h
        exact (Nat.lt_irrefl 0 hij).elim
      simp [L, higham9_8_complexLUFirstStepL, hj]
    · have hj : j ≠ 0 := by
        intro h
        subst h
        exact (Nat.not_lt_zero _ hij).elim
      simp only [L, higham9_8_complexLUFirstStepL, dif_neg hi, dif_neg hj]
      exact hS.L_upper_zero (i.pred hi) (j.pred hj) (by
        have hival := Fin.val_pred i hi
        have hjval := Fin.val_pred j hj
        have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
        have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
        omega)
  · intro i j hij
    by_cases hi : i = 0
    · subst hi
      exact (Nat.not_lt_zero _ hij).elim
    · by_cases hj : j = 0
      · subst hj
        simp [U, higham9_8_complexLUFirstStepU, hi]
      · simp only [U, higham9_8_complexLUFirstStepU, dif_neg hi, dif_neg hj]
        exact hS.U_lower_zero (i.pred hi) (j.pred hj) (by
          have hival := Fin.val_pred i hi
          have hjval := Fin.val_pred j hj
          have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
          have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
  · intro i j
    rw [Fin.sum_univ_succ]
    have hL0 : ∀ p : Fin (m + 1), L 0 p = if p = 0 then 1 else 0 := by
      intro p
      simp [L, higham9_8_complexLUFirstStepL]
    have hU0 : ∀ p : Fin (m + 1), U 0 p = A 0 p := by
      intro p
      simp [U, higham9_8_complexLUFirstStepU]
    have hL0s : ∀ k : Fin m, L 0 k.succ = 0 := by
      intro k
      rw [hL0]
      simp [Fin.succ_ne_zero]
    have hLs0 : ∀ k : Fin m, L k.succ 0 = A k.succ 0 / A 0 0 := by
      intro k
      simp [L, higham9_8_complexLUFirstStepL, Fin.succ_ne_zero]
    have hUs0 : ∀ k : Fin m, U k.succ 0 = 0 := by
      intro k
      simp [U, higham9_8_complexLUFirstStepU, Fin.succ_ne_zero]
    have hLss : ∀ p q : Fin m, L p.succ q.succ = L₁ p q := by
      intro p q
      simp [L, higham9_8_complexLUFirstStepL, Fin.succ_ne_zero, Fin.pred_succ]
    have hUss : ∀ p q : Fin m, U p.succ q.succ = U₁ p q := by
      intro p q
      simp [U, higham9_8_complexLUFirstStepU, Fin.succ_ne_zero, Fin.pred_succ]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi
      subst hj
      rw [hL0 0, hU0 0]
      have hzero :
          (∑ x : Fin m, L 0 x.succ * U x.succ 0) = 0 := by
        simp [hL0s]
      rw [hzero]
      simp
    · subst hi
      rw [hL0 0, hU0 j]
      have hzero :
          (∑ x : Fin m, L 0 x.succ * U x.succ j) = 0 := by
        simp [hL0s]
      rw [hzero]
      simp
    · subst hj
      rw [hU0 0]
      have hzero :
          (∑ x : Fin m, L i x.succ * U x.succ 0) = 0 := by
        simp [hUs0]
      have hLi0 : L i 0 = A i 0 / A 0 0 := by
        have h := hLs0 (i.pred hi)
        simpa [Fin.succ_pred i hi] using h
      rw [hzero, hLi0]
      field_simp [hpivot]
      ring
    · rw [hU0 j]
      have hprod := hS.product_eq (i.pred hi) (j.pred hj)
      have hsucc :
          (∑ x : Fin m, L i x.succ * U x.succ j) =
            ∑ x : Fin m, L₁ (i.pred hi) x * U₁ x (j.pred hj) := by
        apply Finset.sum_congr rfl
        intro x _
        have hLix : L i x.succ = L₁ (i.pred hi) x := by
          have h := hLss (i.pred hi) x
          simpa [Fin.succ_pred i hi] using h
        have hUxj : U x.succ j = U₁ x (j.pred hj) := by
          have h := hUss x (j.pred hj)
          simpa [Fin.succ_pred j hj] using h
        rw [hLix, hUxj]
      have hLi0 : L i 0 = A i 0 / A 0 0 := by
        have h := hLs0 (i.pred hi)
        simpa [Fin.succ_pred i hi] using h
      rw [hLi0, hsucc, hprod]
      simp only [higham9_8_complexFirstSchurComplement, Fin.succ_pred]
      field_simp [hpivot]
      ring

/-- Complex row/column swaps moving a first complete pivot to `(0,0)` preserve
nonsingularity. -/
theorem higham9_8_complex_firstPivotRowColSwap_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (r s : Fin (m + 1))
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0) :
    Matrix.det
      (Matrix.of
        (higham9_2_complexRowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r)
          (higham9_7_firstPivotRowSwap s)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0 := by
  classical
  let sigma := higham9_7_firstPivotRowSwap r
  let tau := higham9_7_firstPivotRowSwap s
  let B : Fin (m + 1) → Fin (m + 1) → ℂ := fun i j => A (sigma i) j
  have hB_det :
      Matrix.det (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0 := by
    let e : Equiv.Perm (Fin (m + 1)) :=
      Equiv.ofBijective sigma (higham9_7_firstPivotRowSwap_isPermutation r)
    have hdet_eq :
        Matrix.det (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
          ((Equiv.Perm.sign e : ℤ) : ℂ) *
            Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
      have hperm :=
        Matrix.det_permute (R := ℂ) e
          (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
      simpa [B, e, sigma, Matrix.of_apply] using hperm
    rw [hdet_eq]
    exact mul_ne_zero (by simp) hdet
  let eTau : Equiv.Perm (Fin (m + 1)) :=
    Equiv.ofBijective tau (higham9_7_firstPivotRowSwap_isPermutation s)
  have hdet_eq :
      Matrix.det
        (Matrix.of
          (higham9_2_complexRowColPermutedMatrix A sigma tau) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
        ((Equiv.Perm.sign eTau : ℤ) : ℂ) *
          Matrix.det (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    have hperm :=
      Matrix.det_permute' eTau
        (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    simpa [B, sigma, tau, eTau, higham9_2_complexRowColPermutedMatrix,
      Matrix.of_apply] using hperm
  rw [hdet_eq]
  exact mul_ne_zero (by simp) hB_det

/-- If a complex matrix is nonsingular and its leading pivot is nonzero, then
the first Schur complement is nonsingular. -/
theorem higham9_8_complexFirstSchurComplement_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (hpivot : A 0 0 ≠ 0)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham9_8_complexFirstSchurComplement A) :
        Matrix (Fin m) (Fin m) ℂ) ≠ 0 := by
  classical
  let A11 : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => A 0 0
  let B : Matrix (Fin 1) (Fin m) ℂ := fun _ c => A 0 c.succ
  let C : Matrix (Fin m) (Fin 1) ℂ := fun r _ => A r.succ 0
  let D : Matrix (Fin m) (Fin m) ℂ := fun r c => A r.succ c.succ
  have hdetA11 : Matrix.det A11 = A 0 0 := by
    simp [A11]
  have hdetA11_ne : Matrix.det A11 ≠ 0 := by
    simpa [hdetA11] using hpivot
  letI : Invertible (Matrix.det A11) := invertibleOfNonzero hdetA11_ne
  letI : Invertible A11 := Matrix.invertibleOfDetInvertible A11
  have hA11_inv : ⅟A11 = (fun _ _ : Fin 1 => (A 0 0)⁻¹) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [A11]
  have hschur :
      Matrix.det (Matrix.fromBlocks A11 B C D) =
        A 0 0 *
          Matrix.det
            (Matrix.of (higham9_8_complexFirstSchurComplement A) :
              Matrix (Fin m) (Fin m) ℂ) := by
    rw [Matrix.det_fromBlocks₁₁, hdetA11]
    congr 1
    apply congrArg Matrix.det
    ext r c
    simp [A11, B, C, D, hA11_inv, higham9_8_complexFirstSchurComplement,
      Matrix.mul_apply]
    rw [div_eq_mul_inv]
    ring_nf
  have hdetBlock :
      Matrix.det (Matrix.fromBlocks A11 B C D) =
        Matrix.det ((Matrix.fromBlocks A11 B C D).submatrix
          (finSumFinEquiv.symm : Fin (1 + m) ≃ Fin 1 ⊕ Fin m)
          (finSumFinEquiv.symm : Fin (1 + m) ≃ Fin 1 ⊕ Fin m)) :=
    (Matrix.det_submatrix_equiv_self
      (finSumFinEquiv.symm : Fin (1 + m) ≃ Fin 1 ⊕ Fin m)
      (Matrix.fromBlocks A11 B C D)).symm
  have hsub :
      (Matrix.fromBlocks A11 B C D).submatrix
          (finSumFinEquiv.symm : Fin (1 + m) ≃ Fin 1 ⊕ Fin m)
          (finSumFinEquiv.symm : Fin (1 + m) ≃ Fin 1 ⊕ Fin m) =
        (Matrix.of (fun i j : Fin (1 + m) =>
          A (finCongr (Nat.add_comm 1 m) i)
            (finCongr (Nat.add_comm 1 m) j)) :
          Matrix (Fin (1 + m)) (Fin (1 + m)) ℂ) := by
    have hcast_zero :
        finCongr (Nat.add_comm 1 m) (Fin.castAdd m (0 : Fin 1)) =
          (0 : Fin (m + 1)) := by
      ext
      simp
    have hcast_zero' :
        Fin.cast (Nat.add_comm 1 m) (Fin.castAdd m (0 : Fin 1)) =
          (0 : Fin (m + 1)) := by
      ext
      simp [Fin.cast]
    ext r c
    cases r using Fin.addCases with
    | left r0 =>
        fin_cases r0
        cases c using Fin.addCases with
        | left c0 =>
            fin_cases c0
            simp [A11, B, C, D]
            rw [hcast_zero']
        | right c0 =>
            simp [A11, B, C, D]
            rw [hcast_zero']
    | right r0 =>
        cases c using Fin.addCases with
        | left c0 =>
            fin_cases c0
            simp [A11, B, C, D]
            rw [hcast_zero']
        | right c0 =>
            simp [A11, B, C, D]
  have hdetA_eq :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
        A 0 0 *
          Matrix.det
            (Matrix.of (higham9_8_complexFirstSchurComplement A) :
              Matrix (Fin m) (Fin m) ℂ) := by
    calc
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
          =
        Matrix.det
          (Matrix.of (fun i j : Fin (1 + m) =>
            A (finCongr (Nat.add_comm 1 m) i)
              (finCongr (Nat.add_comm 1 m) j)) :
            Matrix (Fin (1 + m)) (Fin (1 + m)) ℂ) := by
            change
              Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
                Matrix.det
                  ((Matrix.of A :
                    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix
                    (finCongr (Nat.add_comm 1 m) : Fin (1 + m) ≃ Fin (m + 1))
                    (finCongr (Nat.add_comm 1 m) : Fin (1 + m) ≃ Fin (m + 1)))
            exact
              (Matrix.det_submatrix_equiv_self
                (finCongr (Nat.add_comm 1 m) : Fin (1 + m) ≃ Fin (m + 1))
                (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).symm
      _ = Matrix.det (Matrix.fromBlocks A11 B C D) := by
            rw [← hsub, ← hdetBlock]
      _ = A 0 0 *
          Matrix.det
            (Matrix.of (higham9_8_complexFirstSchurComplement A) :
              Matrix (Fin m) (Fin m) ℂ) := hschur
  intro hSzero
  apply hdet
  rw [hdetA_eq, hSzero, mul_zero]

/-- A complex `PAQ = LU` certificate is an ordinary complex LU certificate for
the row-and-column permuted matrix. -/
theorem higham9_8_complexCompletePermutedLUFactSpec_to_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℂ} {sigma tau : Fin n → Fin n}
    (hLU : higham9_8_ComplexCompletePermutedLUFactSpec n A L U sigma tau) :
    higham9_8_ComplexLUFactSpec n
      (higham9_2_complexRowColPermutedMatrix A sigma tau) L U where
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  product_eq := hLU.product_eq

/-- Complex right-inverse transport through row and column permutations. -/
theorem higham9_2_complexRowColPermutedMatrix_right_inverse {n : ℕ}
    {A A_inv : Fin n → Fin n → ℂ} {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) (htau : IsPermutation n tau)
    (hRight : higham9_8_ComplexIsRightInverse n A A_inv) :
    higham9_8_ComplexIsRightInverse n
      (higham9_2_complexRowColPermutedMatrix A sigma tau)
      (fun i j => A_inv (tau i) (sigma j)) := by
  classical
  intro i j
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau htau
  have hsum :
      (∑ k : Fin n, A (sigma i) (tau k) * A_inv (tau k) (sigma j)) =
        ∑ k : Fin n, A (sigma i) k * A_inv k (sigma j) := by
    simpa [eTau] using
      (Equiv.sum_comp eTau
        (fun k : Fin n => A (sigma i) k * A_inv k (sigma j)))
  calc
    ∑ k : Fin n,
        higham9_2_complexRowColPermutedMatrix A sigma tau i k *
          (fun i j => A_inv (tau i) (sigma j)) k j
        = ∑ k : Fin n, A (sigma i) (tau k) * A_inv (tau k) (sigma j) := by
            simp [higham9_2_complexRowColPermutedMatrix]
    _ = ∑ k : Fin n, A (sigma i) k * A_inv k (sigma j) := hsum
    _ = (if sigma i = sigma j then (1 : ℂ) else 0) := hRight (sigma i) (sigma j)
    _ = (if i = j then (1 : ℂ) else 0) := by
      by_cases hij : i = j
      · simp [hij]
      · have hsne : sigma i ≠ sigma j := by
          intro hs
          exact hij (hsigma.injective hs)
        simp [hij, hsne]

/-- Transposing a complex right inverse gives a complex left inverse. -/
theorem higham9_8_complex_isLeftInverse_finiteTranspose_of_isRightInverse {n : ℕ}
    {T T_inv : Fin n → Fin n → ℂ}
    (hInv : higham9_8_ComplexIsRightInverse n T T_inv) :
    higham9_8_ComplexIsLeftInverse n
      (higham9_8_complexFiniteTranspose T)
      (higham9_8_complexFiniteTranspose T_inv) := by
  intro i j
  have h := hInv j i
  calc
    ∑ k : Fin n,
        higham9_8_complexFiniteTranspose T_inv i k *
          higham9_8_complexFiniteTranspose T k j
        = ∑ k : Fin n, T j k * T_inv k i := by
            apply Finset.sum_congr rfl
            intro k _
            simp [higham9_8_complexFiniteTranspose, mul_comm]
    _ = if j = i then 1 else 0 := h
    _ = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · simp [hij]
      · have hji : j ≠ i := by exact fun h => hij h.symm
        simp [hij, hji]

/-- The left inverse of a complex upper triangular matrix is upper triangular.
This local complex analogue supports the equation (9.13) final-pivot bridge. -/
theorem higham9_8_complex_inv_upper_tri (n : ℕ)
    (U U_inv : Fin n → Fin n → ℂ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : higham9_8_ComplexIsLeftInverse n U U_inv) :
    ∀ i j : Fin n, j.val < i.val → U_inv i j = 0 := by
  suffices ∀ (jv : ℕ) (hjv : jv < n), ∀ i : Fin n, jv < i.val →
      U_inv i ⟨jv, hjv⟩ = 0 by
    intro i j hij
    exact this j.val j.isLt i hij
  intro jv hjv i hi
  revert hjv i
  refine Nat.strongRecOn jv ?_
  intro jv ih hjv i hi
  let j : Fin n := ⟨jv, hjv⟩
  have hij : i ≠ j := Fin.ne_of_val_ne (by simp [j]; omega)
  have h := hInv i j
  simp [hij] at h
  have hterm : U_inv i j * U j j = 0 := by
    suffices ∑ k : Fin n, U_inv i k * U k j = U_inv i j * U j j by
      simpa [this] using h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hzero :
        ∑ k ∈ Finset.univ.erase j, U_inv i k * U k j = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk_ne := Finset.ne_of_mem_erase hk
      by_cases hklt : k.val < jv
      · have hki : k.val < i.val := by omega
        rw [ih k.val hklt k.isLt i hki, zero_mul]
      · push_neg at hklt
        have hjk : jv < k.val := by
          by_contra hc
          push_neg at hc
          have hval : k.val = jv := le_antisymm hc hklt
          exact hk_ne (Fin.ext (by simp [j, hval]))
        rw [hUT k j (by simpa [j] using hjk), mul_zero]
    simp [hzero]
  exact (mul_eq_zero.mp hterm).elim id (fun hdiag => absurd hdiag (hU_diag j))

/-- Diagonal entries of a complex upper-triangular inverse. -/
theorem higham9_8_complex_inv_diag_entry (n : ℕ)
    (U U_inv : Fin n → Fin n → ℂ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : higham9_8_ComplexIsLeftInverse n U U_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → U_inv i j = 0) :
    ∀ i : Fin n, U_inv i i = 1 / U i i := by
  intro i
  have h := hInv i i
  simp at h
  have honly : ∑ k : Fin n, U_inv i k * U k i = U_inv i i * U i i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hzero :
        ∑ k ∈ Finset.univ.erase i, U_inv i k * U k i = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hlt : k.val < i.val
      · rw [hInv_ut i k hlt, zero_mul]
      · push_neg at hlt
        have hk_ne := Finset.ne_of_mem_erase hk
        have hik : i.val < k.val := by
          exact lt_of_le_of_ne hlt (fun hval => hk_ne (Fin.ext hval.symm))
        rw [hUT k i hik, mul_zero]
    simp [hzero]
  rw [honly] at h
  have hmul : U_inv i i * U i i = 1 := h
  field_simp [hU_diag i] at hmul ⊢
  simpa [div_eq_mul_inv, mul_comm] using hmul

/-- Complex final-pivot identity for an exact no-pivot LU certificate. -/
theorem higham9_8_complex_finalPivot_mul_inverse_entry_eq_one {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℂ)
    (hLU : higham9_8_ComplexLUFactSpec (m + 1) A L U)
    (hRight : higham9_8_ComplexIsRightInverse (m + 1) A A_inv) :
    U (Fin.last m) (Fin.last m) *
      A_inv (Fin.last m) (Fin.last m) = 1 := by
  classical
  let n := m + 1
  let last : Fin n := Fin.last m
  let Y : Fin n → Fin n → ℂ := fun i j => ∑ k : Fin n, U i k * A_inv k j
  have hYRight : higham9_8_ComplexIsRightInverse n L Y := by
    intro i j
    have hassoc :
        ∑ k : Fin n, L i k * Y k j =
          ∑ k : Fin n, A i k * A_inv k j := by
      calc
        ∑ k : Fin n, L i k * Y k j
            = ∑ k : Fin n, ∑ l : Fin n, L i k * (U k l * A_inv l j) := by
                apply Finset.sum_congr rfl
                intro k _
                simp [Y, Finset.mul_sum]
        _ = ∑ l : Fin n, ∑ k : Fin n, L i k * (U k l * A_inv l j) := by
              exact Finset.sum_comm
        _ = ∑ l : Fin n, (∑ k : Fin n, L i k * U k l) * A_inv l j := by
              apply Finset.sum_congr rfl
              intro l _
              calc
                ∑ k : Fin n, L i k * (U k l * A_inv l j)
                    = ∑ k : Fin n, (L i k * U k l) * A_inv l j := by
                        apply Finset.sum_congr rfl
                        intro k _
                        ring
                _ = (∑ k : Fin n, L i k * U k l) * A_inv l j := by
                        rw [Finset.sum_mul]
        _ = ∑ l : Fin n, A i l * A_inv l j := by
              apply Finset.sum_congr rfl
              intro l _
              rw [hLU.product_eq i l]
    calc
      ∑ k : Fin n, L i k * Y k j
          = ∑ k : Fin n, A i k * A_inv k j := hassoc
      _ = if i = j then 1 else 0 := hRight i j
  have hLT_transpose :
      ∀ i j : Fin n, j.val < i.val →
        higham9_8_complexFiniteTranspose L i j = 0 := by
    intro i j hji
    exact hLU.L_upper_zero j i (by simpa [higham9_8_complexFiniteTranspose] using hji)
  have hL_diag_ne :
      ∀ i : Fin n, higham9_8_complexFiniteTranspose L i i ≠ 0 := by
    intro i
    simp [higham9_8_complexFiniteTranspose, hLU.L_diag i]
  have hYLeftT :
      higham9_8_ComplexIsLeftInverse n
        (higham9_8_complexFiniteTranspose L)
        (higham9_8_complexFiniteTranspose Y) :=
    higham9_8_complex_isLeftInverse_finiteTranspose_of_isRightInverse hYRight
  have hYt_upper :
      ∀ i j : Fin n, j.val < i.val →
        higham9_8_complexFiniteTranspose Y i j = 0 :=
    higham9_8_complex_inv_upper_tri n
      (higham9_8_complexFiniteTranspose L)
      (higham9_8_complexFiniteTranspose Y)
      hLT_transpose hL_diag_ne hYLeftT
  have hYt_diag :
      ∀ i : Fin n, higham9_8_complexFiniteTranspose Y i i =
        1 / higham9_8_complexFiniteTranspose L i i :=
    higham9_8_complex_inv_diag_entry n
      (higham9_8_complexFiniteTranspose L)
      (higham9_8_complexFiniteTranspose Y)
      hLT_transpose hL_diag_ne hYLeftT hYt_upper
  have hY_last_diag : Y last last = 1 := by
    have h := hYt_diag last
    simpa [higham9_8_complexFiniteTranspose, hLU.L_diag last] using h
  have hY_last_last :
      Y last last =
        U last last * A_inv last last := by
    unfold Y
    exact Finset.sum_eq_single last
      (fun k _ hk => by
        have hk_val_ne : k.val ≠ last.val := by
          intro hval
          exact hk (Fin.ext hval)
        have hk_lt : k.val < last.val := by
          have hlast_val : last.val = m := by simp [last]
          have hk_le : k.val ≤ m := Nat.le_of_lt_succ k.isLt
          have hk_ne_m : k.val ≠ m := by
            intro hkm
            exact hk_val_ne (by simpa [hlast_val] using hkm)
          have hk_lt_m : k.val < m := lt_of_le_of_ne hk_le hk_ne_m
          simpa [hlast_val] using hk_lt_m
        rw [hLU.U_lower_zero last k (by simpa [last] using hk_lt), zero_mul])
      (fun hnot => (hnot (Finset.mem_univ last)).elim)
  rw [hY_last_last] at hY_last_diag
  exact hY_last_diag

/-- Complex final-pivot inverse-entry identity for an explicit complex
complete-pivoting certificate `P A Q = L U`. -/
theorem higham9_8_complex_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec
    {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℂ)
    (sigma tau : Fin (m + 1) → Fin (m + 1))
    (hLU :
      higham9_8_ComplexCompletePermutedLUFactSpec (m + 1) A L U sigma tau)
    (hRight : higham9_8_ComplexIsRightInverse (m + 1) A A_inv) :
    U (Fin.last m) (Fin.last m) *
      A_inv (tau (Fin.last m)) (sigma (Fin.last m)) = 1 := by
  classical
  let B : Fin (m + 1) → Fin (m + 1) → ℂ :=
    higham9_2_complexRowColPermutedMatrix A sigma tau
  let B_inv : Fin (m + 1) → Fin (m + 1) → ℂ :=
    fun i j => A_inv (tau i) (sigma j)
  have hBRight : higham9_8_ComplexIsRightInverse (m + 1) B B_inv :=
    higham9_2_complexRowColPermutedMatrix_right_inverse hLU.row_perm hLU.col_perm hRight
  have hBLU : higham9_8_ComplexLUFactSpec (m + 1) B L U :=
    higham9_8_complexCompletePermutedLUFactSpec_to_LUFactSpec hLU
  simpa [B, B_inv] using
    higham9_8_complex_finalPivot_mul_inverse_entry_eq_one B B_inv L U hBLU hBRight

/-- **Equation (9.13)**, Fourier/Vandermonde growth lower bound from an
explicit complex complete-pivoting certificate.

This removes the final-pivot inverse-entry witness hypothesis from
`higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card`; it still does
not itself construct the complex complete-pivoting trace or certificate; those
are supplied by the later existence theorems. -/
theorem higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card_of_completePermutedLUFactSpec
    {n : ℕ} (hn : 0 < n)
    (L U : Fin n → Fin n → ℂ) (sigma tau : Fin n → Fin n)
    (hLU :
      higham9_8_ComplexCompletePermutedLUFactSpec n
        (higham9_13_fourierVandermonde n) L U sigma tau) :
    (n : ℝ) ≤
      higham9_13_complexGrowthFactorEntry hn
        (higham9_13_fourierVandermonde n) U := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero 0 hn).elim
  | succ m =>
      let V : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_13_fourierVandermonde (m + 1)
      let V_inv : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_13_fourierVandermondeScaledAdjoint (m + 1)
      have hRight : higham9_8_ComplexIsRightInverse (m + 1) V V_inv := by
        exact (higham9_13_fourierVandermonde_inverse_formula (m + 1)).2
      let last : Fin (m + 1) := Fin.last m
      let u : ℂ := U last last
      have hprod :
          u * V_inv (tau last) (sigma last) = 1 := by
        simpa [u, V, V_inv, last] using
          higham9_8_complex_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec
            V V_inv L U sigma tau hLU hRight
      have hu_ne : u ≠ 0 := by
        intro hu
        rw [hu] at hprod
        norm_num at hprod
      have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
      have hu_entry :
          ‖u‖ ≤ higham9_13_complexMaxEntryNorm (Nat.succ_pos m) U := by
        simpa [u, last] using
          higham9_13_entry_norm_le_complexMaxEntryNorm
            (Nat.succ_pos m) U last last
      have hentry_eq : u⁻¹ = V_inv (tau last) (sigma last) := by
        exact (eq_inv_of_mul_eq_one_right hprod).symm
      have hu_inv_entry :
          ∃ i j : Fin (m + 1), u⁻¹ = V_inv i j :=
        ⟨tau last, sigma last, hentry_eq⟩
      simpa [V, V_inv] using
        higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card
          (Nat.succ_pos m) U u hu_pos hu_entry hu_inv_entry

/-! ## Problem 9.11, block doubling for complete-pivoting lower bounds -/

/-- **Problem 9.11**, the doubled block matrix
`B = [[A, A], [A, -A]]`, represented as a `2 × 2` block matrix. -/
def higham9_11_blockMatrix {n : ℕ} (A : Fin n → Fin n → ℝ) :
    Fin 2 → Fin 2 → (Fin n → Fin n → ℝ) :=
  fun bi bj i j => if bi = (1 : Fin 2) ∧ bj = (1 : Fin 2) then -A i j else A i j

/-- **Problem 9.11**, the displayed inverse candidate
`(1/2) [[A⁻¹, A⁻¹], [A⁻¹, -A⁻¹]]`. -/
noncomputable def higham9_11_blockInverseCandidate {n : ℕ} (A_inv : Fin n → Fin n → ℝ) :
    Fin 2 → Fin 2 → (Fin n → Fin n → ℝ) :=
  fun bi bj i j => (1 / 2 : ℝ) * higham9_11_blockMatrix A_inv bi bj i j

/-- Row/column block selector for flattening a `2 × 2` block matrix with
`n × n` blocks into an ordinary `(2n) × (2n)` matrix. -/
def higham9_11_flatBlockIndex {n : ℕ} (i : Fin (2 * n)) : Fin 2 :=
  if i.val < n then 0 else 1

/-- Intra-block row/column selector for flattening a `2 × 2` block matrix with
`n × n` blocks into an ordinary `(2n) × (2n)` matrix. -/
def higham9_11_flatInnerIndex {n : ℕ} (_hn : 0 < n) (i : Fin (2 * n)) : Fin n :=
  if hi : i.val < n then
    ⟨i.val, hi⟩
  else
    ⟨i.val - n, by
      have hi_lt : i.val < 2 * n := i.isLt
      have hni : n ≤ i.val := le_of_not_gt hi
      omega⟩

/-- **Problem 9.11**, flatten the displayed `2 × 2` block matrix into the
ordinary `Fin (2n)` matrix surface used by the complete-pivoting growth
family. -/
def higham9_11_flattenTwoBlock {n : ℕ} (hn : 0 < n)
    (B : Fin 2 → Fin 2 → (Fin n → Fin n → ℝ)) :
    Fin (2 * n) → Fin (2 * n) → ℝ :=
  fun i j =>
    B (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j)
      (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn j)

/-- Inverse direction for `higham9_11_flattenTwoBlock`: embed a block row or
column index and an in-block row or column into the flattened `Fin (2 * n)`
surface. -/
def higham9_11_flatIndexOfBlock {n : ℕ} (hn : 0 < n)
    (bi : Fin 2) (i : Fin n) : Fin (2 * n) :=
  ⟨bi.val * n + i.val, by
    have hi : i.val < n := i.isLt
    fin_cases bi <;> simp <;> omega⟩

lemma higham9_11_flatBlockIndex_flatIndexOfBlock {n : ℕ} (hn : 0 < n)
    (bi : Fin 2) (i : Fin n) :
    higham9_11_flatBlockIndex (higham9_11_flatIndexOfBlock hn bi i) = bi := by
  fin_cases bi
  · simp [higham9_11_flatIndexOfBlock, higham9_11_flatBlockIndex, i.isLt]
  · simp [higham9_11_flatIndexOfBlock, higham9_11_flatBlockIndex]

lemma higham9_11_flatInnerIndex_flatIndexOfBlock {n : ℕ} (hn : 0 < n)
    (bi : Fin 2) (i : Fin n) :
    higham9_11_flatInnerIndex hn (higham9_11_flatIndexOfBlock hn bi i) = i := by
  fin_cases bi
  · ext
    simp [higham9_11_flatIndexOfBlock, higham9_11_flatInnerIndex, i.isLt]
  · ext
    simp [higham9_11_flatIndexOfBlock, higham9_11_flatInnerIndex]

lemma higham9_11_flatIndexOfBlock_flatBlockIndex_flatInnerIndex {n : ℕ}
    (hn : 0 < n) (i : Fin (2 * n)) :
    higham9_11_flatIndexOfBlock hn
        (higham9_11_flatBlockIndex i) (higham9_11_flatInnerIndex hn i) = i := by
  by_cases hi : i.val < n
  · ext
    simp [higham9_11_flatIndexOfBlock, higham9_11_flatBlockIndex,
      higham9_11_flatInnerIndex, hi]
  · ext
    simp [higham9_11_flatIndexOfBlock, higham9_11_flatBlockIndex,
      higham9_11_flatInnerIndex, hi]
    omega

lemma higham9_11_flatBlockInner_eq_iff {n : ℕ} (hn : 0 < n)
    (i j : Fin (2 * n)) :
    (higham9_11_flatBlockIndex i = higham9_11_flatBlockIndex j ∧
        higham9_11_flatInnerIndex hn i = higham9_11_flatInnerIndex hn j) ↔
      i = j := by
  constructor
  · intro h
    calc
      i =
          higham9_11_flatIndexOfBlock hn
            (higham9_11_flatBlockIndex i) (higham9_11_flatInnerIndex hn i) := by
            rw [higham9_11_flatIndexOfBlock_flatBlockIndex_flatInnerIndex]
      _ =
          higham9_11_flatIndexOfBlock hn
            (higham9_11_flatBlockIndex j) (higham9_11_flatInnerIndex hn j) := by
            rw [h.1, h.2]
      _ = j := by
            rw [higham9_11_flatIndexOfBlock_flatBlockIndex_flatInnerIndex]
  · intro h
    subst h
    exact ⟨rfl, rfl⟩

/-- **Problem 9.11 support**, the ordinary flattened `Fin (2*n)` index is
equivalent to a block index and an in-block index. -/
noncomputable def higham9_11_flatBlockEquiv {n : ℕ} (hn : 0 < n) :
    (Fin 2 × Fin n) ≃ Fin (2 * n) where
  toFun x := higham9_11_flatIndexOfBlock hn x.1 x.2
  invFun i := (higham9_11_flatBlockIndex i, higham9_11_flatInnerIndex hn i)
  left_inv := by
    intro x
    cases x with
    | mk bi i =>
        simp [higham9_11_flatBlockIndex_flatIndexOfBlock,
          higham9_11_flatInnerIndex_flatIndexOfBlock]
  right_inv := by
    intro i
    exact higham9_11_flatIndexOfBlock_flatBlockIndex_flatInnerIndex hn i

lemma higham9_11_flattenTwoBlock_entry_flatIndexOfBlock {n : ℕ} (hn : 0 < n)
    (B : Fin 2 → Fin 2 → (Fin n → Fin n → ℝ))
    (bi bj : Fin 2) (i j : Fin n) :
    higham9_11_flattenTwoBlock hn B
        (higham9_11_flatIndexOfBlock hn bi i)
        (higham9_11_flatIndexOfBlock hn bj j) =
      B bi bj i j := by
  simp [higham9_11_flattenTwoBlock,
    higham9_11_flatBlockIndex_flatIndexOfBlock,
    higham9_11_flatInnerIndex_flatIndexOfBlock]

/-- **Problem 9.11**, flattening preserves Chapter 12's block max-entry norm
as the ordinary max-entry norm of the flattened `Fin (2 * n)` matrix. -/
theorem higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm {n : ℕ}
    (hn : 0 < n) (B : Fin 2 → Fin 2 → (Fin n → Fin n → ℝ)) :
    maxEntryNorm (by omega : 0 < 2 * n) (higham9_11_flattenTwoBlock hn B) =
      blockMaxNorm (by norm_num : 0 < 2) hn B := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have hentry :
        |B (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j)
            (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn j)| ≤
          maxEntryNorm hn
            (B (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j)) :=
      entry_le_maxEntryNorm hn
        (B (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j))
        (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn j)
    exact le_trans (by simpa [higham9_11_flattenTwoBlock] using hentry)
      (block_le_blockMaxNorm (by norm_num : 0 < 2) hn B
        (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j))
  · unfold blockMaxNorm
    apply Finset.sup'_le
    intro bi _
    apply Finset.sup'_le
    intro bj _
    conv_lhs => unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have h :=
      entry_le_maxEntryNorm (by omega : 0 < 2 * n)
        (higham9_11_flattenTwoBlock hn B)
        (higham9_11_flatIndexOfBlock hn bi i)
        (higham9_11_flatIndexOfBlock hn bj j)
    simpa [higham9_11_flattenTwoBlock_entry_flatIndexOfBlock] using h

lemma higham9_11_blockMatrix_abs {n : ℕ} (A : Fin n → Fin n → ℝ)
    (bi bj : Fin 2) (i j : Fin n) :
    |higham9_11_blockMatrix A bi bj i j| = |A i j| := by
  unfold higham9_11_blockMatrix
  by_cases h : bi = (1 : Fin 2) ∧ bj = (1 : Fin 2)
  · simp [h]
  · simp [h]

lemma higham9_11_blockInverseCandidate_abs {n : ℕ}
    (A_inv : Fin n → Fin n → ℝ) (bi bj : Fin 2) (i j : Fin n) :
    |higham9_11_blockInverseCandidate A_inv bi bj i j| =
      (1 / 2 : ℝ) * |A_inv i j| := by
  unfold higham9_11_blockInverseCandidate
  rw [abs_mul, higham9_11_blockMatrix_abs]
  norm_num

private lemma higham9_11_sum_half_add_half {n : ℕ} (f : Fin n → ℝ) :
    (∑ l : Fin n, (1 / 2 : ℝ) * f l) +
      (∑ l : Fin n, (1 / 2 : ℝ) * f l) =
        ∑ l : Fin n, f l := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

private lemma higham9_11_sum_half_add_neg_half {n : ℕ} (f : Fin n → ℝ) :
    (∑ l : Fin n, (1 / 2 : ℝ) * f l) +
      (∑ l : Fin n, -(1 / 2 : ℝ) * f l) =
        0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro l _
  ring

/-- **Problem 9.11**, left-inverse half of the displayed identity
`B⁻¹ = (1/2) [[A⁻¹,A⁻¹],[A⁻¹,-A⁻¹]]`. -/
theorem higham9_11_blockInverseCandidate_left {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv) :
    ∀ bi bj : Fin 2, ∀ i j : Fin n,
      blockMatProd (higham9_11_blockInverseCandidate A_inv)
          (higham9_11_blockMatrix A) bi bj i j =
        if bi = bj then if i = j then 1 else 0 else 0 := by
  intro bi bj i j
  fin_cases bi <;> fin_cases bj
  · calc
      blockMatProd (higham9_11_blockInverseCandidate A_inv)
          (higham9_11_blockMatrix A) 0 0 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) +
              (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro l _ <;>
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix] <;>
                ring
        _ = ∑ l : Fin n, A_inv i l * A l j :=
              higham9_11_sum_half_add_half (fun l : Fin n => A_inv i l * A l j)
        _ = if i = j then 1 else 0 := hLeft i j
        _ = (if (0 : Fin 2) = 0 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockInverseCandidate A_inv)
          (higham9_11_blockMatrix A) 0 1 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) +
              (∑ l : Fin n, -(1 / 2 : ℝ) * (A_inv i l * A l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
        _ = 0 := higham9_11_sum_half_add_neg_half (fun l : Fin n => A_inv i l * A l j)
        _ = (if (0 : Fin 2) = 1 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockInverseCandidate A_inv)
          (higham9_11_blockMatrix A) 1 0 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) +
              (∑ l : Fin n, -(1 / 2 : ℝ) * (A_inv i l * A l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
        _ = 0 := higham9_11_sum_half_add_neg_half (fun l : Fin n => A_inv i l * A l j)
        _ = (if (1 : Fin 2) = 0 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockInverseCandidate A_inv)
          (higham9_11_blockMatrix A) 1 1 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) +
              (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro l _ <;>
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix] <;>
                ring
        _ = ∑ l : Fin n, A_inv i l * A l j :=
              higham9_11_sum_half_add_half (fun l : Fin n => A_inv i l * A l j)
        _ = if i = j then 1 else 0 := hLeft i j
        _ = (if (1 : Fin 2) = 1 then if i = j then 1 else 0 else 0) := by simp

/-- **Problem 9.11**, right-inverse half of the displayed identity
`B⁻¹ = (1/2) [[A⁻¹,A⁻¹],[A⁻¹,-A⁻¹]]`. -/
theorem higham9_11_blockInverseCandidate_right {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv) :
    ∀ bi bj : Fin 2, ∀ i j : Fin n,
      blockMatProd (higham9_11_blockMatrix A)
          (higham9_11_blockInverseCandidate A_inv) bi bj i j =
        if bi = bj then if i = j then 1 else 0 else 0 := by
  intro bi bj i j
  fin_cases bi <;> fin_cases bj
  · calc
      blockMatProd (higham9_11_blockMatrix A)
          (higham9_11_blockInverseCandidate A_inv) 0 0 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) +
              (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro l _ <;>
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix] <;>
                ring
        _ = ∑ l : Fin n, A i l * A_inv l j :=
              higham9_11_sum_half_add_half (fun l : Fin n => A i l * A_inv l j)
        _ = if i = j then 1 else 0 := hRight i j
        _ = (if (0 : Fin 2) = 0 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockMatrix A)
          (higham9_11_blockInverseCandidate A_inv) 0 1 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) +
              (∑ l : Fin n, -(1 / 2 : ℝ) * (A i l * A_inv l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
        _ = 0 := higham9_11_sum_half_add_neg_half (fun l : Fin n => A i l * A_inv l j)
        _ = (if (0 : Fin 2) = 1 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockMatrix A)
          (higham9_11_blockInverseCandidate A_inv) 1 0 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) +
              (∑ l : Fin n, -(1 / 2 : ℝ) * (A i l * A_inv l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
        _ = 0 := higham9_11_sum_half_add_neg_half (fun l : Fin n => A i l * A_inv l j)
        _ = (if (1 : Fin 2) = 0 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockMatrix A)
          (higham9_11_blockInverseCandidate A_inv) 1 1 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) +
              (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro l _ <;>
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix] <;>
                ring
        _ = ∑ l : Fin n, A i l * A_inv l j :=
              higham9_11_sum_half_add_half (fun l : Fin n => A i l * A_inv l j)
        _ = if i = j then 1 else 0 := hRight i j
        _ = (if (1 : Fin 2) = 1 then if i = j then 1 else 0 else 0) := by simp

/-- **Problem 9.11 support**, flattening transports block multiplication to
ordinary matrix multiplication on `Fin (2*n)`. -/
theorem higham9_11_flattenTwoBlock_matMul_entry {n : ℕ} (hn : 0 < n)
    (B C : Fin 2 → Fin 2 → (Fin n → Fin n → ℝ))
    (i j : Fin (2 * n)) :
    matMul (2 * n) (higham9_11_flattenTwoBlock hn B)
        (higham9_11_flattenTwoBlock hn C) i j =
      blockMatProd B C
        (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j)
        (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn j) := by
  classical
  unfold matMul blockMatProd higham9_11_flattenTwoBlock
  let e := higham9_11_flatBlockEquiv hn
  rw [← Equiv.sum_comp e
    (fun k : Fin (2 * n) =>
      B (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex k)
          (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn k) *
        C (higham9_11_flatBlockIndex k) (higham9_11_flatBlockIndex j)
          (higham9_11_flatInnerIndex hn k) (higham9_11_flatInnerIndex hn j))]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [e, higham9_11_flatBlockEquiv, higham9_11_flatBlockIndex_flatIndexOfBlock,
    higham9_11_flatInnerIndex_flatIndexOfBlock]

/-- **Problem 9.11 support**, the displayed block right inverse remains a
right inverse after flattening to an ordinary `Fin (2*n)` matrix. -/
theorem higham9_11_flattenTwoBlock_right_inverse {n : ℕ} (hn : 0 < n)
    {B C : Fin 2 → Fin 2 → (Fin n → Fin n → ℝ)}
    (hRight :
      ∀ bi bj : Fin 2, ∀ i j : Fin n,
        blockMatProd B C bi bj i j =
          if bi = bj then if i = j then 1 else 0 else 0) :
    IsRightInverse (2 * n)
      (higham9_11_flattenTwoBlock hn B) (higham9_11_flattenTwoBlock hn C) := by
  intro i j
  change
    matMul (2 * n) (higham9_11_flattenTwoBlock hn B)
        (higham9_11_flattenTwoBlock hn C) i j =
      if i = j then 1 else 0
  rw [higham9_11_flattenTwoBlock_matMul_entry hn B C i j]
  rw [hRight (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j)
    (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn j)]
  by_cases hij : i = j
  · subst j
    simp
  · have hnot :
        ¬ (higham9_11_flatBlockIndex i = higham9_11_flatBlockIndex j ∧
          higham9_11_flatInnerIndex hn i = higham9_11_flatInnerIndex hn j) := by
      intro h
      exact hij ((higham9_11_flatBlockInner_eq_iff hn i j).mp h)
    by_cases hb : higham9_11_flatBlockIndex i = higham9_11_flatBlockIndex j
    · have hi_ne :
          higham9_11_flatInnerIndex hn i ≠ higham9_11_flatInnerIndex hn j := by
        intro hi_eq
        exact hnot ⟨hb, hi_eq⟩
      simp [hij, hb, hi_ne]
    · simp [hij, hb]

/-- **Problem 9.11 support**, a function-shaped right inverse gives a
nonzero determinant for the corresponding Mathlib matrix. -/
theorem higham9_det_ne_zero_of_isRightInverse {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  exact
    Matrix.det_ne_zero_of_right_inverse
      (A := (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))
      (B := (Matrix.of A_inv : Matrix (Fin n) (Fin n) ℝ))
      (by
        ext i j
        rw [Matrix.mul_apply, Matrix.one_apply]
        exact hRight i j)

lemma higham9_11_blockMatrix_block_max_eq {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (bi bj : Fin 2) :
    maxEntryNorm hn (higham9_11_blockMatrix A bi bj) = maxEntryNorm hn A := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    rw [higham9_11_blockMatrix_abs]
    exact entry_le_maxEntryNorm hn A i j
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have h := entry_le_maxEntryNorm hn (higham9_11_blockMatrix A bi bj) i j
    rwa [higham9_11_blockMatrix_abs] at h

/-- **Problem 9.11**, `alpha(B) = alpha(A)` for
`B = [[A,A],[A,-A]]`, using the repository entrywise block max norm. -/
theorem higham9_11_alpha_block_eq {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    blockMaxNorm (by norm_num : 0 < 2) hn (higham9_11_blockMatrix A) =
      maxEntryNorm hn A := by
  apply le_antisymm
  · unfold blockMaxNorm
    apply Finset.sup'_le
    intro bi _
    apply Finset.sup'_le
    intro bj _
    rw [higham9_11_blockMatrix_block_max_eq hn A bi bj]
  · have h :=
      block_le_blockMaxNorm (by norm_num : 0 < 2) hn
        (higham9_11_blockMatrix A) (0 : Fin 2) (0 : Fin 2)
    simpa [higham9_11_blockMatrix_block_max_eq hn A (0 : Fin 2) (0 : Fin 2)] using h

/-- **Problem 9.11**, flattened source-surface form of `alpha(B)=alpha(A)`. -/
theorem higham9_11_flatten_blockMatrix_maxEntryNorm_eq {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    maxEntryNorm (by omega : 0 < 2 * n)
        (higham9_11_flattenTwoBlock hn (higham9_11_blockMatrix A)) =
      maxEntryNorm hn A := by
  rw [higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm hn
    (higham9_11_blockMatrix A), higham9_11_alpha_block_eq hn A]

lemma higham9_11_blockInverseCandidate_block_max_eq {n : ℕ} (hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (bi bj : Fin 2) :
    maxEntryNorm hn (higham9_11_blockInverseCandidate A_inv bi bj) =
      (1 / 2 : ℝ) * maxEntryNorm hn A_inv := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    rw [higham9_11_blockInverseCandidate_abs]
    exact mul_le_mul_of_nonneg_left
      (entry_le_maxEntryNorm hn A_inv i j) (by norm_num)
  · have hentry :
        ∀ i j : Fin n,
          (1 / 2 : ℝ) * |A_inv i j| ≤
            maxEntryNorm hn (higham9_11_blockInverseCandidate A_inv bi bj) := by
      intro i j
      have h :=
        entry_le_maxEntryNorm hn (higham9_11_blockInverseCandidate A_inv bi bj) i j
      simpa [higham9_11_blockInverseCandidate_abs] using h
    have hmax_le :
        maxEntryNorm hn A_inv ≤
          2 * maxEntryNorm hn (higham9_11_blockInverseCandidate A_inv bi bj) := by
      conv_lhs => unfold maxEntryNorm
      apply Finset.sup'_le
      intro i _
      apply Finset.sup'_le
      intro j _
      have hij := hentry i j
      have hmul :=
        mul_le_mul_of_nonneg_left hij (by norm_num : (0 : ℝ) ≤ 2)
      calc
        |A_inv i j| = 2 * ((1 / 2 : ℝ) * |A_inv i j|) := by ring
        _ ≤ 2 * maxEntryNorm hn (higham9_11_blockInverseCandidate A_inv bi bj) := hmul
    linarith

/-- **Problem 9.11**, `beta(B) = beta(A)/2` for the displayed inverse
candidate of `B = [[A,A],[A,-A]]`. -/
theorem higham9_11_beta_blockInv_eq {n : ℕ} (hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) :
    blockMaxNorm (by norm_num : 0 < 2) hn (higham9_11_blockInverseCandidate A_inv) =
      (1 / 2 : ℝ) * maxEntryNorm hn A_inv := by
  apply le_antisymm
  · unfold blockMaxNorm
    apply Finset.sup'_le
    intro bi _
    apply Finset.sup'_le
    intro bj _
    rw [higham9_11_blockInverseCandidate_block_max_eq hn A_inv bi bj]
  · have h :=
      block_le_blockMaxNorm (by norm_num : 0 < 2) hn
        (higham9_11_blockInverseCandidate A_inv) (0 : Fin 2) (0 : Fin 2)
    simpa [higham9_11_blockInverseCandidate_block_max_eq hn A_inv
      (0 : Fin 2) (0 : Fin 2)] using h

/-- **Problem 9.11**, flattened source-surface form of `beta(B)=beta(A)/2`
for the displayed inverse candidate. -/
theorem higham9_11_flatten_blockInverseCandidate_maxEntryNorm_eq {n : ℕ}
    (hn : 0 < n) (A_inv : Fin n → Fin n → ℝ) :
    maxEntryNorm (by omega : 0 < 2 * n)
        (higham9_11_flattenTwoBlock hn (higham9_11_blockInverseCandidate A_inv)) =
      (1 / 2 : ℝ) * maxEntryNorm hn A_inv := by
  rw [higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm hn
    (higham9_11_blockInverseCandidate A_inv), higham9_11_beta_blockInv_eq hn A_inv]

/-- **Problem 9.11**, the source identity
`theta(B) = 2 * theta(A)` for `theta(A) = 1/(alpha(A) * beta(A))`.

This is the local block-matrix algebra used by the appendix solution; it does
not assert the later `g(2n)` lower-bound specialization for the sine matrix. -/
theorem higham9_11_theta_block_eq_two_theta {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hAinv : 0 < maxEntryNorm hn A_inv) :
    1 /
        (blockMaxNorm (by norm_num : 0 < 2) hn (higham9_11_blockMatrix A) *
          blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockInverseCandidate A_inv)) =
      2 * (1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv)) := by
  rw [higham9_11_alpha_block_eq hn A, higham9_11_beta_blockInv_eq hn A_inv]
  field_simp [ne_of_gt hA, ne_of_gt hAinv]

/-- **Problem 9.11 / equation (9.12)**, the block-doubled theta lower-bound
arithmetic for the sine witness used as both the matrix and inverse candidate.

This combines the already proved block identity `theta(B) = 2 * theta(A)` with
the sine-matrix theta bound.  It does not construct the complete-pivoting
growth trace. -/
theorem higham9_11_sine_block_theta_candidate_ge_succ {n : ℕ}
    (hn : 0 < n) :
    (n : ℝ) + 1 ≤
      1 /
        (blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n)) *
          blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n))) := by
  rw [higham9_11_theta_block_eq_two_theta hn
    (higham9_12_sineMatrix n) (higham9_12_sineMatrix n)
    (higham9_12_sineMatrix_maxEntryNorm_pos hn)
    (higham9_12_sineMatrix_maxEntryNorm_pos hn)]
  exact higham9_12_sineMatrix_two_theta_candidate_ge_succ hn

/-- **Problem 9.11**, final lower-bound bridge from the sine block matrix to a
visible growth witness.

The theorem uses the closed sine-block theta estimate and explicit hypotheses
`theta(B) <= rhoB <= g(2n)`.  It does not construct the complete-pivoting
growth trace or hide the source witness as an assumption. -/
theorem higham9_11_complete_pivoting_lower_bound_from_sine_block_theta {n : ℕ}
    (hn : 0 < n)
    (g2n rhoB : ℝ)
    (hg : rhoB ≤ g2n)
    (hrho :
      1 /
        (blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n)) *
          blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n))) ≤ rhoB) :
    (n : ℝ) + 1 ≤ g2n :=
  le_trans (higham9_11_sine_block_theta_candidate_ge_succ hn) (le_trans hrho hg)

/-- Problem 9.11's final lower-bound arithmetic: once the complete-pivoting
growth function and sine-matrix specialization supply
`g(2n) ≥ rho(B) ≥ 2 theta(S_n) = n + 1`, the advertised bound follows. -/
theorem higham9_11_complete_pivoting_lower_bound_consequence (n : ℕ)
    (g2n rhoB thetaSn : ℝ)
    (hg : rhoB ≤ g2n)
    (hrho : 2 * thetaSn ≤ rhoB)
    (hSn : 2 * thetaSn = (n : ℝ) + 1) :
    (n : ℝ) + 1 ≤ g2n := by
  linarith

/-- Problem 9.11's lower-bound arithmetic in inequality form.  This is the
form supplied by the conditional max-entry sine witness
`higham9_12_two_theta_ge_succ_of_maxEntryNorm_le_scale`. -/
theorem higham9_11_complete_pivoting_lower_bound_consequence_le (n : ℕ)
    (g2n rhoB thetaSn : ℝ)
    (hg : rhoB ≤ g2n)
    (hrho : 2 * thetaSn ≤ rhoB)
    (hSn : (n : ℝ) + 1 ≤ 2 * thetaSn) :
    (n : ℝ) + 1 ≤ g2n := by
  linarith

/-- **Equation (9.14)**, Wilkinson's scalar product inside the complete-pivoting
growth upper bound:
`2 * 3^(1/2) * ... * n^(1/(n-1))`.

This records the scalar surface only; the source growth theorem
`rho_n^c <= sqrt n * sqrt(product)` still requires the complete-pivoting trace
and Wilkinson growth proof recorded as open in the Chapter 9 report. -/
noncomputable def higham9_14_completePivotWilkinsonProduct (n : ℕ) : ℝ :=
  (Finset.Icc 2 n).prod fun k => (k : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1))

/-- **Equation (9.14)**, Wilkinson's displayed complete-pivoting upper-bound
RHS `sqrt n * sqrt(2 * 3^(1/2) * ... * n^(1/(n-1)))`. -/
noncomputable def higham9_14_completePivotWilkinsonBound (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.sqrt (higham9_14_completePivotWilkinsonProduct n)

lemma higham9_14_completePivotWilkinsonProduct_nonneg (n : ℕ) :
    0 ≤ higham9_14_completePivotWilkinsonProduct n := by
  unfold higham9_14_completePivotWilkinsonProduct
  exact Finset.prod_nonneg fun k _ =>
    Real.rpow_nonneg (Nat.cast_nonneg k) ((1 : ℝ) / ((k : ℝ) - 1))

lemma higham9_14_completePivotWilkinsonProduct_pos (n : ℕ) :
    0 < higham9_14_completePivotWilkinsonProduct n := by
  unfold higham9_14_completePivotWilkinsonProduct
  exact Finset.prod_pos fun k hk => by
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkposNat : 0 < k := Nat.lt_of_lt_of_le (by decide : 0 < 2) hk2
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkposNat
    exact Real.rpow_pos_of_pos hkpos _

lemma higham9_14_completePivotWilkinsonBound_nonneg (n : ℕ) :
    0 ≤ higham9_14_completePivotWilkinsonBound n := by
  unfold higham9_14_completePivotWilkinsonBound
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma higham9_14_completePivotWilkinsonBound_pos {n : ℕ} (hn : 0 < n) :
    0 < higham9_14_completePivotWilkinsonBound n := by
  unfold higham9_14_completePivotWilkinsonBound
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact mul_pos (Real.sqrt_pos_of_pos hnR)
    (Real.sqrt_pos_of_pos (higham9_14_completePivotWilkinsonProduct_pos n))

/-- **Problem 9.11 / equation (9.15)**, the source growth-function set
underlying `g(n) = sup_A rho_n^c(A)`, parameterized by the still-separate
complete-pivoting growth map `rhoC`. -/
def higham9_completePivotGrowthSet (n : ℕ)
    (rhoC : (Fin n → Fin n → ℝ) → ℝ) : Set ℝ :=
  Set.range rhoC

/-- **Problem 9.11 / equation (9.15)**, the source growth-function supremum
`g(n)`, parameterized by a complete-pivoting growth map `rhoC`.  This definition
records the supremum step only; it does not claim that the complete-pivoting
algorithmic trace for `rho_n^c` has been formalized. -/
noncomputable def higham9_completePivotGrowthSup (n : ℕ)
    (rhoC : (Fin n → Fin n → ℝ) → ℝ) : ℝ :=
  sSup (higham9_completePivotGrowthSet n rhoC)

/-- **Problem 9.11 / equation (9.15)**, every concrete complete-pivoting growth
value is bounded by the supremum `g(n)` when the source growth family is bounded
above. -/
theorem higham9_completePivotGrowth_le_sup (n : ℕ)
    (rhoC : (Fin n → Fin n → ℝ) → ℝ)
    (hBdd : BddAbove (higham9_completePivotGrowthSet n rhoC))
    (A : Fin n → Fin n → ℝ) :
    rhoC A ≤ higham9_completePivotGrowthSup n rhoC := by
  exact le_csSup hBdd ⟨A, rfl⟩

/-- **Problem 9.11**, source lower-bound step with `g(2n)` instantiated as the
supremum of complete-pivoting growth values.  The remaining open source work is
to formalize the actual complete-pivoting trace `rhoC` and the sine-matrix
witness that supplies `2 * theta(S_n) = n + 1`. -/
theorem higham9_11_complete_pivoting_lower_bound_from_witness (n : ℕ)
    (rhoC : (Fin (2 * n) → Fin (2 * n) → ℝ) → ℝ)
    (hBdd : BddAbove (higham9_completePivotGrowthSet (2 * n) rhoC))
    (B : Fin (2 * n) → Fin (2 * n) → ℝ)
    (thetaSn : ℝ)
    (hrho : 2 * thetaSn ≤ rhoC B)
    (hSn : 2 * thetaSn = (n : ℝ) + 1) :
    (n : ℝ) + 1 ≤ higham9_completePivotGrowthSup (2 * n) rhoC := by
  have hg : rhoC B ≤ higham9_completePivotGrowthSup (2 * n) rhoC :=
    higham9_completePivotGrowth_le_sup (2 * n) rhoC hBdd B
  exact higham9_11_complete_pivoting_lower_bound_consequence n
    (higham9_completePivotGrowthSup (2 * n) rhoC) (rhoC B) thetaSn hg hrho hSn

/-- **Problem 9.11**, inequality-form source lower-bound step with `g(2n)`
instantiated as the supremum of complete-pivoting growth values.

This is the form aligned with the sine-matrix witness proved in this file,
which supplies `(n : ℝ) + 1 ≤ 2 * theta(S_n)`.  The complete-pivoting trace
itself remains an explicit hypothesis through `rhoC` and `hrho`. -/
theorem higham9_11_complete_pivoting_lower_bound_from_witness_le (n : ℕ)
    (rhoC : (Fin (2 * n) → Fin (2 * n) → ℝ) → ℝ)
    (hBdd : BddAbove (higham9_completePivotGrowthSet (2 * n) rhoC))
    (B : Fin (2 * n) → Fin (2 * n) → ℝ)
    (thetaSn : ℝ)
    (hrho : 2 * thetaSn ≤ rhoC B)
    (hSn : (n : ℝ) + 1 ≤ 2 * thetaSn) :
    (n : ℝ) + 1 ≤ higham9_completePivotGrowthSup (2 * n) rhoC := by
  have hg : rhoC B ≤ higham9_completePivotGrowthSup (2 * n) rhoC :=
    higham9_completePivotGrowth_le_sup (2 * n) rhoC hBdd B
  exact higham9_11_complete_pivoting_lower_bound_consequence_le n
    (higham9_completePivotGrowthSup (2 * n) rhoC) (rhoC B) thetaSn hg hrho hSn

/-- **Problem 9.11**, flattened sine-block witness for the source
`g(2n) = sup_A rho_n^c(A)` surface.

The theorem instantiates the bounded-family supremum with the flattened
`[[S_n,S_n],[S_n,-S_n]]` matrix.  The complete-pivoting growth lower bound for
that concrete flattened matrix remains the explicit hypothesis `hrho`. -/
theorem higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block
    {n : ℕ} (hn : 0 < n)
    (rhoC : (Fin (2 * n) → Fin (2 * n) → ℝ) → ℝ)
    (hBdd : BddAbove (higham9_completePivotGrowthSet (2 * n) rhoC))
    (hrho :
      1 /
        (blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n)) *
          blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n))) ≤
        rhoC
          (higham9_11_flattenTwoBlock hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n))) ) :
    (n : ℝ) + 1 ≤ higham9_completePivotGrowthSup (2 * n) rhoC := by
  have hg :
      rhoC
          (higham9_11_flattenTwoBlock hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n))) ≤
        higham9_completePivotGrowthSup (2 * n) rhoC :=
    higham9_completePivotGrowth_le_sup (2 * n) rhoC hBdd
      (higham9_11_flattenTwoBlock hn (higham9_11_blockMatrix (higham9_12_sineMatrix n)))
  exact higham9_11_complete_pivoting_lower_bound_from_sine_block_theta hn
    (higham9_completePivotGrowthSup (2 * n) rhoC)
    (rhoC
      (higham9_11_flattenTwoBlock hn (higham9_11_blockMatrix (higham9_12_sineMatrix n))))
    hg hrho

/-- **Problem 9.11**, fully flattened max-entry-norm form of the sine-block
bounded-supremum witness.

This is the same bridge as
`higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block`, but the
visible growth hypothesis uses ordinary max-entry norms on the flattened
`Fin (2n)` matrix and flattened inverse candidate. -/
theorem higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block_maxEntry
    {n : ℕ} (hn : 0 < n)
    (rhoC : (Fin (2 * n) → Fin (2 * n) → ℝ) → ℝ)
    (hBdd : BddAbove (higham9_completePivotGrowthSet (2 * n) rhoC))
    (hrho :
      1 /
        (maxEntryNorm (by omega : 0 < 2 * n)
            (higham9_11_flattenTwoBlock hn
              (higham9_11_blockMatrix (higham9_12_sineMatrix n))) *
          maxEntryNorm (by omega : 0 < 2 * n)
            (higham9_11_flattenTwoBlock hn
              (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n)))) ≤
        rhoC
          (higham9_11_flattenTwoBlock hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n))) ) :
    (n : ℝ) + 1 ≤ higham9_completePivotGrowthSup (2 * n) rhoC :=
  higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block hn rhoC hBdd
    (by
      simpa [higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm] using hrho)

/-- **Equation (9.16)**, Foster's scalar rook-pivoting growth upper-bound RHS
`1.5 * n^(3/4 * log n)`.

This is only the source scalar surface. The actual rook-pivoting growth theorem
and recursive trace remain open Split-2 work. -/
noncomputable def higham9_16_rookPivotFosterBound (n : ℕ) : ℝ :=
  (3 / 2 : ℝ) * (n : ℝ) ^ ((3 / 4 : ℝ) * Real.log (n : ℝ))

lemma higham9_16_rookPivotFosterBound_nonneg (n : ℕ) :
    0 ≤ higham9_16_rookPivotFosterBound n := by
  unfold higham9_16_rookPivotFosterBound
  exact mul_nonneg (by norm_num)
    (Real.rpow_nonneg (Nat.cast_nonneg n) ((3 / 4 : ℝ) * Real.log (n : ℝ)))

lemma higham9_16_rookPivotFosterBound_pos {n : ℕ} (hn : 0 < n) :
    0 < higham9_16_rookPivotFosterBound n := by
  unfold higham9_16_rookPivotFosterBound
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact mul_pos (by norm_num)
    (Real.rpow_pos_of_pos hnR ((3 / 4 : ℝ) * Real.log (n : ℝ)))

/-! ## Problem 9.13: threshold pivoting and sparse-column growth -/

/-- **Problem 9.13**, the per-modification threshold-pivoting factor
`1 + tau^{-1}`. -/
noncomputable def higham9_13_thresholdFactor (τ : ℝ) : ℝ :=
  1 + τ⁻¹

lemma higham9_13_thresholdFactor_ge_one (τ : ℝ) (hτ : 0 < τ) :
    1 ≤ higham9_13_thresholdFactor τ := by
  unfold higham9_13_thresholdFactor
  have hτinv : 0 ≤ τ⁻¹ := inv_nonneg.mpr (le_of_lt hτ)
  linarith

lemma higham9_13_thresholdFactor_nonneg (τ : ℝ) (hτ : 0 < τ) :
    0 ≤ higham9_13_thresholdFactor τ :=
  le_trans (by norm_num : (0 : ℝ) ≤ 1)
    (higham9_13_thresholdFactor_ge_one τ hτ)

/-- **Problem 9.13**, one scalar threshold-pivoting update.

If the old entry and the pivot-row entry are both bounded by the current
column maximum and the multiplier is bounded by `tau^{-1}`, then the updated
entry is bounded by `(1 + tau^{-1})` times the old column maximum. -/
theorem higham9_13_threshold_update_abs_bound (τ maxOld old pivot multiplier : ℝ)
    (hτ : 0 < τ)
    (hold : |old| ≤ maxOld)
    (hpivot : |pivot| ≤ maxOld)
    (hmult : |multiplier| ≤ τ⁻¹) :
    |old - multiplier * pivot| ≤
      higham9_13_thresholdFactor τ * maxOld := by
  have hτinv : 0 ≤ τ⁻¹ := inv_nonneg.mpr (le_of_lt hτ)
  have hmul : |multiplier * pivot| ≤ τ⁻¹ * maxOld := by
    rw [abs_mul]
    exact mul_le_mul hmult hpivot (abs_nonneg pivot) hτinv
  have htri : |old - multiplier * pivot| ≤ |old| + |multiplier * pivot| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le old (-(multiplier * pivot))
  calc
    |old - multiplier * pivot|
        ≤ |old| + |multiplier * pivot| := htri
    _ ≤ maxOld + τ⁻¹ * maxOld := add_le_add hold hmul
    _ = higham9_13_thresholdFactor τ * maxOld := by
        unfold higham9_13_thresholdFactor
        ring

/-- **Problem 9.13**, iteration over the number of modifications to a sparse
column.  If each modification of column `j` multiplies its running maximum by
at most `1 + tau^{-1}`, then after `mu` modifications the source bound follows. -/
theorem higham9_13_column_growth_by_modification_count (τ : ℝ) (hτ : 0 < τ)
    (colMax : ℕ → ℝ) :
    ∀ μ : ℕ,
      (∀ t : ℕ, t < μ →
        colMax (t + 1) ≤ higham9_13_thresholdFactor τ * colMax t) →
      colMax μ ≤ higham9_13_thresholdFactor τ ^ μ * colMax 0 := by
  intro μ
  induction μ with
  | zero =>
      intro _hstep
      simp
  | succ μ ih =>
      intro hstep
      have hstep_prev : ∀ t : ℕ, t < μ →
          colMax (t + 1) ≤ higham9_13_thresholdFactor τ * colMax t := by
        intro t ht
        exact hstep t (Nat.lt_trans ht (Nat.lt_succ_self μ))
      have hih := ih hstep_prev
      have hlast :
          colMax (μ + 1) ≤ higham9_13_thresholdFactor τ * colMax μ :=
        hstep μ (Nat.lt_succ_self μ)
      have hfactor_nonneg : 0 ≤ higham9_13_thresholdFactor τ :=
        higham9_13_thresholdFactor_nonneg τ hτ
      calc
        colMax (Nat.succ μ)
            = colMax (μ + 1) := rfl
        _ ≤ higham9_13_thresholdFactor τ * colMax μ := hlast
        _ ≤ higham9_13_thresholdFactor τ *
              (higham9_13_thresholdFactor τ ^ μ * colMax 0) :=
            mul_le_mul_of_nonneg_left hih hfactor_nonneg
        _ = higham9_13_thresholdFactor τ ^ Nat.succ μ * colMax 0 := by
            rw [pow_succ]
            ring

/-- A max-entry norm is bounded by any uniform entrywise absolute-value bound. -/
theorem higham9_13_maxEntryNorm_bound_of_entry_bound {n : ℕ} (hn : 0 < n)
    (U : Fin n → Fin n → ℝ) (B : ℝ)
    (hB : ∀ i j : Fin n, |U i j| ≤ B) :
    maxEntryNorm hn U ≤ B := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact hB i j

/-- **Problem 9.13**, source-facing growth-factor consequence.

If every entry of the final `U` is bounded by
`(1 + tau^{-1})^muMax * max_i,j |a_ij|`, then Higham's max-entry growth factor
satisfies `rho_n <= (1 + tau^{-1})^muMax`. -/
theorem higham9_13_growthFactorEntry_bound_of_sparse_columns {n : ℕ}
    (hn : 0 < n) (τ : ℝ) (_hτ : 0 < τ)
    (μmax : ℕ) (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hEntry : ∀ i j : Fin n,
      |U i j| ≤ higham9_13_thresholdFactor τ ^ μmax * maxEntryNorm hn A) :
    growthFactorEntry hn A U hA ≤ higham9_13_thresholdFactor τ ^ μmax := by
  have hU :
      maxEntryNorm hn U ≤
        higham9_13_thresholdFactor τ ^ μmax * maxEntryNorm hn A :=
    higham9_13_maxEntryNorm_bound_of_entry_bound hn U
      (higham9_13_thresholdFactor τ ^ μmax * maxEntryNorm hn A) hEntry
  unfold growthFactorEntry
  rw [div_le_iff₀ hA]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hU

/-- **Problem 9.13**, column-count form.

This packages the appendix argument that `mu_j`, the number of nonzeros in
column `j` of `U`, bounds the number of modifications to entries in that
column.  Once the per-column entry bounds are known, taking
`muMax >= max_j mu_j` gives `rho_n <= (1 + tau^{-1})^muMax`. -/
theorem higham9_13_growthFactorEntry_bound_of_column_counts {n : ℕ}
    (hn : 0 < n) (τ : ℝ) (hτ : 0 < τ)
    (μ : Fin n → ℕ) (μmax : ℕ)
    (hμ : ∀ j : Fin n, μ j ≤ μmax)
    (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hEntry : ∀ i j : Fin n,
      |U i j| ≤ higham9_13_thresholdFactor τ ^ μ j * maxEntryNorm hn A) :
    growthFactorEntry hn A U hA ≤ higham9_13_thresholdFactor τ ^ μmax := by
  apply higham9_13_growthFactorEntry_bound_of_sparse_columns hn τ hτ μmax A U hA
  intro i j
  have hpow :
      higham9_13_thresholdFactor τ ^ μ j ≤
        higham9_13_thresholdFactor τ ^ μmax :=
    pow_le_pow_right₀ (higham9_13_thresholdFactor_ge_one τ hτ) (hμ j)
  exact le_trans (hEntry i j)
    (mul_le_mul_of_nonneg_right hpow (le_of_lt hA))

/-- **Problem 9.13**, end-to-end sparse-column modification-count bound.

For each column `j`, `colMax j t` is the running maximum after `t`
modifications to that column.  If threshold pivoting gives the per-modification
factor `1 + tau^{-1}`, the initial column maxima are bounded by
`max_i,j |a_ij|`, and `muMax` bounds the column modification counts `mu_j`,
then Higham's max-entry growth factor satisfies
`rho_n <= (1 + tau^{-1})^muMax`. -/
theorem higham9_13_growthFactorEntry_bound_from_column_modifications {n : ℕ}
    (hn : 0 < n) (τ : ℝ) (hτ : 0 < τ)
    (μ : Fin n → ℕ) (μmax : ℕ)
    (hμ : ∀ j : Fin n, μ j ≤ μmax)
    (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (colMax : Fin n → ℕ → ℝ)
    (hstep : ∀ j : Fin n, ∀ t : ℕ, t < μ j →
      colMax j (t + 1) ≤ higham9_13_thresholdFactor τ * colMax j t)
    (hinitial : ∀ j : Fin n, colMax j 0 ≤ maxEntryNorm hn A)
    (hfinal : ∀ i j : Fin n, |U i j| ≤ colMax j (μ j)) :
    growthFactorEntry hn A U hA ≤ higham9_13_thresholdFactor τ ^ μmax := by
  apply higham9_13_growthFactorEntry_bound_of_column_counts hn τ hτ μ μmax hμ A U hA
  intro i j
  have hiter :
      colMax j (μ j) ≤
        higham9_13_thresholdFactor τ ^ μ j * colMax j 0 :=
    higham9_13_column_growth_by_modification_count τ hτ (colMax j) (μ j) (hstep j)
  have hfactor_pow_nonneg :
      0 ≤ higham9_13_thresholdFactor τ ^ μ j :=
    pow_nonneg (higham9_13_thresholdFactor_nonneg τ hτ) (μ j)
  calc
    |U i j| ≤ colMax j (μ j) := hfinal i j
    _ ≤ higham9_13_thresholdFactor τ ^ μ j * colMax j 0 := hiter
    _ ≤ higham9_13_thresholdFactor τ ^ μ j * maxEntryNorm hn A :=
        mul_le_mul_of_nonneg_left (hinitial j) hfactor_pow_nonneg

/-! ## Problem 9.14: row reversal surface for pre-pivoted GEPP -/

/-- **Problem 9.14**, source-facing predicate for an input that is
pre-pivoted for GEPP: recursive partial pivoting can always choose the leading
row, so no row interchanges are required. -/
abbrev higham_problem9_14_PrePivotedGEPP {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Prop :=
  higham9_7_PartialPivotNoInterchangeTrace 0 n A

/-- **Problem 9.14 / GEPP side**, a no-interchange partial-pivoting trace
constructs an exact no-pivot LU certificate by the standard Schur-complement
induction.  This proves the pre-pivoted GEPP factorization side without
assuming the still-open row-reversal or pairwise-pivoting trace equivalence. -/
theorem higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec :
    ∀ {t n : ℕ} {A : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotNoInterchangeTrace t n A →
        ∃ L U : Fin n → Fin n → ℝ, LUFactSpec n A L U := by
  intro t n A htrace
  induction htrace with
  | done =>
      refine ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_⟩
      refine
        { L_diag := ?_
          L_upper_zero := ?_
          U_lower_zero := ?_
          product_eq := ?_ }
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | step _hchoice hpivot _hnext ih =>
      obtain ⟨L₁, U₁, hLU₁⟩ := ih
      exact
        ⟨luFirstStepL _ L₁, luFirstStepU _ U₁,
          LUFactSpec.of_firstSchurComplement_explicit hpivot hLU₁⟩

/-- **Problem 9.14 / GEPP side**, a no-interchange partial-pivoting trace
constructs exact LU factors whose diagonal pivots are all nonzero.  This is the
nondegeneracy bridge needed before using ordinary exact-LU uniqueness for the
"same LU factorization" clause in Problem 9.14. -/
theorem higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec_pivots_ne_zero :
    ∀ {t n : ℕ} {A : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotNoInterchangeTrace t n A →
        ∃ L U : Fin n → Fin n → ℝ,
          LUFactSpec n A L U ∧ ∀ i : Fin n, U i i ≠ 0 := by
  intro t n A htrace
  induction htrace with
  | done =>
      refine ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_, ?_⟩
      · refine
          { L_diag := ?_
            L_upper_zero := ?_
            U_lower_zero := ?_
            product_eq := ?_ }
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | step _hchoice hpivot _hnext ih =>
      obtain ⟨L₁, U₁, hLU₁, hU₁diag⟩ := ih
      refine
        ⟨luFirstStepL _ L₁, luFirstStepU _ U₁,
          LUFactSpec.of_firstSchurComplement_explicit hpivot hLU₁, ?_⟩
      intro i
      by_cases hi : i = 0
      · subst i
        simpa [luFirstStepU] using hpivot
      · have hdiag := hU₁diag (i.pred hi)
        simpa [luFirstStepU, hi] using hdiag

/-- **Problem 9.14 / GEPP side**, a no-interchange partial-pivoting trace is
nonsingular.  The proof uses the locally constructed exact LU factors with
nonzero pivots, not a separate determinant assumption. -/
theorem higham9_7_PartialPivotNoInterchangeTrace_det_ne_zero
    {t n : ℕ} {A : Fin n → Fin n → ℝ}
    (htrace : higham9_7_PartialPivotNoInterchangeTrace t n A) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  obtain ⟨L, U, hLU, hUdiag⟩ :=
    higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec_pivots_ne_zero
      htrace
  exact (higham9_1_det_ne_zero_iff_pivots_ne_zero hLU).mpr hUdiag

/-- **Problem 9.14**, source-facing consequence: if `A` is pre-pivoted for
GEPP, then the no-interchange exact LU factorization exists.  The equality with
the §9.9 row-reversal method and pairwise pivoting remains a separate open
trace-equivalence target. -/
theorem higham_problem9_14_PrePivotedGEPP_exists_LUFactSpec {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∃ L U : Fin n → Fin n → ℝ, LUFactSpec n A L U :=
  higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec hpre

/-- **Problem 9.14 / GEPP side**, pre-pivoted GEPP supplies a nonsingular
exact no-pivot LU side.  This is a source-facing specialization of the
trace-level nonzero-pivot construction. -/
theorem higham_problem9_14_PrePivotedGEPP_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
  higham9_7_PartialPivotNoInterchangeTrace_det_ne_zero hpre

/-- **Problem 9.14 / same-LU bridge**, for a pre-pivoted input the exact LU
factorization of `A` is unique.  Hence any later source-faithful §9.9 or
pairwise-pivoting trace that is proved to return an exact `LUFactSpec` for the
same `A` must compute the same `L` and `U` as GEPP.  This theorem does not
assert that those row-reversal traces have already been constructed. -/
theorem higham_problem9_14_PrePivotedGEPP_lu_unique {n : ℕ}
    {A L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (hLU₁ : LUFactSpec n A L₁ U₁)
    (hLU₂ : LUFactSpec n A L₂ U₂) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  have hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
    higham_problem9_14_PrePivotedGEPP_det_ne_zero hpre
  exact higham9_1_lu_unique_of_pivots_ne_zero hLU₁ hLU₂
    ((higham9_1_det_ne_zero_iff_pivots_ne_zero hLU₁).mp hdet)

/-- **Problem 9.14 / same-LU bridge**, packaged source-facing form: a
pre-pivoted GEPP trace produces exact LU factors, and every other exact LU
certificate for `A` has exactly those factors.  This is the reusable final
bridge for the §9.9 and pairwise-pivoting trace-equivalence targets. -/
theorem higham_problem9_14_PrePivotedGEPP_exists_unique_LUFactSpec {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        ∀ {L' U' : Fin n → Fin n → ℝ},
          LUFactSpec n A L' U' → L' = L ∧ U' = U := by
  obtain ⟨L, U, hLU⟩ :=
    higham_problem9_14_PrePivotedGEPP_exists_LUFactSpec hpre
  refine ⟨L, U, hLU, ?_⟩
  intro L' U' hLU'
  exact higham_problem9_14_PrePivotedGEPP_lu_unique hpre hLU' hLU

/-- **Theorem 9.7 / trace bookkeeping**, the explicit stage counter in a
no-interchange partial-pivoting trace is only an index of the surrounding
algorithmic stage.  The same active-matrix trace can be reindexed to any
starting counter. -/
theorem higham9_7_PartialPivotNoInterchangeTrace_reindex_time :
    ∀ {t s n : ℕ} {A : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotNoInterchangeTrace t n A →
        higham9_7_PartialPivotNoInterchangeTrace s n A := by
  intro t s n
  induction n generalizing t s with
  | zero =>
      intro A _htrace
      exact higham9_7_PartialPivotNoInterchangeTrace.done
  | succ m ih =>
      intro A htrace
      cases htrace with
      | step hchoice hpivot hnext =>
          exact higham9_7_PartialPivotNoInterchangeTrace.step
            hchoice hpivot (ih (s := s + 1) hnext)

/-- **Problem 9.14 / recursive handoff**, a nonempty pre-pivoted GEPP trace
passes the same no-interchange property to the first Schur complement.  This
is the recursion gate used by the row-reversal/pairwise-pivoting bridge. -/
theorem higham_problem9_14_PrePivotedGEPP_firstSchurComplement {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    higham_problem9_14_PrePivotedGEPP (luFirstSchurComplement A) := by
  cases hpre with
  | step _hchoice _hpivot hnext =>
      exact higham9_7_PartialPivotNoInterchangeTrace_reindex_time hnext

/-- **Problem 9.14**, the row-reversal permutation `i ↦ n-1-i` used in the
source matrix `Π A`, where `Π = I(n:-1:1,:)`. -/
def higham_problem9_14_rowReversal {n : ℕ} (i : Fin n) : Fin n :=
  ⟨n - 1 - i.val, by
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    have hle : n - 1 - i.val ≤ n - 1 := Nat.sub_le (n - 1) i.val
    have hlt : n - 1 < n := Nat.sub_lt hn (by decide : 0 < 1)
    exact lt_of_le_of_lt hle hlt⟩

/-- **Problem 9.14**, row reversal is an involution. -/
theorem higham_problem9_14_rowReversal_involutive {n : ℕ} (i : Fin n) :
    higham_problem9_14_rowReversal (higham_problem9_14_rowReversal i) = i := by
  ext
  simp [higham_problem9_14_rowReversal]
  omega

/-- **Problem 9.14**, the row reversal is a permutation of the row index type. -/
theorem higham_problem9_14_rowReversal_isPermutation {n : ℕ} :
    Function.Bijective (higham_problem9_14_rowReversal (n := n)) := by
  constructor
  · intro x y hxy
    have h := congrArg (higham_problem9_14_rowReversal (n := n)) hxy
    simpa [higham_problem9_14_rowReversal_involutive x,
      higham_problem9_14_rowReversal_involutive y] using h
  · intro y
    exact ⟨higham_problem9_14_rowReversal y,
      higham_problem9_14_rowReversal_involutive y⟩

/-- **Problem 9.14**, row reversal sends the first row to the last row. -/
theorem higham_problem9_14_rowReversal_zero_eq_last {n : ℕ} (hn : 0 < n) :
    higham_problem9_14_rowReversal (⟨0, hn⟩ : Fin n) =
      ⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩ := by
  ext
  simp [higham_problem9_14_rowReversal]

/-- **Problem 9.14**, row reversal sends the last row to the first row. -/
theorem higham_problem9_14_rowReversal_last_eq_zero {n : ℕ} (hn : 0 < n) :
    higham_problem9_14_rowReversal
        (⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩ : Fin n) =
      ⟨0, hn⟩ := by
  ext
  simp [higham_problem9_14_rowReversal]

/-- **Problem 9.14**, the source row-reversed matrix `Π A`. -/
def higham_problem9_14_rowReversedMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  higham9_2_rowPermutedMatrix A higham_problem9_14_rowReversal

/-- **Problem 9.14**, applying the source row reversal twice returns the
original matrix. -/
theorem higham_problem9_14_rowReversedMatrix_involutive {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    higham_problem9_14_rowReversedMatrix
        (higham_problem9_14_rowReversedMatrix A) = A := by
  funext i j
  simp [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_rowReversal_involutive]

/-- **Problem 9.14**, row reversal preserves nonsingularity of the source
matrix.  This is the determinant side condition needed before running the
§9.9 row-reversal or pairwise-pivoting traces on `Π A`. -/
theorem higham_problem9_14_rowReversedMatrix_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham_problem9_14_rowReversedMatrix A) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  classical
  let e : Equiv.Perm (Fin n) :=
    Equiv.ofBijective higham_problem9_14_rowReversal
      higham_problem9_14_rowReversal_isPermutation
  have hdet_eq :
      Matrix.det
        (Matrix.of (higham_problem9_14_rowReversedMatrix A) :
          Matrix (Fin n) (Fin n) ℝ) =
        ((Equiv.Perm.sign e : ℤ) : ℝ) *
          Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
    have hperm :=
      Matrix.det_permute (R := ℝ) e
        (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
    simpa [e, higham_problem9_14_rowReversedMatrix,
      higham9_2_rowPermutedMatrix, Matrix.of_apply] using hperm
  rw [hdet_eq]
  have hsign : ((Equiv.Perm.sign e : ℤ) : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with hs | hs <;> simp [hs]
  exact mul_ne_zero hsign hdet

/-- **Problem 9.14**, if the original first row is a valid first partial pivot,
then the last row of the row-reversed matrix is a valid first partial pivot.
This is the first-column pivot fact needed by the §9.9 row-reversal and
pairwise-pivoting routes applied to `Π A`. -/
theorem higham_problem9_14_rowReversedMatrix_firstColumn_partialPivotChoice_last
    {n : ℕ} (hn : 0 < n) {A : Fin n → Fin n → ℝ}
    (hchoice :
      higham9_1_partialPivotChoice A (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)) :
    higham9_1_partialPivotChoice
      (higham_problem9_14_rowReversedMatrix A) (⟨0, hn⟩ : Fin n)
      (⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩ : Fin n) := by
  constructor
  · exact Nat.zero_le _
  · intro i _hi
    have hbase := hchoice.2 (higham_problem9_14_rowReversal i) (Nat.zero_le _)
    simpa [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
      higham_problem9_14_rowReversal_last_eq_zero hn] using hbase

/-- **Problem 9.14**, source-facing first-column consequence of pre-pivoting:
for a nonempty pre-pivoted input `A`, the row-reversed matrix `Π A` has its
first-column partial-pivot maximum in the last row, and that pivot is nonzero.
This does not prove the still-open §9.9 or pairwise-pivoting trace equivalence;
it records the first pivot fact those traces need. -/
theorem higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    higham9_1_partialPivotChoice
        (higham_problem9_14_rowReversedMatrix A) 0
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ∧
      higham_problem9_14_rowReversedMatrix A
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) 0 ≠ 0 := by
  cases hpre with
  | step hchoice hpivot _hnext =>
      have hchoice₀ :
          higham9_1_partialPivotChoice A
            (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))
            (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) := by
        simpa using hchoice
      constructor
      · simpa using
          higham_problem9_14_rowReversedMatrix_firstColumn_partialPivotChoice_last
            (n := m + 1) (Nat.succ_pos m) (A := A) hchoice₀
      · have hlast :
            higham_problem9_14_rowReversal
                (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) =
              (0 : Fin (m + 1)) := by
          ext
          simp [higham_problem9_14_rowReversal]
        simpa [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
          hlast] using hpivot

/-- **Problem 9.14 / pairwise pivoting**, two rows are adjacent when their
zero-based row indices differ by one.  This records the source restriction that
pairwise elimination uses only adjacent-row interchanges and operations. -/
def higham_problem9_14_adjacentRows {n : ℕ} (p q : Fin n) : Prop :=
  p.val + 1 = q.val ∨ q.val + 1 = p.val

/-- **Problem 9.14 / pairwise pivoting**, the adjacent-row schedule used to
bubble the final row of `ΠA` upward: at step `t`, the carried pivot row is at
zero-based row index `m - t` in an `(m+1)`-by-`(m+1)` matrix.  The definition
is total by saturating at row zero for `t > m`; the source trace uses only
steps `t < m`. -/
def higham_problem9_14_pairwiseBubbleRow {m : ℕ} (t : ℕ) : Fin (m + 1) :=
  ⟨m - t, Nat.lt_succ_of_le (Nat.sub_le m t)⟩

/-- **Problem 9.14 / pairwise pivoting**, the bubble schedule starts at the
last row of the row-reversed matrix. -/
@[simp] theorem higham_problem9_14_pairwiseBubbleRow_zero {m : ℕ} :
    higham_problem9_14_pairwiseBubbleRow (m := m) 0 =
      (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
  ext
  simp [higham_problem9_14_pairwiseBubbleRow]

/-- **Problem 9.14 / pairwise pivoting**, consecutive source bubble rows are
adjacent for every genuine step `t < m`. -/
theorem higham_problem9_14_pairwiseBubbleRows_adjacent {m t : ℕ}
    (ht : t < m) :
    higham_problem9_14_adjacentRows
      (higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1))
      (higham_problem9_14_pairwiseBubbleRow (m := m) t) := by
  left
  simp [higham_problem9_14_pairwiseBubbleRow]
  omega

/-- **Problem 9.14 / pairwise pivoting**, consecutive source bubble rows are
distinct for every genuine step `t < m`. -/
theorem higham_problem9_14_pairwiseBubbleRows_distinct {m t : ℕ}
    (ht : t < m) :
    higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1) ≠
      higham_problem9_14_pairwiseBubbleRow (m := m) t := by
  intro h
  have hval := congrArg Fin.val h
  simp [higham_problem9_14_pairwiseBubbleRow] at hval
  omega

/-- **Problem 9.14 / pairwise pivoting**, consecutive source bubble rows move
strictly upward through the row-reversed matrix for every genuine step. -/
theorem higham_problem9_14_pairwiseBubbleRow_succ_val_lt {m t : ℕ}
    (ht : t < m) :
    (higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1)).val <
      (higham_problem9_14_pairwiseBubbleRow (m := m) t).val := by
  simp [higham_problem9_14_pairwiseBubbleRow]
  omega

/-- **Problem 9.14 / pairwise pivoting**, after the scheduled bubble has run
for `m` genuine steps in an `(m+1)`-by-`(m+1)` matrix, the carried row index is
row zero. -/
@[simp] theorem higham_problem9_14_pairwiseBubbleRow_self {m : ℕ} :
    higham_problem9_14_pairwiseBubbleRow (m := m) m = (0 : Fin (m + 1)) := by
  ext
  simp [higham_problem9_14_pairwiseBubbleRow]

/-- **Problem 9.14 / pairwise pivoting**, source row represented by an
already-eliminated row in the adjacent bubble.  Row `r = 1` stores the Schur
update of the original last row, row `r = 2` stores the next one, and so on.
The row-zero value is a harmless totalization; the theorem using this map only
applies it to rows strictly below the carried pivot. -/
def higham_problem9_14_pairwiseBubbleSourceRow {m : ℕ}
    (r : Fin (m + 1)) : Fin (m + 1) :=
  ⟨m - (r.val - 1), Nat.lt_succ_of_le (Nat.sub_le m (r.val - 1))⟩

/-- **Problem 9.14 / pairwise pivoting**, on a trailing row `i.succ`, the
source-row map agrees with row reversal of the first Schur-complement index. -/
theorem higham_problem9_14_pairwiseBubbleSourceRow_succ {m : ℕ}
    (i : Fin m) :
    higham_problem9_14_pairwiseBubbleSourceRow (m := m) i.succ =
      Fin.succ (higham_problem9_14_rowReversal i) := by
  ext
  simp [higham_problem9_14_pairwiseBubbleSourceRow,
    higham_problem9_14_rowReversal]
  omega

/-- **Problem 9.14 / pairwise pivoting**, the row interchange between the two
rows of a pair.  The source pairwise method restricts such swaps to adjacent
rows, recorded separately by `higham_problem9_14_adjacentRows`. -/
def higham_problem9_14_pairRowSwap {n : ℕ} (p q : Fin n) : Fin n → Fin n :=
  Equiv.swap p q

/-- **Problem 9.14 / pairwise pivoting**, the pair row swap sends the left
row of the pair to the right row. -/
theorem higham_problem9_14_pairRowSwap_left {n : ℕ} (p q : Fin n) :
    higham_problem9_14_pairRowSwap p q p = q := by
  simp [higham_problem9_14_pairRowSwap]

/-- **Problem 9.14 / pairwise pivoting**, the pair row swap sends the right
row of the pair to the left row. -/
theorem higham_problem9_14_pairRowSwap_right {n : ℕ} (p q : Fin n) :
    higham_problem9_14_pairRowSwap p q q = p := by
  simp [higham_problem9_14_pairRowSwap]

/-- **Problem 9.14 / pairwise pivoting**, the pair row swap is an involution. -/
theorem higham_problem9_14_pairRowSwap_involutive {n : ℕ} (p q : Fin n) :
    Function.Involutive (higham_problem9_14_pairRowSwap p q) := by
  intro i
  simp [higham_problem9_14_pairRowSwap]

/-- **Problem 9.14 / pairwise pivoting**, the pair row swap is a permutation of
the row index type. -/
theorem higham_problem9_14_pairRowSwap_isPermutation {n : ℕ} (p q : Fin n) :
    Function.Bijective (higham_problem9_14_pairRowSwap p q) :=
  (Equiv.swap p q).bijective

/-- **Problem 9.14 / pairwise pivoting**, a pair row swap preserves
nonsingularity.  This is the determinant side condition needed for adjacent
row interchanges in a pairwise-pivoting trace. -/
theorem higham_problem9_14_pairRowSwap_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p q : Fin n)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham9_2_rowPermutedMatrix A
        (higham_problem9_14_pairRowSwap p q)) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  classical
  let e : Equiv.Perm (Fin n) := Equiv.swap p q
  have hdet_eq :
      Matrix.det
        (Matrix.of (higham9_2_rowPermutedMatrix A
          (higham_problem9_14_pairRowSwap p q)) :
          Matrix (Fin n) (Fin n) ℝ) =
        ((Equiv.Perm.sign e : ℤ) : ℝ) *
          Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
    have hperm :=
      Matrix.det_permute (R := ℝ) e
        (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
    simpa [e, higham_problem9_14_pairRowSwap, higham9_2_rowPermutedMatrix,
      Matrix.of_apply] using hperm
  rw [hdet_eq]
  have hsign : ((Equiv.Perm.sign e : ℤ) : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with hs | hs <;> simp [hs]
  exact mul_ne_zero hsign hdet

/-- **Problem 9.14 / pairwise pivoting**, the natural two-row pivoting choice:
from rows `p` and `q`, choose one of them whose active-column entry has maximal
absolute value among the pair. -/
def higham_problem9_14_pairPivotChoice {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q r : Fin n) : Prop :=
  (r = p ∨ r = q) ∧ |A p k| ≤ |A r k| ∧ |A q k| ≤ |A r k|

/-- **Problem 9.14 / pairwise pivoting**, the natural two-row pivot choice
exists for every pair of candidate rows. -/
theorem higham_problem9_14_exists_pairPivotChoice {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    ∃ r : Fin n, higham_problem9_14_pairPivotChoice A k p q r := by
  by_cases hpq : |A p k| ≤ |A q k|
  · exact ⟨q, Or.inr rfl, hpq, le_rfl⟩
  · have hqp : |A q k| ≤ |A p k| := le_of_lt (lt_of_not_ge hpq)
    exact ⟨p, Or.inl rfl, le_rfl, hqp⟩

/-- **Problem 9.14 / pairwise pivoting**, the deterministic natural two-row
pivot selector: choose `q` if its active-column entry is at least as large as
that of `p`, and choose `p` otherwise. -/
noncomputable def higham_problem9_14_pairPivotRow {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) : Fin n :=
  if |A p k| ≤ |A q k| then q else p

/-- **Problem 9.14 / pairwise pivoting**, the deterministic natural two-row
pivot selector satisfies the pairwise pivot-choice predicate. -/
theorem higham_problem9_14_pairPivotRow_choice {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    higham_problem9_14_pairPivotChoice A k p q
      (higham_problem9_14_pairPivotRow A k p q) := by
  unfold higham_problem9_14_pairPivotRow
  by_cases hpq : |A p k| ≤ |A q k|
  · simp [hpq, higham_problem9_14_pairPivotChoice]
  · have hqp : |A q k| ≤ |A p k| := le_of_lt (lt_of_not_ge hpq)
    simp [hpq, hqp, higham_problem9_14_pairPivotChoice]

/-- **Problem 9.14 / pairwise pivoting**, the deterministic natural two-row
pivot selector chooses the right row when its active-column entry is at least
as large as the left row's entry. -/
theorem higham_problem9_14_pairPivotRow_eq_right_of_abs_le {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (h : |A p k| ≤ |A q k|) :
    higham_problem9_14_pairPivotRow A k p q = q := by
  simp [higham_problem9_14_pairPivotRow, h]

/-- **Problem 9.14 / pairwise pivoting**, the deterministic natural two-row
pivot selector chooses the left row when its active-column entry is strictly
larger than the right row's entry. -/
theorem higham_problem9_14_pairPivotRow_eq_left_of_abs_gt {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (h : |A q k| < |A p k|) :
    higham_problem9_14_pairPivotRow A k p q = p := by
  have hpq : ¬ |A p k| ≤ |A q k| := not_le.mpr h
  simp [higham_problem9_14_pairPivotRow, hpq]

/-- **Problem 9.14 / pairwise pivoting**, when the right row is a first-column
partial-pivot maximum, the deterministic natural pairwise rule selects it
against any left row.  The right-favoring tie break matches the local
source-facing convention used for the §9.9 row-reversal route. -/
theorem higham_problem9_14_pairPivotRow_eq_right_of_firstColumn_partialPivotChoice
    {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    {p q : Fin (m + 1)}
    (hchoice : higham9_1_partialPivotChoice A 0 q) :
    higham_problem9_14_pairPivotRow A 0 p q = q := by
  exact higham_problem9_14_pairPivotRow_eq_right_of_abs_le A
    (hchoice.2 p (Nat.zero_le _))

/-- **Problem 9.14**, for a pre-pivoted input `A`, the first-column natural
pairwise rule on the row-reversed matrix `Π A` selects the last row whenever
that last row is the right member of the compared pair.  This is a local
deterministic-selector dependency for the still-open §9.9/pairwise trace
equivalence. -/
theorem higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (p : Fin (m + 1)) :
    higham_problem9_14_pairPivotRow
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) =
      (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
  exact
    higham_problem9_14_pairPivotRow_eq_right_of_firstColumn_partialPivotChoice
      (higham_problem9_14_rowReversedMatrix A)
      (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
        hpre).1

/-- **Problem 9.14 / pairwise pivoting**, row permutation that moves the
deterministically chosen pair pivot into the left member `p` of the pair.  If
the left row is already chosen, it is the identity; otherwise it swaps the two
pair rows. -/
noncomputable def higham_problem9_14_pairPivotToLeftSwap {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) : Fin n → Fin n :=
  if higham_problem9_14_pairPivotRow A k p q = p then id
  else higham_problem9_14_pairRowSwap p q

/-- **Problem 9.14 / pairwise pivoting**, after the pair pivot-to-left swap,
the left row maps to the deterministic pair pivot row. -/
theorem higham_problem9_14_pairPivotToLeftSwap_left {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    higham_problem9_14_pairPivotToLeftSwap A k p q p =
    higham_problem9_14_pairPivotRow A k p q := by
  unfold higham_problem9_14_pairPivotToLeftSwap
  by_cases hp : higham_problem9_14_pairPivotRow A k p q = p
  · simp [hp]
  · have hq : higham_problem9_14_pairPivotRow A k p q = q := by
      rcases (higham_problem9_14_pairPivotRow_choice A k p q).1 with hleft | hright
      · exact (hp hleft).elim
      · exact hright
    by_cases hqp : q = p
    · exact (hp (hq.trans hqp)).elim
    · simp [hq, hqp, higham_problem9_14_pairRowSwap_left]

/-- **Problem 9.14 / pairwise pivoting**, the pivot-to-left row map is a
permutation of the row index type. -/
theorem higham_problem9_14_pairPivotToLeftSwap_isPermutation {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    Function.Bijective
      (higham_problem9_14_pairPivotToLeftSwap A k p q) := by
  unfold higham_problem9_14_pairPivotToLeftSwap
  by_cases hp : higham_problem9_14_pairPivotRow A k p q = p
  · simp [hp]
  · simpa [hp] using higham_problem9_14_pairRowSwap_isPermutation p q

/-- **Problem 9.14 / pairwise pivoting**, the pair-pivoted two-row matrix:
rows are permuted so that the deterministic pivot of the pair occupies the
left row. -/
noncomputable def higham_problem9_14_pairPivotToLeftMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    Fin n → Fin n → ℝ :=
  higham9_2_rowPermutedMatrix A
    (higham_problem9_14_pairPivotToLeftSwap A k p q)

/-- **Problem 9.14 / pairwise pivoting**, in the pair-pivoted matrix, the left
row is exactly the deterministically chosen pair pivot row of the original
matrix. -/
theorem higham_problem9_14_pairPivotToLeftMatrix_left {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q j : Fin n) :
    higham_problem9_14_pairPivotToLeftMatrix A k p q p j =
      A (higham_problem9_14_pairPivotRow A k p q) j := by
  simp [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_pairPivotToLeftSwap_left]

/-- **Problem 9.14 / pairwise pivoting**, pair pivot-to-left row permutation
preserves nonsingularity. -/
theorem higham_problem9_14_pairPivotToLeftMatrix_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham_problem9_14_pairPivotToLeftMatrix A k p q) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  unfold higham_problem9_14_pairPivotToLeftMatrix
  unfold higham_problem9_14_pairPivotToLeftSwap
  by_cases hp : higham_problem9_14_pairPivotRow A k p q = p
  · simpa [hp, higham9_2_rowPermutedMatrix] using hdet
  · simpa [hp] using higham_problem9_14_pairRowSwap_det_ne_zero A p q hdet

/-- **Problem 9.14 / pairwise pivoting**, the natural two-row pivot rule bounds
the multiplier for either row in the pair by one, provided the chosen pivot is
nonzero. -/
theorem higham_problem9_14_pairPivotChoice_multiplier_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} {k p q r i : Fin n}
    (hchoice : higham_problem9_14_pairPivotChoice A k p q r)
    (hpivot : A r k ≠ 0) (hi : i = p ∨ i = q) :
    |A i k / A r k| ≤ 1 := by
  have hbound : |A i k| ≤ |A r k| := by
    rcases hi with rfl | rfl
    · exact hchoice.2.1
    · exact hchoice.2.2
  have hpiv_abs_pos : 0 < |A r k| := abs_pos.mpr hpivot
  rw [abs_div]
  rw [div_le_iff₀ hpiv_abs_pos]
  simpa using hbound

/-- **Problem 9.14 / pairwise pivoting**, left-row multiplier bound for the
natural two-row pivot rule. -/
theorem higham_problem9_14_pairPivotChoice_left_multiplier_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} {k p q r : Fin n}
    (hchoice : higham_problem9_14_pairPivotChoice A k p q r)
    (hpivot : A r k ≠ 0) :
    |A p k / A r k| ≤ 1 :=
  higham_problem9_14_pairPivotChoice_multiplier_abs_le_one hchoice hpivot
    (Or.inl rfl)

/-- **Problem 9.14 / pairwise pivoting**, right-row multiplier bound for the
natural two-row pivot rule. -/
theorem higham_problem9_14_pairPivotChoice_right_multiplier_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} {k p q r : Fin n}
    (hchoice : higham_problem9_14_pairPivotChoice A k p q r)
    (hpivot : A r k ≠ 0) :
    |A q k / A r k| ≤ 1 :=
  higham_problem9_14_pairPivotChoice_multiplier_abs_le_one hchoice hpivot
    (Or.inr rfl)

/-- **Problem 9.14 / pairwise pivoting**, left-row multiplier bound for the
deterministic natural two-row pivot selector. -/
theorem higham_problem9_14_pairPivotRow_left_multiplier_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} {k p q : Fin n}
    (hpivot : A (higham_problem9_14_pairPivotRow A k p q) k ≠ 0) :
    |A p k / A (higham_problem9_14_pairPivotRow A k p q) k| ≤ 1 :=
  higham_problem9_14_pairPivotChoice_left_multiplier_abs_le_one
    (higham_problem9_14_pairPivotRow_choice A k p q) hpivot

/-- **Problem 9.14 / pairwise pivoting**, right-row multiplier bound for the
deterministic natural two-row pivot selector. -/
theorem higham_problem9_14_pairPivotRow_right_multiplier_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} {k p q : Fin n}
    (hpivot : A (higham_problem9_14_pairPivotRow A k p q) k ≠ 0) :
    |A q k / A (higham_problem9_14_pairPivotRow A k p q) k| ≤ 1 :=
  higham_problem9_14_pairPivotChoice_right_multiplier_abs_le_one
    (higham_problem9_14_pairPivotRow_choice A k p q) hpivot

/-- **Problem 9.14 / pairwise pivoting**, the exact row operation that zeros
the active-column entry of `target` using `pivot`.  This is the local
element-zeroing primitive for pairwise elimination; the pair/adjacency and
pivot-choice hypotheses are supplied by the trace that uses it. -/
noncomputable def higham_problem9_14_pairEliminateRow {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k pivot target : Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = target then
      A target j - (A target k / A pivot k) * A pivot j
    else
      A i j

/-- **Problem 9.14 / pairwise pivoting**, the eliminated target row has the
expected row-operation formula. -/
theorem higham_problem9_14_pairEliminateRow_target {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k pivot target j : Fin n) :
    higham_problem9_14_pairEliminateRow A k pivot target target j =
      A target j - (A target k / A pivot k) * A pivot j := by
  simp [higham_problem9_14_pairEliminateRow]

/-- **Problem 9.14 / pairwise pivoting**, rows other than the eliminated target
are unchanged by the pairwise row operation. -/
theorem higham_problem9_14_pairEliminateRow_of_ne {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k pivot target i j : Fin n}
    (hi : i ≠ target) :
    higham_problem9_14_pairEliminateRow A k pivot target i j = A i j := by
  simp [higham_problem9_14_pairEliminateRow, hi]

/-- **Problem 9.14 / pairwise pivoting**, the pivot row is unchanged when it is
distinct from the target row. -/
theorem higham_problem9_14_pairEliminateRow_pivot {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k pivot target j : Fin n}
    (hpt : pivot ≠ target) :
    higham_problem9_14_pairEliminateRow A k pivot target pivot j =
      A pivot j :=
  higham_problem9_14_pairEliminateRow_of_ne A hpt

/-- **Problem 9.14 / pairwise pivoting**, the pairwise row operation zeros the
target's active-column entry when the chosen pivot is nonzero. -/
theorem higham_problem9_14_pairEliminateRow_target_active_eq_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k pivot target : Fin n}
    (hpivot : A pivot k ≠ 0) :
    higham_problem9_14_pairEliminateRow A k pivot target target k = 0 := by
  simp [higham_problem9_14_pairEliminateRow]
  field_simp [hpivot]
  ring

/-- **Problem 9.14 / pairwise pivoting**, the pairwise row operation is the
standard determinant-preserving row update: replace `target` by itself plus a
multiple of the distinct pivot row. -/
theorem higham_problem9_14_pairEliminateRow_eq_updateRow_add_smul {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k pivot target : Fin n) :
    (Matrix.of (higham_problem9_14_pairEliminateRow A k pivot target) :
        Matrix (Fin n) (Fin n) ℝ) =
      (Matrix.of A : Matrix (Fin n) (Fin n) ℝ).updateRow target
        ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ) target +
          (-(A target k / A pivot k)) •
            (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) pivot) := by
  ext i j
  by_cases hi : i = target
  · subst hi
    simp [higham_problem9_14_pairEliminateRow, sub_eq_add_neg]
  · simp [higham_problem9_14_pairEliminateRow, Matrix.updateRow_apply, hi]

/-- **Problem 9.14 / pairwise pivoting**, the exact pairwise elimination row
operation preserves the determinant when pivot and target rows are distinct. -/
theorem higham_problem9_14_pairEliminateRow_det_eq {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k pivot target : Fin n}
    (hpt : target ≠ pivot) :
    Matrix.det
        (Matrix.of (higham_problem9_14_pairEliminateRow A k pivot target) :
          Matrix (Fin n) (Fin n) ℝ) =
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
  rw [higham_problem9_14_pairEliminateRow_eq_updateRow_add_smul]
  exact Matrix.det_updateRow_add_smul_self
    (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) hpt
    (-(A target k / A pivot k))

/-- **Problem 9.14 / pairwise pivoting**, a pairwise elimination row operation
preserves nonsingularity when pivot and target rows are distinct. -/
theorem higham_problem9_14_pairEliminateRow_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k pivot target : Fin n}
    (hpt : target ≠ pivot)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
        (Matrix.of (higham_problem9_14_pairEliminateRow A k pivot target) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  simpa [higham_problem9_14_pairEliminateRow_det_eq A hpt] using hdet

/-! ### Problem 9.14, first method from §9.9 -/

/-- **Problem 9.14 / first §9.9 method**, the zero-based target row for the
first method in §9.9.  At first-stage step `t`, the source method zeros row
`t+1`, corresponding to book rows `2,3,...,n`.  The definition is totalized
with `min` outside the meaningful range `t < m`. -/
def higham_problem9_14_firstMethodTarget {m : ℕ} (t : ℕ) : Fin (m + 1) :=
  ⟨min (t + 1) m, Nat.lt_succ_of_le (Nat.min_le_right (t + 1) m)⟩

/-- **Problem 9.14 / first §9.9 method**, target-row value in the meaningful
range of the first-stage source schedule. -/
@[simp] theorem higham_problem9_14_firstMethodTarget_val {m t : ℕ}
    (ht : t < m) :
    (higham_problem9_14_firstMethodTarget (m := m) t).val = t + 1 := by
  have hle : t + 1 ≤ m := Nat.succ_le_iff.mpr ht
  simp [higham_problem9_14_firstMethodTarget, Nat.min_eq_left hle]

/-- **Problem 9.14 / first §9.9 method**, a genuine first-method target row is
not the pivot row. -/
theorem higham_problem9_14_firstMethodTarget_ne_zero {m t : ℕ}
    (ht : t < m) :
    higham_problem9_14_firstMethodTarget (m := m) t ≠
      (0 : Fin (m + 1)) := by
  intro h
  have hval := congrArg Fin.val h
  rw [higham_problem9_14_firstMethodTarget_val ht] at hval
  simp at hval

/-- **Problem 9.14 / first §9.9 method**, recursive exact first-stage matrix
state for the first method described in §9.9, applied to the original
pre-pivoted matrix `A`.  Step `t+1` zeros the first-column entry in row `t+1`
using row zero.  Under the pre-pivoted hypothesis, no row interchange is
needed, and the multiplier bound is proved below. -/
noncomputable def higham_problem9_14_firstMethodMatrix {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ℕ → Fin (m + 1) → Fin (m + 1) → ℝ
  | 0 => A
  | t + 1 =>
      higham_problem9_14_pairEliminateRow
        (higham_problem9_14_firstMethodMatrix A t) 0 0
        (higham_problem9_14_firstMethodTarget (m := m) t)

/-- **Problem 9.14 / first §9.9 method**, the first-method matrix starts from
the original matrix `A`. -/
@[simp] theorem higham_problem9_14_firstMethodMatrix_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_firstMethodMatrix A 0 = A := rfl

/-- **Problem 9.14 / first §9.9 method**, unfolding one scheduled first-method
row-zeroing step. -/
theorem higham_problem9_14_firstMethodMatrix_succ {m t : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_firstMethodMatrix A (t + 1) =
      higham_problem9_14_pairEliminateRow
        (higham_problem9_14_firstMethodMatrix A t) 0 0
        (higham_problem9_14_firstMethodTarget (m := m) t) := rfl

/-- **Problem 9.14 / first §9.9 method**, source-facing trace predicate for
the first §9.9 method.  The initial state is `A`; each genuine first-stage
step zeros the next row `2,3,...,n` using row zero.  The multiplier-bounded
property for pre-pivoted inputs is proved separately instead of being assumed
as a trace field. -/
inductive higham_problem9_14_FirstMethodTrace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ℕ → (Fin (m + 1) → Fin (m + 1) → ℝ) → Prop
  | init :
      higham_problem9_14_FirstMethodTrace A 0 A
  | step {t : ℕ} {B : Fin (m + 1) → Fin (m + 1) → ℝ}
      (ht : t < m)
      (htrace : higham_problem9_14_FirstMethodTrace A t B) :
      higham_problem9_14_FirstMethodTrace A (t + 1)
        (higham_problem9_14_pairEliminateRow B 0 0
          (higham_problem9_14_firstMethodTarget (m := m) t))

/-- **Problem 9.14 / first §9.9 method**, the recursive first-method matrix is
a valid source-facing trace at every prefix `t <= m`. -/
theorem higham_problem9_14_firstMethodMatrix_trace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ∀ t : ℕ, t ≤ m →
      higham_problem9_14_FirstMethodTrace A t
        (higham_problem9_14_firstMethodMatrix A t) := by
  intro t
  induction t with
  | zero =>
      intro _ht
      exact higham_problem9_14_FirstMethodTrace.init
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      simpa [higham_problem9_14_firstMethodMatrix_succ] using
        higham_problem9_14_FirstMethodTrace.step ht (ih ht_le)

/-- **Problem 9.14 / first §9.9 method**, terminal trace for the first-stage
schedule. -/
theorem higham_problem9_14_firstMethodMatrix_terminal_trace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_FirstMethodTrace A m
      (higham_problem9_14_firstMethodMatrix A m) :=
  higham_problem9_14_firstMethodMatrix_trace A m le_rfl

/-- **Problem 9.14 / first §9.9 method**, every scheduled first-method prefix
preserves nonsingularity. -/
theorem higham_problem9_14_firstMethodMatrix_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet : Matrix.det
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∀ t : ℕ, t ≤ m →
      Matrix.det
        (Matrix.of (higham_problem9_14_firstMethodMatrix A t) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
  intro t
  induction t with
  | zero =>
      intro _ht
      simpa [higham_problem9_14_firstMethodMatrix_zero] using hdet
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      have htarget :
          higham_problem9_14_firstMethodTarget (m := m) t ≠
            (0 : Fin (m + 1)) :=
        higham_problem9_14_firstMethodTarget_ne_zero (m := m) (t := t) ht
      simpa [higham_problem9_14_firstMethodMatrix_succ] using
        higham_problem9_14_pairEliminateRow_det_ne_zero
          (A := higham_problem9_14_firstMethodMatrix A t)
          (k := 0) (pivot := (0 : Fin (m + 1)))
          (target := higham_problem9_14_firstMethodTarget (m := m) t)
          htarget (ih ht_le)

/-- **Problem 9.14 / first §9.9 method**, prefix invariant for a pre-pivoted
input.  After `t` first-method steps, row zero is still the original first row
of `A`; rows `1..t` are exactly their first-column Schur updates by row zero;
rows below the prefix are unchanged and remain dominated by row zero in the
active column. -/
theorem higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_prefix_invariant
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∀ t : ℕ, t ≤ m →
      (∀ j : Fin (m + 1),
        higham_problem9_14_firstMethodMatrix A t 0 j = A 0 j) ∧
      higham_problem9_14_firstMethodMatrix A t 0 0 ≠ 0 ∧
      (∀ r : Fin (m + 1), 0 < r.val → r.val ≤ t →
        ∀ j : Fin (m + 1),
          higham_problem9_14_firstMethodMatrix A t r j =
            A r j - (A r 0 / A 0 0) * A 0 j) ∧
      (∀ r : Fin (m + 1), t < r.val →
        ∀ j : Fin (m + 1),
          higham_problem9_14_firstMethodMatrix A t r j = A r j) ∧
      (∀ r : Fin (m + 1), t < r.val →
        |higham_problem9_14_firstMethodMatrix A t r 0| ≤
          |higham_problem9_14_firstMethodMatrix A t 0 0|) := by
  have hchoiceA : higham9_1_partialPivotChoice A 0 0 := by
    cases hpre with
    | step hchoice _hpivot _hnext =>
        simpa using hchoice
  have hpivA : A 0 0 ≠ 0 := by
    cases hpre with
    | step _hchoice hpivot _hnext =>
        exact hpivot
  intro t
  induction t with
  | zero =>
      intro _ht
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j
        simp [higham_problem9_14_firstMethodMatrix_zero]
      · simpa [higham_problem9_14_firstMethodMatrix_zero] using hpivA
      · intro r _hrpos hrle _j
        omega
      · intro r _hr j
        simp [higham_problem9_14_firstMethodMatrix_zero]
      · intro r _hr
        simpa [higham_problem9_14_firstMethodMatrix_zero] using
          hchoiceA.2 r (Nat.zero_le _)
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      rcases ih ht_le with
        ⟨hpivotRow, hpivot_ne, helim, hunchanged, _hdom⟩
      let q : Fin (m + 1) :=
        higham_problem9_14_firstMethodTarget (m := m) t
      have hqval : q.val = t + 1 := by
        simpa [q] using
          higham_problem9_14_firstMethodTarget_val (m := m) (t := t) ht
      have hq_ne_zero : q ≠ (0 : Fin (m + 1)) := by
        simpa [q] using
          higham_problem9_14_firstMethodTarget_ne_zero (m := m) (t := t) ht
      have hzero_ne_q : (0 : Fin (m + 1)) ≠ q := Ne.symm hq_ne_zero
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j
        rw [higham_problem9_14_firstMethodMatrix_succ]
        have hrow :=
          higham_problem9_14_pairEliminateRow_pivot
            (A := higham_problem9_14_firstMethodMatrix A t)
            (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
            (j := j) hzero_ne_q
        simpa [q] using hrow.trans (hpivotRow j)
      · rw [higham_problem9_14_firstMethodMatrix_succ]
        have hrow :=
          higham_problem9_14_pairEliminateRow_pivot
            (A := higham_problem9_14_firstMethodMatrix A t)
            (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
            (j := (0 : Fin (m + 1))) hzero_ne_q
        simpa [q, hrow] using hpivot_ne
      · intro r hrpos hrle j
        by_cases hrq : r = q
        · subst r
          rw [higham_problem9_14_firstMethodMatrix_succ]
          have htarget :=
            higham_problem9_14_pairEliminateRow_target
              (higham_problem9_14_firstMethodMatrix A t)
              (0 : Fin (m + 1)) (0 : Fin (m + 1)) q j
          rw [htarget]
          have hq_old :
              higham_problem9_14_firstMethodMatrix A t q j = A q j :=
            hunchanged q (by omega) j
          have hq_active :
              higham_problem9_14_firstMethodMatrix A t q 0 = A q 0 :=
            hunchanged q (by omega) 0
          rw [hq_old, hq_active, hpivotRow j, hpivotRow (0 : Fin (m + 1))]
        · have hr_val_ne : r.val ≠ t + 1 := by
            intro hv
            exact hrq (Fin.ext (by rw [hv, hqval]))
          have hrle_t : r.val ≤ t := by omega
          rw [higham_problem9_14_firstMethodMatrix_succ]
          have hsame :=
            higham_problem9_14_pairEliminateRow_of_ne
              (A := higham_problem9_14_firstMethodMatrix A t)
              (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
              (i := r) (j := j) hrq
          rw [hsame]
          exact helim r hrpos hrle_t j
      · intro r hr j
        have hrq : r ≠ q := by
          intro h
          have hval := congrArg Fin.val h
          omega
        rw [higham_problem9_14_firstMethodMatrix_succ]
        have hsame :=
          higham_problem9_14_pairEliminateRow_of_ne
            (A := higham_problem9_14_firstMethodMatrix A t)
            (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
            (i := r) (j := j) hrq
        rw [hsame]
        exact hunchanged r (by omega) j
      · intro r hr
        have hrq : r ≠ q := by
          intro h
          have hval := congrArg Fin.val h
          omega
        have hr_step :
            higham_problem9_14_firstMethodMatrix A (t + 1) r
                (0 : Fin (m + 1)) =
              A r 0 := by
          rw [higham_problem9_14_firstMethodMatrix_succ]
          have hsame :=
            higham_problem9_14_pairEliminateRow_of_ne
              (A := higham_problem9_14_firstMethodMatrix A t)
              (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
              (i := r) (j := (0 : Fin (m + 1))) hrq
          rw [hsame]
          exact hunchanged r (by omega) 0
        have hp_step :
            higham_problem9_14_firstMethodMatrix A (t + 1) 0
                (0 : Fin (m + 1)) =
              A 0 0 := by
          rw [higham_problem9_14_firstMethodMatrix_succ]
          have hrow :=
            higham_problem9_14_pairEliminateRow_pivot
              (A := higham_problem9_14_firstMethodMatrix A t)
              (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
              (j := (0 : Fin (m + 1))) hzero_ne_q
          simpa [q] using hrow.trans (hpivotRow (0 : Fin (m + 1)))
        calc
          |higham_problem9_14_firstMethodMatrix A (t + 1) r
              (0 : Fin (m + 1))|
              = |A r 0| := by rw [hr_step]
          _ ≤ |A 0 0| := hchoiceA.2 r (Nat.zero_le _)
          _ = |higham_problem9_14_firstMethodMatrix A (t + 1) 0
              (0 : Fin (m + 1))| := by rw [hp_step]

/-- **Problem 9.14 / first §9.9 method**, the multipliers used by the first
method on a pre-pivoted input are bounded by one at every first-stage step. -/
theorem higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_multiplier_abs_le_one
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) {t : ℕ} (ht : t < m) :
    |higham_problem9_14_firstMethodMatrix A t
        (higham_problem9_14_firstMethodTarget (m := m) t) 0 /
      higham_problem9_14_firstMethodMatrix A t 0 0| ≤ 1 := by
  have hinv :=
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_prefix_invariant
      (A := A) hpre t (Nat.le_of_lt ht)
  have hqval :
      (higham_problem9_14_firstMethodTarget (m := m) t).val = t + 1 :=
    higham_problem9_14_firstMethodTarget_val (m := m) (t := t) ht
  have hdom :=
    hinv.2.2.2.2
      (higham_problem9_14_firstMethodTarget (m := m) t)
      (by omega)
  have hpiv_abs : 0 < |higham_problem9_14_firstMethodMatrix A t 0 0| :=
    abs_pos.mpr hinv.2.1
  rw [abs_div]
  rw [div_le_iff₀ hpiv_abs]
  simpa [mul_one] using hdom

/-- **Problem 9.14 / first §9.9 method**, terminal trailing block of the
first-method first stage is exactly the first Schur complement of `A`. -/
theorem
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_terminal_trailing_eq_firstSchurComplement
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (i j : Fin m) :
    higham_problem9_14_firstMethodMatrix A m i.succ j.succ =
      luFirstSchurComplement A i j := by
  have hinv :=
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_prefix_invariant
      (A := A) hpre m le_rfl
  have hpos : 0 < (i.succ : Fin (m + 1)).val := by simp
  have hle : (i.succ : Fin (m + 1)).val ≤ m := by
    exact Nat.succ_le_iff.mpr i.isLt
  have hrow := hinv.2.2.1 i.succ hpos hle j.succ
  simpa [luFirstSchurComplement, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using hrow

/-- **Problem 9.14 / first §9.9 method**, terminal Schur-complement form:
after the first §9.9 method completes its first-stage row-zeroing schedule,
the first Schur complement of the terminal matrix is the first Schur
complement of the original pre-pivoted input. -/
theorem
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_terminal_firstSchurComplement
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    luFirstSchurComplement (higham_problem9_14_firstMethodMatrix A m) =
      luFirstSchurComplement A := by
  funext i j
  unfold luFirstSchurComplement
  have htrail :=
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_terminal_trailing_eq_firstSchurComplement
      (A := A) hpre i j
  have hinv :=
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_prefix_invariant
      (A := A) hpre m le_rfl
  have hpos : 0 < (i.succ : Fin (m + 1)).val := by simp
  have hle : (i.succ : Fin (m + 1)).val ≤ m := by
    exact Nat.succ_le_iff.mpr i.isLt
  have hzero_row := hinv.2.2.1 i.succ hpos hle (0 : Fin (m + 1))
  have hpiv : A 0 0 ≠ 0 := by
    cases hpre with
    | step _hchoice hpivot _hnext =>
        exact hpivot
  have hzero :
      higham_problem9_14_firstMethodMatrix A m i.succ (0 : Fin (m + 1)) = 0 := by
    rw [hzero_row]
    field_simp [hpiv]
    ring
  rw [htrail, hzero]
  simp [luFirstSchurComplement, div_eq_mul_inv, mul_assoc]

/-- **Problem 9.14 / first §9.9 method**, recursive trace certificate for the
first method.  At each nonempty stage, the method runs the source first-stage
row-zeroing schedule on the current active matrix and recurses on the usual
first Schur complement. -/
inductive higham_problem9_14_RecursiveFirstMethodTrace :
    (n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | done {A : Fin 0 → Fin 0 → ℝ} :
      higham_problem9_14_RecursiveFirstMethodTrace 0 A
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      (hstage :
        higham_problem9_14_FirstMethodTrace A m
          (higham_problem9_14_firstMethodMatrix A m))
      (hmult :
        ∀ t : ℕ, t < m →
          |higham_problem9_14_firstMethodMatrix A t
              (higham_problem9_14_firstMethodTarget (m := m) t) 0 /
            higham_problem9_14_firstMethodMatrix A t 0 0| ≤ 1)
      (hschur :
        luFirstSchurComplement (higham_problem9_14_firstMethodMatrix A m) =
          luFirstSchurComplement A)
      (hnext :
        higham_problem9_14_RecursiveFirstMethodTrace m
          (luFirstSchurComplement A)) :
      higham_problem9_14_RecursiveFirstMethodTrace (m + 1) A

/-- **Problem 9.14 / first §9.9 method**, every pre-pivoted GEPP input admits
the recursive first-method trace certificate. -/
theorem higham_problem9_14_RecursiveFirstMethodTrace_of_PrePivotedGEPP :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      higham_problem9_14_PrePivotedGEPP A →
        higham_problem9_14_RecursiveFirstMethodTrace n A := by
  intro n
  induction n with
  | zero =>
      intro A _hpre
      exact higham_problem9_14_RecursiveFirstMethodTrace.done
  | succ m ih =>
      intro A hpre
      exact higham_problem9_14_RecursiveFirstMethodTrace.step
        (higham_problem9_14_firstMethodMatrix_terminal_trace A)
        (fun t ht =>
          higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_multiplier_abs_le_one
            (A := A) hpre ht)
        (higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_terminal_firstSchurComplement
          (A := A) hpre)
        (ih (A := luFirstSchurComplement A)
          (higham_problem9_14_PrePivotedGEPP_firstSchurComplement hpre))

/-- **Problem 9.14 / first §9.9 method**, recursive LU certificate for the
first method.  The certificate records the first-stage trace, the proved
multiplier bounds, the terminal Schur-complement bridge, and the recursively
constructed factors for the next active matrix. -/
inductive higham_problem9_14_RecursiveFirstMethodLUFactSpec :
    (n : ℕ) → (Fin n → Fin n → ℝ) →
      (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Prop
  | done {A L U : Fin 0 → Fin 0 → ℝ} :
      higham_problem9_14_RecursiveFirstMethodLUFactSpec 0 A L U
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {Lnext Unext : Fin m → Fin m → ℝ}
      (hpivot : A 0 0 ≠ 0)
      (hstage :
        higham_problem9_14_FirstMethodTrace A m
          (higham_problem9_14_firstMethodMatrix A m))
      (hmult :
        ∀ t : ℕ, t < m →
          |higham_problem9_14_firstMethodMatrix A t
              (higham_problem9_14_firstMethodTarget (m := m) t) 0 /
            higham_problem9_14_firstMethodMatrix A t 0 0| ≤ 1)
      (hschur :
        luFirstSchurComplement (higham_problem9_14_firstMethodMatrix A m) =
          luFirstSchurComplement A)
      (hnext :
        higham_problem9_14_RecursiveFirstMethodLUFactSpec m
          (luFirstSchurComplement A) Lnext Unext) :
      higham_problem9_14_RecursiveFirstMethodLUFactSpec (m + 1) A
        (luFirstStepL A Lnext) (luFirstStepU A Unext)

/-- **Problem 9.14 / first §9.9 method**, every recursive first-method LU
certificate is an ordinary exact LU certificate for the source matrix. -/
theorem higham_problem9_14_RecursiveFirstMethodLUFactSpec_to_LUFactSpec :
    ∀ {n : ℕ} {A L U : Fin n → Fin n → ℝ},
      higham_problem9_14_RecursiveFirstMethodLUFactSpec n A L U →
        LUFactSpec n A L U := by
  intro n A L U htrace
  induction htrace with
  | done =>
      refine
        { L_diag := ?_
          L_upper_zero := ?_
          U_lower_zero := ?_
          product_eq := ?_ }
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | step hpivot _hstage _hmult _hschur _hnext ih =>
      exact LUFactSpec.of_firstSchurComplement_explicit hpivot ih

/-- **Problem 9.14 / first §9.9 method**, existence of recursive first-method
LU factors for every pre-pivoted GEPP input. -/
theorem higham_problem9_14_exists_RecursiveFirstMethodLUFactSpec_of_PrePivotedGEPP :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      higham_problem9_14_PrePivotedGEPP A →
        ∃ L U : Fin n → Fin n → ℝ,
          higham_problem9_14_RecursiveFirstMethodLUFactSpec n A L U := by
  intro n
  induction n with
  | zero =>
      intro A _hpre
      exact ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
        higham_problem9_14_RecursiveFirstMethodLUFactSpec.done⟩
  | succ m ih =>
      intro A hpre
      obtain ⟨Lnext, Unext, hnextLU⟩ :=
        ih (A := luFirstSchurComplement A)
          (higham_problem9_14_PrePivotedGEPP_firstSchurComplement hpre)
      have hpivot : A 0 0 ≠ 0 := by
        cases hpre with
        | step _hchoice hpivot _hnext =>
            exact hpivot
      exact
        ⟨luFirstStepL A Lnext, luFirstStepU A Unext,
          higham_problem9_14_RecursiveFirstMethodLUFactSpec.step
            hpivot
            (higham_problem9_14_firstMethodMatrix_terminal_trace A)
            (fun t ht =>
              higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_multiplier_abs_le_one
                (A := A) hpre ht)
            (higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_terminal_firstSchurComplement
              (A := A) hpre)
            hnextLU⟩

/-- **Problem 9.14 / same-LU bridge**, any recursive first-method LU
certificate for a pre-pivoted input has the same exact factors as any
GEPP/no-interchange exact LU certificate for that input. -/
theorem higham_problem9_14_RecursiveFirstMethodLUFactSpec_same_as_PrePivotedGEPP
    {n : ℕ} {A Lf Uf Lg Ug : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (hfirst : higham_problem9_14_RecursiveFirstMethodLUFactSpec n A Lf Uf)
    (hgepp : LUFactSpec n A Lg Ug) :
    Lf = Lg ∧ Uf = Ug := by
  exact higham_problem9_14_PrePivotedGEPP_lu_unique hpre
    (higham_problem9_14_RecursiveFirstMethodLUFactSpec_to_LUFactSpec hfirst)
    hgepp

/-- **Problem 9.14 / pairwise pivoting**, one exact pairwise
pivot-and-eliminate step: move the deterministic pair pivot into the left row
`p`, then eliminate the active-column entry in the right row `q`. -/
noncomputable def higham_problem9_14_pairPivotEliminateToLeft {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    Fin n → Fin n → ℝ :=
  higham_problem9_14_pairEliminateRow
    (higham_problem9_14_pairPivotToLeftMatrix A k p q) k p q

/-- **Problem 9.14 / pairwise pivoting**, target-row formula for one
pairwise pivot-and-eliminate step after the deterministic pair pivot has been
moved to the left row. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_target {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q j : Fin n) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q q j =
      higham_problem9_14_pairPivotToLeftMatrix A k p q q j -
        (higham_problem9_14_pairPivotToLeftMatrix A k p q q k /
          higham_problem9_14_pairPivotToLeftMatrix A k p q p k) *
        higham_problem9_14_pairPivotToLeftMatrix A k p q p j := by
  unfold higham_problem9_14_pairPivotEliminateToLeft
  exact higham_problem9_14_pairEliminateRow_target
    (higham_problem9_14_pairPivotToLeftMatrix A k p q) k p q j

/-- **Problem 9.14 / pairwise pivoting**, rows other than the right-row target
are unchanged by one pairwise pivot-and-eliminate step after the pivot-to-left
permutation. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_of_ne {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q i j : Fin n}
    (hi : i ≠ q) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q i j =
      higham_problem9_14_pairPivotToLeftMatrix A k p q i j := by
  unfold higham_problem9_14_pairPivotEliminateToLeft
  exact higham_problem9_14_pairEliminateRow_of_ne
    (higham_problem9_14_pairPivotToLeftMatrix A k p q) hi

/-- **Problem 9.14 / pairwise pivoting**, the left pivot row is unchanged by
one pairwise pivot-and-eliminate step when the two pair rows are distinct. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_pivot {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q j : Fin n}
    (hpq : p ≠ q) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q p j =
      higham_problem9_14_pairPivotToLeftMatrix A k p q p j :=
  higham_problem9_14_pairPivotEliminateToLeft_of_ne A hpq

/-- **Problem 9.14 / pairwise pivoting**, the multiplier used by one
pairwise pivot-and-eliminate step has magnitude at most one: after the
deterministic pair pivot has been moved to the left row `p`, the right-row
entry divided by the left pivot is bounded by the source pairwise pivot rule. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_multiplier_abs_le_one
    {n : ℕ} {A : Fin n → Fin n → ℝ} {k p q : Fin n}
    (hpq : p ≠ q)
    (hpivot : A (higham_problem9_14_pairPivotRow A k p q) k ≠ 0) :
    |(higham_problem9_14_pairPivotToLeftMatrix A k p q q k /
        higham_problem9_14_pairPivotToLeftMatrix A k p q p k)| ≤ 1 := by
  rw [higham_problem9_14_pairPivotToLeftMatrix_left A k p q k]
  by_cases hp : higham_problem9_14_pairPivotRow A k p q = p
  · have hbound := higham_problem9_14_pairPivotRow_right_multiplier_abs_le_one
      (A := A) (k := k) (p := p) (q := q) hpivot
    simpa [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
      higham_problem9_14_pairPivotToLeftSwap, hp] using hbound
  · have hrow : higham_problem9_14_pairPivotRow A k p q = q := by
      rcases (higham_problem9_14_pairPivotRow_choice A k p q).1 with hleft | hright
      · exact (hp hleft).elim
      · exact hright
    have hbound := higham_problem9_14_pairPivotRow_left_multiplier_abs_le_one
      (A := A) (k := k) (p := p) (q := q) hpivot
    simpa [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
      higham_problem9_14_pairPivotToLeftSwap, higham_problem9_14_pairRowSwap_right,
      hp, hrow, hpq, Ne.symm hpq] using hbound

/-- **Problem 9.14 / pairwise pivoting**, after a pairwise pivot-and-eliminate
step, the left row remains the deterministically chosen pair pivot row of the
original matrix. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_left {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q j : Fin n}
    (hpq : p ≠ q) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q p j =
      A (higham_problem9_14_pairPivotRow A k p q) j := by
  unfold higham_problem9_14_pairPivotEliminateToLeft
  rw [higham_problem9_14_pairEliminateRow_pivot
    (higham_problem9_14_pairPivotToLeftMatrix A k p q) hpq]
  exact higham_problem9_14_pairPivotToLeftMatrix_left A k p q j

/-- **Problem 9.14 / pairwise pivoting**, the pairwise pivot-and-eliminate
step zeros the right row's active-column entry when the chosen pair pivot is
nonzero. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (hpivot : A (higham_problem9_14_pairPivotRow A k p q) k ≠ 0) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q q k = 0 := by
  have hpivot_left :
      higham_problem9_14_pairPivotToLeftMatrix A k p q p k ≠ 0 := by
    simpa [higham_problem9_14_pairPivotToLeftMatrix_left A k p q k] using hpivot
  unfold higham_problem9_14_pairPivotEliminateToLeft
  exact
    higham_problem9_14_pairEliminateRow_target_active_eq_zero
      (higham_problem9_14_pairPivotToLeftMatrix A k p q) hpivot_left

/-- **Problem 9.14 / pairwise pivoting**, one exact pairwise
pivot-and-eliminate step preserves nonsingularity when the pair rows are
distinct. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (hpq : p ≠ q)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham_problem9_14_pairPivotEliminateToLeft A k p q) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  have hdet_left :=
    higham_problem9_14_pairPivotToLeftMatrix_det_ne_zero A k p q hdet
  unfold higham_problem9_14_pairPivotEliminateToLeft
  exact higham_problem9_14_pairEliminateRow_det_ne_zero
    (higham_problem9_14_pairPivotToLeftMatrix A k p q) (Ne.symm hpq)
    hdet_left

/-- **Problem 9.14 / pairwise pivoting**, generic right-dominant pair step:
if the right row has active-column entry at least as large as the left row's
entry, then one pair pivot-and-eliminate step moves the right row into the left
pivot slot.  This is the local row-motion lemma used to build the row-reversal
"bubble" trace for pairwise pivoting. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_left_eq_right_of_abs_le
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (hpq : p ≠ q) (habs : |A p k| ≤ |A q k|) (j : Fin n) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q p j = A q j := by
  rw [higham_problem9_14_pairPivotEliminateToLeft_left A hpq]
  rw [higham_problem9_14_pairPivotRow_eq_right_of_abs_le A habs]

/-- **Problem 9.14 / pairwise pivoting**, generic right-dominant pair step:
after the right row is selected as the pivot, the old right-row slot contains
the exact elimination update of the old left row by that pivot row. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_target_eq_left_sub_right
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (hpq : p ≠ q) (habs : |A p k| ≤ |A q k|) (j : Fin n) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q q j =
      A p j - (A p k / A q k) * A q j := by
  have hsel : higham_problem9_14_pairPivotRow A k p q = q :=
    higham_problem9_14_pairPivotRow_eq_right_of_abs_le A habs
  have hqp : q ≠ p := Ne.symm hpq
  rw [higham_problem9_14_pairPivotEliminateToLeft_target]
  simp [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_pairPivotToLeftSwap, higham_problem9_14_pairRowSwap,
    hsel, hqp]

/-- **Problem 9.14 / pairwise pivoting**, generic right-dominant pair step:
the selected right pivot zeros the old right-row slot in the active column. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero_of_abs_le
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (habs : |A p k| ≤ |A q k|) (hpivot : A q k ≠ 0) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q q k = 0 := by
  have hsel : higham_problem9_14_pairPivotRow A k p q = q :=
    higham_problem9_14_pairPivotRow_eq_right_of_abs_le A habs
  exact higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero A
    (by simpa [hsel] using hpivot)

/-- **Problem 9.14 / pairwise pivoting**, generic right-dominant pair step:
the exact target row after one adjacent-pair elimination is bounded by twice a
row-entry budget when both input rows obey that budget.  This is the local
growth estimate needed for the cumulative pairwise row-reversal trace. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_target_abs_le_two_of_abs_le
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n} {M : ℝ}
    (hpq : p ≠ q) (habs : |A p k| ≤ |A q k|)
    (hpivot : A q k ≠ 0)
    (hp_bound : ∀ j : Fin n, |A p j| ≤ M)
    (hq_bound : ∀ j : Fin n, |A q j| ≤ M)
    (_hM : 0 ≤ M) (j : Fin n) :
    |higham_problem9_14_pairPivotEliminateToLeft A k p q q j| ≤
      2 * M := by
  have hformula :=
    higham_problem9_14_pairPivotEliminateToLeft_target_eq_left_sub_right
      A hpq habs j
  have hden_pos : 0 < |A q k| := abs_pos.mpr hpivot
  have hratio : |A p k / A q k| ≤ 1 := by
    calc
      |A p k / A q k| = |A p k| / |A q k| := by rw [abs_div]
      _ ≤ |A q k| / |A q k| :=
          div_le_div_of_nonneg_right habs (abs_nonneg _)
      _ = 1 := by field_simp [ne_of_gt hden_pos]
  have hterm : |(A p k / A q k) * A q j| ≤ M := by
    calc
      |(A p k / A q k) * A q j|
          = |A p k / A q k| * |A q j| := by rw [abs_mul]
      _ ≤ 1 * |A q j| :=
          mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
      _ ≤ 1 * M :=
          mul_le_mul_of_nonneg_left (hq_bound j) zero_le_one
      _ = M := by ring
  rw [hformula]
  calc
    |A p j - (A p k / A q k) * A q j|
        ≤ |A p j| + |(A p k / A q k) * A q j| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (A p j) (-((A p k / A q k) * A q j))
    _ ≤ M + M := add_le_add (hp_bound j) hterm
    _ = 2 * M := by ring

/-- **Problem 9.14 / pairwise pivoting**, generic right-dominant pair step:
all rows outside the compared pair are unchanged.  This is the row-shape
invariant needed when iterating adjacent pair steps to bubble the pre-pivoted
row upward through the row-reversed matrix. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q i j : Fin n}
    (hpq : p ≠ q) (habs : |A p k| ≤ |A q k|)
    (hip : i ≠ p) (hiq : i ≠ q) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q i j = A i j := by
  rw [higham_problem9_14_pairPivotEliminateToLeft_of_ne A hiq]
  have hsel : higham_problem9_14_pairPivotRow A k p q = q :=
    higham_problem9_14_pairPivotRow_eq_right_of_abs_le A habs
  have hnot : higham_problem9_14_pairPivotRow A k p q ≠ p := by
    intro h
    exact hpq (h.symm.trans hsel)
  simp [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_pairPivotToLeftSwap, higham_problem9_14_pairRowSwap,
    hnot]
  exact congrArg (fun r => A r j) (Equiv.swap_apply_of_ne_of_ne hip hiq)

/-- **Problem 9.14**, running one pair pivot-and-eliminate step on the
row-reversed matrix `ΠA` preserves nonsingularity whenever the source matrix is
nonsingular and the compared pair rows are distinct. -/
theorem higham_problem9_14_rowReversedMatrix_pairPivotEliminateToLeft_det_ne_zero
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (hpq : p ≠ q)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) k p q) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  have hdet_rev := higham_problem9_14_rowReversedMatrix_det_ne_zero A hdet
  exact higham_problem9_14_pairPivotEliminateToLeft_det_ne_zero
    (higham_problem9_14_rowReversedMatrix A) hpq hdet_rev

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: when the
row-reversed matrix `ΠA` compares any distinct left row with the last row in
the first column, one pair pivot-and-eliminate step moves the original first
row of `A` into the left pivot slot. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) p j =
      A 0 j := by
  have hsel :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
      hpre p
  rw [higham_problem9_14_pairPivotEliminateToLeft_left
    (higham_problem9_14_rowReversedMatrix A) hp]
  rw [hsel]
  have hlast :
      higham_problem9_14_rowReversal
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) =
        (0 : Fin (m + 1)) := by
    ext
    simp [higham_problem9_14_rowReversal]
  simp [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
    hlast]

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: one
first-column pair pivot-and-eliminate step leaves every row outside the
compared pair unchanged.  This is the local row-shape invariant for the
still-open cumulative row-reversal/pairwise-pivoting trace equivalence. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_of_ne_pair
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) i j =
      higham_problem9_14_rowReversedMatrix A i j := by
  have hpivot :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).1
  have habs :
      |higham_problem9_14_rowReversedMatrix A p 0| ≤
        |higham_problem9_14_rowReversedMatrix A
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) 0| :=
    hpivot.2 p (Nat.zero_le _)
  exact
    higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
      (higham_problem9_14_rowReversedMatrix A) hp habs hip hilast

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after one
first-column pair pivot-and-eliminate step, the moved pivot row still has a
nonzero active entry.  This is the local nonzero-pivot invariant for the
cumulative adjacent-pair bubble trace. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_active_ne_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) p 0 ≠ 0 := by
  have hpiv : A 0 0 ≠ 0 := by
    cases hpre with
    | step _ hpivot _ => simpa using hpivot
  have hpivrow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row
      hpre hp (0 : Fin (m + 1))
  simpa [hpivrow] using hpiv

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after one
first-column bubble step, every unchanged row remains dominated in the active
column by the moved pivot row.  This is the selector invariant needed to
continue bubbling the same source pivot row through adjacent pair steps. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_unchanged_abs_le_pivot
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    |higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) i 0| ≤
      |higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) p 0| := by
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  have hirow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_of_ne_pair
      hpre hp hip hilast (0 : Fin (m + 1))
  have hprow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row
      hpre hp (0 : Fin (m + 1))
  have hlast :
      higham_problem9_14_rowReversedMatrix A last 0 = A 0 0 := by
    have hlastmap : higham_problem9_14_rowReversal last = (0 : Fin (m + 1)) := by
      subst last
      ext
      simp [higham_problem9_14_rowReversal]
    simp [last, higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
      hlastmap]
  have hchoice :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).1
  have hdom :
      |higham_problem9_14_rowReversedMatrix A i 0| ≤
        |higham_problem9_14_rowReversedMatrix A last 0| :=
    hchoice.2 i (Nat.zero_le _)
  rw [hirow, hprow]
  simpa [hlast] using hdom

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after one
first-column bubble step, the natural pairwise selector chooses the moved
pivot row as the right member against any unchanged row. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_next_pairPivotRow
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    higham_problem9_14_pairPivotRow
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p = p := by
  exact higham_problem9_14_pairPivotRow_eq_right_of_abs_le
    (higham_problem9_14_pairPivotEliminateToLeft
      (higham_problem9_14_rowReversedMatrix A) 0 p
      (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_unchanged_abs_le_pivot
      hpre hp hip hilast)

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after one
bubble step has moved the source pivot row into position `p`, a second
right-dominant pair step against an unchanged row `i` moves that same source
pivot row into position `i`.  This is the two-step local trace shape needed by
the cumulative adjacent-pair bubble construction. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p i j =
      A 0 j := by
  rw [higham_problem9_14_pairPivotEliminateToLeft_left
    (higham_problem9_14_pairPivotEliminateToLeft
      (higham_problem9_14_rowReversedMatrix A) 0 p
      (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) hip]
  rw [
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_next_pairPivotRow
      hpre hp hip hilast]
  exact
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row
      hpre hp j

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after two
right-dominant adjacent pair steps, every row outside the three touched row
positions is still the corresponding row of `ΠA`. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_of_ne_triple
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i r : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hri : r ≠ i)
    (hrp : r ≠ p)
    (hrlast : r ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p r j =
      higham_problem9_14_rowReversedMatrix A r j := by
  have habs :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_unchanged_abs_le_pivot
      hpre hp hip hilast
  have hsecond :=
    higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
      (A := higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
      (k := 0) (p := i) (q := p) (i := r) (j := j)
      hip habs hri hrp
  rw [hsecond]
  exact
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_of_ne_pair
      hpre hp hrp hrlast j

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after two
adjacent pair steps, the twice-moved source pivot row still has a nonzero
active entry. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_active_ne_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p i 0 ≠ 0 := by
  have hpiv : A 0 0 ≠ 0 := by
    cases hpre with
    | step _ hpivot _ => simpa using hpivot
  have hrow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_row
      hpre hp hip hilast (0 : Fin (m + 1))
  simpa [hrow] using hpiv

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after two
adjacent pair steps, every row outside the three touched row positions remains
dominated in the active column by the twice-moved pivot row. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_unchanged_abs_le_pivot
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i r : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hri : r ≠ i)
    (hrp : r ≠ p)
    (hrlast : r ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    |higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p r 0| ≤
      |higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p i 0| := by
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  have hrrow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_of_ne_triple
      hpre hp hip hilast hri hrp hrlast (0 : Fin (m + 1))
  have hirow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_row
      hpre hp hip hilast (0 : Fin (m + 1))
  have hlast :
      higham_problem9_14_rowReversedMatrix A last 0 = A 0 0 := by
    have hlastmap : higham_problem9_14_rowReversal last = (0 : Fin (m + 1)) := by
      subst last
      ext
      simp [higham_problem9_14_rowReversal]
    simp [last, higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
      hlastmap]
  have hchoice :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).1
  have hdom :
      |higham_problem9_14_rowReversedMatrix A r 0| ≤
        |higham_problem9_14_rowReversedMatrix A last 0| :=
    hchoice.2 r (Nat.zero_le _)
  rw [hrrow, hirow]
  simpa [hlast] using hdom

/-- **Problem 9.14 / pairwise pivoting**, recursive exact first-column
pairwise-bubble matrix for the source row-reversal route.  Step `t + 1`
compares rows `m-(t+1)` and `m-t`, so each genuine step is an adjacent
pairwise pivot-and-eliminate operation. -/
noncomputable def higham_problem9_14_pairwiseBubbleMatrix {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ℕ → Fin (m + 1) → Fin (m + 1) → ℝ
  | 0 => higham_problem9_14_rowReversedMatrix A
  | t + 1 =>
      higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairwiseBubbleMatrix A t) 0
        (higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1))
        (higham_problem9_14_pairwiseBubbleRow (m := m) t)

/-- **Problem 9.14 / pairwise pivoting**, the recursive bubble matrix starts
from the source row-reversed matrix `ΠA`. -/
@[simp] theorem higham_problem9_14_pairwiseBubbleMatrix_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_pairwiseBubbleMatrix A 0 =
      higham_problem9_14_rowReversedMatrix A := rfl

/-- **Problem 9.14 / pairwise pivoting**, unfolding one scheduled adjacent
pairwise bubble step. -/
theorem higham_problem9_14_pairwiseBubbleMatrix_succ {m t : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_pairwiseBubbleMatrix A (t + 1) =
      higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairwiseBubbleMatrix A t) 0
        (higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1))
        (higham_problem9_14_pairwiseBubbleRow (m := m) t) := rfl

/-- **Problem 9.14 / pairwise pivoting**, source-facing trace predicate for
the adjacent row-reversal bubble.  The initial state is `ΠA`; each genuine
step compares the scheduled adjacent rows `m-(t+1)` and `m-t` in column zero
and performs one exact pairwise pivot-and-eliminate operation. -/
inductive higham_problem9_14_PairwiseBubbleTrace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ℕ → (Fin (m + 1) → Fin (m + 1) → ℝ) → Prop
  | init :
      higham_problem9_14_PairwiseBubbleTrace A 0
        (higham_problem9_14_rowReversedMatrix A)
  | step {t : ℕ} {B : Fin (m + 1) → Fin (m + 1) → ℝ}
      (ht : t < m)
      (htrace : higham_problem9_14_PairwiseBubbleTrace A t B) :
      higham_problem9_14_PairwiseBubbleTrace A (t + 1)
        (higham_problem9_14_pairPivotEliminateToLeft B 0
          (higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1))
          (higham_problem9_14_pairwiseBubbleRow (m := m) t))

/-- **Problem 9.14 / pairwise pivoting**, the recursive scheduled matrix is a
valid adjacent row-reversal bubble trace at every prefix `t <= m`. -/
theorem higham_problem9_14_pairwiseBubbleMatrix_trace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ∀ t : ℕ, t ≤ m →
      higham_problem9_14_PairwiseBubbleTrace A t
        (higham_problem9_14_pairwiseBubbleMatrix A t) := by
  intro t
  induction t with
  | zero =>
      intro _ht
      exact higham_problem9_14_PairwiseBubbleTrace.init
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      simpa [higham_problem9_14_pairwiseBubbleMatrix_succ] using
        higham_problem9_14_PairwiseBubbleTrace.step ht (ih ht_le)

/-- **Problem 9.14 / pairwise pivoting**, terminal source-facing trace for the
scheduled adjacent row-reversal bubble. -/
theorem higham_problem9_14_pairwiseBubbleMatrix_terminal_trace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_PairwiseBubbleTrace A m
      (higham_problem9_14_pairwiseBubbleMatrix A m) :=
  higham_problem9_14_pairwiseBubbleMatrix_trace A m le_rfl

/-- **Problem 9.14 / pairwise pivoting**, every scheduled adjacent
row-reversal bubble prefix preserves nonsingularity.  The base step uses
nonsingularity of `ΠA`; each later step is one determinant-preserving pairwise
pivot-and-eliminate operation on distinct adjacent rows. -/
theorem higham_problem9_14_pairwiseBubbleMatrix_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet : Matrix.det
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∀ t : ℕ, t ≤ m →
      Matrix.det
        (Matrix.of (higham_problem9_14_pairwiseBubbleMatrix A t) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
  intro t
  induction t with
  | zero =>
      intro _ht
      simpa [higham_problem9_14_pairwiseBubbleMatrix_zero] using
        higham_problem9_14_rowReversedMatrix_det_ne_zero A hdet
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      have hpq :
          higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1) ≠
            higham_problem9_14_pairwiseBubbleRow (m := m) t :=
        higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := t) ht
      simpa [higham_problem9_14_pairwiseBubbleMatrix_succ] using
        higham_problem9_14_pairPivotEliminateToLeft_det_ne_zero
          (A := higham_problem9_14_pairwiseBubbleMatrix A t)
          (k := 0)
          (p := higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1))
          (q := higham_problem9_14_pairwiseBubbleRow (m := m) t)
          hpq (ih ht_le)

/-- **Problem 9.14 / pairwise pivoting**, terminal nonsingularity for the
scheduled row-reversal bubble. -/
theorem higham_problem9_14_pairwiseBubbleMatrix_terminal_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet : Matrix.det
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham_problem9_14_pairwiseBubbleMatrix A m) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 :=
  higham_problem9_14_pairwiseBubbleMatrix_det_ne_zero A hdet m le_rfl

/-- **Problem 9.14 / pairwise pivoting**, general prefix invariant for the
scheduled row-reversal bubble.  After `t` genuine adjacent pairwise steps, the
carried pivot row contains the original first row of `A`, that active pivot is
nonzero, every still-untouched row above it is still the corresponding row of
`ΠA`, and those untouched active-column entries are dominated by the carried
pivot.  This is the local induction surface needed before proving the terminal
pairwise trace equivalence in full Problem 9.14. -/
theorem higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∀ t : ℕ, t ≤ m →
      (∀ j : Fin (m + 1),
        higham_problem9_14_pairwiseBubbleMatrix A t
          (higham_problem9_14_pairwiseBubbleRow (m := m) t) j = A 0 j) ∧
      higham_problem9_14_pairwiseBubbleMatrix A t
        (higham_problem9_14_pairwiseBubbleRow (m := m) t) 0 ≠ 0 ∧
      (∀ r : Fin (m + 1),
        r.val < (higham_problem9_14_pairwiseBubbleRow (m := m) t).val →
          ∀ j : Fin (m + 1),
            higham_problem9_14_pairwiseBubbleMatrix A t r j =
              higham_problem9_14_rowReversedMatrix A r j) ∧
      (∀ r : Fin (m + 1),
        r.val < (higham_problem9_14_pairwiseBubbleRow (m := m) t).val →
          |higham_problem9_14_pairwiseBubbleMatrix A t r 0| ≤
            |higham_problem9_14_pairwiseBubbleMatrix A t
              (higham_problem9_14_pairwiseBubbleRow (m := m) t) 0|) := by
  let row : ℕ → Fin (m + 1) :=
    fun t => higham_problem9_14_pairwiseBubbleRow (m := m) t
  have hrow0 : ∀ j : Fin (m + 1),
      higham_problem9_14_rowReversedMatrix A (row 0) j = A 0 j := by
    intro j
    have hmap : higham_problem9_14_rowReversal (row 0) = (0 : Fin (m + 1)) := by
      ext
      simp [row, higham_problem9_14_pairwiseBubbleRow,
        higham_problem9_14_rowReversal]
    rw [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix]
    change A (higham_problem9_14_rowReversal (row 0)) j = A 0 j
    rw [hmap]
  have hpivA : A 0 0 ≠ 0 := by
    cases hpre with
    | step _ hpivot _ => simpa using hpivot
  have hchoice :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).1
  intro t
  induction t with
  | zero =>
      intro _ht
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j
        simpa [row, higham_problem9_14_pairwiseBubbleMatrix_zero] using
          hrow0 j
      · rw [higham_problem9_14_pairwiseBubbleMatrix_zero,
          hrow0 (0 : Fin (m + 1))]
        exact hpivA
      · intro r _hr j
        simp [higham_problem9_14_pairwiseBubbleMatrix_zero]
      · intro r _hr
        have hdom :
            |higham_problem9_14_rowReversedMatrix A r 0| ≤
              |higham_problem9_14_rowReversedMatrix A (row 0) 0| :=
          by
            simpa [row] using hchoice.2 r (Nat.zero_le _)
        simpa [row, higham_problem9_14_pairwiseBubbleMatrix_zero] using hdom
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      rcases ih ht_le with ⟨hpivotRow, hpivot_ne, hunchanged, hdom⟩
      let p : Fin (m + 1) := row (t + 1)
      let q : Fin (m + 1) := row t
      have hpq : p ≠ q := by
        simpa [p, q, row] using
          higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := t) ht
      have hpq_val : p.val < q.val := by
        simpa [p, q, row] using
          higham_problem9_14_pairwiseBubbleRow_succ_val_lt (m := m) (t := t) ht
      have habs :
          |higham_problem9_14_pairwiseBubbleMatrix A t p 0| ≤
            |higham_problem9_14_pairwiseBubbleMatrix A t q 0| := by
        simpa [p, q, row] using hdom p hpq_val
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have hleft :=
          higham_problem9_14_pairPivotEliminateToLeft_left_eq_right_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) hpq habs j
        rw [hleft]
        simpa [q, row] using hpivotRow j
      · rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have hleft :=
          higham_problem9_14_pairPivotEliminateToLeft_left_eq_right_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) hpq habs (0 : Fin (m + 1))
        rw [hleft]
        simpa [q, row] using hpivot_ne
      · intro r hr j
        have hrp_lt : r.val < p.val := by
          simpa [p] using hr
        have hrq_lt : r.val < q.val := lt_trans hrp_lt hpq_val
        have hrp : r ≠ p := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = p.val := hval
          omega
        have hrq : r ≠ q := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = q.val := hval
          omega
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have hsame :=
          higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) (i := r) (j := j)
            hpq habs hrp hrq
        rw [hsame]
        exact hunchanged r hrq_lt j
      · intro r hr
        have hrp_lt : r.val < p.val := by
          simpa [p] using hr
        have hrq_lt : r.val < q.val := lt_trans hrp_lt hpq_val
        have hrp : r ≠ p := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = p.val := hval
          omega
        have hrq : r ≠ q := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = q.val := hval
          omega
        have hr_step :
            higham_problem9_14_pairwiseBubbleMatrix A (t + 1) r
                (0 : Fin (m + 1)) =
              higham_problem9_14_rowReversedMatrix A r 0 := by
          rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
          have hsame :=
            higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
              (A := higham_problem9_14_pairwiseBubbleMatrix A t)
              (k := 0) (p := p) (q := q) (i := r)
              (j := (0 : Fin (m + 1))) hpq habs hrp hrq
          rw [hsame]
          exact hunchanged r hrq_lt 0
        have hp_step :
            higham_problem9_14_pairwiseBubbleMatrix A (t + 1) p
                (0 : Fin (m + 1)) = A 0 0 := by
          rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
          have hleft :=
            higham_problem9_14_pairPivotEliminateToLeft_left_eq_right_of_abs_le
              (A := higham_problem9_14_pairwiseBubbleMatrix A t)
              (k := 0) (p := p) (q := q) hpq habs (0 : Fin (m + 1))
          rw [hleft]
          simpa [q, row] using hpivotRow (0 : Fin (m + 1))
        have horig :
            |higham_problem9_14_rowReversedMatrix A r 0| ≤
              |higham_problem9_14_rowReversedMatrix A (row 0) 0| :=
          by
            simpa [row] using hchoice.2 r (Nat.zero_le _)
        calc
          |higham_problem9_14_pairwiseBubbleMatrix A (t + 1) r
              (0 : Fin (m + 1))|
              = |higham_problem9_14_rowReversedMatrix A r 0| := by
                rw [hr_step]
          _ ≤ |higham_problem9_14_rowReversedMatrix A (row 0) 0| := horig
          _ = |higham_problem9_14_pairwiseBubbleMatrix A (t + 1) p
              (0 : Fin (m + 1))| := by
                rw [hrow0 (0 : Fin (m + 1)), hp_step]

/-- **Problem 9.14 / pairwise pivoting**, terminal row-motion consequence of
the scheduled prefix invariant: after the adjacent bubble has run from the last
row of `ΠA` to row zero, row zero contains the original first row of `A`. -/
theorem higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_pivot_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (j : Fin (m + 1)) :
    higham_problem9_14_pairwiseBubbleMatrix A m 0 j = A 0 j := by
  have h :=
    (higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant
      hpre m le_rfl).1 j
  simpa using h

/-- **Problem 9.14 / pairwise pivoting**, terminal nonzero-pivot consequence
of the scheduled prefix invariant. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_pivot_active_ne_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    higham_problem9_14_pairwiseBubbleMatrix A m 0 0 ≠ 0 := by
  have h :=
    (higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant
      hpre m le_rfl).2.1
  simpa using h

/-- **Problem 9.14 / pairwise pivoting**, eliminated-column prefix invariant
for the scheduled row-reversal bubble.  After `t` scheduled adjacent pairwise
steps, every row below the carried pivot has zero active-column entry. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_active_eq_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∀ t : ℕ, t ≤ m →
      ∀ r : Fin (m + 1),
        (higham_problem9_14_pairwiseBubbleRow (m := m) t).val < r.val →
          higham_problem9_14_pairwiseBubbleMatrix A t r 0 = 0 := by
  intro t
  induction t with
  | zero =>
      intro _ht r hr
      have hlt := r.isLt
      simp [higham_problem9_14_pairwiseBubbleRow] at hr
      omega
  | succ t ih =>
      intro hsucc r hr
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      let p : Fin (m + 1) :=
        higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1)
      let q : Fin (m + 1) :=
        higham_problem9_14_pairwiseBubbleRow (m := m) t
      have hpq : p ≠ q := by
        simpa [p, q] using
          higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := t) ht
      have hpq_val : p.val < q.val := by
        simpa [p, q] using
          higham_problem9_14_pairwiseBubbleRow_succ_val_lt (m := m) (t := t) ht
      have hq_eq : p.val + 1 = q.val := by
        have hadj :=
          higham_problem9_14_pairwiseBubbleRows_adjacent (m := m) (t := t) ht
        rcases hadj with hforward | hback
        · simpa [p, q] using hforward
        · have hbad : q.val + 1 = p.val := by
            simpa [p, q] using hback
          omega
      have hinv :=
        higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant
          (A := A) hpre t ht_le
      have habs :
          |higham_problem9_14_pairwiseBubbleMatrix A t p 0| ≤
            |higham_problem9_14_pairwiseBubbleMatrix A t q 0| := by
        simpa [p, q] using hinv.2.2.2 p hpq_val
      have hpivot : higham_problem9_14_pairwiseBubbleMatrix A t q 0 ≠ 0 := by
        simpa [q] using hinv.2.1
      by_cases hrq : r = q
      · subst r
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        exact
          higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) habs hpivot
      · have hrp : r ≠ p := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = p.val := hval
          omega
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have hsame :=
          higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) (i := r)
            (j := (0 : Fin (m + 1))) hpq habs hrp hrq
        rw [hsame]
        have hr_val_ne_q : r.val ≠ q.val := by
          intro hval
          exact hrq (Fin.ext hval)
        have hq_lt_r : q.val < r.val := by
          have hp_lt_r : p.val < r.val := by
            simpa [p] using hr
          omega
        exact ih ht_le r hq_lt_r

/-- **Problem 9.14 / pairwise pivoting**, terminal eliminated-column
consequence: after the scheduled bubble reaches row zero, every nonzero row
has active-column entry zero. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_active_eq_zero_of_ne_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {i : Fin (m + 1)} (hi : i ≠ 0) :
    higham_problem9_14_pairwiseBubbleMatrix A m i 0 = 0 := by
  have hival_ne : i.val ≠ 0 := by
    intro hval
    exact hi (Fin.ext hval)
  have hpos : 0 < i.val := Nat.pos_of_ne_zero hival_ne
  exact
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_active_eq_zero
      (A := A) hpre m le_rfl i (by
        simpa [higham_problem9_14_pairwiseBubbleRow_self] using hpos)

/-- **Problem 9.14 / pairwise pivoting**, prefix row formula for rows already
eliminated by the scheduled adjacent bubble.  Every row below the carried pivot
is the exact first-column Schur update of the corresponding source row by the
original first row of `A`. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∀ t : ℕ, t ≤ m →
      ∀ r : Fin (m + 1),
        (higham_problem9_14_pairwiseBubbleRow (m := m) t).val < r.val →
          ∀ j : Fin (m + 1),
            higham_problem9_14_pairwiseBubbleMatrix A t r j =
              A (higham_problem9_14_pairwiseBubbleSourceRow (m := m) r) j -
                (A (higham_problem9_14_pairwiseBubbleSourceRow (m := m) r) 0 /
                    A 0 0) * A 0 j := by
  let row : ℕ → Fin (m + 1) :=
    fun t => higham_problem9_14_pairwiseBubbleRow (m := m) t
  have hrow0 : ∀ j : Fin (m + 1),
      higham_problem9_14_rowReversedMatrix A (row 0) j = A 0 j := by
    intro j
    have hmap : higham_problem9_14_rowReversal (row 0) = (0 : Fin (m + 1)) := by
      ext
      simp [row, higham_problem9_14_pairwiseBubbleRow,
        higham_problem9_14_rowReversal]
    rw [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix]
    change A (higham_problem9_14_rowReversal (row 0)) j = A 0 j
    rw [hmap]
  intro t
  induction t with
  | zero =>
      intro _ht r hr j
      have hlt := r.isLt
      simp [higham_problem9_14_pairwiseBubbleRow] at hr
      omega
  | succ t ih =>
      intro hsucc r hr j
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      let p : Fin (m + 1) := row (t + 1)
      let q : Fin (m + 1) := row t
      have hpq : p ≠ q := by
        simpa [p, q, row] using
          higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := t) ht
      have hpq_val : p.val < q.val := by
        simpa [p, q, row] using
          higham_problem9_14_pairwiseBubbleRow_succ_val_lt (m := m) (t := t) ht
      have hq_eq : p.val + 1 = q.val := by
        have hadj :=
          higham_problem9_14_pairwiseBubbleRows_adjacent (m := m) (t := t) ht
        rcases hadj with hforward | hback
        · simpa [p, q, row] using hforward
        · have hbad : q.val + 1 = p.val := by
            simpa [p, q, row] using hback
          omega
      have hinv :=
        higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant
          (A := A) hpre t ht_le
      have hpivotRow := hinv.1
      have hunchanged := hinv.2.2.1
      have hdom := hinv.2.2.2
      have habs :
          |higham_problem9_14_pairwiseBubbleMatrix A t p 0| ≤
            |higham_problem9_14_pairwiseBubbleMatrix A t q 0| := by
        simpa [p, q, row] using hdom p hpq_val
      by_cases hrq : r = q
      · subst r
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have htarget :=
          higham_problem9_14_pairPivotEliminateToLeft_target_eq_left_sub_right
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) hpq habs j
        rw [htarget]
        have hp_row :
            higham_problem9_14_pairwiseBubbleMatrix A t p j =
              higham_problem9_14_rowReversedMatrix A p j :=
          hunchanged p hpq_val j
        have hp_active :
            higham_problem9_14_pairwiseBubbleMatrix A t p 0 =
              higham_problem9_14_rowReversedMatrix A p 0 :=
          hunchanged p hpq_val 0
        have hq_row :
            higham_problem9_14_pairwiseBubbleMatrix A t q j = A 0 j := by
          simpa [q, row] using hpivotRow j
        have hq_active :
            higham_problem9_14_pairwiseBubbleMatrix A t q 0 = A 0 0 := by
          simpa [q, row] using hpivotRow (0 : Fin (m + 1))
        have hsrc :
            higham_problem9_14_pairwiseBubbleSourceRow (m := m) q =
              higham_problem9_14_rowReversal p := by
          ext
          simp [higham_problem9_14_pairwiseBubbleSourceRow,
            higham_problem9_14_rowReversal, p, q, row,
            higham_problem9_14_pairwiseBubbleRow]
          omega
        rw [hp_row, hp_active, hq_row, hq_active]
        simp only [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix]
        rw [← hsrc]
      · have hp_lt_r : p.val < r.val := by
          simpa [p, row] using hr
        have hrp : r ≠ p := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = p.val := hval
          omega
        have hq_lt_r : q.val < r.val := by
          have hr_val_ne_q : r.val ≠ q.val := by
            intro hval
            exact hrq (Fin.ext hval)
          omega
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have hsame :=
          higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) (i := r) (j := j)
            hpq habs hrp hrq
        rw [hsame]
        exact ih ht_le r hq_lt_r j

/-- **Problem 9.14 / pairwise pivoting**, terminal first-Schur bridge.  The
trailing block of the scheduled adjacent row-reversal bubble is exactly the
row reversal of the first Schur complement of `A`.  Together with the terminal
row-zero/column-zero facts, this is the local bridge from the source pairwise
trace toward the recursive no-interchange LU route. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_trailing_eq_rowReversed_firstSchurComplement
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (i j : Fin m) :
    higham_problem9_14_pairwiseBubbleMatrix A m i.succ j.succ =
      higham_problem9_14_rowReversedMatrix (luFirstSchurComplement A) i j := by
  have hrow :=
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_row
      (A := A) hpre m le_rfl i.succ (by
        simp [higham_problem9_14_pairwiseBubbleRow_self]) j.succ
  rw [hrow]
  rw [higham_problem9_14_pairwiseBubbleSourceRow_succ]
  have hpiv : A 0 0 ≠ 0 := by
    cases hpre with
    | step _ hpivot _ => simpa using hpivot
  simp [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
    luFirstSchurComplement]
  field_simp [hpiv]

/-- **Problem 9.14 / pairwise pivoting**, terminal Schur-complement form.
After the scheduled adjacent row-reversal bubble reaches row zero, the first
Schur complement of the terminal full matrix is exactly the row reversal of
the first Schur complement of the original pre-pivoted input. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_firstSchurComplement_eq_rowReversed_firstSchurComplement
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    luFirstSchurComplement (higham_problem9_14_pairwiseBubbleMatrix A m) =
      higham_problem9_14_rowReversedMatrix (luFirstSchurComplement A) := by
  funext i j
  unfold luFirstSchurComplement
  have htrail :=
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_trailing_eq_rowReversed_firstSchurComplement
      (A := A) hpre i j
  have hzero :
      higham_problem9_14_pairwiseBubbleMatrix A m i.succ (0 : Fin (m + 1)) = 0 :=
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_active_eq_zero_of_ne_zero
      (A := A) hpre i.succ_ne_zero
  rw [htrail, hzero]
  simp [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
    luFirstSchurComplement, div_eq_mul_inv]

/-- **Problem 9.14 / pairwise pivoting**, recursive source-facing trace
certificate.  At each nonempty stage, the row-reversed active matrix runs the
scheduled adjacent pairwise bubble, whose first Schur complement is the
row-reversal of the next no-interchange Schur complement; the certificate then
recurses on that next source Schur complement. -/
inductive higham_problem9_14_RecursivePairwiseBubbleTrace :
    (n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | done {A : Fin 0 → Fin 0 → ℝ} :
      higham_problem9_14_RecursivePairwiseBubbleTrace 0 A
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      (hbubble :
        higham_problem9_14_PairwiseBubbleTrace A m
          (higham_problem9_14_pairwiseBubbleMatrix A m))
      (hschur :
        luFirstSchurComplement
            (higham_problem9_14_pairwiseBubbleMatrix A m) =
          higham_problem9_14_rowReversedMatrix
            (luFirstSchurComplement A))
      (hnext :
        higham_problem9_14_RecursivePairwiseBubbleTrace m
          (luFirstSchurComplement A)) :
      higham_problem9_14_RecursivePairwiseBubbleTrace (m + 1) A

/-- **Problem 9.14 / pairwise pivoting**, a pre-pivoted GEPP input admits the
recursive row-reversal pairwise-bubble trace certificate.  This packages the
terminal first-Schur bridge with the no-interchange Schur-complement handoff;
it is still an intermediate trace-existence result, not the final same-LU
factorization theorem. -/
theorem higham_problem9_14_RecursivePairwiseBubbleTrace_of_PrePivotedGEPP :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      higham_problem9_14_PrePivotedGEPP A →
        higham_problem9_14_RecursivePairwiseBubbleTrace n A := by
  intro n
  induction n with
  | zero =>
      intro A _hpre
      exact higham_problem9_14_RecursivePairwiseBubbleTrace.done
  | succ m ih =>
      intro A hpre
      exact higham_problem9_14_RecursivePairwiseBubbleTrace.step
        (higham_problem9_14_pairwiseBubbleMatrix_terminal_trace A)
        (higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_firstSchurComplement_eq_rowReversed_firstSchurComplement
          (A := A) hpre)
        (ih (A := luFirstSchurComplement A)
          (higham_problem9_14_PrePivotedGEPP_firstSchurComplement hpre))

/-- **Problem 9.14 / pairwise pivoting**, recursive pairwise LU certificate.
The certificate records, at each nonempty stage, the source-facing scheduled
pairwise bubble on the row-reversed active matrix, the terminal Schur bridge,
and the recursively constructed factors for the no-interchange Schur
complement. -/
inductive higham_problem9_14_RecursivePairwiseLUFactSpec :
    (n : ℕ) → (Fin n → Fin n → ℝ) →
      (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Prop
  | done {A L U : Fin 0 → Fin 0 → ℝ} :
      higham_problem9_14_RecursivePairwiseLUFactSpec 0 A L U
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {L₁ U₁ : Fin m → Fin m → ℝ}
      (hpivot : A 0 0 ≠ 0)
      (hbubble :
        higham_problem9_14_PairwiseBubbleTrace A m
          (higham_problem9_14_pairwiseBubbleMatrix A m))
      (hschur :
        luFirstSchurComplement
            (higham_problem9_14_pairwiseBubbleMatrix A m) =
          higham_problem9_14_rowReversedMatrix
            (luFirstSchurComplement A))
      (hnext :
        higham_problem9_14_RecursivePairwiseLUFactSpec m
          (luFirstSchurComplement A) L₁ U₁) :
      higham_problem9_14_RecursivePairwiseLUFactSpec (m + 1) A
        (luFirstStepL A L₁) (luFirstStepU A U₁)

/-- **Problem 9.14 / pairwise pivoting**, every recursive pairwise LU
certificate is an exact ordinary LU certificate for the source matrix. -/
theorem higham_problem9_14_RecursivePairwiseLUFactSpec_to_LUFactSpec :
    ∀ {n : ℕ} {A L U : Fin n → Fin n → ℝ},
      higham_problem9_14_RecursivePairwiseLUFactSpec n A L U →
        LUFactSpec n A L U := by
  intro n A L U htrace
  induction htrace with
  | done =>
      refine
        { L_diag := ?_
          L_upper_zero := ?_
          U_lower_zero := ?_
          product_eq := ?_ }
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | step hpivot _hbubble _hschur _hnext ih =>
      exact LUFactSpec.of_firstSchurComplement_explicit hpivot ih

/-- **Problem 9.14 / pairwise pivoting**, existence of recursive pairwise LU
factors for every pre-pivoted GEPP input. -/
theorem higham_problem9_14_exists_RecursivePairwiseLUFactSpec_of_PrePivotedGEPP :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      higham_problem9_14_PrePivotedGEPP A →
        ∃ L U : Fin n → Fin n → ℝ,
          higham_problem9_14_RecursivePairwiseLUFactSpec n A L U := by
  intro n
  induction n with
  | zero =>
      intro A _hpre
      exact ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
        higham_problem9_14_RecursivePairwiseLUFactSpec.done⟩
  | succ m ih =>
      intro A hpre
      obtain ⟨L₁, U₁, hnextLU⟩ :=
        ih (A := luFirstSchurComplement A)
          (higham_problem9_14_PrePivotedGEPP_firstSchurComplement hpre)
      have hpivot : A 0 0 ≠ 0 := by
        cases hpre with
        | step _hchoice hpivot _hnext =>
            exact hpivot
      exact
        ⟨luFirstStepL A L₁, luFirstStepU A U₁,
          higham_problem9_14_RecursivePairwiseLUFactSpec.step
            hpivot
            (higham_problem9_14_pairwiseBubbleMatrix_terminal_trace A)
            (higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_firstSchurComplement_eq_rowReversed_firstSchurComplement
              (A := A) hpre)
            hnextLU⟩

/-- **Problem 9.14 / same-LU bridge**, any recursive pairwise LU certificate
for a pre-pivoted input has the same exact factors as any GEPP/no-interchange
exact LU certificate for that input. -/
theorem higham_problem9_14_RecursivePairwiseLUFactSpec_same_as_PrePivotedGEPP
    {n : ℕ} {A Lp Up Lg Ug : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (hpair : higham_problem9_14_RecursivePairwiseLUFactSpec n A Lp Up)
    (hgepp : LUFactSpec n A Lg Ug) :
    Lp = Lg ∧ Up = Ug := by
  exact higham_problem9_14_PrePivotedGEPP_lu_unique hpre
    (higham_problem9_14_RecursivePairwiseLUFactSpec_to_LUFactSpec hpair)
    hgepp

/-- **Problem 9.14 / pairwise pivoting**, the first scheduled bubble step
moves the original first row of a pre-pivoted input into row `m-1`. -/
theorem higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_one_pivot_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (hm : 0 < m) (j : Fin (m + 1)) :
    higham_problem9_14_pairwiseBubbleMatrix A 1
        (higham_problem9_14_pairwiseBubbleRow (m := m) 1) j =
      A 0 j := by
  have hp :
      higham_problem9_14_pairwiseBubbleRow (m := m) 1 ≠
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
    simpa using
      higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := 0) hm
  simpa [higham_problem9_14_pairwiseBubbleMatrix_succ,
    higham_problem9_14_pairwiseBubbleMatrix_zero] using
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row
      (A := A) hpre (p := higham_problem9_14_pairwiseBubbleRow (m := m) 1)
      hp j

/-- **Problem 9.14 / pairwise pivoting**, after two scheduled adjacent bubble
steps, the original first row of a pre-pivoted input has moved into row
`m-2`.  This packages the previously proved two-step row-motion lemma in the
explicit recursive schedule. -/
theorem higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_two_pivot_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (hm : 1 < m) (j : Fin (m + 1)) :
    higham_problem9_14_pairwiseBubbleMatrix A 2
        (higham_problem9_14_pairwiseBubbleRow (m := m) 2) j =
      A 0 j := by
  let r0 : Fin (m + 1) := higham_problem9_14_pairwiseBubbleRow (m := m) 0
  let r1 : Fin (m + 1) := higham_problem9_14_pairwiseBubbleRow (m := m) 1
  let r2 : Fin (m + 1) := higham_problem9_14_pairwiseBubbleRow (m := m) 2
  have h0m : 0 < m := lt_trans Nat.zero_lt_one hm
  have hp : r1 ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
    simpa [r1] using
      higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := 0) h0m
  have h21 : r2 ≠ r1 := by
    simpa [r1, r2] using
      higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := 1) hm
  have h2last : r2 ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
    intro h
    have hval := congrArg Fin.val h
    simp [r2, higham_problem9_14_pairwiseBubbleRow] at hval
    omega
  simpa [higham_problem9_14_pairwiseBubbleMatrix_succ,
    higham_problem9_14_pairwiseBubbleMatrix_zero, r0, r1, r2] using
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_row
      (A := A) hpre (p := r1) (i := r2) hp h21 h2last j

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: explicit
target-row update for the first-column pair pivot-and-eliminate step.  After
the last row of `ΠA` is moved into the left pivot slot, the target row carries
the original left-row data and is updated by the original first row of `A`. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) j =
      higham_problem9_14_rowReversedMatrix A p j -
        (higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j := by
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  have hsel :
      higham_problem9_14_pairPivotRow
          (higham_problem9_14_rowReversedMatrix A) 0 p last = last := by
    simpa [last] using
      higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
        hpre p
  have hnot :
      higham_problem9_14_pairPivotRow
          (higham_problem9_14_rowReversedMatrix A) 0 p last ≠ p := by
    intro h
    exact hp (h.symm.trans hsel)
  have hnot' :
      higham_problem9_14_pairPivotRow
          (higham9_2_rowPermutedMatrix A higham_problem9_14_rowReversal)
          0 p last ≠ p := by
    simpa [higham_problem9_14_rowReversedMatrix] using hnot
  have hlast :
      higham_problem9_14_rowReversal last = (0 : Fin (m + 1)) := by
    subst last
    ext
    simp [higham_problem9_14_rowReversal]
  rw [higham_problem9_14_pairPivotEliminateToLeft_target]
  subst last
  simp [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_pairPivotToLeftSwap, hnot',
    higham_problem9_14_pairRowSwap, higham_problem9_14_rowReversedMatrix, hlast]

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: the same
first-column pair pivot-and-eliminate step zeros the compared last row's active
entry. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_active_eq_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (p : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) 0 = 0 := by
  have hsel :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
      hpre p
  have hpivot :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).2
  exact
    higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero
      (higham_problem9_14_rowReversedMatrix A)
      (by simpa [hsel] using hpivot)

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: the multiplier
used by that first-column pair pivot-and-eliminate step has magnitude at most
one. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_multiplier_abs_le_one
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    |(higham_problem9_14_pairPivotToLeftMatrix
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) 0 /
      higham_problem9_14_pairPivotToLeftMatrix
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) p 0)| ≤ 1 := by
  have hsel :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
      hpre p
  have hpivot :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).2
  exact
    higham_problem9_14_pairPivotEliminateToLeft_multiplier_abs_le_one
      (A := higham_problem9_14_rowReversedMatrix A) (k := 0) (p := p)
      (q := (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) hp
      (by simpa [hsel] using hpivot)

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: the
first-column multiplier can be read in the normalized source coordinates as
`(ΠA) p 0 / A 0 0`, and has magnitude at most one. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_normalized_multiplier_abs_le_one
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    |(higham_problem9_14_rowReversedMatrix A p 0 / A 0 0)| ≤ 1 := by
  have hmul :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_multiplier_abs_le_one
      hpre hp
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  have hlast :
      higham_problem9_14_rowReversal last = (0 : Fin (m + 1)) := by
    subst last
    ext
    simp [higham_problem9_14_rowReversal]
  have hsel :
      higham_problem9_14_pairPivotRow
          (higham_problem9_14_rowReversedMatrix A) 0 p last = last := by
    simpa [last] using
      higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
        hpre p
  have hnot :
      higham_problem9_14_pairPivotRow
          (higham9_2_rowPermutedMatrix A higham_problem9_14_rowReversal)
          0 p last ≠ p := by
    intro h
    exact hp
      (h.symm.trans (by
        simpa [higham_problem9_14_rowReversedMatrix] using hsel))
  subst last
  simpa [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_pairPivotToLeftSwap, hnot,
    higham_problem9_14_pairRowSwap, higham_problem9_14_rowReversedMatrix, hlast] using
    hmul

/-- **Problem 9.14**, row reversal preserves the max-entry norm used in the
growth-factor statements. -/
theorem higham_problem9_14_rowReversedMatrix_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    maxEntryNorm hn (higham_problem9_14_rowReversedMatrix A) =
      maxEntryNorm hn A := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  apply le_antisymm
  · change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne
          (fun j => |higham_problem9_14_rowReversedMatrix A i j|)) ≤
      maxEntryNorm hn A
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix]
      using entry_le_maxEntryNorm hn A (higham_problem9_14_rowReversal i) j
  · change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |A i j|)) ≤
      maxEntryNorm hn (higham_problem9_14_rowReversedMatrix A)
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
      higham_problem9_14_rowReversal_involutive] using
      entry_le_maxEntryNorm hn (higham_problem9_14_rowReversedMatrix A)
        (higham_problem9_14_rowReversal i) j

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: one
first-column pair pivot-and-eliminate step changes the target row by at most a
factor-two max-entry bound.  This is the one-step growth estimate needed by
the row-reversal/pairwise-pivoting trace equivalence. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_abs_le_two
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    |higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) j| ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  let M : ℝ := maxEntryNorm (Nat.succ_pos m) A
  have hformula :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_row
      hpre hp j
  have hentry :
      |higham_problem9_14_rowReversedMatrix A p j| ≤ M := by
    simpa [M, higham_problem9_14_rowReversedMatrix_maxEntryNorm
        (Nat.succ_pos m) A] using
      entry_le_maxEntryNorm (Nat.succ_pos m)
        (higham_problem9_14_rowReversedMatrix A) p j
  have hpivotrow : |A 0 j| ≤ M := by
    simpa [M] using entry_le_maxEntryNorm (Nat.succ_pos m) A 0 j
  have hratio :
      |higham_problem9_14_rowReversedMatrix A p 0 / A 0 0| ≤ 1 :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_normalized_multiplier_abs_le_one
      hpre hp
  have hterm :
      |(higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j| ≤
        M := by
    calc
      |(higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j|
          = |higham_problem9_14_rowReversedMatrix A p 0 / A 0 0| * |A 0 j| := by
            rw [abs_mul]
      _ ≤ 1 * |A 0 j| :=
            mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
      _ ≤ 1 * M :=
            mul_le_mul_of_nonneg_left hpivotrow zero_le_one
      _ = M := by ring
  rw [hformula]
  calc
    |higham_problem9_14_rowReversedMatrix A p j -
        (higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j| ≤
        |higham_problem9_14_rowReversedMatrix A p j| +
          |(higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (higham_problem9_14_rowReversedMatrix A p j)
              (-((higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j))
    _ ≤ M + M := add_le_add hentry hterm
    _ = 2 * maxEntryNorm (Nat.succ_pos m) A := by simp [M, two_mul]

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: the whole
matrix produced by one first-column pair pivot-and-eliminate step has max-entry
norm bounded by `2 * maxEntryNorm A`.  This packages the target-row bound with
the fact that the other rows are only row-permuted entries of `ΠA`. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_maxEntryNorm_le_two
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    maxEntryNorm (Nat.succ_pos m)
      (higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  let M : ℝ := maxEntryNorm (Nat.succ_pos m) A
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  refine higham9_13_maxEntryNorm_bound_of_entry_bound (Nat.succ_pos m)
    (higham_problem9_14_pairPivotEliminateToLeft
      (higham_problem9_14_rowReversedMatrix A) 0 p last)
    (2 * maxEntryNorm (Nat.succ_pos m) A) ?_
  intro i j
  by_cases hi : i = last
  · subst i
    simpa [last] using
      higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_abs_le_two
        hpre hp j
  · have hrow :=
      higham_problem9_14_pairPivotEliminateToLeft_of_ne
        (A := higham_problem9_14_rowReversedMatrix A) (k := 0) (p := p)
        (q := last) (i := i) (j := j) hi
    rw [hrow]
    have hentry :
        |higham_problem9_14_pairPivotToLeftMatrix
            (higham_problem9_14_rowReversedMatrix A) 0 p last i j| ≤
          M := by
      unfold higham_problem9_14_pairPivotToLeftMatrix
      simpa [M, higham9_2_rowPermutedMatrix,
        higham_problem9_14_rowReversedMatrix_maxEntryNorm
          (Nat.succ_pos m) A] using
        entry_le_maxEntryNorm (Nat.succ_pos m)
          (higham_problem9_14_rowReversedMatrix A)
          (higham_problem9_14_pairPivotToLeftSwap
            (higham_problem9_14_rowReversedMatrix A) 0 p last i) j
    have hM_nonneg : 0 ≤ M := maxEntryNorm_nonneg (Nat.succ_pos m) A
    have hM_le : M ≤ 2 * maxEntryNorm (Nat.succ_pos m) A := by
      dsimp [M] at hM_nonneg ⊢
      nlinarith
    exact le_trans hentry hM_le

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: the one-step
pair pivot-and-eliminate matrix has max-entry growth factor at most two
relative to the row-reversed input.  This is only the first-step quotient; the
cumulative row-reversal/pairwise trace equivalence remains separate. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_growthFactorEntry_le_two
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hAmax : 0 < maxEntryNorm (Nat.succ_pos m) A) :
    growthFactorEntry (Nat.succ_pos m)
      (higham_problem9_14_rowReversedMatrix A)
      (higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
      (by
        simpa [higham_problem9_14_rowReversedMatrix_maxEntryNorm
          (Nat.succ_pos m) A] using hAmax) ≤ 2 := by
  have hmax :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_maxEntryNorm_le_two
      hpre hp
  unfold growthFactorEntry
  rw [higham_problem9_14_rowReversedMatrix_maxEntryNorm (Nat.succ_pos m) A]
  rwa [div_le_iff₀ hAmax]

/-- **Problem 9.14**, row reversal preserves positivity of the max-entry
denominator used by `growthFactorEntry`. -/
theorem higham_problem9_14_rowReversedMatrix_maxEntryNorm_pos {n : ℕ} (hn : 0 < n)
    {A : Fin n → Fin n → ℝ} (hA : 0 < maxEntryNorm hn A) :
    0 < maxEntryNorm hn (higham_problem9_14_rowReversedMatrix A) := by
  simpa [higham_problem9_14_rowReversedMatrix_maxEntryNorm hn A] using hA

/-- **Problem 9.14**, if a row-reversed input and the original input produce
the same final upper factor, then the max-entry growth-factor quotient has the
same denominator.  This does not assert the missing pivoting trace equivalence;
it is the local norm bridge needed once that trace supplies the common `U`. -/
theorem higham_problem9_14_rowReversedMatrix_growthFactorEntry_eq {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hRev : 0 < maxEntryNorm hn (higham_problem9_14_rowReversedMatrix A)) :
    growthFactorEntry hn (higham_problem9_14_rowReversedMatrix A) U hRev =
      growthFactorEntry hn A U hA := by
  unfold growthFactorEntry
  rw [higham_problem9_14_rowReversedMatrix_maxEntryNorm hn A]

/-- Prefix dot products from Algorithm 9.2 are bounded by the corresponding
entry of `|L||U|`. -/
theorem higham9_2_rectPrefixDot_abs_le_absLUProduct {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) :
    |higham9_2_rectPrefixDot L U i j k| ≤
      ∑ s : Fin n, |L i s| * |U s j| := by
  unfold higham9_2_rectPrefixDot
  calc
    |∑ s : Fin n, (if s.val < k.val then L i s * U s j else 0)|
        ≤ ∑ s : Fin n, |if s.val < k.val then L i s * U s j else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Fin n, |L i s| * |U s j| := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s.val < k.val
      · simp [hs, abs_mul]
      · simp [hs, mul_nonneg (abs_nonneg (L i s)) (abs_nonneg (U s j))]

/-- A reduced entry from equation (9.5) is bounded by the initial max-entry
norm plus the infinity norm of `|L||U|`. -/
theorem higham9_5_rectGEReducedEntry_abs_le_maxEntryNorm_add_absLU_infNorm
    {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ) (step : Fin n) (i j : Fin n) :
    |higham9_5_rectGEReducedEntry A L U step.val i j| ≤
      maxEntryNorm hn A +
        infNorm (matMul n (absMatrix n L) (absMatrix n U)) := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  have hprefix :
      |higham9_2_rectPrefixDot L U i j step| ≤ W i j := by
    have hraw := higham9_2_rectPrefixDot_abs_le_absLUProduct L U i j step
    simpa [W, matMul, absMatrix] using hraw
  have hW_nonneg : ∀ p q : Fin n, 0 ≤ W p q := by
    intro p q
    unfold W matMul absMatrix
    exact Finset.sum_nonneg fun r _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hWij_le_inf : W i j ≤ infNorm W := by
    have hWij_le_row : W i j ≤ ∑ q : Fin n, |W i q| := by
      have hsingle :
          (fun q : Fin n => |W i q|) j ≤
            ∑ q : Fin n, (fun q : Fin n => |W i q|) q :=
        Finset.single_le_sum
          (s := Finset.univ) (f := fun q : Fin n => |W i q|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      simpa [abs_of_nonneg (hW_nonneg i j)] using hsingle
    exact le_trans hWij_le_row (row_sum_le_infNorm W i)
  rw [higham9_5_rectGEReducedEntry_eq_rectPrefixDot A L U i j step]
  calc
    |A i j - higham9_2_rectPrefixDot L U i j step|
        ≤ |A i j| + |higham9_2_rectPrefixDot L U i j step| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le (A i j) (-(higham9_2_rectPrefixDot L U i j step))
    _ ≤ maxEntryNorm hn A + W i j :=
      add_le_add (entry_le_maxEntryNorm hn A i j) hprefix
    _ ≤ maxEntryNorm hn A + infNorm W :=
      add_le_add (le_refl _) hWij_le_inf

/-- **Equation (9.5)** after all `n` rank-one updates: the natural-number
prefix is the full `L*U` entry. -/
theorem higham9_5_rectPrefixRange_full_eq_matMul {n : ℕ}
    (L U : Fin n → Fin n → ℝ) (i j : Fin n) :
    higham9_5_rectPrefixRange L U i j n =
      ∑ k : Fin n, L i k * U k j := by
  unfold higham9_5_rectPrefixRange
  let g : ℕ → ℝ := fun r =>
    if h : r < n then L i ⟨r, h⟩ * U ⟨r, h⟩ j else 0
  calc
    (∑ r ∈ Finset.range n,
        if h : r < n then L i ⟨r, h⟩ * U ⟨r, h⟩ j else 0)
        = ∑ r ∈ Finset.range n, g r := rfl
    _ = ∑ k : Fin n, g k.val := by
        rw [← Fin.sum_univ_eq_sum_range g n]
    _ = ∑ k : Fin n, L i k * U k j := by
        apply Finset.sum_congr rfl
        intro k _
        have hk : (⟨k.val, k.isLt⟩ : Fin n) = k := by ext; rfl
        simp [g, k.isLt, hk]

/-- **Equation (9.5)** terminal residual: for an exact LU certificate, the
reduced entry after all rank-one updates is zero. -/
theorem higham9_5_rectGEReducedEntry_full_eq_zero_of_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) (i j : Fin n) :
    higham9_5_rectGEReducedEntry A L U n i j = 0 := by
  unfold higham9_5_rectGEReducedEntry
  rw [higham9_5_rectPrefixRange_full_eq_matMul L U i j, hLU.product_eq i j]
  ring

/-- **Lemma 9.6**, local rank-one stage estimate: the `k`th absolute LU
outer-product entry is bounded by the neighboring exact no-pivot reduced
matrices from equation (9.5). -/
theorem higham9_6_rankOne_abs_le_reduced_add_succ {n : ℕ}
    (A L U : Fin n → Fin n → ℝ) (k : Fin n) (i j : Fin n) :
    |L i k * U k j| ≤
      |higham9_5_rectGEReducedEntry A L U k.val i j| +
        |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j| := by
  have hrec :=
    higham9_5_rectGEReducedEntry_succ_of_lt A L U k.val k.isLt i j
  have hk : (⟨k.val, k.isLt⟩ : Fin n) = k := by ext; rfl
  rw [hk] at hrec
  have hterm :
      L i k * U k j =
        higham9_5_rectGEReducedEntry A L U k.val i j -
          higham9_5_rectGEReducedEntry A L U (k.val + 1) i j := by
    linarith
  rw [hterm]
  simpa [sub_eq_add_neg, abs_neg] using
    abs_add_le
      (higham9_5_rectGEReducedEntry A L U k.val i j)
      (-(higham9_5_rectGEReducedEntry A L U (k.val + 1) i j))

/-- **Lemma 9.6**, stage-pair row-sum bridge: once the neighboring reduced
matrix rows from equation (9.5) have the source row-sum budget, the absolute
LU product has the corresponding infinity-norm budget. -/
theorem higham9_6_absLU_infNorm_le_of_reduced_stage_pair_rows {n : ℕ}
    (A L U : Fin n → Fin n → ℝ) (C : ℝ)
    (hrows : ∀ i : Fin n,
      ∑ k : Fin n, ∑ j : Fin n,
        (|higham9_5_rectGEReducedEntry A L U k.val i j| +
          |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|) ≤ C)
    (hC : 0 ≤ C) :
    infNorm (matMul n (absMatrix n L) (absMatrix n U)) ≤ C := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  have hW_nonneg : ∀ i j : Fin n, 0 ≤ W i j := by
    intro i j
    unfold W matMul absMatrix
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |W i j|
          = ∑ j : Fin n, W i j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hW_nonneg i j)]
      _ = ∑ j : Fin n, ∑ k : Fin n, |L i k| * |U k j| := by
            simp [W, matMul, absMatrix]
      _ = ∑ j : Fin n, ∑ k : Fin n, |L i k * U k j| := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            rw [abs_mul]
      _ ≤ ∑ j : Fin n, ∑ k : Fin n,
            (|higham9_5_rectGEReducedEntry A L U k.val i j| +
              |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|) := by
            apply Finset.sum_le_sum
            intro j _
            apply Finset.sum_le_sum
            intro k _
            exact higham9_6_rankOne_abs_le_reduced_add_succ A L U k i j
      _ = ∑ k : Fin n, ∑ j : Fin n,
            (|higham9_5_rectGEReducedEntry A L U k.val i j| +
              |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|) := by
            rw [Finset.sum_comm]
      _ ≤ C := hrows i
  · exact hC

/-- **Lemma 9.6**, row-budget accumulation form: a uniform row-sum budget for
each exact reduced stage in equation (9.5), including the terminal stage,
implies the corresponding `|L||U|` infinity-norm budget. -/
theorem higham9_6_absLU_infNorm_le_two_card_mul_of_reduced_stage_row_bounds {n : ℕ}
    (A L U : Fin n → Fin n → ℝ) (C : ℝ)
    (hstageRows : ∀ step : ℕ, step ≤ n →
      ∀ i : Fin n,
        ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U step i j| ≤ C)
    (hC : 0 ≤ C) :
    infNorm (matMul n (absMatrix n L) (absMatrix n U)) ≤
      (2 * (n : ℝ)) * C := by
  apply higham9_6_absLU_infNorm_le_of_reduced_stage_pair_rows
    A L U ((2 * (n : ℝ)) * C)
  · intro i
    have hfirst :
        (∑ k : Fin n,
          ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U k.val i j|) ≤
          ∑ _k : Fin n, C := by
      apply Finset.sum_le_sum
      intro k _
      exact hstageRows k.val (le_of_lt k.isLt) i
    have hsecond :
        (∑ k : Fin n,
          ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|) ≤
          ∑ _k : Fin n, C := by
      apply Finset.sum_le_sum
      intro k _
      exact hstageRows (k.val + 1) (Nat.succ_le_of_lt k.isLt) i
    calc
      ∑ k : Fin n, ∑ j : Fin n,
          (|higham9_5_rectGEReducedEntry A L U k.val i j| +
            |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|)
          = (∑ k : Fin n,
              ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U k.val i j|) +
            (∑ k : Fin n,
              ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_add_distrib]
      _ ≤ (∑ _k : Fin n, C) + ∑ _k : Fin n, C :=
            add_le_add hfirst hsecond
      _ = (2 * (n : ℝ)) * C := by
            simp [Fintype.card_fin]
            ring
  · exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hC

/-- **Lemma 9.6**, finite stage counting: summing neighboring exact reduced
stages counts the initial and terminal stages once and all intermediate stages
twice.  This is the bookkeeping step behind Higham's
`|A| + 2 ∑_{k=2}^n |A^(k)|` line. -/
theorem higham9_6_sum_stage_pair_eq_endpoints_add_two_range {n : ℕ}
    (hn : 0 < n) (row : ℕ → ℝ) :
    (∑ k : Fin n, (row k.val + row (k.val + 1))) =
      row 0 + row n + 2 * ∑ r ∈ Finset.range (n - 1), row (r + 1) := by
  have hn1 : 1 ≤ n := Nat.succ_le_iff.mpr hn
  have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  have hsum_fin :
      (∑ k : Fin n, (row k.val + row (k.val + 1))) =
        ∑ k ∈ Finset.range n, (row k + row (k + 1)) := by
    simpa using
      (Fin.sum_univ_eq_sum_range (fun k : ℕ => row k + row (k + 1)) n)
  have hfirst :
      (∑ k ∈ Finset.range n, row k) =
        row 0 + ∑ r ∈ Finset.range (n - 1), row (r + 1) := by
    conv_lhs => rw [← hn_eq]
    rw [Finset.sum_range_succ']
    ring
  have hsecond :
      (∑ k ∈ Finset.range n, row (k + 1)) =
        (∑ r ∈ Finset.range (n - 1), row (r + 1)) + row n := by
    conv_lhs => rw [← hn_eq]
    rw [Finset.sum_range_succ]
    simp [hn_eq]
  rw [hsum_fin, Finset.sum_add_distrib, hfirst, hsecond]
  ring

/-- **Lemma 9.6**, source counting budget with an explicit reduced-stage
growth hypothesis.  If every intermediate reduced stage has entries bounded by
`rho * maxEntryNorm A`, then the already proved rank-one stage estimate gives
Higham's printed infinity-norm constant. -/
theorem higham9_6_absLU_infNorm_le_source_constant_of_reduced_entry_growth {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ) (rho : ℝ)
    (hLU : LUFactSpec n A L U)
    (hrho : 0 ≤ rho)
    (hstage : ∀ step : ℕ, 1 ≤ step → step < n →
      ∀ i j : Fin n,
        |higham9_5_rectGEReducedEntry A L U step i j| ≤
          rho * maxEntryNorm hn A) :
    infNorm (matMul n (absMatrix n L) (absMatrix n U)) ≤
      (1 + 2 * ((n : ℝ) ^ 2 - (n : ℝ)) * rho) * infNorm A := by
  have hn1 : 1 ≤ n := Nat.succ_le_iff.mpr hn
  have hcast_pred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  have hn_minus_nonneg : 0 ≤ (n : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hn1)
  have hcoef_nonneg :
      0 ≤ 1 + 2 * ((n : ℝ) ^ 2 - (n : ℝ)) * rho := by
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hquad_nonneg : 0 ≤ (n : ℝ) ^ 2 - (n : ℝ) := by
      have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
        mul_nonneg hn_nonneg hn_minus_nonneg
      nlinarith [hprod]
    have hterm : 0 ≤ 2 * ((n : ℝ) ^ 2 - (n : ℝ)) * rho :=
      mul_nonneg (mul_nonneg (by norm_num) hquad_nonneg) hrho
    exact add_nonneg zero_le_one hterm
  apply higham9_6_absLU_infNorm_le_of_reduced_stage_pair_rows
    A L U ((1 + 2 * ((n : ℝ) ^ 2 - (n : ℝ)) * rho) * infNorm A)
  · intro i
    let row : ℕ → ℝ := fun step =>
      ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U step i j|
    have hpair :
        (∑ k : Fin n,
          ∑ j : Fin n,
            (|higham9_5_rectGEReducedEntry A L U k.val i j| +
              |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|)) =
          ∑ k : Fin n, (row k.val + row (k.val + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp [row, Finset.sum_add_distrib]
    have hcount := higham9_6_sum_stage_pair_eq_endpoints_add_two_range hn row
    have hrow0 : row 0 = ∑ j : Fin n, |A i j| := by
      apply Finset.sum_congr rfl
      intro j _
      simp [higham9_5_rectGEReducedEntry_zero]
    have hrow0_le : row 0 ≤ infNorm A := by
      rw [hrow0]
      exact row_sum_le_infNorm A i
    have hrown : row n = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [higham9_5_rectGEReducedEntry_full_eq_zero_of_LUFactSpec hLU]
    have hrow_intermediate :
        ∑ r ∈ Finset.range (n - 1), row (r + 1) ≤
          ∑ _r ∈ Finset.range (n - 1), (n : ℝ) * rho * infNorm A := by
      apply Finset.sum_le_sum
      intro r hr
      have hr_lt_pred : r < n - 1 := Finset.mem_range.mp hr
      have hstep_lt : r + 1 < n := by omega
      have hrow_to_max :
          row (r + 1) ≤ ∑ _j : Fin n, rho * maxEntryNorm hn A := by
        apply Finset.sum_le_sum
        intro j _
        exact hstage (r + 1) (Nat.succ_le_succ (Nat.zero_le r)) hstep_lt i j
      have hmax_to_inf :
          (n : ℝ) * rho * maxEntryNorm hn A ≤ (n : ℝ) * rho * infNorm A := by
        exact mul_le_mul_of_nonneg_left (maxEntryNorm_le_infNorm hn A)
          (mul_nonneg (Nat.cast_nonneg n) hrho)
      calc
        row (r + 1) ≤ ∑ _j : Fin n, rho * maxEntryNorm hn A := hrow_to_max
        _ = (n : ℝ) * rho * maxEntryNorm hn A := by
            simp [Fintype.card_fin]
            ring
        _ ≤ (n : ℝ) * rho * infNorm A := hmax_to_inf
    have hsum_const :
        (∑ _r ∈ Finset.range (n - 1), (n : ℝ) * rho * infNorm A) =
          ((n - 1 : ℕ) : ℝ) * ((n : ℝ) * rho * infNorm A) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hpair, hcount]
    calc
      row 0 + row n + 2 * ∑ r ∈ Finset.range (n - 1), row (r + 1)
          ≤ infNorm A + 0 +
              2 * (((n - 1 : ℕ) : ℝ) * ((n : ℝ) * rho * infNorm A)) := by
            apply add_le_add
            · exact add_le_add hrow0_le (by rw [hrown])
            · exact mul_le_mul_of_nonneg_left
                (le_trans hrow_intermediate (le_of_eq hsum_const)) (by norm_num)
      _ = (1 + 2 * ((n : ℝ) ^ 2 - (n : ℝ)) * rho) * infNorm A := by
            rw [hcast_pred]
            ring
  · exact mul_nonneg hcoef_nonneg (infNorm_nonneg A)

/-- **Problem 9.9**, the source max over exact no-pivot reduced matrices
`A^(1), ..., A^(n)`, represented as equation (9.5) stages `0, ..., n-1`. -/
noncomputable def higham_problem9_9_noPivotReducedEntryMax {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin n))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun step : Fin n =>
      maxEntryNorm hn
        (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U step.val i j))

/-- **Problem 9.9**, source no-pivot growth factor over all exact reduced
matrices generated by equation (9.5). -/
noncomputable def higham_problem9_9_noPivotReducedGrowthFactor {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (_hAmax : 0 < maxEntryNorm hn A) : ℝ :=
  higham_problem9_9_noPivotReducedEntryMax hn A L U / maxEntryNorm hn A

/-- **Problem 9.6 / equation (9.5)** support: a no-pivot prefix product is
nonnegative when both exact factors are componentwise nonnegative. -/
theorem higham9_5_rectPrefixRange_nonneg_of_nonnegative_factors {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (hL_nn : ∀ i k, 0 ≤ L i k) (hU_nn : ∀ k j, 0 ≤ U k j)
    (i : Fin m) (j : Fin n) (steps : ℕ) :
    0 ≤ higham9_5_rectPrefixRange L U i j steps := by
  unfold higham9_5_rectPrefixRange
  apply Finset.sum_nonneg
  intro r _hr
  by_cases hrn : r < n
  · simpa [hrn] using mul_nonneg (hL_nn i ⟨r, hrn⟩) (hU_nn ⟨r, hrn⟩ j)
  · simp [hrn]

/-- **Problem 9.6 / equation (9.5)** support: under componentwise nonnegative
exact factors, every no-pivot prefix is bounded by the full product prefix. -/
theorem higham9_5_rectPrefixRange_le_full_of_nonnegative_factors {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (hL_nn : ∀ i k, 0 ≤ L i k) (hU_nn : ∀ k j, 0 ≤ U k j)
    (i : Fin m) (j : Fin n) {steps : ℕ} (hsteps : steps ≤ n) :
    higham9_5_rectPrefixRange L U i j steps ≤
      higham9_5_rectPrefixRange L U i j n := by
  unfold higham9_5_rectPrefixRange
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hr) hsteps)
  · intro r _hrn hrsteps
    by_cases hrn : r < n
    · simpa [hrn] using mul_nonneg (hL_nn i ⟨r, hrn⟩) (hU_nn ⟨r, hrn⟩ j)
    · simp [hrn]

/-- **Problem 9.6**, exact reduced-entry no-growth from a nonnegative
no-pivot LU certificate.  Each reduced entry in equation (9.5) is the
nonnegative tail of the exact product `A = L*U`, hence its absolute value is
bounded by the corresponding source entry. -/
theorem higham9_6_reducedEntry_abs_le_maxEntryNorm_of_nonnegative_LU {n : ℕ}
    (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k, 0 ≤ L i k)
    (hU_nn : ∀ k j, 0 ≤ U k j)
    (step : Fin n) (i j : Fin n) :
    |higham9_5_rectGEReducedEntry A L U step.val i j| ≤ maxEntryNorm hn A := by
  have hprefix_nonneg :
      0 ≤ higham9_5_rectPrefixRange L U i j step.val :=
    higham9_5_rectPrefixRange_nonneg_of_nonnegative_factors
      L U hL_nn hU_nn i j step.val
  have hprefix_le_full :
      higham9_5_rectPrefixRange L U i j step.val ≤
        higham9_5_rectPrefixRange L U i j n :=
    higham9_5_rectPrefixRange_le_full_of_nonnegative_factors
      L U hL_nn hU_nn i j (le_of_lt step.isLt)
  have hfull_eq :
      higham9_5_rectPrefixRange L U i j n = A i j := by
    rw [higham9_5_rectPrefixRange_full_eq_matMul L U i j, hLU.product_eq i j]
  have hA_nonneg : 0 ≤ A i j := by
    rw [← hfull_eq]
    exact higham9_5_rectPrefixRange_nonneg_of_nonnegative_factors
      L U hL_nn hU_nn i j n
  have hred_nonneg :
      0 ≤ higham9_5_rectGEReducedEntry A L U step.val i j := by
    unfold higham9_5_rectGEReducedEntry
    rw [← hfull_eq]
    exact sub_nonneg.mpr hprefix_le_full
  have hred_le_A :
      higham9_5_rectGEReducedEntry A L U step.val i j ≤ A i j := by
    unfold higham9_5_rectGEReducedEntry
    exact sub_le_self _ hprefix_nonneg
  calc
    |higham9_5_rectGEReducedEntry A L U step.val i j|
        = higham9_5_rectGEReducedEntry A L U step.val i j :=
          abs_of_nonneg hred_nonneg
    _ ≤ A i j := hred_le_A
    _ = |A i j| := (abs_of_nonneg hA_nonneg).symm
    _ ≤ maxEntryNorm hn A := entry_le_maxEntryNorm hn A i j

/-- **Problem 9.6**, source reduced-matrix growth endpoint from a nonnegative
no-pivot LU certificate: the max-entry growth factor over all exact reduced
matrices in equation (9.5) is at most one. -/
theorem higham_problem9_9_noPivotReducedGrowthFactor_le_one_of_nonnegative_LU
    {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k, 0 ≤ L i k)
    (hU_nn : ∀ k j, 0 ≤ U k j)
    (hAmax : 0 < maxEntryNorm hn A) :
    higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 1 := by
  have hentryMax_le :
      higham_problem9_9_noPivotReducedEntryMax hn A L U ≤ maxEntryNorm hn A := by
    unfold higham_problem9_9_noPivotReducedEntryMax
    apply Finset.sup'_le
    intro step _hstep
    unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _hi
    apply Finset.sup'_le
    intro j _hj
    exact higham9_6_reducedEntry_abs_le_maxEntryNorm_of_nonnegative_LU
      hn hLU hL_nn hU_nn step i j
  unfold higham_problem9_9_noPivotReducedGrowthFactor
  rw [div_le_iff₀ hAmax]
  simpa using hentryMax_le

/-- **Lemma 9.6**, source-constant form using the no-pivot reduced growth
factor from Problem 9.9.  This packages the explicit reduced-stage growth
hypothesis of `higham9_6_absLU_infNorm_le_source_constant_of_reduced_entry_growth`
with the actual max over equation (9.5) reduced matrices. -/
theorem higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor
    {n : ℕ} (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hAmax : 0 < maxEntryNorm hn A) :
    infNorm (matMul n (absMatrix n L) (absMatrix n U)) ≤
      (1 + 2 * ((n : ℝ) ^ 2 - (n : ℝ)) *
        higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax) *
        infNorm A := by
  have hmax_nonneg :
      0 ≤ higham_problem9_9_noPivotReducedEntryMax hn A L U := by
    let step0 : Fin n := ⟨0, hn⟩
    have hstage0_nonneg :
        0 ≤ maxEntryNorm hn
          (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U step0.val i j) :=
      maxEntryNorm_nonneg hn _
    have hstage0_le :
        maxEntryNorm hn
          (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U step0.val i j) ≤
          higham_problem9_9_noPivotReducedEntryMax hn A L U := by
      unfold higham_problem9_9_noPivotReducedEntryMax
      exact Finset.le_sup' (fun step : Fin n =>
        maxEntryNorm hn
          (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U step.val i j))
        (Finset.mem_univ step0)
    exact le_trans hstage0_nonneg hstage0_le
  have hgrowth_nonneg :
      0 ≤ higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax := by
    unfold higham_problem9_9_noPivotReducedGrowthFactor
    exact div_nonneg hmax_nonneg (le_of_lt hAmax)
  apply higham9_6_absLU_infNorm_le_source_constant_of_reduced_entry_growth
    hn A L U (higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax)
    hLU hgrowth_nonneg
  intro step _hstep_pos hstep_lt i j
  let stepFin : Fin n := ⟨step, hstep_lt⟩
  have hentry_le_stage :
      |higham9_5_rectGEReducedEntry A L U step i j| ≤
        maxEntryNorm hn
          (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U stepFin.val i j) := by
    simpa [stepFin] using
      entry_le_maxEntryNorm hn
        (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U stepFin.val i j)
        i j
  have hstage_le_max :
      maxEntryNorm hn
        (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U stepFin.val i j) ≤
        higham_problem9_9_noPivotReducedEntryMax hn A L U := by
    unfold higham_problem9_9_noPivotReducedEntryMax
    exact Finset.le_sup' (fun step : Fin n =>
      maxEntryNorm hn
        (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U step.val i j))
      (Finset.mem_univ stepFin)
  have hmul_eq :
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax *
          maxEntryNorm hn A =
        higham_problem9_9_noPivotReducedEntryMax hn A L U := by
    unfold higham_problem9_9_noPivotReducedGrowthFactor
    field_simp [ne_of_gt hAmax]
  calc
    |higham9_5_rectGEReducedEntry A L U step i j|
        ≤ higham_problem9_9_noPivotReducedEntryMax hn A L U :=
          le_trans hentry_le_stage hstage_le_max
    _ = higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax *
          maxEntryNorm hn A := by
          rw [← hmul_eq]

/-- **Problem 9.9**, stage-max form before division by the initial matrix
size: every exact no-pivot reduced matrix from equation (9.5) is bounded by
`max |A| + || |L||U| ||_∞`. -/
theorem higham_problem9_9_noPivotReducedEntryMax_le_maxEntryNorm_add_absLU_infNorm
    {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ) :
    higham_problem9_9_noPivotReducedEntryMax hn A L U ≤
      maxEntryNorm hn A +
        infNorm (matMul n (absMatrix n L) (absMatrix n U)) := by
  unfold higham_problem9_9_noPivotReducedEntryMax
  apply Finset.sup'_le
  intro step _
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact higham9_5_rectGEReducedEntry_abs_le_maxEntryNorm_add_absLU_infNorm
    hn A L U step i j

/-- **Problem 9.9**, source-facing exact no-pivot reduced-matrix growth bound:
`rho_n <= 1 + n * || |L||U| ||_inf / ||A||_inf`.

Here `rho_n` is formalized as the maximum, over the exact reduced matrices in
equation (9.5), of the max-entry size divided by the initial max-entry size. -/
theorem higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_absLU_infNorm_div
    {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hAinf : 0 < infNorm A) :
    higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤
      1 + (n : ℝ) *
        infNorm (matMul n (absMatrix n L) (absMatrix n U)) / infNorm A := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  have hentryMax :
      higham_problem9_9_noPivotReducedEntryMax hn A L U ≤
        maxEntryNorm hn A + infNorm W := by
    simpa [W] using
      higham_problem9_9_noPivotReducedEntryMax_le_maxEntryNorm_add_absLU_infNorm
        hn A L U
  have hdivMax :
      higham_problem9_9_noPivotReducedEntryMax hn A L U / maxEntryNorm hn A ≤
        (maxEntryNorm hn A + infNorm W) / maxEntryNorm hn A :=
    div_le_div_of_nonneg_right hentryMax (le_of_lt hAmax)
  have hdivBound :
      (maxEntryNorm hn A + infNorm W) / maxEntryNorm hn A ≤
        1 + (n : ℝ) * infNorm W / infNorm A := by
    have hWnorm_nonneg : 0 ≤ infNorm W := infNorm_nonneg W
    have hmax_ne : maxEntryNorm hn A ≠ 0 := ne_of_gt hAmax
    have hW_div :
        infNorm W / maxEntryNorm hn A ≤ (n : ℝ) * infNorm W / infNorm A := by
      have hAinf_le : infNorm A ≤ (n : ℝ) * maxEntryNorm hn A :=
        infNorm_le_card_mul_maxEntryNorm hn A
      have hmul :
          infNorm W * infNorm A ≤
            infNorm W * ((n : ℝ) * maxEntryNorm hn A) :=
        mul_le_mul_of_nonneg_left hAinf_le hWnorm_nonneg
      have hcross :
          infNorm W * infNorm A ≤
            (n : ℝ) * infNorm W * maxEntryNorm hn A := by
        calc
          infNorm W * infNorm A
              ≤ infNorm W * ((n : ℝ) * maxEntryNorm hn A) := hmul
          _ = (n : ℝ) * infNorm W * maxEntryNorm hn A := by ring
      exact (div_le_div_iff₀ hAmax hAinf).mpr hcross
    calc
      (maxEntryNorm hn A + infNorm W) / maxEntryNorm hn A
          = 1 + infNorm W / maxEntryNorm hn A := by
        field_simp [hmax_ne]
      _ ≤ 1 + (n : ℝ) * infNorm W / infNorm A :=
        by simpa [add_comm] using add_le_add_left hW_div 1
  unfold higham_problem9_9_noPivotReducedGrowthFactor
  exact le_trans hdivMax hdivBound

/-- **Problem 9.9**, source-facing max-entry growth bound for exact no-pivot
LU factors: `rho_n <= 1 + n * || |L||U| ||_inf / ||A||_inf`.

The remaining algorithmic part of the source problem is the separate proof that
the factors supplied here are exactly those generated by GE without pivoting. -/
theorem higham_problem9_9_growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div
    {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hAmax : 0 < maxEntryNorm hn A)
    (hAinf : 0 < infNorm A) :
    growthFactorEntry hn A U hAmax ≤
      1 + (n : ℝ) *
        infNorm (matMul n (absMatrix n L) (absMatrix n U)) / infNorm A :=
  growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div hn hLU hAmax hAinf

/-- **Problem 9.10**, the rank-one matrix `e_i e_j^T` used to model a
single multiplier error as a rank-one perturbation. -/
noncomputable def higham_problem9_10_rankOneBasis {n : ℕ} (i j : Fin n) :
    Fin n → Fin n → ℝ :=
  fun r c => finiteBasisVec i r * finiteBasisVec j c

/-- **Problem 9.10**, the scalar perturbation coefficient
`α = ε * \hat l_ij * \hat u_jj`. -/
noncomputable def higham_problem9_10_multiplierBlunderAlpha
    (epsilon lhatij uhatjj : ℝ) : ℝ :=
  epsilon * lhatij * uhatjj

/-- **Problem 9.10**, matrix-vector action of the rank-one basis
`e_i e_j^T`. -/
theorem higham_problem9_10_rankOneBasis_mulVec {n : ℕ}
    (i j : Fin n) (v : Fin n → ℝ) :
    matMulVec n (higham_problem9_10_rankOneBasis i j) v =
      fun r => finiteBasisVec i r * v j := by
  ext r
  unfold matMulVec higham_problem9_10_rankOneBasis
  have hbasis : (∑ c : Fin n, finiteBasisVec j c * v c) = v j := by
    unfold finiteBasisVec
    rw [Finset.sum_eq_single j]
    · simp
    · intro c _ hc
      simp [hc]
    · simp
  calc
    ∑ c : Fin n, (finiteBasisVec i r * finiteBasisVec j c) * v c
        = finiteBasisVec i r * (∑ c : Fin n, finiteBasisVec j c * v c) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _
            ring
    _ = finiteBasisVec i r * v j := by rw [hbasis]

/-- **Problem 9.10**, matrix-vector action of the perturbed matrix
`A - α e_i e_j^T`. -/
theorem higham_problem9_10_rankOnePerturbed_mulVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (v : Fin n → ℝ) :
    matMulVec n
        (fun r c => A r c - alpha * higham_problem9_10_rankOneBasis i j r c) v =
      fun r => matMulVec n A v r - alpha * finiteBasisVec i r * v j := by
  ext r
  have hrank := congrFun (higham_problem9_10_rankOneBasis_mulVec i j v) r
  have hrank_sum :
      (∑ c : Fin n, higham_problem9_10_rankOneBasis i j r c * v c) =
        finiteBasisVec i r * v j := by
    simpa [matMulVec] using hrank
  unfold matMulVec
  calc
    ∑ c : Fin n,
        (A r c - alpha * higham_problem9_10_rankOneBasis i j r c) * v c
        = (∑ c : Fin n, A r c * v c) -
            ∑ c : Fin n,
              alpha * (higham_problem9_10_rankOneBasis i j r c * v c) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro c _
            ring
    _ = (∑ c : Fin n, A r c * v c) -
          alpha *
            (∑ c : Fin n, higham_problem9_10_rankOneBasis i j r c * v c) := by
            rw [Finset.mul_sum]
    _ = (∑ c : Fin n, A r c * v c) -
          alpha * (finiteBasisVec i r * v j) := by
            rw [hrank_sum]
    _ = (∑ c : Fin n, A r c * v c) - alpha * finiteBasisVec i r * v j := by
            ring

/-- **Problem 9.10**, applying an available left inverse to a matrix-vector
equation. -/
theorem higham_problem9_10_apply_left_inverse_of_matMulVec_eq {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ) (d rhs : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hd : matMulVec n A d = rhs) :
    d = matMulVec n A_inv rhs := by
  have hprod : matMul n A_inv A = idMatrix n := by
    ext r c
    simpa [matMul] using hInv r c
  ext r
  calc
    d r = matMulVec n (idMatrix n) d r := by
      rw [matMulVec_id]
    _ = matMulVec n (matMul n A_inv A) d r := by
      rw [hprod]
    _ = matMulVec n A_inv (matMulVec n A d) r :=
      matMulVec_matMul n A_inv A d r
    _ = matMulVec n A_inv rhs r := by rw [hd]

/-- **Problem 9.10**, multiplying by a vector supported at one standard-basis
coordinate. -/
theorem higham_problem9_10_matMulVec_scaledBasis {n : ℕ}
    (A_inv : Fin n → Fin n → ℝ) (i : Fin n) (alpha xj : ℝ) :
    matMulVec n A_inv (fun r => alpha * finiteBasisVec i r * xj) =
      fun r => alpha * A_inv r i * xj := by
  ext r
  unfold matMulVec
  rw [Finset.sum_eq_single i]
  · simp [finiteBasisVec]
    ring
  · intro c _ hc
    simp [finiteBasisVec, hc]
  · simp

/-- **Problem 9.10**, source rank-one blunder solution formula.  If the exact
solution satisfies `A x = b` and the computed solution satisfies
`(A - α e_i e_j^T) xhat = b`, then `xhat` is the Sherman-Morrison update
obtained by direct left-inverse algebra. -/
theorem higham_problem9_10_rankOne_blunder_solution {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (b x xhat : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hx : matMulVec n A x = b)
    (hxhat :
      matMulVec n
          (fun r c => A r c - alpha * higham_problem9_10_rankOneBasis i j r c)
          xhat = b)
    (hden : 1 - alpha * A_inv j i ≠ 0) :
    xhat =
      fun r => x r + (alpha * x j / (1 - alpha * A_inv j i)) * A_inv r i := by
  have hxhat_exp := hxhat
  rw [higham_problem9_10_rankOnePerturbed_mulVec] at hxhat_exp
  have hdA :
      matMulVec n A (fun q => xhat q - x q) =
        fun r => alpha * finiteBasisVec i r * xhat j := by
    ext r
    have hxhat_r := congrFun hxhat_exp r
    have hx_r := congrFun hx r
    unfold matMulVec at hxhat_r hx_r ⊢
    calc
      ∑ c : Fin n, A r c * (xhat c - x c)
          = (∑ c : Fin n, A r c * xhat c) -
              (∑ c : Fin n, A r c * x c) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro c _
              ring
      _ = alpha * finiteBasisVec i r * xhat j := by
              nlinarith
  have hd_eq :
      (fun q => xhat q - x q) =
        matMulVec n A_inv (fun r => alpha * finiteBasisVec i r * xhat j) :=
    higham_problem9_10_apply_left_inverse_of_matMulVec_eq A A_inv
      (fun q => xhat q - x q)
      (fun r => alpha * finiteBasisVec i r * xhat j) hInv hdA
  have hscaled := higham_problem9_10_matMulVec_scaledBasis A_inv i alpha (xhat j)
  have hd_entry : ∀ r : Fin n, xhat r - x r = alpha * A_inv r i * xhat j := by
    intro r
    have hr := congrFun hd_eq r
    rw [hscaled] at hr
    exact hr
  have hsolve : xhat j = x j / (1 - alpha * A_inv j i) := by
    have hj := hd_entry j
    field_simp [hden]
    nlinarith
  ext r
  have hr := hd_entry r
  calc
    xhat r = x r + alpha * A_inv r i * xhat j := by
      nlinarith
    _ = x r + alpha * A_inv r i * (x j / (1 - alpha * A_inv j i)) := by
      rw [hsolve]
    _ = x r + (alpha * x j / (1 - alpha * A_inv j i)) * A_inv r i := by
      field_simp [hden]

/-- **Problem 9.10**, source error formula for a rank-one multiplier blunder:
`x - xhat = -α x_j /(1 - α A^{-1}_{j i}) A^{-1}(:,i)`. -/
theorem higham_problem9_10_rankOne_blunder_error {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (b x xhat : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hx : matMulVec n A x = b)
    (hxhat :
      matMulVec n
          (fun r c => A r c - alpha * higham_problem9_10_rankOneBasis i j r c)
          xhat = b)
    (hden : 1 - alpha * A_inv j i ≠ 0)
    (r : Fin n) :
    x r - xhat r =
      - (alpha * x j / (1 - alpha * A_inv j i)) * A_inv r i := by
  have hsol :=
    higham_problem9_10_rankOne_blunder_solution A A_inv i j alpha b x xhat
      hInv hx hxhat hden
  have hr := congrFun hsol r
  rw [hr]
  ring

/-- **Problem 9.10**, source-facing multiplier-error formula with
`α = ε * \hat l_ij * \hat u_jj`. -/
theorem higham_problem9_10_multiplier_blunder_error {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n)
    (epsilon lhatij uhatjj : ℝ) (b x xhat : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hx : matMulVec n A x = b)
    (hxhat :
      matMulVec n
          (fun r c =>
            A r c -
              higham_problem9_10_multiplierBlunderAlpha epsilon lhatij uhatjj *
                higham_problem9_10_rankOneBasis i j r c)
          xhat = b)
    (hden :
      1 - higham_problem9_10_multiplierBlunderAlpha epsilon lhatij uhatjj *
            A_inv j i ≠ 0)
    (r : Fin n) :
    x r - xhat r =
      - (epsilon * lhatij * uhatjj * x j /
          (1 - epsilon * lhatij * uhatjj * A_inv j i)) * A_inv r i := by
  have h :=
    higham_problem9_10_rankOne_blunder_error A A_inv i j
      (higham_problem9_10_multiplierBlunderAlpha epsilon lhatij uhatjj)
      b x xhat hInv hx hxhat hden r
  simpa [higham_problem9_10_multiplierBlunderAlpha, mul_assoc] using h

/-! ## §9.5 Diagonally Dominant and Banded Matrices -/

/-- **Theorem 9.9**, column/row diagonal-dominance bound packaged as a
componentwise solve error once the `ρ ≤ 2` growth hypothesis is available. -/
theorem higham9_9_diagDom_lu_solve_backward_stable_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 2 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  diagDom_lu_solve_backward_stable_tight fp n A L_hat U_hat b
    hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Equation (9.17)** / corrected Lemma-8.8 route, exposed as a reusable
source-facing predicate for Chapter 9 wrappers. -/
def higham9_17_rowDiagDom_absLU_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) : Prop :=
  infNorm (matMul n (absMatrix n L_hat) (absMatrix n U_hat)) ≤
    (2 * (n : ℝ) - 1) * infNorm A

/-- **Equation (9.17)**, exact-LU algebraic bridge to the Skeel condition of
the final upper factor.

If `A = L U` and `U_inv` is an exact inverse of `U`, then
`‖|L||U|‖∞ ≤ condSkeel(U) ‖A‖∞`.  This is the local Chapter 9 algebra behind
the source step `|L||U| = |A U⁻¹| |U| ≤ |A||U⁻¹||U|`. -/
theorem higham9_17_absLU_infNorm_le_condSkeel_of_LUFactSpec {n : ℕ}
    (hn : 0 < n)
    (A L U U_inv : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hUInv : IsInverse n U U_inv) :
    infNorm (matMul n (absMatrix n L) (absMatrix n U)) ≤
      condSkeel n hn U U_inv * infNorm A := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  let κrow : Fin n → ℝ :=
    fun s => ∑ k : Fin n, |U_inv s k| * (∑ j : Fin n, |U k j|)
  have hprod : matMul n L U = A := by
    ext i j
    exact hLU.product_eq i j
  have hUright : matMul n U U_inv = idMatrix n := by
    ext i j
    exact hUInv.2 i j
  have hAUinv : matMul n A U_inv = L := by
    calc
      matMul n A U_inv = matMul n (matMul n L U) U_inv := by rw [hprod]
      _ = matMul n L (matMul n U U_inv) := matMul_assoc n L U U_inv
      _ = matMul n L (idMatrix n) := by rw [hUright]
      _ = L := matMul_id_right n L
  have hL_entry : ∀ i k : Fin n, L i k = ∑ s : Fin n, A i s * U_inv s k := by
    intro i k
    simpa [matMul] using (congrFun (congrFun hAUinv i) k).symm
  have hκrow_le : ∀ s : Fin n, κrow s ≤ condSkeel n hn U U_inv := by
    intro s
    unfold κrow condSkeel
    exact Finset.le_sup'
      (fun i => ∑ k : Fin n, |U_inv i k| * (∑ j : Fin n, |U k j|))
      (Finset.mem_univ s)
  have hcond_nonneg : 0 ≤ condSkeel n hn U U_inv := by
    let i0 : Fin n := ⟨0, hn⟩
    have hrow0_nonneg :
        0 ≤ ∑ k : Fin n, |U_inv i0 k| * (∑ j : Fin n, |U k j|) := by
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun j _ => abs_nonneg _))
    exact le_trans hrow0_nonneg (hκrow_le i0)
  have hW_nonneg : ∀ i j : Fin n, 0 ≤ W i j := by
    intro i j
    unfold W matMul absMatrix
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |W i j| = ∑ j : Fin n, W i j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_of_nonneg (hW_nonneg i j)]
      _ = ∑ j : Fin n, ∑ k : Fin n, |L i k| * |U k j| := by
        simp [W, matMul, absMatrix]
      _ ≤ ∑ j : Fin n, ∑ k : Fin n,
            (∑ s : Fin n, |A i s| * |U_inv s k|) * |U k j| := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro k _
          have hLik :
              |L i k| ≤ ∑ s : Fin n, |A i s| * |U_inv s k| := by
            rw [hL_entry i k]
            calc
              |∑ s : Fin n, A i s * U_inv s k|
                  ≤ ∑ s : Fin n, |A i s * U_inv s k| :=
                    Finset.abs_sum_le_sum_abs _ _
              _ = ∑ s : Fin n, |A i s| * |U_inv s k| := by
                    apply Finset.sum_congr rfl
                    intro s _
                    rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hLik (abs_nonneg _)
      _ = ∑ k : Fin n,
            (∑ s : Fin n, |A i s| * |U_inv s k|) * (∑ j : Fin n, |U k j|) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          rw [← Finset.mul_sum]
      _ = ∑ k : Fin n, ∑ s : Fin n,
            (|A i s| * |U_inv s k|) * (∑ j : Fin n, |U k j|) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
      _ = ∑ s : Fin n, ∑ k : Fin n,
            |A i s| * (|U_inv s k| * (∑ j : Fin n, |U k j|)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = ∑ s : Fin n, |A i s| * κrow s := by
          unfold κrow
          apply Finset.sum_congr rfl
          intro s _
          rw [← Finset.mul_sum]
      _ ≤ ∑ s : Fin n, |A i s| * condSkeel n hn U U_inv := by
          apply Finset.sum_le_sum
          intro s _
          exact mul_le_mul_of_nonneg_left (hκrow_le s) (abs_nonneg _)
      _ = (∑ s : Fin n, |A i s|) * condSkeel n hn U U_inv := by
          rw [Finset.sum_mul]
      _ ≤ infNorm A * condSkeel n hn U U_inv := by
          exact mul_le_mul_of_nonneg_right (row_sum_le_infNorm A i) hcond_nonneg
      _ = condSkeel n hn U U_inv * infNorm A := by ring
  · exact mul_nonneg hcond_nonneg (infNorm_nonneg A)

/-- **Equation (9.17)**, source-facing norm bound from the corrected
Chapter-8 Lemma-8.8 hypothesis on the final upper factor.

If `A = L U` and the exact upper factor `U` satisfies the corrected strict-upper
row-sum dominance condition from Lemma 8.8, then
`‖|L||U|‖∞ ≤ (2n - 1) ‖A‖∞`. -/
theorem higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec {n : ℕ}
    (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hURow : higham8_8_rowDiagDominantUpper n U) :
    higham9_17_rowDiagDom_absLU_bound n A L U := by
  have hURow' := hURow
  rcases hURow with ⟨hUT, hUdiag, _⟩
  have hdetU :
      Matrix.det (U : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
    det_ne_zero_of_upper_triangular_diag_ne_zero n U hUT hUdiag
  let U_inv : Fin n → Fin n → ℝ := nonsingInv n U
  have hUInv : IsInverse n U U_inv :=
    isInverse_nonsingInv_of_det_ne_zero n U hdetU
  calc
    infNorm (matMul n (absMatrix n L) (absMatrix n U))
        ≤ condSkeel n hn U U_inv * infNorm A :=
      higham9_17_absLU_infNorm_le_condSkeel_of_LUFactSpec
        hn A L U U_inv hLU hUInv
    _ ≤ (2 * (n : ℝ) - 1) * infNorm A := by
      exact mul_le_mul_of_nonneg_right
        (higham8_8_rowDiagDominantUpper_condSkeel_bound n hn U U_inv hURow' hUInv)
        (infNorm_nonneg A)

/-- **Theorem 9.9**, source side condition: for a row diagonally dominant
matrix, a zero diagonal entry forces the whole row to be zero. -/
theorem higham9_9_rowDiagDominant_zero_diag_row_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsRowDiagDominant n A)
    {i : Fin n} (hdiag : A i i = 0) :
  ∀ j : Fin n, A i j = 0 := by
  have hsum_le_zero :
      (∑ j : Fin n, (if i = j then 0 else |A i j|)) ≤ 0 := by
    simpa [hdiag] using hDD i
  have hterm_nonneg :
      ∀ j ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (if i = j then 0 else |A i j|) := by
    intro j _
    by_cases hij : i = j <;> simp [hij, abs_nonneg]
  have hsum_eq_zero :
      (∑ j : Fin n, (if i = j then 0 else |A i j|)) = 0 := by
    exact le_antisymm hsum_le_zero (Finset.sum_nonneg hterm_nonneg)
  have hterms :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum_eq_zero
  intro j
  by_cases hij : i = j
  · simpa [hij] using hdiag
  · have hterm : (if i = j then 0 else |A i j|) = 0 :=
      hterms j (Finset.mem_univ j)
    exact abs_eq_zero.mp (by simpa [hij] using hterm)

/-- **Theorem 9.9**, source side condition: for a column diagonally dominant
matrix, a zero diagonal entry forces the whole column to be zero. -/
theorem higham9_9_colDiagDominant_zero_diag_col_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsDiagDominant n A)
    {j : Fin n} (hdiag : A j j = 0) :
    ∀ i : Fin n, A i j = 0 := by
  have hsum_le_zero :
      (∑ i : Fin n, (if i = j then 0 else |A i j|)) ≤ 0 := by
    simpa [hdiag] using hDD j
  have hterm_nonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (if i = j then 0 else |A i j|) := by
    intro i _
    by_cases hij : i = j <;> simp [hij, abs_nonneg]
  have hsum_eq_zero :
      (∑ i : Fin n, (if i = j then 0 else |A i j|)) = 0 := by
    exact le_antisymm hsum_le_zero (Finset.sum_nonneg hterm_nonneg)
  have hterms :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum_eq_zero
  intro i
  by_cases hij : i = j
  · simpa [hij] using hdiag
  · have hterm : (if i = j then 0 else |A i j|) = 0 :=
      hterms i (Finset.mem_univ i)
    exact abs_eq_zero.mp (by simpa [hij] using hterm)

/-- **Theorem 9.9**, source side condition: a nonsingular row diagonally
dominant matrix has nonzero diagonal entries. -/
theorem higham9_9_rowDiagDominant_diag_ne_zero_of_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hDD : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∀ i : Fin n, A i i ≠ 0 := by
  intro i hdiag
  have hrow := higham9_9_rowDiagDominant_zero_diag_row_zero hDD hdiag
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i
    (fun j => by simpa [Matrix.of_apply] using hrow j))

/-- **Theorem 9.9**, source side condition: a nonsingular column diagonally
dominant matrix has nonzero diagonal entries. -/
theorem higham9_9_colDiagDominant_diag_ne_zero_of_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hDD : IsDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∀ i : Fin n, A i i ≠ 0 := by
  intro i hdiag
  have hcol := higham9_9_colDiagDominant_zero_diag_col_zero hDD hdiag
  exact hdet (Matrix.det_eq_zero_of_column_eq_zero i
    (fun j => by simpa [Matrix.of_apply] using hcol j))

/-- **Theorem 9.9**, row diagonal dominance bounds each off-diagonal row
entry by the corresponding diagonal entry. -/
theorem higham9_9_rowDiagDominant_offdiag_abs_le_diag {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsRowDiagDominant n A)
    {i j : Fin n} (hij : j ≠ i) :
    |A i j| ≤ |A i i| := by
  have hterm :
      |A i j| ≤ ∑ k : Fin n, (if i = k then 0 else |A i k|) := by
    have hj :
        (fun k : Fin n => if i = k then (0 : ℝ) else |A i k|) j =
          |A i j| := by
      simp [Ne.symm hij]
    rw [← hj]
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun k : Fin n => if i = k then (0 : ℝ) else |A i k|)
      (by intro k _; by_cases hik : i = k <;> simp [hik, abs_nonneg])
      (Finset.mem_univ j)
  exact le_trans hterm (hDD i)

/-- **Theorem 9.9**, column diagonal dominance bounds each off-diagonal
column entry by the corresponding diagonal entry. -/
theorem higham9_9_colDiagDominant_offdiag_abs_le_diag {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsDiagDominant n A)
    {i j : Fin n} (hij : i ≠ j) :
    |A i j| ≤ |A j j| := by
  have hterm :
      |A i j| ≤ ∑ k : Fin n, (if k = j then 0 else |A k j|) := by
    have hi :
        (fun k : Fin n => if k = j then (0 : ℝ) else |A k j|) i =
          |A i j| := by
      simp [hij]
    rw [← hi]
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun k : Fin n => if k = j then (0 : ℝ) else |A k j|)
      (by intro k _; by_cases hkj : k = j <;> simp [hkj, abs_nonneg])
      (Finset.mem_univ i)
  exact le_trans hterm (hDD j)

/-- **Theorem 9.9**, row diagonal dominance gives a unit bound for the
off-diagonal row ratio `aᵢⱼ / aᵢᵢ` when the diagonal entry is nonzero. -/
theorem higham9_9_rowDiagDominant_entry_ratio_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsRowDiagDominant n A)
    {i j : Fin n} (hij : j ≠ i) (hdiag : A i i ≠ 0) :
    |A i j / A i i| ≤ 1 := by
  have hle : |A i j| ≤ |A i i| :=
    higham9_9_rowDiagDominant_offdiag_abs_le_diag hDD hij
  have hden_pos : 0 < |A i i| := abs_pos.mpr hdiag
  calc
    |A i j / A i i| = |A i j| / |A i i| := by rw [abs_div]
    _ ≤ |A i i| / |A i i| :=
        div_le_div_of_nonneg_right hle (abs_nonneg _)
    _ = 1 := div_self (ne_of_gt hden_pos)

/-- **Theorem 9.9**, column diagonal dominance gives the source first-step
unit multiplier bound `|aᵢⱼ / aⱼⱼ| <= 1` when the diagonal entry is nonzero. -/
theorem higham9_9_colDiagDominant_entry_ratio_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hDD : IsDiagDominant n A)
    {i j : Fin n} (hij : i ≠ j) (hdiag : A j j ≠ 0) :
    |A i j / A j j| ≤ 1 := by
  have hle : |A i j| ≤ |A j j| :=
    higham9_9_colDiagDominant_offdiag_abs_le_diag hDD hij
  have hden_pos : 0 < |A j j| := abs_pos.mpr hdiag
  calc
    |A i j / A j j| = |A i j| / |A j j| := by rw [abs_div]
    _ ≤ |A j j| / |A j j| :=
        div_le_div_of_nonneg_right hle (abs_nonneg _)
    _ = 1 := div_self (ne_of_gt hden_pos)

/-- **Theorem 9.9**, nonsingular row diagonal dominance gives the row-ratio
unit bound without a separate diagonal-nonzero hypothesis. -/
theorem higham9_9_rowDiagDominant_entry_ratio_abs_le_one_of_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hDD : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    {i j : Fin n} (hij : j ≠ i) :
    |A i j / A i i| ≤ 1 :=
  higham9_9_rowDiagDominant_entry_ratio_abs_le_one hDD hij
    ((higham9_9_rowDiagDominant_diag_ne_zero_of_det_ne_zero hDD hdet) i)

/-- **Theorem 9.9**, nonsingular column diagonal dominance gives the
source first-step unit multiplier bound without a separate diagonal-nonzero
hypothesis. -/
theorem higham9_9_colDiagDominant_entry_ratio_abs_le_one_of_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hDD : IsDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    {i j : Fin n} (hij : i ≠ j) :
    |A i j / A j j| ≤ 1 :=
  higham9_9_colDiagDominant_entry_ratio_abs_le_one hDD hij
    ((higham9_9_colDiagDominant_diag_ne_zero_of_det_ne_zero hDD hdet) j)

/-- **Theorem 9.9**, column diagonal dominance bounds the sum of the first
column no-pivot multipliers by one.  This is the finite-sum form of the
source statement that column diagonal dominance gives `|lᵢ₁| <= 1` at the
first elimination step. -/
theorem higham9_9_colDiagDominant_first_column_multiplier_sum_le_one {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0) :
    (∑ i : Fin m, |A i.succ 0 / A 0 0|) ≤ 1 := by
  have hden_pos : 0 < |A 0 0| := abs_pos.mpr hdiag
  have hcol0 : (∑ i : Fin m, |A i.succ 0|) ≤ |A 0 0| := by
    have h := hDD (0 : Fin (m + 1))
    rw [Fin.sum_univ_succ] at h
    simpa using h
  have hsum_div :
      (∑ i : Fin m, |A i.succ 0 / A 0 0|) =
        (∑ i : Fin m, |A i.succ 0|) / |A 0 0| := by
    calc
      (∑ i : Fin m, |A i.succ 0 / A 0 0|)
          = ∑ i : Fin m, |A i.succ 0| / |A 0 0| := by
              apply Finset.sum_congr rfl
              intro i _
              rw [abs_div]
      _ = (∑ i : Fin m, |A i.succ 0|) / |A 0 0| := by
              rw [Finset.sum_div]
  calc
    (∑ i : Fin m, |A i.succ 0 / A 0 0|)
        = (∑ i : Fin m, |A i.succ 0|) / |A 0 0| := hsum_div
    _ ≤ |A 0 0| / |A 0 0| :=
        div_le_div_of_nonneg_right hcol0 (abs_nonneg _)
    _ = 1 := div_self (ne_of_gt hden_pos)

/-- **Theorem 9.9**, column diagonal dominance bounds the first-column
multiplier sum with one selected trailing row removed.  This is the sharp
finite-sum form consumed by the first Schur-complement diagonal-dominance
proof. -/
theorem higham9_9_colDiagDominant_first_column_multiplier_sum_except_le
    {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0) (j : Fin m) :
    (∑ i : Fin m, (if i = j then 0 else |A i.succ 0 / A 0 0|)) ≤
      1 - |A j.succ 0 / A 0 0| := by
  classical
  let f : Fin m → ℝ := fun i => |A i.succ 0 / A 0 0|
  have htotal : (∑ i : Fin m, f i) ≤ 1 := by
    simpa [f] using
      higham9_9_colDiagDominant_first_column_multiplier_sum_le_one hDD hdiag
  have hsplit :
      (∑ i : Fin m, f i) =
        f j + ∑ i : Fin m, (if i = j then 0 else f i) := by
    calc
      (∑ i : Fin m, f i)
          = ∑ i : Fin m,
              ((if i = j then f i else 0) + (if i = j then 0 else f i)) := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hij : i = j <;> simp [hij]
      _ = (∑ i : Fin m, if i = j then f i else 0) +
            ∑ i : Fin m, (if i = j then 0 else f i) := by
              rw [Finset.sum_add_distrib]
      _ = f j + ∑ i : Fin m, (if i = j then 0 else f i) := by
              congr 1
              rw [Finset.sum_eq_single j]
              · simp
              · intro i _ hij
                simp [hij]
              · intro hj
                exact (hj (Finset.mem_univ j)).elim
  have hbound : f j + ∑ i : Fin m, (if i = j then 0 else f i) ≤ 1 := by
    simpa [hsplit] using htotal
  have hrest : ∑ i : Fin m, (if i = j then 0 else f i) ≤ 1 - f j := by
    linarith
  simpa [f] using hrest

/-- **Theorem 9.9**, column diagonal dominance is preserved by the first
no-pivot Schur-complement step.  This is the local Split-2 Schur-complement
dependency behind the column-dominant half of Wilkinson's diagonal-dominance
growth theorem; it does not invoke the row-dominant Lemma 8.8 route. -/
theorem higham9_9_colDiagDominant_firstSchurComplement {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0) :
    IsDiagDominant m (higham9_1_firstSchurComplement A) := by
  classical
  intro j
  let S : Fin m → Fin m → ℝ := higham9_1_firstSchurComplement A
  let aoff : ℝ := ∑ i : Fin m, if i = j then 0 else |A i.succ j.succ|
  let rsum : ℝ := ∑ i : Fin m, if i = j then 0 else |A i.succ 0 / A 0 0|
  let rj : ℝ := |A j.succ 0 / A 0 0|
  let a0j : ℝ := |A 0 j.succ|
  have hcolj : a0j + aoff ≤ |A j.succ j.succ| := by
    have h := hDD j.succ
    rw [Fin.sum_univ_succ] at h
    simpa [aoff, a0j, Fin.succ_inj] using h
  have hratio : rsum ≤ 1 - rj := by
    simpa [rsum, rj] using
      higham9_9_colDiagDominant_first_column_multiplier_sum_except_le hDD hdiag j
  have hsum_le :
      (∑ i : Fin m, (if i = j then 0 else |S i j|)) ≤
        aoff + rsum * a0j := by
    calc
      (∑ i : Fin m, (if i = j then 0 else |S i j|))
          ≤ ∑ i : Fin m,
              ((if i = j then 0 else |A i.succ j.succ|) +
                (if i = j then 0 else |A i.succ 0 / A 0 0| * a0j)) := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hij : i = j
              · simp [hij]
              · simp only [hij, if_false]
                have htri :
                    |S i j| ≤
                      |A i.succ j.succ| + |A i.succ 0 / A 0 0| * a0j := by
                  have habs :
                      |A i.succ 0 * A 0 j.succ / A 0 0| =
                        |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
                    have hden_abs : |A 0 0| ≠ 0 := abs_ne_zero.mpr hdiag
                    calc
                      |A i.succ 0 * A 0 j.succ / A 0 0|
                          = |A i.succ 0| * |A 0 j.succ| / |A 0 0| := by
                              rw [abs_div, abs_mul]
                      _ = (|A i.succ 0| / |A 0 0|) * |A 0 j.succ| := by
                              field_simp [hden_abs]
                      _ = |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
                              rw [abs_div]
                  calc
                    |S i j|
                        = |A i.succ j.succ -
                            A i.succ 0 * A 0 j.succ / A 0 0| := by
                            simp [S, higham9_1_firstSchurComplement,
                              luFirstSchurComplement]
                    _ ≤ |A i.succ j.succ| +
                          |A i.succ 0 * A 0 j.succ / A 0 0| :=
                        by
                          simpa [abs_neg] using
                            (abs_sub_le (A i.succ j.succ) 0
                              (A i.succ 0 * A 0 j.succ / A 0 0))
                    _ = |A i.succ j.succ| +
                          |A i.succ 0 / A 0 0| * a0j := by
                        rw [habs]
                exact htri
      _ = aoff + rsum * a0j := by
              simp [aoff, rsum, Finset.sum_add_distrib, Finset.sum_mul]
  have hratio_mul : rsum * a0j ≤ (1 - rj) * a0j :=
    mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
  have hsource_to_diag :
      aoff + (1 - rj) * a0j ≤ |A j.succ j.succ| - rj * a0j := by
    nlinarith [hcolj]
  have hdiag_lower :
      |A j.succ j.succ| - rj * a0j ≤ |S j j| := by
    have hb_abs :
        |A j.succ 0 * A 0 j.succ / A 0 0| =
          rj * a0j := by
      have hden_abs : |A 0 0| ≠ 0 := abs_ne_zero.mpr hdiag
      calc
        |A j.succ 0 * A 0 j.succ / A 0 0|
            = |A j.succ 0| * |A 0 j.succ| / |A 0 0| := by
                rw [abs_div, abs_mul]
        _ = (|A j.succ 0| / |A 0 0|) * |A 0 j.succ| := by
                field_simp [hden_abs]
        _ = |A j.succ 0 / A 0 0| * |A 0 j.succ| := by
                rw [abs_div]
        _ = rj * a0j := rfl
    have hrev :
        |A j.succ j.succ| - |A j.succ 0 * A 0 j.succ / A 0 0| ≤
          |A j.succ j.succ - A j.succ 0 * A 0 j.succ / A 0 0| := by
      exact abs_sub_abs_le_abs_sub (A j.succ j.succ)
        (A j.succ 0 * A 0 j.succ / A 0 0)
    calc
      |A j.succ j.succ| - rj * a0j
          = |A j.succ j.succ| -
              |A j.succ 0 * A 0 j.succ / A 0 0| := by rw [hb_abs]
      _ ≤ |A j.succ j.succ - A j.succ 0 * A 0 j.succ / A 0 0| := hrev
      _ = |S j j| := by
          simp [S, higham9_1_firstSchurComplement, luFirstSchurComplement]
  calc
    (∑ i : Fin m, (if i = j then 0 else |higham9_1_firstSchurComplement A i j|))
        = ∑ i : Fin m, (if i = j then 0 else |S i j|) := rfl
    _ ≤ aoff + rsum * a0j := hsum_le
    _ ≤ aoff + (1 - rj) * a0j := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hratio_mul aoff
    _ ≤ |A j.succ j.succ| - rj * a0j := hsource_to_diag
    _ ≤ |S j j| := hdiag_lower
    _ = |higham9_1_firstSchurComplement A j j| := rfl

/-- **Theorem 9.9**, first-step max-entry growth for the column-dominant
no-pivot route.  The first Schur complement has every entry bounded by twice
the max-entry norm of the source matrix.  This is a local dependency for the
remaining direct `rho_n <= 2` growth proof; it does not use the row-dominant
equation (9.17) route. -/
theorem higham9_9_colDiagDominant_firstSchurComplement_maxEntryNorm_le_two {m : ℕ}
    (hm : 0 < m)
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0) :
    maxEntryNorm hm (higham9_1_firstSchurComplement A) ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  classical
  let M : ℝ := maxEntryNorm (Nat.succ_pos m) A
  let hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  change Finset.sup' Finset.univ hne
      (fun i => Finset.sup' Finset.univ hne
        (fun j => |higham9_1_firstSchurComplement A i j|)) ≤ 2 * M
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  have hratio : |A i.succ 0 / A 0 0| ≤ 1 :=
    higham9_9_colDiagDominant_entry_ratio_abs_le_one hDD
      (Fin.succ_ne_zero i) hdiag
  have hsource : |A i.succ j.succ| ≤ M := by
    simpa [M] using entry_le_maxEntryNorm (Nat.succ_pos m) A i.succ j.succ
  have hpivotRow : |A 0 j.succ| ≤ M := by
    simpa [M] using entry_le_maxEntryNorm (Nat.succ_pos m) A 0 j.succ
  have hprod :
      |A i.succ 0 / A 0 0| * |A 0 j.succ| ≤ 1 * M :=
    mul_le_mul hratio hpivotRow (abs_nonneg _) (by norm_num)
  have hfactor :
      |A i.succ 0 * A 0 j.succ / A 0 0| =
        |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
    have hden_abs : |A 0 0| ≠ 0 := abs_ne_zero.mpr hdiag
    calc
      |A i.succ 0 * A 0 j.succ / A 0 0|
          = |A i.succ 0| * |A 0 j.succ| / |A 0 0| := by
              rw [abs_div, abs_mul]
      _ = (|A i.succ 0| / |A 0 0|) * |A 0 j.succ| := by
              field_simp [hden_abs]
      _ = |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
              rw [abs_div]
  calc
    |higham9_1_firstSchurComplement A i j|
        = |A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0| := by
            simp [higham9_1_firstSchurComplement, luFirstSchurComplement]
    _ ≤ |A i.succ j.succ| + |A i.succ 0 * A 0 j.succ / A 0 0| := by
            simpa [abs_neg] using
              (abs_sub_le (A i.succ j.succ) 0
                (A i.succ 0 * A 0 j.succ / A 0 0))
    _ = |A i.succ j.succ| +
          |A i.succ 0 / A 0 0| * |A 0 j.succ| := by rw [hfactor]
    _ ≤ M + 1 * M := add_le_add hsource hprod
    _ = 2 * M := by ring

/-- **Theorem 9.9**, max-entry growth-factor endpoint from the remaining
final-upper entry bound.  This adapter isolates the last scalar step in the
diagonal-dominance proof: once the local GE trace supplies
`|U_ij| <= 2 * maxEntryNorm A` for the final upper factor, Higham's
`rho_n <= 2` conclusion follows. -/
theorem higham9_9_growthFactorEntry_le_two_of_upper_entry_bound {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hU : ∀ i j : Fin n, |U i j| ≤ 2 * maxEntryNorm hn A) :
    growthFactorEntry hn A U hA ≤ 2 :=
  growthFactorEntry_le_of_entry_bound_factor hn A U 2 hA hU

/-- **Theorem 9.9**, sharper first-step off-diagonal growth for the
column-dominant no-pivot route.  In the first Schur complement, off-diagonal
trailing entries are bounded by the original max-entry norm; only the diagonal
entries need the coarser `2 * maxEntryNorm A` bound. -/
theorem higham9_9_colDiagDominant_firstSchurComplement_offdiag_le_maxEntryNorm
    {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsDiagDominant (m + 1) A)
    (hdiag : A 0 0 ≠ 0)
    {i j : Fin m} (hij : i ≠ j) :
    |higham9_1_firstSchurComplement A i j| ≤
      maxEntryNorm (Nat.succ_pos m) A := by
  classical
  let M : ℝ := maxEntryNorm (Nat.succ_pos m) A
  let off : ℝ := ∑ r : Fin m, if r = j then 0 else |A r.succ j.succ|
  have hcolj : |A 0 j.succ| + off ≤ |A j.succ j.succ| := by
    have h := hDD j.succ
    rw [Fin.sum_univ_succ] at h
    simpa [off, Fin.succ_inj] using h
  have hentry_off_le : |A i.succ j.succ| ≤ off := by
    have hnonneg :
        ∀ r ∈ (Finset.univ : Finset (Fin m)),
          0 ≤ (if r = j then 0 else |A r.succ j.succ|) := by
      intro r _
      by_cases hrj : r = j <;> simp [hrj]
    have hsingle :=
      Finset.single_le_sum hnonneg (Finset.mem_univ i)
    simpa [off, hij] using hsingle
  have hpair_le_diag : |A i.succ j.succ| + |A 0 j.succ| ≤ |A j.succ j.succ| := by
    calc
      |A i.succ j.succ| + |A 0 j.succ|
          = |A 0 j.succ| + |A i.succ j.succ| := by ring
      _ ≤ |A 0 j.succ| + off := by linarith
      _ ≤ |A j.succ j.succ| := hcolj
  have hdiag_le_M : |A j.succ j.succ| ≤ M := by
    simpa [M] using entry_le_maxEntryNorm (Nat.succ_pos m) A j.succ j.succ
  have hpair_le_M : |A i.succ j.succ| + |A 0 j.succ| ≤ M :=
    le_trans hpair_le_diag hdiag_le_M
  have hratio : |A i.succ 0 / A 0 0| ≤ 1 :=
    higham9_9_colDiagDominant_entry_ratio_abs_le_one hDD
      (Fin.succ_ne_zero i) hdiag
  have hprod :
      |A i.succ 0 / A 0 0| * |A 0 j.succ| ≤ |A 0 j.succ| := by
    have hmul :
        |A i.succ 0 / A 0 0| * |A 0 j.succ| ≤
          1 * |A 0 j.succ| :=
      mul_le_mul hratio (le_refl _) (abs_nonneg _) (by norm_num)
    simpa using hmul
  have hfactor :
      |A i.succ 0 * A 0 j.succ / A 0 0| =
        |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
    have hden_abs : |A 0 0| ≠ 0 := abs_ne_zero.mpr hdiag
    calc
      |A i.succ 0 * A 0 j.succ / A 0 0|
          = |A i.succ 0| * |A 0 j.succ| / |A 0 0| := by
              rw [abs_div, abs_mul]
      _ = (|A i.succ 0| / |A 0 0|) * |A 0 j.succ| := by
              field_simp [hden_abs]
      _ = |A i.succ 0 / A 0 0| * |A 0 j.succ| := by
              rw [abs_div]
  calc
    |higham9_1_firstSchurComplement A i j|
        = |A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0| := by
            simp [higham9_1_firstSchurComplement, luFirstSchurComplement]
    _ ≤ |A i.succ j.succ| + |A i.succ 0 * A 0 j.succ / A 0 0| := by
            simpa [abs_neg] using
              (abs_sub_le (A i.succ j.succ) 0
                (A i.succ 0 * A 0 j.succ / A 0 0))
    _ = |A i.succ j.succ| +
          |A i.succ 0 / A 0 0| * |A 0 j.succ| := by rw [hfactor]
    _ ≤ |A i.succ j.succ| + |A 0 j.succ| := by linarith
    _ ≤ M := hpair_le_M

/-- **Theorem 9.9**, real transpose convention: column diagonal dominance of
`Aᵀ` is exactly row diagonal dominance of `A`.  This is the real-matrix analogue
of the source statement that column dominance can be expressed through `A*`. -/
theorem higham9_9_colDiagDominant_transpose_iff_rowDiagDominant {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    IsDiagDominant n (matTranspose A) ↔ IsRowDiagDominant n A := by
  constructor
  · intro h i
    simpa [IsDiagDominant, IsRowDiagDominant, matTranspose, eq_comm] using h i
  · intro h i
    simpa [IsDiagDominant, IsRowDiagDominant, matTranspose, eq_comm] using h i

/-- **Theorem 9.9**, real transpose convention: row diagonal dominance of
`Aᵀ` is exactly column diagonal dominance of `A`. -/
theorem higham9_9_rowDiagDominant_transpose_iff_colDiagDominant {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    IsRowDiagDominant n (matTranspose A) ↔ IsDiagDominant n A := by
  constructor
  · intro h i
    simpa [IsDiagDominant, IsRowDiagDominant, matTranspose, eq_comm] using h i
  · intro h i
    simpa [IsDiagDominant, IsRowDiagDominant, matTranspose, eq_comm] using h i

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, first pivot row.
In the first column of an upper-Hessenberg matrix, any nonzero entry lies in
row `0` or row `1`.  Thus a nonzero partial-pivoting first pivot can only be
the current row or the next row, matching the source's adjacent-swap argument. -/
theorem higham9_10_hessenberg_firstColumn_nonzero_row_le_one {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ} {r : Fin (m + 1)}
    (hH : IsUpperHessenberg (m + 1) A) (hpivot : A r 0 ≠ 0) :
    r.val ≤ 1 := by
  by_contra hle
  have hbelow : (0 : Fin (m + 1)).val + 1 < r.val := by
    simpa using (Nat.lt_of_not_ge hle)
  exact hpivot (hH r 0 hbelow)

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, a nonsingular
active matrix has a nonzero entry in its first active column. -/
theorem higham9_10_exists_first_active_column_nonzero_of_det_ne_zero {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∃ r : Fin (m + 1), A r 0 ≠ 0 := by
  classical
  by_contra hnone
  apply hdet
  apply Matrix.det_eq_zero_of_column_eq_zero
  intro i
  by_contra hne
  exact hnone ⟨i, by simpa [Matrix.of_apply] using hne⟩

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, a nonsingular
active matrix admits a first partial-pivoting choice with nonzero pivot. -/
theorem higham9_10_exists_first_partialPivotChoice_pivot_ne_zero_of_det_ne_zero
    {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∃ r : Fin (m + 1),
      higham9_1_partialPivotChoice A 0 r ∧ A r 0 ≠ 0 := by
  obtain ⟨r₀, hr₀⟩ :=
    higham9_10_exists_first_active_column_nonzero_of_det_ne_zero
      (A := A) hdet
  exact higham9_1_exists_partialPivotChoice_pivot_ne_zero A 0
    ⟨r₀, Nat.zero_le _, hr₀⟩

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, the first-stage
partial-pivot row swap fixes every active row after the first reduced row. -/
theorem higham9_10_hessenberg_firstPivotRowSwap_tail {m : ℕ}
    {r : Fin (m + 1)} (hr : r.val ≤ 1) {i : Fin m}
    (hi : 1 ≤ i.val) :
    higham9_7_firstPivotRowSwap r i.succ = i.succ := by
  have hne_zero : i.succ ≠ (0 : Fin (m + 1)) := Fin.succ_ne_zero i
  have hne_r : i.succ ≠ r := by
    intro h
    have hval : i.val + 1 = r.val := by
      simpa using congrArg Fin.val h
    omega
  simp [higham9_7_firstPivotRowSwap, hne_zero, hne_r]

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, rows below the
first active row are unchanged by the first Schur-complement update. -/
theorem higham9_10_hessenberg_firstSchurComplement_tail_rows_eq_original {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ} {r : Fin (m + 1)}
    (hH : IsUpperHessenberg (m + 1) A) (hr : r.val ≤ 1)
    {i j : Fin m} (hi : 1 ≤ i.val) :
    luFirstSchurComplement
        (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) i j =
      A i.succ j.succ := by
  let sigma := higham9_7_firstPivotRowSwap r
  have hsigma : sigma i.succ = i.succ :=
    higham9_10_hessenberg_firstPivotRowSwap_tail hr hi
  have hzero : A i.succ 0 = 0 := by
    apply hH
    have hpos : 0 < i.val := by omega
    simpa using Nat.succ_lt_succ hpos
  simp [luFirstSchurComplement, higham9_2_rowPermutedMatrix, sigma, hsigma, hzero]

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, after the first
partial-pivoting adjacent row swap and Schur update, the reduced active matrix
is still upper Hessenberg. -/
theorem higham9_10_hessenberg_firstSchurComplement_isUpperHessenberg {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ} {r : Fin (m + 1)}
    (hH : IsUpperHessenberg (m + 1) A) (hpivot : A r 0 ≠ 0) :
    IsUpperHessenberg m
      (luFirstSchurComplement
        (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) := by
  intro i j hij
  have hr : r.val ≤ 1 :=
    higham9_10_hessenberg_firstColumn_nonzero_row_le_one hH hpivot
  by_cases hi : 1 ≤ i.val
  · rw [higham9_10_hessenberg_firstSchurComplement_tail_rows_eq_original hH hr hi]
    apply hH
    have hlt : j.succ.val + 1 < i.succ.val := by
      have hjs : j.succ.val = j.val + 1 := rfl
      have his : i.succ.val = i.val + 1 := rfl
      omega
    exact hlt
  · omega

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, first reduced-row
bound.  The general partial-pivoting first-step `2M` estimate is normalized
into the row-indexed form needed by the source induction for Hessenberg
matrices: reduced row `i` is bounded by `(i+2) * maxEntryNorm A`. -/
theorem higham9_10_hessenberg_firstSchurComplement_row_bound {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) {r : Fin (m + 1)}
    (hchoice : higham9_1_partialPivotChoice A 0 r) (hpivot : A r 0 ≠ 0)
    (i j : Fin m) :
    |luFirstSchurComplement
        (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) i j| ≤
      (((i.val + 2 : ℕ) : ℝ) * maxEntryNorm (Nat.succ_pos m) A) := by
  have hfirst :=
    higham9_7_partialPivot_firstSchurComplement_entry_abs_le_two A r hchoice hpivot i j
  have hcoef : (2 : ℝ) ≤ ((i.val + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 2 i.val
  exact le_trans hfirst
    (mul_le_mul_of_nonneg_right hcoef (maxEntryNorm_nonneg (Nat.succ_pos m) A))

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, stage invariant.
At a positive active stage, row `0` is the current pivot row and is bounded by
`k * M`; rows below it are unchanged source rows and are bounded by `M`. -/
def higham9_10_HessenbergStageBound {n : ℕ} (M : ℝ) (k : ℕ)
    (A : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, i.val = 0 → |A i j| ≤ (k : ℝ) * M) ∧
    (∀ i j : Fin n, 1 ≤ i.val → |A i j| ≤ M)

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, one-stage
Hessenberg invariant transition.  Under a nonzero first partial pivot, the
Schur complement advances the source row bound from `k * M` to `(k+1) * M`
while preserving the unchanged-tail-row bound by `M`. -/
theorem higham9_10_hessenberg_firstSchurComplement_stageBound {m k : ℕ}
    {M : ℝ} (hM : 0 ≤ M)
    {A : Fin (m + 1) → Fin (m + 1) → ℝ} {r : Fin (m + 1)}
    (hH : IsUpperHessenberg (m + 1) A)
    (hstage : higham9_10_HessenbergStageBound M k A)
    (hchoice : higham9_1_partialPivotChoice A 0 r) (hpivot : A r 0 ≠ 0) :
    higham9_10_HessenbergStageBound M (k + 1)
      (luFirstSchurComplement
        (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) := by
  let sigma := higham9_7_firstPivotRowSwap r
  let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_2_rowPermutedMatrix A sigma
  let S : Fin m → Fin m → ℝ := luFirstSchurComplement Aperm
  change higham9_10_HessenbergStageBound M (k + 1) S
  have hr : r.val ≤ 1 :=
    higham9_10_hessenberg_firstColumn_nonzero_row_le_one hH hpivot
  constructor
  · intro i j hi0
    have hratio : |Aperm i.succ 0 / Aperm 0 0| ≤ 1 := by
      have hraw :=
        higham9_1_partialPivot_multiplier_abs_le_one A 0 r (sigma i.succ)
          hchoice hpivot (Nat.zero_le _)
      simpa [Aperm, higham9_2_rowPermutedMatrix, sigma, higham9_7_firstPivotRowSwap]
        using hraw
    have hterm_le {B : ℝ} (hB : 0 ≤ B)
        (hpivrow : |Aperm 0 j.succ| ≤ B) :
        |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| ≤ B := by
      have hfactor :
          |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| =
            |Aperm i.succ 0 / Aperm 0 0| * |Aperm 0 j.succ| := by
        rw [abs_div, abs_mul, abs_div]
        ring
      calc
        |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0|
            = |Aperm i.succ 0 / Aperm 0 0| * |Aperm 0 j.succ| := hfactor
        _ ≤ 1 * B := mul_le_mul hratio hpivrow (abs_nonneg _) zero_le_one
        _ = B := by ring
    have hsplit :
        |S i j| ≤
          |Aperm i.succ j.succ| +
            |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| := by
      change
        |Aperm i.succ j.succ -
            Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| ≤
          |Aperm i.succ j.succ| +
            |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0|
      simpa [sub_eq_add_neg] using
        abs_add_le (Aperm i.succ j.succ)
          (-(Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0))
    by_cases hr0 : r = 0
    · have hsigma_i : sigma i.succ = i.succ := by
        simp [sigma, higham9_7_firstPivotRowSwap, hr0, Fin.succ_ne_zero]
      have hentry : |Aperm i.succ j.succ| ≤ M := by
        have htail : 1 ≤ i.succ.val := by
          simp
        simpa [Aperm, higham9_2_rowPermutedMatrix, hsigma_i] using
          hstage.2 i.succ j.succ htail
      have hpivrow : |Aperm 0 j.succ| ≤ (k : ℝ) * M := by
        simpa [Aperm, higham9_2_rowPermutedMatrix, sigma,
          higham9_7_firstPivotRowSwap, hr0] using
          hstage.1 (0 : Fin (m + 1)) j.succ rfl
      have hkM_nonneg : 0 ≤ (k : ℝ) * M :=
        mul_nonneg (Nat.cast_nonneg' k) hM
      calc
        |S i j|
            ≤ |Aperm i.succ j.succ| +
                |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| := hsplit
        _ ≤ M + (k : ℝ) * M :=
              add_le_add hentry (hterm_le hkM_nonneg hpivrow)
        _ = ((k + 1 : ℕ) : ℝ) * M := by
              rw [Nat.cast_add, Nat.cast_one]
              ring
    · have hrval : r.val = 1 := by
        have hrne : r.val ≠ 0 := by
          intro hzero
          exact hr0 (Fin.ext hzero)
        omega
      have hir : i.succ = r := by
        apply Fin.ext
        have his : i.succ.val = i.val + 1 := rfl
        omega
      have hsigma_i : sigma i.succ = 0 := by
        simp [sigma, higham9_7_firstPivotRowSwap, hir]
      have hentry : |Aperm i.succ j.succ| ≤ (k : ℝ) * M := by
        simpa [Aperm, higham9_2_rowPermutedMatrix, hsigma_i] using
          hstage.1 (0 : Fin (m + 1)) j.succ rfl
      have hpivrow : |Aperm 0 j.succ| ≤ M := by
        have hr_tail : 1 ≤ r.val := by omega
        simpa [Aperm, higham9_2_rowPermutedMatrix, sigma,
          higham9_7_firstPivotRowSwap] using
          hstage.2 r j.succ hr_tail
      have hkM_nonneg : 0 ≤ (k : ℝ) * M :=
        mul_nonneg (Nat.cast_nonneg' k) hM
      calc
        |S i j|
            ≤ |Aperm i.succ j.succ| +
                |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| := hsplit
        _ ≤ (k : ℝ) * M + M := add_le_add hentry (hterm_le hM hpivrow)
        _ = ((k + 1 : ℕ) : ℝ) * M := by
              rw [Nat.cast_add, Nat.cast_one]
              ring
  · intro i j hi
    have htail :=
      higham9_10_hessenberg_firstSchurComplement_tail_rows_eq_original
        hH hr hi (i := i) (j := j)
    have hS_eq : S i j = A i.succ j.succ := by
      simpa [S, Aperm, sigma] using htail
    rw [hS_eq]
    have hsucc_tail : 1 ≤ i.succ.val := by
      simp
    exact hstage.2 i.succ j.succ hsucc_tail

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, initial stage
bound.  Every entry of the original active matrix is bounded by its max-entry
norm, so it satisfies the source invariant with stage counter `1`. -/
theorem higham9_10_HessenbergStageBound_one_of_maxEntryNorm {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) :
    higham9_10_HessenbergStageBound (maxEntryNorm hn A) 1 A := by
  constructor
  · intro i j _hi
    simpa using entry_le_maxEntryNorm hn A i j
  · intro i j _hi
    exact entry_le_maxEntryNorm hn A i j

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, an explicit
recursive trace interface for partial-pivoting elimination on upper-Hessenberg
active matrices.  The `step` constructor records exactly the adjacent
partial-pivot row swap and first Schur complement used by the source proof; it
does not assert that such a trace has been constructed for every nonsingular
input. -/
inductive higham9_10_HessenbergGEPPTrace (M : ℝ) :
    (k n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | init {n : ℕ} {A : Fin n → Fin n → ℝ}
      (hH : IsUpperHessenberg n A)
      (hstage : higham9_10_HessenbergStageBound M 1 A) :
      higham9_10_HessenbergGEPPTrace M 1 n A
  | step {m k : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {r : Fin (m + 1)}
      (hprev : higham9_10_HessenbergGEPPTrace M k (m + 1) A)
      (hchoice : higham9_1_partialPivotChoice A 0 r)
      (hpivot : A r 0 ≠ 0) :
      higham9_10_HessenbergGEPPTrace M (k + 1) m
        (luFirstSchurComplement
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)))

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, recursive trace
induction.  Along any explicit Hessenberg GEPP trace, every active matrix
remains upper Hessenberg and satisfies the source stage invariant. -/
theorem higham9_10_HessenbergGEPPTrace_upperHessenberg_and_stageBound
    {M : ℝ} (hM : 0 ≤ M) {k n : ℕ} {A : Fin n → Fin n → ℝ}
    (htrace : higham9_10_HessenbergGEPPTrace M k n A) :
    IsUpperHessenberg n A ∧ higham9_10_HessenbergStageBound M k A := by
  induction htrace with
  | init hH hstage =>
      exact ⟨hH, hstage⟩
  | step hprev hchoice hpivot ih =>
      rcases ih with ⟨hH, hstage⟩
      exact
        ⟨higham9_10_hessenberg_firstSchurComplement_isUpperHessenberg hH hpivot,
          higham9_10_hessenberg_firstSchurComplement_stageBound hM hH hstage
            hchoice hpivot⟩

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, upper-Hessenberg
projection from the recursive trace invariant. -/
theorem higham9_10_HessenbergGEPPTrace_isUpperHessenberg
    {M : ℝ} (hM : 0 ≤ M) {k n : ℕ} {A : Fin n → Fin n → ℝ}
    (htrace : higham9_10_HessenbergGEPPTrace M k n A) :
    IsUpperHessenberg n A :=
  (higham9_10_HessenbergGEPPTrace_upperHessenberg_and_stageBound hM htrace).1

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, stage-bound
projection from the recursive trace invariant. -/
theorem higham9_10_HessenbergGEPPTrace_stageBound
    {M : ℝ} (hM : 0 ≤ M) {k n : ℕ} {A : Fin n → Fin n → ℝ}
    (htrace : higham9_10_HessenbergGEPPTrace M k n A) :
    higham9_10_HessenbergStageBound M k A :=
  (higham9_10_HessenbergGEPPTrace_upperHessenberg_and_stageBound hM htrace).2

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, every stage
counter occurring in the explicit Hessenberg trace is positive. -/
theorem higham9_10_HessenbergGEPPTrace_stage_pos
    {M : ℝ} {k n : ℕ} {A : Fin n → Fin n → ℝ}
    (htrace : higham9_10_HessenbergGEPPTrace M k n A) :
    0 < k := by
  induction htrace with
  | init _hH _hstage =>
      norm_num
  | step _hprev _hchoice _hpivot ih =>
      omega

/-- **Theorem 9.10 / upper-Hessenberg GEPP `U` trace**, a recursive exact
partial-pivoting trace that exposes the final upper-factor rows.  A step stores
the current Hessenberg trace, the adjacent partial-pivoting row swap, and the
upper factor obtained by placing the permuted pivot row above the recursively
computed upper factor of the Schur complement. -/
inductive higham9_10_HessenbergGEPPUTrace (M : ℝ) :
    (k n : ℕ) → (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Prop
  | done {k : ℕ} {A U : Fin 0 → Fin 0 → ℝ} :
      higham9_10_HessenbergGEPPUTrace M k 0 A U
  | step {m k : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {r : Fin (m + 1)} {U₁ : Fin m → Fin m → ℝ}
      (htrace : higham9_10_HessenbergGEPPTrace M k (m + 1) A)
      (hchoice : higham9_1_partialPivotChoice A 0 r)
      (hpivot : A r 0 ≠ 0)
      (hnext :
        higham9_10_HessenbergGEPPUTrace M (k + 1) m
          (luFirstSchurComplement
            (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) U₁) :
      higham9_10_HessenbergGEPPUTrace M k (m + 1) A
        (luFirstStepU
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) U₁)

/-- **Theorem 9.10 / upper-Hessenberg GEPP `U` trace**, the exposed `U` rows
are upper triangular along the recursive trace. -/
theorem higham9_10_HessenbergGEPPUTrace_upper_zero {M : ℝ} :
    ∀ {k n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_10_HessenbergGEPPUTrace M k n A U →
      ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
  intro k n A U htrace
  induction htrace with
  | done =>
      intro i
      exact Fin.elim0 i
  | step hactive _hchoice _hpivot hnext ih =>
      intro i j hij
      by_cases hi : i = 0
      · subst i
        exact (Nat.not_lt_zero _ hij).elim
      · by_cases hj : j = 0
        · subst j
          simp [luFirstStepU, hi]
        · have hpred : (j.pred hj).val < (i.pred hi).val := by
            have hival := Fin.val_pred i hi
            have hjval := Fin.val_pred j hj
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
            omega
          have hrec := ih (i.pred hi) (j.pred hj) hpred
          simpa [luFirstStepU, hi, hj] using hrec

/-- **Theorem 9.10 / upper-Hessenberg GEPP `U` trace**, row-indexed upper
factor bound.  Along any explicit Hessenberg GEPP `U` trace at source stage
counter `k`, row `i` of the exposed upper factor is bounded by `(k+i)M`. -/
theorem higham9_10_HessenbergGEPPUTrace_row_bound {M : ℝ} (hM : 0 ≤ M) :
    ∀ {k n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_10_HessenbergGEPPUTrace M k n A U →
      ∀ i j : Fin n, |U i j| ≤ ((k + i.val : ℕ) : ℝ) * M := by
  intro k n A U hutrace
  induction hutrace with
  | done =>
      intro i
      exact Fin.elim0 i
  | step hactive hchoice hpivot hnext ih =>
      rename_i m k A r U₁
      intro i j
      let sigma := higham9_7_firstPivotRowSwap r
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
        higham9_2_rowPermutedMatrix A sigma
      rcases higham9_10_HessenbergGEPPTrace_upperHessenberg_and_stageBound
          hM hactive with ⟨hH, hstage⟩
      by_cases hi : i = 0
      · subst i
        have hpivrow : |Aperm 0 j| ≤ (k : ℝ) * M := by
          by_cases hr0 : r = 0
          · simpa [Aperm, higham9_2_rowPermutedMatrix, sigma,
              higham9_7_firstPivotRowSwap, hr0] using
              hstage.1 (0 : Fin (m + 1)) j rfl
          · have hrle : r.val ≤ 1 :=
              higham9_10_hessenberg_firstColumn_nonzero_row_le_one hH hpivot
            have hrpos : 1 ≤ r.val := by
              have hrne : r.val ≠ 0 := by
                intro hzero
                exact hr0 (Fin.ext hzero)
              omega
            have htail : |A r j| ≤ M := hstage.2 r j hrpos
            have hkpos : 0 < k :=
              higham9_10_HessenbergGEPPTrace_stage_pos hactive
            have hkcoef : (1 : ℝ) ≤ (k : ℝ) := by
              exact_mod_cast hkpos
            have hM_le : M ≤ (k : ℝ) * M := by
              calc
                M = (1 : ℝ) * M := by ring
                _ ≤ (k : ℝ) * M :=
                    mul_le_mul_of_nonneg_right hkcoef hM
            calc
              |Aperm 0 j| = |A r j| := by
                  simp [Aperm, higham9_2_rowPermutedMatrix, sigma,
                    higham9_7_firstPivotRowSwap]
              _ ≤ M := htail
              _ ≤ (k : ℝ) * M := hM_le
        simpa [Aperm, luFirstStepU] using hpivrow
      · by_cases hj : j = 0
        · subst j
          have hnonneg : 0 ≤ ((k + i.val : ℕ) : ℝ) * M :=
            mul_nonneg (Nat.cast_nonneg' (k + i.val)) hM
          simpa [Aperm, luFirstStepU, hi] using hnonneg
        · have hrec := ih (i.pred hi) (j.pred hj)
          have hidx : k + i.val = k + 1 + (i.pred hi).val := by
            have hival := Fin.val_pred i hi
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            omega
          simpa [Aperm, luFirstStepU, hi, hj, hidx] using hrec

/-- **Theorem 9.10**, final scalar step in Wilkinson's upper-Hessenberg growth
argument.  If the source induction for GEPP on an upper-Hessenberg matrix has
shown that final upper-row `i` is bounded by `(i+1) * maxEntryNorm A`, then the
Higham max-entry growth factor satisfies `rho_n^p <= n`.

This is not the full GEPP trace proof; it isolates the arithmetic consequence of
the row-indexed pivot-row bound stated in the source proof. -/
theorem higham9_10_hessenberg_growthFactorEntry_le_card_of_row_bounds {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hRowBound : ∀ i j : Fin n,
      |U i j| ≤ ((i.val + 1 : ℕ) : ℝ) * maxEntryNorm hn A) :
    growthFactorEntry hn A U hA ≤ (n : ℝ) := by
  apply growthFactorEntry_le_of_entry_bound_factor hn A U (n : ℝ) hA
  intro i j
  have hcoef : ((i.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt i.isLt
  exact le_trans (hRowBound i j)
    (mul_le_mul_of_nonneg_right hcoef (le_of_lt hA))

/-- **Theorem 9.10**, upper-Hessenberg componentwise stability once the
algorithmic growth bound is supplied. -/
theorem higham9_10_hessenberg_growth_backward_error (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ ↑n * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * ↑n * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  hessenberg_growth_backward_error n A L_hat U_hat ε hε hLU hGrowth

/-- **Theorem 9.10**, solve-level componentwise stability for upper-Hessenberg
systems once the source growth inequality is supplied.  The theorem does not
assert the algorithmic Hessenberg growth proof; it packages the available
factorization-and-triangular-solve error theorem with the explicit
`|L_hat||U_hat| <= n |A|` hypothesis. -/
theorem higham9_10_hessenberg_lu_solve_backward_stable_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ (n : ℝ) * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ (n : ℝ) * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_tight fp n A L_hat U_hat b hL_diag hU_diag hLU hn hn3
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hγ3n := gamma_nonneg fp hn3
  calc |ΔA i j|
      ≤ gamma fp (3 * n) * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * n) * ((n : ℝ) * |A i j|) :=
        mul_le_mul_of_nonneg_left (hGrowth i j) hγ3n
    _ = (n : ℝ) * gamma fp (3 * n) * |A i j| := by ring

/-- **Theorem 9.11**, Bohte banded-growth scalar bound.

The source formula is `2^(2p-1) - (p-1)2^(p-2)`.  The formal expression uses
natural-number exponents; for the printed `p = 1` case the second coefficient
is zero, so the saturated exponent has no effect on the value. -/
noncomputable def higham9_11_bohteBound (p : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * p - 1) - ((p : ℝ) - 1) * (2 : ℝ) ^ (p - 2)

/-- **Theorem 9.11**, Bohte formula special case `p = 1`: tridiagonal
matrices give the scalar bound `2`. -/
theorem higham9_11_bohteBound_tridiagonal :
    higham9_11_bohteBound 1 = 2 := by
  norm_num [higham9_11_bohteBound]
  rfl

/-- **Theorem 9.11**, arithmetic check for the formal Bohte expression at
`p = 2`: the printed scalar formula evaluates to `7`.  This records only the
formula arithmetic, not a pentadiagonal growth theorem or attainability claim. -/
theorem higham9_11_bohteBound_pentadiagonal_formula :
    higham9_11_bohteBound 2 = 7 := by
  norm_num [higham9_11_bohteBound]
  rfl

/-- **Theorem 9.11**, arithmetic check for the source's `n = 9`, `p = 4`
Bohte example: the printed scalar formula evaluates to `116`.  This records
only the scalar formula value, not the example's pivot trace or attainability
claim. -/
theorem higham9_11_bohteBound_bandwidth_four_formula :
    higham9_11_bohteBound 4 = 116 := by
  norm_num [higham9_11_bohteBound]
  rfl

/-- **Theorem 9.11**, the printed Bohte scalar expression is nonnegative.
This discharges the nonnegativity side condition needed when using the
expression as a growth constant; it does not prove the banded growth theorem
that supplies the componentwise growth hypothesis. -/
theorem higham9_11_bohteBound_nonneg (p : ℕ) :
    0 ≤ higham9_11_bohteBound p := by
  cases p with
  | zero =>
      have h0 : higham9_11_bohteBound 0 = 2 := by
        norm_num [higham9_11_bohteBound]
        rfl
      rw [h0]
      norm_num
  | succ p =>
      cases p with
      | zero =>
          rw [higham9_11_bohteBound_tridiagonal]
          norm_num
      | succ k =>
          unfold higham9_11_bohteBound
          norm_num
          change ((k : ℝ) + 1) * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (2 * k + 3)
          rw [show 2 * k + 3 = k + (k + 3) by omega, pow_add]
          rw [mul_comm ((2 : ℝ) ^ k)]
          exact mul_le_mul_of_nonneg_right (by
            have hk1 : k + 1 ≤ 2 ^ (k + 1) := (k + 1).lt_two_pow_self.le
            have hmono : 2 ^ (k + 1) ≤ 2 ^ (k + 3) :=
              pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega)
            exact_mod_cast hk1.trans hmono) (pow_nonneg (by norm_num) k)

/-- **Theorem 9.11**, banded growth-factor solve bound once the Bohte growth
constant has been supplied. -/
theorem higham9_11_banded_growth_factor_solve_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ) (hρ : 0 ≤ ρ_bound)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ρ_bound * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  banded_growth_factor_solve_tight fp n A L_hat U_hat b ρ_bound hρ
    hL_diag hU_diag hLU hn hn3 hGrowth

/-- **Theorem 9.11**, solve bound specialized to the printed Bohte scalar
expression.  The theorem still requires the source growth hypothesis with this
constant; it only proves the scalar nonnegativity needed by the generic
growth-factor wrapper. -/
theorem higham9_11_bohte_banded_solve_tight (fp : FPModel) (n p : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤
        higham9_11_bohteBound p * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        higham9_11_bohteBound p * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_11_banded_growth_factor_solve_tight fp n A L_hat U_hat b
    (higham9_11_bohteBound p) (higham9_11_bohteBound_nonneg p)
    hL_diag hU_diag hLU hn hn3 hGrowth

/-! ## §9.6 Special Tridiagonal Classes -/

/-- **Theorem 9.12(a)**, SPD optimal-growth backward-error form once the
SPD growth inequality has been supplied. -/
theorem higham9_12_spd_lu_backward_error (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  spd_lu_backward_error n A L_hat U_hat ε hε hSPD hLU hGrowth

/-- **Theorem 9.12(a)**, SPD tridiagonal algebraic core.  If the exact
tridiagonal LU certificate has the source SPD factor shape `U = D L^T` with
positive diagonal `D`, then `|L||U| = |LU| = |A|` componentwise.  This proves
the local equality step in the printed proof; the existence of such a
factorization remains an explicit certificate input. -/
theorem higham9_12_spd_tridiag_absLU_eq_of_positive_DLT {n : ℕ}
    (A L U : Fin n → Fin n → ℝ) (d : Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U k j = d k * L j k) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| = |A i j| :=
  tridiag_spd_shape_absLU_eq_absA L U A d hStruct hLU_eq hd_pos hDLT

/-- **Theorem 9.12(a)**, SPD tridiagonal backward-error handoff from the
explicit positive-`D L^T` LU certificate.  The theorem supplies the
componentwise growth hypothesis needed by the generic SPD LU backward-error
bound; it does not assert existence of the certificate. -/
theorem higham9_12_spd_tridiag_lu_backward_error_of_positive_DLT (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (d : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U_hat k j = d k * L_hat j k) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_12_spd_lu_backward_error n A L_hat U_hat ε hε hSPD hLU
    (fun i j =>
      le_of_eq
        (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT A L_hat U_hat d
          hStruct hLU_eq hd_pos hDLT i j))

/-- **Theorem 9.12(b/c)**, nonnegative LU factors give
`|L||U| = |A|`. -/
theorem higham9_12_nonneg_lu_optimal_growth (n : ℕ)
    (A L U : Fin n → Fin n → ℝ)
    (hNonneg : HasNonnegLUFactors n A L U) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| = |A i j| :=
  nonneg_lu_optimal_growth n A L U hNonneg

/-- **Theorem 9.12**, max-entry growth consequence of optimal componentwise
growth.  If the unit-lower factor satisfies `|L||U| ≤ |A|`, then the final
upper factor has Higham max-entry growth factor at most one. -/
theorem higham9_growthFactorEntry_le_one_of_absLU_le_absA {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hLdiag_abs : ∀ i : Fin n, |L i i| = 1)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ |A i j|) :
    growthFactorEntry hn A U hAmax ≤ 1 := by
  have hUmax_le_Amax : maxEntryNorm hn U ≤ maxEntryNorm hn A := by
    unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have hterm :
        |L i i| * |U i j| ≤ ∑ k : Fin n, |L i k| * |U k j| :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun k : Fin n => |L i k| * |U k j|)
        (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ i)
    have hU_le_absLU :
        |U i j| ≤ ∑ k : Fin n, |L i k| * |U k j| := by
      simpa [hLdiag_abs i] using hterm
    exact le_trans hU_le_absLU (le_trans (hAbsLU_le i j) (entry_le_maxEntryNorm hn A i j))
  unfold growthFactorEntry
  rw [div_le_iff₀ hAmax]
  simpa using hUmax_le_Amax

/-- **Theorem 9.12(a)**, max-entry growth consequence of the SPD
tridiagonal positive-`D L^T` LU certificate: Higham's growth factor satisfies
`rho <= 1`. -/
theorem higham9_12_spd_tridiag_growthFactorEntry_le_one {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ) (d : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n, U k j = d k * L j k) :
    growthFactorEntry hn A U hAmax ≤ 1 := by
  apply higham9_growthFactorEntry_le_one_of_absLU_le_absA hn A L U hAmax
  · intro i
    simp [hStruct.L_diag i]
  · intro i j
    exact le_of_eq
      (higham9_12_spd_tridiag_absLU_eq_of_positive_DLT A L U d
        hStruct hLU_eq hd_pos hDLT i j)

/-- **Theorem 9.12(b/c)**, nonnegative LU factors give max-entry growth
factor at most one. -/
theorem higham9_12_nonneg_lu_growthFactorEntry_le_one {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hNonneg : HasNonnegLUFactors n A L U) :
    growthFactorEntry hn A U hAmax ≤ 1 := by
  apply higham9_growthFactorEntry_le_one_of_absLU_le_absA hn A L U hAmax
  · intro i
    simp [hNonneg.1.L_diag i]
  · intro i j
    exact le_of_eq (higham9_12_nonneg_lu_optimal_growth n A L U hNonneg i j)

/-- **Theorem 9.12(c)**, M-matrix optimal growth from nonnegative LU factors. -/
theorem higham9_12_mmatrix_lu_optimal_growth (n : ℕ)
    (A L U : Fin n → Fin n → ℝ)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U k j) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| = |A i j| :=
  mmatrix_lu_optimal_growth n A L U hM hLU hL_nn hU_nn

/-- **Theorem 9.12(c)**, the M-matrix optimal-growth hypothesis also gives
Higham max-entry growth factor at most one. -/
theorem higham9_12_mmatrix_lu_growthFactorEntry_le_one {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hM : IsMMatrix n A)
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U k j) :
    growthFactorEntry hn A U hAmax ≤ 1 := by
  apply higham9_growthFactorEntry_le_one_of_absLU_le_absA hn A L U hAmax
  · intro i
    simp [hLU.L_diag i]
  · intro i j
    exact le_of_eq (higham9_12_mmatrix_lu_optimal_growth n A L U hM hLU hL_nn hU_nn i j)

/-- **Theorem 9.12(d)**, sign equivalence preserves optimal growth. -/
theorem higham9_12_sign_equiv_optimal_growth (n : ℕ)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (A : Fin n → Fin n → ℝ)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (L_A U_A : Fin n → Fin n → ℝ)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L_A i k| * |U_A k j| = |A i j| :=
  sign_equiv_optimal_growth n B L_B U_B D₁ D₂ hD₁ hD₂ hB_growth
    A hA_eq L_A U_A hLA_abs hUA_abs

/-- **Theorem 9.12(d)**, sign-equivalent optimal-growth factors also give
Higham max-entry growth factor at most one. -/
theorem higham9_12_sign_equiv_growthFactorEntry_le_one {n : ℕ} (hn : 0 < n)
    (B L_B U_B : Fin n → Fin n → ℝ)
    (D₁ D₂ : Fin n → Fin n → ℝ)
    (hD₁ : IsSignDiag n D₁) (hD₂ : IsSignDiag n D₂)
    (hB_growth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_B i k| * |U_B k j| = |B i j|)
    (hLBdiag_abs : ∀ i : Fin n, |L_B i i| = 1)
    (A : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hA_eq : ∀ i j : Fin n,
      A i j = ∑ k₁ : Fin n, D₁ i k₁ * (∑ k₂ : Fin n, B k₁ k₂ * D₂ k₂ j))
    (L_A U_A : Fin n → Fin n → ℝ)
    (hLA_abs : ∀ i k : Fin n, |L_A i k| = |L_B i k|)
    (hUA_abs : ∀ k j : Fin n, |U_A k j| = |U_B k j|) :
    growthFactorEntry hn A U_A hAmax ≤ 1 := by
  apply higham9_growthFactorEntry_le_one_of_absLU_le_absA hn A L_A U_A hAmax
  · intro i
    rw [hLA_abs i i, hLBdiag_abs i]
  · intro i j
    exact le_of_eq
      (higham9_12_sign_equiv_optimal_growth n B L_B U_B D₁ D₂ hD₁ hD₂
        hB_growth A hA_eq L_A U_A hLA_abs hUA_abs i j)

/-! ## §9.6 Tridiagonal Matrices -/

/-- **Equations (9.18)--(9.19)**: tridiagonal source data. -/
abbrev higham9_18_TridiagData (n : ℕ) : Type :=
  TridiagData n

/-- **Equation (9.18)**: convert tridiagonal data to its matrix. -/
noncomputable def higham9_18_tridiag_to_matrix {n : ℕ}
    (T : higham9_18_TridiagData n) : Fin n → Fin n → ℝ :=
  tridiag_to_matrix T

/-- **Equation (9.18)**, the matrix assembled from tridiagonal source data is
tridiagonal in the repository structural predicate. -/
theorem higham9_18_tridiag_to_matrix_isTridiagonal {n : ℕ}
    (T : higham9_18_TridiagData n) :
    IsTridiagonal n (higham9_18_tridiag_to_matrix T) :=
  tridiag_to_matrix_isTridiagonal T

/-- **Equation (9.19)**: computed tridiagonal LU recurrence. -/
noncomputable def higham9_19_tridiag_lu (fp : FPModel) {n : ℕ}
    (T : higham9_18_TridiagData n) : (Fin n → ℝ) × (Fin n → ℝ) :=
  tridiag_lu fp T

/-- **Equation (9.19)**: exact-arithmetic tridiagonal LU recurrence predicate.

This records the algebraic side of the displayed recurrence separately from
the rounded `FPModel` implementation. -/
abbrev higham9_19_TridiagExactLURecurrence {n : ℕ}
    (T : higham9_18_TridiagData n) (l_hat u_hat : Fin n → ℝ) : Prop :=
  TridiagExactLURecurrence T l_hat u_hat

/-- **Equation (9.19)**: a positive tridiagonal index's predecessor. -/
def higham9_19_tridiag_prevIndex {n : ℕ} (i : Fin n)
    (hi : 0 < i.val) : Fin n :=
  tridiag_prevIndex i hi

/-- **Equation (9.19)**, exact recurrence product certificate.

If the explicit tridiagonal factors satisfy the exact recurrence, their matrix
product is the source tridiagonal matrix. -/
theorem higham9_19_tridiag_exact_product_of_recurrence {n : ℕ}
    (T : higham9_18_TridiagData n) (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat) :
    ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j :=
  tridiag_exact_product_of_recurrence T l_hat u_hat hrec

/-- **Theorem 9.12(a)**, explicit tridiagonal-builder SPD algebraic core.
For factors assembled from equation (9.19)'s `L`/`U` builders, a visible
positive-`D L^T` certificate gives `|L||U| = |A|` componentwise. -/
theorem higham9_12_spd_tridiag_builder_absLU_eq_of_positive_DLT {n : ℕ}
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| =
        |higham9_18_tridiag_to_matrix T i j| :=
  higham9_12_spd_tridiag_absLU_eq_of_positive_DLT
    (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) d
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact hd_pos hDLT

/-- **Theorem 9.12(a)**, explicit tridiagonal-builder SPD max-entry growth
consequence `rho <= 1` from a positive-`D L^T` certificate. -/
theorem higham9_12_spd_tridiag_builder_growthFactorEntry_le_one {n : ℕ}
    (hn : 0 < n)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T))
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 1 :=
  higham9_12_spd_tridiag_growthFactorEntry_le_one hn
    (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) d
    hAmax
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact hd_pos hDLT

/-- **Theorem 9.12(a)**, explicit tridiagonal-builder SPD backward-error
handoff from a positive-`D L^T` certificate. -/
theorem higham9_12_spd_tridiag_builder_lu_backward_error_of_positive_DLT
    (n : ℕ)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hLU : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i j,
        ∑ k : Fin n, tridiag_L_matrix l_hat i k *
            tridiag_U_matrix u_hat T.c k j =
          higham9_18_tridiag_to_matrix T i j + ΔA i j) :=
  higham9_12_spd_tridiag_lu_backward_error_of_positive_DLT n
    (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) d
    ε hε hSPD hLU
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact hd_pos hDLT

/-- **Theorem 9.12(a)**, exact-recurrence builder form of the SPD
positive-`D L^T` equality.  The equation (9.19) exact recurrence supplies the
product certificate. -/
theorem higham9_12_spd_tridiag_builder_absLU_eq_of_recurrence {n : ℕ}
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| =
        |higham9_18_tridiag_to_matrix T i j| :=
  higham9_12_spd_tridiag_builder_absLU_eq_of_positive_DLT T l_hat u_hat d
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hd_pos hDLT

/-- **Theorem 9.12(a)**, exact-recurrence builder form of the SPD
positive-`D L^T` max-entry growth consequence. -/
theorem higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_recurrence
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T))
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 1 :=
  higham9_12_spd_tridiag_builder_growthFactorEntry_le_one hn T l_hat u_hat d
    hAmax
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hd_pos hDLT

/-- **Theorem 9.12(a)**, exact-recurrence builder form of the SPD
positive-`D L^T` backward-error handoff. -/
theorem higham9_12_spd_tridiag_builder_lu_backward_error_of_recurrence
    (n : ℕ)
    (T : higham9_18_TridiagData n) (l_hat u_hat d : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hSPD : IsSymPosDef n (higham9_18_tridiag_to_matrix T))
    (hLU : LUBackwardError n (higham9_18_tridiag_to_matrix T)
      (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c) ε)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hd_pos : ∀ k : Fin n, 0 < d k)
    (hDLT : ∀ k j : Fin n,
      tridiag_U_matrix u_hat T.c k j = d k * tridiag_L_matrix l_hat j k) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i j,
        ∑ k : Fin n, tridiag_L_matrix l_hat i k *
            tridiag_U_matrix u_hat T.c k j =
          higham9_18_tridiag_to_matrix T i j + ΔA i j) :=
  higham9_12_spd_tridiag_builder_lu_backward_error_of_positive_DLT n
    T l_hat u_hat d ε hε hSPD hLU
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hd_pos hDLT

/-- **Theorem 9.13**, structural transpose adapter: tridiagonality is preserved
and reflected by the real matrix transpose.  This supplies the row/column
orientation bridge needed before the remaining row-dominant tridiagonal growth
proof. -/
theorem higham9_13_tridiagonal_transpose_iff {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    IsTridiagonal n (matTranspose A) ↔ IsTridiagonal n A := by
  constructor
  · intro h i j hij
    have hswap : j.val + 1 < i.val ∨ i.val + 1 < j.val := by
      rcases hij with hlt | hlt
      · exact Or.inr hlt
      · exact Or.inl hlt
    simpa [matTranspose] using h j i hswap
  · intro h i j hij
    have hswap : j.val + 1 < i.val ∨ i.val + 1 < j.val := by
      rcases hij with hlt | hlt
      · exact Or.inr hlt
      · exact Or.inl hlt
    simpa [matTranspose] using h j i hswap

/-- **Theorem 9.12 / Theorem 9.13 core**: for bidiagonal LU of a
column-diagonally-dominant tridiagonal matrix, `|L||U| ≤ 3|A|`. -/
theorem higham9_13_tridiag_growth_bound_3 {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hL_bound : ∀ i j : Fin n, |L i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| :=
  tridiag_growth_bound_3 L U A hStruct hLU_eq hL_bound hA_tridiag hColDom

/-- **Theorem 9.13**, max-entry growth consequence of the structural
tridiagonal bound.  The local componentwise theorem `|L||U| <= 3|A|`,
together with the unit lower diagonal in the tridiagonal LU structure, implies
Higham's max-entry growth factor satisfies `rho <= 3`. -/
theorem higham9_13_tridiag_growthFactorEntry_le_three {n : ℕ} (hn : 0 < n)
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hL_bound : ∀ i j : Fin n, |L i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hAmax ≤ 3 := by
  exact growthFactorEntry_le_of_absLU_componentwise hn A L U 3 (by norm_num)
    hAmax
    (fun i => by rw [hStruct.L_diag i, abs_one])
    (higham9_13_tridiag_growth_bound_3 L U A hStruct hLU_eq hL_bound
      hA_tridiag hColDom)

/-- **Theorem 9.13**, exact-LU structural handoff for column-dominant
tridiagonal matrices.  This removes the separate `IsTridiagLU` hypothesis
from the structural wrapper while keeping the source multiplier bound
`|L_ij| <= 1` visible. -/
theorem higham9_13_tridiag_growth_bound_3_of_LUFactSpec {n : ℕ}
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_bound : ∀ i j : Fin n, |L i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| := by
  have hStruct : IsTridiagLU n L U :=
    hLU.isTridiagLU_of_tridiagonal hA_tridiag
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
  exact higham9_13_tridiag_growth_bound_3 L U A hStruct hLU.product_eq
    hL_bound hA_tridiag hColDom

/-- **Theorem 9.13**, max-entry growth consequence for an ordinary exact LU
factorization of a nonsingular column-diagonally-dominant tridiagonal matrix,
once the source multiplier bound `|L_ij| <= 1` is supplied. -/
theorem higham9_13_growthFactorEntry_le_three_of_LUFactSpec {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_bound : ∀ i j : Fin n, |L i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hAmax ≤ 3 := by
  have hStruct : IsTridiagLU n L U :=
    hLU.isTridiagLU_of_tridiagonal hA_tridiag
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
  exact growthFactorEntry_le_of_absLU_componentwise hn A L U 3 (by norm_num)
    hAmax
    (fun i => by rw [hStruct.L_diag i, abs_one])
    (higham9_13_tridiag_growth_bound_3_of_LUFactSpec
      A L U hLU hdetA hL_bound hA_tridiag hColDom)

/-- **Theorem 9.13**, column-dominant multiplier bound for an ordinary exact
LU factorization of a nonsingular tridiagonal matrix.  This is the source
side condition `|l_ij| <= 1` derived from column diagonal dominance rather than
left as an extra hypothesis. -/
theorem higham9_13_colDiagDom_L_entries_bounded_of_LUFactSpec {n : ℕ}
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    ∀ i j : Fin n, |L i j| ≤ 1 := by
  have hU_diag : ∀ i : Fin n, U i i ≠ 0 :=
    hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA
  have hStruct : IsTridiagLU n L U :=
    hLU.isTridiagLU_of_tridiagonal hA_tridiag hU_diag
  exact tridiag_colDom_L_entries_bounded L U A hStruct hLU.product_eq
    hColDom hU_diag

/-- **Theorem 9.13**, exact-LU column-dominant tridiagonal componentwise
growth bound without a separate multiplier-bound hypothesis. -/
theorem higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec {n : ℕ}
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| :=
  higham9_13_tridiag_growth_bound_3_of_LUFactSpec A L U hLU hdetA
    (higham9_13_colDiagDom_L_entries_bounded_of_LUFactSpec
      A L U hLU hdetA hA_tridiag hColDom)
    hA_tridiag hColDom

/-- **Theorem 9.13**, exact-LU column-dominant tridiagonal max-entry growth
bound without a separate multiplier-bound hypothesis. -/
theorem higham9_13_colDiagDom_growthFactorEntry_le_three_of_LUFactSpec
    {n : ℕ} (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hAmax ≤ 3 :=
  higham9_13_growthFactorEntry_le_three_of_LUFactSpec hn A L U hLU hdetA
    (higham9_13_colDiagDom_L_entries_bounded_of_LUFactSpec
      A L U hLU hdetA hA_tridiag hColDom)
    hA_tridiag hColDom hAmax

/-- **Theorem 9.13**, row-dominant tridiagonal transpose specialization.

If `A` is row-diagonally dominant and tridiagonal, then `Aᵀ` is
column-diagonally dominant and tridiagonal. Hence any explicit bidiagonal LU
certificate for the transposed problem satisfies the same source `3|Aᵀ|`
componentwise growth bound. This is only the transpose structural bridge; it
does not construct the LU factors of `A` itself. -/
theorem higham9_13_rowDiagDom_transpose_tridiag_growth_bound_3 {n : ℕ}
    (L_T U_T A : Fin n → Fin n → ℝ)
    (hStructT : IsTridiagLU n L_T U_T)
    (hLU_eqT : ∀ i j : Fin n,
      ∑ k : Fin n, L_T i k * U_T k j = matTranspose A i j)
    (hL_boundT : ∀ i j : Fin n, |L_T i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L_T i k| * |U_T k j| ≤
        3 * |matTranspose A i j| :=
  higham9_13_tridiag_growth_bound_3 L_T U_T (matTranspose A)
    hStructT hLU_eqT hL_boundT
    ((higham9_13_tridiagonal_transpose_iff A).2 hA_tridiag)
    ((higham9_9_colDiagDominant_transpose_iff_rowDiagDominant A).2 hRowDom)

/-- **Theorem 9.13**, row-dominant transpose max-entry growth consequence.

This is the max-entry growth-factor form of
`higham9_13_rowDiagDom_transpose_tridiag_growth_bound_3`: for the explicit LU
certificate of `Aᵀ`, the upper factor has `rho <= 3`. -/
theorem higham9_13_rowDiagDom_transpose_growthFactorEntry_le_three {n : ℕ}
    (hn : 0 < n)
    (L_T U_T A : Fin n → Fin n → ℝ)
    (hStructT : IsTridiagLU n L_T U_T)
    (hLU_eqT : ∀ i j : Fin n,
      ∑ k : Fin n, L_T i k * U_T k j = matTranspose A i j)
    (hL_boundT : ∀ i j : Fin n, |L_T i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hAmaxT : 0 < maxEntryNorm hn (matTranspose A)) :
    growthFactorEntry hn (matTranspose A) U_T hAmaxT ≤ 3 := by
  exact higham9_13_tridiag_growthFactorEntry_le_three hn L_T U_T
    (matTranspose A) hStructT hLU_eqT hL_boundT
    ((higham9_13_tridiagonal_transpose_iff A).2 hA_tridiag)
    ((higham9_9_colDiagDominant_transpose_iff_rowDiagDominant A).2 hRowDom)
    hAmaxT

/-- **Theorem 9.13**, row-dominant transpose max-entry growth with the source
matrix denominator.

This variant records that `maxEntryNorm Aᵀ = maxEntryNorm A`, so the positivity
needed in the growth-factor denominator is the source matrix's max-entry
positivity, not a separate transposed-matrix assumption. -/
theorem higham9_13_rowDiagDom_transpose_growthFactorEntry_le_three_of_Amax
    {n : ℕ} (hn : 0 < n)
    (L_T U_T A : Fin n → Fin n → ℝ)
    (hStructT : IsTridiagLU n L_T U_T)
    (hLU_eqT : ∀ i j : Fin n,
      ∑ k : Fin n, L_T i k * U_T k j = matTranspose A i j)
    (hL_boundT : ∀ i j : Fin n, |L_T i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn (matTranspose A) U_T
      (by simpa [maxEntryNorm_matTranspose hn A] using hAmax) ≤ 3 := by
  exact higham9_13_rowDiagDom_transpose_growthFactorEntry_le_three hn
    L_T U_T A hStructT hLU_eqT hL_boundT hA_tridiag hRowDom
    (by simpa [maxEntryNorm_matTranspose hn A] using hAmax)

/-- **Theorem 9.13**, direct row-dominant tridiagonal growth bound.

This is the source proof orientation for row diagonal dominance: from an
explicit bidiagonal LU certificate of a row-diagonally-dominant tridiagonal
matrix, `|L||U| <= 3|A|` componentwise. -/
theorem higham9_13_rowDiagDom_tridiag_growth_bound_3 {n : ℕ}
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| :=
  tridiag_rowDom_growth_bound_3 L U A hStruct hLU_eq hA_tridiag hRowDom

/-- **Theorem 9.13**, max-entry growth consequence for the direct row-dominant
tridiagonal case. -/
theorem higham9_13_rowDiagDom_growthFactorEntry_le_three {n : ℕ} (hn : 0 < n)
    (L U A : Fin n → Fin n → ℝ)
    (hStruct : IsTridiagLU n L U)
    (hLU_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hAmax ≤ 3 := by
  exact growthFactorEntry_le_of_absLU_componentwise hn A L U 3 (by norm_num)
    hAmax
    (fun i => by rw [hStruct.L_diag i, abs_one])
    (higham9_13_rowDiagDom_tridiag_growth_bound_3 L U A hStruct hLU_eq
      hA_tridiag hRowDom)

/-- **Theorem 9.13**, exact-LU structural handoff for row-dominant
tridiagonal matrices.  A nonsingular tridiagonal matrix with an ordinary
exact LU certificate has the bidiagonal factor structure needed by Higham's
row-dominant proof, so the componentwise `|L||U| <= 3|A|` conclusion follows
without a separate `IsTridiagLU` assumption. -/
theorem higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec {n : ℕ}
    (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j| := by
  have hStruct : IsTridiagLU n L U :=
    hLU.isTridiagLU_of_tridiagonal hA_tridiag
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
  exact higham9_13_rowDiagDom_tridiag_growth_bound_3 L U A hStruct
    hLU.product_eq hA_tridiag hRowDom

/-- **Theorem 9.13**, source-facing max-entry growth consequence for an
ordinary exact LU factorization of a nonsingular row-diagonally-dominant
tridiagonal matrix. -/
theorem higham9_13_rowDiagDom_growthFactorEntry_le_three_of_LUFactSpec
    {n : ℕ} (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hAmax ≤ 3 := by
  have hStruct : IsTridiagLU n L U :=
    hLU.isTridiagLU_of_tridiagonal hA_tridiag
      (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdetA)
  exact growthFactorEntry_le_of_absLU_componentwise hn A L U 3 (by norm_num)
    hAmax
    (fun i => by rw [hStruct.L_diag i, abs_one])
    (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L U hLU hdetA hA_tridiag hRowDom)

/-- **Theorem 9.13**, source-data builder form for column-dominant
tridiagonal matrices.

The explicit `tridiag_L_matrix`/`tridiag_U_matrix` builders have the
bidiagonal shape required by the structural theorem.  This wrapper keeps the
exact-product certificate and multiplier bound explicit while removing the
separate `IsTridiagLU` hypothesis for matrices assembled from
`TridiagData`. -/
theorem higham9_13_tridiag_builder_growth_bound_3 {n : ℕ}
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| ≤
        3 * |higham9_18_tridiag_to_matrix T i j| :=
  higham9_13_tridiag_growth_bound_3
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    (higham9_18_tridiag_to_matrix T)
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (tridiag_L_matrix_entries_bounded l_hat hl)
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hColDom

/-- **Theorem 9.13**, max-entry growth consequence for the source-data
tridiagonal builders in the column-dominant case. -/
theorem higham9_13_tridiag_builder_growthFactorEntry_le_three {n : ℕ}
    (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T)) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 :=
  higham9_13_tridiag_growthFactorEntry_le_three hn
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    (higham9_18_tridiag_to_matrix T)
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (tridiag_L_matrix_entries_bounded l_hat hl)
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hColDom hAmax

/-- **Theorem 9.13**, source-data builder form for row-dominant tridiagonal
matrices.  The row-dominant structural theorem supplies the growth bound
without a separate multiplier-bound hypothesis. -/
theorem higham9_13_rowDiagDom_tridiag_builder_growth_bound_3 {n : ℕ}
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| ≤
        3 * |higham9_18_tridiag_to_matrix T i j| :=
  higham9_13_rowDiagDom_tridiag_growth_bound_3
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    (higham9_18_tridiag_to_matrix T)
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hRowDom

/-- **Theorem 9.13**, max-entry growth consequence for the source-data
tridiagonal builders in the row-dominant case. -/
theorem higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T)) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 :=
  higham9_13_rowDiagDom_growthFactorEntry_le_three hn
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    (higham9_18_tridiag_to_matrix T)
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hRowDom hAmax

/-- **Theorem 9.13**, source-data column-dominant builder form from the exact
tridiagonal recurrence.

This discharges the exact-product certificate in
`higham9_13_tridiag_builder_growth_bound_3` from the displayed recurrence
(9.19). -/
theorem higham9_13_tridiag_builder_growth_bound_3_of_recurrence {n : ℕ}
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| ≤
        3 * |higham9_18_tridiag_to_matrix T i j| :=
  higham9_13_tridiag_builder_growth_bound_3 T l_hat u_hat
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom

/-- **Theorem 9.13**, max-entry growth consequence for the source-data
column-dominant tridiagonal recurrence. -/
theorem higham9_13_tridiag_builder_growthFactorEntry_le_three_of_recurrence
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T)) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 :=
  higham9_13_tridiag_builder_growthFactorEntry_le_three hn T l_hat u_hat
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom hAmax

/-- **Theorem 9.13**, source-data row-dominant builder form from the exact
tridiagonal recurrence. -/
theorem higham9_13_rowDiagDom_tridiag_builder_growth_bound_3_of_recurrence
    {n : ℕ}
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T)) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j| ≤
        3 * |higham9_18_tridiag_to_matrix T i j| :=
  higham9_13_rowDiagDom_tridiag_builder_growth_bound_3 T l_hat u_hat
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom

/-- **Theorem 9.13**, max-entry growth consequence for the source-data
row-dominant tridiagonal recurrence. -/
theorem higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three_of_recurrence
    {n : ℕ} (hn : 0 < n)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (hAmax : 0 < maxEntryNorm hn (higham9_18_tridiag_to_matrix T)) :
    growthFactorEntry hn (higham9_18_tridiag_to_matrix T)
      (tridiag_U_matrix u_hat T.c) hAmax ≤ 3 :=
  higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three hn
    T l_hat u_hat
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom hAmax

/-- **Theorem 9.14**, tridiagonal diagonally-dominant solve bound in the
absorbed `3γ_6` form. -/
theorem higham9_14_tridiag_diagDom_fu_bound_tight (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 3 * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp 6 * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  tridiag_diagDom_fu_bound_tight n A L_hat U_hat y_hat x_hat b fp h2 h6
    ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq
    ΔU hΔU_bound hΔU_eq
    hGrowth

/-- **Theorem 9.14**, structural tridiagonal diagonally-dominant specialization.

This packages the local Theorem 9.13 growth proof into the absorbed `3γ_6`
backward-error surface: when the computed factors have the bidiagonal
tridiagonal LU structure, multiply exactly to the source matrix, have
unit-bounded lower entries, and the source matrix is tridiagonal and
column-diagonally dominant, the growth hypothesis of
`higham9_14_tridiag_diagDom_fu_bound_tight` follows from
`higham9_13_tridiag_growth_bound_3`. -/
theorem higham9_14_tridiag_diagDom_fu_bound_from_structural_growth (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp 6 * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_diagDom_fu_bound_tight n A L_hat U_hat y_hat x_hat b
    fp h2 h6 ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
    (higham9_13_tridiag_growth_bound_3 L_hat U_hat A
      hStruct hLU_exact hL_bound hA_tridiag hColDom)

/-- **Theorem 9.14**, direct row-dominant structural tridiagonal
specialization.

This is the row-dominant analogue of
`higham9_14_tridiag_diagDom_fu_bound_from_structural_growth`; the growth
hypothesis is discharged by the direct row-dominant proof of Theorem 9.13, so
no separate multiplier-bound hypothesis is needed. -/
theorem higham9_14_tridiag_rowDiagDom_fu_bound_from_structural_growth (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hStruct : IsTridiagLU n L_hat U_hat)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp 6 * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_diagDom_fu_bound_tight n A L_hat U_hat y_hat x_hat b
    fp h2 h6 ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
    (higham9_13_rowDiagDom_tridiag_growth_bound_3 L_hat U_hat A
      hStruct hLU_exact hA_tridiag hRowDom)

/-- **Theorem 9.14**, source-data builder specialization for column-dominant
tridiagonal matrices.

This instantiates the structural `3γ_6` backward-error wrapper with the
explicit tridiagonal matrix builders.  The exact-product and perturbation
certificates remain explicit hypotheses. -/
theorem higham9_14_tridiag_colDiagDom_fu_bound_from_builders (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j,
      |ΔL i j| ≤ gamma fp 2 * |tridiag_L_matrix l_hat i j|)
    (hΔL_eq : ∀ i,
      ∑ j : Fin n, (tridiag_L_matrix l_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j,
      |ΔU i j| ≤ gamma fp 2 * |tridiag_U_matrix u_hat T.c i j|)
    (hΔU_eq : ∀ i,
      ∑ j : Fin n, (tridiag_U_matrix u_hat T.c i j + ΔU i j) * x_hat j =
        y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        3 * gamma fp 6 * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_diagDom_fu_bound_from_structural_growth n
    (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    y_hat x_hat b fp h2 h6
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (tridiag_L_matrix_entries_bounded l_hat hl)
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hColDom
    ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq
    ΔU hΔU_bound hΔU_eq

/-- **Theorem 9.14**, source-data builder specialization for row-dominant
tridiagonal matrices. -/
theorem higham9_14_tridiag_rowDiagDom_fu_bound_from_builders (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hLU_exact : ∀ i j : Fin n,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j,
      |ΔL i j| ≤ gamma fp 2 * |tridiag_L_matrix l_hat i j|)
    (hΔL_eq : ∀ i,
      ∑ j : Fin n, (tridiag_L_matrix l_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j,
      |ΔU i j| ≤ gamma fp 2 * |tridiag_U_matrix u_hat T.c i j|)
    (hΔU_eq : ∀ i,
      ∑ j : Fin n, (tridiag_U_matrix u_hat T.c i j + ΔU i j) * x_hat j =
        y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        3 * gamma fp 6 * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_fu_bound_from_structural_growth n
    (higham9_18_tridiag_to_matrix T)
    (tridiag_L_matrix l_hat) (tridiag_U_matrix u_hat T.c)
    y_hat x_hat b fp h2 h6
    (tridiag_matrices_isTridiagLU l_hat u_hat T.c)
    hLU_exact
    (higham9_18_tridiag_to_matrix_isTridiagonal T)
    hRowDom
    ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq
    ΔU hΔU_bound hΔU_eq

/-- **Theorem 9.14**, column-dominant builder specialization from the exact
tridiagonal recurrence.

This is an exact-recurrence specialization of the existing builder wrapper:
the product certificate is proved from equation (9.19), while the separate
floating-point perturbation certificates remain explicit. -/
theorem higham9_14_tridiag_colDiagDom_fu_bound_from_recurrence (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hl : ∀ i : Fin n, |l_hat i| ≤ 1)
    (hColDom : IsDiagDominant n (higham9_18_tridiag_to_matrix T))
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j,
      |ΔL i j| ≤ gamma fp 2 * |tridiag_L_matrix l_hat i j|)
    (hΔL_eq : ∀ i,
      ∑ j : Fin n, (tridiag_L_matrix l_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j,
      |ΔU i j| ≤ gamma fp 2 * |tridiag_U_matrix u_hat T.c i j|)
    (hΔU_eq : ∀ i,
      ∑ j : Fin n, (tridiag_U_matrix u_hat T.c i j + ΔU i j) * x_hat j =
        y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        3 * gamma fp 6 * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_colDiagDom_fu_bound_from_builders n T l_hat u_hat
    y_hat x_hat b fp h2 h6
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hl hColDom
    ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq
    ΔU hΔU_bound hΔU_eq

/-- **Theorem 9.14**, row-dominant builder specialization from the exact
tridiagonal recurrence. -/
theorem higham9_14_tridiag_rowDiagDom_fu_bound_from_recurrence (n : ℕ)
    (T : higham9_18_TridiagData n)
    (l_hat u_hat : Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hrec : higham9_19_TridiagExactLURecurrence T l_hat u_hat)
    (hRowDom : IsRowDiagDominant n (higham9_18_tridiag_to_matrix T))
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |tridiag_L_matrix l_hat i k| *
        |tridiag_U_matrix u_hat T.c k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, tridiag_L_matrix l_hat i k *
        tridiag_U_matrix u_hat T.c k j =
        higham9_18_tridiag_to_matrix T i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j,
      |ΔL i j| ≤ gamma fp 2 * |tridiag_L_matrix l_hat i j|)
    (hΔL_eq : ∀ i,
      ∑ j : Fin n, (tridiag_L_matrix l_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j,
      |ΔU i j| ≤ gamma fp 2 * |tridiag_U_matrix u_hat T.c i j|)
    (hΔU_eq : ∀ i,
      ∑ j : Fin n, (tridiag_U_matrix u_hat T.c i j + ΔU i j) * x_hat j =
        y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        3 * gamma fp 6 * |higham9_18_tridiag_to_matrix T i j|) ∧
      (∀ i, ∑ j : Fin n,
        (higham9_18_tridiag_to_matrix T i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_rowDiagDom_fu_bound_from_builders n T l_hat u_hat
    y_hat x_hat b fp h2 h6
    (higham9_19_tridiag_exact_product_of_recurrence T l_hat u_hat hrec)
    hRowDom
    ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq
    ΔU hΔU_bound hΔU_eq

/-- **Theorem 9.14**, column-dominant exact-LU tridiagonal specialization.

This is the ordinary exact-LU version of
`higham9_14_tridiag_diagDom_fu_bound_from_structural_growth`: the growth
hypothesis is discharged from `LUFactSpec`, tridiagonality, nonsingularity, and
column diagonal dominance, with the multiplier bound proved locally by
Theorem 9.13. -/
theorem higham9_14_tridiag_colDiagDom_fu_bound_from_LUFactSpec (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp 6 * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_diagDom_fu_bound_tight n A L_hat U_hat y_hat x_hat b
    fp h2 h6 ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
    (higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hColDom)

/-- **Theorem 9.14**, row-dominant exact-LU tridiagonal specialization.

This packages the direct row-dominant Theorem 9.13 exact-LU growth wrapper into
the absorbed `3γ_6` backward-error surface. -/
theorem higham9_14_tridiag_rowDiagDom_fu_bound_from_LUFactSpec (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp 6 * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_14_tridiag_diagDom_fu_bound_tight n A L_hat U_hat y_hat x_hat b
    fp h2 h6 ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
    (higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      A L_hat U_hat hLU hdetA hA_tridiag hRowDom)

/-- **Equation (9.22)**, source scalar `f(u) = 4u + 3u² + u³`. -/
noncomputable def higham9_14_f (u : ℝ) : ℝ :=
  4 * u + 3 * u ^ 2 + u ^ 3

/-- **Theorem 9.14**, source scalar `h(u) = f(u)/(1-u)`. -/
noncomputable def higham9_14_h (u : ℝ) : ℝ :=
  higham9_14_f u / (1 - u)

/-- **Theorem 9.14**, source relation between the printed scalars:
`h(u) = f(u)/(1-u)`. -/
theorem higham9_14_h_eq_f_div (u : ℝ) :
    higham9_14_h u = higham9_14_f u / (1 - u) := by
  rfl

/-- **Theorem 9.14**, nonnegativity of the printed source polynomial
`f(u) = 4u + 3u² + u³` under the standard `0 <= u` side condition. -/
theorem higham9_14_f_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ higham9_14_f u := by
  unfold higham9_14_f
  have hu2 : 0 ≤ u ^ 2 := pow_nonneg hu 2
  have hu3 : 0 ≤ u ^ 3 := pow_nonneg hu 3
  nlinarith

/-- **Theorem 9.14**, denominator-cleared form of the source relation between
`f(u)` and `h(u)`. -/
theorem higham9_14_h_mul_one_sub_eq_f {u : ℝ} (hden : 1 - u ≠ 0) :
    higham9_14_h u * (1 - u) = higham9_14_f u := by
  unfold higham9_14_h higham9_14_f
  field_simp [hden]

/-- **Equations (9.20)--(9.22)**, source-coefficient aggregation.

If the tridiagonal LU factorization perturbation has coefficient `u`, the
forward solve has coefficient `u`, and the back solve has coefficient
`2u + u²`, then the combined solve perturbation has the printed source
coefficient `f(u) = 4u + 3u² + u³` multiplying `|L̂||Û|`. -/
theorem higham9_14_source_f_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ u * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        higham9_14_f u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  have hUcoeff : 0 ≤ 2 * u + u ^ 2 := by
    nlinarith [sq_nonneg u, hu]
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_mixed n A L_hat U_hat y_hat x_hat
      u u (2 * u + u ^ 2) hu hu hUcoeff
      ΔA_LU hΔA_LU_bound hΔA_LU_eq
      b ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
  refine ⟨ΔA, ?_, hΔA_eq⟩
  intro i j
  calc |ΔA i j|
      ≤ (u + u + (2 * u + u ^ 2) + u * (2 * u + u ^ 2)) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ = higham9_14_f u * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
        unfold higham9_14_f
        ring

/-- **Theorem 9.14**, conditional `h(u)` source bound.

This is the final scalar step after `higham9_14_source_f_bound`: once the
remaining class-specific comparison
`|L̂||Û| <= |A|/(1-u)` is available, the printed bound
`|ΔA| <= h(u)|A|` follows. -/
theorem higham9_14_source_h_bound_of_absLUhat_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hAbsLUhat_bound : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j| / (1 - u))
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ u * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    higham9_14_source_f_bound n A L_hat U_hat y_hat x_hat b u hu
      ΔA_LU hΔA_LU_bound hΔA_LU_eq
      ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
  refine ⟨ΔA, ?_, hΔA_eq⟩
  intro i j
  have hf_nonneg : 0 ≤ higham9_14_f u := higham9_14_f_nonneg hu
  calc |ΔA i j|
      ≤ higham9_14_f u * ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
        hΔA_bound i j
    _ ≤ higham9_14_f u * (|A i j| / (1 - u)) :=
        mul_le_mul_of_nonneg_left (hAbsLUhat_bound i j) hf_nonneg
    _ = higham9_14_h u * |A i j| := by
        unfold higham9_14_h
        ring

/-- **Theorem 9.14**, denominator-cleared `h(u)` source bound.

This is the same conditional `h(u)` conclusion as
`higham9_14_source_h_bound_of_absLUhat_bound`, but with the comparison
hypothesis in the source-shaped form
`(1-u) * |L_hat||U_hat| <= |A|`. -/
theorem higham9_14_source_h_bound_of_absLUhat_mul_one_sub_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu_lt_one : u < 1)
    (hAbsLUhat_mul_bound : ∀ i j : Fin n,
      (1 - u) * (∑ k : Fin n, |L_hat i k| * |U_hat k j|) ≤ |A i j|)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      u * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ u * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ (2 * u + u ^ 2) * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ higham9_14_h u * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  refine higham9_14_source_h_bound_of_absLUhat_bound n A L_hat U_hat
    y_hat x_hat b u hu ?_ ΔA_LU hΔA_LU_bound hΔA_LU_eq
    ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
  intro i j
  have hpos : 0 < 1 - u := by linarith
  exact (le_div_iff₀ hpos).mpr (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hAbsLUhat_mul_bound i j)

/-! ## §9.8 Scaling -/

/-- **Equation (9.24)**: two-sided diagonal scaling of the coefficient matrix. -/
noncomputable def higham9_24_scaledMatrix {n : ℕ}
    (D1 D2 : Fin n → ℝ) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => D1 i * A i j * D2 j

/-- **Equation (9.24)**: scaled right-hand side. -/
noncomputable def higham9_24_scaledRhs {n : ℕ}
    (D1 : Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => D1 i * b i

/-- **Equation (9.24)**: change of variables `y = D₂⁻¹ x`. -/
noncomputable def higham9_24_scaledUnknown {n : ℕ}
    (D2 : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (D2 i)⁻¹ * x i

/-- **Equation (9.24)**: scaling preserves exact solutions when `D₂` is
nonsingular componentwise. -/
theorem higham9_24_scaled_system_equiv {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b x D1 D2 : Fin n → ℝ)
    (hD2 : ∀ j : Fin n, D2 j ≠ 0)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i) :
    ∀ i, ∑ j : Fin n,
        higham9_24_scaledMatrix D1 D2 A i j *
          higham9_24_scaledUnknown D2 x j =
        higham9_24_scaledRhs D1 b i := by
  intro i
  unfold higham9_24_scaledMatrix higham9_24_scaledUnknown higham9_24_scaledRhs
  have hterm : ∀ j : Fin n,
      (D1 i * A i j * D2 j) * ((D2 j)⁻¹ * x j) =
        D1 i * (A i j * x j) := by
    intro j
    field_simp [hD2 j]
  calc
    ∑ j : Fin n, (D1 i * A i j * D2 j) * ((D2 j)⁻¹ * x j)
        = ∑ j : Fin n, D1 i * (A i j * x j) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hterm j
    _ = D1 i * ∑ j : Fin n, A i j * x j := by
          rw [Finset.mul_sum]
    _ = D1 i * b i := by
          rw [hAx i]

/-- **Equation (9.25)**: trailing row `∞`-norm used by implicit row scaling. -/
noncomputable def higham9_25_trailingRowInf {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k i : Fin n) : ℝ :=
  Finset.sup' (Finset.univ.filter (fun j : Fin n => k.val ≤ j.val))
    ⟨k, by simp⟩ (fun j => |Astage i j|)

/-- **Equation (9.25)**: implicit row-scaling pivot rule. -/
def higham9_25_implicitRowScalingPivotRule {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r : Fin n) : Prop :=
  k.val ≤ r.val ∧
  higham9_25_trailingRowInf Astage k r ≠ 0 ∧
  ∀ i : Fin n, k.val ≤ i.val →
    higham9_25_trailingRowInf Astage k i ≠ 0 →
      |Astage i k| / higham9_25_trailingRowInf Astage k i ≤
        |Astage r k| / higham9_25_trailingRowInf Astage k r

/-! ## §9.11 Sensitivity -/

/-- **Theorem 9.15**, componentwise LU perturbation identity. -/
theorem higham9_15_lu_perturbation_identity (n : ℕ)
    (A L U δA δL δU : Fin n → Fin n → ℝ)
    (hLU : ∀ i j, ∑ k : Fin n, L i k * U k j = A i j)
    (hPerturbed : ∀ i j,
      ∑ k : Fin n, (L i k + δL i k) * (U k j + δU k j) = A i j + δA i j) :
    ∀ i j, δA i j =
      ∑ k : Fin n, L i k * δU k j +
      ∑ k : Fin n, δL i k * U k j +
      ∑ k : Fin n, δL i k * δU k j :=
  lu_perturbation_identity n A L U δA δL δU hLU hPerturbed

/-- **Theorem 9.15**, componentwise perturbation propagation:
relative perturbations in `L` and `U` produce an
`(α + β + αβ)|L||U|` perturbation in `A`. -/
theorem higham9_15_lu_perturbation_relative_bound (n : ℕ)
    (A L U δA δL δU : Fin n → Fin n → ℝ)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hLU : ∀ i j, ∑ k : Fin n, L i k * U k j = A i j)
    (hPerturbed : ∀ i j,
      ∑ k : Fin n, (L i k + δL i k) * (U k j + δU k j) = A i j + δA i j)
    (hδL : ∀ i k, |δL i k| ≤ α * |L i k|)
    (hδU : ∀ k j, |δU k j| ≤ β * |U k j|) :
    ∀ i j, |δA i j| ≤
      (α + β + α * β) * ∑ k : Fin n, |L i k| * |U k j| :=
  lu_perturbation_relative_bound n A L U δA δL δU
    α β hα hβ hLU hPerturbed hδL hδU

/-! ## Appendix A, Problem 9.2 -/

/-- **Problem 9.2**, appendix counting step: if the danger values coming from
the leading principal submatrix of order `k` form a finite set of size at most
`k`, then the union of all danger values for orders below `n` has cardinality at
most `1 + 2 + ... + (n - 1) = n(n - 1)/2`.

This is the finite-union part of the appendix solution.  Connecting the danger
sets to the eigenvalues of the shifted leading principal blocks
`A(σ)(1:k,1:k)` is still the separate characteristic-polynomial API. -/
theorem higham9_2_danger_shift_count_bound {α : Type*} [DecidableEq α]
    (n : ℕ) (danger : ℕ → Finset α)
    (hcard : ∀ k, k ∈ Finset.range n → (danger k).card ≤ k) :
    ((Finset.range n).biUnion danger).card ≤ n * (n - 1) / 2 := by
  calc
    ((Finset.range n).biUnion danger).card
        ≤ ∑ k ∈ Finset.range n, (danger k).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range n, k :=
          Finset.sum_le_sum (fun k hk => hcard k hk)
    _ = n * (n - 1) / 2 := by
          rw [Finset.sum_range_id]

/-- **Problem 9.2**, the danger values contributed by a leading block, modeled
as the distinct roots of its characteristic polynomial.  For a leading block
`B`, these are precisely the shifts `sigma` for which `sigma I - B` is
singular. -/
noncomputable def higham9_2_charpolyDangerSet {k : ℕ}
    (B : Matrix (Fin k) (Fin k) ℝ) : Finset ℝ :=
  B.charpoly.roots.toFinset

/-- **Problem 9.2**, membership in the characteristic-polynomial danger set is
the source root condition. -/
theorem higham9_2_mem_charpolyDangerSet_iff_isRoot {k : ℕ}
    (B : Matrix (Fin k) (Fin k) ℝ) (sigma : ℝ) :
    sigma ∈ higham9_2_charpolyDangerSet B ↔ B.charpoly.IsRoot sigma := by
  unfold higham9_2_charpolyDangerSet
  rw [Multiset.mem_toFinset]
  exact Polynomial.mem_roots B.charpoly_monic.ne_zero

/-- **Problem 9.2**, membership in the characteristic-polynomial danger set is
equivalent to singularity of the shifted leading block `sigma I - B`. -/
theorem higham9_2_mem_charpolyDangerSet_iff_det_shift_eq_zero {k : ℕ}
    (B : Matrix (Fin k) (Fin k) ℝ) (sigma : ℝ) :
    sigma ∈ higham9_2_charpolyDangerSet B ↔
      (Matrix.scalar (Fin k) sigma - B).det = 0 := by
  rw [higham9_2_mem_charpolyDangerSet_iff_isRoot, Polynomial.IsRoot.def,
    Matrix.eval_charpoly]

/-- **Problem 9.2**, a leading block of order `k` contributes at most `k`
danger shifts, since its characteristic polynomial has degree `k`. -/
theorem higham9_2_charpolyDangerSet_card_le {k : ℕ}
    (B : Matrix (Fin k) (Fin k) ℝ) :
    (higham9_2_charpolyDangerSet B).card ≤ k := by
  unfold higham9_2_charpolyDangerSet
  calc
    B.charpoly.roots.toFinset.card ≤ B.charpoly.roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ B.charpoly.natDegree :=
      Polynomial.card_roots' B.charpoly
    _ = k := by
      simp

/-- **Problem 9.2**, characteristic-polynomial danger sets for all leading
block sizes below `n` have total cardinality at most `n(n-1)/2`. -/
theorem higham9_2_charpoly_danger_shift_count_bound
    (n : ℕ) (leadingBlock : (k : ℕ) → Matrix (Fin k) (Fin k) ℝ) :
    ((Finset.range n).biUnion fun k =>
      higham9_2_charpolyDangerSet (leadingBlock k)).card ≤ n * (n - 1) / 2 := by
  exact higham9_2_danger_shift_count_bound n
    (fun k => higham9_2_charpolyDangerSet (leadingBlock k))
    (fun k _ => higham9_2_charpolyDangerSet_card_le (leadingBlock k))

/-- **Problem 9.2**, the `k` by `k` leading principal block of a concrete
`n` by `n` source matrix.  The out-of-range branch is irrelevant for the source
union over `k < n`, but keeps the definition total as a function of `k`. -/
def higham9_2_leadingPrincipalBlock {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  if h : k ≤ n then
    fun i j => A ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩
  else
    0

/-- **Problem 9.2**, danger shifts contributed by the `k` by `k` leading
principal block of a source matrix. -/
noncomputable def higham9_2_leadingBlockDangerSet {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Finset ℝ :=
  higham9_2_charpolyDangerSet (higham9_2_leadingPrincipalBlock A k)

/-- **Problem 9.2**, the shifted `k` by `k` leading principal block
`sigma I - A(1:k,1:k)`. -/
def higham9_2_shiftedLeadingBlock {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (sigma : ℝ) (k : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.scalar (Fin k) sigma - higham9_2_leadingPrincipalBlock A k

/-- **Problem 9.2**, membership in a source leading-block danger set is exactly
singularity of the shifted leading principal block. -/
theorem higham9_2_mem_leadingBlockDangerSet_iff_det_shift_eq_zero {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (sigma : ℝ) :
    sigma ∈ higham9_2_leadingBlockDangerSet A k ↔
      (higham9_2_shiftedLeadingBlock A sigma k).det = 0 := by
  unfold higham9_2_shiftedLeadingBlock
  exact higham9_2_mem_charpolyDangerSet_iff_det_shift_eq_zero
    (higham9_2_leadingPrincipalBlock A k) sigma

/-- **Problem 9.2**, if a shift avoids the finite source danger union, then
each leading shifted block in the source range is nonsingular. -/
theorem higham9_2_shiftedLeadingBlock_det_ne_zero_of_not_mem_danger_union {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (sigma : ℝ)
    (hk : k ∈ Finset.range n)
    (hsigma :
      sigma ∉ (Finset.range n).biUnion fun r =>
        higham9_2_leadingBlockDangerSet A r) :
    (higham9_2_shiftedLeadingBlock A sigma k).det ≠ 0 := by
  intro hdet
  have hmemBlock :
      sigma ∈ higham9_2_leadingBlockDangerSet A k :=
    (higham9_2_mem_leadingBlockDangerSet_iff_det_shift_eq_zero A sigma).2 hdet
  exact hsigma (Finset.mem_biUnion.mpr ⟨k, hk, hmemBlock⟩)

/-- **Problem 9.2**, a concrete source leading block contributes at most `k`
danger shifts. -/
theorem higham9_2_leadingBlockDangerSet_card_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    (higham9_2_leadingBlockDangerSet A k).card ≤ k := by
  exact higham9_2_charpolyDangerSet_card_le
    (higham9_2_leadingPrincipalBlock A k)

/-- **Problem 9.2**, the source union of shifted leading-principal-block danger
values for a concrete `n` by `n` matrix has cardinality at most
`n(n-1)/2`. -/
theorem higham9_2_leadingBlockDangerSet_count_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ((Finset.range n).biUnion fun k =>
      higham9_2_leadingBlockDangerSet A k).card ≤ n * (n - 1) / 2 := by
  exact higham9_2_charpoly_danger_shift_count_bound n
    (fun k => higham9_2_leadingPrincipalBlock A k)

/-- **Problem 9.2**, the shifted source matrix `sigma I - A`.  The sign is
chosen to match the characteristic-polynomial danger sets above; replacing it
by `A - sigma I` has the same singularity exclusions up to a nonzero scalar
factor on each leading determinant. -/
def higham9_2_shiftedMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (sigma : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.scalar (Fin n) sigma - A

/-- **Problem 9.2**, the finite bad set of shifts appearing in Appendix A:
the union of danger shifts from all proper leading principal blocks. -/
noncomputable def higham9_2_shiftedMatrixDangerSet {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Finset ℝ :=
  (Finset.range n).biUnion fun k => higham9_2_leadingBlockDangerSet A k

/-- **Problem 9.2**, the shifted-matrix bad set has the source cardinality
bound `n(n-1)/2`. -/
theorem higham9_2_shiftedMatrixDangerSet_card_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (higham9_2_shiftedMatrixDangerSet A).card ≤ n * (n - 1) / 2 := by
  simpa [higham9_2_shiftedMatrixDangerSet] using
    higham9_2_leadingBlockDangerSet_count_bound A

/-! ## Appendix A, Problem 9.5 -/

/-- **Problem 9.5**, the source matrix `A = [[1, 1], [1, 0]]`. -/
def higham9_5_problemA : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = 1 ∧ j = 1 then 0 else 1

/-- **Problem 9.5**, unit lower-triangular factor
`L = [[1, 0], [1, 1]]`. -/
def higham9_5_problemL : Fin 2 → Fin 2 → ℝ :=
  fun i j => if j.val ≤ i.val then 1 else 0

/-- **Problem 9.5**, upper-triangular factor `U = [[1, 1], [0, -1]]`. -/
def higham9_5_problemU : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = 0 then 1 else if j = 1 then -1 else 0

/-- **Problem 9.5**, exact `LU = A` factorization for the displayed matrix. -/
theorem higham9_5_problem_lu_product :
    ∀ i j : Fin 2, ∑ k : Fin 2, higham9_5_problemL i k * higham9_5_problemU k j =
      higham9_5_problemA i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [higham9_5_problemA, higham9_5_problemL, higham9_5_problemU]

/-- **Problem 9.5**, the bottom-right entry of `|L||U|` is `2`. -/
theorem higham9_5_problem_abs_lu_bottom_right :
    (∑ k : Fin 2, |higham9_5_problemL (1 : Fin 2) k| *
      |higham9_5_problemU k (1 : Fin 2)|) = 2 := by
  norm_num [higham9_5_problemL, higham9_5_problemU]

/-- **Problem 9.5**, no scalar multiple of `|A|` componentwise bounds
`|L||U|` for the displayed factorization. -/
theorem higham9_5_problem_no_componentwise_bound :
    ¬ ∃ c : ℝ, ∀ i j : Fin 2,
        ∑ k : Fin 2, |higham9_5_problemL i k| * |higham9_5_problemU k j| ≤
          c * |higham9_5_problemA i j| := by
  rintro ⟨c, hc⟩
  have h := hc (1 : Fin 2) (1 : Fin 2)
  norm_num [higham9_5_problemA, higham9_5_problemL, higham9_5_problemU] at h

/-! ## Appendix A, Problem 9.6 -/

/-- **Problem 9.6**, the source `2 by 2` submatrix on rows `i₁,i₂` and
columns `j₁,j₂`.  The intended use is with strictly increasing row and column
indices, as in the total-nonnegativity determinant condition. -/
def higham9_6_twoByTwoSubmatrix {n : ℕ} (A : Fin n → Fin n → ℝ)
    (i₁ i₂ j₁ j₂ : Fin n) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun r c =>
    if r = 0 then
      if c = 0 then A i₁ j₁ else A i₁ j₂
    else
      if c = 0 then A i₂ j₁ else A i₂ j₂

/-- **Problem 9.6**, first no-pivot Schur-complement update at pivot `p`. -/
noncomputable def higham9_6_firstSchurUpdate {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p i j : Fin n) : ℝ :=
  A i j - (A i p / A p p) * A p j

/-- **Problem 9.6**, the `3 by 3` source submatrix on rows `p,i₁,i₂` and
columns `p,j₁,j₂`, used to prove the first Schur update preserves `2 by 2`
minor nonnegativity. -/
def higham9_6_threeByThreeSubmatrix {n : ℕ} (A : Fin n → Fin n → ℝ)
    (p i₁ i₂ j₁ j₂ : Fin n) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun r c =>
    if r = 0 then
      if c = 0 then A p p else if c = 1 then A p j₁ else A p j₂
    else if r = 1 then
      if c = 0 then A i₁ p else if c = 1 then A i₁ j₁ else A i₁ j₂
    else
      if c = 0 then A i₂ p else if c = 1 then A i₂ j₁ else A i₂ j₂

/-- **Problem 9.6**, source-level total nonnegativity: every square minor
formed from strictly increasing row and column selections has nonnegative
determinant.  This is the source assumption used by the Appendix A argument;
the later Problem 9.6 theorems use it for the recursive nonnegative LU
construction and no-growth endpoints. -/
def higham9_6_IsTotallyNonnegative {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ k : ℕ, ∀ rows cols : Fin k → Fin n,
    StrictMono (fun r : Fin k => (rows r).val) →
    StrictMono (fun c : Fin k => (cols c).val) →
    0 ≤ Matrix.det (fun r c : Fin k => A (rows r) (cols c))

/-- **Problem 9.6**, the trailing principal block `A(p:n,p:n)` in zero-based
Lean indexing, corresponding to the source `A(p+1:n,p+1:n)` for a leading
block of size `p`. -/
def higham9_6_trailingPrincipalBlock {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) :
    Matrix (Fin (n - p)) (Fin (n - p)) ℝ :=
  if hp : p ≤ n then
    fun i j =>
      A ⟨p + i.val, by omega⟩ ⟨p + j.val, by omega⟩
  else
    0

/-- **Problem 9.6**, total nonnegativity is inherited by strictly ordered
square submatrices.  This is a local structural dependency for the recursive
total-nonnegative elimination argument. -/
theorem higham9_6_totalNonnegative_submatrix {n m : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {rows cols : Fin m → Fin n}
    (hrows : StrictMono (fun r : Fin m => (rows r).val))
    (hcols : StrictMono (fun c : Fin m => (cols c).val)) :
    higham9_6_IsTotallyNonnegative
      (fun i j : Fin m => A (rows i) (cols j)) := by
  intro k subRows subCols hsubRows hsubCols
  exact hTN k (fun r => rows (subRows r)) (fun c => cols (subCols c))
    (hrows.comp hsubRows) (hcols.comp hsubCols)

/-- **Problem 9.6**, total nonnegativity gives nonnegativity of every leading
principal-block determinant. -/
theorem higham9_6_totalNonnegative_leadingPrincipalBlock_det_nonneg {n p : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hp : p ≤ n) :
    0 ≤ Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) := by
  let rows : Fin p → Fin n := fun i =>
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt hp⟩
  have hrows : StrictMono (fun i : Fin p => (rows i).val) := by
    intro i j hij
    simpa [rows] using hij
  have h := hTN p rows rows hrows hrows
  simpa [higham9_2_leadingPrincipalBlock, hp, rows] using h

/-- **Problem 9.6**, total nonnegativity gives nonnegativity of every trailing
principal-block determinant. -/
theorem higham9_6_totalNonnegative_trailingPrincipalBlock_det_nonneg {n p : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hp : p ≤ n) :
    0 ≤ Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p) := by
  let rows : Fin (n - p) → Fin n := fun i =>
    ⟨p + i.val, by omega⟩
  have hrows : StrictMono (fun i : Fin (n - p) => (rows i).val) := by
    intro i j hij
    simp [rows]
    omega
  have h := hTN (n - p) rows rows hrows hrows
  simpa [higham9_6_trailingPrincipalBlock, hp, rows] using h

/-- **Problem 9.6**, total nonnegativity gives nonnegativity of the full
determinant. -/
theorem higham9_6_totalNonnegative_det_nonneg {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A) :
    0 ≤ Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
  let rows : Fin n → Fin n := fun i => i
  have hrows : StrictMono (fun i : Fin n => (rows i).val) := by
    intro i j hij
    simpa [rows] using hij
  have h := hTN n rows rows hrows hrows
  simpa [rows] using h

/-- **Problem 9.6**, a nonsingular totally nonnegative matrix has positive
determinant.  This adapts the source hypothesis "A is nonsingular" to the
positive determinant form used by the downstream determinant-inequality route. -/
theorem higham9_6_totalNonnegative_det_pos_of_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    0 < Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) :=
  lt_of_le_of_ne (higham9_6_totalNonnegative_det_nonneg hTN) (Ne.symm hdetA)

/-- **Problem 9.6**, the singular branch of the source-cited
principal-block determinant inequality.  If `det A = 0`, total
nonnegativity of the leading and trailing principal blocks already gives
`det A <= det A(1:p,1:p) * det A(p+1:n,p+1:n)`.  The remaining
Koteljanskii/Fischer bottleneck is the nonsingular case. -/
theorem higham9_6_principalBlock_determinantal_inequality_of_det_eq_zero
    {n p : ℕ} {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hp : p ≤ n)
    (hdetA :
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) = 0) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) *
        Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p) := by
  have hlead_nonneg :
      0 ≤ Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) :=
    higham9_6_totalNonnegative_leadingPrincipalBlock_det_nonneg hTN hp
  have htrail_nonneg :
      0 ≤ Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p) :=
    higham9_6_totalNonnegative_trailingPrincipalBlock_det_nonneg hTN hp
  rw [hdetA]
  exact mul_nonneg hlead_nonneg htrail_nonneg

/-- **Problem 9.6**, the `p = 0` boundary case of the source-cited
principal-block determinant inequality.  The leading empty determinant is
`1`, and the trailing block is the whole matrix. -/
theorem higham9_6_principalBlock_determinantal_inequality_zero
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) 0) *
        Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 0) := by
  simp [higham9_2_leadingPrincipalBlock, higham9_6_trailingPrincipalBlock]
  change Matrix.det (fun i j : Fin n => A i j) ≤ Matrix.det (fun i j : Fin n => A i j)
  exact le_rfl

/-- **Problem 9.6**, the `p = n` boundary case of the source-cited
principal-block determinant inequality.  The leading block is the whole
matrix, and the trailing empty determinant is `1`. -/
theorem higham9_6_principalBlock_determinantal_inequality_full
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) n) *
        Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) n) := by
  simp [higham9_2_leadingPrincipalBlock, higham9_6_trailingPrincipalBlock]
  have htrail :
      Matrix.det (fun i j : Fin (n - n) => A ⟨n + ↑i, by omega⟩ ⟨n + ↑j, by omega⟩) =
        1 := by
    haveI : IsEmpty (Fin (n - n)) := by
      rw [Nat.sub_self]
      infer_instance
    exact Matrix.det_isEmpty
  rw [htrail, mul_one]
  change Matrix.det (fun i j : Fin n => A i j) ≤ Matrix.det (fun i j : Fin n => A i j)
  exact le_rfl

/-- **Problem 9.6**, appendix determinant-inequality step.  Once the
source-cited inequality
`det A <= det A(1:p,1:p) * det A(p+1:n,p+1:n)` is supplied, total
nonnegativity and nonsingularity force both displayed principal determinants
to be positive.  The cited total-positivity determinant inequality itself is
not hidden in this theorem. -/
theorem higham9_6_principalBlock_dets_pos_of_determinantal_inequality
    {n p : ℕ} {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hp : p ≤ n)
    (hdetA_pos : 0 < Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))
    (hineq :
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
        Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) *
          Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p)) :
    0 < Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) ∧
      0 < Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p) := by
  have hlead_nonneg :
      0 ≤ Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) :=
    higham9_6_totalNonnegative_leadingPrincipalBlock_det_nonneg hTN hp
  have htrail_nonneg :
      0 ≤ Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p) :=
    higham9_6_totalNonnegative_trailingPrincipalBlock_det_nonneg hTN hp
  have hprod_pos :
      0 < Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) *
        Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p) :=
    lt_of_lt_of_le hdetA_pos hineq
  have hlead_pos :
      0 < Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) := by
    by_contra hnot
    have hlead_nonpos :
        Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) ≤ 0 :=
      le_of_not_gt hnot
    have hprod_nonpos :
        Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) *
            Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hlead_nonpos htrail_nonneg
    linarith
  have htrail_pos :
      0 < Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p) := by
    by_contra hnot
    have htrail_nonpos :
        Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p) ≤ 0 :=
      le_of_not_gt hnot
    have hprod_nonpos :
        Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) *
            Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hlead_nonneg htrail_nonpos
    linarith
  exact ⟨hlead_pos, htrail_pos⟩

/-- **Problem 9.6**, leading-principal determinant positivity extracted from
the appendix determinant-inequality step. -/
theorem higham9_6_leadingPrincipalBlock_det_pos_of_determinantal_inequality
    {n p : ℕ} {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hp : p ≤ n)
    (hdetA_pos : 0 < Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))
    (hineq :
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
        Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) *
          Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p)) :
    0 < Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) :=
  (higham9_6_principalBlock_dets_pos_of_determinantal_inequality
    hTN hp hdetA_pos hineq).1

/-- **Problem 9.6**, order-two total nonnegativity support: nonnegative
entries and nonnegative `2 by 2` minors for strictly increasing row/column
pairs.  This is only the local determinant infrastructure used by the appendix
argument, not the final source-level determinant-inequality theorem. -/
def higham9_6_IsTotallyNonnegativeOrderTwo {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, 0 ≤ A i j) ∧
  (∀ i₁ i₂ j₁ j₂ : Fin n, i₁.val < i₂.val → j₁.val < j₂.val →
    0 ≤ Matrix.det (higham9_6_twoByTwoSubmatrix A i₁ i₂ j₁ j₂))

/-- **Problem 9.6**, a source-level totally nonnegative matrix has
nonnegative entries, by applying total nonnegativity to `1 by 1` minors. -/
theorem higham9_6_totalNonnegative_entry_nonneg {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A) :
    ∀ i j : Fin n, 0 ≤ A i j := by
  intro i j
  let rows : Fin 1 → Fin n := fun _ => i
  let cols : Fin 1 → Fin n := fun _ => j
  have hrow : StrictMono (fun r : Fin 1 => (rows r).val) := by
    intro a b hab
    omega
  have hcol : StrictMono (fun c : Fin 1 => (cols c).val) := by
    intro a b hab
    omega
  have h := hTN 1 rows cols hrow hcol
  rw [Matrix.det_fin_one] at h
  simpa [rows, cols] using h

/-- **Problem 9.6**, the `2 by 2` base case of the source-cited
Koteljanskii/Fischer principal-block determinant inequality.  For a totally
nonnegative `2 by 2` matrix the source inequality at `p = 1`,
`det A <= det A(1:1,1:1) * det A(2:2,2:2)`, follows directly from
nonnegativity of the off-diagonal entries. -/
theorem higham9_6_principalBlock_determinantal_inequality_fin_two
    {A : Fin 2 → Fin 2 → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A) :
    Matrix.det (Matrix.of A : Matrix (Fin 2) (Fin 2) ℝ) ≤
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) 1) *
        Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 1) := by
  have h01 : 0 ≤ A 0 1 :=
    higham9_6_totalNonnegative_entry_nonneg hTN 0 1
  have h10 : 0 ≤ A 1 0 :=
    higham9_6_totalNonnegative_entry_nonneg hTN 1 0
  have hprod : 0 ≤ A 0 1 * A 1 0 := mul_nonneg h01 h10
  have hlead :
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) 1) =
        A 0 0 := by
    rw [Matrix.det_fin_one]
    simp [higham9_2_leadingPrincipalBlock]
  have htrail :
      Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 1) =
        A 1 1 := by
    rw [Matrix.det_fin_one]
    simp [higham9_6_trailingPrincipalBlock]
  rw [Matrix.det_fin_two, hlead, htrail]
  change A 0 0 * A 1 1 - A 0 1 * A 1 0 ≤ A 0 0 * A 1 1
  nlinarith

/-- **Problem 9.6**, a source-level totally nonnegative matrix has all
nonnegative `2 by 2` minors used by the first Schur-complement step. -/
theorem higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {i₁ i₂ j₁ j₂ : Fin n}
    (hi : i₁.val < i₂.val) (hj : j₁.val < j₂.val) :
    0 ≤ Matrix.det (higham9_6_twoByTwoSubmatrix A i₁ i₂ j₁ j₂) := by
  let rows : Fin 2 → Fin n := fun r => if r = 0 then i₁ else i₂
  let cols : Fin 2 → Fin n := fun c => if c = 0 then j₁ else j₂
  have hrow : StrictMono (fun r : Fin 2 => (rows r).val) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [rows] at hab ⊢
    exact hi
  have hcol : StrictMono (fun c : Fin 2 => (cols c).val) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [cols] at hab ⊢
    exact hj
  have h := hTN 2 rows cols hrow hcol
  convert h using 1

/-- **Problem 9.6**, in the `3 by 3` case a totally nonnegative matrix with
positive determinant has a positive middle diagonal entry.  This is the local
side-condition needed by the adjacent Sylvester/condensation proof of the
`p = 1` principal-block determinant inequality. -/
theorem higham9_6_middle_entry_pos_of_fin_three_totalNonnegative_det_pos
    {A : Fin 3 → Fin 3 → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdet_pos :
      0 < Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ)) :
    0 < A 1 1 := by
  have h11nonneg : 0 ≤ A 1 1 :=
    higham9_6_totalNonnegative_entry_nonneg hTN 1 1
  by_contra hnot
  have h11le : A 1 1 ≤ 0 := le_of_not_gt hnot
  have h11eq : A 1 1 = 0 := le_antisymm h11le h11nonneg
  have h00 : 0 ≤ A 0 0 :=
    higham9_6_totalNonnegative_entry_nonneg hTN 0 0
  have h01 : 0 ≤ A 0 1 :=
    higham9_6_totalNonnegative_entry_nonneg hTN 0 1
  have h10 : 0 ≤ A 1 0 :=
    higham9_6_totalNonnegative_entry_nonneg hTN 1 0
  have h12 : 0 ≤ A 1 2 :=
    higham9_6_totalNonnegative_entry_nonneg hTN 1 2
  have h21 : 0 ≤ A 2 1 :=
    higham9_6_totalNonnegative_entry_nonneg hTN 2 1
  have h01_10 : 0 ≤ A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
    have h := higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg
      (A := A) hTN (i₁ := 0) (i₂ := 1) (j₁ := 0) (j₂ := 1)
      (by norm_num) (by norm_num)
    simpa [higham9_6_twoByTwoSubmatrix, Matrix.det_fin_two] using h
  have h12_21 : 0 ≤ A 1 1 * A 2 2 - A 1 2 * A 2 1 := by
    have h := higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg
      (A := A) hTN (i₁ := 1) (i₂ := 2) (j₁ := 1) (j₂ := 2)
      (by norm_num) (by norm_num)
    simpa [higham9_6_twoByTwoSubmatrix, Matrix.det_fin_two] using h
  have h01_20 : 0 ≤ A 0 0 * A 2 1 - A 0 1 * A 2 0 := by
    have h := higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg
      (A := A) hTN (i₁ := 0) (i₂ := 2) (j₁ := 0) (j₂ := 1)
      (by norm_num) (by norm_num)
    simpa [higham9_6_twoByTwoSubmatrix, Matrix.det_fin_two] using h
  have h00_12 : 0 ≤ A 0 0 * A 1 2 - A 0 2 * A 1 0 := by
    have h := higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg
      (A := A) hTN (i₁ := 0) (i₂ := 1) (j₁ := 0) (j₂ := 2)
      (by norm_num) (by norm_num)
    simpa [higham9_6_twoByTwoSubmatrix, Matrix.det_fin_two] using h
  have h01_10_zero : A 0 1 * A 1 0 = 0 := by
    apply le_antisymm
    · have hminor := h01_10
      rw [h11eq, mul_zero, zero_sub] at hminor
      nlinarith
    · exact mul_nonneg h01 h10
  have h12_21_zero : A 1 2 * A 2 1 = 0 := by
    apply le_antisymm
    · have hminor := h12_21
      rw [h11eq, zero_mul, zero_sub] at hminor
      nlinarith
    · exact mul_nonneg h12 h21
  have hterm1 : A 0 1 * A 1 2 * A 2 0 ≤ 0 := by
    have hle : A 0 1 * A 2 0 ≤ A 0 0 * A 2 1 := by
      nlinarith [h01_20]
    have hmul := mul_le_mul_of_nonneg_right hle h12
    calc
      A 0 1 * A 1 2 * A 2 0 = (A 0 1 * A 2 0) * A 1 2 := by ring
      _ ≤ (A 0 0 * A 2 1) * A 1 2 := hmul
      _ = A 0 0 * (A 1 2 * A 2 1) := by ring
      _ = 0 := by rw [h12_21_zero, mul_zero]
  have hterm2 : A 0 2 * A 1 0 * A 2 1 ≤ 0 := by
    have hle : A 0 2 * A 1 0 ≤ A 0 0 * A 1 2 := by
      nlinarith [h00_12]
    have hmul := mul_le_mul_of_nonneg_right hle h21
    calc
      A 0 2 * A 1 0 * A 2 1 = (A 0 2 * A 1 0) * A 2 1 := by ring
      _ ≤ (A 0 0 * A 1 2) * A 2 1 := hmul
      _ = A 0 0 * (A 1 2 * A 2 1) := by ring
      _ = 0 := by rw [h12_21_zero, mul_zero]
  have hneg1 : A 0 0 * A 1 2 * A 2 1 = 0 := by
    calc
      A 0 0 * A 1 2 * A 2 1 = A 0 0 * (A 1 2 * A 2 1) := by ring
      _ = 0 := by rw [h12_21_zero, mul_zero]
  have hneg2 : A 0 1 * A 1 0 * A 2 2 = 0 := by
    calc
      A 0 1 * A 1 0 * A 2 2 = (A 0 1 * A 1 0) * A 2 2 := by ring
      _ = 0 := by rw [h01_10_zero, zero_mul]
  have hmid1 : A 0 0 * A 1 1 * A 2 2 = 0 := by
    calc
      A 0 0 * A 1 1 * A 2 2 = (A 0 0 * A 2 2) * A 1 1 := by ring
      _ = 0 := by rw [h11eq, mul_zero]
  have hmid2 : A 0 2 * A 1 1 * A 2 0 = 0 := by
    calc
      A 0 2 * A 1 1 * A 2 0 = (A 0 2 * A 2 0) * A 1 1 := by ring
      _ = 0 := by rw [h11eq, mul_zero]
  have hdet_nonpos :
      Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) ≤ 0 := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply]
    nlinarith [hmid1, hmid2, hneg1, hneg2, hterm1, hterm2]
  linarith

/-- **Problem 9.6**, conditional `3 by 3`, `p = 1`
Koteljanskii/Fischer principal-block determinant inequality.  The proof uses
the adjacent Sylvester condensation identity together with total
nonnegativity of the relevant `2 by 2` minors. -/
theorem higham9_6_principalBlock_determinantal_inequality_fin_three_one_of_middle_pos
    {A : Fin 3 → Fin 3 → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hmid : 0 < A 1 1) :
    Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) ≤
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) 1) *
        Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 1) := by
  have h23minor : 0 ≤ A 1 1 * A 2 2 - A 1 2 * A 2 1 := by
    have h := higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg
      (A := A) hTN (i₁ := 1) (i₂ := 2) (j₁ := 1) (j₂ := 2)
      (by norm_num) (by norm_num)
    simpa [higham9_6_twoByTwoSubmatrix, Matrix.det_fin_two] using h
  have hrows12cols01 : 0 ≤ A 1 0 * A 2 1 - A 1 1 * A 2 0 := by
    have h := higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg
      (A := A) hTN (i₁ := 1) (i₂ := 2) (j₁ := 0) (j₂ := 1)
      (by norm_num) (by norm_num)
    simpa [higham9_6_twoByTwoSubmatrix, Matrix.det_fin_two] using h
  have hrows01cols12 : 0 ≤ A 0 1 * A 1 2 - A 0 2 * A 1 1 := by
    have h := higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg
      (A := A) hTN (i₁ := 0) (i₂ := 1) (j₁ := 1) (j₂ := 2)
      (by norm_num) (by norm_num)
    simpa [higham9_6_twoByTwoSubmatrix, Matrix.det_fin_two] using h
  have hcondense_nonneg :
      0 ≤ (A 1 0 * A 2 1 - A 1 1 * A 2 0) *
          (A 0 1 * A 1 2 - A 0 2 * A 1 1) :=
    mul_nonneg hrows12cols01 hrows01cols12
  have hcondense :
      Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) * A 1 1 ≤
        (A 0 0 * A 1 1 - A 0 1 * A 1 0) *
          (A 1 1 * A 2 2 - A 1 2 * A 2 1) := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply]
    nlinarith [hcondense_nonneg]
  have hbase : A 0 0 * A 1 1 - A 0 1 * A 1 0 ≤ A 0 0 * A 1 1 := by
    have h01 : 0 ≤ A 0 1 :=
      higham9_6_totalNonnegative_entry_nonneg hTN 0 1
    have h10 : 0 ≤ A 1 0 :=
      higham9_6_totalNonnegative_entry_nonneg hTN 1 0
    have hprod : 0 ≤ A 0 1 * A 1 0 := mul_nonneg h01 h10
    nlinarith
  have hscaled :
      Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) * A 1 1 ≤
        (A 0 0 * A 1 1) * (A 1 1 * A 2 2 - A 1 2 * A 2 1) := by
    have hmul := mul_le_mul_of_nonneg_right hbase h23minor
    nlinarith
  have hlead :
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) 1) =
        A 0 0 := by
    rw [Matrix.det_fin_one]
    simp [higham9_2_leadingPrincipalBlock]
  have htrail :
      Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 1) =
        A 1 1 * A 2 2 - A 1 2 * A 2 1 := by
    simp [higham9_6_trailingPrincipalBlock, Matrix.det_fin_two]
  rw [hlead, htrail]
  nlinarith [hscaled, hmid]

/-- **Problem 9.6**, the `3 by 3`, `p = 1` case of the source-cited
Koteljanskii/Fischer principal-block determinant inequality.  This closes the
first nontrivial nonsingular case in addition to the singular, boundary, and
`2 by 2` cases. -/
theorem higham9_6_principalBlock_determinantal_inequality_fin_three_one
    {A : Fin 3 → Fin 3 → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A) :
    Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) ≤
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) 1) *
        Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 1) := by
  by_cases hdet :
      Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) = 0
  · exact higham9_6_principalBlock_determinantal_inequality_of_det_eq_zero
      hTN (by norm_num) hdet
  · have hdet_pos :
        0 < Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) :=
      higham9_6_totalNonnegative_det_pos_of_det_ne_zero hTN hdet
    exact
      higham9_6_principalBlock_determinantal_inequality_fin_three_one_of_middle_pos
        hTN
        (higham9_6_middle_entry_pos_of_fin_three_totalNonnegative_det_pos
          hTN hdet_pos)

/-- **Problem 9.6**, conditional `3 by 3`, `p = 2`
Koteljanskii/Fischer principal-block determinant inequality.  This is the
right-hand analogue of
`higham9_6_principalBlock_determinantal_inequality_fin_three_one_of_middle_pos`;
the proof uses the same Sylvester condensation identity and total
nonnegativity of the adjacent `2 by 2` minors. -/
theorem higham9_6_principalBlock_determinantal_inequality_fin_three_two_of_middle_pos
    {A : Fin 3 → Fin 3 → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hmid : 0 < A 1 1) :
    Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) ≤
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) 2) *
        Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 2) := by
  have hlead_nonneg : 0 ≤ A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
    have h := higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg
      (A := A) hTN (i₁ := 0) (i₂ := 1) (j₁ := 0) (j₂ := 1)
      (by norm_num) (by norm_num)
    simpa [higham9_6_twoByTwoSubmatrix, Matrix.det_fin_two] using h
  have hbottom2 : A 1 1 * A 2 2 - A 1 2 * A 2 1 ≤ A 1 1 * A 2 2 := by
    have h12 : 0 ≤ A 1 2 :=
      higham9_6_totalNonnegative_entry_nonneg hTN 1 2
    have h21 : 0 ≤ A 2 1 :=
      higham9_6_totalNonnegative_entry_nonneg hTN 2 1
    have hprod : 0 ≤ A 1 2 * A 2 1 := mul_nonneg h12 h21
    nlinarith
  have hrows12cols01 : 0 ≤ A 1 0 * A 2 1 - A 1 1 * A 2 0 := by
    have h := higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg
      (A := A) hTN (i₁ := 1) (i₂ := 2) (j₁ := 0) (j₂ := 1)
      (by norm_num) (by norm_num)
    simpa [higham9_6_twoByTwoSubmatrix, Matrix.det_fin_two] using h
  have hrows01cols12 : 0 ≤ A 0 1 * A 1 2 - A 0 2 * A 1 1 := by
    have h := higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg
      (A := A) hTN (i₁ := 0) (i₂ := 1) (j₁ := 1) (j₂ := 2)
      (by norm_num) (by norm_num)
    simpa [higham9_6_twoByTwoSubmatrix, Matrix.det_fin_two] using h
  have hcondense_nonneg :
      0 ≤ (A 1 0 * A 2 1 - A 1 1 * A 2 0) *
          (A 0 1 * A 1 2 - A 0 2 * A 1 1) :=
    mul_nonneg hrows12cols01 hrows01cols12
  have hcondense :
      Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) * A 1 1 ≤
        (A 0 0 * A 1 1 - A 0 1 * A 1 0) *
          (A 1 1 * A 2 2 - A 1 2 * A 2 1) := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply]
    nlinarith [hcondense_nonneg]
  have hscaled :
      Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) * A 1 1 ≤
        (A 0 0 * A 1 1 - A 0 1 * A 1 0) * (A 1 1 * A 2 2) := by
    exact le_trans hcondense
      (mul_le_mul_of_nonneg_left hbottom2 hlead_nonneg)
  have hlead :
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) 2) =
        A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
    simp [higham9_2_leadingPrincipalBlock, Matrix.det_fin_two]
  have htrail :
      Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 2) =
        A 2 2 := by
    rw [Matrix.det_fin_one]
    simp [higham9_6_trailingPrincipalBlock]
  rw [hlead, htrail]
  nlinarith [hscaled, hmid]

/-- **Problem 9.6**, the `3 by 3`, `p = 2` case of the source-cited
Koteljanskii/Fischer principal-block determinant inequality.  Together with
the `p = 1` theorem and boundary cases, this closes every principal split of a
`3 by 3` totally nonnegative matrix. -/
theorem higham9_6_principalBlock_determinantal_inequality_fin_three_two
    {A : Fin 3 → Fin 3 → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A) :
    Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) ≤
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) 2) *
        Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 2) := by
  by_cases hdet :
      Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) = 0
  · exact higham9_6_principalBlock_determinantal_inequality_of_det_eq_zero
      hTN (by norm_num) hdet
  · have hdet_pos :
        0 < Matrix.det (Matrix.of A : Matrix (Fin 3) (Fin 3) ℝ) :=
      higham9_6_totalNonnegative_det_pos_of_det_ne_zero hTN hdet
    exact
      higham9_6_principalBlock_determinantal_inequality_fin_three_two_of_middle_pos
        hTN
        (higham9_6_middle_entry_pos_of_fin_three_totalNonnegative_det_pos
          hTN hdet_pos)

/-- **Problem 9.6**, source-level total nonnegativity supplies the order-two
support predicate consumed by the existing first-step Schur-update lemmas. -/
theorem higham9_6_totalNonnegative_to_orderTwo {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A) :
    higham9_6_IsTotallyNonnegativeOrderTwo A :=
  ⟨higham9_6_totalNonnegative_entry_nonneg hTN,
    fun _ _ _ _ hi hj =>
      higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg hTN hi hj⟩

/-- **Problem 9.6**, determinant of the selected `2 by 2` submatrix. -/
theorem higham9_6_twoByTwoSubmatrix_det {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i₁ i₂ j₁ j₂ : Fin n) :
    Matrix.det (higham9_6_twoByTwoSubmatrix A i₁ i₂ j₁ j₂) =
      A i₁ j₁ * A i₂ j₂ - A i₁ j₂ * A i₂ j₁ := by
  rw [Matrix.det_fin_two]
  norm_num [higham9_6_twoByTwoSubmatrix]

/-- **Problem 9.6**, first-pivot positivity without the external determinant
inequality.  If the top-left entry of a totally nonnegative nonsingular matrix
were zero, then either the first row is zero or a nonzero first-row entry and
the `2 by 2` total-nonnegativity inequalities force the first column to be
zero; either case contradicts nonsingularity. -/
theorem higham9_6_topLeft_pos_of_totalNonnegative_det_ne_zero {n : ℕ}
    {A : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : Matrix.det
      (Matrix.of A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) ≠ 0) :
    0 < A 0 0 := by
  classical
  have h00_nonneg : 0 ≤ A 0 0 :=
    higham9_6_totalNonnegative_entry_nonneg hTN 0 0
  rcases lt_or_eq_of_le h00_nonneg with hpos | hzero
  · exact hpos
  exfalso
  apply hdetA
  have hA00 : A 0 0 = 0 := hzero.symm
  by_cases hrow_zero : ∀ j : Fin (n + 1), A 0 j = 0
  · exact Matrix.det_eq_zero_of_row_eq_zero (A := Matrix.of A) (0 : Fin (n + 1))
      (by intro j; simpa using hrow_zero j)
  · push_neg at hrow_zero
    obtain ⟨j, hj_nonzero⟩ := hrow_zero
    have hj_ne_zero : j ≠ 0 := by
      intro hj
      subst j
      exact hj_nonzero hA00
    have hj_pos : (0 : Fin (n + 1)).val < j.val := by
      simp
      exact Nat.pos_of_ne_zero (by
        intro hjval
        exact hj_ne_zero (Fin.ext hjval))
    have h0j_nonneg : 0 ≤ A 0 j :=
      higham9_6_totalNonnegative_entry_nonneg hTN 0 j
    have h0j_pos : 0 < A 0 j :=
      lt_of_le_of_ne h0j_nonneg (Ne.symm hj_nonzero)
    have hcol_zero : ∀ i : Fin (n + 1), A i 0 = 0 := by
      intro i
      by_cases hi0 : i = 0
      · subst i
        exact hA00
      · have hi_pos : (0 : Fin (n + 1)).val < i.val := by
          simp
          exact Nat.pos_of_ne_zero (by
            intro hival
            exact hi0 (Fin.ext hival))
        have hminor :
            0 ≤ Matrix.det
              (higham9_6_twoByTwoSubmatrix A (0 : Fin (n + 1)) i 0 j) :=
          higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg hTN
            hi_pos hj_pos
        rw [higham9_6_twoByTwoSubmatrix_det] at hminor
        rw [hA00, zero_mul, zero_sub] at hminor
        have hi0_nonneg : 0 ≤ A i 0 :=
          higham9_6_totalNonnegative_entry_nonneg hTN i 0
        have hprod_nonneg : 0 ≤ A 0 j * A i 0 :=
          mul_nonneg (le_of_lt h0j_pos) hi0_nonneg
        have hprod_nonpos : A 0 j * A i 0 ≤ 0 := by
          nlinarith [hminor]
        have hprod_zero : A 0 j * A i 0 = 0 :=
          le_antisymm hprod_nonpos hprod_nonneg
        exact (eq_zero_or_eq_zero_of_mul_eq_zero hprod_zero).resolve_left
          (ne_of_gt h0j_pos)
    exact Matrix.det_eq_zero_of_column_eq_zero (A := Matrix.of A) (0 : Fin (n + 1))
      (by intro i; simpa using hcol_zero i)

/-- **Problem 9.6**, denominator-cleared Sylvester identity for the first
Schur update: the pivot times the updated `2 by 2` minor equals the
corresponding `3 by 3` source minor. -/
theorem higham9_6_pivot_mul_schur_twoByTwo_det_eq_threeByThree_det {n : ℕ}
    (A : Fin n → Fin n → ℝ) {p i₁ i₂ j₁ j₂ : Fin n}
    (hpivot : A p p ≠ 0) :
    A p p *
        Matrix.det (higham9_6_twoByTwoSubmatrix
          (fun i j => higham9_6_firstSchurUpdate A p i j) i₁ i₂ j₁ j₂) =
      Matrix.det (higham9_6_threeByThreeSubmatrix A p i₁ i₂ j₁ j₂) := by
  rw [higham9_6_twoByTwoSubmatrix_det, Matrix.det_fin_three]
  simp [higham9_6_firstSchurUpdate, higham9_6_threeByThreeSubmatrix]
  field_simp [hpivot]
  ring

/-- **Problem 9.6**, general denominator-cleared Schur determinant identity
for a first pivot.  The pivot times any square minor of the first Schur update
equals the corresponding source minor with the pivot row and column prepended.
This is the arbitrary-size version of the local Sylvester identity used by the
recursive total-nonnegative elimination argument. -/
theorem higham9_6_pivot_mul_schur_det_eq_source_minor {n k : ℕ}
    (A : Fin n → Fin n → ℝ) {p : Fin n}
    (rows cols : Fin k → Fin n) (hpivot : A p p ≠ 0) :
    A p p *
        Matrix.det
          (fun r c : Fin k => higham9_6_firstSchurUpdate A p (rows r) (cols c)) =
      Matrix.det
        (fun r c : Fin (1 + k) =>
          A
            (Fin.addCases (fun _ : Fin 1 => p) rows r)
            (Fin.addCases (fun _ : Fin 1 => p) cols c)) := by
  let A11 : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => A p p
  let B : Matrix (Fin 1) (Fin k) ℝ := fun _ c => A p (cols c)
  let C : Matrix (Fin k) (Fin 1) ℝ := fun r _ => A (rows r) p
  let D : Matrix (Fin k) (Fin k) ℝ := fun r c => A (rows r) (cols c)
  have hdetA11 : Matrix.det A11 = A p p := by
    simp [A11]
  have hdetA11_ne : Matrix.det A11 ≠ 0 := by
    simpa [hdetA11] using hpivot
  letI : Invertible (Matrix.det A11) := invertibleOfNonzero hdetA11_ne
  letI : Invertible A11 := Matrix.invertibleOfDetInvertible A11
  have hA11_inv : ⅟A11 = (fun _ _ : Fin 1 => (A p p)⁻¹) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [A11]
  have hschur :
      Matrix.det (Matrix.fromBlocks A11 B C D) =
        A p p *
          Matrix.det
            (fun r c : Fin k =>
              higham9_6_firstSchurUpdate A p (rows r) (cols c)) := by
    rw [Matrix.det_fromBlocks₁₁, hdetA11]
    congr 1
    apply congrArg Matrix.det
    ext r c
    simp [A11, B, C, D, hA11_inv, higham9_6_firstSchurUpdate, Matrix.mul_apply]
    rw [div_eq_mul_inv]
    ring_nf
    simp
  rw [← hschur]
  have hdetBlock :
      Matrix.det (Matrix.fromBlocks A11 B C D) =
        Matrix.det ((Matrix.fromBlocks A11 B C D).submatrix
          (finSumFinEquiv.symm : Fin (1 + k) ≃ Fin 1 ⊕ Fin k)
          (finSumFinEquiv.symm : Fin (1 + k) ≃ Fin 1 ⊕ Fin k)) :=
    (Matrix.det_submatrix_equiv_self
      (finSumFinEquiv.symm : Fin (1 + k) ≃ Fin 1 ⊕ Fin k)
      (Matrix.fromBlocks A11 B C D)).symm
  rw [hdetBlock]
  apply congrArg Matrix.det
  ext r c
  cases r using Fin.addCases <;> cases c using Fin.addCases <;> simp [A11, B, C, D]

/-- **Problem 9.6**, leading-principal-block form of the first Schur
determinant identity.  The first pivot times the `k` by `k` leading principal
determinant of the first Schur complement is the `(1+k)` by `(1+k)` leading
principal determinant of the source matrix. -/
theorem higham9_6_pivot_mul_firstSchur_leadingPrincipalBlock_det_eq
    {m k : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hk : k ≤ m) (hpivot : A 0 0 ≠ 0) :
    A 0 0 *
        Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of (higham9_1_firstSchurComplement A) :
              Matrix (Fin m) (Fin m) ℝ) k) =
      Matrix.det
        (higham9_2_leadingPrincipalBlock
          (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (1 + k)) := by
  let rows : Fin k → Fin (m + 1) :=
    fun i => Fin.succ (Fin.castLE hk i)
  have hid :=
    higham9_6_pivot_mul_schur_det_eq_source_minor
      (n := m + 1) (k := k) A (p := (0 : Fin (m + 1))) rows rows hpivot
  have hschurMatrix :
      (fun r c : Fin k => higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) =
        higham9_2_leadingPrincipalBlock
          (Matrix.of (higham9_1_firstSchurComplement A) :
            Matrix (Fin m) (Fin m) ℝ) k := by
    ext r c
    have hr :
        (Fin.castLE hk r).succ =
          (⟨r.val + 1, by omega⟩ : Fin (m + 1)) := by
      ext
      simp [Fin.castLE]
    have hc :
        (Fin.castLE hk c).succ =
          (⟨c.val + 1, by omega⟩ : Fin (m + 1)) := by
      ext
      simp [Fin.castLE]
    simp [rows, higham9_2_leadingPrincipalBlock, hk, hr, hc,
      higham9_1_firstSchurComplement, luFirstSchurComplement,
      higham9_6_firstSchurUpdate]
    field_simp [hpivot]
  have hsourceMatrix :
      (fun r c : Fin (1 + k) =>
          A
            (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows r)
            (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows c)) =
        higham9_2_leadingPrincipalBlock
          (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (1 + k) := by
    have hle : 1 + k ≤ m + 1 := by omega
    ext r c
    cases r using Fin.addCases <;> cases c using Fin.addCases
    · simp [rows, higham9_2_leadingPrincipalBlock, hle, Fin.castLE]
    · simp [rows, higham9_2_leadingPrincipalBlock, hle, Fin.castLE]
      apply congrArg (fun q : Fin (m + 1) => A 0 q)
      apply Fin.ext
      simp
      omega
    · simp [rows, higham9_2_leadingPrincipalBlock, hle, Fin.castLE]
      apply congrArg (fun q : Fin (m + 1) => A q 0)
      apply Fin.ext
      simp
      omega
    · simp [rows, higham9_2_leadingPrincipalBlock, hle, Fin.castLE]
      apply congrArg₂ A
      · apply Fin.ext
        simp
        omega
      · apply Fin.ext
        simp
        omega
  simpa [hschurMatrix, hsourceMatrix] using hid

/-- **Problem 9.6**, block Desnanot/Sylvester determinant core in Schur
form.  If a middle block `M` is invertible and two border indices are grouped
after it, then the determinant of the full bordered block times `det M`
equals the product of the two diagonal bordered determinants minus the product
of the two off-diagonal bordered determinants.  This is pure determinant
infrastructure for the remaining adjacent Koteljanskii/Fischer route; it does
not assert any total-nonnegativity inequality. -/
theorem higham9_6_desnanot_schur_core {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) [Invertible M]
    (B : Matrix (Fin m) (Fin 2) ℝ)
    (C : Matrix (Fin 2) (Fin m) ℝ)
    (D : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.det (Matrix.fromBlocks M B C D) * Matrix.det M =
      Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 0)
            (fun (_ : Fin 1) (j : Fin m) => C 0 j)
            (fun (_ _ : Fin 1) => D 0 0)) *
        Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 1)
            (fun (_ : Fin 1) (j : Fin m) => C 1 j)
            (fun (_ _ : Fin 1) => D 1 1)) -
        Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 1)
            (fun (_ : Fin 1) (j : Fin m) => C 0 j)
            (fun (_ _ : Fin 1) => D 0 1)) *
          Matrix.det
            (Matrix.fromBlocks M
              (fun (i : Fin m) (_ : Fin 1) => B i 0)
              (fun (_ : Fin 1) (j : Fin m) => C 1 j)
              (fun (_ _ : Fin 1) => D 1 0)) := by
  let S : Matrix (Fin 2) (Fin 2) ℝ := D - C * ⅟M * B
  have hfull :
      Matrix.det (Matrix.fromBlocks M B C D) =
        Matrix.det M * Matrix.det S := by
    simpa [S] using Matrix.det_fromBlocks₁₁ M B C D
  have hlead :
      Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 0)
            (fun (_ : Fin 1) (j : Fin m) => C 0 j)
            (fun (_ _ : Fin 1) => D 0 0)) =
        Matrix.det M * S 0 0 := by
    rw [Matrix.det_fromBlocks₁₁]
    congr 1
    rw [Matrix.det_fin_one]
    simp [S, Matrix.mul_apply]
  have htrail :
      Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 1)
            (fun (_ : Fin 1) (j : Fin m) => C 1 j)
            (fun (_ _ : Fin 1) => D 1 1)) =
        Matrix.det M * S 1 1 := by
    rw [Matrix.det_fromBlocks₁₁]
    congr 1
    rw [Matrix.det_fin_one]
    simp [S, Matrix.mul_apply]
  have hoff01 :
      Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 1)
            (fun (_ : Fin 1) (j : Fin m) => C 0 j)
            (fun (_ _ : Fin 1) => D 0 1)) =
        Matrix.det M * S 0 1 := by
    rw [Matrix.det_fromBlocks₁₁]
    congr 1
    rw [Matrix.det_fin_one]
    simp [S, Matrix.mul_apply]
  have hoff10 :
      Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 0)
            (fun (_ : Fin 1) (j : Fin m) => C 1 j)
            (fun (_ _ : Fin 1) => D 1 0)) =
        Matrix.det M * S 1 0 := by
    rw [Matrix.det_fromBlocks₁₁]
    congr 1
    rw [Matrix.det_fin_one]
    simp [S, Matrix.mul_apply]
  rw [hfull, hlead, htrail, hoff01, hoff10, Matrix.det_fin_two]
  ring

/-- **Problem 9.6**, block Koteljanskii/Fischer inequality in the reordered
Desnanot model.  The preceding identity reduces the determinant comparison to
subtracting the product of the two off-diagonal bordered minors; total
nonnegativity supplies those two nonnegativity hypotheses in the source-indexed
application. -/
theorem higham9_6_desnanot_schur_core_inequality {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) [Invertible M]
    (B : Matrix (Fin m) (Fin 2) ℝ)
    (C : Matrix (Fin 2) (Fin m) ℝ)
    (D : Matrix (Fin 2) (Fin 2) ℝ)
    (hoff01 :
      0 ≤ Matrix.det
        (Matrix.fromBlocks M
          (fun (i : Fin m) (_ : Fin 1) => B i 1)
          (fun (_ : Fin 1) (j : Fin m) => C 0 j)
          (fun (_ _ : Fin 1) => D 0 1)))
    (hoff10 :
      0 ≤ Matrix.det
        (Matrix.fromBlocks M
          (fun (i : Fin m) (_ : Fin 1) => B i 0)
          (fun (_ : Fin 1) (j : Fin m) => C 1 j)
          (fun (_ _ : Fin 1) => D 1 0))) :
    Matrix.det (Matrix.fromBlocks M B C D) * Matrix.det M ≤
      Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 0)
            (fun (_ : Fin 1) (j : Fin m) => C 0 j)
            (fun (_ _ : Fin 1) => D 0 0)) *
        Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 1)
            (fun (_ : Fin 1) (j : Fin m) => C 1 j)
            (fun (_ _ : Fin 1) => D 1 1)) := by
  have hcore := higham9_6_desnanot_schur_core M B C D
  have hoff_prod :
      0 ≤
        Matrix.det
            (Matrix.fromBlocks M
              (fun (i : Fin m) (_ : Fin 1) => B i 1)
              (fun (_ : Fin 1) (j : Fin m) => C 0 j)
              (fun (_ _ : Fin 1) => D 0 1)) *
          Matrix.det
            (Matrix.fromBlocks M
              (fun (i : Fin m) (_ : Fin 1) => B i 0)
              (fun (_ : Fin 1) (j : Fin m) => C 1 j)
              (fun (_ _ : Fin 1) => D 1 0)) :=
    mul_nonneg hoff01 hoff10
  linarith

/-- **Problem 9.6**, block Koteljanskii/Fischer inequality from the
reordered Desnanot identity under the exact product-side condition needed by
the source-indexed application.  The two off-diagonal bordered determinants
may each acquire the same permutation sign when translated from natural
source order; their product is the invariant nonnegative quantity. -/
theorem higham9_6_desnanot_schur_core_inequality_of_offdiag_product_nonneg {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) [Invertible M]
    (B : Matrix (Fin m) (Fin 2) ℝ)
    (C : Matrix (Fin 2) (Fin m) ℝ)
    (D : Matrix (Fin 2) (Fin 2) ℝ)
    (hoff_prod :
      0 ≤
        Matrix.det
            (Matrix.fromBlocks M
              (fun (i : Fin m) (_ : Fin 1) => B i 1)
              (fun (_ : Fin 1) (j : Fin m) => C 0 j)
              (fun (_ _ : Fin 1) => D 0 1)) *
          Matrix.det
            (Matrix.fromBlocks M
              (fun (i : Fin m) (_ : Fin 1) => B i 0)
              (fun (_ : Fin 1) (j : Fin m) => C 1 j)
              (fun (_ _ : Fin 1) => D 1 0))) :
    Matrix.det (Matrix.fromBlocks M B C D) * Matrix.det M ≤
      Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 0)
            (fun (_ : Fin 1) (j : Fin m) => C 0 j)
            (fun (_ _ : Fin 1) => D 0 0)) *
        Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 1)
            (fun (_ : Fin 1) (j : Fin m) => C 1 j)
            (fun (_ _ : Fin 1) => D 1 1)) := by
  have hcore := higham9_6_desnanot_schur_core M B C D
  linarith

/-- **Problem 9.6 support**, the source-index map from the reordered
Desnanot block order `[1, ..., m, 0, m+1]` to the natural order
`[0, 1, ..., m, m+1]`. -/
def higham9_6_middleEndpointsToSource (m : ℕ) :
    Fin m ⊕ Fin 2 → Fin (m + 2)
  | Sum.inl i => ⟨i.val + 1, by omega⟩
  | Sum.inr t => if t = 0 then 0 else ⟨m + 1, by omega⟩

/-- **Problem 9.6 support**, the reordered Desnanot block index map is
bijective. -/
theorem higham9_6_middleEndpointsToSource_bijective (m : ℕ) :
    Function.Bijective (higham9_6_middleEndpointsToSource m) := by
  constructor
  · intro a b hab
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            apply congrArg Sum.inl
            apply Fin.ext
            simp [higham9_6_middleEndpointsToSource] at hab
            omega
        | inr t =>
            fin_cases t
            · simp [higham9_6_middleEndpointsToSource] at hab
            · simp [higham9_6_middleEndpointsToSource] at hab
              omega
    | inr t =>
        fin_cases t
        · cases b with
          | inl j =>
              simp [higham9_6_middleEndpointsToSource] at hab
          | inr u =>
              fin_cases u <;> simp [higham9_6_middleEndpointsToSource] at hab ⊢
        · cases b with
          | inl j =>
              simp [higham9_6_middleEndpointsToSource] at hab
              omega
          | inr u =>
              fin_cases u <;> simp [higham9_6_middleEndpointsToSource] at hab ⊢
  · intro y
    by_cases hy0 : y.val = 0
    · refine ⟨Sum.inr (0 : Fin 2), ?_⟩
      apply Fin.ext
      simp [higham9_6_middleEndpointsToSource, hy0]
    · by_cases hylast : y.val = m + 1
      · refine ⟨Sum.inr (1 : Fin 2), ?_⟩
        apply Fin.ext
        simp [higham9_6_middleEndpointsToSource, hylast]
      · have hy_pos : 0 < y.val := Nat.pos_of_ne_zero hy0
        have hy_lt_last : y.val < m + 1 := by
          have hy_le : y.val ≤ m + 1 := by omega
          exact lt_of_le_of_ne hy_le hylast
        refine ⟨Sum.inl (⟨y.val - 1, by omega⟩ : Fin m), ?_⟩
        apply Fin.ext
        simp [higham9_6_middleEndpointsToSource]
        omega

/-- **Problem 9.6 support**, equivalence between the reordered Desnanot block
index type and the natural source index type. -/
noncomputable def higham9_6_middleEndpointsEquiv (m : ℕ) :
    Fin m ⊕ Fin 2 ≃ Fin (m + 2) :=
  Equiv.ofBijective (higham9_6_middleEndpointsToSource m)
    (higham9_6_middleEndpointsToSource_bijective m)

@[simp]
theorem higham9_6_middleEndpointsEquiv_inl {m : ℕ} (i : Fin m) :
    higham9_6_middleEndpointsEquiv m (Sum.inl i) =
      (⟨i.val + 1, by omega⟩ : Fin (m + 2)) := by
  rfl

@[simp]
theorem higham9_6_middleEndpointsEquiv_inr_zero {m : ℕ} :
    higham9_6_middleEndpointsEquiv m (Sum.inr (0 : Fin 2)) =
      (0 : Fin (m + 2)) := by
  rfl

@[simp]
theorem higham9_6_middleEndpointsEquiv_inr_one {m : ℕ} :
    higham9_6_middleEndpointsEquiv m (Sum.inr (1 : Fin 2)) =
      (⟨m + 1, by omega⟩ : Fin (m + 2)) := by
  rfl

/-- **Problem 9.6 support**, middle source indices `1, ..., m` inside a
matrix of order `m+2`. -/
def higham9_6_middleIndex (m : ℕ) (i : Fin m) : Fin (m + 2) :=
  ⟨i.val + 1, by omega⟩

/-- **Problem 9.6 support**, the two endpoint source indices `0` and `m+1`
inside a matrix of order `m+2`. -/
def higham9_6_endpointIndex (m : ℕ) (t : Fin 2) : Fin (m + 2) :=
  if t = 0 then 0 else ⟨m + 1, by omega⟩

@[simp]
theorem higham9_6_endpointIndex_zero {m : ℕ} :
    higham9_6_endpointIndex m (0 : Fin 2) = (0 : Fin (m + 2)) := by
  simp [higham9_6_endpointIndex]

@[simp]
theorem higham9_6_endpointIndex_one {m : ℕ} :
    higham9_6_endpointIndex m (1 : Fin 2) =
      (⟨m + 1, by omega⟩ : Fin (m + 2)) := by
  simp [higham9_6_endpointIndex]

/-- **Problem 9.6 support**, middle block `A(1:m,1:m)` used by the adjacent
Desnanot/Koteljanskii bridge. -/
def higham9_6_adjacentMiddleBlock {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => A (higham9_6_middleIndex m i) (higham9_6_middleIndex m j)

/-- **Problem 9.6 support**, the two endpoint columns bordering the middle
block in the adjacent Desnanot decomposition. -/
def higham9_6_adjacentEndpointCols {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix (Fin m) (Fin 2) ℝ :=
  fun i t => A (higham9_6_middleIndex m i) (higham9_6_endpointIndex m t)

/-- **Problem 9.6 support**, the two endpoint rows bordering the middle block
in the adjacent Desnanot decomposition. -/
def higham9_6_adjacentEndpointRows {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix (Fin 2) (Fin m) ℝ :=
  fun t j => A (higham9_6_endpointIndex m t) (higham9_6_middleIndex m j)

/-- **Problem 9.6 support**, the `2 by 2` endpoint block in the adjacent
Desnanot decomposition. -/
def higham9_6_adjacentEndpointBlock {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun t u => A (higham9_6_endpointIndex m t) (higham9_6_endpointIndex m u)

/-- **Problem 9.6 support**, natural-order off-diagonal bordered minor with
source rows `[0, 1, ..., m]` and columns `[1, ..., m, m+1]`. -/
def higham9_6_adjacentOffdiag01Natural {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun r c => A (⟨r.val, by omega⟩ : Fin (m + 2))
    (⟨c.val + 1, by omega⟩ : Fin (m + 2))

/-- **Problem 9.6 support**, natural-order off-diagonal bordered minor with
source rows `[1, ..., m, m+1]` and columns `[0, 1, ..., m]`. -/
def higham9_6_adjacentOffdiag10Natural {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun r c => A (⟨r.val + 1, by omega⟩ : Fin (m + 2))
    (⟨c.val, by omega⟩ : Fin (m + 2))

/-- **Problem 9.6 support**, total nonnegativity gives nonnegativity of the
natural-order `[0, ..., m]` by `[1, ..., m+1]` off-diagonal bordered minor. -/
theorem higham9_6_adjacentOffdiag01Natural_det_nonneg {m : ℕ}
    {A : Fin (m + 2) → Fin (m + 2) → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A) :
    0 ≤ Matrix.det (higham9_6_adjacentOffdiag01Natural A) := by
  let rows : Fin (m + 1) → Fin (m + 2) :=
    fun r => ⟨r.val, by omega⟩
  let cols : Fin (m + 1) → Fin (m + 2) :=
    fun c => ⟨c.val + 1, by omega⟩
  have hrows : StrictMono (fun r : Fin (m + 1) => (rows r).val) := by
    intro i j hij
    simpa [rows] using hij
  have hcols : StrictMono (fun c : Fin (m + 1) => (cols c).val) := by
    intro i j hij
    simp [cols]
    omega
  have h := hTN (m + 1) rows cols hrows hcols
  simpa [higham9_6_adjacentOffdiag01Natural, rows, cols] using h

/-- **Problem 9.6 support**, total nonnegativity gives nonnegativity of the
natural-order `[1, ..., m+1]` by `[0, ..., m]` off-diagonal bordered minor. -/
theorem higham9_6_adjacentOffdiag10Natural_det_nonneg {m : ℕ}
    {A : Fin (m + 2) → Fin (m + 2) → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A) :
    0 ≤ Matrix.det (higham9_6_adjacentOffdiag10Natural A) := by
  let rows : Fin (m + 1) → Fin (m + 2) :=
    fun r => ⟨r.val + 1, by omega⟩
  let cols : Fin (m + 1) → Fin (m + 2) :=
    fun c => ⟨c.val, by omega⟩
  have hrows : StrictMono (fun r : Fin (m + 1) => (rows r).val) := by
    intro i j hij
    simp [rows]
    omega
  have hcols : StrictMono (fun c : Fin (m + 1) => (cols c).val) := by
    intro i j hij
    simpa [cols] using hij
  have h := hTN (m + 1) rows cols hrows hcols
  simpa [higham9_6_adjacentOffdiag10Natural, rows, cols] using h

/-- **Problem 9.6 support**, the reordered Desnanot block matrix is the
natural source matrix reindexed by `[1, ..., m, 0, m+1]`. -/
theorem higham9_6_middleEndpoints_fromBlocks_eq_source {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix.fromBlocks
        (fun i j : Fin m => A (higham9_6_middleIndex m i)
          (higham9_6_middleIndex m j))
        (fun (i : Fin m) (t : Fin 2) => A (higham9_6_middleIndex m i)
          (higham9_6_endpointIndex m t))
        (fun (t : Fin 2) (j : Fin m) => A (higham9_6_endpointIndex m t)
          (higham9_6_middleIndex m j))
        (fun t u : Fin 2 => A (higham9_6_endpointIndex m t)
          (higham9_6_endpointIndex m u)) =
      (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ).submatrix
        (higham9_6_middleEndpointsEquiv m)
        (higham9_6_middleEndpointsEquiv m) := by
  ext r c
  cases r with
  | inl i =>
      cases c with
      | inl j =>
          simp [Matrix.fromBlocks, higham9_6_middleIndex]
      | inr t =>
          fin_cases t <;> simp [Matrix.fromBlocks, higham9_6_middleIndex,
            higham9_6_endpointIndex]
  | inr t =>
      fin_cases t
      · cases c with
        | inl j =>
            simp [Matrix.fromBlocks, higham9_6_middleIndex,
              higham9_6_endpointIndex]
        | inr u =>
            fin_cases u <;> simp [Matrix.fromBlocks, higham9_6_endpointIndex]
      · cases c with
        | inl j =>
            simp [Matrix.fromBlocks, higham9_6_middleIndex,
              higham9_6_endpointIndex]
        | inr u =>
            fin_cases u <;> simp [Matrix.fromBlocks, higham9_6_endpointIndex]

/-- **Problem 9.6 support**, determinant form of
`higham9_6_middleEndpoints_fromBlocks_eq_source`. -/
theorem higham9_6_det_middleEndpoints_fromBlocks_eq_source {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix.det
        (Matrix.fromBlocks
          (fun i j : Fin m => A (higham9_6_middleIndex m i)
            (higham9_6_middleIndex m j))
          (fun (i : Fin m) (t : Fin 2) => A (higham9_6_middleIndex m i)
            (higham9_6_endpointIndex m t))
          (fun (t : Fin 2) (j : Fin m) => A (higham9_6_endpointIndex m t)
            (higham9_6_middleIndex m j))
          (fun t u : Fin 2 => A (higham9_6_endpointIndex m t)
            (higham9_6_endpointIndex m u))) =
      Matrix.det (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) := by
  rw [higham9_6_middleEndpoints_fromBlocks_eq_source]
  rw [Matrix.det_submatrix_equiv_self]

/-- **Problem 9.6 support**, block order `[1, ..., m, 0]` mapped to the
leading source index order `[0, 1, ..., m]`. -/
def higham9_6_middleEndpoint0ToLeading (m : ℕ) :
    Fin m ⊕ Fin 1 → Fin (m + 1)
  | Sum.inl i => ⟨i.val + 1, by omega⟩
  | Sum.inr _ => 0

/-- **Problem 9.6 support**, the `[1, ..., m, 0]` leading-block index map is
bijective. -/
theorem higham9_6_middleEndpoint0ToLeading_bijective (m : ℕ) :
    Function.Bijective (higham9_6_middleEndpoint0ToLeading m) := by
  constructor
  · intro a b hab
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            apply congrArg Sum.inl
            apply Fin.ext
            simp [higham9_6_middleEndpoint0ToLeading] at hab
            omega
        | inr t =>
            fin_cases t
            simp [higham9_6_middleEndpoint0ToLeading] at hab
    | inr t =>
        fin_cases t
        cases b with
        | inl j =>
            simp [higham9_6_middleEndpoint0ToLeading] at hab
        | inr u =>
            fin_cases u
            rfl
  · intro y
    by_cases hy0 : y.val = 0
    · refine ⟨Sum.inr (0 : Fin 1), ?_⟩
      apply Fin.ext
      simp [higham9_6_middleEndpoint0ToLeading, hy0]
    · refine ⟨Sum.inl (⟨y.val - 1, by omega⟩ : Fin m), ?_⟩
      apply Fin.ext
      simp [higham9_6_middleEndpoint0ToLeading]
      omega

/-- **Problem 9.6 support**, equivalence between `[1, ..., m, 0]` block
order and the leading source index type. -/
noncomputable def higham9_6_middleEndpoint0LeadingEquiv (m : ℕ) :
    Fin m ⊕ Fin 1 ≃ Fin (m + 1) :=
  Equiv.ofBijective (higham9_6_middleEndpoint0ToLeading m)
    (higham9_6_middleEndpoint0ToLeading_bijective m)

@[simp]
theorem higham9_6_middleEndpoint0LeadingEquiv_inl {m : ℕ} (i : Fin m) :
    higham9_6_middleEndpoint0LeadingEquiv m (Sum.inl i) =
      (⟨i.val + 1, by omega⟩ : Fin (m + 1)) := by
  rfl

@[simp]
theorem higham9_6_middleEndpoint0LeadingEquiv_inr {m : ℕ} (t : Fin 1) :
    higham9_6_middleEndpoint0LeadingEquiv m (Sum.inr t) =
      (0 : Fin (m + 1)) := by
  fin_cases t
  rfl

/-- **Problem 9.6 support**, block order `[1, ..., m, m+1]` mapped to the
trailing source index order. -/
def higham9_6_middleEndpoint1ToTrailing (m : ℕ) :
    Fin m ⊕ Fin 1 → Fin (m + 1)
  | Sum.inl i => ⟨i.val, by omega⟩
  | Sum.inr _ => ⟨m, by omega⟩

/-- **Problem 9.6 support**, the `[1, ..., m, m+1]` trailing-block index map
is bijective. -/
theorem higham9_6_middleEndpoint1ToTrailing_bijective (m : ℕ) :
    Function.Bijective (higham9_6_middleEndpoint1ToTrailing m) := by
  constructor
  · intro a b hab
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            apply congrArg Sum.inl
            apply Fin.ext
            simp [higham9_6_middleEndpoint1ToTrailing] at hab
            omega
        | inr t =>
            fin_cases t
            simp [higham9_6_middleEndpoint1ToTrailing] at hab
            omega
    | inr t =>
        fin_cases t
        cases b with
        | inl j =>
            simp [higham9_6_middleEndpoint1ToTrailing] at hab
            omega
        | inr u =>
            fin_cases u
            rfl
  · intro y
    by_cases hylast : y.val = m
    · refine ⟨Sum.inr (0 : Fin 1), ?_⟩
      apply Fin.ext
      simp [higham9_6_middleEndpoint1ToTrailing, hylast]
    · refine ⟨Sum.inl (⟨y.val, by omega⟩ : Fin m), ?_⟩
      apply Fin.ext
      simp [higham9_6_middleEndpoint1ToTrailing]

/-- **Problem 9.6 support**, equivalence between `[1, ..., m, m+1]` block
order and the trailing source index type. -/
noncomputable def higham9_6_middleEndpoint1TrailingEquiv (m : ℕ) :
    Fin m ⊕ Fin 1 ≃ Fin (m + 1) :=
  Equiv.ofBijective (higham9_6_middleEndpoint1ToTrailing m)
    (higham9_6_middleEndpoint1ToTrailing_bijective m)

@[simp]
theorem higham9_6_middleEndpoint1TrailingEquiv_inl {m : ℕ} (i : Fin m) :
    higham9_6_middleEndpoint1TrailingEquiv m (Sum.inl i) =
      (⟨i.val, by omega⟩ : Fin (m + 1)) := by
  rfl

@[simp]
theorem higham9_6_middleEndpoint1TrailingEquiv_inr {m : ℕ} (t : Fin 1) :
    higham9_6_middleEndpoint1TrailingEquiv m (Sum.inr t) =
      (⟨m, by omega⟩ : Fin (m + 1)) := by
  fin_cases t
  rfl

/-- **Problem 9.6 support**, determinant adapter from the reordered
`[1, ..., m, 0]` bordered block to the natural leading principal block. -/
theorem higham9_6_det_middleEndpoint0_fromBlocks_eq_leadingPrincipalBlock {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix.det
        (Matrix.fromBlocks
          (fun i j : Fin m => A (higham9_6_middleIndex m i)
            (higham9_6_middleIndex m j))
          (fun (i : Fin m) (_ : Fin 1) => A (higham9_6_middleIndex m i) 0)
          (fun (_ : Fin 1) (j : Fin m) => A 0 (higham9_6_middleIndex m j))
          (fun (_ _ : Fin 1) => A 0 0)) =
      Matrix.det
        (higham9_2_leadingPrincipalBlock
          (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) (m + 1)) := by
  have hle : m + 1 ≤ m + 2 := by omega
  have hmatrix :
      Matrix.fromBlocks
          (fun i j : Fin m => A (higham9_6_middleIndex m i)
            (higham9_6_middleIndex m j))
          (fun (i : Fin m) (_ : Fin 1) => A (higham9_6_middleIndex m i) 0)
          (fun (_ : Fin 1) (j : Fin m) => A 0 (higham9_6_middleIndex m j))
          (fun (_ _ : Fin 1) => A 0 0) =
        (higham9_2_leadingPrincipalBlock
            (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) (m + 1)).submatrix
          (higham9_6_middleEndpoint0LeadingEquiv m)
          (higham9_6_middleEndpoint0LeadingEquiv m) := by
    ext r c
    cases r with
    | inl i =>
        cases c with
        | inl j =>
            simp [Matrix.fromBlocks, higham9_2_leadingPrincipalBlock, hle,
              higham9_6_middleIndex]
        | inr t =>
            fin_cases t
            simp [Matrix.fromBlocks, higham9_2_leadingPrincipalBlock, hle,
              higham9_6_middleIndex]
    | inr t =>
        fin_cases t
        cases c with
        | inl j =>
            simp [Matrix.fromBlocks, higham9_2_leadingPrincipalBlock, hle,
              higham9_6_middleIndex]
        | inr u =>
            fin_cases u
            simp [Matrix.fromBlocks, higham9_2_leadingPrincipalBlock, hle]
  rw [hmatrix]
  rw [Matrix.det_submatrix_equiv_self]

/-- **Problem 9.6 support**, determinant adapter from the reordered
`[1, ..., m, m+1]` bordered block to the natural trailing principal block. -/
theorem higham9_6_det_middleEndpoint1_fromBlocks_eq_trailingPrincipalBlock {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix.det
        (Matrix.fromBlocks
          (fun i j : Fin m => A (higham9_6_middleIndex m i)
            (higham9_6_middleIndex m j))
          (fun (i : Fin m) (_ : Fin 1) =>
            A (higham9_6_middleIndex m i) (⟨m + 1, by omega⟩ : Fin (m + 2)))
          (fun (_ : Fin 1) (j : Fin m) =>
            A (⟨m + 1, by omega⟩ : Fin (m + 2)) (higham9_6_middleIndex m j))
          (fun (_ _ : Fin 1) =>
            A (⟨m + 1, by omega⟩ : Fin (m + 2))
              (⟨m + 1, by omega⟩ : Fin (m + 2)))) =
      Matrix.det
        (higham9_6_trailingPrincipalBlock
          (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) 1) := by
  have hp : 1 ≤ m + 2 := by omega
  have hmatrix :
      Matrix.fromBlocks
          (fun i j : Fin m => A (higham9_6_middleIndex m i)
            (higham9_6_middleIndex m j))
          (fun (i : Fin m) (_ : Fin 1) =>
            A (higham9_6_middleIndex m i) (⟨m + 1, by omega⟩ : Fin (m + 2)))
          (fun (_ : Fin 1) (j : Fin m) =>
            A (⟨m + 1, by omega⟩ : Fin (m + 2)) (higham9_6_middleIndex m j))
          (fun (_ _ : Fin 1) =>
            A (⟨m + 1, by omega⟩ : Fin (m + 2))
              (⟨m + 1, by omega⟩ : Fin (m + 2))) =
        (higham9_6_trailingPrincipalBlock
            (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) 1).submatrix
          (higham9_6_middleEndpoint1TrailingEquiv m)
          (higham9_6_middleEndpoint1TrailingEquiv m) := by
    ext r c
    cases r with
    | inl i =>
        cases c with
        | inl j =>
            simp [Matrix.fromBlocks, higham9_6_trailingPrincipalBlock, hp,
              higham9_6_middleIndex]
            apply congrArg₂ A <;> apply Fin.ext <;> simp <;> omega
        | inr t =>
            fin_cases t
            simp [Matrix.fromBlocks, higham9_6_trailingPrincipalBlock, hp,
              higham9_6_middleIndex]
            apply congrArg₂ A <;> apply Fin.ext <;> simp <;> omega
    | inr t =>
        fin_cases t
        cases c with
        | inl j =>
            simp [Matrix.fromBlocks, higham9_6_trailingPrincipalBlock, hp,
              higham9_6_middleIndex]
            apply congrArg₂ A <;> apply Fin.ext <;> simp <;> omega
        | inr u =>
            fin_cases u
            simp [Matrix.fromBlocks, higham9_6_trailingPrincipalBlock, hp]
            apply congrArg₂ A <;> apply Fin.ext <;> simp <;> omega
  rw [hmatrix]
  exact Matrix.det_submatrix_equiv_self
    (higham9_6_middleEndpoint1TrailingEquiv m)
    (higham9_6_trailingPrincipalBlock
      (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) 1)

/-- **Problem 9.6 support**, the reordered off-diagonal bordered determinant
with endpoint columns `(m+1)` and endpoint rows `0` differs from the
natural-order TN minor only by the column permutation sign. -/
theorem higham9_6_det_adjacentOffdiag01_eq_sign_mul_natural {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix.det
        (Matrix.fromBlocks (higham9_6_adjacentMiddleBlock A)
          (fun (i : Fin m) (_ : Fin 1) =>
            higham9_6_adjacentEndpointCols A i 1)
          (fun (_ : Fin 1) (j : Fin m) =>
            higham9_6_adjacentEndpointRows A 0 j)
          (fun (_ _ : Fin 1) =>
            higham9_6_adjacentEndpointBlock A 0 1)) =
      ((Equiv.Perm.sign
          ((higham9_6_middleEndpoint1TrailingEquiv m).trans
            (higham9_6_middleEndpoint0LeadingEquiv m).symm) : ℤ) : ℝ) *
        Matrix.det (higham9_6_adjacentOffdiag01Natural A) := by
  let e0 := higham9_6_middleEndpoint0LeadingEquiv m
  let e1 := higham9_6_middleEndpoint1TrailingEquiv m
  let σ : Equiv.Perm (Fin m ⊕ Fin 1) := e1.trans e0.symm
  have hperm := Matrix.det_permute' σ
    ((higham9_6_adjacentOffdiag01Natural A).submatrix e0 e0)
  have hmatrix :
      ((higham9_6_adjacentOffdiag01Natural A).submatrix e0 e0).submatrix
          id σ =
        Matrix.fromBlocks (higham9_6_adjacentMiddleBlock A)
          (fun (i : Fin m) (_ : Fin 1) =>
            higham9_6_adjacentEndpointCols A i 1)
          (fun (_ : Fin 1) (j : Fin m) =>
            higham9_6_adjacentEndpointRows A 0 j)
          (fun (_ _ : Fin 1) =>
            higham9_6_adjacentEndpointBlock A 0 1) := by
    ext r c
    cases r with
    | inl i =>
        cases c with
        | inl j =>
            simp [e0, e1, σ, Matrix.fromBlocks,
              higham9_6_adjacentOffdiag01Natural,
              higham9_6_adjacentMiddleBlock, higham9_6_adjacentEndpointCols,
              higham9_6_middleIndex, higham9_6_endpointIndex]
        | inr t =>
            fin_cases t
            simp [e0, e1, σ, Matrix.fromBlocks,
              higham9_6_adjacentOffdiag01Natural,
              higham9_6_adjacentEndpointCols, higham9_6_middleIndex,
              higham9_6_endpointIndex]
    | inr t =>
        fin_cases t
        cases c with
        | inl j =>
            simp [e0, e1, σ, Matrix.fromBlocks,
              higham9_6_adjacentOffdiag01Natural,
              higham9_6_adjacentEndpointRows, higham9_6_middleIndex,
              higham9_6_endpointIndex]
        | inr u =>
            fin_cases u
            simp [e0, e1, σ, Matrix.fromBlocks,
              higham9_6_adjacentOffdiag01Natural,
              higham9_6_adjacentEndpointBlock, higham9_6_endpointIndex]
  rw [hmatrix] at hperm
  simpa [e0, e1, σ] using hperm

/-- **Problem 9.6 support**, the reordered off-diagonal bordered determinant
with endpoint columns `0` and endpoint rows `(m+1)` differs from the
natural-order TN minor only by the inverse column permutation sign. -/
theorem higham9_6_det_adjacentOffdiag10_eq_sign_mul_natural {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    Matrix.det
        (Matrix.fromBlocks (higham9_6_adjacentMiddleBlock A)
          (fun (i : Fin m) (_ : Fin 1) =>
            higham9_6_adjacentEndpointCols A i 0)
          (fun (_ : Fin 1) (j : Fin m) =>
            higham9_6_adjacentEndpointRows A 1 j)
          (fun (_ _ : Fin 1) =>
            higham9_6_adjacentEndpointBlock A 1 0)) =
      ((Equiv.Perm.sign
          ((higham9_6_middleEndpoint0LeadingEquiv m).trans
            (higham9_6_middleEndpoint1TrailingEquiv m).symm) : ℤ) : ℝ) *
        Matrix.det (higham9_6_adjacentOffdiag10Natural A) := by
  let e0 := higham9_6_middleEndpoint0LeadingEquiv m
  let e1 := higham9_6_middleEndpoint1TrailingEquiv m
  let σ : Equiv.Perm (Fin m ⊕ Fin 1) := e0.trans e1.symm
  have hperm := Matrix.det_permute' σ
    ((higham9_6_adjacentOffdiag10Natural A).submatrix e1 e1)
  have hmatrix :
      ((higham9_6_adjacentOffdiag10Natural A).submatrix e1 e1).submatrix
          id σ =
        Matrix.fromBlocks (higham9_6_adjacentMiddleBlock A)
          (fun (i : Fin m) (_ : Fin 1) =>
            higham9_6_adjacentEndpointCols A i 0)
          (fun (_ : Fin 1) (j : Fin m) =>
            higham9_6_adjacentEndpointRows A 1 j)
          (fun (_ _ : Fin 1) =>
            higham9_6_adjacentEndpointBlock A 1 0) := by
    ext r c
    cases r with
    | inl i =>
        cases c with
        | inl j =>
            simp [e0, e1, σ, Matrix.fromBlocks,
              higham9_6_adjacentOffdiag10Natural,
              higham9_6_adjacentMiddleBlock, higham9_6_adjacentEndpointCols,
              higham9_6_middleIndex, higham9_6_endpointIndex]
        | inr t =>
            fin_cases t
            simp [e0, e1, σ, Matrix.fromBlocks,
              higham9_6_adjacentOffdiag10Natural,
              higham9_6_adjacentEndpointCols, higham9_6_middleIndex,
              higham9_6_endpointIndex]
    | inr t =>
        fin_cases t
        cases c with
        | inl j =>
            simp [e0, e1, σ, Matrix.fromBlocks,
              higham9_6_adjacentOffdiag10Natural,
              higham9_6_adjacentEndpointRows, higham9_6_middleIndex,
              higham9_6_endpointIndex]
        | inr u =>
            fin_cases u
            simp [e0, e1, σ, Matrix.fromBlocks,
              higham9_6_adjacentOffdiag10Natural,
              higham9_6_adjacentEndpointBlock, higham9_6_endpointIndex]
  rw [hmatrix] at hperm
  simpa [e0, e1, σ] using hperm

/-- **Problem 9.6 support**, total nonnegativity supplies the nonnegative
off-diagonal bordered-minor product needed by the adjacent Desnanot bridge.
Each reordered determinant is a signed natural-order TN minor, and the two
permutation signs are inverse signs, so their product is one. -/
theorem higham9_6_adjacent_offdiag_product_nonneg_of_totalNonnegative {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A) :
    0 ≤
      Matrix.det
          (Matrix.fromBlocks (higham9_6_adjacentMiddleBlock A)
            (fun (i : Fin m) (_ : Fin 1) =>
              higham9_6_adjacentEndpointCols A i 1)
            (fun (_ : Fin 1) (j : Fin m) =>
              higham9_6_adjacentEndpointRows A 0 j)
            (fun (_ _ : Fin 1) =>
              higham9_6_adjacentEndpointBlock A 0 1)) *
        Matrix.det
          (Matrix.fromBlocks (higham9_6_adjacentMiddleBlock A)
            (fun (i : Fin m) (_ : Fin 1) =>
              higham9_6_adjacentEndpointCols A i 0)
            (fun (_ : Fin 1) (j : Fin m) =>
              higham9_6_adjacentEndpointRows A 1 j)
            (fun (_ _ : Fin 1) =>
              higham9_6_adjacentEndpointBlock A 1 0)) := by
  let e0 := higham9_6_middleEndpoint0LeadingEquiv m
  let e1 := higham9_6_middleEndpoint1TrailingEquiv m
  let σ01 : Equiv.Perm (Fin m ⊕ Fin 1) := e1.trans e0.symm
  let σ10 : Equiv.Perm (Fin m ⊕ Fin 1) := e0.trans e1.symm
  have h01 :
      Matrix.det
          (Matrix.fromBlocks (higham9_6_adjacentMiddleBlock A)
            (fun (i : Fin m) (_ : Fin 1) =>
              higham9_6_adjacentEndpointCols A i 1)
            (fun (_ : Fin 1) (j : Fin m) =>
              higham9_6_adjacentEndpointRows A 0 j)
            (fun (_ _ : Fin 1) =>
              higham9_6_adjacentEndpointBlock A 0 1)) =
        ((Equiv.Perm.sign σ01 : ℤ) : ℝ) *
          Matrix.det (higham9_6_adjacentOffdiag01Natural A) := by
    simpa [σ01] using higham9_6_det_adjacentOffdiag01_eq_sign_mul_natural A
  have h10 :
      Matrix.det
          (Matrix.fromBlocks (higham9_6_adjacentMiddleBlock A)
            (fun (i : Fin m) (_ : Fin 1) =>
              higham9_6_adjacentEndpointCols A i 0)
            (fun (_ : Fin 1) (j : Fin m) =>
              higham9_6_adjacentEndpointRows A 1 j)
            (fun (_ _ : Fin 1) =>
              higham9_6_adjacentEndpointBlock A 1 0)) =
        ((Equiv.Perm.sign σ10 : ℤ) : ℝ) *
          Matrix.det (higham9_6_adjacentOffdiag10Natural A) := by
    simpa [σ10] using higham9_6_det_adjacentOffdiag10_eq_sign_mul_natural A
  have hn01 : 0 ≤ Matrix.det (higham9_6_adjacentOffdiag01Natural A) :=
    higham9_6_adjacentOffdiag01Natural_det_nonneg hTN
  have hn10 : 0 ≤ Matrix.det (higham9_6_adjacentOffdiag10Natural A) :=
    higham9_6_adjacentOffdiag10Natural_det_nonneg hTN
  have hσ : σ10 = σ01.symm := by
    ext x
    simp [σ01, σ10]
  have hsign_int :
      ((Equiv.Perm.sign σ01 : ℤ) * (Equiv.Perm.sign σ10 : ℤ)) = 1 := by
    rw [hσ, Equiv.Perm.sign_symm]
    exact Int.isUnit_mul_self (Equiv.Perm.sign σ01).isUnit
  have hsign_real :
      ((Equiv.Perm.sign σ01 : ℤ) : ℝ) *
          ((Equiv.Perm.sign σ10 : ℤ) : ℝ) = 1 := by
    exact_mod_cast hsign_int
  have hnat_prod :
      0 ≤ Matrix.det (higham9_6_adjacentOffdiag01Natural A) *
        Matrix.det (higham9_6_adjacentOffdiag10Natural A) :=
    mul_nonneg hn01 hn10
  rw [h01, h10]
  have hprod_eq :
      (((Equiv.Perm.sign σ01 : ℤ) : ℝ) *
            Matrix.det (higham9_6_adjacentOffdiag01Natural A)) *
          (((Equiv.Perm.sign σ10 : ℤ) : ℝ) *
            Matrix.det (higham9_6_adjacentOffdiag10Natural A)) =
        Matrix.det (higham9_6_adjacentOffdiag01Natural A) *
          Matrix.det (higham9_6_adjacentOffdiag10Natural A) := by
    calc
      (((Equiv.Perm.sign σ01 : ℤ) : ℝ) *
            Matrix.det (higham9_6_adjacentOffdiag01Natural A)) *
          (((Equiv.Perm.sign σ10 : ℤ) : ℝ) *
            Matrix.det (higham9_6_adjacentOffdiag10Natural A)) =
          (((Equiv.Perm.sign σ01 : ℤ) : ℝ) *
              ((Equiv.Perm.sign σ10 : ℤ) : ℝ)) *
            (Matrix.det (higham9_6_adjacentOffdiag01Natural A) *
              Matrix.det (higham9_6_adjacentOffdiag10Natural A)) := by
            ring
      _ = Matrix.det (higham9_6_adjacentOffdiag01Natural A) *
          Matrix.det (higham9_6_adjacentOffdiag10Natural A) := by
            rw [hsign_real]
            ring
  rw [hprod_eq]
  exact hnat_prod

/-- **Problem 9.6 support**, adjacent source-indexed determinant inequality
from the reordered block Desnanot inequality and a nonnegative off-diagonal
bordered-minor product.  The remaining source work is to derive the displayed
product-side condition from total nonnegativity after the natural-order
reindexing/sign bridge. -/
theorem higham9_6_adjacent_desnanot_inequality_of_offdiag_product_nonneg
    {m : ℕ} (A : Fin (m + 2) → Fin (m + 2) → ℝ)
    (hM_ne :
      Matrix.det (higham9_6_adjacentMiddleBlock A) ≠ 0)
    (hoff_prod :
      0 ≤
        Matrix.det
            (Matrix.fromBlocks (higham9_6_adjacentMiddleBlock A)
              (fun (i : Fin m) (_ : Fin 1) =>
                higham9_6_adjacentEndpointCols A i 1)
              (fun (_ : Fin 1) (j : Fin m) =>
                higham9_6_adjacentEndpointRows A 0 j)
              (fun (_ _ : Fin 1) =>
                higham9_6_adjacentEndpointBlock A 0 1)) *
          Matrix.det
            (Matrix.fromBlocks (higham9_6_adjacentMiddleBlock A)
              (fun (i : Fin m) (_ : Fin 1) =>
                higham9_6_adjacentEndpointCols A i 0)
              (fun (_ : Fin 1) (j : Fin m) =>
                higham9_6_adjacentEndpointRows A 1 j)
              (fun (_ _ : Fin 1) =>
                higham9_6_adjacentEndpointBlock A 1 0))) :
    Matrix.det (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) *
        Matrix.det (higham9_6_adjacentMiddleBlock A) ≤
      Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) (m + 1)) *
        Matrix.det
          (higham9_6_trailingPrincipalBlock
            (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) 1) := by
  let M : Matrix (Fin m) (Fin m) ℝ := higham9_6_adjacentMiddleBlock A
  let B : Matrix (Fin m) (Fin 2) ℝ := higham9_6_adjacentEndpointCols A
  let C : Matrix (Fin 2) (Fin m) ℝ := higham9_6_adjacentEndpointRows A
  let D : Matrix (Fin 2) (Fin 2) ℝ := higham9_6_adjacentEndpointBlock A
  letI : Invertible (Matrix.det M) := invertibleOfNonzero (by simpa [M] using hM_ne)
  letI : Invertible M := Matrix.invertibleOfDetInvertible M
  have hineq :
      Matrix.det (Matrix.fromBlocks M B C D) * Matrix.det M ≤
        Matrix.det
            (Matrix.fromBlocks M
              (fun (i : Fin m) (_ : Fin 1) => B i 0)
              (fun (_ : Fin 1) (j : Fin m) => C 0 j)
              (fun (_ _ : Fin 1) => D 0 0)) *
          Matrix.det
            (Matrix.fromBlocks M
              (fun (i : Fin m) (_ : Fin 1) => B i 1)
              (fun (_ : Fin 1) (j : Fin m) => C 1 j)
              (fun (_ _ : Fin 1) => D 1 1)) := by
    exact higham9_6_desnanot_schur_core_inequality_of_offdiag_product_nonneg
      M B C D (by simpa [M, B, C, D] using hoff_prod)
  have hfull :
      Matrix.det (Matrix.fromBlocks M B C D) =
        Matrix.det (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) := by
    simpa [M, B, C, D, higham9_6_adjacentMiddleBlock,
      higham9_6_adjacentEndpointCols, higham9_6_adjacentEndpointRows,
      higham9_6_adjacentEndpointBlock] using
      higham9_6_det_middleEndpoints_fromBlocks_eq_source A
  have hlead :
      Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 0)
            (fun (_ : Fin 1) (j : Fin m) => C 0 j)
            (fun (_ _ : Fin 1) => D 0 0)) =
        Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) (m + 1)) := by
    simpa [M, B, C, D, higham9_6_adjacentMiddleBlock,
      higham9_6_adjacentEndpointCols, higham9_6_adjacentEndpointRows,
      higham9_6_adjacentEndpointBlock, higham9_6_endpointIndex] using
      higham9_6_det_middleEndpoint0_fromBlocks_eq_leadingPrincipalBlock A
  have htrail :
      Matrix.det
          (Matrix.fromBlocks M
            (fun (i : Fin m) (_ : Fin 1) => B i 1)
            (fun (_ : Fin 1) (j : Fin m) => C 1 j)
            (fun (_ _ : Fin 1) => D 1 1)) =
        Matrix.det
          (higham9_6_trailingPrincipalBlock
            (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) 1) := by
    simpa [M, B, C, D, higham9_6_adjacentMiddleBlock,
      higham9_6_adjacentEndpointCols, higham9_6_adjacentEndpointRows,
      higham9_6_adjacentEndpointBlock, higham9_6_endpointIndex] using
      higham9_6_det_middleEndpoint1_fromBlocks_eq_trailingPrincipalBlock A
  rw [hfull, hlead, htrail] at hineq
  simpa [M] using hineq

/-- **Problem 9.6 support**, adjacent source-indexed
Koteljanskii/Fischer step from total nonnegativity.  This closes the local
off-diagonal bordered-minor sign bridge for adjacent principal blocks; the
remaining higher-dimensional source work is to remove/use the nonzero middle
determinant condition in the induction proving the general `p` inequality. -/
theorem higham9_6_adjacent_desnanot_inequality_of_totalNonnegative
    {m : ℕ} (A : Fin (m + 2) → Fin (m + 2) → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hM_ne :
      Matrix.det (higham9_6_adjacentMiddleBlock A) ≠ 0) :
    Matrix.det (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) *
        Matrix.det (higham9_6_adjacentMiddleBlock A) ≤
      Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) (m + 1)) *
        Matrix.det
          (higham9_6_trailingPrincipalBlock
            (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) 1) :=
  higham9_6_adjacent_desnanot_inequality_of_offdiag_product_nonneg A hM_ne
    (higham9_6_adjacent_offdiag_product_nonneg_of_totalNonnegative A hTN)

/-- **Theorem 9.9**, nonsingularity is inherited by the first Schur complement
in the column-dominant no-pivot route.  The proof is the scalar Schur
determinant identity with the first row and column selected. -/
theorem higham9_9_colDiagDominant_firstSchurComplement_det_ne_zero {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hdiag : A 0 0 ≠ 0)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham9_1_firstSchurComplement A) : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  classical
  let rows : Fin m → Fin (m + 1) := fun i => i.succ
  have hid :=
    higham9_6_pivot_mul_schur_det_eq_source_minor
      (n := m + 1) (k := m) A (p := (0 : Fin (m + 1))) rows rows hdiag
  have hschurMatrix :
      (fun r c : Fin m => higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) =
        higham9_1_firstSchurComplement A := by
    ext i j
    simp [rows, higham9_6_firstSchurUpdate, higham9_1_firstSchurComplement,
      luFirstSchurComplement]
    field_simp [hdiag]
  have hsource_det :
      Matrix.det
        (fun r c : Fin (1 + m) =>
          A
            (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows r)
            (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows c)) ≠ 0 := by
    let e : Fin (1 + m) ≃ Fin (m + 1) := finCongr (by omega)
    have hdet_eq :
        Matrix.det
          (fun r c : Fin (1 + m) =>
            A
              (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows r)
              (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows c)) =
          Matrix.det ((Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).submatrix e e) := by
      apply congrArg Matrix.det
      ext r c
      congr 2
      · cases r using Fin.addCases
        · apply Fin.ext
          simp [e, rows]
        · apply Fin.ext
          simp [e, rows, Fin.cast]
          omega
      · cases c using Fin.addCases
        · apply Fin.ext
          simp [e, rows]
        · apply Fin.ext
          simp [e, rows, Fin.cast]
          omega
    rw [hdet_eq]
    rw [Matrix.det_submatrix_equiv_self e
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)]
    exact hdet
  have hmul_ne :
      A 0 0 *
        Matrix.det
          (fun r c : Fin m => higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) ≠ 0 := by
    simpa [hid] using hsource_det
  have hschur_ne :
      Matrix.det
        (fun r c : Fin m => higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) ≠ 0 :=
    (mul_ne_zero_iff.mp hmul_ne).2
  simpa [hschurMatrix] using hschur_ne

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, nonsingularity is
preserved by the first partial-pivot row swap and Schur-complement reduction. -/
theorem higham9_10_firstSchurComplement_det_ne_zero_of_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) {r : Fin (m + 1)}
    (hpivot : A r 0 ≠ 0)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of
        (luFirstSchurComplement
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) :
        Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  let sigma := higham9_7_firstPivotRowSwap r
  let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_2_rowPermutedMatrix A sigma
  have hdiag : Aperm 0 0 ≠ 0 := by
    simpa [Aperm, higham9_2_rowPermutedMatrix, sigma,
      higham9_7_firstPivotRowSwap] using hpivot
  have hdet_perm :
      Matrix.det (Matrix.of Aperm : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
    simpa [Aperm, sigma] using
      higham9_7_firstPivotRowSwap_det_ne_zero A r hdet
  simpa [Aperm, sigma, higham9_1_firstSchurComplement] using
    higham9_9_colDiagDominant_firstSchurComplement_det_ne_zero
      (A := Aperm) hdiag hdet_perm

/-- **Section 9.1 / complete-pivoting trace support**, after the first
complete-pivoting row and column swaps, nonsingularity passes to the first
Schur complement. -/
theorem higham9_1_firstCompletePivotSchurComplement_det_ne_zero_of_det_ne_zero
    {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    {r s : Fin (m + 1)}
    (hpivot : A r s ≠ 0)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of
        (luFirstSchurComplement
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s))) :
        Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  let sigma := higham9_7_firstPivotRowSwap r
  let tau := higham9_7_firstPivotRowSwap s
  let B : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_2_rowColPermutedMatrix A sigma tau
  have hdiag : B 0 0 ≠ 0 := by
    simpa [B, sigma, tau, higham9_2_rowColPermutedMatrix,
      higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix,
      higham9_7_firstPivotRowSwap] using hpivot
  have hdetB :
      Matrix.det (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
    simpa [B, sigma, tau] using
      higham9_2_firstPivotRowColSwap_det_ne_zero A r s hdet
  simpa [B, higham9_1_firstSchurComplement] using
    higham9_9_colDiagDominant_firstSchurComplement_det_ne_zero
      (A := B) hdiag hdetB

/-- **Theorem 9.8 / cumulative complete-pivoting support**, extend a
permutation of the trailing `m` active indices to a permutation of `m+1`
indices that fixes the leading index. -/
def higham9_8_extendTrailingPerm {m : ℕ} (sigma : Fin m → Fin m) :
    Fin (m + 1) → Fin (m + 1) :=
  fun i => if hi : i = 0 then 0 else (sigma (i.pred hi)).succ

@[simp] theorem higham9_8_extendTrailingPerm_zero {m : ℕ}
    (sigma : Fin m → Fin m) :
    higham9_8_extendTrailingPerm sigma 0 = 0 := by
  simp [higham9_8_extendTrailingPerm]

@[simp] theorem higham9_8_extendTrailingPerm_succ {m : ℕ}
    (sigma : Fin m → Fin m) (i : Fin m) :
    higham9_8_extendTrailingPerm sigma i.succ = (sigma i).succ := by
  simp [higham9_8_extendTrailingPerm]

theorem higham9_8_extendTrailingPerm_isPermutation {m : ℕ}
    {sigma : Fin m → Fin m} (hsigma : IsPermutation m sigma) :
    IsPermutation (m + 1) (higham9_8_extendTrailingPerm sigma) := by
  constructor
  · intro x y hxy
    cases x using Fin.cases with
    | zero =>
        cases y using Fin.cases with
        | zero => rfl
        | succ y =>
            have hy : (higham9_8_extendTrailingPerm sigma y.succ).val ≠ 0 := by
              simp
            exact (hy (by rw [← hxy]; simp)).elim
    | succ x =>
        cases y using Fin.cases with
        | zero =>
            have hx : (higham9_8_extendTrailingPerm sigma x.succ).val ≠ 0 := by
              simp
            exact (hx (by rw [hxy]; simp)).elim
        | succ y =>
            have hsxy : sigma x = sigma y := by
              apply Fin.ext
              have hval := congrArg Fin.val hxy
              simpa using hval
            exact congrArg Fin.succ (hsigma.1 hsxy)
  · intro y
    cases y using Fin.cases with
    | zero =>
        exact ⟨0, by simp⟩
    | succ y =>
        obtain ⟨x, hx⟩ := hsigma.2 y
        exact ⟨x.succ, by simp [hx]⟩

theorem higham9_8_isPermutation_comp {n : ℕ}
    {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) (htau : IsPermutation n tau) :
    IsPermutation n (fun i => sigma (tau i)) := by
  exact Function.Bijective.comp hsigma htau

theorem higham9_2_rowColPermutedMatrix_comp {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (sigma₀ tau₀ sigma₁ tau₁ : Fin n → Fin n) :
    higham9_2_rowColPermutedMatrix
        (higham9_2_rowColPermutedMatrix A sigma₀ tau₀) sigma₁ tau₁ =
      higham9_2_rowColPermutedMatrix A
        (fun i => sigma₀ (sigma₁ i)) (fun j => tau₀ (tau₁ j)) := by
  rfl

/-- Complex row/column permutations compose pointwise. -/
theorem higham9_2_complexRowColPermutedMatrix_comp {n : ℕ}
    (A : Fin n → Fin n → ℂ)
    (sigma₀ tau₀ sigma₁ tau₁ : Fin n → Fin n) :
    higham9_2_complexRowColPermutedMatrix
        (higham9_2_complexRowColPermutedMatrix A sigma₀ tau₀) sigma₁ tau₁ =
      higham9_2_complexRowColPermutedMatrix A
        (fun i => sigma₀ (sigma₁ i)) (fun j => tau₀ (tau₁ j)) := by
  rfl

/-- **Theorem 9.8 / cumulative complete-pivoting support**, trailing row and
column permutations commute with the first Schur-complement construction.
This is the algebraic step that lets later complete-pivoting swaps be lifted
back to a single cumulative `PAQ = LU` certificate. -/
theorem higham9_8_luFirstSchurComplement_trailingPerm {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (sigma tau : Fin m → Fin m) :
    luFirstSchurComplement
        (higham9_2_rowColPermutedMatrix A
          (higham9_8_extendTrailingPerm sigma)
          (higham9_8_extendTrailingPerm tau)) =
      higham9_2_rowColPermutedMatrix
        (luFirstSchurComplement A) sigma tau := by
  ext i j
  simp [luFirstSchurComplement, higham9_2_rowColPermutedMatrix,
    higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix]

/-- Complex trailing row/column permutations commute with the first
Schur-complement construction. -/
theorem higham9_8_complexFirstSchurComplement_trailingPerm {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (sigma tau : Fin m → Fin m) :
    higham9_8_complexFirstSchurComplement
        (higham9_2_complexRowColPermutedMatrix A
          (higham9_8_extendTrailingPerm sigma)
          (higham9_8_extendTrailingPerm tau)) =
      higham9_2_complexRowColPermutedMatrix
        (higham9_8_complexFirstSchurComplement A) sigma tau := by
  ext i j
  simp [higham9_8_complexFirstSchurComplement, higham9_2_complexRowColPermutedMatrix]

/-- **Theorem 9.8 / cumulative complete-pivoting support**, every nonsingular
real matrix admits an exact cumulative complete-pivoting certificate
`P A Q = L U`.

The proof follows the recursive complete-pivoting choices already used for the
`U` trace: move a nonzero complete pivot to `(0,0)`, recurse on the first Schur
complement, then lift the trailing row and column permutations into cumulative
permutations of the original matrix. -/
theorem higham9_8_exists_CompletePermutedLUFactSpec_of_det_ne_zero :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∃ L U : Fin n → Fin n → ℝ,
      ∃ sigma tau : Fin n → Fin n,
        higham9_2_CompletePermutedLUFactSpec n A L U sigma tau := by
  intro n
  induction n with
  | zero =>
      intro A _hdet
      let empty : Fin 0 → Fin 0 := fun i => Fin.elim0 i
      have hempty : IsPermutation 0 empty := by
        constructor
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
      refine ⟨(fun i j => Fin.elim0 i), (fun i j => Fin.elim0 i), empty, empty, ?_⟩
      refine ⟨hempty, ?_⟩
      refine
        { perm := hempty
          L_diag := ?_
          L_upper_zero := ?_
          U_lower_zero := ?_
          product_eq := ?_ }
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      intro A hdet
      obtain ⟨r, s, hchoice, hpivot⟩ :=
        higham9_1_exists_first_completePivotChoice_pivot_ne_zero_of_det_ne_zero
          A hdet
      let sigma₀ : Fin (m + 1) → Fin (m + 1) :=
        higham9_7_firstPivotRowSwap r
      let tau₀ : Fin (m + 1) → Fin (m + 1) :=
        higham9_7_firstPivotRowSwap s
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
        higham9_2_rowColPermutedMatrix A sigma₀ tau₀
      let S : Fin m → Fin m → ℝ := luFirstSchurComplement Aperm
      have hdetS :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
        simpa [S, Aperm, sigma₀, tau₀] using
          higham9_1_firstCompletePivotSchurComplement_det_ne_zero_of_det_ne_zero
            A hpivot hdet
      obtain ⟨L₁, U₁, sigma₁, tau₁, hLU₁⟩ := ih (A := S) hdetS
      let sigmaExt : Fin (m + 1) → Fin (m + 1) :=
        higham9_8_extendTrailingPerm sigma₁
      let tauExt : Fin (m + 1) → Fin (m + 1) :=
        higham9_8_extendTrailingPerm tau₁
      let sigma : Fin (m + 1) → Fin (m + 1) := fun i => sigma₀ (sigmaExt i)
      let tau : Fin (m + 1) → Fin (m + 1) := fun i => tau₀ (tauExt i)
      let B : Fin (m + 1) → Fin (m + 1) → ℝ :=
        higham9_2_rowColPermutedMatrix Aperm sigmaExt tauExt
      let L : Fin (m + 1) → Fin (m + 1) → ℝ := luFirstStepL B L₁
      let U : Fin (m + 1) → Fin (m + 1) → ℝ := luFirstStepU B U₁
      have hsigmaExt : IsPermutation (m + 1) sigmaExt :=
        higham9_8_extendTrailingPerm_isPermutation hLU₁.2.perm
      have htauExt : IsPermutation (m + 1) tauExt :=
        higham9_8_extendTrailingPerm_isPermutation hLU₁.1
      have hsigma : IsPermutation (m + 1) sigma :=
        higham9_8_isPermutation_comp
          (by
            show IsPermutation (m + 1) (higham9_7_firstPivotRowSwap r)
            exact higham9_7_firstPivotRowSwap_isPermutation r)
          hsigmaExt
      have htau : IsPermutation (m + 1) tau :=
        higham9_8_isPermutation_comp
          (by
            show IsPermutation (m + 1) (higham9_7_firstPivotRowSwap s)
            exact higham9_7_firstPivotRowSwap_isPermutation s)
          htauExt
      have hpivotB : B 0 0 ≠ 0 := by
        simpa [B, Aperm, sigma₀, tau₀, sigmaExt, tauExt,
          higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
          higham9_2_colPermutedMatrix, higham9_7_firstPivotRowSwap] using hpivot
      have hschur :
          luFirstSchurComplement B =
            higham9_2_rowColPermutedMatrix S sigma₁ tau₁ := by
        simpa [B, S] using
          higham9_8_luFirstSchurComplement_trailingPerm Aperm sigma₁ tau₁
      have hLU₁_plain :
          LUFactSpec m (higham9_2_rowColPermutedMatrix S sigma₁ tau₁) L₁ U₁ :=
        higham9_2_completePermutedLUFactSpec_to_LUFactSpec hLU₁
      have hS_B : LUFactSpec m (luFirstSchurComplement B) L₁ U₁ := by
        simpa [hschur] using hLU₁_plain
      have hLU_B : LUFactSpec (m + 1) B L U :=
        LUFactSpec.of_firstSchurComplement_explicit hpivotB hS_B
      refine ⟨L, U, sigma, tau, ?_⟩
      refine ⟨htau, ?_⟩
      refine
        { perm := hsigma
          L_diag := hLU_B.L_diag
          L_upper_zero := hLU_B.L_upper_zero
          U_lower_zero := hLU_B.U_lower_zero
          product_eq := ?_ }
      intro i j
      have h := hLU_B.product_eq i j
      simpa [L, U, B, Aperm, sigma, tau, sigma₀, tau₀,
        higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
        higham9_2_colPermutedMatrix] using h

/-- **Theorem 9.8 / equation (9.13) support**, every nonsingular complex
matrix admits an exact cumulative complete-pivoting certificate `P A Q = L U`.

This is the complex analogue of
`higham9_8_exists_CompletePermutedLUFactSpec_of_det_ne_zero`, specialized to
the certificate surface needed for the Fourier/Vandermonde equation (9.13)
branch. -/
theorem higham9_8_exists_ComplexCompletePermutedLUFactSpec_of_det_ne_zero :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℂ},
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) ≠ 0 →
      ∃ L U : Fin n → Fin n → ℂ,
      ∃ sigma tau : Fin n → Fin n,
        higham9_8_ComplexCompletePermutedLUFactSpec n A L U sigma tau := by
  intro n
  induction n with
  | zero =>
      intro A _hdet
      let empty : Fin 0 → Fin 0 := fun i => Fin.elim0 i
      let Z : Fin 0 → Fin 0 → ℂ := fun i => Fin.elim0 i
      have hempty : IsPermutation 0 empty := by
        constructor
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
      refine ⟨Z, Z, empty, empty, ?_⟩
      refine
        { row_perm := hempty
          col_perm := hempty
          L_diag := ?_
          L_upper_zero := ?_
          U_lower_zero := ?_
          product_eq := ?_ }
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      intro A hdet
      obtain ⟨r, s, hchoice, hpivot⟩ :=
        higham9_8_exists_first_complexCompletePivotChoice_pivot_ne_zero_of_det_ne_zero
          A hdet
      let sigma₀ : Fin (m + 1) → Fin (m + 1) :=
        higham9_7_firstPivotRowSwap r
      let tau₀ : Fin (m + 1) → Fin (m + 1) :=
        higham9_7_firstPivotRowSwap s
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_2_complexRowColPermutedMatrix A sigma₀ tau₀
      let S : Fin m → Fin m → ℂ := higham9_8_complexFirstSchurComplement Aperm
      have hpivotAperm : Aperm 0 0 ≠ 0 := by
        simpa [Aperm, sigma₀, tau₀, higham9_2_complexRowColPermutedMatrix,
          higham9_7_firstPivotRowSwap] using hpivot
      have hdetAperm :
          Matrix.det (Matrix.of Aperm : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0 := by
        simpa [Aperm, sigma₀, tau₀] using
          higham9_8_complex_firstPivotRowColSwap_det_ne_zero A r s hdet
      have hdetS :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℂ) ≠ 0 := by
        simpa [S] using
          higham9_8_complexFirstSchurComplement_det_ne_zero
            Aperm hpivotAperm hdetAperm
      obtain ⟨L₁, U₁, sigma₁, tau₁, hLU₁⟩ := ih (A := S) hdetS
      let sigmaExt : Fin (m + 1) → Fin (m + 1) :=
        higham9_8_extendTrailingPerm sigma₁
      let tauExt : Fin (m + 1) → Fin (m + 1) :=
        higham9_8_extendTrailingPerm tau₁
      let sigma : Fin (m + 1) → Fin (m + 1) := fun i => sigma₀ (sigmaExt i)
      let tau : Fin (m + 1) → Fin (m + 1) := fun i => tau₀ (tauExt i)
      let B : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_2_complexRowColPermutedMatrix Aperm sigmaExt tauExt
      let L : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_8_complexLUFirstStepL B L₁
      let U : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_8_complexLUFirstStepU B U₁
      have hsigmaExt : IsPermutation (m + 1) sigmaExt :=
        higham9_8_extendTrailingPerm_isPermutation hLU₁.row_perm
      have htauExt : IsPermutation (m + 1) tauExt :=
        higham9_8_extendTrailingPerm_isPermutation hLU₁.col_perm
      have hsigma : IsPermutation (m + 1) sigma :=
        higham9_8_isPermutation_comp
          (by
            show IsPermutation (m + 1) (higham9_7_firstPivotRowSwap r)
            exact higham9_7_firstPivotRowSwap_isPermutation r)
          hsigmaExt
      have htau : IsPermutation (m + 1) tau :=
        higham9_8_isPermutation_comp
          (by
            show IsPermutation (m + 1) (higham9_7_firstPivotRowSwap s)
            exact higham9_7_firstPivotRowSwap_isPermutation s)
          htauExt
      have hpivotB : B 0 0 ≠ 0 := by
        simpa [B, Aperm, sigma₀, tau₀, sigmaExt, tauExt,
          higham9_2_complexRowColPermutedMatrix, higham9_7_firstPivotRowSwap] using hpivot
      have hschur :
          higham9_8_complexFirstSchurComplement B =
            higham9_2_complexRowColPermutedMatrix S sigma₁ tau₁ := by
        simpa [B, S] using
          higham9_8_complexFirstSchurComplement_trailingPerm Aperm sigma₁ tau₁
      have hLU₁_plain :
          higham9_8_ComplexLUFactSpec m
            (higham9_2_complexRowColPermutedMatrix S sigma₁ tau₁) L₁ U₁ :=
        higham9_8_complexCompletePermutedLUFactSpec_to_LUFactSpec hLU₁
      have hS_B :
          higham9_8_ComplexLUFactSpec m
            (higham9_8_complexFirstSchurComplement B) L₁ U₁ := by
        simpa [hschur] using hLU₁_plain
      have hLU_B :
          higham9_8_ComplexLUFactSpec (m + 1) B L U :=
        higham9_8_complexLUFactSpec_of_firstSchurComplement_explicit hpivotB hS_B
      refine ⟨L, U, sigma, tau, ?_⟩
      refine
        { row_perm := hsigma
          col_perm := htau
          L_diag := hLU_B.L_diag
          L_upper_zero := hLU_B.L_upper_zero
          U_lower_zero := hLU_B.U_lower_zero
          product_eq := ?_ }
      intro i j
      have h := hLU_B.product_eq i j
      simpa [L, U, B, Aperm, sigma, tau, sigma₀, tau₀,
        higham9_2_complexRowColPermutedMatrix] using h

/-- A complex function-shaped right inverse gives a nonzero determinant for the
corresponding Mathlib matrix. -/
theorem higham9_8_complex_det_ne_zero_of_isRightInverse {n : ℕ}
    (A A_inv : Fin n → Fin n → ℂ)
    (hRight : higham9_8_ComplexIsRightInverse n A A_inv) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
  exact
    Matrix.det_ne_zero_of_right_inverse
      (A := (Matrix.of A : Matrix (Fin n) (Fin n) ℂ))
      (B := (Matrix.of A_inv : Matrix (Fin n) (Fin n) ℂ))
      (by
        ext i j
        rw [Matrix.mul_apply, Matrix.one_apply]
        exact hRight i j)

/-- **Equation (9.13)**, end-to-end complex Fourier/Vandermonde certificate
existence with growth lower bound.

The inverse formula makes the Fourier/Vandermonde matrix nonsingular; the
complex cumulative complete-pivoting construction supplies an exact `P A Q = L U`
certificate; and the final-pivot bridge proves `n <= rho`. -/
theorem higham9_13_exists_fourierVandermonde_complexCompletePermutedLUFactSpec_growth_ge_card
    {n : ℕ} (hn : 0 < n) :
    ∃ L U : Fin n → Fin n → ℂ,
    ∃ sigma tau : Fin n → Fin n,
      higham9_8_ComplexCompletePermutedLUFactSpec n
        (higham9_13_fourierVandermonde n) L U sigma tau ∧
      (n : ℝ) ≤ higham9_13_complexGrowthFactorEntry hn
        (higham9_13_fourierVandermonde n) U := by
  let V : Fin n → Fin n → ℂ := higham9_13_fourierVandermonde n
  let V_inv : Fin n → Fin n → ℂ :=
    higham9_13_fourierVandermondeScaledAdjoint n
  have hRight : higham9_8_ComplexIsRightInverse n V V_inv := by
    exact (higham9_13_fourierVandermonde_inverse_formula n).2
  have hdet :
      Matrix.det (Matrix.of V : Matrix (Fin n) (Fin n) ℂ) ≠ 0 :=
    higham9_8_complex_det_ne_zero_of_isRightInverse V V_inv hRight
  obtain ⟨L, U, sigma, tau, hLU⟩ :=
    higham9_8_exists_ComplexCompletePermutedLUFactSpec_of_det_ne_zero
      (A := V) hdet
  refine ⟨L, U, sigma, tau, ?_, ?_⟩
  · simpa [V] using hLU
  · simpa [V] using
      higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card_of_completePermutedLUFactSpec
        hn L U sigma tau hLU

/-- **Theorem 9.8**, source-facing real complete-pivoting lower-bound
existence form.

For every nonsingular real matrix with a visible right inverse, the cumulative
complete-pivoting construction above supplies `P A Q = L U`; the already
proved final-pivot inverse-entry argument then gives
`theta(A) <= growthFactorEntry(A,U)`. -/
theorem higham9_8_exists_completePivoting_growth_factor_ge_theta_real {n : ℕ}
    (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hRight : IsRightInverse n A A_inv)
    (hA : 0 < maxEntryNorm hn A)
    (hAinv : 0 < maxEntryNorm hn A_inv) :
    ∃ L U : Fin n → Fin n → ℝ,
    ∃ sigma tau : Fin n → Fin n,
      higham9_2_CompletePermutedLUFactSpec n A L U sigma tau ∧
        1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv) ≤
          growthFactorEntry hn A U hA := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero 0 hn).elim
  | succ m =>
      obtain ⟨L, U, sigma, tau, hLU⟩ :=
        higham9_8_exists_CompletePermutedLUFactSpec_of_det_ne_zero
          (A := A) hdet
      refine ⟨L, U, sigma, tau, hLU, ?_⟩
      exact
        higham9_8_growth_factor_ge_theta_of_completePermutedLUFactSpec_right_inverse
          A A_inv L U sigma tau hLU hRight hA hAinv

/-- **Problem 9.11**, the flattened sine block has an actual cumulative
complete-pivoting certificate whose entrywise growth is at least `n + 1`.

This closes the local complete-pivoting witness `rho(B) >= theta(B)` for the
source sine-block construction.  It does not assert the later global bounded
supremum `g(2n)` without the separate Wilkinson complete-pivoting upper-bound
family. -/
theorem higham9_11_exists_completePivoting_sine_block_growth_ge_succ
    {n : ℕ} (hn : 0 < n) :
    ∃ L U : Fin (2 * n) → Fin (2 * n) → ℝ,
    ∃ sigma tau : Fin (2 * n) → Fin (2 * n),
      higham9_2_CompletePermutedLUFactSpec (2 * n)
        (higham9_11_flattenTwoBlock hn
          (higham9_11_blockMatrix (higham9_12_sineMatrix n)))
        L U sigma tau ∧
      (n : ℝ) + 1 ≤
        growthFactorEntry (by omega : 0 < 2 * n)
          (higham9_11_flattenTwoBlock hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n)))
          U
          (by
            rw [higham9_11_flatten_blockMatrix_maxEntryNorm_eq hn]
            exact higham9_12_sineMatrix_maxEntryNorm_pos hn) := by
  let B : Fin (2 * n) → Fin (2 * n) → ℝ :=
    higham9_11_flattenTwoBlock hn
      (higham9_11_blockMatrix (higham9_12_sineMatrix n))
  let B_inv : Fin (2 * n) → Fin (2 * n) → ℝ :=
    higham9_11_flattenTwoBlock hn
      (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n))
  have hsineRight :
      IsRightInverse n (higham9_12_sineMatrix n) (higham9_12_sineMatrix n) :=
    (higham9_12_sineMatrix_inverse_formula hn).2
  have hBlockRight :
      ∀ bi bj : Fin 2, ∀ i j : Fin n,
        blockMatProd
            (higham9_11_blockMatrix (higham9_12_sineMatrix n))
            (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n))
            bi bj i j =
          if bi = bj then if i = j then 1 else 0 else 0 :=
    higham9_11_blockInverseCandidate_right
      (higham9_12_sineMatrix n) (higham9_12_sineMatrix n) hsineRight
  have hRight : IsRightInverse (2 * n) B B_inv := by
    simpa [B, B_inv] using
      higham9_11_flattenTwoBlock_right_inverse hn hBlockRight
  have hdet :
      Matrix.det (Matrix.of B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) ≠ 0 :=
    higham9_det_ne_zero_of_isRightInverse B B_inv hRight
  have hBpos : 0 < maxEntryNorm (by omega : 0 < 2 * n) B := by
    dsimp [B]
    rw [higham9_11_flatten_blockMatrix_maxEntryNorm_eq hn]
    exact higham9_12_sineMatrix_maxEntryNorm_pos hn
  have hBinvpos : 0 < maxEntryNorm (by omega : 0 < 2 * n) B_inv := by
    dsimp [B_inv]
    rw [higham9_11_flatten_blockInverseCandidate_maxEntryNorm_eq hn]
    exact mul_pos (by norm_num) (higham9_12_sineMatrix_maxEntryNorm_pos hn)
  obtain ⟨L, U, sigma, tau, hLU, htheta_le_growth⟩ :=
    higham9_8_exists_completePivoting_growth_factor_ge_theta_real
      (hn := by omega) B B_inv hdet hRight hBpos hBinvpos
  refine ⟨L, U, sigma, tau, ?_⟩
  refine ⟨by simpa [B] using hLU, ?_⟩
  have hsineTheta :
      (n : ℝ) + 1 ≤
        1 /
          (maxEntryNorm (by omega : 0 < 2 * n) B *
            maxEntryNorm (by omega : 0 < 2 * n) B_inv) := by
    dsimp [B, B_inv]
    simpa [higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm] using
      higham9_11_sine_block_theta_candidate_ge_succ hn
  have hfinal := le_trans hsineTheta htheta_le_growth
  simpa [B, growthFactorEntry] using hfinal

/-- **Problem 9.11**, the set of entry-growth values obtained by exact
complete-pivoting certificates for the flattened sine block
`[[S_n,S_n],[S_n,-S_n]]`.

This is a source-facing local object: it ranges only over actual
`PAQ = LU` certificates for the concrete flattened matrix, and does not define
the still-open global growth function `g(2n)`. -/
def higham9_11_sineBlockCompletePivotingGrowthSet {n : ℕ} (hn : 0 < n) :
    Set ℝ :=
  { r | ∃ L U : Fin (2 * n) → Fin (2 * n) → ℝ,
      ∃ sigma tau : Fin (2 * n) → Fin (2 * n),
        higham9_2_CompletePermutedLUFactSpec (2 * n)
          (higham9_11_flattenTwoBlock hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n)))
          L U sigma tau ∧
        r =
          growthFactorEntry (by omega : 0 < 2 * n)
            (higham9_11_flattenTwoBlock hn
              (higham9_11_blockMatrix (higham9_12_sineMatrix n)))
            U
            (by
              rw [higham9_11_flatten_blockMatrix_maxEntryNorm_eq hn]
              exact higham9_12_sineMatrix_maxEntryNorm_pos hn) }

/-- **Problem 9.11**, the concrete sine block contributes an actual
complete-pivoting certificate growth value at least `n + 1`. -/
theorem higham9_11_sineBlockCompletePivotingGrowthSet_exists_ge_succ
    {n : ℕ} (hn : 0 < n) :
    ∃ r ∈ higham9_11_sineBlockCompletePivotingGrowthSet hn,
      (n : ℝ) + 1 ≤ r := by
  obtain ⟨L, U, sigma, tau, hLU, hgrowth⟩ :=
    higham9_11_exists_completePivoting_sine_block_growth_ge_succ hn
  refine
    ⟨growthFactorEntry (by omega : 0 < 2 * n)
        (higham9_11_flattenTwoBlock hn
          (higham9_11_blockMatrix (higham9_12_sineMatrix n)))
        U
        (by
          rw [higham9_11_flatten_blockMatrix_maxEntryNorm_eq hn]
          exact higham9_12_sineMatrix_maxEntryNorm_pos hn),
      ?_, hgrowth⟩
  exact ⟨L, U, sigma, tau, hLU, rfl⟩

/-- **Problem 9.11**, fixed-matrix lower-bound bridge.

Any real number that bounds all exact complete-pivoting certificate growth
values for the concrete sine block is at least `n + 1`.  The missing global
source step is to show that the book's `g(2n)` is such an upper bound. -/
theorem higham9_11_sineBlockCompletePivotingGrowth_upper_bound_ge_succ
    {n : ℕ} (hn : 0 < n) (g2n : ℝ)
    (hg :
      ∀ r ∈ higham9_11_sineBlockCompletePivotingGrowthSet hn, r ≤ g2n) :
    (n : ℝ) + 1 ≤ g2n := by
  obtain ⟨r, hr, hle⟩ :=
    higham9_11_sineBlockCompletePivotingGrowthSet_exists_ge_succ hn
  exact le_trans hle (hg r hr)

/-- **Problem 9.11 / equation (9.15)**, certificate-level complete-pivoting
growth values for one source matrix.

This is not an arbitrary growth map: each value comes from an explicit exact
`PAQ = LU` certificate.  The still-open Wilkinson step is the uniform
boundedness of these values by the source complete-pivoting bound. -/
def higham9_completePivotingCertificateGrowthSet {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hApos : 0 < maxEntryNorm hn A) : Set ℝ :=
  { r | ∃ L U : Fin n → Fin n → ℝ,
      ∃ sigma tau : Fin n → Fin n,
        higham9_2_CompletePermutedLUFactSpec n A L U sigma tau ∧
          r = growthFactorEntry hn A U hApos }

/-- **Problem 9.11 / equation (9.15)**, all certificate-level
complete-pivoting growth values in dimension `n`. -/
def higham9_completePivotingCertificateGrowthValues (n : ℕ) : Set ℝ :=
  { r | ∃ hn : 0 < n,
      ∃ A : Fin n → Fin n → ℝ,
      ∃ hApos : 0 < maxEntryNorm hn A,
        r ∈ higham9_completePivotingCertificateGrowthSet hn A hApos }

/-- **Problem 9.11 / equation (9.15)**, the certificate-level global growth
supremum corresponding to `g(n)` once Wilkinson boundedness is supplied. -/
noncomputable def higham9_completePivotingCertificateGrowthSup (n : ℕ) : ℝ :=
  sSup (higham9_completePivotingCertificateGrowthValues n)

/-- **Problem 9.11 / equation (9.15)**, every certificate-level
complete-pivoting growth value is bounded by the certificate-level supremum
when the value family is bounded above. -/
theorem higham9_completePivotingCertificateGrowth_le_sup {n : ℕ}
    (hBdd : BddAbove (higham9_completePivotingCertificateGrowthValues n))
    {r : ℝ} (hr : r ∈ higham9_completePivotingCertificateGrowthValues n) :
    r ≤ higham9_completePivotingCertificateGrowthSup n := by
  exact le_csSup hBdd hr

/-- **Problem 9.11**, the certificate-level complete-pivoting value set
contains the flattened sine-block lower-bound value. -/
theorem higham9_11_completePivotingCertificateGrowthValues_exists_ge_succ
    {n : ℕ} (hn : 0 < n) :
    ∃ r ∈ higham9_completePivotingCertificateGrowthValues (2 * n),
      (n : ℝ) + 1 ≤ r := by
  obtain ⟨r, hr, hle⟩ :=
    higham9_11_sineBlockCompletePivotingGrowthSet_exists_ge_succ hn
  let B : Fin (2 * n) → Fin (2 * n) → ℝ :=
    higham9_11_flattenTwoBlock hn
      (higham9_11_blockMatrix (higham9_12_sineMatrix n))
  have hBpos : 0 < maxEntryNorm (by omega : 0 < 2 * n) B := by
    dsimp [B]
    rw [higham9_11_flatten_blockMatrix_maxEntryNorm_eq hn]
    exact higham9_12_sineMatrix_maxEntryNorm_pos hn
  refine ⟨r, ?_, hle⟩
  rcases hr with ⟨L, U, sigma, tau, hLU, hr_eq⟩
  refine ⟨by omega, B, hBpos, ?_⟩
  refine ⟨L, U, sigma, tau, ?_⟩
  refine ⟨by simpa [B] using hLU, ?_⟩
  rw [hr_eq]

/-- **Problem 9.11**, source-shaped lower-bound consequence for the
certificate-level `g(2n)` surface.

The proof uses the concrete flattened sine-block complete-pivoting certificate.
The explicit hypothesis `hBdd` is the remaining Wilkinson complete-pivoting
upper-bound/boundedness theorem; no arbitrary `rhoC` map is introduced here. -/
theorem higham9_11_completePivotingCertificateGrowthSup_ge_succ
    {n : ℕ} (hn : 0 < n)
    (hBdd :
      BddAbove (higham9_completePivotingCertificateGrowthValues (2 * n))) :
    (n : ℝ) + 1 ≤ higham9_completePivotingCertificateGrowthSup (2 * n) := by
  obtain ⟨r, hr, hle⟩ :=
    higham9_11_completePivotingCertificateGrowthValues_exists_ge_succ hn
  exact le_trans hle
    (higham9_completePivotingCertificateGrowth_le_sup hBdd hr)

/-- **Theorem 9.8 / complete-pivoting `U` trace**, a recursive exact
complete-pivoting trace that exposes the final upper-factor rows.  Each step
chooses a first-stage complete pivot, moves it to `(0,0)` by row and column
swaps, stores the permuted pivot row in `U`, and recurses on the first Schur
complement. -/
inductive higham9_8_CompletePivotGECPUTrace :
    (n : ℕ) → (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Prop
  | done {A U : Fin 0 → Fin 0 → ℝ} :
      higham9_8_CompletePivotGECPUTrace 0 A U
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {r s : Fin (m + 1)} {U₁ : Fin m → Fin m → ℝ}
      (hchoice : higham9_1_completePivotChoice A 0 r s)
      (hpivot : A r s ≠ 0)
      (hnext :
        higham9_8_CompletePivotGECPUTrace m
          (luFirstSchurComplement
            (higham9_2_rowColPermutedMatrix A
              (higham9_7_firstPivotRowSwap r)
              (higham9_7_firstPivotRowSwap s))) U₁) :
      higham9_8_CompletePivotGECPUTrace (m + 1) A
        (luFirstStepU
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s)) U₁)

/-- **Theorem 9.8 / complete-pivoting `U` trace**, the exposed `U` rows are
upper triangular along the recursive complete-pivoting trace. -/
theorem higham9_8_CompletePivotGECPUTrace_upper_zero :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_8_CompletePivotGECPUTrace n A U →
      ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro i
      exact Fin.elim0 i
  | step _hchoice _hpivot _hnext ih =>
      intro i j hij
      by_cases hi : i = 0
      · subst i
        exact (Nat.not_lt_zero _ hij).elim
      · by_cases hj : j = 0
        · subst j
          simp [luFirstStepU, hi]
        · have hpred : (j.pred hj).val < (i.pred hi).val := by
            have hival := Fin.val_pred i hi
            have hjval := Fin.val_pred j hj
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
            omega
          have hrec := ih (i.pred hi) (j.pred hj) hpred
          simpa [luFirstStepU, hi, hj] using hrec

/-- **Theorem 9.8 / complete-pivoting trace support**, the exposed `U` rows
of any recursive complete-pivoting trace satisfy the same elementary
`2^(n-1)` max-entry bound as the partial-pivoting trace.  This is a boundedness
dependency for the source `g(n)` surface; it is not Wilkinson's sharper
complete-pivoting product bound (9.14). -/
theorem higham9_8_CompletePivotGECPUTrace_entry_abs_le_pow_two :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_8_CompletePivotGECPUTrace n A U →
      ∀ (hn : 0 < n) (i j : Fin n),
        |U i j| ≤ (2 : ℝ) ^ (n - 1) * maxEntryNorm hn A := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro hn
      omega
  | step hchoice hpivot hnext ih =>
      rename_i m A r s U₁
      intro hn i j
      let sigma := higham9_7_firstPivotRowSwap r
      let tau := higham9_7_firstPivotRowSwap s
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
        higham9_2_rowColPermutedMatrix A sigma tau
      by_cases hi : i = 0
      · subst i
        have hrow : |Aperm 0 j| ≤ maxEntryNorm (Nat.succ_pos m) A := by
          simpa [Aperm, higham9_2_rowColPermutedMatrix,
            higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix, sigma, tau,
            higham9_7_firstPivotRowSwap] using
            entry_le_maxEntryNorm (Nat.succ_pos m) A r (tau j)
        have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ m := by
          simpa using
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le m)
        have hM_nonneg : 0 ≤ maxEntryNorm (Nat.succ_pos m) A :=
          maxEntryNorm_nonneg (Nat.succ_pos m) A
        have hrow_pow :
            |Aperm 0 j| ≤ (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
          calc
            |Aperm 0 j| ≤ maxEntryNorm (Nat.succ_pos m) A := hrow
            _ = (1 : ℝ) * maxEntryNorm (Nat.succ_pos m) A := by ring
            _ ≤ (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A :=
                mul_le_mul_of_nonneg_right hpow_ge_one hM_nonneg
        simpa [Aperm, luFirstStepU] using hrow_pow
      · by_cases hj : j = 0
        · subst j
          have hnonneg :
              0 ≤ (2 : ℝ) ^ ((m + 1) - 1) *
                  maxEntryNorm (Nat.succ_pos m) A :=
            mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((m + 1) - 1))
              (maxEntryNorm_nonneg (Nat.succ_pos m) A)
          simpa [Aperm, luFirstStepU, hi] using hnonneg
        · have hm : 0 < m := by
            by_contra hm0
            have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
            subst hmzero
            have hival : i.val = 0 := by omega
            exact hi (Fin.ext hival)
          have hrec := ih hm (i.pred hi) (j.pred hj)
          let S : Fin m → Fin m → ℝ :=
            luFirstSchurComplement Aperm
          have hS_bound :
              maxEntryNorm hm S ≤ 2 * maxEntryNorm (Nat.succ_pos m) A := by
            simpa [S, Aperm, sigma, tau] using
              higham9_8_completePivot_firstSchurComplement_maxEntryNorm_le_two
                hm A hchoice hpivot
          have hcoef_nonneg : 0 ≤ (2 : ℝ) ^ (m - 1) :=
            pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (m - 1)
          have hpow : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
            have hmidx : m = (m - 1) + 1 := by omega
            calc
              (2 : ℝ) ^ m = (2 : ℝ) ^ ((m - 1) + 1) :=
                congrArg (fun k : ℕ => (2 : ℝ) ^ k) hmidx
              _ = (2 : ℝ) ^ (m - 1) * 2 := by
                exact pow_succ (2 : ℝ) (m - 1)
          have hpow_step :
              (2 : ℝ) ^ (m - 1) * (2 * maxEntryNorm (Nat.succ_pos m) A) =
                (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
            rw [hpow]
            ring
          have htail :
              |U₁ (i.pred hi) (j.pred hj)| ≤
                (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
            calc
              |U₁ (i.pred hi) (j.pred hj)|
                  ≤ (2 : ℝ) ^ (m - 1) * maxEntryNorm hm S := by
                      simpa [S] using hrec
              _ ≤ (2 : ℝ) ^ (m - 1) *
                    (2 * maxEntryNorm (Nat.succ_pos m) A) :=
                  mul_le_mul_of_nonneg_left hS_bound hcoef_nonneg
              _ = (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := hpow_step
          simpa [Aperm, luFirstStepU, hi, hj] using htail

/-- **Theorem 9.8 / complete-pivoting trace support**, trace-level elementary
complete-pivoting growth bound. -/
theorem higham9_8_CompletePivotGECPUTrace_growthFactorEntry_le_pow_two {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (htrace : higham9_8_CompletePivotGECPUTrace n A U) :
    growthFactorEntry hn A U hAmax ≤ (2 : ℝ) ^ (n - 1) := by
  apply growthFactorEntry_le_of_entry_bound_factor hn A U ((2 : ℝ) ^ (n - 1)) hAmax
  exact higham9_8_CompletePivotGECPUTrace_entry_abs_le_pow_two htrace hn

/-- **Problem 9.11 / equation (9.15)**, trace-level complete-pivoting growth
values in dimension `n`.

This set ranges over the recursive complete-pivoting `U` traces formalized in
this file, not over arbitrary `PAQ = LU` certificates. -/
def higham9_completePivotingUTraceGrowthValues (n : ℕ) : Set ℝ :=
  { r | ∃ hn : 0 < n,
      ∃ A U : Fin n → Fin n → ℝ,
      ∃ hApos : 0 < maxEntryNorm hn A,
        higham9_8_CompletePivotGECPUTrace n A U ∧
          r = growthFactorEntry hn A U hApos }

/-- **Problem 9.11 / equation (9.15)**, trace-level complete-pivoting growth
supremum. -/
noncomputable def higham9_completePivotingUTraceGrowthSup (n : ℕ) : ℝ :=
  sSup (higham9_completePivotingUTraceGrowthValues n)

/-- **Problem 9.11 / equation (9.15)**, the trace-level complete-pivoting
growth values are bounded above by the elementary `2^(n-1)` bound. -/
theorem higham9_completePivotingUTraceGrowthValues_bddAbove (n : ℕ) :
    BddAbove (higham9_completePivotingUTraceGrowthValues n) := by
  refine ⟨(2 : ℝ) ^ (n - 1), ?_⟩
  intro r hr
  rcases hr with ⟨hn, A, U, hApos, htrace, rfl⟩
  exact higham9_8_CompletePivotGECPUTrace_growthFactorEntry_le_pow_two
    hn A U hApos htrace

/-- **Problem 9.11 / equation (9.15)**, every trace-level complete-pivoting
growth value is bounded by the trace-level supremum. -/
theorem higham9_completePivotingUTraceGrowth_le_sup {n : ℕ} {r : ℝ}
    (hr : r ∈ higham9_completePivotingUTraceGrowthValues n) :
    r ≤ higham9_completePivotingUTraceGrowthSup n := by
  exact le_csSup (higham9_completePivotingUTraceGrowthValues_bddAbove n) hr

/-- **Theorem 9.8 / Problem 9.11 bridge**, every recursive complete-pivoting
`U` trace determines a cumulative complete-pivoting `PAQ = LU` certificate
whose certificate `U` has max-entry norm no larger than the trace `U`.

The certificate `U` is not definitionally the trace `U`, because cumulative
trailing column permutations reorder earlier pivot rows.  The max-entry norm
comparison is the invariant needed for the source growth-factor surface. -/
theorem higham9_8_CompletePivotGECPUTrace_exists_CompletePermutedLUFactSpec_maxEntryNorm_le :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_8_CompletePivotGECPUTrace n A U →
      ∃ L Uc : Fin n → Fin n → ℝ,
      ∃ sigma tau : Fin n → Fin n,
        higham9_2_CompletePermutedLUFactSpec n A L Uc sigma tau ∧
          ∀ hn : 0 < n, maxEntryNorm hn Uc ≤ maxEntryNorm hn U := by
  intro n A U htrace
  induction htrace with
  | done =>
      let empty : Fin 0 → Fin 0 := fun i => Fin.elim0 i
      let Z : Fin 0 → Fin 0 → ℝ := fun i => Fin.elim0 i
      have hempty : IsPermutation 0 empty := by
        constructor
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
      refine ⟨Z, Z, empty, empty, ?_, ?_⟩
      · refine ⟨hempty, ?_⟩
        refine
          { perm := hempty
            L_diag := ?_
            L_upper_zero := ?_
            U_lower_zero := ?_
            product_eq := ?_ }
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
      · intro hn
        exact (Nat.not_lt_zero 0 hn).elim
  | step hchoice hpivot hnext ih =>
      rename_i m A r s U₁
      obtain ⟨L₁, Uc₁, sigma₁, tau₁, hLU₁, hmax₁⟩ := ih
      let sigma₀ : Fin (m + 1) → Fin (m + 1) :=
        higham9_7_firstPivotRowSwap r
      let tau₀ : Fin (m + 1) → Fin (m + 1) :=
        higham9_7_firstPivotRowSwap s
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
        higham9_2_rowColPermutedMatrix A sigma₀ tau₀
      let S : Fin m → Fin m → ℝ := luFirstSchurComplement Aperm
      let sigmaExt : Fin (m + 1) → Fin (m + 1) :=
        higham9_8_extendTrailingPerm sigma₁
      let tauExt : Fin (m + 1) → Fin (m + 1) :=
        higham9_8_extendTrailingPerm tau₁
      let sigma : Fin (m + 1) → Fin (m + 1) := fun i => sigma₀ (sigmaExt i)
      let tau : Fin (m + 1) → Fin (m + 1) := fun i => tau₀ (tauExt i)
      let B : Fin (m + 1) → Fin (m + 1) → ℝ :=
        higham9_2_rowColPermutedMatrix Aperm sigmaExt tauExt
      let L : Fin (m + 1) → Fin (m + 1) → ℝ := luFirstStepL B L₁
      let Uc : Fin (m + 1) → Fin (m + 1) → ℝ := luFirstStepU B Uc₁
      let Utrace : Fin (m + 1) → Fin (m + 1) → ℝ := luFirstStepU Aperm U₁
      have hsigmaExt : IsPermutation (m + 1) sigmaExt :=
        higham9_8_extendTrailingPerm_isPermutation hLU₁.2.perm
      have htauExt : IsPermutation (m + 1) tauExt :=
        higham9_8_extendTrailingPerm_isPermutation hLU₁.1
      have hsigma : IsPermutation (m + 1) sigma :=
        higham9_8_isPermutation_comp
          (by
            show IsPermutation (m + 1) (higham9_7_firstPivotRowSwap r)
            exact higham9_7_firstPivotRowSwap_isPermutation r)
          hsigmaExt
      have htau : IsPermutation (m + 1) tau :=
        higham9_8_isPermutation_comp
          (by
            show IsPermutation (m + 1) (higham9_7_firstPivotRowSwap s)
            exact higham9_7_firstPivotRowSwap_isPermutation s)
          htauExt
      have hpivotB : B 0 0 ≠ 0 := by
        simpa [B, Aperm, sigmaExt, tauExt, higham9_2_rowColPermutedMatrix,
          higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix] using hpivot
      have hschur :
          luFirstSchurComplement B =
            higham9_2_rowColPermutedMatrix S sigma₁ tau₁ := by
        simpa [B, S] using
          higham9_8_luFirstSchurComplement_trailingPerm Aperm sigma₁ tau₁
      have hLU₁_plain :
          LUFactSpec m (higham9_2_rowColPermutedMatrix S sigma₁ tau₁) L₁ Uc₁ :=
        higham9_2_completePermutedLUFactSpec_to_LUFactSpec hLU₁
      have hS_B : LUFactSpec m (luFirstSchurComplement B) L₁ Uc₁ := by
        simpa [hschur] using hLU₁_plain
      have hLU_B : LUFactSpec (m + 1) B L Uc :=
        LUFactSpec.of_firstSchurComplement_explicit hpivotB hS_B
      refine ⟨L, Uc, sigma, tau, ?_, ?_⟩
      · refine ⟨htau, ?_⟩
        refine
          { perm := hsigma
            L_diag := hLU_B.L_diag
            L_upper_zero := hLU_B.L_upper_zero
            U_lower_zero := hLU_B.U_lower_zero
            product_eq := ?_ }
        intro i j
        have h := hLU_B.product_eq i j
        simpa [L, Uc, B, Aperm, sigma, tau, sigma₀, tau₀,
          higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
          higham9_2_colPermutedMatrix] using h
      · intro hn
        apply maxEntryNorm_le_of_entry_le_max hn Uc Utrace
        intro i j
        by_cases hi : i = 0
        · subst i
          by_cases hj : j = 0
          · subst j
            simpa [Uc, Utrace, B, Aperm, sigmaExt, tauExt, luFirstStepU,
              higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
              higham9_2_colPermutedMatrix] using
              entry_le_maxEntryNorm hn Utrace 0 0
          · have htop :=
              entry_le_maxEntryNorm hn Utrace
                (0 : Fin (m + 1)) ((tau₁ (j.pred hj)).succ)
            have htauj :
                higham9_8_extendTrailingPerm tau₁ j =
                  (tau₁ (j.pred hj)).succ := by
              simp [higham9_8_extendTrailingPerm, hj]
            simpa [Uc, Utrace, B, Aperm, sigmaExt, tauExt, htauj, luFirstStepU, hj,
              higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
              higham9_2_colPermutedMatrix, Fin.succ_pred] using htop
        · by_cases hj : j = 0
          · subst j
            have hnonneg : 0 ≤ maxEntryNorm hn Utrace :=
              maxEntryNorm_nonneg hn Utrace
            simpa [Uc, Utrace, luFirstStepU, hi] using hnonneg
          · have hm : 0 < m := by
              by_contra hm0
              have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
              subst hmzero
              have hival : i.val = 0 := by omega
              exact hi (Fin.ext hival)
            have hUc_entry :
                |Uc₁ (i.pred hi) (j.pred hj)| ≤ maxEntryNorm hm Uc₁ :=
              entry_le_maxEntryNorm hm Uc₁ (i.pred hi) (j.pred hj)
            have hUc_to_U₁ :
                |Uc₁ (i.pred hi) (j.pred hj)| ≤ maxEntryNorm hm U₁ :=
              le_trans hUc_entry (hmax₁ hm)
            have hU₁_to_trace :
                maxEntryNorm hm U₁ ≤ maxEntryNorm hn Utrace := by
              apply maxEntryNorm_le_of_entry_le_bound hm U₁ (maxEntryNorm hn Utrace)
              intro p q
              have h := entry_le_maxEntryNorm hn Utrace p.succ q.succ
              simpa [Utrace, luFirstStepU] using h
            have hfinal :
                |Uc₁ (i.pred hi) (j.pred hj)| ≤ maxEntryNorm hn Utrace :=
              le_trans hUc_to_U₁ hU₁_to_trace
            simpa [Uc, Utrace, luFirstStepU, hi, hj] using hfinal

/-- **Theorem 9.8 / complete-pivoting trace support**, every nonsingular real
matrix admits an explicit recursive complete-pivoting upper-factor trace. -/
theorem higham9_8_exists_CompletePivotGECPUTrace_of_det_ne_zero :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∃ U : Fin n → Fin n → ℝ,
        higham9_8_CompletePivotGECPUTrace n A U := by
  intro n
  induction n with
  | zero =>
      intro A _hdet
      exact ⟨A, higham9_8_CompletePivotGECPUTrace.done⟩
  | succ m ih =>
      intro A hdet
      obtain ⟨r, s, hchoice, hpivot⟩ :=
        higham9_1_exists_first_completePivotChoice_pivot_ne_zero_of_det_ne_zero
          A hdet
      let S : Fin m → Fin m → ℝ :=
        luFirstSchurComplement
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s))
      have hdetS :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
        simpa [S] using
          higham9_1_firstCompletePivotSchurComplement_det_ne_zero_of_det_ne_zero
            A hpivot hdet
      obtain ⟨U₁, hU₁⟩ := ih (A := S) hdetS
      refine
        ⟨luFirstStepU
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s)) U₁, ?_⟩
      simpa [S] using
        higham9_8_CompletePivotGECPUTrace.step hchoice hpivot hU₁

/-- **Theorem 9.8 / complete-pivoting trace support**, source-facing existence
of a triangular exposed upper-factor trace for every nonsingular real input.
This constructs the recursive exact trace only; it does not by itself prove the
Wilkinson complete-pivoting growth upper bound. -/
theorem higham9_8_exists_CompletePivotGECPUTrace_upper_zero_of_det_ne_zero
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ U : Fin n → Fin n → ℝ,
      higham9_8_CompletePivotGECPUTrace n A U ∧
        ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
  obtain ⟨U, hU⟩ :=
    higham9_8_exists_CompletePivotGECPUTrace_of_det_ne_zero (A := A) hdet
  exact ⟨U, hU, higham9_8_CompletePivotGECPUTrace_upper_zero hU⟩

/-- **Problem 9.11 / equation (9.15)**, the trace-level complete-pivoting
growth-value family is nonempty in every positive dimension. -/
theorem higham9_completePivotingUTraceGrowthValues_nonempty {n : ℕ}
    (hn : 0 < n) :
    (higham9_completePivotingUTraceGrowthValues n).Nonempty := by
  let A : Fin n → Fin n → ℝ := higham9_7_wilkinsonGrowthMatrix (n := n)
  have hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    exact higham9_7_PartialPivotNoInterchangeTrace_det_ne_zero
      (by
        simpa [A] using higham9_7_wilkinsonGrowth_noInterchangeTrace n)
  let hApos : 0 < maxEntryNorm hn A :=
    by simpa [A] using higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_pos hn
  obtain ⟨U, htrace⟩ :=
    higham9_8_exists_CompletePivotGECPUTrace_of_det_ne_zero (A := A) hdet
  refine ⟨growthFactorEntry hn A U hApos, ?_⟩
  exact ⟨hn, A, U, hApos, htrace, rfl⟩

/-- **Problem 9.11 / equation (9.15)**, elementary source-shaped supremum
upper bound for recursive complete-pivoting `U` traces. -/
theorem higham9_8_completePivotingUTraceGrowthSup_le_pow_two {n : ℕ}
    (hn : 0 < n) :
    higham9_completePivotingUTraceGrowthSup n ≤ (2 : ℝ) ^ (n - 1) := by
  apply csSup_le (higham9_completePivotingUTraceGrowthValues_nonempty hn)
  intro r hr
  rcases hr with ⟨hn', A, U, hApos, htrace, rfl⟩
  exact higham9_8_CompletePivotGECPUTrace_growthFactorEntry_le_pow_two
    hn' A U hApos htrace

/-- **Theorem 9.4 / Theorem 9.5**, complete-pivoted explicit-certificate
normwise source bound.

If a supplied `P A Q` backward-error certificate computes the same `U_hat` as
an explicit complete-pivoting `U` trace, then the elementary complete-pivoting
trace bound gives Wilkinson's normwise source bound over the original matrix
norm.  The theorem keeps the complete-pivoting trace, backward-error
certificate, nonzero pivots, and multiplier bound as visible hypotheses; it
does not prove Wilkinson's sharper complete-pivoting product bound. -/
theorem higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma tau : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_8_CompletePivotGECPUTrace n A U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU :
      higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau
        (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let z_hat := fl_backSub fp n U_hat y_hat
    let x_hat : Fin n → ℝ :=
      fun j => z_hat ((Equiv.ofBijective tau hLU.1).symm j)
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  classical
  let bP : Fin n → ℝ := fun i => b (sigma i)
  let B : Fin n → Fin n → ℝ := higham9_2_rowColPermutedMatrix A sigma tau
  have hBmax : 0 < maxEntryNorm hn_pos B := by
    simpa [B, higham9_2_rowColPermutedMatrix_maxEntryNorm hn_pos A hLU.2.perm hLU.1]
      using hAmax
  have hgrowth :
      growthFactorEntry hn_pos B U_hat hBmax ≤
        (2 : ℝ) ^ (n - 1) := by
    have htrace_growth :
        growthFactorEntry hn_pos A U_hat hAmax ≤ (2 : ℝ) ^ (n - 1) :=
      higham9_8_CompletePivotGECPUTrace_growthFactorEntry_le_pow_two
        hn_pos A U_hat hAmax htrace
    unfold growthFactorEntry at htrace_growth ⊢
    simpa [B, higham9_2_rowColPermutedMatrix_maxEntryNorm hn_pos A hLU.2.perm hLU.1]
      using htrace_growth
  have hL_diag : ∀ i : Fin n, L_hat i i ≠ 0 := by
    intro i
    rw [hLU.2.L_diag i]
    norm_num
  obtain ⟨ΔB, hΔB_bound, hΔB_eq⟩ :=
    higham9_5_wilkinson_source_bound_of_entry_growth fp n hn_pos B
      L_hat U_hat bP ((2 : ℝ) ^ (n - 1)) hBmax
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n - 1))
      hgrowth hL_diag hU_diag
      (higham9_2_completePermutedLUBackwardError_to_LUBackwardError hLU)
      hn hn3 hL_bound
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hLU.2.perm
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau hLU.1
  let z_hat := fl_backSub fp n U_hat (fl_forwardSub fp n L_hat bP)
  let x_hat : Fin n → ℝ := fun j => z_hat (eTau.symm j)
  let ΔA : Fin n → Fin n → ℝ := fun i j => ΔB (eSigma.symm i) (eTau.symm j)
  refine ⟨ΔA, ?_, ?_⟩
  · have hperm_eq :
        higham9_2_rowColPermutedMatrix ΔA sigma tau = ΔB := by
      funext i j
      have hsigma_left : eSigma.symm (sigma i) = i := by
        change eSigma.symm (eSigma i) = i
        exact Equiv.symm_apply_apply eSigma i
      have htau_left : eTau.symm (tau j) = j := by
        change eTau.symm (eTau j) = j
        exact Equiv.symm_apply_apply eTau j
      simp [ΔA, higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
        higham9_2_colPermutedMatrix, hsigma_left, htau_left]
    have hΔnorm : infNorm ΔA = infNorm ΔB := by
      have hpermΔ :=
        higham9_2_rowColPermutedMatrix_infNorm ΔA hLU.2.perm hLU.1
      rw [hperm_eq] at hpermΔ
      exact hpermΔ.symm
    have hB_inf : infNorm B = infNorm A := by
      simpa [B] using
        higham9_2_rowColPermutedMatrix_infNorm A hLU.2.perm hLU.1
    calc
      infNorm ΔA = infNorm ΔB := hΔnorm
      _ ≤ (↑n) ^ 2 * gamma fp (3 * n) *
            (2 : ℝ) ^ (n - 1) * infNorm B := hΔB_bound
      _ = (↑n) ^ 2 * gamma fp (3 * n) *
            (2 : ℝ) ^ (n - 1) * infNorm A := by
          rw [hB_inf]
  · intro i
    have hrow := hΔB_eq (eSigma.symm i)
    have hsigma_symm : sigma (eSigma.symm i) = i := by
      change eSigma (eSigma.symm i) = i
      exact Equiv.apply_symm_apply eSigma i
    let f : Fin n → ℝ := fun j => (A i j + ΔA i j) * x_hat j
    calc
      ∑ j : Fin n, (A i j + ΔA i j) * x_hat j
          = ∑ j : Fin n, f (eTau j) := by
              simpa [f] using (Equiv.sum_comp eTau f).symm
      _ = ∑ j : Fin n, (B (eSigma.symm i) j + ΔB (eSigma.symm i) j) *
            z_hat j := by
          apply Finset.sum_congr rfl
          intro j _
          simp [f, B, higham9_2_rowColPermutedMatrix,
            higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix,
            ΔA, x_hat, z_hat, eTau, hsigma_symm]
      _ = bP (eSigma.symm i) := hrow
      _ = b i := by simp [bP, hsigma_symm]

/-- **Theorem 9.8 / equation (9.13) complex support**, a recursive exact
complete-pivoting trace over complex matrices. -/
inductive higham9_8_ComplexCompletePivotGECPUTrace :
    (n : ℕ) → (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ) → Prop
  | done {A U : Fin 0 → Fin 0 → ℂ} :
      higham9_8_ComplexCompletePivotGECPUTrace 0 A U
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℂ}
      {r s : Fin (m + 1)} {U₁ : Fin m → Fin m → ℂ}
      (hchoice : higham9_8_complexCompletePivotChoice A 0 r s)
      (hpivot : A r s ≠ 0)
      (hnext :
        higham9_8_ComplexCompletePivotGECPUTrace m
          (higham9_8_complexFirstSchurComplement
            (higham9_2_complexRowColPermutedMatrix A
              (higham9_7_firstPivotRowSwap r)
              (higham9_7_firstPivotRowSwap s))) U₁) :
      higham9_8_ComplexCompletePivotGECPUTrace (m + 1) A
        (higham9_8_complexLUFirstStepU
          (higham9_2_complexRowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s)) U₁)

/-- Complex complete-pivoting trace upper-triangularity. -/
theorem higham9_8_ComplexCompletePivotGECPUTrace_upper_zero :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℂ},
      higham9_8_ComplexCompletePivotGECPUTrace n A U →
      ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro i
      exact Fin.elim0 i
  | step _hchoice _hpivot _hnext ih =>
      intro i j hij
      by_cases hi : i = 0
      · subst i
        exact (Nat.not_lt_zero _ hij).elim
      · by_cases hj : j = 0
        · subst j
          simp [higham9_8_complexLUFirstStepU, hi]
        · have hpred : (j.pred hj).val < (i.pred hi).val := by
            have hival := Fin.val_pred i hi
            have hjval := Fin.val_pred j hj
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
            omega
          have hrec := ih (i.pred hi) (j.pred hj) hpred
          simpa [higham9_8_complexLUFirstStepU, hi, hj] using hrec

/-- Every nonsingular complex matrix admits a recursive exact complete-pivoting
`U` trace. -/
theorem higham9_8_exists_ComplexCompletePivotGECPUTrace_of_det_ne_zero :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℂ},
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) ≠ 0 →
      ∃ U : Fin n → Fin n → ℂ,
        higham9_8_ComplexCompletePivotGECPUTrace n A U := by
  intro n
  induction n with
  | zero =>
      intro A _hdet
      exact ⟨A, higham9_8_ComplexCompletePivotGECPUTrace.done⟩
  | succ m ih =>
      intro A hdet
      obtain ⟨r, s, hchoice, hpivot⟩ :=
        higham9_8_exists_first_complexCompletePivotChoice_pivot_ne_zero_of_det_ne_zero
          A hdet
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_2_complexRowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r)
          (higham9_7_firstPivotRowSwap s)
      let S : Fin m → Fin m → ℂ :=
        higham9_8_complexFirstSchurComplement Aperm
      have hpivotAperm : Aperm 0 0 ≠ 0 := by
        simpa [Aperm, higham9_2_complexRowColPermutedMatrix,
          higham9_7_firstPivotRowSwap] using hpivot
      have hdetAperm :
          Matrix.det (Matrix.of Aperm : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0 := by
        simpa [Aperm] using
          higham9_8_complex_firstPivotRowColSwap_det_ne_zero A r s hdet
      have hdetS :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℂ) ≠ 0 := by
        simpa [S] using
          higham9_8_complexFirstSchurComplement_det_ne_zero
            Aperm hpivotAperm hdetAperm
      obtain ⟨U₁, hU₁⟩ := ih (A := S) hdetS
      refine
        ⟨higham9_8_complexLUFirstStepU
          (higham9_2_complexRowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s)) U₁, ?_⟩
      simpa [Aperm, S] using
        higham9_8_ComplexCompletePivotGECPUTrace.step hchoice hpivot hU₁

/-- Source-facing existence of a triangular complex complete-pivoting trace for
every nonsingular complex input. -/
theorem higham9_8_exists_ComplexCompletePivotGECPUTrace_upper_zero_of_det_ne_zero
    {n : ℕ} (A : Fin n → Fin n → ℂ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) ≠ 0) :
    ∃ U : Fin n → Fin n → ℂ,
      higham9_8_ComplexCompletePivotGECPUTrace n A U ∧
        ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
  obtain ⟨U, hU⟩ :=
    higham9_8_exists_ComplexCompletePivotGECPUTrace_of_det_ne_zero (A := A) hdet
  exact ⟨U, hU, higham9_8_ComplexCompletePivotGECPUTrace_upper_zero hU⟩

/-- **Theorem 9.8 / equation (9.13) bridge**, every recursive complex
complete-pivoting `U` trace determines a cumulative complex complete-pivoting
`PAQ = LU` certificate whose certificate `U` has complex max-entry norm no
larger than the trace `U`. -/
theorem higham9_8_ComplexCompletePivotGECPUTrace_exists_ComplexCompletePermutedLUFactSpec_complexMaxEntryNorm_le :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℂ},
      higham9_8_ComplexCompletePivotGECPUTrace n A U →
      ∃ L Uc : Fin n → Fin n → ℂ,
      ∃ sigma tau : Fin n → Fin n,
        higham9_8_ComplexCompletePermutedLUFactSpec n A L Uc sigma tau ∧
          ∀ hn : 0 < n,
            higham9_13_complexMaxEntryNorm hn Uc ≤
              higham9_13_complexMaxEntryNorm hn U := by
  intro n A U htrace
  induction htrace with
  | done =>
      let empty : Fin 0 → Fin 0 := fun i => Fin.elim0 i
      let Z : Fin 0 → Fin 0 → ℂ := fun i => Fin.elim0 i
      have hempty : IsPermutation 0 empty := by
        constructor
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
      refine ⟨Z, Z, empty, empty, ?_, ?_⟩
      · refine
          { row_perm := hempty
            col_perm := hempty
            L_diag := ?_
            L_upper_zero := ?_
            U_lower_zero := ?_
            product_eq := ?_ }
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
      · intro hn
        exact (Nat.not_lt_zero 0 hn).elim
  | step hchoice hpivot hnext ih =>
      rename_i m A r s U₁
      obtain ⟨L₁, Uc₁, sigma₁, tau₁, hLU₁, hmax₁⟩ := ih
      let sigma₀ : Fin (m + 1) → Fin (m + 1) :=
        higham9_7_firstPivotRowSwap r
      let tau₀ : Fin (m + 1) → Fin (m + 1) :=
        higham9_7_firstPivotRowSwap s
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_2_complexRowColPermutedMatrix A sigma₀ tau₀
      let S : Fin m → Fin m → ℂ := higham9_8_complexFirstSchurComplement Aperm
      let sigmaExt : Fin (m + 1) → Fin (m + 1) :=
        higham9_8_extendTrailingPerm sigma₁
      let tauExt : Fin (m + 1) → Fin (m + 1) :=
        higham9_8_extendTrailingPerm tau₁
      let sigma : Fin (m + 1) → Fin (m + 1) := fun i => sigma₀ (sigmaExt i)
      let tau : Fin (m + 1) → Fin (m + 1) := fun i => tau₀ (tauExt i)
      let B : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_2_complexRowColPermutedMatrix Aperm sigmaExt tauExt
      let L : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_8_complexLUFirstStepL B L₁
      let Uc : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_8_complexLUFirstStepU B Uc₁
      let Utrace : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_8_complexLUFirstStepU Aperm U₁
      have hsigmaExt : IsPermutation (m + 1) sigmaExt :=
        higham9_8_extendTrailingPerm_isPermutation hLU₁.row_perm
      have htauExt : IsPermutation (m + 1) tauExt :=
        higham9_8_extendTrailingPerm_isPermutation hLU₁.col_perm
      have hsigma : IsPermutation (m + 1) sigma :=
        higham9_8_isPermutation_comp
          (by
            show IsPermutation (m + 1) (higham9_7_firstPivotRowSwap r)
            exact higham9_7_firstPivotRowSwap_isPermutation r)
          hsigmaExt
      have htau : IsPermutation (m + 1) tau :=
        higham9_8_isPermutation_comp
          (by
            show IsPermutation (m + 1) (higham9_7_firstPivotRowSwap s)
            exact higham9_7_firstPivotRowSwap_isPermutation s)
          htauExt
      have hpivotB : B 0 0 ≠ 0 := by
        simpa [B, Aperm, sigma₀, tau₀, sigmaExt, tauExt,
          higham9_2_complexRowColPermutedMatrix, higham9_7_firstPivotRowSwap] using hpivot
      have hschur :
          higham9_8_complexFirstSchurComplement B =
            higham9_2_complexRowColPermutedMatrix S sigma₁ tau₁ := by
        simpa [B, S] using
          higham9_8_complexFirstSchurComplement_trailingPerm Aperm sigma₁ tau₁
      have hLU₁_plain :
          higham9_8_ComplexLUFactSpec m
            (higham9_2_complexRowColPermutedMatrix S sigma₁ tau₁) L₁ Uc₁ :=
        higham9_8_complexCompletePermutedLUFactSpec_to_LUFactSpec hLU₁
      have hS_B :
          higham9_8_ComplexLUFactSpec m
            (higham9_8_complexFirstSchurComplement B) L₁ Uc₁ := by
        simpa [hschur] using hLU₁_plain
      have hLU_B :
          higham9_8_ComplexLUFactSpec (m + 1) B L Uc :=
        higham9_8_complexLUFactSpec_of_firstSchurComplement_explicit hpivotB hS_B
      refine ⟨L, Uc, sigma, tau, ?_, ?_⟩
      · refine
          { row_perm := hsigma
            col_perm := htau
            L_diag := hLU_B.L_diag
            L_upper_zero := hLU_B.L_upper_zero
            U_lower_zero := hLU_B.U_lower_zero
            product_eq := ?_ }
        intro i j
        have h := hLU_B.product_eq i j
        simpa [L, Uc, B, Aperm, sigma, tau, sigma₀, tau₀,
          higham9_2_complexRowColPermutedMatrix] using h
      · intro hn
        apply higham9_13_complexMaxEntryNorm_le_of_entry_le_max hn Uc Utrace
        intro i j
        by_cases hi : i = 0
        · subst i
          by_cases hj : j = 0
          · subst j
            simpa [Uc, Utrace, B, Aperm, sigmaExt, tauExt,
              higham9_8_complexLUFirstStepU, higham9_2_complexRowColPermutedMatrix] using
              higham9_13_entry_norm_le_complexMaxEntryNorm hn Utrace 0 0
          · have htop :=
              higham9_13_entry_norm_le_complexMaxEntryNorm hn Utrace
                (0 : Fin (m + 1)) ((tau₁ (j.pred hj)).succ)
            have htauj :
                higham9_8_extendTrailingPerm tau₁ j =
                  (tau₁ (j.pred hj)).succ := by
              simp [higham9_8_extendTrailingPerm, hj]
            simpa [Uc, Utrace, B, Aperm, sigmaExt, tauExt, htauj,
              higham9_8_complexLUFirstStepU, hj,
              higham9_2_complexRowColPermutedMatrix, Fin.succ_pred] using htop
        · by_cases hj : j = 0
          · subst j
            have hnonneg : 0 ≤ higham9_13_complexMaxEntryNorm hn Utrace :=
              higham9_13_complexMaxEntryNorm_nonneg hn Utrace
            simpa [Uc, Utrace, higham9_8_complexLUFirstStepU, hi] using hnonneg
          · have hm : 0 < m := by
              by_contra hm0
              have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
              subst hmzero
              have hival : i.val = 0 := by omega
              exact hi (Fin.ext hival)
            have hUc_entry :
                ‖Uc₁ (i.pred hi) (j.pred hj)‖ ≤
                  higham9_13_complexMaxEntryNorm hm Uc₁ :=
              higham9_13_entry_norm_le_complexMaxEntryNorm
                hm Uc₁ (i.pred hi) (j.pred hj)
            have hUc_to_U₁ :
                ‖Uc₁ (i.pred hi) (j.pred hj)‖ ≤
                  higham9_13_complexMaxEntryNorm hm U₁ :=
              le_trans hUc_entry (hmax₁ hm)
            have hU₁_to_trace :
                higham9_13_complexMaxEntryNorm hm U₁ ≤
                  higham9_13_complexMaxEntryNorm hn Utrace := by
              apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
                hm U₁ (higham9_13_complexMaxEntryNorm hn Utrace)
              intro p q
              have h := higham9_13_entry_norm_le_complexMaxEntryNorm
                hn Utrace p.succ q.succ
              simpa [Utrace, higham9_8_complexLUFirstStepU] using h
            have hfinal :
                ‖Uc₁ (i.pred hi) (j.pred hj)‖ ≤
                  higham9_13_complexMaxEntryNorm hn Utrace :=
              le_trans hUc_to_U₁ hU₁_to_trace
            simpa [Uc, Utrace, higham9_8_complexLUFirstStepU, hi, hj] using hfinal

/-- **Equation (9.13)**, Fourier/Vandermonde growth lower bound from a
recursive complex complete-pivoting trace. -/
theorem higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card_of_ComplexCompletePivotGECPUTrace
    {n : ℕ} (hn : 0 < n) (U : Fin n → Fin n → ℂ)
    (htrace :
      higham9_8_ComplexCompletePivotGECPUTrace n
        (higham9_13_fourierVandermonde n) U) :
    (n : ℝ) ≤
      higham9_13_complexGrowthFactorEntry hn
        (higham9_13_fourierVandermonde n) U := by
  obtain ⟨L, Uc, sigma, tau, hLU, hmax⟩ :=
    higham9_8_ComplexCompletePivotGECPUTrace_exists_ComplexCompletePermutedLUFactSpec_complexMaxEntryNorm_le
      htrace
  have hcert :
      (n : ℝ) ≤
        higham9_13_complexGrowthFactorEntry hn
          (higham9_13_fourierVandermonde n) Uc :=
    higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card_of_completePermutedLUFactSpec
      hn L Uc sigma tau hLU
  have hApos : 0 < higham9_13_complexMaxEntryNorm hn (higham9_13_fourierVandermonde n) := by
    rw [higham9_13_fourierVandermonde_complexMaxEntryNorm_eq_one hn]
    norm_num
  have hgrowth :
      higham9_13_complexGrowthFactorEntry hn
          (higham9_13_fourierVandermonde n) Uc ≤
        higham9_13_complexGrowthFactorEntry hn
          (higham9_13_fourierVandermonde n) U := by
    unfold higham9_13_complexGrowthFactorEntry
    exact div_le_div_of_nonneg_right (hmax hn) (le_of_lt hApos)
  exact le_trans hcert hgrowth

/-- **Equation (9.13)**, end-to-end recursive complex complete-pivoting trace
existence for the Fourier/Vandermonde example with trace-level growth
`n <= rho`. -/
theorem higham9_13_exists_fourierVandermonde_ComplexCompletePivotGECPUTrace_growth_ge_card
    {n : ℕ} (hn : 0 < n) :
    ∃ U : Fin n → Fin n → ℂ,
      higham9_8_ComplexCompletePivotGECPUTrace n
        (higham9_13_fourierVandermonde n) U ∧
      (n : ℝ) ≤
        higham9_13_complexGrowthFactorEntry hn
          (higham9_13_fourierVandermonde n) U := by
  let V : Fin n → Fin n → ℂ := higham9_13_fourierVandermonde n
  let V_inv : Fin n → Fin n → ℂ := higham9_13_fourierVandermondeScaledAdjoint n
  have hRight : higham9_8_ComplexIsRightInverse n V V_inv := by
    exact (higham9_13_fourierVandermonde_inverse_formula n).2
  have hdet : Matrix.det (Matrix.of V : Matrix (Fin n) (Fin n) ℂ) ≠ 0 :=
    higham9_8_complex_det_ne_zero_of_isRightInverse V V_inv hRight
  obtain ⟨U, htrace⟩ :=
    higham9_8_exists_ComplexCompletePivotGECPUTrace_of_det_ne_zero (A := V) hdet
  refine ⟨U, htrace, ?_⟩
  simpa [V] using
    higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card_of_ComplexCompletePivotGECPUTrace
      hn U htrace

/-- **Theorem 9.8 / Problem 9.11 bridge**, the final-pivot inverse-entry
lower bound transfers from cumulative complete-pivoting certificates to the
recursive complete-pivoting `U` trace surface. -/
theorem higham9_8_CompletePivotGECPUTrace_growth_factor_ge_theta_real {n : ℕ}
    (hn : 0 < n)
    (A A_inv U : Fin n → Fin n → ℝ)
    (htrace : higham9_8_CompletePivotGECPUTrace n A U)
    (hRight : IsRightInverse n A A_inv)
    (hA : 0 < maxEntryNorm hn A)
    (hAinv : 0 < maxEntryNorm hn A_inv) :
    1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv) ≤
      growthFactorEntry hn A U hA := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero 0 hn).elim
  | succ m =>
      obtain ⟨L, Uc, sigma, tau, hLU, hmax⟩ :=
        higham9_8_CompletePivotGECPUTrace_exists_CompletePermutedLUFactSpec_maxEntryNorm_le
          htrace
      have hA' : 0 < maxEntryNorm (Nat.succ_pos m) A := by
        simpa using hA
      have hAinv' : 0 < maxEntryNorm (Nat.succ_pos m) A_inv := by
        simpa using hAinv
      have hcert' :
          1 / (maxEntryNorm (Nat.succ_pos m) A *
              maxEntryNorm (Nat.succ_pos m) A_inv) ≤
            growthFactorEntry (Nat.succ_pos m) A Uc hA' :=
        higham9_8_growth_factor_ge_theta_of_completePermutedLUFactSpec_right_inverse
          A A_inv L Uc sigma tau hLU hRight hA' hAinv'
      have hgrowth_le' :
          growthFactorEntry (Nat.succ_pos m) A Uc hA' ≤
            growthFactorEntry (Nat.succ_pos m) A U hA' := by
        unfold growthFactorEntry
        exact div_le_div_of_nonneg_right
          (hmax (Nat.succ_pos m)) (le_of_lt hA')
      have hfinal' :
          1 / (maxEntryNorm (Nat.succ_pos m) A *
              maxEntryNorm (Nat.succ_pos m) A_inv) ≤
            growthFactorEntry (Nat.succ_pos m) A U hA' :=
        le_trans hcert' hgrowth_le'
      simpa using hfinal'

/-- **Problem 9.11**, the flattened sine block has an actual recursive
complete-pivoting `U` trace whose entrywise growth is at least `n + 1`. -/
theorem higham9_11_exists_completePivotingUTrace_sine_block_growth_ge_succ
    {n : ℕ} (hn : 0 < n) :
    ∃ U : Fin (2 * n) → Fin (2 * n) → ℝ,
      higham9_8_CompletePivotGECPUTrace (2 * n)
        (higham9_11_flattenTwoBlock hn
          (higham9_11_blockMatrix (higham9_12_sineMatrix n)))
        U ∧
      (n : ℝ) + 1 ≤
        growthFactorEntry (by omega : 0 < 2 * n)
          (higham9_11_flattenTwoBlock hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n)))
          U
          (by
            rw [higham9_11_flatten_blockMatrix_maxEntryNorm_eq hn]
            exact higham9_12_sineMatrix_maxEntryNorm_pos hn) := by
  let B : Fin (2 * n) → Fin (2 * n) → ℝ :=
    higham9_11_flattenTwoBlock hn
      (higham9_11_blockMatrix (higham9_12_sineMatrix n))
  let B_inv : Fin (2 * n) → Fin (2 * n) → ℝ :=
    higham9_11_flattenTwoBlock hn
      (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n))
  have hsineRight :
      IsRightInverse n (higham9_12_sineMatrix n) (higham9_12_sineMatrix n) :=
    (higham9_12_sineMatrix_inverse_formula hn).2
  have hBlockRight :
      ∀ bi bj : Fin 2, ∀ i j : Fin n,
        blockMatProd
            (higham9_11_blockMatrix (higham9_12_sineMatrix n))
            (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n))
            bi bj i j =
          if bi = bj then if i = j then 1 else 0 else 0 :=
    higham9_11_blockInverseCandidate_right
      (higham9_12_sineMatrix n) (higham9_12_sineMatrix n) hsineRight
  have hRight : IsRightInverse (2 * n) B B_inv := by
    simpa [B, B_inv] using
      higham9_11_flattenTwoBlock_right_inverse hn hBlockRight
  have hdet :
      Matrix.det (Matrix.of B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) ≠ 0 :=
    higham9_det_ne_zero_of_isRightInverse B B_inv hRight
  have hBpos : 0 < maxEntryNorm (by omega : 0 < 2 * n) B := by
    dsimp [B]
    rw [higham9_11_flatten_blockMatrix_maxEntryNorm_eq hn]
    exact higham9_12_sineMatrix_maxEntryNorm_pos hn
  have hBinvpos : 0 < maxEntryNorm (by omega : 0 < 2 * n) B_inv := by
    dsimp [B_inv]
    rw [higham9_11_flatten_blockInverseCandidate_maxEntryNorm_eq hn]
    exact mul_pos (by norm_num) (higham9_12_sineMatrix_maxEntryNorm_pos hn)
  obtain ⟨U, htrace⟩ :=
    higham9_8_exists_CompletePivotGECPUTrace_of_det_ne_zero (A := B) hdet
  refine ⟨U, by simpa [B] using htrace, ?_⟩
  have htheta_le_growth :
      1 / (maxEntryNorm (by omega : 0 < 2 * n) B *
            maxEntryNorm (by omega : 0 < 2 * n) B_inv) ≤
        growthFactorEntry (by omega : 0 < 2 * n) B U hBpos :=
    higham9_8_CompletePivotGECPUTrace_growth_factor_ge_theta_real
      (hn := by omega) B B_inv U htrace hRight hBpos hBinvpos
  have hsineTheta :
      (n : ℝ) + 1 ≤
        1 /
          (maxEntryNorm (by omega : 0 < 2 * n) B *
            maxEntryNorm (by omega : 0 < 2 * n) B_inv) := by
    dsimp [B, B_inv]
    simpa [higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm] using
      higham9_11_sine_block_theta_candidate_ge_succ hn
  have hfinal := le_trans hsineTheta htheta_le_growth
  simpa [B, growthFactorEntry] using hfinal

/-- **Problem 9.11**, the trace-level complete-pivoting value set contains
the flattened sine-block lower-bound value. -/
theorem higham9_11_completePivotingUTraceGrowthValues_exists_ge_succ
    {n : ℕ} (hn : 0 < n) :
    ∃ r ∈ higham9_completePivotingUTraceGrowthValues (2 * n),
      (n : ℝ) + 1 ≤ r := by
  obtain ⟨U, htrace, hgrowth⟩ :=
    higham9_11_exists_completePivotingUTrace_sine_block_growth_ge_succ hn
  let B : Fin (2 * n) → Fin (2 * n) → ℝ :=
    higham9_11_flattenTwoBlock hn
      (higham9_11_blockMatrix (higham9_12_sineMatrix n))
  have hBpos : 0 < maxEntryNorm (by omega : 0 < 2 * n) B := by
    dsimp [B]
    rw [higham9_11_flatten_blockMatrix_maxEntryNorm_eq hn]
    exact higham9_12_sineMatrix_maxEntryNorm_pos hn
  refine ⟨growthFactorEntry (by omega : 0 < 2 * n) B U hBpos, ?_, ?_⟩
  · refine ⟨by omega, B, U, hBpos, ?_, rfl⟩
    simpa [B] using htrace
  · simpa [B] using hgrowth

/-- **Problem 9.11 / equation (9.15)**, trace-level source-shaped lower bound
`n + 1 <= g(2n)` for the bounded complete-pivoting `U` trace surface. -/
theorem higham9_11_completePivotingUTraceGrowthSup_ge_succ
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ) + 1 ≤ higham9_completePivotingUTraceGrowthSup (2 * n) := by
  obtain ⟨r, hr, hle⟩ :=
    higham9_11_completePivotingUTraceGrowthValues_exists_ge_succ hn
  exact le_trans hle (higham9_completePivotingUTraceGrowth_le_sup hr)

/-- **Equation (9.16) / rook-pivoting `U` trace**, a recursive exact
rook-pivoting trace that exposes the final upper-factor rows.  Each step
chooses a first-stage rook pivot, moves it to `(0,0)` by row and column swaps,
stores the permuted pivot row in `U`, and recurses on the first Schur
complement. -/
inductive higham9_16_RookPivotGEUTrace :
    (n : ℕ) → (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Prop
  | done {A U : Fin 0 → Fin 0 → ℝ} :
      higham9_16_RookPivotGEUTrace 0 A U
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {r s : Fin (m + 1)} {U₁ : Fin m → Fin m → ℝ}
      (hchoice : higham9_1_rookPivotChoice A 0 r s)
      (hpivot : A r s ≠ 0)
      (hnext :
        higham9_16_RookPivotGEUTrace m
          (luFirstSchurComplement
            (higham9_2_rowColPermutedMatrix A
              (higham9_7_firstPivotRowSwap r)
              (higham9_7_firstPivotRowSwap s))) U₁) :
      higham9_16_RookPivotGEUTrace (m + 1) A
        (luFirstStepU
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s)) U₁)

/-- **Equation (9.16) / rook-pivoting `U` trace**, the exposed `U` rows are
upper triangular along the recursive rook-pivoting trace. -/
theorem higham9_16_RookPivotGEUTrace_upper_zero :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_16_RookPivotGEUTrace n A U →
      ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro i
      exact Fin.elim0 i
  | step _hchoice _hpivot _hnext ih =>
      intro i j hij
      by_cases hi : i = 0
      · subst i
        exact (Nat.not_lt_zero _ hij).elim
      · by_cases hj : j = 0
        · subst j
          simp [luFirstStepU, hi]
        · have hpred : (j.pred hj).val < (i.pred hi).val := by
            have hival := Fin.val_pred i hi
            have hjval := Fin.val_pred j hj
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
            omega
          have hrec := ih (i.pred hi) (j.pred hj) hpred
          simpa [luFirstStepU, hi, hj] using hrec

/-- **Equation (9.16) / rook-pivoting growth support**, first-step entry
bound.  A rook pivot is maximal in its active column, so after moving it to
`(0,0)` the Schur-complement multiplier has absolute value at most one.  This
is the elementary doubling step; it is not Foster's sharper rook-pivoting
bound. -/
theorem higham9_16_rookPivot_firstSchurComplement_entry_abs_le_two {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) {r s : Fin (m + 1)}
    (hchoice : higham9_1_rookPivotChoice A 0 r s)
    (hpivot : A r s ≠ 0) (i j : Fin m) :
    |luFirstSchurComplement
        (higham9_2_rowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r)
          (higham9_7_firstPivotRowSwap s)) i j| ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  let sigma := higham9_7_firstPivotRowSwap r
  let tau := higham9_7_firstPivotRowSwap s
  let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_2_rowColPermutedMatrix A sigma tau
  have hpivB : Aperm 0 0 ≠ 0 := by
    simpa [Aperm, higham9_2_rowColPermutedMatrix,
      higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix, sigma, tau,
      higham9_7_firstPivotRowSwap] using hpivot
  have hentry : |Aperm i.succ j.succ| ≤ maxEntryNorm (Nat.succ_pos m) A := by
    exact entry_le_maxEntryNorm (Nat.succ_pos m) A (sigma i.succ) (tau j.succ)
  have hpivot_row : |Aperm 0 j.succ| ≤ maxEntryNorm (Nat.succ_pos m) A := by
    exact entry_le_maxEntryNorm (Nat.succ_pos m) A r (tau j.succ)
  have hnum_le : |Aperm i.succ 0| ≤ |Aperm 0 0| := by
    have hraw := hchoice.2.2.1 (sigma i.succ) (Nat.zero_le _)
    simpa [Aperm, higham9_2_rowColPermutedMatrix,
      higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix, sigma, tau,
      higham9_7_firstPivotRowSwap] using hraw
  have hratio : |Aperm i.succ 0 / Aperm 0 0| ≤ 1 := by
    have hpiv_abs_pos : 0 < |Aperm 0 0| := abs_pos.mpr hpivB
    calc
      |Aperm i.succ 0 / Aperm 0 0|
          = |Aperm i.succ 0| / |Aperm 0 0| := by rw [abs_div]
      _ ≤ |Aperm 0 0| / |Aperm 0 0| :=
          div_le_div_of_nonneg_right hnum_le (abs_nonneg _)
      _ = 1 := div_self (ne_of_gt hpiv_abs_pos)
  have hterm :
      |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| ≤
        maxEntryNorm (Nat.succ_pos m) A := by
    calc
      |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0|
          = |Aperm i.succ 0 / Aperm 0 0| * |Aperm 0 j.succ| := by
            rw [abs_div, abs_mul, abs_div]
            ring
      _ ≤ 1 * |Aperm 0 j.succ| :=
            mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
      _ ≤ 1 * maxEntryNorm (Nat.succ_pos m) A :=
            mul_le_mul_of_nonneg_left hpivot_row zero_le_one
      _ = maxEntryNorm (Nat.succ_pos m) A := by ring
  unfold luFirstSchurComplement
  calc
    |Aperm i.succ j.succ - Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0|
        ≤ |Aperm i.succ j.succ| +
            |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (Aperm i.succ j.succ)
              (-(Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0))
    _ ≤ maxEntryNorm (Nat.succ_pos m) A + maxEntryNorm (Nat.succ_pos m) A :=
        add_le_add hentry hterm
    _ = 2 * maxEntryNorm (Nat.succ_pos m) A := by ring

/-- **Equation (9.16) / rook-pivoting growth support**, first-step max-entry
Schur-complement doubling bound.  This is an elementary trace dependency for
rook pivoting, not Foster's sharper product theorem. -/
theorem higham9_16_rookPivot_firstSchurComplement_maxEntryNorm_le_two {m : ℕ}
    (hm : 0 < m) (A : Fin (m + 1) → Fin (m + 1) → ℝ) {r s : Fin (m + 1)}
    (hchoice : higham9_1_rookPivotChoice A 0 r s)
    (hpivot : A r s ≠ 0) :
    maxEntryNorm hm
        (luFirstSchurComplement
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s))) ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact higham9_16_rookPivot_firstSchurComplement_entry_abs_le_two
    A hchoice hpivot i j

/-- **Equation (9.16) / rook-pivoting trace support**, elementary recursive
entry-growth bound for any explicit rook-pivoting `U` trace.  This proves a
bounded cumulative-growth connection for the trace surface; Foster's sharper
rook-pivoting bound remains a separate source theorem. -/
theorem higham9_16_RookPivotGEUTrace_entry_abs_le_pow_two :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_16_RookPivotGEUTrace n A U →
      ∀ (hn : 0 < n) (i j : Fin n),
        |U i j| ≤ (2 : ℝ) ^ (n - 1) * maxEntryNorm hn A := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro hn
      omega
  | step hchoice hpivot hnext ih =>
      rename_i m A r s U₁
      intro hn i j
      let sigma := higham9_7_firstPivotRowSwap r
      let tau := higham9_7_firstPivotRowSwap s
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
        higham9_2_rowColPermutedMatrix A sigma tau
      by_cases hi : i = 0
      · subst i
        have hrow : |Aperm 0 j| ≤ maxEntryNorm (Nat.succ_pos m) A := by
          simpa [Aperm, higham9_2_rowColPermutedMatrix,
            higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix, sigma, tau,
            higham9_7_firstPivotRowSwap] using
            entry_le_maxEntryNorm (Nat.succ_pos m) A r (tau j)
        have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ m := by
          simpa using
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le m)
        have hM_nonneg : 0 ≤ maxEntryNorm (Nat.succ_pos m) A :=
          maxEntryNorm_nonneg (Nat.succ_pos m) A
        have hrow_pow :
            |Aperm 0 j| ≤ (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
          calc
            |Aperm 0 j| ≤ maxEntryNorm (Nat.succ_pos m) A := hrow
            _ = (1 : ℝ) * maxEntryNorm (Nat.succ_pos m) A := by ring
            _ ≤ (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A :=
                mul_le_mul_of_nonneg_right hpow_ge_one hM_nonneg
        simpa [Aperm, luFirstStepU] using hrow_pow
      · by_cases hj : j = 0
        · subst j
          have hnonneg :
              0 ≤ (2 : ℝ) ^ ((m + 1) - 1) *
                  maxEntryNorm (Nat.succ_pos m) A :=
            mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((m + 1) - 1))
              (maxEntryNorm_nonneg (Nat.succ_pos m) A)
          simpa [Aperm, luFirstStepU, hi] using hnonneg
        · have hm : 0 < m := by
            by_contra hm0
            have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
            subst hmzero
            have hival : i.val = 0 := by omega
            exact hi (Fin.ext hival)
          have hrec := ih hm (i.pred hi) (j.pred hj)
          let S : Fin m → Fin m → ℝ :=
            luFirstSchurComplement Aperm
          have hS_bound :
              maxEntryNorm hm S ≤ 2 * maxEntryNorm (Nat.succ_pos m) A := by
            simpa [S, Aperm, sigma, tau] using
              higham9_16_rookPivot_firstSchurComplement_maxEntryNorm_le_two
                hm A hchoice hpivot
          have hcoef_nonneg : 0 ≤ (2 : ℝ) ^ (m - 1) :=
            pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (m - 1)
          have hpow : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
            have hmidx : m = (m - 1) + 1 := by omega
            calc
              (2 : ℝ) ^ m = (2 : ℝ) ^ ((m - 1) + 1) :=
                congrArg (fun k : ℕ => (2 : ℝ) ^ k) hmidx
              _ = (2 : ℝ) ^ (m - 1) * 2 := by
                exact pow_succ (2 : ℝ) (m - 1)
          have hpow_step :
              (2 : ℝ) ^ (m - 1) * (2 * maxEntryNorm (Nat.succ_pos m) A) =
                (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
            rw [hpow]
            ring
          have htail :
              |U₁ (i.pred hi) (j.pred hj)| ≤
                (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
            calc
              |U₁ (i.pred hi) (j.pred hj)|
                  ≤ (2 : ℝ) ^ (m - 1) * maxEntryNorm hm S := by
                      simpa [S] using hrec
              _ ≤ (2 : ℝ) ^ (m - 1) *
                    (2 * maxEntryNorm (Nat.succ_pos m) A) :=
                  mul_le_mul_of_nonneg_left hS_bound hcoef_nonneg
              _ = (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := hpow_step
          simpa [Aperm, luFirstStepU, hi, hj] using htail

/-- **Equation (9.16) / rook-pivoting trace support**, elementary
growth-factor bound for any explicit recursive rook-pivoting `U` trace.  The
source Foster product bound remains open. -/
theorem higham9_16_RookPivotGEUTrace_growthFactorEntry_le_pow_two {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (htrace : higham9_16_RookPivotGEUTrace n A U) :
    growthFactorEntry hn A U hAmax ≤ (2 : ℝ) ^ (n - 1) := by
  apply growthFactorEntry_le_of_entry_bound_factor hn A U ((2 : ℝ) ^ (n - 1)) hAmax
  exact higham9_16_RookPivotGEUTrace_entry_abs_le_pow_two htrace hn

/-- **Equation (9.16) / rook-pivoting trace support**, every nonsingular real
matrix admits an explicit recursive rook-pivoting upper-factor trace.  The
existence proof uses a complete pivot as a valid first rook pivot; it does not
prove Foster's rook-pivoting growth bound. -/
theorem higham9_16_exists_RookPivotGEUTrace_of_det_ne_zero :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∃ U : Fin n → Fin n → ℝ,
        higham9_16_RookPivotGEUTrace n A U := by
  intro n
  induction n with
  | zero =>
      intro A _hdet
      exact ⟨A, higham9_16_RookPivotGEUTrace.done⟩
  | succ m ih =>
      intro A hdet
      obtain ⟨r, s, hcomplete, hpivot⟩ :=
        higham9_1_exists_first_completePivotChoice_pivot_ne_zero_of_det_ne_zero
          A hdet
      have hrook : higham9_1_rookPivotChoice A 0 r s :=
        higham9_1_rookPivotChoice_of_completePivotChoice A 0 r s hcomplete
      let S : Fin m → Fin m → ℝ :=
        luFirstSchurComplement
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s))
      have hdetS :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
        simpa [S] using
          higham9_1_firstCompletePivotSchurComplement_det_ne_zero_of_det_ne_zero
            A hpivot hdet
      obtain ⟨U₁, hU₁⟩ := ih (A := S) hdetS
      refine
        ⟨luFirstStepU
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r)
            (higham9_7_firstPivotRowSwap s)) U₁, ?_⟩
      simpa [S] using
        higham9_16_RookPivotGEUTrace.step hrook hpivot hU₁

/-- **Equation (9.16) / rook-pivoting trace support**, source-facing existence
of a triangular exposed upper-factor trace for every nonsingular real input.
This constructs the recursive exact trace only; it does not prove the Foster
rook-pivoting growth bound. -/
theorem higham9_16_exists_RookPivotGEUTrace_upper_zero_of_det_ne_zero
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ U : Fin n → Fin n → ℝ,
      higham9_16_RookPivotGEUTrace n A U ∧
        ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
  obtain ⟨U, hU⟩ :=
    higham9_16_exists_RookPivotGEUTrace_of_det_ne_zero (A := A) hdet
  exact ⟨U, hU, higham9_16_RookPivotGEUTrace_upper_zero hU⟩

/-- **Equation (9.16) / rook-pivoting trace support**, source-facing
elementary growth package for nonsingular real inputs.  This combines the
recursive rook trace existence theorem with the elementary trace-level bound
`rho <= 2^(n-1)`; Foster's sharper product bound remains separate. -/
theorem higham9_16_exists_RookPivotGEUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ U : Fin n → Fin n → ℝ,
      higham9_16_RookPivotGEUTrace n A U ∧
        growthFactorEntry hn A U hAmax ≤ (2 : ℝ) ^ (n - 1) := by
  obtain ⟨U, hU⟩ :=
    higham9_16_exists_RookPivotGEUTrace_of_det_ne_zero (A := A) hdet
  exact ⟨U, hU,
    higham9_16_RookPivotGEUTrace_growthFactorEntry_le_pow_two hn A U hAmax hU⟩

/-- **Equation (9.16) / rook-pivoting trace growth family**, trace-level
rook-pivoting growth values in dimension `n`.

This set ranges over the recursive rook-pivoting `U` traces formalized above.
It records the elementary trace-growth surface; Foster's sharper product bound
remains a separate theorem. -/
def higham9_16_rookPivotingUTraceGrowthValues (n : ℕ) : Set ℝ :=
  { r | ∃ hn : 0 < n,
      ∃ A U : Fin n → Fin n → ℝ,
      ∃ hApos : 0 < maxEntryNorm hn A,
        higham9_16_RookPivotGEUTrace n A U ∧
          r = growthFactorEntry hn A U hApos }

/-- **Equation (9.16) / rook-pivoting trace growth family**, trace-level
rook-pivoting growth supremum. -/
noncomputable def higham9_16_rookPivotingUTraceGrowthSup (n : ℕ) : ℝ :=
  sSup (higham9_16_rookPivotingUTraceGrowthValues n)

/-- **Equation (9.16) / rook-pivoting trace growth family**, every trace-level
rook-pivoting growth value satisfies the elementary `2^(n-1)` bound. -/
theorem higham9_16_rookPivotingUTraceGrowthValues_le_pow_two {n : ℕ} {r : ℝ}
    (hr : r ∈ higham9_16_rookPivotingUTraceGrowthValues n) :
    r ≤ (2 : ℝ) ^ (n - 1) := by
  rcases hr with ⟨hn, A, U, hApos, htrace, rfl⟩
  exact higham9_16_RookPivotGEUTrace_growthFactorEntry_le_pow_two
    hn A U hApos htrace

/-- **Equation (9.16) / rook-pivoting trace growth family**, the trace-level
rook-pivoting growth values are bounded above by the elementary `2^(n-1)`
bound. -/
theorem higham9_16_rookPivotingUTraceGrowthValues_bddAbove (n : ℕ) :
    BddAbove (higham9_16_rookPivotingUTraceGrowthValues n) := by
  refine ⟨(2 : ℝ) ^ (n - 1), ?_⟩
  intro r hr
  exact higham9_16_rookPivotingUTraceGrowthValues_le_pow_two (n := n) hr

/-- **Equation (9.16) / rook-pivoting trace growth family**, every trace-level
rook-pivoting growth value is bounded by the trace-level supremum. -/
theorem higham9_16_rookPivotingUTraceGrowth_le_sup {n : ℕ} {r : ℝ}
    (hr : r ∈ higham9_16_rookPivotingUTraceGrowthValues n) :
    r ≤ higham9_16_rookPivotingUTraceGrowthSup n := by
  exact le_csSup (higham9_16_rookPivotingUTraceGrowthValues_bddAbove n) hr

/-- **Equation (9.16) / rook-pivoting trace growth family**, the trace-level
rook-pivoting growth-value family is nonempty in every positive dimension. -/
theorem higham9_16_rookPivotingUTraceGrowthValues_nonempty {n : ℕ}
    (hn : 0 < n) :
    (higham9_16_rookPivotingUTraceGrowthValues n).Nonempty := by
  let A : Fin n → Fin n → ℝ := higham9_7_wilkinsonGrowthMatrix (n := n)
  have hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    exact higham9_7_PartialPivotNoInterchangeTrace_det_ne_zero
      (by
        simpa [A] using higham9_7_wilkinsonGrowth_noInterchangeTrace n)
  let hApos : 0 < maxEntryNorm hn A :=
    by simpa [A] using higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_pos hn
  obtain ⟨U, htrace⟩ :=
    higham9_16_exists_RookPivotGEUTrace_of_det_ne_zero (A := A) hdet
  refine ⟨growthFactorEntry hn A U hApos, ?_⟩
  exact ⟨hn, A, U, hApos, htrace, rfl⟩

/-- **Equation (9.16) / rook-pivoting trace growth family**, elementary
source-shaped supremum upper bound for recursive rook-pivoting `U` traces. -/
theorem higham9_16_rookPivotingUTraceGrowthSup_le_pow_two {n : ℕ}
    (hn : 0 < n) :
    higham9_16_rookPivotingUTraceGrowthSup n ≤ (2 : ℝ) ^ (n - 1) := by
  apply csSup_le (higham9_16_rookPivotingUTraceGrowthValues_nonempty hn)
  intro r hr
  exact higham9_16_rookPivotingUTraceGrowthValues_le_pow_two hr

/-- **Theorem 9.7 / GEPP trace support**, every nonsingular real matrix admits
an explicit recursive partial-pivoting upper-factor trace. -/
theorem higham9_7_exists_PartialPivotGEPPUTrace_of_det_ne_zero :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∃ U : Fin n → Fin n → ℝ,
        higham9_7_PartialPivotGEPPUTrace n A U := by
  intro n
  induction n with
  | zero =>
      intro A _hdet
      exact ⟨A, higham9_7_PartialPivotGEPPUTrace.done⟩
  | succ m ih =>
      intro A hdet
      obtain ⟨r, hchoice, hpivot⟩ :=
        higham9_10_exists_first_partialPivotChoice_pivot_ne_zero_of_det_ne_zero
          A hdet
      let S : Fin m → Fin m → ℝ :=
        luFirstSchurComplement
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))
      have hdetS :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
        simpa [S] using
          higham9_10_firstSchurComplement_det_ne_zero_of_det_ne_zero
            A hpivot hdet
      obtain ⟨U₁, hU₁⟩ := ih (A := S) hdetS
      refine
        ⟨luFirstStepU
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) U₁, ?_⟩
      simpa [S] using
        higham9_7_PartialPivotGEPPUTrace.step hchoice hpivot hU₁

/-- **Theorem 9.7 (Wilkinson)**, source-facing exact-arithmetic GEPP upper
bound for the explicit recursive partial-pivoting `U` trace:
`rho_n^p <= 2^(n-1)` for every nonsingular input. -/
theorem higham9_7_exists_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ U : Fin n → Fin n → ℝ,
      higham9_7_PartialPivotGEPPUTrace n A U ∧
        growthFactorEntry hn A U hAmax ≤ (2 : ℝ) ^ (n - 1) := by
  obtain ⟨U, hU⟩ :=
    higham9_7_exists_PartialPivotGEPPUTrace_of_det_ne_zero (A := A) hdet
  exact ⟨U, hU,
    higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two hn A U hAmax hU⟩

/-- **Theorem 9.7**, source-facing upper-bound plus attainability package.
Every nonsingular real matrix admits the closed partial-pivoting `U` trace with
`rho_n^p <= 2^(n-1)`, and the Wilkinson family attains this value. -/
theorem higham9_7_partialPivoting_growth_bound_and_attainment {n : ℕ}
    (hn : 0 < n) :
    (∀ A : Fin n → Fin n → ℝ,
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
        ∀ hAmax : 0 < maxEntryNorm hn A,
          ∃ U : Fin n → Fin n → ℝ,
            higham9_7_PartialPivotGEPPUTrace n A U ∧
              growthFactorEntry hn A U hAmax ≤ (2 : ℝ) ^ (n - 1)) ∧
      ∃ A L U : Fin n → Fin n → ℝ,
      ∃ hAmax : 0 < maxEntryNorm hn A,
        LUFactSpec n A L U ∧
        higham9_7_PartialPivotNoInterchangeTrace 0 n A ∧
      growthFactorEntry hn A U hAmax = (2 : ℝ) ^ (n - 1) := by
  constructor
  · intro A hdet hAmax
    exact higham9_7_exists_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero
      hn A hdet hAmax
  · exact higham9_7_wilkinsonGrowth_attains_partialPivoting_bound hn

/-- **Theorem 9.7 / equation (9.10)**, trace-level partial-pivoting growth
values in dimension `n`.

This is the source-facing `rho_n^p` value family for the exact recursive GEPP
`U` traces formalized above.  It deliberately ranges over traces, not over a
floating-point implementation certificate. -/
def higham9_partialPivotingUTraceGrowthValues (n : ℕ) : Set ℝ :=
  { r | ∃ hn : 0 < n,
      ∃ A U : Fin n → Fin n → ℝ,
      ∃ hApos : 0 < maxEntryNorm hn A,
        higham9_7_PartialPivotGEPPUTrace n A U ∧
          r = growthFactorEntry hn A U hApos }

/-- **Theorem 9.7 / equation (9.10)**, trace-level partial-pivoting growth
supremum. -/
noncomputable def higham9_partialPivotingUTraceGrowthSup (n : ℕ) : ℝ :=
  sSup (higham9_partialPivotingUTraceGrowthValues n)

/-- **Theorem 9.7 / equation (9.10)**, the trace-level partial-pivoting
growth values are bounded above by Wilkinson's `2^(n-1)` bound. -/
theorem higham9_partialPivotingUTraceGrowthValues_bddAbove (n : ℕ) :
    BddAbove (higham9_partialPivotingUTraceGrowthValues n) := by
  refine ⟨(2 : ℝ) ^ (n - 1), ?_⟩
  intro r hr
  rcases hr with ⟨hn, A, U, hApos, htrace, rfl⟩
  exact higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two
    hn A U hApos htrace

/-- **Theorem 9.7 / equation (9.10)**, every trace-level partial-pivoting
growth value is bounded by the trace-level supremum. -/
theorem higham9_partialPivotingUTraceGrowth_le_sup {n : ℕ} {r : ℝ}
    (hr : r ∈ higham9_partialPivotingUTraceGrowthValues n) :
    r ≤ higham9_partialPivotingUTraceGrowthSup n := by
  exact le_csSup (higham9_partialPivotingUTraceGrowthValues_bddAbove n) hr

/-- **Theorem 9.7 / equation (9.10)**, the trace-level GEPP growth-value
family is nonempty in every positive dimension. -/
theorem higham9_partialPivotingUTraceGrowthValues_nonempty {n : ℕ}
    (hn : 0 < n) :
    (higham9_partialPivotingUTraceGrowthValues n).Nonempty := by
  let A : Fin n → Fin n → ℝ := higham9_7_wilkinsonGrowthMatrix (n := n)
  have hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    exact higham9_7_PartialPivotNoInterchangeTrace_det_ne_zero
      (by
        simpa [A] using higham9_7_wilkinsonGrowth_noInterchangeTrace n)
  let hApos : 0 < maxEntryNorm hn A :=
    by simpa [A] using higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_pos hn
  obtain ⟨U, htrace, _hbound⟩ :=
    higham9_7_exists_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero
      hn A hdet hApos
  refine
    ⟨growthFactorEntry hn A U hApos, ?_⟩
  exact ⟨hn, A, U, hApos, htrace, rfl⟩

/-- **Theorem 9.7 / equation (9.10)**, source-shaped supremum form of
Wilkinson's exact GEPP growth bound for recursive partial-pivoting `U` traces. -/
theorem higham9_7_partialPivotingUTraceGrowthSup_le_pow_two {n : ℕ}
    (hn : 0 < n) :
    higham9_partialPivotingUTraceGrowthSup n ≤ (2 : ℝ) ^ (n - 1) := by
  apply csSup_le (higham9_partialPivotingUTraceGrowthValues_nonempty hn)
  intro r hr
  rcases hr with ⟨hn', A, U, hApos, htrace, rfl⟩
  exact higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two
    hn' A U hApos htrace

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, a nonsingular
active Hessenberg trace can be extended recursively to the terminal active
matrix.  This constructs the pivot-choice/Schur-complement trace only; the
separate final-upper-factor row-bound connection remains a further source
target. -/
theorem higham9_10_exists_HessenbergGEPPTrace_terminal {M : ℝ} :
    ∀ {n k : ℕ} {A : Fin n → Fin n → ℝ},
      higham9_10_HessenbergGEPPTrace M k n A →
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∃ B : Fin 0 → Fin 0 → ℝ,
        higham9_10_HessenbergGEPPTrace M (k + n) 0 B := by
  intro n
  induction n with
  | zero =>
      intro k A htrace _hdet
      exact ⟨A, by simpa using htrace⟩
  | succ m ih =>
      intro k A htrace hdet
      obtain ⟨r, hchoice, hpivot⟩ :=
        higham9_10_exists_first_partialPivotChoice_pivot_ne_zero_of_det_ne_zero
          A hdet
      let S : Fin m → Fin m → ℝ :=
        luFirstSchurComplement
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))
      have htraceS : higham9_10_HessenbergGEPPTrace M (k + 1) m S := by
        exact higham9_10_HessenbergGEPPTrace.step htrace hchoice hpivot
      have hdetS :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
        simpa [S] using
          higham9_10_firstSchurComplement_det_ne_zero_of_det_ne_zero
            A hpivot hdet
      obtain ⟨B, hB⟩ := ih (k := k + 1) (A := S) htraceS hdetS
      refine ⟨B, ?_⟩
      have hidx : k + (m + 1) = k + 1 + m := by omega
      simpa [hidx] using hB

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace support**, terminal trace
existence for a nonsingular upper-Hessenberg source matrix, starting from the
source max-entry stage bound. -/
theorem higham9_10_exists_HessenbergGEPPTrace_terminal_of_det_ne_zero {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hH : IsUpperHessenberg n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ B : Fin 0 → Fin 0 → ℝ,
      higham9_10_HessenbergGEPPTrace (maxEntryNorm hn A) (1 + n) 0 B := by
  have hinit : higham9_10_HessenbergGEPPTrace (maxEntryNorm hn A) 1 n A :=
    higham9_10_HessenbergGEPPTrace.init hH
      (higham9_10_HessenbergStageBound_one_of_maxEntryNorm hn A)
  simpa using
    higham9_10_exists_HessenbergGEPPTrace_terminal hinit hdet

/-- **Theorem 9.10 / upper-Hessenberg GEPP `U` trace support**, a nonsingular
active Hessenberg trace recursively produces an exposed upper factor `U`. -/
theorem higham9_10_exists_HessenbergGEPPUTrace_of_trace_det_ne_zero {M : ℝ} :
    ∀ {n k : ℕ} {A : Fin n → Fin n → ℝ},
      higham9_10_HessenbergGEPPTrace M k n A →
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∃ U : Fin n → Fin n → ℝ,
        higham9_10_HessenbergGEPPUTrace M k n A U := by
  intro n
  induction n with
  | zero =>
      intro k A _htrace _hdet
      exact ⟨A, higham9_10_HessenbergGEPPUTrace.done⟩
  | succ m ih =>
      intro k A htrace hdet
      obtain ⟨r, hchoice, hpivot⟩ :=
        higham9_10_exists_first_partialPivotChoice_pivot_ne_zero_of_det_ne_zero
          A hdet
      let S : Fin m → Fin m → ℝ :=
        luFirstSchurComplement
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))
      have htraceS : higham9_10_HessenbergGEPPTrace M (k + 1) m S := by
        exact higham9_10_HessenbergGEPPTrace.step htrace hchoice hpivot
      have hdetS :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
        simpa [S] using
          higham9_10_firstSchurComplement_det_ne_zero_of_det_ne_zero
            A hpivot hdet
      obtain ⟨U₁, hU₁⟩ := ih (k := k + 1) (A := S) htraceS hdetS
      refine
        ⟨luFirstStepU
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) U₁, ?_⟩
      simpa [S] using
        higham9_10_HessenbergGEPPUTrace.step htrace hchoice hpivot hU₁

/-- **Theorem 9.10 / upper-Hessenberg GEPP `U` trace support**, source-facing
existence of the exposed upper-factor trace for a nonsingular upper-Hessenberg
input. -/
theorem higham9_10_exists_HessenbergGEPPUTrace_of_det_ne_zero {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hH : IsUpperHessenberg n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ U : Fin n → Fin n → ℝ,
      higham9_10_HessenbergGEPPUTrace (maxEntryNorm hn A) 1 n A U := by
  have hinit : higham9_10_HessenbergGEPPTrace (maxEntryNorm hn A) 1 n A :=
    higham9_10_HessenbergGEPPTrace.init hH
      (higham9_10_HessenbergStageBound_one_of_maxEntryNorm hn A)
  exact higham9_10_exists_HessenbergGEPPUTrace_of_trace_det_ne_zero hinit hdet

/-- **Theorem 9.10**, the exposed upper factor of an explicit upper-Hessenberg
GEPP `U` trace satisfies Wilkinson's max-entry growth bound `rho_n^p <= n`. -/
theorem higham9_10_HessenbergGEPPUTrace_growthFactorEntry_le_card {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (htrace :
      higham9_10_HessenbergGEPPUTrace (maxEntryNorm hn A) 1 n A U) :
    growthFactorEntry hn A U hA ≤ (n : ℝ) := by
  apply higham9_10_hessenberg_growthFactorEntry_le_card_of_row_bounds hn A U hA
  intro i j
  have hrow :=
    higham9_10_HessenbergGEPPUTrace_row_bound
      (maxEntryNorm_nonneg hn A) htrace i j
  have hidx : 1 + i.val = i.val + 1 := by omega
  simpa [hidx] using hrow

/-- **Theorem 9.10 (Wilkinson)**, source-facing exact-arithmetic
upper-Hessenberg GEPP growth theorem for the explicit recursive `U` trace:
every nonsingular upper-Hessenberg input admits a GEPP upper-factor trace whose
max-entry growth factor is bounded by `n`. -/
theorem higham9_10_exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_of_det_ne_zero
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hH : IsUpperHessenberg n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA : 0 < maxEntryNorm hn A) :
    ∃ U : Fin n → Fin n → ℝ,
      higham9_10_HessenbergGEPPUTrace (maxEntryNorm hn A) 1 n A U ∧
        growthFactorEntry hn A U hA ≤ (n : ℝ) := by
  obtain ⟨U, hU⟩ :=
    higham9_10_exists_HessenbergGEPPUTrace_of_det_ne_zero hn A hH hdet
  exact
    ⟨U, hU,
      higham9_10_HessenbergGEPPUTrace_growthFactorEntry_le_card hn A U hA hU⟩

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace growth family**, trace-level
upper-Hessenberg GEPP growth values in dimension `n`.

This set ranges over recursive GEPP `U` traces started from nonsingular
upper-Hessenberg source matrices. -/
def higham9_10_hessenbergGEPPUTraceGrowthValues (n : ℕ) : Set ℝ :=
  { r | ∃ hn : 0 < n,
      ∃ A U : Fin n → Fin n → ℝ,
      ∃ hApos : 0 < maxEntryNorm hn A,
        IsUpperHessenberg n A ∧
          higham9_10_HessenbergGEPPUTrace (maxEntryNorm hn A) 1 n A U ∧
            r = growthFactorEntry hn A U hApos }

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace growth family**, trace-level
upper-Hessenberg GEPP growth supremum. -/
noncomputable def higham9_10_hessenbergGEPPUTraceGrowthSup (n : ℕ) : ℝ :=
  sSup (higham9_10_hessenbergGEPPUTraceGrowthValues n)

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace growth family**, every
trace-level upper-Hessenberg GEPP growth value satisfies Wilkinson's `n`
bound. -/
theorem higham9_10_hessenbergGEPPUTraceGrowthValues_le_card {n : ℕ} {r : ℝ}
    (hr : r ∈ higham9_10_hessenbergGEPPUTraceGrowthValues n) :
    r ≤ (n : ℝ) := by
  rcases hr with ⟨hn, A, U, hApos, _hH, htrace, rfl⟩
  exact higham9_10_HessenbergGEPPUTrace_growthFactorEntry_le_card
    hn A U hApos htrace

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace growth family**, the
trace-level upper-Hessenberg GEPP growth values are bounded above by `n`. -/
theorem higham9_10_hessenbergGEPPUTraceGrowthValues_bddAbove (n : ℕ) :
    BddAbove (higham9_10_hessenbergGEPPUTraceGrowthValues n) := by
  refine ⟨(n : ℝ), ?_⟩
  intro r hr
  exact higham9_10_hessenbergGEPPUTraceGrowthValues_le_card hr

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace growth family**, every
trace-level upper-Hessenberg GEPP growth value is bounded by the trace-level
supremum. -/
theorem higham9_10_hessenbergGEPPUTraceGrowth_le_sup {n : ℕ} {r : ℝ}
    (hr : r ∈ higham9_10_hessenbergGEPPUTraceGrowthValues n) :
    r ≤ higham9_10_hessenbergGEPPUTraceGrowthSup n := by
  exact le_csSup
    (higham9_10_hessenbergGEPPUTraceGrowthValues_bddAbove n) hr

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace growth family**, the
trace-level upper-Hessenberg GEPP growth-value family is nonempty in every
positive dimension. -/
theorem higham9_10_hessenbergGEPPUTraceGrowthValues_nonempty {n : ℕ}
    (hn : 0 < n) :
    (higham9_10_hessenbergGEPPUTraceGrowthValues n).Nonempty := by
  let A : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0
  have hH : IsUpperHessenberg n A := by
    intro i j hij
    have hne : i ≠ j := by
      intro h
      subst i
      omega
    simp [A, hne]
  have hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    have hmat : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst i
        simp [A]
      · simp [A, hij]
    rw [hmat, Matrix.det_one]
    norm_num
  have hApos : 0 < maxEntryNorm hn A := by
    have hentry : |A (⟨0, hn⟩ : Fin n) ⟨0, hn⟩| = 1 := by
      simp [A]
    have hle :=
      entry_le_maxEntryNorm hn A (⟨0, hn⟩ : Fin n) ⟨0, hn⟩
    have hone : (1 : ℝ) ≤ maxEntryNorm hn A := by
      simpa [hentry] using hle
    exact lt_of_lt_of_le zero_lt_one hone
  obtain ⟨U, htrace⟩ :=
    higham9_10_exists_HessenbergGEPPUTrace_of_det_ne_zero hn A hH hdet
  refine ⟨growthFactorEntry hn A U hApos, ?_⟩
  exact ⟨hn, A, U, hApos, hH, htrace, rfl⟩

/-- **Theorem 9.10 / upper-Hessenberg GEPP trace growth family**, source-shaped
supremum form of Wilkinson's exact upper-Hessenberg GEPP growth bound for
recursive `U` traces. -/
theorem higham9_10_hessenbergGEPPUTraceGrowthSup_le_card {n : ℕ}
    (hn : 0 < n) :
    higham9_10_hessenbergGEPPUTraceGrowthSup n ≤ (n : ℝ) := by
  apply csSup_le (higham9_10_hessenbergGEPPUTraceGrowthValues_nonempty hn)
  intro r hr
  exact higham9_10_hessenbergGEPPUTraceGrowthValues_le_card hr

/-- **Theorem 9.9**, column diagonally dominant nonsingular matrices have an
exact no-pivot LU factorization whose unit-lower factor has entries bounded by
one in absolute value.  This closes the source local claim that column diagonal
dominance supplies unit multipliers for Gaussian elimination without pivoting;
the separate max-entry growth theorem `ρ_n <= 2` remains open. -/
theorem higham9_9_colDiagDominant_lu_exists_unit_lower_of_det_ne_zero :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℝ,
      IsDiagDominant n A →
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∃ L U : Fin n → Fin n → ℝ,
        LUFactSpec n A L U ∧ ∀ i j : Fin n, |L i j| ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro A _hDD _hdet
      refine ⟨(fun i _j => Fin.elim0 i), (fun i _j => Fin.elim0 i), ?_, ?_⟩
      · refine
          { L_diag := ?_
            L_upper_zero := ?_
            U_lower_zero := ?_
            product_eq := ?_ }
        · intro i
          exact Fin.elim0 i
        · intro i _j _hij
          exact Fin.elim0 i
        · intro i _j _hij
          exact Fin.elim0 i
        · intro i _j
          exact Fin.elim0 i
      · intro i _j
        exact Fin.elim0 i
  | succ m ih =>
      intro A hDD hdet
      have hpivot : A 0 0 ≠ 0 :=
        (higham9_9_colDiagDominant_diag_ne_zero_of_det_ne_zero hDD hdet) 0
      let S : Fin m → Fin m → ℝ := higham9_1_firstSchurComplement A
      have hS_DD : IsDiagDominant m S := by
        simpa [S] using higham9_9_colDiagDominant_firstSchurComplement hDD hpivot
      have hS_det :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
        simpa [S] using
          higham9_9_colDiagDominant_firstSchurComplement_det_ne_zero hpivot hdet
      obtain ⟨L₁, U₁, hLU₁, hL₁_bound⟩ := ih S hS_DD hS_det
      let L : Fin (m + 1) → Fin (m + 1) → ℝ := luFirstStepL A L₁
      let U : Fin (m + 1) → Fin (m + 1) → ℝ := luFirstStepU A U₁
      refine ⟨L, U, ?_, ?_⟩
      · exact LUFactSpec.of_firstSchurComplement_explicit hpivot hLU₁
      · intro i j
        by_cases hi : i = 0
        · subst i
          by_cases hj : j = 0
          · simp [L, luFirstStepL, hj]
          · simp [L, luFirstStepL, hj]
        · by_cases hj : j = 0
          · have hratio : |A i 0 / A 0 0| ≤ 1 :=
              higham9_9_colDiagDominant_entry_ratio_abs_le_one hDD hi hpivot
            simpa [L, luFirstStepL, hi, hj] using hratio
          · simpa [L, luFirstStepL, hi, hj] using hL₁_bound (i.pred hi) (j.pred hj)

/-- **Theorem 9.9**, source-facing exact no-pivot LU existence/uniqueness for
nonsingular column diagonally dominant matrices, with the constructed lower
factor's entries bounded by one.  Uniqueness is the ordinary exact-LU uniqueness
consequence of nonsingularity, not a pivot-trace theorem. -/
theorem higham9_9_colDiagDominant_lu_exists_unique_unit_lower_of_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hDD : IsDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    (∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧ ∀ i j : Fin n, |L i j| ≤ 1) ∧
      ∀ {L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ},
        LUFactSpec n A L₁ U₁ →
        LUFactSpec n A L₂ U₂ →
          L₁ = L₂ ∧ U₁ = U₂ := by
  refine ⟨higham9_9_colDiagDominant_lu_exists_unit_lower_of_det_ne_zero n A hDD hdet, ?_⟩
  intro L₁ U₁ L₂ U₂ hLU₁ hLU₂
  exact higham9_1_lu_unique_of_pivots_ne_zero hLU₁ hLU₂
    ((higham9_1_det_ne_zero_iff_pivots_ne_zero hLU₁).mp hdet)

/-- **Theorem 9.13**, source-facing exact-LU existence and componentwise
growth package for nonsingular column-diagonally-dominant tridiagonal
matrices.  The no-pivot LU existence theorem supplies exact factors with
unit-bounded lower entries; the tridiagonal growth theorem then gives
`|L||U| <= 3|A|` for those factors. -/
theorem higham9_13_colDiagDom_exists_LUFactSpec_growth_bound_3 {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
      (∀ i j : Fin n, |L i j| ≤ 1) ∧
      (∀ i j : Fin n,
        ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j|) := by
  obtain ⟨L, U, hLU, hL_bound⟩ :=
    higham9_9_colDiagDominant_lu_exists_unit_lower_of_det_ne_zero
      n A hColDom hdetA
  refine ⟨L, U, hLU, hL_bound, ?_⟩
  exact higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
    A L U hLU hdetA hA_tridiag hColDom

/-- **Theorem 9.13**, source-facing exact-LU existence and max-entry growth
package for nonsingular column-diagonally-dominant tridiagonal matrices.  This
is the existential form of the source `rho <= 3` conclusion for the exact
no-pivot LU factors produced from column diagonal dominance. -/
theorem higham9_13_colDiagDom_exists_LUFactSpec_growthFactorEntry_le_three
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hColDom : IsDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
      (∀ i j : Fin n, |L i j| ≤ 1) ∧
      (∀ i j : Fin n,
        ∑ k : Fin n, |L i k| * |U k j| ≤ 3 * |A i j|) ∧
      growthFactorEntry hn A U hAmax ≤ 3 := by
  obtain ⟨L, U, hLU, hL_bound, hGrowth⟩ :=
    higham9_13_colDiagDom_exists_LUFactSpec_growth_bound_3
      A hdetA hA_tridiag hColDom
  refine ⟨L, U, hLU, hL_bound, hGrowth, ?_⟩
  exact higham9_13_colDiagDom_growthFactorEntry_le_three_of_LUFactSpec
    hn A L U hLU hdetA hA_tridiag hColDom hAmax

/-- **Theorem 9.13**, source-facing row-dominant transpose exact-LU and
componentwise growth package.

For a nonsingular row-diagonally-dominant tridiagonal source matrix `A`, the
transposed problem `Aᵀ` is column-diagonally dominant and tridiagonal.  The
column-dominant exact no-pivot LU package therefore supplies exact factors of
`Aᵀ` with `|L_T||U_T| <= 3|Aᵀ|`.  This theorem deliberately constructs factors
for `Aᵀ`; it is not a direct exact-LU existence theorem for `A` itself. -/
theorem higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growth_bound_3
    {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A) :
    ∃ L_T U_T : Fin n → Fin n → ℝ,
      LUFactSpec n (matTranspose A) L_T U_T ∧
      (∀ i j : Fin n, |L_T i j| ≤ 1) ∧
      (∀ i j : Fin n,
        ∑ k : Fin n, |L_T i k| * |U_T k j| ≤
          3 * |matTranspose A i j|) := by
  have hdetT :
      Matrix.det
        (Matrix.of (matTranspose A) : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    have hmat :
        (Matrix.of (matTranspose A) : Matrix (Fin n) (Fin n) ℝ) =
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ).transpose := by
      ext i j
      rfl
    intro hzero
    apply hdetA
    rw [← Matrix.det_transpose (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)]
    rw [← hmat]
    exact hzero
  exact higham9_13_colDiagDom_exists_LUFactSpec_growth_bound_3
    (matTranspose A) hdetT
    ((higham9_13_tridiagonal_transpose_iff A).2 hA_tridiag)
    ((higham9_9_colDiagDominant_transpose_iff_rowDiagDominant A).2 hRowDom)

/-- **Theorem 9.13**, source-facing row-dominant transpose exact-LU and
max-entry growth package.

This is the existential `rho <= 3` form for the exact no-pivot LU factors of
`Aᵀ` obtained from a nonsingular row-diagonally-dominant tridiagonal source
matrix `A`.  The denominator positivity is stated over `A` and normalized by
`maxEntryNorm Aᵀ = maxEntryNorm A`. -/
theorem higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growthFactorEntry_le_three
    {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hA_tridiag : IsTridiagonal n A)
    (hRowDom : IsRowDiagDominant n A)
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ L_T U_T : Fin n → Fin n → ℝ,
      LUFactSpec n (matTranspose A) L_T U_T ∧
      (∀ i j : Fin n, |L_T i j| ≤ 1) ∧
      (∀ i j : Fin n,
        ∑ k : Fin n, |L_T i k| * |U_T k j| ≤
          3 * |matTranspose A i j|) ∧
      growthFactorEntry hn (matTranspose A) U_T
        (by simpa [maxEntryNorm_matTranspose hn A] using hAmax) ≤ 3 := by
  have hdetT :
      Matrix.det
        (Matrix.of (matTranspose A) : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    have hmat :
        (Matrix.of (matTranspose A) : Matrix (Fin n) (Fin n) ℝ) =
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ).transpose := by
      ext i j
      rfl
    intro hzero
    apply hdetA
    rw [← Matrix.det_transpose (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)]
    rw [← hmat]
    exact hzero
  exact higham9_13_colDiagDom_exists_LUFactSpec_growthFactorEntry_le_three
    hn (matTranspose A) hdetT
    ((higham9_13_tridiagonal_transpose_iff A).2 hA_tridiag)
    ((higham9_9_colDiagDominant_transpose_iff_rowDiagDominant A).2 hRowDom)
    (by simpa [maxEntryNorm_matTranspose hn A] using hAmax)

/-- **Theorem 9.1 support**, Schur-complement inheritance of nonsingular
leading principal blocks.  If all nonempty leading principal blocks of `A` are
nonsingular, then every leading principal block of the first Schur complement
is nonsingular.  This is the determinant step in the no-pivot LU existence
induction. -/
theorem higham9_1_firstSchurComplement_leadingPrincipalBlock_det_ne_zero {m k : ℕ}
    (hk : k ≤ m)
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hlead :
      ∀ t : ℕ, ∀ ht : t ≤ m + 1, t ≠ 0 →
        Matrix.det
          (fun i j : Fin t => A (Fin.castLE ht i) (Fin.castLE ht j)) ≠ 0) :
    Matrix.det
      (fun i j : Fin k =>
        higham9_1_firstSchurComplement A (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0 := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp
  · have hkm : 1 + k ≤ m + 1 := by omega
    have h1m : 1 ≤ m + 1 := by omega
    have hone : (1 : ℕ) ≠ 0 := by omega
    have hpivot : A 0 0 ≠ 0 := by
      have hdet := hlead 1 h1m hone
      simpa using hdet
    let rows : Fin k → Fin (m + 1) :=
      fun i => Fin.succ (Fin.castLE hk i)
    have hrow :
        ∀ r : Fin (1 + k),
          Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows r =
            Fin.castLE hkm r := by
      intro r
      cases r using Fin.addCases
      · apply Fin.ext
        simp [Fin.castLE]
      · apply Fin.ext
        simp [rows, Fin.castLE]
        omega
    have hschurMatrix :
        (fun r c : Fin k => higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) =
          (fun i j : Fin k =>
            higham9_1_firstSchurComplement A (Fin.castLE hk i) (Fin.castLE hk j)) := by
      ext i j
      simp [rows, higham9_6_firstSchurUpdate, higham9_1_firstSchurComplement,
        luFirstSchurComplement]
      field_simp [hpivot]
    have hsourceMatrix :
        (fun r c : Fin (1 + k) =>
            A
              (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows r)
              (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows c)) =
          (fun r c : Fin (1 + k) =>
            A (Fin.castLE hkm r) (Fin.castLE hkm c)) := by
      ext r c
      rw [hrow r, hrow c]
    have hid :=
      higham9_6_pivot_mul_schur_det_eq_source_minor
        (n := m + 1) (k := k) A (p := (0 : Fin (m + 1))) rows rows hpivot
    have hsource_ne :
        Matrix.det
          (fun r c : Fin (1 + k) =>
            A
              (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows r)
              (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows c)) ≠ 0 := by
      simpa [hsourceMatrix] using hlead (1 + k) hkm (by omega)
    have hmul_ne :
        A 0 0 *
          Matrix.det
            (fun r c : Fin k => higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) ≠ 0 := by
      simpa [hid] using hsource_ne
    have hschur_ne :
        Matrix.det
          (fun r c : Fin k => higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) ≠ 0 :=
      (mul_ne_zero_iff.mp hmul_ne).2
    simpa [hschurMatrix] using hschur_ne

/-- **Theorem 9.1**, exact no-pivot LU existence from nonsingular leading
principal submatrices.  Under the source condition that every nonempty leading
principal block of `A` has nonzero determinant, there exist exact unit-lower
and upper-triangular factors `L` and `U` with `A = L * U`. -/
theorem higham9_1_lu_exists_of_leadingPrincipalBlock_det_ne_zero :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℝ,
      (∀ k : ℕ, ∀ hk : k ≤ n, k ≠ 0 →
        Matrix.det
          (fun i j : Fin k => A (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0) →
      ∃ L U : Fin n → Fin n → ℝ, LUFactSpec n A L U := by
  intro n
  induction n with
  | zero =>
      intro A _hlead
      refine ⟨(fun _ _ => 0), (fun _ _ => 0), ?_⟩
      refine
        { L_diag := ?_
          L_upper_zero := ?_
          U_lower_zero := ?_
          product_eq := ?_ }
      · intro i
        exact Fin.elim0 i
      · intro i _j _hij
        exact Fin.elim0 i
      · intro i _j _hij
        exact Fin.elim0 i
      · intro i _j
        exact Fin.elim0 i
  | succ m ih =>
      intro A hlead
      have h1m : 1 ≤ m + 1 := by omega
      have hpivot : A 0 0 ≠ 0 := by
        have hdet := hlead 1 h1m (by omega)
        simpa using hdet
      let S : Fin m → Fin m → ℝ := higham9_1_firstSchurComplement A
      have hSlead :
          ∀ k : ℕ, ∀ hk : k ≤ m, k ≠ 0 →
            Matrix.det
              (fun i j : Fin k => S (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0 := by
        intro k hk _hk0
        simpa [S] using
          higham9_1_firstSchurComplement_leadingPrincipalBlock_det_ne_zero hk hlead
      obtain ⟨L₁, U₁, hLU₁⟩ := ih S hSlead
      exact higham9_1_lu_exists_of_firstSchurComplement hpivot hLU₁

/-- **Theorem 9.1**, exact no-pivot LU uniqueness under nonsingular leading
principal submatrices.  The same source leading-minor hypothesis makes every
diagonal pivot in any exact LU certificate nonzero, so the Doolittle
recurrence uniqueness theorem applies. -/
theorem higham9_1_lu_unique_of_leadingPrincipalBlock_det_ne_zero {n : ℕ}
    {A L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ}
    (hlead :
      ∀ k : ℕ, ∀ hk : k ≤ n, k ≠ 0 →
        Matrix.det
          (fun i j : Fin k => A (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0)
    (hLU₁ : LUFactSpec n A L₁ U₁)
    (hLU₂ : LUFactSpec n A L₂ U₂) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  have hUdiag : ∀ k : Fin n, U₁ k k ≠ 0 := by
    by_cases hn0 : n = 0
    · intro k
      subst n
      exact Fin.elim0 k
    · have hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
        have hlead_full := hlead n le_rfl hn0
        simpa using hlead_full
      exact hLU₁.det_ne_zero_iff_U_diag_ne_zero.mp hdet
  exact higham9_1_lu_unique_of_pivots_ne_zero hLU₁ hLU₂ hUdiag

/-- **Theorem 9.1**, exact no-pivot LU existence and uniqueness from
nonsingular leading principal submatrices.  This packages the source theorem:
under nonzero leading principal minors, the exact no-pivot LU factorization
exists and any two exact certificates are equal. -/
theorem higham9_1_lu_exists_and_unique_of_leadingPrincipalBlock_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hlead :
      ∀ k : ℕ, ∀ hk : k ≤ n, k ≠ 0 →
        Matrix.det
          (fun i j : Fin k => A (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0) :
    (∃ L U : Fin n → Fin n → ℝ, LUFactSpec n A L U) ∧
      ∀ {L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ},
        LUFactSpec n A L₁ U₁ →
        LUFactSpec n A L₂ U₂ →
          L₁ = L₂ ∧ U₁ = U₂ :=
  ⟨higham9_1_lu_exists_of_leadingPrincipalBlock_det_ne_zero n A hlead,
    fun hLU₁ hLU₂ =>
      higham9_1_lu_unique_of_leadingPrincipalBlock_det_ne_zero hlead hLU₁ hLU₂⟩

/-- **Theorem 9.1 base case**, every `1 by 1` matrix has an exact no-pivot
unit-lower/upper LU certificate. -/
theorem higham9_1_lu_exists_one (A : Fin 1 → Fin 1 → ℝ) :
    ∃ L U : Fin 1 → Fin 1 → ℝ, LUFactSpec 1 A L U := by
  refine ⟨(fun _ _ => 1), A, ?_⟩
  refine
    { L_diag := ?_
      L_upper_zero := ?_
      U_lower_zero := ?_
      product_eq := ?_ }
  · intro i
    fin_cases i
    rfl
  · intro i j hij
    fin_cases i
    fin_cases j
    exact (Nat.lt_irrefl 0 hij).elim
  · intro i j hij
    fin_cases i
    fin_cases j
    exact (Nat.lt_irrefl 0 hij).elim
  · intro i j
    fin_cases i
    fin_cases j
    simp

/-- **Theorem 9.1 support**, source-strength Schur-complement inheritance for
proper leading principal blocks.  Higham's condition only requires
`A(1:k,1:k)` nonsingular for `k = 1 : n-1`; this lemma transfers exactly those
proper leading-minor hypotheses to the first Schur complement. -/
theorem higham9_1_firstSchurComplement_properLeadingPrincipalBlock_det_ne_zero {m k : ℕ}
    (hk : k < m)
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hlead :
      ∀ t : ℕ, ∀ ht : t < m + 1, t ≠ 0 →
        Matrix.det
          (fun i j : Fin t => A (Fin.castLE (Nat.le_of_lt ht) i)
            (Fin.castLE (Nat.le_of_lt ht) j)) ≠ 0) :
    Matrix.det
      (fun i j : Fin k =>
        higham9_1_firstSchurComplement A (Fin.castLE (Nat.le_of_lt hk) i)
          (Fin.castLE (Nat.le_of_lt hk) j)) ≠ 0 := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp
  · have hkm_lt : 1 + k < m + 1 := by omega
    have hkm : 1 + k ≤ m + 1 := Nat.le_of_lt hkm_lt
    have h1_lt : 1 < m + 1 := by omega
    have hpivot : A 0 0 ≠ 0 := by
      have hdet := hlead 1 h1_lt (by omega)
      simpa using hdet
    let hk_le : k ≤ m := Nat.le_of_lt hk
    let rows : Fin k → Fin (m + 1) :=
      fun i => Fin.succ (Fin.castLE hk_le i)
    have hrow :
        ∀ r : Fin (1 + k),
          Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows r =
            Fin.castLE hkm r := by
      intro r
      cases r using Fin.addCases
      · apply Fin.ext
        simp [Fin.castLE]
      · apply Fin.ext
        simp [rows, Fin.castLE]
        omega
    have hschurMatrix :
        (fun r c : Fin k => higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) =
          (fun i j : Fin k =>
            higham9_1_firstSchurComplement A (Fin.castLE hk_le i) (Fin.castLE hk_le j)) := by
      ext i j
      simp [rows, higham9_6_firstSchurUpdate, higham9_1_firstSchurComplement,
        luFirstSchurComplement]
      field_simp [hpivot]
    have hsourceMatrix :
        (fun r c : Fin (1 + k) =>
            A
              (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows r)
              (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows c)) =
          (fun r c : Fin (1 + k) =>
            A (Fin.castLE hkm r) (Fin.castLE hkm c)) := by
      ext r c
      rw [hrow r, hrow c]
    have hid :=
      higham9_6_pivot_mul_schur_det_eq_source_minor
        (n := m + 1) (k := k) A (p := (0 : Fin (m + 1))) rows rows hpivot
    have hsource_ne :
        Matrix.det
          (fun r c : Fin (1 + k) =>
            A
              (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows r)
              (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows c)) ≠ 0 := by
      simpa [hsourceMatrix] using hlead (1 + k) hkm_lt (by omega)
    have hmul_ne :
        A 0 0 *
          Matrix.det
            (fun r c : Fin k => higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) ≠ 0 := by
      simpa [hid] using hsource_ne
    have hschur_ne :
        Matrix.det
          (fun r c : Fin k => higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) ≠ 0 :=
      (mul_ne_zero_iff.mp hmul_ne).2
    simpa [hschurMatrix, hk_le] using hschur_ne

/-- **Theorem 9.1**, exact no-pivot LU existence from Higham's proper
leading-principal nonsingularity condition: `A(1:k,1:k)` is nonsingular for
`k = 1 : n-1`.  Unlike the stronger all-leading-block corollary above, this
does not assume that the full matrix is nonsingular. -/
theorem higham9_1_lu_exists_of_properLeadingPrincipalBlock_det_ne_zero :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℝ,
      (∀ k : ℕ, ∀ hk : k < n, k ≠ 0 →
        Matrix.det
          (fun i j : Fin k => A (Fin.castLE (Nat.le_of_lt hk) i)
            (Fin.castLE (Nat.le_of_lt hk) j)) ≠ 0) →
      ∃ L U : Fin n → Fin n → ℝ, LUFactSpec n A L U := by
  intro n
  induction n with
  | zero =>
      intro A _hlead
      refine ⟨(fun _ _ => 0), (fun _ _ => 0), ?_⟩
      refine
        { L_diag := ?_
          L_upper_zero := ?_
          U_lower_zero := ?_
          product_eq := ?_ }
      · intro i
        exact Fin.elim0 i
      · intro i _j _hij
        exact Fin.elim0 i
      · intro i _j _hij
        exact Fin.elim0 i
      · intro i _j
        exact Fin.elim0 i
  | succ m ih =>
      intro A hlead
      by_cases hm0 : m = 0
      · subst m
        exact higham9_1_lu_exists_one A
      · have h1_lt : 1 < m + 1 := by omega
        have hpivot : A 0 0 ≠ 0 := by
          have hdet := hlead 1 h1_lt (by omega)
          simpa using hdet
        let S : Fin m → Fin m → ℝ := higham9_1_firstSchurComplement A
        have hSlead :
            ∀ k : ℕ, ∀ hk : k < m, k ≠ 0 →
              Matrix.det
                (fun i j : Fin k => S (Fin.castLE (Nat.le_of_lt hk) i)
                  (Fin.castLE (Nat.le_of_lt hk) j)) ≠ 0 := by
          intro k hk _hk0
          simpa [S] using
            higham9_1_firstSchurComplement_properLeadingPrincipalBlock_det_ne_zero hk hlead
        obtain ⟨L₁, U₁, hLU₁⟩ := ih S hSlead
        exact higham9_1_lu_exists_of_firstSchurComplement hpivot hLU₁

/-- **Theorem 9.1 support**, uniqueness of exact LU certificates when all
proper pivots are nonzero.  The final column of a unit lower triangular factor
is forced by triangularity and the diagonal, so the last pivot need not be
nonzero. -/
theorem higham9_1_lu_unique_of_proper_pivots_ne_zero {n : ℕ}
    {A L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ}
    (hLU₁ : LUFactSpec n A L₁ U₁)
    (hLU₂ : LUFactSpec n A L₂ U₂)
    (hU₁diag : ∀ k : Fin n, k.val + 1 < n → U₁ k k ≠ 0) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  classical
  have hstage :
      ∀ t : ℕ, t ≤ n →
        ∀ k : Fin n, k.val < t →
          (∀ j : Fin n, U₁ k j = U₂ k j) ∧
            (∀ i : Fin n, L₁ i k = L₂ i k) := by
    intro t
    induction t with
    | zero =>
        intro _ k hk
        exact (Nat.not_lt_zero _ hk).elim
    | succ t ih =>
        intro ht k hk
        have ht_le : t ≤ n := Nat.le_trans (Nat.le_succ t) ht
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | hk_eq
        · exact ih ht_le k hk_lt
        · have ht_lt_n : t < n := Nat.lt_of_succ_le ht
          let kk : Fin n := ⟨t, ht_lt_n⟩
          have hk_eq_fin : k = kk := Fin.ext hk_eq
          subst k
          have hprev :
              ∀ s : Fin n, s.val < kk.val →
                (∀ j : Fin n, U₁ s j = U₂ s j) ∧
                  (∀ i : Fin n, L₁ i s = L₂ i s) := by
            intro s hs
            exact ih ht_le s hs
          have hUeq : ∀ j : Fin n, U₁ kk j = U₂ kk j := by
            intro j
            have hrec₁ :=
              higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec hLU₁ kk j
            have hrec₂ :=
              higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec hLU₂ kk j
            have hprefix :
                higham9_2_rectPrefixDot L₁ U₁ kk j kk =
                  higham9_2_rectPrefixDot L₂ U₂ kk j kk := by
              unfold higham9_2_rectPrefixDot
              apply Finset.sum_congr rfl
              intro s _
              by_cases hs : s.val < kk.val
              · have hp := hprev s hs
                simp [hs, hp.2 kk, hp.1 j]
              · simp [hs]
            rw [hrec₁, hrec₂]
            unfold higham9_2_rectDoolittleUUpdate
            simp [higham9_2_rectRow, hprefix]
          have hLeq : ∀ i : Fin n, L₁ i kk = L₂ i kk := by
            intro i
            by_cases hproper : kk.val + 1 < n
            · have hU₂diag : U₂ kk kk ≠ 0 := by
                rw [← hUeq kk]
                exact hU₁diag kk hproper
              have hrec₁ :=
                higham9_2_rectDoolittleLUpdate_eq_of_LUFactSpec hLU₁ i kk
                  (hU₁diag kk hproper)
              have hrec₂ :=
                higham9_2_rectDoolittleLUpdate_eq_of_LUFactSpec hLU₂ i kk
                  hU₂diag
              have hprefix :
                  higham9_2_rectPrefixDot L₁ U₁ i kk kk =
                    higham9_2_rectPrefixDot L₂ U₂ i kk kk := by
                unfold higham9_2_rectPrefixDot
                apply Finset.sum_congr rfl
                intro s _
                by_cases hs : s.val < kk.val
                · have hp := hprev s hs
                  simp [hs, hp.2 i, hp.1 kk]
                · simp [hs]
              rw [hrec₁, hrec₂]
              unfold higham9_2_rectDoolittleLUpdate
              simp [hprefix, hUeq kk]
            · have hi_le : i.val ≤ kk.val := by
                have hi_lt : i.val < kk.val + 1 := by omega
                exact Nat.le_of_lt_succ hi_lt
              by_cases hik : i = kk
              · subst i
                rw [hLU₁.L_diag kk, hLU₂.L_diag kk]
              · have hi_lt : i.val < kk.val := lt_of_le_of_ne hi_le (by
                  intro hval
                  exact hik (Fin.ext hval))
                rw [hLU₁.L_upper_zero i kk hi_lt, hLU₂.L_upper_zero i kk hi_lt]
          exact ⟨hUeq, hLeq⟩
  constructor
  · funext i j
    exact (hstage n (Nat.le_refl n) j j.isLt).2 i
  · funext i j
    exact (hstage n (Nat.le_refl n) i i.isLt).1 j

/-- **Theorem 9.1**, exact no-pivot LU uniqueness from Higham's proper
leading-principal nonsingularity condition. -/
theorem higham9_1_lu_unique_of_properLeadingPrincipalBlock_det_ne_zero {n : ℕ}
    {A L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ}
    (hlead :
      ∀ k : ℕ, ∀ hk : k < n, k ≠ 0 →
        Matrix.det
          (fun i j : Fin k => A (Fin.castLE (Nat.le_of_lt hk) i)
            (Fin.castLE (Nat.le_of_lt hk) j)) ≠ 0)
    (hLU₁ : LUFactSpec n A L₁ U₁)
    (hLU₂ : LUFactSpec n A L₂ U₂) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  apply higham9_1_lu_unique_of_proper_pivots_ne_zero hLU₁ hLU₂
  intro k hkproper
  let t : ℕ := k.val + 1
  have htlt : t < n := hkproper
  have htne : t ≠ 0 := by omega
  have hdet := hlead t htlt htne
  have hiff :=
    higham9_1_leadingPrincipalBlock_det_ne_zero_iff_pivots_ne_zero
      (Nat.le_of_lt htlt) hLU₁
  have hpivots := hiff.mp hdet
  let kt : Fin t := ⟨k.val, by omega⟩
  have hcast : Fin.castLE (Nat.le_of_lt htlt) kt = k := by
    apply Fin.ext
    simp [kt, t]
  have hkdiag := hpivots kt
  simpa [hcast] using hkdiag

/-- **Theorem 9.1**, exact no-pivot LU existence and uniqueness from
Higham's source condition that `A(1:k,1:k)` is nonsingular for
`k = 1 : n-1`. -/
theorem higham9_1_lu_exists_and_unique_of_properLeadingPrincipalBlock_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hlead :
      ∀ k : ℕ, ∀ hk : k < n, k ≠ 0 →
        Matrix.det
          (fun i j : Fin k => A (Fin.castLE (Nat.le_of_lt hk) i)
            (Fin.castLE (Nat.le_of_lt hk) j)) ≠ 0) :
    (∃ L U : Fin n → Fin n → ℝ, LUFactSpec n A L U) ∧
      ∀ {L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ},
        LUFactSpec n A L₁ U₁ →
        LUFactSpec n A L₂ U₂ →
          L₁ = L₂ ∧ U₁ = U₂ :=
  ⟨higham9_1_lu_exists_of_properLeadingPrincipalBlock_det_ne_zero n A hlead,
    fun hLU₁ hLU₂ =>
      higham9_1_lu_unique_of_properLeadingPrincipalBlock_det_ne_zero hlead hLU₁ hLU₂⟩

/-- **Problem 9.1 support**, a zero proper pivot makes an exact LU
factorization nonunique.  The proof applies the elementary lower shear
`E = I + e_(k+1,k)` to `L` and `E⁻¹` to `U`; upper triangularity of the new
`U` is preserved exactly because `u_kk = 0`. -/
theorem higham9_1_lu_nonunique_of_zero_proper_pivot {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    {k : Fin n} (hk : k.val + 1 < n)
    (hzero : U k k = 0) :
    ∃ L' U' : Fin n → Fin n → ℝ,
      LUFactSpec n A L' U' ∧ L' ≠ L := by
  classical
  let kp : Fin n := ⟨k.val + 1, hk⟩
  have hk_ne_kp : k ≠ kp := by
    intro h
    have := congrArg Fin.val h
    simp [kp] at this
  let L' : Fin n → Fin n → ℝ :=
    fun i j => L i j + if j = k then L i kp else 0
  let U' : Fin n → Fin n → ℝ :=
    fun i j => U i j - if i = kp then U k j else 0
  refine ⟨L', U', ?_, ?_⟩
  · refine
      { L_diag := ?_
        L_upper_zero := ?_
        U_lower_zero := ?_
        product_eq := ?_ }
    · intro i
      by_cases hik : i = k
      · subst i
        have hkp_gt : k.val < kp.val := by simp [kp]
        simp [L', hLU.L_diag, hLU.L_upper_zero k kp hkp_gt]
      · simp [L', hik, hLU.L_diag]
    · intro i j hij
      by_cases hjk : j = k
      · subst j
        have hi_kp : i.val < kp.val := by
          simp [kp]
          omega
        simp [L', hLU.L_upper_zero i k hij, hLU.L_upper_zero i kp hi_kp]
      · simp [L', hjk, hLU.L_upper_zero i j hij]
    · intro i j hij
      by_cases hikp : i = kp
      · subst i
        have hj_le_k : j.val ≤ k.val := by
          simp [kp] at hij
          omega
        by_cases hjk : j = k
        · subst j
          simp [U', hLU.U_lower_zero kp k (by simp [kp]), hzero]
        · have hj_lt_k : j.val < k.val := lt_of_le_of_ne hj_le_k (by
            intro hval
            exact hjk (Fin.ext hval))
          simp [U', hLU.U_lower_zero kp j hij, hLU.U_lower_zero k j hj_lt_k]
      · simp [U', hikp, hLU.U_lower_zero i j hij]
    · intro i j
      have hterm :
          ∀ s : Fin n,
            L' i s * U' s j =
              L i s * U s j +
                (if s = k then L i kp * U k j else 0) -
                (if s = kp then L i kp * U k j else 0) := by
        intro s
        by_cases hsk : s = k
        · subst s
          simp [L', U', hk_ne_kp, add_mul]
        · by_cases hskp : s = kp
          · subst s
            simp [L', U', hk_ne_kp.symm]
            ring
          · simp [L', U', hsk, hskp]
      calc
        (∑ s : Fin n, L' i s * U' s j)
            = ∑ s : Fin n,
                (L i s * U s j +
                  (if s = k then L i kp * U k j else 0) -
                  (if s = kp then L i kp * U k j else 0)) := by
              apply Finset.sum_congr rfl
              intro s _
              exact hterm s
        _ = (∑ s : Fin n, L i s * U s j) := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = A i j := hLU.product_eq i j
  · intro hEq
    have hentry := congrFun (congrFun hEq kp) k
    have hdiag : L kp kp = 1 := hLU.L_diag kp
    simp [L', hdiag] at hentry

/-- **Problem 9.1**, if an exact LU factorization exists and is unique, then
all proper leading principal blocks are nonsingular.  This is the source
converse used when `A` itself may be singular: a singular proper leading block
forces a zero proper pivot in any exact LU certificate, and the lower-shear
lemma above constructs a second certificate. -/
theorem higham_problem9_1_properLeadingPrincipalBlock_det_ne_zero_of_unique_lu {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hunique :
      ∀ {L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ},
        LUFactSpec n A L₁ U₁ →
        LUFactSpec n A L₂ U₂ →
          L₁ = L₂ ∧ U₁ = U₂) :
    ∀ k : ℕ, ∀ hk : k < n, k ≠ 0 →
      Matrix.det
        (fun i j : Fin k => A (Fin.castLE (Nat.le_of_lt hk) i)
          (Fin.castLE (Nat.le_of_lt hk) j)) ≠ 0 := by
  classical
  intro k hk _hk0
  let hk_le : k ≤ n := Nat.le_of_lt hk
  have hiff :=
    higham9_1_leadingPrincipalBlock_det_ne_zero_iff_pivots_ne_zero hk_le hLU
  intro hdet_zero
  have hnot_all :
      ¬ ∀ i : Fin k, U (Fin.castLE hk_le i) (Fin.castLE hk_le i) ≠ 0 := by
    intro hpiv
    exact (hiff.mpr hpiv) hdet_zero
  push_neg at hnot_all
  obtain ⟨r, hrzero⟩ := hnot_all
  let rr : Fin n := Fin.castLE hk_le r
  have hproper : rr.val + 1 < n := by
    have hr_lt_k : r.val < k := r.isLt
    simp [rr, Fin.castLE]
    omega
  obtain ⟨L', U', hLU', hL_ne⟩ :=
    higham9_1_lu_nonunique_of_zero_proper_pivot hLU hproper hrzero
  have hsame := hunique hLU' hLU
  exact hL_ne hsame.1

/-- **Theorem 9.1**, source-strength iff form: an exact no-pivot LU
factorization exists and is unique iff all proper leading principal blocks
`A(1:k,1:k)`, `k = 1 : n-1`, are nonsingular. -/
theorem higham9_1_lu_exists_unique_iff_properLeadingPrincipalBlock_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ} :
    ((∃ L U : Fin n → Fin n → ℝ, LUFactSpec n A L U) ∧
      ∀ {L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ},
        LUFactSpec n A L₁ U₁ →
        LUFactSpec n A L₂ U₂ →
          L₁ = L₂ ∧ U₁ = U₂) ↔
      ∀ k : ℕ, ∀ hk : k < n, k ≠ 0 →
        Matrix.det
          (fun i j : Fin k => A (Fin.castLE (Nat.le_of_lt hk) i)
            (Fin.castLE (Nat.le_of_lt hk) j)) ≠ 0 := by
  constructor
  · rintro ⟨⟨L, U, hLU⟩, hunique⟩
    exact higham_problem9_1_properLeadingPrincipalBlock_det_ne_zero_of_unique_lu hLU hunique
  · intro hlead
    exact higham9_1_lu_exists_and_unique_of_properLeadingPrincipalBlock_det_ne_zero hlead

/-- **Problem 9.2**, if `sigma` avoids the finite danger union, then the
shifted matrix `sigma I - A` satisfies Higham Theorem 9.1's proper-leading
minor hypothesis. -/
theorem higham9_2_shiftedMatrix_properLeadingPrincipalBlock_det_ne_zero_of_not_mem_danger
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {sigma : ℝ}
    (hsigma : sigma ∉ higham9_2_shiftedMatrixDangerSet A) :
    ∀ k : ℕ, ∀ hk : k < n, k ≠ 0 →
      Matrix.det
        (fun i j : Fin k =>
          (higham9_2_shiftedMatrix A sigma)
            (Fin.castLE (Nat.le_of_lt hk) i)
            (Fin.castLE (Nat.le_of_lt hk) j)) ≠ 0 := by
  classical
  intro k hk _hk0
  have hk_mem : k ∈ Finset.range n := Finset.mem_range.mpr hk
  have hdet :=
    higham9_2_shiftedLeadingBlock_det_ne_zero_of_not_mem_danger_union
      A sigma hk_mem (by simpa [higham9_2_shiftedMatrixDangerSet] using hsigma)
  have hmatrix :
      (fun i j : Fin k =>
          (higham9_2_shiftedMatrix A sigma)
            (Fin.castLE (Nat.le_of_lt hk) i)
            (Fin.castLE (Nat.le_of_lt hk) j)) =
        higham9_2_shiftedLeadingBlock A sigma k := by
    ext i j
    apply congrArg₂ Sub.sub
    · by_cases hij : i = j
      · subst j
        simp [Matrix.diagonal]
      · have hcast_ne :
          Fin.castLE (Nat.le_of_lt hk) i ≠ Fin.castLE (Nat.le_of_lt hk) j := by
            intro h
            exact hij (Fin.ext (by simpa [Fin.castLE] using congrArg Fin.val h))
        simp [Matrix.diagonal, hij, hcast_ne]
    · simp [higham9_2_leadingPrincipalBlock, Nat.le_of_lt hk]
      apply congrArg₂ A
      · exact Fin.ext rfl
      · exact Fin.ext rfl
  simpa [hmatrix] using hdet

/-- **Problem 9.2**, any shift outside the Appendix A danger union gives a
unique exact no-pivot LU factorization of `sigma I - A`. -/
theorem higham9_2_shiftedMatrix_lu_exists_unique_of_not_mem_danger {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {sigma : ℝ}
    (hsigma : sigma ∉ higham9_2_shiftedMatrixDangerSet A) :
    ((∃ L U : Fin n → Fin n → ℝ,
        LUFactSpec n (higham9_2_shiftedMatrix A sigma) L U) ∧
      ∀ {L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ},
        LUFactSpec n (higham9_2_shiftedMatrix A sigma) L₁ U₁ →
        LUFactSpec n (higham9_2_shiftedMatrix A sigma) L₂ U₂ →
          L₁ = L₂ ∧ U₁ = U₂) := by
  exact higham9_1_lu_exists_and_unique_of_properLeadingPrincipalBlock_det_ne_zero
    (higham9_2_shiftedMatrix_properLeadingPrincipalBlock_det_ne_zero_of_not_mem_danger
      A hsigma)

/-- **Problem 9.2**, source-facing finite-exception theorem: there is a set of
at most `n(n-1)/2` shifts outside which `sigma I - A` has a unique exact
no-pivot LU factorization. -/
theorem higham_problem9_2_shiftedMatrix_lu_exists_unique_except_card_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ danger : Finset ℝ,
      danger.card ≤ n * (n - 1) / 2 ∧
        ∀ sigma : ℝ, sigma ∉ danger →
          ((∃ L U : Fin n → Fin n → ℝ,
              LUFactSpec n (higham9_2_shiftedMatrix A sigma) L U) ∧
            ∀ {L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ},
              LUFactSpec n (higham9_2_shiftedMatrix A sigma) L₁ U₁ →
              LUFactSpec n (higham9_2_shiftedMatrix A sigma) L₂ U₂ →
                L₁ = L₂ ∧ U₁ = U₂) := by
  refine ⟨higham9_2_shiftedMatrixDangerSet A,
    higham9_2_shiftedMatrixDangerSet_card_le A, ?_⟩
  intro sigma hsigma
  exact higham9_2_shiftedMatrix_lu_exists_unique_of_not_mem_danger A hsigma

/-- **Problem 9.6**, the selected `3 by 3` source minor is nonnegative under
source total nonnegativity. -/
theorem higham9_6_totalNonnegative_threeByThreeSubmatrix_det_nonneg {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {p i₁ i₂ j₁ j₂ : Fin n}
    (hi₁ : p.val < i₁.val) (hi₂ : i₁.val < i₂.val)
    (hj₁ : p.val < j₁.val) (hj₂ : j₁.val < j₂.val) :
    0 ≤ Matrix.det (higham9_6_threeByThreeSubmatrix A p i₁ i₂ j₁ j₂) := by
  let rows : Fin 3 → Fin n := fun r => if r = 0 then p else if r = 1 then i₁ else i₂
  let cols : Fin 3 → Fin n := fun c => if c = 0 then p else if c = 1 then j₁ else j₂
  have hrow : StrictMono (fun r : Fin 3 => (rows r).val) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [rows] at hab ⊢
    · exact hi₁
    · exact lt_trans hi₁ hi₂
    · exact hi₂
  have hcol : StrictMono (fun c : Fin 3 => (cols c).val) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [cols] at hab ⊢
    · exact hj₁
    · exact lt_trans hj₁ hj₂
    · exact hj₂
  have h := hTN 3 rows cols hrow hcol
  convert h using 1

/-- **Problem 9.6**, source total nonnegativity and a positive pivot imply
nonnegativity of every `2 by 2` minor of the first Schur update whose rows and
columns lie strictly after the pivot. -/
theorem higham9_6_schur_twoByTwo_det_nonneg_of_totalNonnegative {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {p i₁ i₂ j₁ j₂ : Fin n}
    (hi₁ : p.val < i₁.val) (hi₂ : i₁.val < i₂.val)
    (hj₁ : p.val < j₁.val) (hj₂ : j₁.val < j₂.val)
    (hpivot : 0 < A p p) :
    0 ≤ Matrix.det (higham9_6_twoByTwoSubmatrix
      (fun i j => higham9_6_firstSchurUpdate A p i j) i₁ i₂ j₁ j₂) := by
  have h3 :
      0 ≤ Matrix.det (higham9_6_threeByThreeSubmatrix A p i₁ i₂ j₁ j₂) :=
    higham9_6_totalNonnegative_threeByThreeSubmatrix_det_nonneg hTN hi₁ hi₂ hj₁ hj₂
  have hid := higham9_6_pivot_mul_schur_twoByTwo_det_eq_threeByThree_det
    A (p := p) (i₁ := i₁) (i₂ := i₂) (j₁ := j₁) (j₂ := j₂) (ne_of_gt hpivot)
  have hdiv :
      Matrix.det (higham9_6_twoByTwoSubmatrix
          (fun i j => higham9_6_firstSchurUpdate A p i j) i₁ i₂ j₁ j₂) =
        Matrix.det (higham9_6_threeByThreeSubmatrix A p i₁ i₂ j₁ j₂) / A p p := by
    rw [← hid]
    field_simp [ne_of_gt hpivot]
  rw [hdiv]
  exact div_nonneg h3 (le_of_lt hpivot)

/-- **Problem 9.6**, the basic determinantal inequality supplied by
order-two total nonnegativity:
`a_{i₁j₂} a_{i₂j₁} <= a_{i₁j₁} a_{i₂j₂}` for increasing rows and columns. -/
theorem higham9_6_twoByTwo_determinantal_inequality {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegativeOrderTwo A)
    {i₁ i₂ j₁ j₂ : Fin n}
    (hi : i₁.val < i₂.val) (hj : j₁.val < j₂.val) :
    A i₁ j₂ * A i₂ j₁ ≤ A i₁ j₁ * A i₂ j₂ := by
  have hdet := hTN.2 i₁ i₂ j₁ j₂ hi hj
  rw [higham9_6_twoByTwoSubmatrix_det] at hdet
  linarith

/-- **Problem 9.6**, entrywise nonnegativity projection from the local
order-two total-nonnegativity support predicate. -/
theorem higham9_6_totalNonnegativeOrderTwo_entry_nonneg {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegativeOrderTwo A) :
    ∀ i j : Fin n, 0 ≤ A i j :=
  hTN.1

/-- **Problem 9.6**, nonnegativity of a first-step no-pivot multiplier from
the local total-nonnegativity support predicate and a positive pivot. -/
theorem higham9_6_multiplier_nonneg_of_orderTwo {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegativeOrderTwo A)
    {p i : Fin n} (hpivot : 0 < A p p) :
    0 ≤ A i p / A p p := by
  exact div_nonneg (hTN.1 i p) (le_of_lt hpivot)

/-- **Problem 9.6**, the first Schur-complement update is nonnegative for
trailing entries under the order-two determinant inequality.  This is the
source step `a_ij - l_ip u_pj >= 0`; the recursive nonnegative LU construction
is supplied by the later positive-leading-principal-block theorem. -/
theorem higham9_6_schur_update_nonneg_of_orderTwo {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegativeOrderTwo A)
    {p i j : Fin n}
    (hpi : p.val < i.val) (hpj : p.val < j.val)
    (hpivot : 0 < A p p) :
    0 ≤ A i j - (A i p / A p p) * A p j := by
  have hdet :
      A p j * A i p ≤ A p p * A i j :=
    higham9_6_twoByTwo_determinantal_inequality hTN hpi hpj
  have hden_nonneg : 0 ≤ A p p := le_of_lt hpivot
  have hstep :
      (A i p / A p p) * A p j ≤ A i j := by
    calc
      (A i p / A p p) * A p j
          = (A p j * A i p) / A p p := by
            field_simp [ne_of_gt hpivot]
      _ ≤ (A p p * A i j) / A p p :=
            div_le_div_of_nonneg_right hdet hden_nonneg
      _ = A i j := by
            field_simp [ne_of_gt hpivot]
  linarith

/-- **Problem 9.6**, the first Schur-complement update cannot exceed the
original trailing entry when the pivot row and column are nonnegative. -/
theorem higham9_6_schur_update_le_original_of_orderTwo {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegativeOrderTwo A)
    {p i j : Fin n} (hpivot : 0 < A p p) :
    A i j - (A i p / A p p) * A p j ≤ A i j := by
  have hmult_nonneg : 0 ≤ A i p / A p p :=
    higham9_6_multiplier_nonneg_of_orderTwo hTN hpivot
  have hprod_nonneg : 0 ≤ (A i p / A p p) * A p j :=
    mul_nonneg hmult_nonneg (hTN.1 p j)
  linarith

/-- **Problem 9.6**, source no-growth form for the first Schur-complement
update: under the order-two determinant inequality and a positive pivot, a
trailing updated entry has absolute value bounded by its original entry. -/
theorem higham9_6_abs_schur_update_le_abs_entry_of_orderTwo {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegativeOrderTwo A)
    {p i j : Fin n}
    (hpi : p.val < i.val) (hpj : p.val < j.val)
    (hpivot : 0 < A p p) :
    |A i j - (A i p / A p p) * A p j| ≤ |A i j| := by
  have hnonneg :
      0 ≤ A i j - (A i p / A p p) * A p j :=
    higham9_6_schur_update_nonneg_of_orderTwo hTN hpi hpj hpivot
  have hle :
      A i j - (A i p / A p p) * A p j ≤ A i j :=
    higham9_6_schur_update_le_original_of_orderTwo hTN hpivot
  rw [abs_of_nonneg hnonneg, abs_of_nonneg (hTN.1 i j)]
  exact hle

/-- **Problem 9.6**, source-level total nonnegativity gives nonnegativity of
the first Schur-complement update.  This is the same local step as
`higham9_6_schur_update_nonneg_of_orderTwo`, with the source predicate exposed
on the theorem surface. -/
theorem higham9_6_schur_update_nonneg_of_totalNonnegative {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {p i j : Fin n}
    (hpi : p.val < i.val) (hpj : p.val < j.val)
    (hpivot : 0 < A p p) :
    0 ≤ A i j - (A i p / A p p) * A p j :=
  higham9_6_schur_update_nonneg_of_orderTwo
    (higham9_6_totalNonnegative_to_orderTwo hTN) hpi hpj hpivot

/-- **Problem 9.6**, source-level total nonnegativity gives the first-step
Schur-complement no-growth inequality used in the appendix argument.  The
remaining source gap after the later recursive LU theorem is the cited
determinant inequality and its full reduced-growth integration. -/
theorem higham9_6_abs_schur_update_le_abs_entry_of_totalNonnegative {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {p i j : Fin n}
    (hpi : p.val < i.val) (hpj : p.val < j.val)
    (hpivot : 0 < A p p) :
    |A i j - (A i p / A p p) * A p j| ≤ |A i j| :=
  higham9_6_abs_schur_update_le_abs_entry_of_orderTwo
    (higham9_6_totalNonnegative_to_orderTwo hTN) hpi hpj hpivot

/-- **Problem 9.6**, a source-level totally nonnegative matrix has an
order-two totally nonnegative first Schur update on every strictly ordered
trailing submatrix after a positive pivot.  This packages the local
Sylvester-identity step; the all-minors preservation theorem below supplies
the recursive total-nonnegativity step used by the LU construction. -/
theorem higham9_6_firstSchurUpdate_trailing_orderTwo_of_totalNonnegative {n m : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {p : Fin n} {rows cols : Fin m → Fin n}
    (hrows_p : ∀ i : Fin m, p.val < (rows i).val)
    (hcols_p : ∀ j : Fin m, p.val < (cols j).val)
    (hrows : StrictMono (fun i : Fin m => (rows i).val))
    (hcols : StrictMono (fun j : Fin m => (cols j).val))
    (hpivot : 0 < A p p) :
    higham9_6_IsTotallyNonnegativeOrderTwo
      (fun i j : Fin m => higham9_6_firstSchurUpdate A p (rows i) (cols j)) := by
  refine ⟨?_, ?_⟩
  · intro i j
    exact higham9_6_schur_update_nonneg_of_totalNonnegative hTN
      (hrows_p i) (hcols_p j) hpivot
  · intro i₁ i₂ j₁ j₂ hi hj
    exact higham9_6_schur_twoByTwo_det_nonneg_of_totalNonnegative hTN
      (hrows_p i₁) (hrows hi) (hcols_p j₁) (hcols hj) hpivot

/-- **Problem 9.6**, source-level total nonnegativity is preserved by the
first no-pivot Schur update on any strictly trailing square submatrix after a
positive pivot.  This is the all-minors version of the Appendix A recursive
step; it does not assert LU existence or choose subsequent pivots. -/
theorem higham9_6_firstSchurUpdate_trailing_totalNonnegative_of_totalNonnegative
    {n m : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {p : Fin n} {rows cols : Fin m → Fin n}
    (hrows_p : ∀ i : Fin m, p.val < (rows i).val)
    (hcols_p : ∀ j : Fin m, p.val < (cols j).val)
    (hrows : StrictMono (fun i : Fin m => (rows i).val))
    (hcols : StrictMono (fun j : Fin m => (cols j).val))
    (hpivot : 0 < A p p) :
    higham9_6_IsTotallyNonnegative
      (fun i j : Fin m => higham9_6_firstSchurUpdate A p (rows i) (cols j)) := by
  intro k subRows subCols hsubRows hsubCols
  let rowSel : Fin k → Fin n := fun r => rows (subRows r)
  let colSel : Fin k → Fin n := fun c => cols (subCols c)
  let rowsFull : Fin (1 + k) → Fin n :=
    Fin.addCases (fun _ : Fin 1 => p) rowSel
  let colsFull : Fin (1 + k) → Fin n :=
    Fin.addCases (fun _ : Fin 1 => p) colSel
  have hrowsFull : StrictMono (fun r : Fin (1 + k) => (rowsFull r).val) := by
    intro a b hab
    cases a using Fin.addCases with
    | left a0 =>
        cases b using Fin.addCases with
        | left b0 =>
            fin_cases a0
            fin_cases b0
            omega
        | right b0 =>
            simpa [rowsFull, rowSel] using hrows_p (subRows b0)
    | right a0 =>
        cases b using Fin.addCases with
        | left b0 =>
            fin_cases b0
            change (Fin.natAdd 1 a0).val < (Fin.castAdd k (0 : Fin 1)).val at hab
            simp [Fin.natAdd] at hab
        | right b0 =>
            have hab0 : a0 < b0 := by simpa [rowsFull, rowSel] using hab
            simpa [rowsFull, rowSel] using hrows (hsubRows hab0)
  have hcolsFull : StrictMono (fun c : Fin (1 + k) => (colsFull c).val) := by
    intro a b hab
    cases a using Fin.addCases with
    | left a0 =>
        cases b using Fin.addCases with
        | left b0 =>
            fin_cases a0
            fin_cases b0
            omega
        | right b0 =>
            simpa [colsFull, colSel] using hcols_p (subCols b0)
    | right a0 =>
        cases b using Fin.addCases with
        | left b0 =>
            fin_cases b0
            change (Fin.natAdd 1 a0).val < (Fin.castAdd k (0 : Fin 1)).val at hab
            simp [Fin.natAdd] at hab
        | right b0 =>
            have hab0 : a0 < b0 := by simpa [colsFull, colSel] using hab
            simpa [colsFull, colSel] using hcols (hsubCols hab0)
  have hsource :
      0 ≤ Matrix.det (fun r c : Fin (1 + k) => A (rowsFull r) (colsFull c)) :=
    hTN (1 + k) rowsFull colsFull hrowsFull hcolsFull
  have hid :
      A p p *
          Matrix.det
            (fun r c : Fin k =>
              higham9_6_firstSchurUpdate A p (rowSel r) (colSel c)) =
        Matrix.det (fun r c : Fin (1 + k) => A (rowsFull r) (colsFull c)) := by
    simpa [rowsFull, colsFull, rowSel, colSel] using
      higham9_6_pivot_mul_schur_det_eq_source_minor A rowSel colSel
        (ne_of_gt hpivot)
  have hdet_nonneg :
      0 ≤ Matrix.det
        (fun r c : Fin k =>
          higham9_6_firstSchurUpdate A p (rowSel r) (colSel c)) := by
    have hmul_nonneg :
        0 ≤ A p p *
          Matrix.det
            (fun r c : Fin k =>
              higham9_6_firstSchurUpdate A p (rowSel r) (colSel c)) := by
      simpa [hid] using hsource
    have hmul_nonneg' :
        0 ≤
          Matrix.det
              (fun r c : Fin k =>
                higham9_6_firstSchurUpdate A p (rowSel r) (colSel c)) *
            A p p := by
      simpa [mul_comm] using hmul_nonneg
    exact nonneg_of_mul_nonneg_left hmul_nonneg' hpivot
  simpa [rowSel, colSel] using hdet_nonneg

/-- **Problem 9.6**, nonsingular totally nonnegative matrices have positive
nonempty leading principal determinants.  This removes the non-Split local
gap between source nonsingularity and the positive-leading-block hypothesis
used by the recursive nonnegative LU construction; the separate
Koteljanskii/Fischer determinant inequality cited in the problem hint remains
an independent source claim. -/
theorem higham9_6_leadingPrincipalBlock_det_pos_of_totalNonnegative_det_ne_zero :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℝ,
      higham9_6_IsTotallyNonnegative A →
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∀ k : ℕ, ∀ hk : k ≤ n, k ≠ 0 →
        0 < Matrix.det
          (fun i j : Fin k => A (Fin.castLE hk i) (Fin.castLE hk j)) := by
  intro n
  induction n with
  | zero =>
      intro A _hTN _hdet k hk hk0
      omega
  | succ m ih =>
      intro A hTN hdet k hk hk0
      have hpivot :
          0 < A 0 0 :=
        higham9_6_topLeft_pos_of_totalNonnegative_det_ne_zero hTN hdet
      obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = 1 + t := ⟨k - 1, by omega⟩
      by_cases ht0 : t = 0
      · subst t
        simpa using hpivot
      · have ht_le : t ≤ m := by omega
        let rows : Fin t → Fin (m + 1) := fun i => Fin.succ (Fin.castLE ht_le i)
        have hrows_p : ∀ i : Fin t, (0 : Fin (m + 1)).val < (rows i).val := by
          intro i
          simp [rows]
        have hrows : StrictMono (fun i : Fin t => (rows i).val) := by
          intro i j hij
          simpa [rows] using hij
        let S : Fin m → Fin m → ℝ := higham9_1_firstSchurComplement A
        have hS_update_TN :
            higham9_6_IsTotallyNonnegative
              (fun i j : Fin m =>
                higham9_6_firstSchurUpdate A 0 (Fin.succ i) (Fin.succ j)) :=
          higham9_6_firstSchurUpdate_trailing_totalNonnegative_of_totalNonnegative
            hTN
            (by intro i; simp)
            (by intro i; simp)
            (by intro i j hij; simpa using hij)
            (by intro i j hij; simpa using hij)
            hpivot
        have hS_eq :
            (fun i j : Fin m =>
                higham9_6_firstSchurUpdate A 0 (Fin.succ i) (Fin.succ j)) =
              S := by
          ext i j
          simp [S, higham9_1_firstSchurComplement, luFirstSchurComplement,
            higham9_6_firstSchurUpdate]
          field_simp [ne_of_gt hpivot]
        have hS_TN : higham9_6_IsTotallyNonnegative S := by
          simpa [hS_eq] using hS_update_TN
        have hSdet :
            Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
          simpa [S] using
            higham9_9_colDiagDominant_firstSchurComplement_det_ne_zero
              (m := m) (A := A) (ne_of_gt hpivot) hdet
        have hSlead_pos :
            0 < Matrix.det
              (fun i j : Fin t => S (Fin.castLE ht_le i) (Fin.castLE ht_le j)) :=
          ih S hS_TN hSdet t ht_le ht0
        have hschurMatrix :
            (fun r c : Fin t =>
                higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) =
              (fun i j : Fin t => S (Fin.castLE ht_le i) (Fin.castLE ht_le j)) := by
          ext i j
          simp [S, rows, higham9_1_firstSchurComplement, luFirstSchurComplement,
            higham9_6_firstSchurUpdate]
          field_simp [ne_of_gt hpivot]
        have hupdate_pos :
            0 < Matrix.det
              (fun r c : Fin t =>
                higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) := by
          rw [hschurMatrix]
          exact hSlead_pos
        have hmul_pos :
            0 < A 0 0 *
              Matrix.det
                (fun r c : Fin t =>
                  higham9_6_firstSchurUpdate A 0 (rows r) (rows c)) :=
          mul_pos hpivot hupdate_pos
        have hsourceMatrix :
            (fun r c : Fin (1 + t) =>
                A
                  (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows r)
                  (Fin.addCases (fun _ : Fin 1 => (0 : Fin (m + 1))) rows c)) =
              (fun r c : Fin (1 + t) => A (Fin.castLE hk r) (Fin.castLE hk c)) := by
          ext r c
          congr 2
          · cases r using Fin.addCases
            · apply Fin.ext
              simp [Fin.castLE]
            · apply Fin.ext
              simp [rows, Fin.castLE]
              omega
          · cases c using Fin.addCases
            · apply Fin.ext
              simp [Fin.castLE]
            · apply Fin.ext
              simp [rows, Fin.castLE]
              omega
        have hid :=
          higham9_6_pivot_mul_schur_det_eq_source_minor
            (n := m + 1) (k := t) A (p := (0 : Fin (m + 1))) rows rows
            (ne_of_gt hpivot)
        simpa [hid, hsourceMatrix] using hmul_pos

/-- **Problem 9.6 support**, all-dimensional `p = 1`
Koteljanskii/Fischer principal-block determinant comparison.  The proof uses
the adjacent Desnanot step plus induction on the leading principal block; it
is local Split-2 determinant algebra, not a Split 1 dependency. -/
theorem higham9_6_principalBlock_determinantal_inequality_one_of_totalNonnegative :
    ∀ m : ℕ, ∀ A : Fin (m + 2) → Fin (m + 2) → ℝ,
      higham9_6_IsTotallyNonnegative A →
      Matrix.det (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) ≤
        Matrix.det
            (higham9_2_leadingPrincipalBlock
              (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) 1) *
          Matrix.det
            (higham9_6_trailingPrincipalBlock
              (Matrix.of A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) 1) := by
  intro m
  induction m with
  | zero =>
      intro A hTN
      exact higham9_6_principalBlock_determinantal_inequality_fin_two hTN
  | succ m ih =>
      intro A hTN
      by_cases hdet :
          Matrix.det (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ) = 0
      · exact higham9_6_principalBlock_determinantal_inequality_of_det_eq_zero
          hTN (by omega) hdet
      · let L : Fin (m + 2) → Fin (m + 2) → ℝ :=
          higham9_2_leadingPrincipalBlock
            (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ)
            (m + 2)
        let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
          higham9_6_adjacentMiddleBlock A
        have hrows : StrictMono
            (fun i : Fin (m + 2) =>
              ((⟨i.val, by omega⟩ : Fin (Nat.succ m + 2))).val) := by
          intro i j hij
          simpa using hij
        have hL_TN : higham9_6_IsTotallyNonnegative L := by
          have hsub :=
            higham9_6_totalNonnegative_submatrix
              (A := A) hTN (rows := fun i : Fin (m + 2) =>
                (⟨i.val, by omega⟩ : Fin (Nat.succ m + 2)))
              (cols := fun i : Fin (m + 2) =>
                (⟨i.val, by omega⟩ : Fin (Nat.succ m + 2)))
              hrows hrows
          simpa [L, higham9_2_leadingPrincipalBlock] using hsub
        have hL_ineq :
            Matrix.det (Matrix.of L : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) ≤
              Matrix.det
                  (higham9_2_leadingPrincipalBlock
                    (Matrix.of L : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) 1) *
                Matrix.det
                  (higham9_6_trailingPrincipalBlock
                    (Matrix.of L : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) 1) :=
          ih L hL_TN
        have hLdet_pos :
            0 < Matrix.det (Matrix.of L : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) := by
          have hlead_pos :=
            higham9_6_leadingPrincipalBlock_det_pos_of_totalNonnegative_det_ne_zero
              (Nat.succ m + 2) A hTN hdet (m + 2) (by omega) (by omega)
          simpa [L, higham9_2_leadingPrincipalBlock] using hlead_pos
        have hL_trailing_middle :
            Matrix.det
                (higham9_6_trailingPrincipalBlock
                  (Matrix.of L : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) 1) =
              Matrix.det M := by
          apply congrArg Matrix.det
          ext i j
          simp [L, M, higham9_2_leadingPrincipalBlock,
            higham9_6_trailingPrincipalBlock, higham9_6_adjacentMiddleBlock,
            higham9_6_middleIndex]
          apply congrArg₂ A
          · apply Fin.ext
            simp
            omega
          · apply Fin.ext
            simp
            omega
        have hmiddle_pos : 0 < Matrix.det M := by
          have hpos_pair :=
            higham9_6_principalBlock_dets_pos_of_determinantal_inequality
              hL_TN (by omega : 1 ≤ m + 2) hLdet_pos hL_ineq
          rw [hL_trailing_middle] at hpos_pair
          exact hpos_pair.2
        have hadj :
            Matrix.det (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ) *
                Matrix.det M ≤
              Matrix.det
                  (higham9_2_leadingPrincipalBlock
                    (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ)
                    (m + 2)) *
                Matrix.det
                  (higham9_6_trailingPrincipalBlock
                    (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ) 1) := by
          simpa [M, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            higham9_6_adjacent_desnanot_inequality_of_totalNonnegative
              (m := m + 1) A hTN (ne_of_gt hmiddle_pos)
        have hlead_eq :
            Matrix.det (Matrix.of L : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) =
              Matrix.det
                (higham9_2_leadingPrincipalBlock
                  (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ)
                  (m + 2)) := by
          rfl
        have hL_le :
            Matrix.det
                (higham9_2_leadingPrincipalBlock
                  (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ)
                  (m + 2)) ≤
              Matrix.det
                  (higham9_2_leadingPrincipalBlock
                    (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ) 1) *
                Matrix.det M := by
          have hL_le_raw := hL_ineq
          rw [hlead_eq, hL_trailing_middle] at hL_le_raw
          simpa [L, higham9_2_leadingPrincipalBlock] using hL_le_raw
        have htrail_nonneg :
            0 ≤ Matrix.det
              (higham9_6_trailingPrincipalBlock
                (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ) 1) :=
          higham9_6_totalNonnegative_trailingPrincipalBlock_det_nonneg hTN (by omega)
        have hmul_le :
            Matrix.det
                (higham9_2_leadingPrincipalBlock
                  (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ)
                  (m + 2)) *
                Matrix.det
                  (higham9_6_trailingPrincipalBlock
                    (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ) 1) ≤
              (Matrix.det
                  (higham9_2_leadingPrincipalBlock
                    (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ) 1) *
                Matrix.det M) *
                Matrix.det
                  (higham9_6_trailingPrincipalBlock
                    (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ) 1) :=
          mul_le_mul_of_nonneg_right hL_le htrail_nonneg
        have hcombo :
            Matrix.det (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ) *
                Matrix.det M ≤
              (Matrix.det
                  (higham9_2_leadingPrincipalBlock
                    (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ) 1) *
                Matrix.det
                  (higham9_6_trailingPrincipalBlock
                    (Matrix.of A : Matrix (Fin (Nat.succ m + 2)) (Fin (Nat.succ m + 2)) ℝ) 1)) *
                Matrix.det M := by
          nlinarith [hadj, hmul_le]
        exact (mul_le_mul_iff_right₀ hmiddle_pos).mp (by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hcombo)

/-- **Problem 9.6 support**, source-shaped `p = 1`
Koteljanskii/Fischer determinant comparison for every nonempty order. -/
theorem higham9_6_principalBlock_determinantal_inequality_one
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hn : 1 ≤ n) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
      Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) 1) *
        Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 1) := by
  cases n with
  | zero =>
      omega
  | succ n =>
      cases n with
      | zero =>
          simpa using higham9_6_principalBlock_determinantal_inequality_full A
      | succ m =>
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            higham9_6_principalBlock_determinantal_inequality_one_of_totalNonnegative
              m A hTN

/-- **Problem 9.6 support**, delete the first row and column of a principal
matrix.  This is the source tail block `A(2:n,2:n)` in one-based indexing. -/
def higham9_6_tailBlock {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => A i.succ j.succ

/-- **Problem 9.6 support**, total nonnegativity is inherited by the tail
principal block. -/
theorem higham9_6_tailBlock_totalNonnegative {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A) :
    higham9_6_IsTotallyNonnegative (higham9_6_tailBlock A) := by
  have hrows : StrictMono (fun i : Fin m => (Fin.succ i : Fin (m + 1)).val) := by
    intro i j hij
    simpa using hij
  simpa [higham9_6_tailBlock] using
    higham9_6_totalNonnegative_submatrix
      (A := A) hTN (rows := fun i : Fin m => Fin.succ i)
      (cols := fun i : Fin m => Fin.succ i) hrows hrows

/-- **Problem 9.6 support**, the full determinant of the tail block is the
determinant of the source trailing principal block at split `p = 1`. -/
theorem higham9_6_tailBlock_det_eq_trailingPrincipalBlock_one {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    Matrix.det (Matrix.of (higham9_6_tailBlock A) : Matrix (Fin m) (Fin m) ℝ) =
      Matrix.det
        (higham9_6_trailingPrincipalBlock
          (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) 1) := by
  apply congrArg Matrix.det
  ext i j
  simp [higham9_6_tailBlock, higham9_6_trailingPrincipalBlock]
  apply congrArg₂ A <;> apply Fin.ext <;> simp <;> omega

/-- **Problem 9.6 support**, a trailing block of the tail block is the
corresponding source trailing block with the split index shifted by one. -/
theorem higham9_6_tailBlock_trailingPrincipalBlock_eq {m p : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    Matrix.det
        (higham9_6_trailingPrincipalBlock
          (Matrix.of (higham9_6_tailBlock A) : Matrix (Fin m) (Fin m) ℝ) p) =
      Matrix.det
        (higham9_6_trailingPrincipalBlock
          (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (p + 1)) := by
  by_cases hp : p ≤ m
  · let e : Fin (m - p) ≃ Fin ((m + 1) - (p + 1)) := finCongr (by omega)
    rw [← Matrix.det_submatrix_equiv_self e
      (higham9_6_trailingPrincipalBlock
        (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (p + 1))]
    apply congrArg Matrix.det
    ext i j
    simp [e, higham9_6_tailBlock, higham9_6_trailingPrincipalBlock, hp]
    apply congrArg₂ A <;> apply Fin.ext <;> simp <;> omega
  · have hpA : ¬p + 1 ≤ m + 1 := by omega
    have hleft : m - p = 0 := by omega
    have hright : (m + 1) - (p + 1) = 0 := by omega
    haveI : IsEmpty (Fin (m - p)) := by
      rw [hleft]
      infer_instance
    haveI : IsEmpty (Fin ((m + 1) - (p + 1))) := by
      rw [hright]
      infer_instance
    simp [higham9_6_trailingPrincipalBlock, hp, hpA, Matrix.det_isEmpty]

/-- **Problem 9.6 support**, the leading block of the tail is the trailing
block at split `1` inside the corresponding leading source block. -/
theorem higham9_6_tailBlock_leading_eq_leading_trailing {m k : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (hk : k ≤ m) :
    Matrix.det
        (higham9_2_leadingPrincipalBlock
          (Matrix.of (higham9_6_tailBlock A) : Matrix (Fin m) (Fin m) ℝ) k) =
      Matrix.det
        (higham9_6_trailingPrincipalBlock
          (higham9_2_leadingPrincipalBlock
            (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (k + 1)) 1) := by
  apply congrArg Matrix.det
  ext i j
  have hk1 : k + 1 ≤ m + 1 := by omega
  simp [higham9_6_tailBlock, higham9_2_leadingPrincipalBlock,
    higham9_6_trailingPrincipalBlock, hk, hk1]
  apply congrArg₂ A <;> apply Fin.ext <;> simp <;> omega

/-- **Problem 9.6 support**, adjacent Desnanot inequality for leading source
blocks, expressed in the two sequences used by the telescoping proof:
`D(0,k)` and `D(1,k)`. -/
theorem higham9_6_leading_adjacent_desnanot_step {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hr : r + 2 ≤ m + 1)
    (hmiddle_ne :
      Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of (higham9_6_tailBlock A) : Matrix (Fin m) (Fin m) ℝ) r) ≠ 0) :
    Matrix.det
        (higham9_2_leadingPrincipalBlock
          (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (r + 2)) *
        Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of (higham9_6_tailBlock A) : Matrix (Fin m) (Fin m) ℝ) r) ≤
      Matrix.det
        (higham9_2_leadingPrincipalBlock
          (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (r + 1)) *
        Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of (higham9_6_tailBlock A) : Matrix (Fin m) (Fin m) ℝ) (r + 1)) := by
  let L : Fin (r + 2) → Fin (r + 2) → ℝ :=
    higham9_2_leadingPrincipalBlock
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (r + 2)
  have hrows : StrictMono
      (fun i : Fin (r + 2) =>
        ((⟨i.val, Nat.lt_of_lt_of_le i.isLt hr⟩ : Fin (m + 1))).val) := by
    intro i j hij
    simpa using hij
  have hL_TN : higham9_6_IsTotallyNonnegative L := by
    have hsub :=
      higham9_6_totalNonnegative_submatrix
        (A := A) hTN
        (rows := fun i : Fin (r + 2) =>
          (⟨i.val, Nat.lt_of_lt_of_le i.isLt hr⟩ : Fin (m + 1)))
        (cols := fun i : Fin (r + 2) =>
          (⟨i.val, Nat.lt_of_lt_of_le i.isLt hr⟩ : Fin (m + 1)))
        hrows hrows
    simpa [L, higham9_2_leadingPrincipalBlock, hr] using hsub
  have hmiddle :
      Matrix.det (higham9_6_adjacentMiddleBlock L) =
        Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of (higham9_6_tailBlock A) : Matrix (Fin m) (Fin m) ℝ) r) := by
    apply congrArg Matrix.det
    ext i j
    have hr_tail : r ≤ m := by omega
    simp [L, higham9_6_adjacentMiddleBlock, higham9_6_middleIndex,
      higham9_2_leadingPrincipalBlock, higham9_6_tailBlock, hr, hr_tail]
  have hadj :
      Matrix.det (Matrix.of L : Matrix (Fin (r + 2)) (Fin (r + 2)) ℝ) *
          Matrix.det (higham9_6_adjacentMiddleBlock L) ≤
        Matrix.det
            (higham9_2_leadingPrincipalBlock
              (Matrix.of L : Matrix (Fin (r + 2)) (Fin (r + 2)) ℝ) (r + 1)) *
          Matrix.det
            (higham9_6_trailingPrincipalBlock
              (Matrix.of L : Matrix (Fin (r + 2)) (Fin (r + 2)) ℝ) 1) := by
    exact higham9_6_adjacent_desnanot_inequality_of_totalNonnegative
      L hL_TN (by simpa [hmiddle] using hmiddle_ne)
  have hfull :
      Matrix.det (Matrix.of L : Matrix (Fin (r + 2)) (Fin (r + 2)) ℝ) =
        Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (r + 2)) := by
    rfl
  have hlead :
      Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of L : Matrix (Fin (r + 2)) (Fin (r + 2)) ℝ) (r + 1)) =
        Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (r + 1)) := by
    apply congrArg Matrix.det
    ext i j
    have hr1 : r + 1 ≤ r + 2 := by omega
    have hr1A : r + 1 ≤ m + 1 := by omega
    simp [L, higham9_2_leadingPrincipalBlock, hr, hr1, hr1A]
  have htrail :
      Matrix.det
          (higham9_6_trailingPrincipalBlock
            (Matrix.of L : Matrix (Fin (r + 2)) (Fin (r + 2)) ℝ) 1) =
        Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of (higham9_6_tailBlock A) : Matrix (Fin m) (Fin m) ℝ) (r + 1)) := by
    apply congrArg Matrix.det
    ext i j
    have hr1_tail : r + 1 ≤ m := by omega
    simp [L, higham9_6_trailingPrincipalBlock, higham9_2_leadingPrincipalBlock,
      higham9_6_tailBlock, hr, hr1_tail]
    apply congrArg₂ A <;> apply Fin.ext <;> simp <;> omega
  rw [hfull, hmiddle, hlead, htrail] at hadj
  exact hadj

/-- **Problem 9.6 support**, telescoping adjacent determinant inequalities.
If `a k = D(0,k)` and `b k = D(1,k)`, adjacent steps
`a(q+1)b(q) <= a(q)b(q+1)` imply the shifted comparison
`a n b p <= a p b n` after cancellation of positive intermediate `b`s. -/
private theorem higham9_6_adjacent_chain_shift
    (a b : ℕ → ℝ) (p n : ℕ)
    (hpn : p ≤ n)
    (hadj : ∀ q : ℕ, p ≤ q → q < n → a (q + 1) * b q ≤ a q * b (q + 1))
    (hbpos : ∀ q : ℕ, p ≤ q → q ≤ n → 0 < b q) :
    a n * b p ≤ a p * b n := by
  induction n, hpn using Nat.le_induction with
  | base =>
      exact le_rfl
  | succ q hpq ih =>
      have ih_shift : a q * b p ≤ a p * b q :=
        ih
          (fun s hps hsq => hadj s hps (Nat.lt_trans hsq (Nat.lt_succ_self q)))
          (fun s hps hsq => hbpos s hps (Nat.le_trans hsq (Nat.le_succ q)))
      have hbp : 0 ≤ b p := le_of_lt (hbpos p (by omega) (by omega))
      have hbq : 0 < b q := hbpos q hpq (by omega)
      have hbq1_nonneg : 0 ≤ b (q + 1) := le_of_lt (hbpos (q + 1) (by omega) (by omega))
      have hstep := hadj q hpq (by omega : q < q + 1)
      have hstep_mul :
          (a (q + 1) * b q) * b p ≤ (a q * b (q + 1)) * b p :=
        mul_le_mul_of_nonneg_right hstep hbp
      have hih_mul :
          (a q * b p) * b (q + 1) ≤ (a p * b q) * b (q + 1) :=
        mul_le_mul_of_nonneg_right ih_shift hbq1_nonneg
      have hcombo :
          (a (q + 1) * b p) * b q ≤ (a p * b (q + 1)) * b q := by
        nlinarith [hstep_mul, hih_mul]
      exact (mul_le_mul_iff_right₀ hbq).mp (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hcombo)

/-- **Problem 9.6**, source-cited Koteljanskii/Fischer principal-block
determinant inequality for every split of a totally nonnegative matrix:
`det A <= det A(1:p,1:p) * det A(p+1:n,p+1:n)`.  The proof is local Split 2
work: adjacent Desnanot inequalities telescope to a shifted determinant
comparison, and the remaining factor is handled by induction on the tail
principal block. -/
theorem higham9_6_principalBlock_determinantal_inequality_of_totalNonnegative :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℝ,
      higham9_6_IsTotallyNonnegative A →
      ∀ p : ℕ, p ≤ n →
        Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
          Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) p) *
            Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) p) := by
  intro n
  induction n with
  | zero =>
      intro A _hTN p hp
      have hp0 : p = 0 := by omega
      subst p
      exact higham9_6_principalBlock_determinantal_inequality_zero A
  | succ m ih =>
      intro A hTN p hp
      by_cases hp0 : p = 0
      · subst p
        exact higham9_6_principalBlock_determinantal_inequality_zero A
      by_cases hpfull : p = m + 1
      · subst p
        exact higham9_6_principalBlock_determinantal_inequality_full A
      by_cases hpone : p = 1
      · subst p
        exact higham9_6_principalBlock_determinantal_inequality_one A hTN (by omega)
      by_cases hdet :
          Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = 0
      · exact higham9_6_principalBlock_determinantal_inequality_of_det_eq_zero
          hTN hp hdet
      · have hdet_pos :
            0 < Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :=
          higham9_6_totalNonnegative_det_pos_of_det_ne_zero hTN hdet
        obtain ⟨q, hq_eq⟩ : ∃ q : ℕ, p = q + 1 := ⟨p - 1, by omega⟩
        subst p
        have hq_ne_zero : q ≠ 0 := by
          intro hq0
          subst q
          exact hpone rfl
        have hq_le_m : q ≤ m := by omega
        have hq_lt_m : q < m := by omega
        let T : Fin m → Fin m → ℝ := higham9_6_tailBlock A
        have hT_TN : higham9_6_IsTotallyNonnegative T := by
          simpa [T] using higham9_6_tailBlock_totalNonnegative (A := A) hTN
        have hineq_one :
            Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≤
              Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) 1) *
                Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 1) :=
          higham9_6_principalBlock_determinantal_inequality_one A hTN (by omega)
        have htail_pos_source :
            0 < Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) 1) :=
          (higham9_6_principalBlock_dets_pos_of_determinantal_inequality
            hTN (by omega : 1 ≤ m + 1) hdet_pos hineq_one).2
        have hTdet_pos :
            0 < Matrix.det (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) := by
          have hraw :
              0 < Matrix.det
                (Matrix.of (higham9_6_tailBlock A) : Matrix (Fin m) (Fin m) ℝ) := by
            rw [higham9_6_tailBlock_det_eq_trailingPrincipalBlock_one]
            exact htail_pos_source
          simpa [T] using hraw
        have hTdet_ne :
            Matrix.det (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
          ne_of_gt hTdet_pos
        have hTlead_pos :
            ∀ k : ℕ, k ≤ m → k ≠ 0 →
              0 < Matrix.det
                (higham9_2_leadingPrincipalBlock
                  (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) k) := by
          intro k hk hk0
          simpa [higham9_2_leadingPrincipalBlock, hk] using
            higham9_6_leadingPrincipalBlock_det_pos_of_totalNonnegative_det_ne_zero
              m T hT_TN hTdet_ne k hk hk0
        have htail_ineq :
            Matrix.det (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) ≤
              Matrix.det
                  (higham9_2_leadingPrincipalBlock
                    (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) q) *
                Matrix.det
                  (higham9_6_trailingPrincipalBlock
                    (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) q) :=
          ih T hT_TN q hq_le_m
        let a : ℕ → ℝ := fun k =>
          Matrix.det
            (higham9_2_leadingPrincipalBlock
              (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) k)
        let b : ℕ → ℝ := fun k =>
          Matrix.det
            (higham9_2_leadingPrincipalBlock
              (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) (k - 1))
        have hbpos :
            ∀ s : ℕ, q + 1 ≤ s → s ≤ m + 1 → 0 < b s := by
          intro s hs hsle
          have hs_pred_le : s - 1 ≤ m := by omega
          have hs_pred_ne : s - 1 ≠ 0 := by omega
          exact hTlead_pos (s - 1) hs_pred_le hs_pred_ne
        have hchain :
            a (m + 1) * b (q + 1) ≤ a (q + 1) * b (m + 1) := by
          apply higham9_6_adjacent_chain_shift a b (q + 1) (m + 1) (by omega)
          · intro s hs hslt
            have hstep :=
              higham9_6_leading_adjacent_desnanot_step
                (m := m) (r := s - 1) A hTN (by omega)
                (by
                  have hb : 0 < b s := hbpos s hs (by omega)
                  exact ne_of_gt hb)
            have hs1 : s - 1 + 1 = s := by omega
            have hs2 : s - 1 + 2 = s + 1 := by omega
            rw [hs1, hs2] at hstep
            simpa [a, b, T] using hstep
          · exact hbpos
        have hshift :
            Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *
                Matrix.det
                  (higham9_2_leadingPrincipalBlock
                    (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) q) ≤
              Matrix.det
                  (higham9_2_leadingPrincipalBlock
                    (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (q + 1)) *
                Matrix.det (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) := by
          simpa [a, b, T, higham9_2_leadingPrincipalBlock] using hchain
        have hlead_nonneg :
            0 ≤ Matrix.det
              (higham9_2_leadingPrincipalBlock
                (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (q + 1)) :=
          higham9_6_totalNonnegative_leadingPrincipalBlock_det_nonneg hTN (by omega)
        have htail_scaled :
            Matrix.det
                (higham9_2_leadingPrincipalBlock
                  (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (q + 1)) *
                Matrix.det (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) ≤
              Matrix.det
                  (higham9_2_leadingPrincipalBlock
                    (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (q + 1)) *
                (Matrix.det
                    (higham9_2_leadingPrincipalBlock
                      (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) q) *
                  Matrix.det
                    (higham9_6_trailingPrincipalBlock
                      (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) q)) :=
          mul_le_mul_of_nonneg_left htail_ineq hlead_nonneg
        have htail_trailing :
            Matrix.det
                (higham9_6_trailingPrincipalBlock
                  (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) q) =
              Matrix.det
                (higham9_6_trailingPrincipalBlock
                  (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (q + 1)) := by
          simpa [T] using higham9_6_tailBlock_trailingPrincipalBlock_eq (m := m) (p := q) A
        have hmiddle_pos :
            0 < Matrix.det
              (higham9_2_leadingPrincipalBlock
                (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) q) :=
          hTlead_pos q hq_le_m hq_ne_zero
        have hcombo :
            Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) *
                Matrix.det
                  (higham9_2_leadingPrincipalBlock
                    (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) q) ≤
              Matrix.det
                  (higham9_2_leadingPrincipalBlock
                    (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (q + 1)) *
                (Matrix.det
                    (higham9_2_leadingPrincipalBlock
                      (Matrix.of T : Matrix (Fin m) (Fin m) ℝ) q) *
                  Matrix.det
                    (higham9_6_trailingPrincipalBlock
                      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (q + 1))) := by
          rw [← htail_trailing]
          exact le_trans hshift htail_scaled
        exact (mul_le_mul_iff_right₀ hmiddle_pos).mp (by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hcombo)

/-- **Problem 9.6**, entrywise nonnegativity of a first Schur update on any
explicit trailing submatrix after a positive pivot. -/
theorem higham9_6_firstSchurUpdate_trailing_nonneg_of_totalNonnegative {n m : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {p : Fin n} {rows cols : Fin m → Fin n}
    (hrows_p : ∀ i : Fin m, p.val < (rows i).val)
    (hcols_p : ∀ j : Fin m, p.val < (cols j).val)
    (hpivot : 0 < A p p) :
    ∀ i j : Fin m,
      0 ≤ higham9_6_firstSchurUpdate A p (rows i) (cols j) := by
  intro i j
  exact higham9_6_schur_update_nonneg_of_totalNonnegative hTN
    (hrows_p i) (hcols_p j) hpivot

/-- **Problem 9.6**, componentwise no-growth of a first Schur update on any
explicit trailing submatrix after a positive pivot.  This is the pointwise
package consumed by recursive no-pivot growth arguments; the all-minors
total-nonnegative preservation theorem is proved separately. -/
theorem higham9_6_firstSchurUpdate_trailing_abs_le_original_of_totalNonnegative
    {n m : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {p : Fin n} {rows cols : Fin m → Fin n}
    (hrows_p : ∀ i : Fin m, p.val < (rows i).val)
    (hcols_p : ∀ j : Fin m, p.val < (cols j).val)
    (hpivot : 0 < A p p) :
    ∀ i j : Fin m,
      |higham9_6_firstSchurUpdate A p (rows i) (cols j)| ≤
        |A (rows i) (cols j)| := by
  intro i j
  exact higham9_6_abs_schur_update_le_abs_entry_of_totalNonnegative hTN
    (hrows_p i) (hcols_p j) hpivot

/-- **Problem 9.6**, max-entry no-growth for the first Schur update restricted
to an explicit trailing submatrix after a positive pivot. -/
theorem higham9_6_firstSchurUpdate_trailing_maxEntryNorm_le_original
    {n m : ℕ} (hm : 0 < m)
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {p : Fin n} {rows cols : Fin m → Fin n}
    (hrows_p : ∀ i : Fin m, p.val < (rows i).val)
    (hcols_p : ∀ j : Fin m, p.val < (cols j).val)
    (hpivot : 0 < A p p) :
    maxEntryNorm hm
        (fun i j : Fin m => higham9_6_firstSchurUpdate A p (rows i) (cols j)) ≤
      maxEntryNorm hm (fun i j : Fin m => A (rows i) (cols j)) :=
  maxEntryNorm_le_of_entry_abs_le hm
    (fun i j : Fin m => higham9_6_firstSchurUpdate A p (rows i) (cols j))
    (fun i j : Fin m => A (rows i) (cols j))
    (higham9_6_firstSchurUpdate_trailing_abs_le_original_of_totalNonnegative
      hTN hrows_p hcols_p hpivot)

/-- **Problem 9.6**, first-step trailing max-entry no-growth relative to the
full source matrix.  This combines the local first Schur-update no-growth
argument with the generic fact that a submatrix cannot have larger max-entry
norm than its source matrix. -/
theorem higham9_6_firstSchurUpdate_trailing_maxEntryNorm_le_source
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {p : Fin n} {rows cols : Fin m → Fin n}
    (hrows_p : ∀ i : Fin m, p.val < (rows i).val)
    (hcols_p : ∀ j : Fin m, p.val < (cols j).val)
    (hpivot : 0 < A p p) :
    maxEntryNorm hm
        (fun i j : Fin m => higham9_6_firstSchurUpdate A p (rows i) (cols j)) ≤
      maxEntryNorm hn A :=
  le_trans
    (higham9_6_firstSchurUpdate_trailing_maxEntryNorm_le_original hm
      hTN hrows_p hcols_p hpivot)
    (maxEntryNorm_submatrix_le hn hm A rows cols)

/-- **Problem 9.6**, final growth-factor deduction from an explicit
nonnegative LU certificate.  This is the source endpoint once the preceding
total-nonnegative LU existence step has supplied `A = L U` with `L >= 0` and
`U >= 0`; it does not assume or prove that existence step. -/
theorem higham9_6_nonnegativeLU_growthFactorEntry_le_one {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U k j) :
    growthFactorEntry hn A U hAmax ≤ 1 :=
  higham9_12_nonneg_lu_growthFactorEntry_le_one hn A L U hAmax
    ⟨hLU, hL_nn, hU_nn⟩

/-- **Problem 9.6**, nonnegativity of the explicit lower factor produced by
one exact no-pivot LU construction step from a totally nonnegative source
matrix. -/
theorem higham9_6_luFirstStepL_nonneg {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    {L₁ : Fin m → Fin m → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hpivot : 0 < A 0 0)
    (hL₁_nn : ∀ i j : Fin m, 0 ≤ L₁ i j) :
    ∀ i j : Fin (m + 1), 0 ≤ luFirstStepL A L₁ i j := by
  intro i j
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · simp [luFirstStepL, hi, hj]
    · simp [luFirstStepL, hi, hj]
  · by_cases hj : j = 0
    · have hnum : 0 ≤ A i 0 :=
        higham9_6_totalNonnegative_entry_nonneg hTN i 0
      have hdiv : 0 ≤ A i 0 / A 0 0 :=
        div_nonneg hnum (le_of_lt hpivot)
      simpa [luFirstStepL, hi, hj] using hdiv
    · simpa [luFirstStepL, hi, hj] using hL₁_nn (i.pred hi) (j.pred hj)

/-- **Problem 9.6**, nonnegativity of the explicit upper factor produced by
one exact no-pivot LU construction step from a totally nonnegative source
matrix. -/
theorem higham9_6_luFirstStepU_nonneg {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    {U₁ : Fin m → Fin m → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hU₁_nn : ∀ i j : Fin m, 0 ≤ U₁ i j) :
    ∀ i j : Fin (m + 1), 0 ≤ luFirstStepU A U₁ i j := by
  intro i j
  by_cases hi : i = 0
  · have hentry : 0 ≤ A 0 j :=
      higham9_6_totalNonnegative_entry_nonneg hTN 0 j
    simpa [luFirstStepU, hi] using hentry
  · by_cases hj : j = 0
    · simp [luFirstStepU, hi, hj]
    · simpa [luFirstStepU, hi, hj] using hU₁_nn (i.pred hi) (j.pred hj)

/-- **Problem 9.6**, recursive exact no-pivot LU construction for totally
nonnegative matrices once the leading principal blocks are known positive.
The theorem exposes nonnegative `L` and `U`; the later source-facing
`det_ne_zero` wrapper derives these positive blocks directly from total
nonnegativity and nonsingularity.  The source-cited Koteljanskii/Fischer
determinant inequality is now also proved separately in
`higham9_6_principalBlock_determinantal_inequality_of_totalNonnegative`. -/
theorem higham9_6_lu_exists_nonnegative_of_totalNonnegative_and_leadingPrincipalBlock_pos :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℝ,
      higham9_6_IsTotallyNonnegative A →
      (∀ k : ℕ, ∀ hk : k ≤ n, k ≠ 0 →
        0 < Matrix.det
          (fun i j : Fin k => A (Fin.castLE hk i) (Fin.castLE hk j))) →
      ∃ L U : Fin n → Fin n → ℝ,
        LUFactSpec n A L U ∧
          (∀ i j : Fin n, 0 ≤ L i j) ∧
          (∀ i j : Fin n, 0 ≤ U i j) := by
  intro n
  induction n with
  | zero =>
      intro A _hTN _hlead
      refine ⟨(fun i _j => Fin.elim0 i), (fun i _j => Fin.elim0 i), ?_, ?_, ?_⟩
      · refine
          { L_diag := ?_
            L_upper_zero := ?_
            U_lower_zero := ?_
            product_eq := ?_ }
        · intro i
          exact Fin.elim0 i
        · intro i _j _hij
          exact Fin.elim0 i
        · intro i _j _hij
          exact Fin.elim0 i
        · intro i _j
          exact Fin.elim0 i
      · intro i _j
        exact Fin.elim0 i
      · intro i _j
        exact Fin.elim0 i
  | succ m ih =>
      intro A hTN hlead
      have hpivot : 0 < A 0 0 := by
        have h := hlead 1 (by omega) (by omega)
        simpa using h
      let rows : Fin m → Fin (m + 1) := fun i => i.succ
      have hrows_p : ∀ i : Fin m, (0 : Fin (m + 1)).val < (rows i).val := by
        intro i
        simp [rows]
      have hrows : StrictMono (fun i : Fin m => (rows i).val) := by
        intro i j hij
        simpa [rows] using hij
      let S : Fin m → Fin m → ℝ := higham9_1_firstSchurComplement A
      have hS_update_TN :
          higham9_6_IsTotallyNonnegative
            (fun i j : Fin m => higham9_6_firstSchurUpdate A 0 (rows i) (rows j)) :=
        higham9_6_firstSchurUpdate_trailing_totalNonnegative_of_totalNonnegative
          hTN hrows_p hrows_p hrows hrows hpivot
      have hS_eq :
          (fun i j : Fin m => higham9_6_firstSchurUpdate A 0 (rows i) (rows j)) =
            S := by
        ext i j
        simp [S, rows, higham9_1_firstSchurComplement, luFirstSchurComplement,
          higham9_6_firstSchurUpdate]
        field_simp [ne_of_gt hpivot]
      have hS_TN : higham9_6_IsTotallyNonnegative S := by
        simpa [hS_eq] using hS_update_TN
      have hSlead :
          ∀ k : ℕ, ∀ hk : k ≤ m, k ≠ 0 →
            0 < Matrix.det
              (fun i j : Fin k => S (Fin.castLE hk i) (Fin.castLE hk j)) := by
        intro k hk hk0
        have hnonneg_block :
            0 ≤ Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of S) k) :=
          higham9_6_totalNonnegative_leadingPrincipalBlock_det_nonneg hS_TN hk
        have hnonneg :
            0 ≤ Matrix.det
              (fun i j : Fin k => S (Fin.castLE hk i) (Fin.castLE hk j)) := by
          simpa [higham9_2_leadingPrincipalBlock, hk, S] using hnonneg_block
        have hne :
            Matrix.det
              (fun i j : Fin k => S (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0 := by
          simpa [S] using
            higham9_1_firstSchurComplement_leadingPrincipalBlock_det_ne_zero
              hk (fun t ht ht0 => ne_of_gt (hlead t ht ht0))
        rcases lt_or_eq_of_le hnonneg with hpos | hzero
        · exact hpos
        · exact (hne hzero.symm).elim
      obtain ⟨L₁, U₁, hLU₁, hL₁_nn, hU₁_nn⟩ := ih S hS_TN hSlead
      refine
        ⟨luFirstStepL A L₁, luFirstStepU A U₁,
          LUFactSpec.of_firstSchurComplement_explicit (ne_of_gt hpivot) hLU₁,
          ?_, ?_⟩
      · exact higham9_6_luFirstStepL_nonneg hTN hpivot hL₁_nn
      · exact higham9_6_luFirstStepU_nonneg hTN hU₁_nn

/-- **Problem 9.6**, total nonnegativity plus positive proper leading
principal blocks gives nonnegative exact no-pivot LU factors.  The full
determinant is supplied separately, while proper leading blocks use Higham's
`k = 1, ..., n-1` convention. -/
theorem higham9_6_lu_exists_nonnegative_of_totalNonnegative_and_properLeadingPrincipalBlock_pos
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : 0 < Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))
    (hlead :
      ∀ k : ℕ, k < n → k ≠ 0 →
        0 < Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) k)) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        (∀ i j : Fin n, 0 ≤ L i j) ∧
        (∀ i j : Fin n, 0 ≤ U i j) := by
  apply higham9_6_lu_exists_nonnegative_of_totalNonnegative_and_leadingPrincipalBlock_pos
    n A hTN
  intro k hk hk0
  by_cases hkn : k = n
  · subst k
    simpa using hdetA
  · have hklt : k < n := lt_of_le_of_ne hk hkn
    simpa [higham9_2_leadingPrincipalBlock, Nat.le_of_lt hklt] using
      hlead k hklt hk0

/-- **Problem 9.6**, nonsingular totally nonnegative matrices have exact
no-pivot LU factors with `L >= 0` and `U >= 0`.  This closes the Appendix A LU
existence step directly from source nonsingularity; it does not assume a hidden
Koteljanskii/Fischer determinant inequality. -/
theorem higham9_6_lu_exists_nonnegative_of_totalNonnegative_det_ne_zero
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        (∀ i j : Fin n, 0 ≤ L i j) ∧
        (∀ i j : Fin n, 0 ≤ U i j) :=
  higham9_6_lu_exists_nonnegative_of_totalNonnegative_and_leadingPrincipalBlock_pos
    n A hTN
    (higham9_6_leadingPrincipalBlock_det_pos_of_totalNonnegative_det_ne_zero
      n A hTN hdetA)

/-- **Problem 9.6**, source-facing no-pivot growth endpoint once total
nonnegativity and positive proper leading principal blocks are available. -/
theorem higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_properLeadingPrincipalBlock_pos
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : 0 < Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))
    (hlead :
      ∀ k : ℕ, k < n → k ≠ 0 →
        0 < Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) k))
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        (∀ i j : Fin n, 0 ≤ L i j) ∧
        (∀ i j : Fin n, 0 ≤ U i j) ∧
        growthFactorEntry hn A U hAmax ≤ 1 := by
  obtain ⟨L, U, hLU, hL_nn, hU_nn⟩ :=
    higham9_6_lu_exists_nonnegative_of_totalNonnegative_and_properLeadingPrincipalBlock_pos
      hTN hdetA hlead
  exact
    ⟨L, U, hLU, hL_nn, hU_nn,
      higham9_6_nonnegativeLU_growthFactorEntry_le_one hn A L U hAmax
        hLU hL_nn hU_nn⟩

/-- **Problem 9.6**, source-facing no-pivot growth endpoint from total
nonnegativity and nonsingularity alone.  The proof obtains positive leading
principal blocks internally by the Schur-complement induction above, then uses
the existing nonnegative-LU no-growth argument. -/
theorem higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        (∀ i j : Fin n, 0 ≤ L i j) ∧
        (∀ i j : Fin n, 0 ≤ U i j) ∧
        growthFactorEntry hn A U hAmax ≤ 1 := by
  obtain ⟨L, U, hLU, hL_nn, hU_nn⟩ :=
    higham9_6_lu_exists_nonnegative_of_totalNonnegative_det_ne_zero hTN hdetA
  exact
    ⟨L, U, hLU, hL_nn, hU_nn,
      higham9_6_nonnegativeLU_growthFactorEntry_le_one hn A L U hAmax
        hLU hL_nn hU_nn⟩

/-- **Problem 9.6**, source-facing combined endpoint from total nonnegativity
and nonsingularity alone: exact no-pivot LU has nonnegative factors, final
max-entry growth is at most one, and the reduced-matrix no-pivot growth factor
`rho_n` is at most one. -/
theorem higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        (∀ i j : Fin n, 0 ≤ L i j) ∧
        (∀ i j : Fin n, 0 ≤ U i j) ∧
        growthFactorEntry hn A U hAmax ≤ 1 ∧
        higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 1 := by
  obtain ⟨L, U, hLU, hL_nn, hU_nn, hGrowth⟩ :=
    higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero
      hn A hTN hdetA hAmax
  exact
    ⟨L, U, hLU, hL_nn, hU_nn, hGrowth,
      higham_problem9_9_noPivotReducedGrowthFactor_le_one_of_nonnegative_LU
        hn hLU hL_nn hU_nn hAmax⟩

/-- **Theorem 9.12(b/c)**, total-nonnegative special-class existence
package.  Problem 9.6 supplies exact no-pivot LU factors with nonnegative
entries; Theorem 9.12's nonnegative-LU specialization then gives
`|L||U| = |A|` componentwise. -/
theorem higham9_12_totalNonnegative_exists_LUFactSpec_optimal_growth
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        (∀ i j : Fin n, 0 ≤ L i j) ∧
        (∀ i j : Fin n, 0 ≤ U i j) ∧
        (∀ i j : Fin n,
          ∑ k : Fin n, |L i k| * |U k j| = |A i j|) := by
  obtain ⟨L, U, hLU, hL_nn, hU_nn⟩ :=
    higham9_6_lu_exists_nonnegative_of_totalNonnegative_det_ne_zero hTN hdetA
  exact
    ⟨L, U, hLU, hL_nn, hU_nn,
      higham9_12_nonneg_lu_optimal_growth n A L U ⟨hLU, hL_nn, hU_nn⟩⟩

/-- **Theorem 9.12(b/c)**, total-nonnegative special-class max-entry growth
package.  A nonsingular totally nonnegative source matrix admits exact
no-pivot LU factors with `L >= 0`, `U >= 0`, and Higham max-entry growth
factor at most one. -/
theorem higham9_12_totalNonnegative_exists_LUFactSpec_growthFactorEntry_le_one
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        (∀ i j : Fin n, 0 ≤ L i j) ∧
        (∀ i j : Fin n, 0 ≤ U i j) ∧
        growthFactorEntry hn A U hAmax ≤ 1 := by
  obtain ⟨L, U, hLU, hL_nn, hU_nn⟩ :=
    higham9_6_lu_exists_nonnegative_of_totalNonnegative_det_ne_zero hTN hdetA
  exact
    ⟨L, U, hLU, hL_nn, hU_nn,
      higham9_12_nonneg_lu_growthFactorEntry_le_one hn A L U hAmax
        ⟨hLU, hL_nn, hU_nn⟩⟩

/-- **Problem 9.6**, the Appendix A route made explicit: if the source-cited
determinant inequalities supply positive proper leading principal blocks for a
nonsingular totally nonnegative matrix, then no-pivot exact LU has nonnegative
factors and final max-entry growth at most one.  The determinant inequalities
remain visible hypotheses; they are not assumed as a hidden certificate. -/
theorem higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_principalBlock_inequalities
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : 0 < Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))
    (hineq :
      ∀ k : ℕ, k < n → k ≠ 0 →
        Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
          Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) k) *
            Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) k))
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        (∀ i j : Fin n, 0 ≤ L i j) ∧
        (∀ i j : Fin n, 0 ≤ U i j) ∧
        growthFactorEntry hn A U hAmax ≤ 1 := by
  apply
    higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_properLeadingPrincipalBlock_pos
      hn A hTN hdetA ?_ hAmax
  intro k hk hk0
  exact
    higham9_6_leadingPrincipalBlock_det_pos_of_determinantal_inequality
      hTN (Nat.le_of_lt hk) hdetA (hineq k hk hk0)

/-- **Problem 9.6**, source-facing combined endpoint: the Appendix A
determinant-inequality route gives nonnegative no-pivot exact LU factors,
final max-entry growth at most one, and the reduced-matrix no-pivot growth
factor `rho_n` at most one.  The determinant inequalities remain visible
hypotheses; this theorem only performs the local Split 2 LU/growth work once
that source-cited input is supplied. -/
theorem higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_and_principalBlock_inequalities
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : 0 < Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))
    (hineq :
      ∀ k : ℕ, k < n → k ≠ 0 →
        Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
          Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) k) *
            Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) k))
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        (∀ i j : Fin n, 0 ≤ L i j) ∧
        (∀ i j : Fin n, 0 ≤ U i j) ∧
        growthFactorEntry hn A U hAmax ≤ 1 ∧
        higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 1 := by
  obtain ⟨L, U, hLU, hL_nn, hU_nn, hGrowth⟩ :=
    higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_principalBlock_inequalities
      hn A hTN hdetA hineq hAmax
  exact
    ⟨L, U, hLU, hL_nn, hU_nn, hGrowth,
      higham_problem9_9_noPivotReducedGrowthFactor_le_one_of_nonnegative_LU
        hn hLU hL_nn hU_nn hAmax⟩

/-- **Problem 9.6**, source-facing no-pivot growth endpoint with the source
nonsingularity hypothesis `det(A) ≠ 0` instead of the derived positivity
`det(A) > 0`.  Total nonnegativity supplies determinant nonnegativity; the
principal-block determinant inequality is kept explicit on this appendix-route
surface.  The matching source inequality is proved separately by
`higham9_6_principalBlock_determinantal_inequality_of_totalNonnegative`. -/
theorem higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero_and_principalBlock_inequalities
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hineq :
      ∀ k : ℕ, k < n → k ≠ 0 →
        Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
          Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) k) *
            Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) k))
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        (∀ i j : Fin n, 0 ≤ L i j) ∧
        (∀ i j : Fin n, 0 ≤ U i j) ∧
        growthFactorEntry hn A U hAmax ≤ 1 :=
  higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_principalBlock_inequalities
    hn A hTN (higham9_6_totalNonnegative_det_pos_of_det_ne_zero hTN hdetA)
    hineq hAmax

/-- **Problem 9.6**, source-facing combined endpoint with the source
nonsingularity hypothesis `det(A) ≠ 0`: the determinant-inequality route gives
nonnegative exact no-pivot LU factors, final max-entry growth at most one, and
the reduced-matrix no-pivot growth factor `rho_n` at most one. -/
theorem higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero_and_principalBlock_inequalities
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hineq :
      ∀ k : ℕ, k < n → k ≠ 0 →
        Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
          Matrix.det (higham9_2_leadingPrincipalBlock (Matrix.of A) k) *
            Matrix.det (higham9_6_trailingPrincipalBlock (Matrix.of A) k))
    (hAmax : 0 < maxEntryNorm hn A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        (∀ i j : Fin n, 0 ≤ L i j) ∧
        (∀ i j : Fin n, 0 ≤ U i j) ∧
        growthFactorEntry hn A U hAmax ≤ 1 ∧
        higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 1 :=
  higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_and_principalBlock_inequalities
    hn A hTN (higham9_6_totalNonnegative_det_pos_of_det_ne_zero hTN hdetA)
    hineq hAmax

/-! ## Appendix A, Problem 9.7 -/

/-- **Problem 9.7**, square-submatrix count with the empty `0 × 0` case.
Vandermonde's identity gives `∑ₖ (n choose k)^2 = (2n choose n)`. -/
theorem higham9_7_square_submatrix_count_with_empty (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 2) =
      (2 * n).choose n :=
  Nat.sum_range_choose_sq n

/-- **Problem 9.7**, rectangular-submatrix count with empty row and column
choices allowed in each direction. -/
theorem higham9_7_rectangular_submatrix_count_with_empty (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), n.choose k) ^ 2 =
      (2 ^ n) ^ 2 := by
  rw [Nat.sum_range_choose]

/-- **Problem 9.7**, nonempty square-submatrix count.  This is the source
count excluding the empty `0 × 0` submatrix. -/
theorem higham9_7_square_submatrix_count_nonempty (n : ℕ) :
    (∑ k ∈ Finset.range n, (n.choose (k + 1)) ^ 2) =
      (2 * n).choose n - 1 := by
  have hfull := Nat.sum_range_choose_sq n
  rw [Finset.sum_range_succ'] at hfull
  simp at hfull
  omega

/-- **Problem 9.7**, nonempty rectangular-submatrix count. -/
theorem higham9_7_rectangular_submatrix_count_nonempty (n : ℕ) :
    (∑ k ∈ Finset.range n, n.choose (k + 1)) ^ 2 =
      (2 ^ n - 1) ^ 2 := by
  have hfull := Nat.sum_range_choose n
  rw [Finset.sum_range_succ'] at hfull
  simp at hfull
  have hsum : (∑ k ∈ Finset.range n, n.choose (k + 1)) = 2 ^ n - 1 := by
    omega
  rw [hsum]

/-! ## Appendix A, Problem 9.8 -/

/-- **Problem 9.8**, alternating signs used in the checkerboard sign matrix
`J = diag(1,-1,1,-1,...)`. -/
noncomputable def higham9_8_alternatingSign {n : ℕ} (i : Fin n) : ℝ :=
  (-1 : ℝ) ^ i.val

/-- **Problem 9.8**, the diagonal checkerboard sign matrix `J`. -/
noncomputable def higham9_8_signMatrixJ (n : ℕ) :
    Fin n → Fin n → ℝ :=
  fun i j => if i = j then higham9_8_alternatingSign i else 0

/-- **Problem 9.8**, conjugation by the checkerboard sign matrix at the
entry level: `(J A J)ᵢⱼ = (-1)^i Aᵢⱼ (-1)^j`. -/
noncomputable def higham9_8_checkerboardConjugate {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => higham9_8_alternatingSign i * A i j *
    higham9_8_alternatingSign j

/-- **Problem 9.8**, alternating signs have absolute value one. -/
theorem higham9_8_abs_alternatingSign {n : ℕ} (i : Fin n) :
    |higham9_8_alternatingSign i| = 1 := by
  unfold higham9_8_alternatingSign
  rw [abs_pow, abs_neg, abs_one, one_pow]

/-- **Problem 9.8**, diagonal entries of the checkerboard sign matrix. -/
theorem higham9_8_signMatrixJ_diag {n : ℕ} (i : Fin n) :
    higham9_8_signMatrixJ n i i = higham9_8_alternatingSign i := by
  simp [higham9_8_signMatrixJ]

/-- **Problem 9.8**, off-diagonal entries of the checkerboard sign matrix
are zero. -/
theorem higham9_8_signMatrixJ_offdiag {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) :
    higham9_8_signMatrixJ n i j = 0 := by
  simp [higham9_8_signMatrixJ, hij]

/-- **Problem 9.8**, left multiplication by the checkerboard sign matrix
scales row `i` by the alternating sign. -/
theorem higham9_8_signMatrixJ_left_mul {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    matMul n (higham9_8_signMatrixJ n) A =
      fun i j => higham9_8_alternatingSign i * A i j := by
  ext i j
  unfold matMul higham9_8_signMatrixJ
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk.symm]
  · intro hi
    simp at hi

/-- **Problem 9.8**, right multiplication by the checkerboard sign matrix
scales column `j` by the alternating sign. -/
theorem higham9_8_signMatrixJ_right_mul {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    matMul n A (higham9_8_signMatrixJ n) =
      fun i j => A i j * higham9_8_alternatingSign j := by
  ext i j
  unfold matMul higham9_8_signMatrixJ
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hj
    simp at hj

/-- **Problem 9.8**, checkerboard sign conjugation preserves componentwise
absolute values. -/
theorem higham9_8_abs_checkerboardConjugate {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, |higham9_8_checkerboardConjugate A i j| = |A i j| := by
  intro i j
  unfold higham9_8_checkerboardConjugate
  calc |higham9_8_alternatingSign i * A i j *
        higham9_8_alternatingSign j|
      = |higham9_8_alternatingSign i| * |A i j| *
          |higham9_8_alternatingSign j| := by
          rw [abs_mul, abs_mul]
    _ = |A i j| := by
          rw [higham9_8_abs_alternatingSign, higham9_8_abs_alternatingSign]
          ring

/-- **Problem 9.8**, alternating signs square to one. -/
theorem higham9_8_alternatingSign_sq {n : ℕ} (i : Fin n) :
    higham9_8_alternatingSign i * higham9_8_alternatingSign i = 1 := by
  have hs_abs := higham9_8_abs_alternatingSign i
  have hs_sq : (higham9_8_alternatingSign i) ^ 2 = 1 := by
    calc (higham9_8_alternatingSign i) ^ 2
        = |higham9_8_alternatingSign i| ^ 2 := by
            rw [← sq_abs]
      _ = 1 := by
            rw [hs_abs]
            norm_num
  simpa [pow_two] using hs_sq

/-- **Problem 9.8 support**, a product of checkerboard signs over a selected
row or column list is the checkerboard sign of the sum of selected indices. -/
theorem higham9_8_prod_alternatingSign_eq_pow_sum {n k : ℕ}
    (rows : Fin k → Fin n) :
    (∏ r : Fin k, higham9_8_alternatingSign (rows r)) =
      (-1 : ℝ) ^ (∑ r : Fin k, (rows r).val) := by
  unfold higham9_8_alternatingSign
  simpa using
    (Finset.prod_pow_eq_pow_sum
      (s := (Finset.univ : Finset (Fin k)))
      (f := fun r : Fin k => (rows r).val) (-1 : ℝ))

/-- **Problem 9.8 support**, subtracting exponents of `-1` is the same as
multiplying by the subtracted sign.  This is the parity bookkeeping needed for
cycle/shuffle signs in the selected/complement reindex proof. -/
theorem higham9_8_neg_one_pow_sub_eq_mul (a b : ℕ) (hb : b ≤ a) :
    (-1 : ℝ) ^ (a - b) = (-1 : ℝ) ^ a * (-1 : ℝ) ^ b := by
  have ha : a = b + (a - b) := (Nat.add_sub_of_le hb).symm
  have hb_sq : (-1 : ℝ) ^ b * (-1 : ℝ) ^ b = 1 := by
    calc
      (-1 : ℝ) ^ b * (-1 : ℝ) ^ b = (-1 : ℝ) ^ (b + b) := by
        rw [← pow_add]
      _ = (-1 : ℝ) ^ (2 * b) := by
        have h : b + b = 2 * b := by omega
        rw [h]
      _ = 1 := by
        rw [pow_mul]
        simp
  calc
    (-1 : ℝ) ^ (a - b)
        = ((-1 : ℝ) ^ b * (-1 : ℝ) ^ b) *
            (-1 : ℝ) ^ (a - b) := by rw [hb_sq]; ring
    _ = (-1 : ℝ) ^ b *
          ((-1 : ℝ) ^ b * (-1 : ℝ) ^ (a - b)) := by ring
    _ = (-1 : ℝ) ^ b * (-1 : ℝ) ^ (b + (a - b)) := by
          rw [pow_add]
    _ = (-1 : ℝ) ^ b * (-1 : ℝ) ^ a := by rw [← ha]
    _ = (-1 : ℝ) ^ a * (-1 : ℝ) ^ b := by ring

/-- **Problem 9.8 support**, the checkerboard row and column scaling factors
cancel the Jacobi complementary-minor sign for arbitrary selected row and
column lists. -/
theorem higham9_8_checkerboard_sign_products_cancel {n k : ℕ}
    (rows cols : Fin k → Fin n) :
    (∏ r : Fin k, higham9_8_alternatingSign (rows r)) *
        ((-1 : ℝ) ^
          ((∑ r : Fin k, (rows r).val) +
            (∑ c : Fin k, (cols c).val))) *
        (∏ c : Fin k, higham9_8_alternatingSign (cols c)) = 1 := by
  let sr : ℕ := ∑ r : Fin k, (rows r).val
  let sc : ℕ := ∑ c : Fin k, (cols c).val
  have hrows :
      (∏ r : Fin k, higham9_8_alternatingSign (rows r)) =
        (-1 : ℝ) ^ sr := by
    simpa [sr] using higham9_8_prod_alternatingSign_eq_pow_sum rows
  have hcols :
      (∏ c : Fin k, higham9_8_alternatingSign (cols c)) =
        (-1 : ℝ) ^ sc := by
    simpa [sc] using higham9_8_prod_alternatingSign_eq_pow_sum cols
  rw [hrows, hcols]
  calc
    (-1 : ℝ) ^ sr * (-1 : ℝ) ^ (sr + sc) * (-1 : ℝ) ^ sc
        = (-1 : ℝ) ^ (sr + (sr + sc) + sc) := by
          rw [← pow_add, ← pow_add]
    _ = (-1 : ℝ) ^ (2 * (sr + sc)) := by
          have h : sr + (sr + sc) + sc = 2 * (sr + sc) := by omega
          rw [h]
    _ = 1 := by
          rw [pow_mul]
          simp

/-- **Problem 9.8 support**, the finite set selected by a row/column map. -/
noncomputable def higham9_8_selectedFinset {n k : ℕ}
    (rows : Fin k → Fin n) : Finset (Fin n) :=
  Finset.image rows Finset.univ

/-- **Problem 9.8 support**, a strictly increasing `k`-selection has exactly
`k` selected indices. -/
theorem higham9_8_selectedFinset_card {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val)) :
    (higham9_8_selectedFinset rows).card = k := by
  have hrows_fin : StrictMono rows := by
    intro a b hab
    exact hrows hab
  simp [higham9_8_selectedFinset,
    Finset.card_image_of_injective _ hrows_fin.injective]

/-- **Problem 9.8 support**, a strict `k`-selection into `Fin n` forces
`k <= n`. -/
theorem higham9_8_selection_card_le {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val)) :
    k ≤ n := by
  have hrows_fin : StrictMono rows := by
    intro a b hab
    exact hrows hab
  simpa using Fintype.card_le_of_injective rows hrows_fin.injective

/-- **Problem 9.8 support**, a strictly increasing row/column selection cannot
place the `r`th selected source index before position `r`.  This is the
counting side condition used by the selected/complement shuffle-sign route. -/
theorem higham9_8_selection_index_le_value {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (r : Fin k) :
    r.val ≤ (rows r).val := by
  have hrows_fin : StrictMono rows := by
    intro a b hab
    exact hrows hab
  let s : Finset (Fin n) := Finset.image rows (Finset.Iic r)
  have hs_subset : s ⊆ Finset.Iic (rows r) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact Finset.mem_Iic.mpr (hrows_fin.monotone (Finset.mem_Iic.mp hi))
  have hcard_le : s.card ≤ (Finset.Iic (rows r)).card :=
    Finset.card_le_card hs_subset
  have hcard_s : s.card = (Finset.Iic r).card := by
    simp [s, Finset.card_image_of_injective (Finset.Iic r) hrows_fin.injective]
  have hcard_iic_r : (Finset.Iic r).card = r.val + 1 := by
    simp
  have hcard_iic_rows : (Finset.Iic (rows r)).card = (rows r).val + 1 := by
    simp
  omega

/-- **Problem 9.8 support**, the complement of a strictly increasing
`k`-selection in `Fin n` has cardinality `n-k`. -/
theorem higham9_8_selectedFinset_compl_card {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val)) :
    ((higham9_8_selectedFinset rows)ᶜ).card = n - k := by
  rw [Finset.card_compl, higham9_8_selectedFinset_card hrows]
  simp

/-- **Problem 9.8 support**, the ordered complement of a selected row/column
set, represented again as a strictly increasing map into `Fin n`. -/
noncomputable def higham9_8_complementSelection {n k : ℕ}
    (rows : Fin k → Fin n)
    (hrows : StrictMono (fun r : Fin k => (rows r).val)) :
    Fin (n - k) → Fin n :=
  ((higham9_8_selectedFinset rows)ᶜ).orderEmbOfFin
    (higham9_8_selectedFinset_compl_card hrows)

/-- **Problem 9.8 support**, ordered complements are strictly increasing in
the source index order. -/
theorem higham9_8_complementSelection_strictMono {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val)) :
    StrictMono
      (fun r : Fin (n - k) =>
        (higham9_8_complementSelection rows hrows r).val) := by
  intro a b hab
  simpa [higham9_8_complementSelection] using
    (((higham9_8_selectedFinset rows)ᶜ).orderEmbOfFin
      (higham9_8_selectedFinset_compl_card hrows)).strictMono hab

/-- **Problem 9.8 support**, every ordered-complement index is outside the
selected set. -/
theorem higham9_8_complementSelection_not_mem_selected {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (r : Fin (n - k)) :
    higham9_8_complementSelection rows hrows r ∉
      higham9_8_selectedFinset rows := by
  have hmem :
      higham9_8_complementSelection rows hrows r ∈
        (higham9_8_selectedFinset rows)ᶜ := by
    simp [higham9_8_complementSelection,
      Finset.orderEmbOfFin_mem
        (s := (higham9_8_selectedFinset rows)ᶜ)
        (h := higham9_8_selectedFinset_compl_card hrows) r]
  simpa using hmem

/-- **Problem 9.8 support**, exactly `r` selected indices lie below the
`r`th selected index. -/
theorem higham9_8_selected_below_card {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (r : Fin k) :
    ((higham9_8_selectedFinset rows) ∩ Finset.Iio (rows r)).card = r.val := by
  classical
  have hrows_fin : StrictMono rows := by
    intro a b hab
    exact hrows hab
  have hset :
      (higham9_8_selectedFinset rows) ∩ Finset.Iio (rows r) =
        (Finset.Iio r).image rows := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxsel, hxlt⟩
      rcases Finset.mem_image.mp hxsel with ⟨i, _hi, rfl⟩
      have hir : i < r := by
        by_contra hnot
        have hri : r ≤ i := le_of_not_gt hnot
        have hxlt' : rows i < rows r := Finset.mem_Iio.mp hxlt
        rcases lt_or_eq_of_le hri with hlt | heq
        · have hlt' : rows r < rows i := hrows_fin hlt
          exact (not_lt_of_ge (le_of_lt hlt') hxlt')
        · subst heq
          exact (lt_irrefl (rows r) hxlt')
      exact Finset.mem_image.mpr ⟨i, Finset.mem_Iio.mpr hir, rfl⟩
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
          Finset.mem_Iio.mpr (hrows_fin (Finset.mem_Iio.mp hi))⟩
  rw [hset]
  rw [Finset.card_image_of_injective]
  · simp
  · exact hrows_fin.injective

/-- **Problem 9.8 support**, the complement entries below the `r`th selected
index are exactly the unselected positions below it. -/
theorem higham9_8_complement_below_card {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (r : Fin k) :
    ((Finset.univ : Finset (Fin (n - k))).filter
        (fun t =>
          higham9_8_complementSelection rows hrows t < rows r)).card =
      (rows r).val - r.val := by
  classical
  let s : Finset (Fin n) := higham9_8_selectedFinset rows
  let below : Finset (Fin n) := Finset.Iio (rows r)
  let compBelow : Finset (Fin (n - k)) :=
    (Finset.univ : Finset (Fin (n - k))).filter
      (fun t => higham9_8_complementSelection rows hrows t < rows r)
  have hcomp_inj : Function.Injective (higham9_8_complementSelection rows hrows) :=
    fun a b hab =>
      (higham9_8_complementSelection_strictMono hrows).injective
        (congrArg Fin.val hab)
  have hcomp_image :
      (Finset.univ.image (higham9_8_complementSelection rows hrows)) = sᶜ := by
    simp [s, higham9_8_complementSelection]
  have himage :
      compBelow.image (higham9_8_complementSelection rows hrows) =
        sᶜ ∩ below := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
      have htlt : higham9_8_complementSelection rows hrows t < rows r := by
        simpa [compBelow] using ht
      have htcomp :
          higham9_8_complementSelection rows hrows t ∈ sᶜ := by
        rw [← hcomp_image]
        exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
      exact Finset.mem_inter.mpr
        ⟨htcomp, by simpa [below] using Finset.mem_Iio.mpr htlt⟩
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxcomp, hxbelow⟩
      rw [← hcomp_image] at hxcomp
      rcases Finset.mem_image.mp hxcomp with ⟨t, _ht, rfl⟩
      exact Finset.mem_image.mpr
        ⟨t, by
          simp [compBelow, below] at hxbelow ⊢
          exact hxbelow, rfl⟩
  have hcard_compBelow :
      compBelow.card = (sᶜ ∩ below).card := by
    rw [← himage]
    exact (Finset.card_image_of_injective compBelow hcomp_inj).symm
  have hcomp_inter_eq : sᶜ ∩ below = below \ s := by
    ext x
    simp [and_comm, Finset.sdiff_eq_filter]
  have hbelow_card : below.card = (rows r).val := by
    simp [below]
  have hselected_below_card : (s ∩ below).card = r.val := by
    simpa [s, below] using higham9_8_selected_below_card hrows r
  calc
    compBelow.card = (sᶜ ∩ below).card := hcard_compBelow
    _ = (below \ s).card := by rw [hcomp_inter_eq]
    _ = below.card - (s ∩ below).card := by
      rw [Finset.card_sdiff]
    _ = (rows r).val - r.val := by
      rw [hbelow_card, hselected_below_card]

/-- **Problem 9.8 support**, a product of `-1` over the true entries of a
predicate is `(-1)` to the filtered cardinality. -/
theorem higham9_8_prod_if_neg_one_eq_pow_card {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    (∏ x : α, if p x then (-1 : ℝ) else 1) =
      (-1 : ℝ) ^ ((Finset.univ.filter p).card) := by
  rw [← Finset.prod_filter]
  simp [Finset.prod_const]

/-- **Problem 9.8 support**, cross-block factors for one selected index give
`(-1)` to the number of complement entries below it. -/
theorem higham9_8_cross_complement_product_eq_pow {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (r : Fin k) :
    (∏ t : Fin (n - k),
        if rows r < higham9_8_complementSelection rows hrows t
          then (1 : ℝ) else -1) =
      (-1 : ℝ) ^ ((rows r).val - r.val) := by
  classical
  have hfactor :
      (fun t : Fin (n - k) =>
        if rows r < higham9_8_complementSelection rows hrows t
          then (1 : ℝ) else -1) =
      (fun t : Fin (n - k) =>
        if higham9_8_complementSelection rows hrows t < rows r
          then (-1 : ℝ) else 1) := by
    funext t
    have hne :
        higham9_8_complementSelection rows hrows t ≠ rows r := by
      intro h
      have hmem :
          higham9_8_complementSelection rows hrows t ∈
            higham9_8_selectedFinset rows := by
        rw [h]
        exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
      exact higham9_8_complementSelection_not_mem_selected hrows t hmem
    rcases lt_trichotomy
        (higham9_8_complementSelection rows hrows t) (rows r) with hlt | heq | hgt
    · simp [hlt, not_lt_of_ge (le_of_lt hlt)]
    · exact (hne heq).elim
    · simp [hgt, not_lt_of_ge (le_of_lt hgt)]
  rw [hfactor]
  rw [higham9_8_prod_if_neg_one_eq_pow_card
    (fun t : Fin (n - k) =>
      higham9_8_complementSelection rows hrows t < rows r)]
  rw [higham9_8_complement_below_card hrows r]

/-- **Problem 9.8 support**, total nonnegativity supplies the complementary
minor that appears in Jacobi's inverse-minor formula. -/
theorem higham9_8_totalNonnegative_complement_minor_nonneg {n k : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    {rows cols : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hcols : StrictMono (fun c : Fin k => (cols c).val)) :
    0 ≤ Matrix.det
      (fun r c : Fin (n - k) =>
        A (higham9_8_complementSelection cols hcols r)
          (higham9_8_complementSelection rows hrows c)) := by
  exact hTN (n - k)
    (higham9_8_complementSelection cols hcols)
    (higham9_8_complementSelection rows hrows)
    (higham9_8_complementSelection_strictMono hcols)
    (higham9_8_complementSelection_strictMono hrows)

/-- **Problem 9.8 support**, concatenate a selected increasing index list with
its ordered complement to get a permutation of `Fin n`. -/
noncomputable def higham9_8_selectionComplementEquiv {n k : ℕ}
    (rows : Fin k → Fin n)
    (hrows : StrictMono (fun r : Fin k => (rows r).val)) :
    (Fin k ⊕ Fin (n - k)) ≃ Fin n :=
  Equiv.ofBijective
    (Sum.elim rows (higham9_8_complementSelection rows hrows))
    (by
      constructor
      · intro a b hab
        have hrows_fin : StrictMono rows := by
          intro i j hij
          exact hrows hij
        have hcomp_fin :
            StrictMono (higham9_8_complementSelection rows hrows) := by
          intro i j hij
          exact higham9_8_complementSelection_strictMono hrows hij
        cases a with
        | inl a =>
            cases b with
            | inl b =>
                have hab' : a = b := hrows_fin.injective hab
                subst hab'
                rfl
            | inr b =>
                have hmem :
                    higham9_8_complementSelection rows hrows b ∈
                      higham9_8_selectedFinset rows := by
                  have heq :
                      higham9_8_complementSelection rows hrows b = rows a := by
                    simpa using hab.symm
                  rw [heq]
                  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
                exact (higham9_8_complementSelection_not_mem_selected hrows b hmem).elim
        | inr a =>
            cases b with
            | inl b =>
                have hmem :
                    higham9_8_complementSelection rows hrows a ∈
                      higham9_8_selectedFinset rows := by
                  have heq :
                      higham9_8_complementSelection rows hrows a = rows b := by
                    simpa using hab
                  rw [heq]
                  exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
                exact (higham9_8_complementSelection_not_mem_selected hrows a hmem).elim
            | inr b =>
                have hab' : a = b := hcomp_fin.injective hab
                subst hab'
                rfl
      · intro x
        by_cases hx : x ∈ higham9_8_selectedFinset rows
        · rcases Finset.mem_image.mp hx with ⟨r, _hr, rfl⟩
          exact ⟨Sum.inl r, rfl⟩
        · have hxcomp : x ∈ (higham9_8_selectedFinset rows)ᶜ := by
            simpa using hx
          have hximage :
              x ∈ Finset.image
                (((higham9_8_selectedFinset rows)ᶜ).orderEmbOfFin
                  (higham9_8_selectedFinset_compl_card hrows))
                Finset.univ := by
            simpa using hxcomp
          rcases Finset.mem_image.mp hximage with ⟨r, _hr, hr⟩
          exact ⟨Sum.inr r, by
            simpa [higham9_8_complementSelection] using hr⟩)

@[simp]
theorem higham9_8_selectionComplementEquiv_inl {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (r : Fin k) :
    higham9_8_selectionComplementEquiv rows hrows (Sum.inl r) = rows r :=
  rfl

@[simp]
theorem higham9_8_selectionComplementEquiv_inr {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (r : Fin (n - k)) :
    higham9_8_selectionComplementEquiv rows hrows (Sum.inr r) =
      higham9_8_complementSelection rows hrows r :=
  rfl

/-- **Problem 9.8 support**, the selected list is the sorted enumeration of
its selected finset. -/
theorem higham9_8_selectedFinset_orderEmbOfFin_eq {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (r : Fin k) :
    (higham9_8_selectedFinset rows).orderEmbOfFin
        (higham9_8_selectedFinset_card hrows) r = rows r := by
  classical
  have hrows_fin : StrictMono rows := by
    intro a b hab
    exact hrows hab
  have huniq :
      rows =
        (higham9_8_selectedFinset rows).orderEmbOfFin
          (higham9_8_selectedFinset_card hrows) :=
    Finset.orderEmbOfFin_unique
      (higham9_8_selectedFinset_card hrows)
      (fun x => by simp [higham9_8_selectedFinset])
      hrows_fin
  exact congrFun huniq.symm r

/-- **Problem 9.8 support**, the Chapter 9 selected/complement equivalence is
Mathlib's sorted finite-set split equivalence for the selected finset. -/
theorem higham9_8_selectionComplementEquiv_eq_finSumEquivOfFinset {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val)) :
    higham9_8_selectionComplementEquiv rows hrows =
      finSumEquivOfFinset
        (s := higham9_8_selectedFinset rows)
        (higham9_8_selectedFinset_card hrows)
        (higham9_8_selectedFinset_compl_card hrows) := by
  ext x
  cases x with
  | inl r =>
      rw [higham9_8_selectionComplementEquiv_inl hrows]
      rw [finSumEquivOfFinset_inl]
      exact congrArg Fin.val
        (higham9_8_selectedFinset_orderEmbOfFin_eq hrows r).symm
  | inr r =>
      rw [higham9_8_selectionComplementEquiv_inr hrows]
      rw [finSumEquivOfFinset_inr]
      rfl

/-- **Problem 9.8 support**, the canonical split that sends the first `k`
indices to themselves and the remaining `n-k` indices to the tail of `Fin n`. -/
noncomputable def higham9_8_canonicalSelectionComplementEquiv {n k : ℕ}
    (hk : k ≤ n) : (Fin k ⊕ Fin (n - k)) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk))

@[simp]
theorem higham9_8_canonicalSelectionComplementEquiv_inl {n k : ℕ}
    (hk : k ≤ n) (r : Fin k) :
    higham9_8_canonicalSelectionComplementEquiv (n := n) (k := k) hk
        (Sum.inl r) =
      ⟨r.val, by exact lt_of_lt_of_le r.isLt hk⟩ := by
  ext
  simp [higham9_8_canonicalSelectionComplementEquiv]

@[simp]
theorem higham9_8_canonicalSelectionComplementEquiv_inr_val {n k : ℕ}
    (hk : k ≤ n) (r : Fin (n - k)) :
    (higham9_8_canonicalSelectionComplementEquiv (n := n) (k := k) hk
        (Sum.inr r)).val = k + r.val := by
  simp [higham9_8_canonicalSelectionComplementEquiv]

/-- **Problem 9.8 support**, split the strict upper interval above a selected
prefix position into later selected-prefix positions and all complement-suffix
positions. -/
theorem higham9_8_prod_Ioi_castAdd_split {k l : ℕ}
    (F : Fin (k + l) → ℝ) (r : Fin k) :
    (∏ j ∈ Finset.Ioi (Fin.castAdd l r), F j) =
      (∏ r' ∈ Finset.Ioi r, F (Fin.castAdd l r')) *
        (∏ t : Fin l, F (Fin.natAdd k t)) := by
  classical
  let e : (Fin k ⊕ Fin l) ≃ Fin (k + l) := finSumFinEquiv
  let s : Finset (Fin k ⊕ Fin l) :=
    (Finset.Ioi r).disjSum (Finset.univ : Finset (Fin l))
  have hst : ∀ x : Fin k ⊕ Fin l,
      x ∈ s ↔ e x ∈ Finset.Ioi (Fin.castAdd l r) := by
    intro x
    cases x with
    | inl a =>
        simp only [s, Finset.inl_mem_disjSum, Finset.mem_Ioi, e,
          finSumFinEquiv_apply_left]
        constructor
        · intro ha
          exact Fin.lt_def.mpr (by
            simpa [Fin.castAdd] using (Fin.lt_def.mp ha))
        · intro ha
          exact Fin.lt_def.mpr (by
            simpa [Fin.castAdd] using (Fin.lt_def.mp ha))
    | inr b =>
        simp only [s, Finset.inr_mem_disjSum, Finset.mem_univ,
          Finset.mem_Ioi, true_iff, e, finSumFinEquiv_apply_right]
        exact Fin.lt_def.mpr (by
          simp [Fin.castAdd, Fin.natAdd]
          omega)
  have hprod :=
    Finset.prod_equiv
      (s := s)
      (t := Finset.Ioi (Fin.castAdd l r))
      (f := fun x : Fin k ⊕ Fin l => F (e x))
      (g := F)
      e hst (by intro x hx; rfl)
  rw [← hprod]
  simp [s, e, Finset.prod_disjSum, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right]

/-- **Problem 9.8 support**, strict upper intervals in the complement suffix
are transported by `Fin.natAdd`. -/
theorem higham9_8_prod_Ioi_natAdd {k l : ℕ}
    (F : Fin (k + l) → ℝ) (t : Fin l) :
    (∏ j ∈ Finset.Ioi (Fin.natAdd k t), F j) =
      ∏ u ∈ Finset.Ioi t, F (Fin.natAdd k u) := by
  conv_lhs =>
    rw [← Fin.map_natAddEmb_Ioi k t]
  rw [Finset.prod_map]
  rfl

/-- **Problem 9.8 support**, the sign of a one-sided selected/complement
shuffle is the product of its cross-block inversion factors. -/
theorem higham9_8_selectionComplementEquiv_canonical_shuffle_sign_eq_cross_prod
    {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hk : k ≤ n) :
    (Equiv.Perm.sign
        ((higham9_8_canonicalSelectionComplementEquiv
            (n := n) (k := k) hk).symm.trans
          (higham9_8_selectionComplementEquiv rows hrows)) : ℝ) =
      ∏ r : Fin k, ∏ t : Fin (n - k),
        if rows r < higham9_8_complementSelection rows hrows t
          then (1 : ℝ) else -1 := by
  classical
  let c := higham9_8_canonicalSelectionComplementEquiv (n := n) (k := k) hk
  let e := higham9_8_selectionComplementEquiv rows hrows
  let p : Equiv.Perm (Fin n) := c.symm.trans e
  let hkn : k + (n - k) = n := Nat.add_sub_of_le hk
  let f : Fin (k + (n - k)) ≃ Fin n := finCongr hkn
  let s : (Fin k ⊕ Fin (n - k)) ≃ Fin (k + (n - k)) := finSumFinEquiv
  let q : Equiv.Perm (Fin (k + (n - k))) := (s.symm.trans e).trans f.symm
  have hsign_conj : Equiv.Perm.sign p = Equiv.Perm.sign q := by
    refine Equiv.Perm.sign_eq_sign_of_equiv p q f.symm ?_
    intro x
    simp [p, q, c, e, f, s, higham9_8_canonicalSelectionComplementEquiv]
  have hsign_q_units := Equiv.Perm.sign_eq_prod_prod_Ioi q
  have hsign_q :
      (Equiv.Perm.sign q : ℝ) =
        ∏ i : Fin (k + (n - k)),
          ∏ j ∈ Finset.Ioi i,
            if q i < q j then (1 : ℝ) else -1 := by
    rw [hsign_q_units]
    change
      (Int.castRingHom ℝ)
      ((Units.coeHom ℤ)
        (∏ i : Fin (k + (n - k)),
          ∏ j ∈ Finset.Ioi i,
            if q i < q j then (1 : ℤˣ) else -1)) =
        ∏ i : Fin (k + (n - k)),
          ∏ j ∈ Finset.Ioi i,
            if q i < q j then (1 : ℝ) else -1
    simp only [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    by_cases hij : q i < q j
    · simp [hij]
    · simp [hij]
  have hq_cast_val (r : Fin k) :
      (q (Fin.castAdd (n - k) r)).val = (rows r).val := by
    simp [q, s, e, f, finSumFinEquiv_symm_apply_castAdd,
      higham9_8_selectionComplementEquiv_inl]
  have hq_nat_val (t : Fin (n - k)) :
      (q (Fin.natAdd k t)).val =
        (higham9_8_complementSelection rows hrows t).val := by
    simp [q, s, e, f, finSumFinEquiv_symm_apply_natAdd,
      higham9_8_selectionComplementEquiv_inr]
  rw [show (Equiv.Perm.sign
        ((higham9_8_canonicalSelectionComplementEquiv
            (n := n) (k := k) hk).symm.trans
          (higham9_8_selectionComplementEquiv rows hrows)) : ℝ) =
        (Equiv.Perm.sign p : ℝ) by rfl]
  rw [hsign_conj, hsign_q]
  rw [Fin.prod_univ_add]
  have hhead :
      (∏ r : Fin k,
        ∏ j ∈ Finset.Ioi (Fin.castAdd (n - k) r),
          if q (Fin.castAdd (n - k) r) < q j then (1 : ℝ) else -1) =
        ∏ r : Fin k, ∏ t : Fin (n - k),
          if rows r < higham9_8_complementSelection rows hrows t
            then (1 : ℝ) else -1 := by
    apply Finset.prod_congr rfl
    intro r _
    rw [higham9_8_prod_Ioi_castAdd_split]
    have hselected :
        (∏ r' ∈ Finset.Ioi r,
          if q (Fin.castAdd (n - k) r) < q (Fin.castAdd (n - k) r')
            then (1 : ℝ) else -1) = 1 := by
      apply Finset.prod_eq_one
      intro r' hr'
      have hrr' : r < r' := Finset.mem_Ioi.mp hr'
      have hlt_val :
          (q (Fin.castAdd (n - k) r)).val <
            (q (Fin.castAdd (n - k) r')).val := by
        rw [hq_cast_val r, hq_cast_val r']
        exact hrows hrr'
      have hltq :
          q (Fin.castAdd (n - k) r) < q (Fin.castAdd (n - k) r') :=
        Fin.lt_def.mpr hlt_val
      simp [hltq]
    have hcross :
        (∏ t : Fin (n - k),
          if q (Fin.castAdd (n - k) r) < q (Fin.natAdd k t)
            then (1 : ℝ) else -1) =
          ∏ t : Fin (n - k),
            if rows r < higham9_8_complementSelection rows hrows t
              then (1 : ℝ) else -1 := by
      apply Finset.prod_congr rfl
      intro t _
      have hiff :
          q (Fin.castAdd (n - k) r) < q (Fin.natAdd k t) ↔
            rows r < higham9_8_complementSelection rows hrows t := by
        constructor
        · intro hlt
          exact Fin.lt_def.mpr (by
            rw [← hq_cast_val r, ← hq_nat_val t]
            exact Fin.lt_def.mp hlt)
        · intro hlt
          exact Fin.lt_def.mpr (by
            rw [hq_cast_val r, hq_nat_val t]
            exact Fin.lt_def.mp hlt)
      by_cases hlt :
          rows r < higham9_8_complementSelection rows hrows t
      · have hq :
            q (Fin.castAdd (n - k) r) < q (Fin.natAdd k t) :=
          hiff.mpr hlt
        simp [hlt, hq]
      · have hnq :
            ¬ q (Fin.castAdd (n - k) r) < q (Fin.natAdd k t) :=
          fun hq => hlt (hiff.mp hq)
        simp [hlt, hnq]
    rw [hselected, one_mul, hcross]
  have htail :
      (∏ t : Fin (n - k),
        ∏ j ∈ Finset.Ioi (Fin.natAdd k t),
          if q (Fin.natAdd k t) < q j then (1 : ℝ) else -1) = 1 := by
    apply Finset.prod_eq_one
    intro t _
    rw [higham9_8_prod_Ioi_natAdd]
    apply Finset.prod_eq_one
    intro u hu
    have htu : t < u := Finset.mem_Ioi.mp hu
    have hlt_val :
        (q (Fin.natAdd k t)).val < (q (Fin.natAdd k u)).val := by
      rw [hq_nat_val t, hq_nat_val u]
      exact higham9_8_complementSelection_strictMono hrows htu
    have hq : q (Fin.natAdd k t) < q (Fin.natAdd k u) :=
      Fin.lt_def.mpr hlt_val
    simp [hq]
  rw [hhead, htail, mul_one]

/-- **Problem 9.8 support**, one-sided selected/complement shuffle sign
against the canonical selected-prefix/complement-suffix split. -/
theorem higham9_8_selectionComplementEquiv_canonical_shuffle_sign {n k : ℕ}
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hk : k ≤ n) :
    (Equiv.Perm.sign
        ((higham9_8_canonicalSelectionComplementEquiv
            (n := n) (k := k) hk).symm.trans
          (higham9_8_selectionComplementEquiv rows hrows)) : ℝ) =
      (∏ r : Fin k, higham9_8_alternatingSign (rows r)) *
        (∏ r : Fin k, (-1 : ℝ) ^ r.val) := by
  classical
  rw [higham9_8_selectionComplementEquiv_canonical_shuffle_sign_eq_cross_prod
    hrows hk]
  have hcross :
      (∏ r : Fin k, ∏ t : Fin (n - k),
        if rows r < higham9_8_complementSelection rows hrows t
          then (1 : ℝ) else -1) =
        ∏ r : Fin k, (-1 : ℝ) ^ ((rows r).val - r.val) := by
    apply Finset.prod_congr rfl
    intro r _
    exact higham9_8_cross_complement_product_eq_pow hrows r
  rw [hcross]
  calc
    (∏ r : Fin k, (-1 : ℝ) ^ ((rows r).val - r.val))
        = ∏ r : Fin k,
            ((-1 : ℝ) ^ (rows r).val * (-1 : ℝ) ^ r.val) := by
          apply Finset.prod_congr rfl
          intro r _
          exact higham9_8_neg_one_pow_sub_eq_mul
            (rows r).val r.val
            (higham9_8_selection_index_le_value hrows r)
    _ = (∏ r : Fin k, (-1 : ℝ) ^ (rows r).val) *
          (∏ r : Fin k, (-1 : ℝ) ^ r.val) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ r : Fin k, higham9_8_alternatingSign (rows r)) *
          (∏ r : Fin k, (-1 : ℝ) ^ r.val) := by
          simp [higham9_8_alternatingSign]

/-- **Problem 9.8 support**, reducing the full selected/complement
row-column permutation sign to two one-sided shuffle signs against the
canonical selected/complement split.  This reduction is retained as an audit
adapter; the unconditional permutation-sign theorem below instantiates it with
the proved one-sided shuffle formulas. -/
theorem higham9_8_selectionComplementEquiv_perm_sign_of_canonical_shuffle_signs
    {n k : ℕ}
    {rows cols : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hcols : StrictMono (fun c : Fin k => (cols c).val))
    (hk : k ≤ n)
    (hrowShuffle :
      (Equiv.Perm.sign
          ((higham9_8_canonicalSelectionComplementEquiv
              (n := n) (k := k) hk).symm.trans
            (higham9_8_selectionComplementEquiv rows hrows)) : ℝ) =
        (∏ r : Fin k, higham9_8_alternatingSign (rows r)) *
          (∏ r : Fin k, (-1 : ℝ) ^ r.val))
    (hcolShuffle :
      (Equiv.Perm.sign
          ((higham9_8_canonicalSelectionComplementEquiv
              (n := n) (k := k) hk).symm.trans
            (higham9_8_selectionComplementEquiv cols hcols)) : ℝ) =
        (∏ c : Fin k, higham9_8_alternatingSign (cols c)) *
          (∏ c : Fin k, (-1 : ℝ) ^ c.val)) :
    (Equiv.Perm.sign
        ((higham9_8_selectionComplementEquiv rows hrows).symm.trans
          (higham9_8_selectionComplementEquiv cols hcols)) : ℝ) =
      (∏ c : Fin k, higham9_8_alternatingSign (cols c)) *
        (∏ r : Fin k, higham9_8_alternatingSign (rows r)) := by
  classical
  let eRows := higham9_8_selectionComplementEquiv rows hrows
  let eCols := higham9_8_selectionComplementEquiv cols hcols
  let c := higham9_8_canonicalSelectionComplementEquiv (n := n) (k := k) hk
  let pRows : Equiv.Perm (Fin n) := c.symm.trans eRows
  let pCols : Equiv.Perm (Fin n) := c.symm.trans eCols
  have hperm : eRows.symm.trans eCols = pRows.symm.trans pCols := by
    ext x
    simp [pRows, pCols, c, eRows, eCols]
  have hsign_raw :
      Equiv.Perm.sign (eRows.symm.trans eCols) =
        Equiv.Perm.sign pCols * Equiv.Perm.sign pRows := by
    rw [hperm, Equiv.Perm.sign_trans, Equiv.Perm.sign_symm]
  have hsign :
      (Equiv.Perm.sign (eRows.symm.trans eCols) : ℝ) =
        (Equiv.Perm.sign pCols : ℝ) * (Equiv.Perm.sign pRows : ℝ) := by
    rw [hsign_raw]
    norm_num
  have hcanon_sq :
      (∏ c : Fin k, (-1 : ℝ) ^ c.val) ^ 2 = 1 := by
    rw [pow_two, ← Finset.prod_mul_distrib]
    simp [← pow_add]
  rw [hsign]
  rw [hrowShuffle, hcolShuffle]
  ring_nf
  rw [hcanon_sq]
  ring

/-- **Problem 9.8 support**, full selected/complement row-column permutation
sign.  This removes the former pure-combinatorial sign hypothesis from the
nonsingular-complement arbitrary-minor branch. -/
theorem higham9_8_selectionComplementEquiv_perm_sign
    {n k : ℕ}
    {rows cols : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hcols : StrictMono (fun c : Fin k => (cols c).val)) :
    (Equiv.Perm.sign
        ((higham9_8_selectionComplementEquiv rows hrows).symm.trans
          (higham9_8_selectionComplementEquiv cols hcols)) : ℝ) =
      (∏ c : Fin k, higham9_8_alternatingSign (cols c)) *
        (∏ r : Fin k, higham9_8_alternatingSign (rows r)) := by
  let hk : k ≤ n := higham9_8_selection_card_le hrows
  exact
    higham9_8_selectionComplementEquiv_perm_sign_of_canonical_shuffle_signs
      hrows hcols hk
      (higham9_8_selectionComplementEquiv_canonical_shuffle_sign hrows hk)
      (higham9_8_selectionComplementEquiv_canonical_shuffle_sign hcols hk)

/-- **Problem 9.8 support**, block form of Jacobi's complementary-minor
identity.  If `M = [[A,B],[C,D]]` and both `M` and `D` are nonsingular, then
the determinant of the top-left block of `M^{-1}` is `det(D) / det(M)`.
This is the Schur-complement algebra needed before adding arbitrary row/column
permutation signs. -/
theorem higham9_8_det_inv_topLeft_fromBlocks_eq_det_D_mul_inv_det
    {k l : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ)
    (B : Matrix (Fin k) (Fin l) ℝ)
    (C : Matrix (Fin l) (Fin k) ℝ)
    (D : Matrix (Fin l) (Fin l) ℝ)
    (hM : Matrix.det (Matrix.fromBlocks A B C D) ≠ 0)
    (hD : Matrix.det D ≠ 0) :
    Matrix.det (((Matrix.fromBlocks A B C D)⁻¹).toBlocks₁₁) =
      Matrix.det D *
        (Matrix.det (Matrix.fromBlocks A B C D))⁻¹ := by
  classical
  have hD_unit_det : IsUnit (Matrix.det D) := isUnit_iff_ne_zero.mpr hD
  have hD_unit_mat : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr hD_unit_det
  have hM_unit_det : IsUnit (Matrix.det (Matrix.fromBlocks A B C D)) :=
    isUnit_iff_ne_zero.mpr hM
  have hM_unit_mat : IsUnit (Matrix.fromBlocks A B C D) :=
    (Matrix.isUnit_iff_isUnit_det (Matrix.fromBlocks A B C D)).mpr hM_unit_det
  obtain ⟨iD⟩ := hD_unit_mat.nonempty_invertible
  obtain ⟨iM⟩ := hM_unit_mat.nonempty_invertible
  letI : Invertible D := iD
  letI : Invertible (Matrix.fromBlocks A B C D) := iM
  let S : Matrix (Fin k) (Fin k) ℝ := A - B * ⅟D * C
  letI : Invertible S := by
    simpa [S] using Matrix.invertibleOfFromBlocks₂₂Invertible A B C D
  letI : Invertible (Matrix.det S) := Matrix.detInvertibleOfInvertible S
  have htop :
      ((Matrix.fromBlocks A B C D)⁻¹).toBlocks₁₁ = ⅟S := by
    calc
      ((Matrix.fromBlocks A B C D)⁻¹).toBlocks₁₁ =
          (⅟(Matrix.fromBlocks A B C D)).toBlocks₁₁ := by
            rw [Matrix.invOf_eq_nonsing_inv]
      _ = ⅟S := by
            rw [Matrix.invOf_fromBlocks₂₂_eq]
            simp [S]
  have hdet_top :
      Matrix.det (((Matrix.fromBlocks A B C D)⁻¹).toBlocks₁₁) =
        ⅟(Matrix.det S) := by
    rw [htop, Matrix.det_invOf]
  have hdetM_eq :
      Matrix.det (Matrix.fromBlocks A B C D) =
        Matrix.det D * Matrix.det S := by
    simpa [S] using Matrix.det_fromBlocks₂₂ A B C D
  have hSdet_ne : Matrix.det S ≠ 0 :=
    (Matrix.isUnit_det_of_invertible S).ne_zero
  rw [hdet_top, hdetM_eq, invOf_eq_inv]
  field_simp [hD, hSdet_ne]

/-- **Problem 9.8 support**, block Jacobi determinant identity without a
nonsingular complementary block assumption.  If `M = [[A,B],[C,D]]` is
nonsingular, then the determinant of the top-left block of `M^{-1}` times
`det(M)` equals `det(D)`.  This is the local algebraic form needed for the
singular-complementary-minor branch of Jacobi's inverse-minor theorem. -/
theorem higham9_8_det_inv_topLeft_fromBlocks_mul_det_eq_det_D
    {k l : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ)
    (B : Matrix (Fin k) (Fin l) ℝ)
    (C : Matrix (Fin l) (Fin k) ℝ)
    (D : Matrix (Fin l) (Fin l) ℝ)
    (hM : Matrix.det (Matrix.fromBlocks A B C D) ≠ 0) :
    Matrix.det (((Matrix.fromBlocks A B C D)⁻¹).toBlocks₁₁) *
        Matrix.det (Matrix.fromBlocks A B C D) =
      Matrix.det D := by
  classical
  let M : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) ℝ :=
    Matrix.fromBlocks A B C D
  let E : Matrix (Fin k) (Fin k) ℝ := (M⁻¹).toBlocks₁₁
  let F : Matrix (Fin k) (Fin l) ℝ := (M⁻¹).toBlocks₁₂
  let P : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) ℝ :=
    Matrix.fromBlocks E F 0 1
  have hM_unit : IsUnit (Matrix.det M) := isUnit_iff_ne_zero.mpr (by
    simpa [M] using hM)
  have hprod : M⁻¹ * M = 1 :=
    Matrix.nonsing_inv_mul M hM_unit
  have hprod_blocks :
      Matrix.fromBlocks (M⁻¹).toBlocks₁₁ (M⁻¹).toBlocks₁₂
          (M⁻¹).toBlocks₂₁ (M⁻¹).toBlocks₂₂ *
        Matrix.fromBlocks A B C D = 1 := by
    change Matrix.fromBlocks (M⁻¹).toBlocks₁₁ (M⁻¹).toBlocks₁₂
        (M⁻¹).toBlocks₂₁ (M⁻¹).toBlocks₂₂ * M = 1
    rw [Matrix.fromBlocks_toBlocks (M⁻¹)]
    exact hprod
  rw [Matrix.fromBlocks_multiply] at hprod_blocks
  have h11 : E * A + F * C = 1 := by
    have h := congrArg Matrix.toBlocks₁₁ hprod_blocks
    ext i j
    have hij := congrFun (congrFun h i) j
    have hone :
        (1 : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) ℝ)
            (Sum.inl i) (Sum.inl j) =
          (1 : Matrix (Fin k) (Fin k) ℝ) i j := by
      by_cases hij' : i = j <;> simp [Matrix.one_apply, hij']
    simpa [E, F, Matrix.toBlocks₁₁, Matrix.add_apply, hone] using hij
  have h12 : E * B + F * D = 0 := by
    have h := congrArg Matrix.toBlocks₁₂ hprod_blocks
    ext i j
    have hij := congrFun (congrFun h i) j
    simpa [E, F, Matrix.toBlocks₁₂, Matrix.add_apply] using hij
  have hPM :
      P * M =
        Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 C D := by
    change Matrix.fromBlocks E F 0 1 * Matrix.fromBlocks A B C D =
      Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 C D
    rw [Matrix.fromBlocks_multiply]
    simp [h11, h12]
  have hdetP :
      Matrix.det P = Matrix.det E := by
    change Matrix.det (Matrix.fromBlocks E F 0 (1 : Matrix (Fin l) (Fin l) ℝ)) =
      Matrix.det E
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  calc
    Matrix.det (((Matrix.fromBlocks A B C D)⁻¹).toBlocks₁₁) *
        Matrix.det (Matrix.fromBlocks A B C D)
        = Matrix.det E * Matrix.det M := by
            simp [M, E]
    _ = Matrix.det P * Matrix.det M := by
            rw [hdetP]
    _ = Matrix.det (P * M) := by
            rw [Matrix.det_mul]
    _ = Matrix.det
          (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 C D) := by
            rw [hPM]
    _ = Matrix.det D := by
            rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

/-- **Problem 9.8 support**, selected-minor form of the Schur-complement
Jacobi identity under the extra hypothesis that the complementary minor is
nonsingular.  The row/column selection is arbitrary and strictly increasing,
but the conclusion is deliberately stated with the determinant of the reindexed
full matrix in the denominator.  This older specialized identity is retained
for the nonsingular-complement route; the theorem
`higham9_8_det_inv_selected_mul_det_reindexed_eq_det_complement` below removes
the complementary-minor nonsingularity hypothesis. -/
theorem higham9_8_det_inv_selected_eq_det_complement_mul_inv_det_reindexed
    {n k : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    {rows cols : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hcols : StrictMono (fun c : Fin k => (cols c).val))
    (hcomp :
      Matrix.det
        (fun r c : Fin (n - k) =>
          A (higham9_8_complementSelection cols hcols r)
            (higham9_8_complementSelection rows hrows c)) ≠ 0) :
    Matrix.det
        (fun r c : Fin k =>
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (cols c)) =
      Matrix.det
        (fun r c : Fin (n - k) =>
          A (higham9_8_complementSelection cols hcols r)
            (higham9_8_complementSelection rows hrows c)) *
        (Matrix.det
          ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
            (higham9_8_selectionComplementEquiv cols hcols)
            (higham9_8_selectionComplementEquiv rows hrows)))⁻¹ := by
  classical
  let eRows := higham9_8_selectionComplementEquiv rows hrows
  let eCols := higham9_8_selectionComplementEquiv cols hcols
  let M : Matrix (Fin k ⊕ Fin (n - k)) (Fin k ⊕ Fin (n - k)) ℝ :=
    (Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix eCols eRows
  have hA_unit_det : IsUnit (Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)) :=
    isUnit_iff_ne_zero.mpr hA
  have hA_unit_mat : IsUnit (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) :=
    (Matrix.isUnit_iff_isUnit_det
      (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)).mpr hA_unit_det
  have hM_unit_mat : IsUnit M := by
    simpa [M, eRows, eCols] using
      ((Matrix.isUnit_submatrix_equiv eCols eRows).mpr hA_unit_mat)
  have hM : Matrix.det M ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det M).mp hM_unit_mat).ne_zero
  have hD :
      Matrix.det M.toBlocks₂₂ ≠ 0 := by
    simpa [M, eRows, eCols] using hcomp
  have hblock :=
    higham9_8_det_inv_topLeft_fromBlocks_eq_det_D_mul_inv_det
      M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
      (by simpa [Matrix.fromBlocks_toBlocks M] using hM)
      hD
  have hblock' :
      Matrix.det (M⁻¹).toBlocks₁₁ =
        Matrix.det M.toBlocks₂₂ * (Matrix.det M)⁻¹ := by
    simpa [Matrix.fromBlocks_toBlocks M] using hblock
  have htop :
      (M⁻¹).toBlocks₁₁ =
        (fun r c : Fin k =>
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (cols c)) := by
    ext r c
    simp [M, eRows, eCols, Matrix.toBlocks₁₁, Matrix.inv_submatrix_equiv]
  have hbottom :
      M.toBlocks₂₂ =
        (fun r c : Fin (n - k) =>
          A (higham9_8_complementSelection cols hcols r)
            (higham9_8_complementSelection rows hrows c)) := by
    ext r c
    simp [M, eRows, eCols, Matrix.toBlocks₂₂]
  rw [htop, hbottom] at hblock'
  simpa [M, eRows, eCols] using hblock'

/-- **Problem 9.8 support**, selected-row/selected-column Jacobi determinant
identity with no complementary-minor nonsingularity hypothesis.  After
reindexing the chosen rows and columns to the leading block, the block identity
`det((M⁻¹)₁₁) * det(M) = det(M₂₂)` gives the complementary minor directly.

This is the algebraic identity that removes the need for a complementary-minor
nonsingularity hypothesis in the source theorem. -/
theorem higham9_8_det_inv_selected_mul_det_reindexed_eq_det_complement
    {n k : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    {rows cols : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hcols : StrictMono (fun c : Fin k => (cols c).val)) :
    Matrix.det
        (fun r c : Fin k =>
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (cols c)) *
      Matrix.det
        ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
          (higham9_8_selectionComplementEquiv cols hcols)
          (higham9_8_selectionComplementEquiv rows hrows)) =
      Matrix.det
        (fun r c : Fin (n - k) =>
          A (higham9_8_complementSelection cols hcols r)
            (higham9_8_complementSelection rows hrows c)) := by
  classical
  let eRows := higham9_8_selectionComplementEquiv rows hrows
  let eCols := higham9_8_selectionComplementEquiv cols hcols
  let M : Matrix (Fin k ⊕ Fin (n - k)) (Fin k ⊕ Fin (n - k)) ℝ :=
    (Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix eCols eRows
  have hA_unit_det : IsUnit (Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)) :=
    isUnit_iff_ne_zero.mpr hA
  have hA_unit_mat : IsUnit (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) :=
    (Matrix.isUnit_iff_isUnit_det
      (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)).mpr hA_unit_det
  have hM_unit_mat : IsUnit M := by
    simpa [M, eRows, eCols] using
      ((Matrix.isUnit_submatrix_equiv eCols eRows).mpr hA_unit_mat)
  have hM : Matrix.det M ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det M).mp hM_unit_mat).ne_zero
  have hblock :=
    higham9_8_det_inv_topLeft_fromBlocks_mul_det_eq_det_D
      M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
      (by simpa [Matrix.fromBlocks_toBlocks M] using hM)
  have hblock' :
      Matrix.det (M⁻¹).toBlocks₁₁ * Matrix.det M =
        Matrix.det M.toBlocks₂₂ := by
    simpa [Matrix.fromBlocks_toBlocks M] using hblock
  have htop :
      (M⁻¹).toBlocks₁₁ =
        (fun r c : Fin k =>
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (cols c)) := by
    ext r c
    simp [M, eRows, eCols, Matrix.toBlocks₁₁, Matrix.inv_submatrix_equiv]
  have hbottom :
      M.toBlocks₂₂ =
        (fun r c : Fin (n - k) =>
          A (higham9_8_complementSelection cols hcols r)
            (higham9_8_complementSelection rows hrows c)) := by
    ext r c
    simp [M, eRows, eCols, Matrix.toBlocks₂₂]
  rw [htop, hbottom] at hblock'
  simpa [M, eRows, eCols] using hblock'

/-- **Problem 9.8**, the checkerboard sign matrix is involutive:
`J * J = I`. -/
theorem higham9_8_signMatrixJ_involutive {n : ℕ} :
    matMul n (higham9_8_signMatrixJ n) (higham9_8_signMatrixJ n) =
      idMatrix n := by
  ext i j
  have hleft := congrFun
    (congrFun
      (higham9_8_signMatrixJ_left_mul
        (A := higham9_8_signMatrixJ n)) i) j
  rw [hleft]
  by_cases hij : i = j
  · subst j
    simp [idMatrix, higham9_8_signMatrixJ, higham9_8_alternatingSign_sq]
  · simp [idMatrix, higham9_8_signMatrixJ, hij]

/-- **Problem 9.8**, matrix multiplication by the printed checkerboard sign
matrix agrees with the entrywise conjugation definition:
`J * A * J = checkerboardConjugate A`. -/
theorem higham9_8_signMatrixJ_mul_mul_eq_checkerboardConjugate {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    matMul n (matMul n (higham9_8_signMatrixJ n) A)
        (higham9_8_signMatrixJ n) =
      higham9_8_checkerboardConjugate A := by
  ext i j
  have hright := congrFun
    (congrFun
      (higham9_8_signMatrixJ_right_mul
        (A := matMul n (higham9_8_signMatrixJ n) A)) i) j
  have hleft := congrFun
    (congrFun (higham9_8_signMatrixJ_left_mul (A := A)) i) j
  rw [hright, hleft]
  unfold higham9_8_checkerboardConjugate
  ring

/-- **Problem 9.8**, checkerboard conjugation fixes the identity matrix. -/
theorem higham9_8_checkerboardConjugate_id {n : ℕ} :
    higham9_8_checkerboardConjugate (idMatrix n) = idMatrix n := by
  ext i j
  unfold higham9_8_checkerboardConjugate
  by_cases hij : i = j
  · subst j
    simp [idMatrix, higham9_8_alternatingSign_sq]
  · simp [idMatrix, hij]

/-- **Problem 9.8**, every square minor of a checkerboard conjugate is the
corresponding source minor multiplied by the row and column alternating-sign
products.  This is the local determinant-scaling half of the inverse-minor
route; it does not assert the missing Jacobi complementary-minor theorem for
inverses. -/
theorem higham9_8_checkerboardConjugate_minor_det_scale {n k : ℕ}
    (A : Fin n → Fin n → ℝ) (rows cols : Fin k → Fin n) :
    Matrix.det
        (fun r c : Fin k =>
          higham9_8_checkerboardConjugate A (rows r) (cols c)) =
      (∏ r : Fin k, higham9_8_alternatingSign (rows r)) *
        Matrix.det (fun r c : Fin k => A (rows r) (cols c)) *
        (∏ c : Fin k, higham9_8_alternatingSign (cols c)) := by
  let sr : Fin k → ℝ := fun r => higham9_8_alternatingSign (rows r)
  let sc : Fin k → ℝ := fun c => higham9_8_alternatingSign (cols c)
  let M : Matrix (Fin k) (Fin k) ℝ :=
    fun r c => A (rows r) (cols c)
  calc
    Matrix.det
        (fun r c : Fin k =>
          higham9_8_checkerboardConjugate A (rows r) (cols c))
        =
      Matrix.det (fun r c : Fin k => sr r * (M r c * sc c)) := by
        congr 1
        ext r c
        simp [sr, sc, M, higham9_8_checkerboardConjugate]
        ring
    _ = (∏ r : Fin k, sr r) *
        Matrix.det (fun r c : Fin k => M r c * sc c) := by
          simpa using
            (Matrix.det_mul_column (R := ℝ) sr
              (A := fun r c : Fin k => M r c * sc c))
    _ = (∏ r : Fin k, sr r) *
        Matrix.det (fun r c : Fin k => sc c * M r c) := by
          congr 1
          congr 1
          ext r c
          ring
    _ = (∏ r : Fin k, sr r) *
        ((∏ c : Fin k, sc c) * Matrix.det M) := by
          simpa using (congrArg (fun x => (∏ r : Fin k, sr r) * x)
            (Matrix.det_mul_row (R := ℝ) sc M))
    _ = (∏ r : Fin k, higham9_8_alternatingSign (rows r)) *
        Matrix.det (fun r c : Fin k => A (rows r) (cols c)) *
        (∏ c : Fin k, higham9_8_alternatingSign (cols c)) := by
          simp [sr, sc, M]
          ring

/-- **Problem 9.8**, checkerboard conjugation preserves the absolute value of
every square minor. -/
theorem higham9_8_abs_checkerboardConjugate_minor_det {n k : ℕ}
    (A : Fin n → Fin n → ℝ) (rows cols : Fin k → Fin n) :
    |Matrix.det
        (fun r c : Fin k =>
          higham9_8_checkerboardConjugate A (rows r) (cols c))| =
      |Matrix.det (fun r c : Fin k => A (rows r) (cols c))| := by
  have hscale :=
    higham9_8_checkerboardConjugate_minor_det_scale A rows cols
  rw [hscale, abs_mul, abs_mul]
  have hrows :
      |∏ r : Fin k, higham9_8_alternatingSign (rows r)| = 1 := by
    rw [Finset.abs_prod]
    simp [higham9_8_abs_alternatingSign]
  have hcols :
      |∏ c : Fin k, higham9_8_alternatingSign (cols c)| = 1 := by
    rw [Finset.abs_prod]
    simp [higham9_8_abs_alternatingSign]
  rw [hrows, hcols]
  ring

/-- **Problem 9.8 support**, conditional principal-minor case of the
checkerboard inverse theorem.  If the complementary principal minor is
nonsingular, the Schur-complement Jacobi identity and total nonnegativity prove
that the corresponding principal minor of `J A⁻¹ J` is nonnegative.

The complementary-minor nonsingularity hypothesis is explicit: this does not
prove the singular-complement branch of Jacobi's theorem, and it does not prove
the arbitrary non-principal row/column sign formula. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_principal_minor_nonneg_of_complement_det_ne_zero
    {n k : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    {rows : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hcomp :
      Matrix.det
        (fun r c : Fin (n - k) =>
          A (higham9_8_complementSelection rows hrows r)
            (higham9_8_complementSelection rows hrows c)) ≠ 0) :
    0 ≤ Matrix.det
      (fun r c : Fin k =>
        higham9_8_checkerboardConjugate
          (fun i j : Fin n =>
            (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ i j)
          (rows r) (rows c)) := by
  classical
  let eRows := higham9_8_selectionComplementEquiv rows hrows
  have hselected :=
    higham9_8_det_inv_selected_eq_det_complement_mul_inv_det_reindexed
      A hA hrows hrows hcomp
  have hdet_reindex :
      Matrix.det
        ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix eRows eRows) =
        Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
    simp [eRows,
      (Matrix.det_submatrix_equiv_self eRows
        (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))]
  have hcomp_nonneg :
      0 ≤ Matrix.det
        (fun r c : Fin (n - k) =>
          A (higham9_8_complementSelection rows hrows r)
            (higham9_8_complementSelection rows hrows c)) :=
    higham9_8_totalNonnegative_complement_minor_nonneg
      hTN hrows hrows
  have hA_pos :
      0 < Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) :=
    higham9_6_totalNonnegative_det_pos_of_det_ne_zero hTN hA
  have hselected_nonneg :
      0 ≤ Matrix.det
        (fun r c : Fin k =>
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (rows c)) := by
    rw [hselected, hdet_reindex]
    exact mul_nonneg hcomp_nonneg (inv_nonneg.mpr (le_of_lt hA_pos))
  have hscale :=
    higham9_8_checkerboardConjugate_minor_det_scale
      (fun i j : Fin n =>
        (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ i j) rows rows
  let s : ℝ := ∏ r : Fin k, higham9_8_alternatingSign (rows r)
  have hs_sq : s * s = 1 := by
    dsimp [s]
    rw [← Finset.prod_mul_distrib]
    simp [higham9_8_alternatingSign_sq]
  have hscale_rhs :
      (∏ r : Fin k, higham9_8_alternatingSign (rows r)) *
          Matrix.det
            (fun r c : Fin k =>
              (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (rows c)) *
          (∏ c : Fin k, higham9_8_alternatingSign (rows c)) =
        Matrix.det
          (fun r c : Fin k =>
            (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (rows c)) := by
    change s *
          Matrix.det
            (fun r c : Fin k =>
              (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (rows c)) *
          s =
        Matrix.det
          (fun r c : Fin k =>
            (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (rows c))
    let d : ℝ :=
      Matrix.det
        (fun r c : Fin k =>
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (rows c))
    change s * d * s = d
    calc
      s * d * s = (s * s) * d := by ring
      _ = d := by rw [hs_sq]; ring
  rw [hscale]
  convert hselected_nonneg using 1

/-- **Problem 9.8 support**, determinant of the selected/complement reindex
of the full matrix, with the remaining permutation sign exposed explicitly.
The next local sign target is to identify this permutation sign with the
product of the selected checkerboard row and column signs. -/
theorem higham9_8_det_selectionComplementEquiv_reindex_eq_perm_sign
    {n k : ℕ}
    (A : Fin n → Fin n → ℝ)
    {rows cols : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hcols : StrictMono (fun c : Fin k => (cols c).val)) :
    Matrix.det
        ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
          (higham9_8_selectionComplementEquiv cols hcols)
          (higham9_8_selectionComplementEquiv rows hrows)) =
      (Equiv.Perm.sign
          ((higham9_8_selectionComplementEquiv rows hrows).symm.trans
            (higham9_8_selectionComplementEquiv cols hcols)) : ℝ) *
        Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  let eRows := higham9_8_selectionComplementEquiv rows hrows
  let eCols := higham9_8_selectionComplementEquiv cols hcols
  have h :=
    Matrix.det_reindex (R := ℝ) (e := eCols.symm) (e' := eRows.symm)
      (M := (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))
  simpa [Matrix.reindex_apply, eRows, eCols, Equiv.symm_symm] using h

/-- **Problem 9.8 support**, arbitrary selected-minor consequence of the
Schur-complement Jacobi identity once the remaining row/column reindex sign is
available.  This closes the algebraic nonsingular-complement branch for
non-principal row and column selections; the explicit determinant-reindex sign
hypothesis is the local combinatorial bookkeeping still to be proved, not a
replacement for Jacobi's all-minors theorem. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero_of_reindex_det
    {n k : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    {rows cols : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hcols : StrictMono (fun c : Fin k => (cols c).val))
    (hcomp :
      Matrix.det
        (fun r c : Fin (n - k) =>
          A (higham9_8_complementSelection cols hcols r)
            (higham9_8_complementSelection rows hrows c)) ≠ 0)
    (hdet_reindex :
      Matrix.det
          ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
            (higham9_8_selectionComplementEquiv cols hcols)
            (higham9_8_selectionComplementEquiv rows hrows)) =
        (∏ c : Fin k, higham9_8_alternatingSign (cols c)) *
          (∏ r : Fin k, higham9_8_alternatingSign (rows r)) *
            Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)) :
    0 ≤ Matrix.det
      (fun r c : Fin k =>
        higham9_8_checkerboardConjugate
          (nonsingInv n A) (rows r) (cols c)) := by
  classical
  let sr : ℝ := ∏ r : Fin k, higham9_8_alternatingSign (rows r)
  let sc : ℝ := ∏ c : Fin k, higham9_8_alternatingSign (cols c)
  let dA : ℝ := Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
  let dC : ℝ :=
    Matrix.det
      (fun r c : Fin (n - k) =>
        A (higham9_8_complementSelection cols hcols r)
          (higham9_8_complementSelection rows hrows c))
  have hselected :=
    higham9_8_det_inv_selected_eq_det_complement_mul_inv_det_reindexed
      A hA hrows hcols hcomp
  have hscale :=
    higham9_8_checkerboardConjugate_minor_det_scale
      (fun i j : Fin n =>
        (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ i j) rows cols
  have hscale' :
      Matrix.det
        (fun r c : Fin k =>
          higham9_8_checkerboardConjugate
            (nonsingInv n A) (rows r) (cols c)) =
        sr *
          Matrix.det
            (fun r c : Fin k =>
              (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (cols c)) *
          sc := by
    simpa [nonsingInv, sr, sc] using hscale
  have hsr_sq : sr * sr = 1 := by
    dsimp [sr]
    rw [← Finset.prod_mul_distrib]
    simp [higham9_8_alternatingSign_sq]
  have hsc_sq : sc * sc = 1 := by
    dsimp [sc]
    rw [← Finset.prod_mul_distrib]
    simp [higham9_8_alternatingSign_sq]
  have hsr_ne : sr ≠ 0 := by
    intro h
    rw [h] at hsr_sq
    norm_num at hsr_sq
  have hsc_ne : sc ≠ 0 := by
    intro h
    rw [h] at hsc_sq
    norm_num at hsc_sq
  have hdet_reindex' :
      Matrix.det
          ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
            (higham9_8_selectionComplementEquiv cols hcols)
            (higham9_8_selectionComplementEquiv rows hrows)) =
        sc * sr * dA := by
    simpa [sc, sr, dA] using hdet_reindex
  have hchecker_eq :
      Matrix.det
        (fun r c : Fin k =>
          higham9_8_checkerboardConjugate
            (nonsingInv n A) (rows r) (cols c)) =
        dC * dA⁻¹ := by
    rw [hscale', hselected, hdet_reindex']
    dsimp [dC]
    field_simp [hA, hsr_ne, hsc_ne]
  rw [hchecker_eq]
  have hcomp_nonneg : 0 ≤ dC := by
    dsimp [dC]
    exact higham9_8_totalNonnegative_complement_minor_nonneg
      hTN hrows hcols
  have hA_pos : 0 < dA := by
    dsimp [dA]
    exact higham9_6_totalNonnegative_det_pos_of_det_ne_zero hTN hA
  exact mul_nonneg hcomp_nonneg (inv_nonneg.mpr (le_of_lt hA_pos))

/-- **Problem 9.8 support**, arbitrary selected-minor consequence of the
Schur-complement Jacobi identity once the selected/complement permutation sign
is supplied.  This is the same nonsingular-complement branch
as
`higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero_of_reindex_det`,
but the explicit hypothesis is the pure combinatorial sign formula rather than
a determinant-reindex equation. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero_of_perm_sign
    {n k : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    {rows cols : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hcols : StrictMono (fun c : Fin k => (cols c).val))
    (hcomp :
      Matrix.det
        (fun r c : Fin (n - k) =>
          A (higham9_8_complementSelection cols hcols r)
            (higham9_8_complementSelection rows hrows c)) ≠ 0)
    (hperm_sign :
      (Equiv.Perm.sign
          ((higham9_8_selectionComplementEquiv rows hrows).symm.trans
            (higham9_8_selectionComplementEquiv cols hcols)) : ℝ) =
        (∏ c : Fin k, higham9_8_alternatingSign (cols c)) *
          (∏ r : Fin k, higham9_8_alternatingSign (rows r))) :
    0 ≤ Matrix.det
      (fun r c : Fin k =>
        higham9_8_checkerboardConjugate
          (nonsingInv n A) (rows r) (cols c)) := by
  classical
  have hdet_reindex_raw :=
    higham9_8_det_selectionComplementEquiv_reindex_eq_perm_sign
      A hrows hcols
  have hdet_reindex :
      Matrix.det
          ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
            (higham9_8_selectionComplementEquiv cols hcols)
            (higham9_8_selectionComplementEquiv rows hrows)) =
        (∏ c : Fin k, higham9_8_alternatingSign (cols c)) *
          (∏ r : Fin k, higham9_8_alternatingSign (rows r)) *
            Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hdet_reindex_raw, hperm_sign]
  exact
    higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero_of_reindex_det
      hTN hA hrows hcols hcomp hdet_reindex

/-- **Problem 9.8**, arbitrary selected-minor nonsingular-complement branch:
if the complementary minor in Jacobi's inverse-minor formula is nonsingular,
then every corresponding minor of `J A⁻¹ J` is nonnegative for a nonsingular
totally nonnegative `A`.  This older Schur-complement branch is retained as a
specialized corollary; the full selected-minor theorem below removes the
complementary-minor nonsingularity hypothesis. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero
    {n k : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    {rows cols : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hcols : StrictMono (fun c : Fin k => (cols c).val))
    (hcomp :
      Matrix.det
        (fun r c : Fin (n - k) =>
          A (higham9_8_complementSelection cols hcols r)
            (higham9_8_complementSelection rows hrows c)) ≠ 0) :
    0 ≤ Matrix.det
      (fun r c : Fin k =>
        higham9_8_checkerboardConjugate
          (nonsingInv n A) (rows r) (cols c)) := by
  exact
    higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero_of_perm_sign
      hTN hA hrows hcols hcomp
      (higham9_8_selectionComplementEquiv_perm_sign hrows hcols)

/-- **Problem 9.8**, full selected-minor case of the checkerboard inverse
theorem: if `A` is nonsingular and totally nonnegative, then every square
minor of `J A⁻¹ J` is nonnegative.  This removes the former
complementary-minor nonsingularity hypothesis by using
`higham9_8_det_inv_selected_mul_det_reindexed_eq_det_complement`, the local
all-minors Jacobi identity. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg
    {n k : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    {rows cols : Fin k → Fin n}
    (hrows : StrictMono (fun r : Fin k => (rows r).val))
    (hcols : StrictMono (fun c : Fin k => (cols c).val)) :
    0 ≤ Matrix.det
      (fun r c : Fin k =>
        higham9_8_checkerboardConjugate
          (nonsingInv n A) (rows r) (cols c)) := by
  classical
  let sr : ℝ := ∏ r : Fin k, higham9_8_alternatingSign (rows r)
  let sc : ℝ := ∏ c : Fin k, higham9_8_alternatingSign (cols c)
  let dA : ℝ := Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
  let dC : ℝ :=
    Matrix.det
      (fun r c : Fin (n - k) =>
        A (higham9_8_complementSelection cols hcols r)
          (higham9_8_complementSelection rows hrows c))
  let dJ : ℝ :=
    Matrix.det
      (fun r c : Fin k =>
        higham9_8_checkerboardConjugate
          (nonsingInv n A) (rows r) (cols c))
  have hselected :=
    higham9_8_det_inv_selected_mul_det_reindexed_eq_det_complement
      A hA hrows hcols
  have hscale :=
    higham9_8_checkerboardConjugate_minor_det_scale
      (fun i j : Fin n =>
        (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ i j) rows cols
  have hscale' :
      dJ =
        sr *
          Matrix.det
            (fun r c : Fin k =>
              (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (cols c)) *
          sc := by
    simpa [dJ, nonsingInv, sr, sc] using hscale
  have hdet_reindex_raw :=
    higham9_8_det_selectionComplementEquiv_reindex_eq_perm_sign
      A hrows hcols
  have hdet_reindex :
      Matrix.det
          ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
            (higham9_8_selectionComplementEquiv cols hcols)
            (higham9_8_selectionComplementEquiv rows hrows)) =
        sc * sr * dA := by
    rw [hdet_reindex_raw,
      higham9_8_selectionComplementEquiv_perm_sign hrows hcols]
  have hselected' :
      Matrix.det
          (fun r c : Fin k =>
            (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (cols c)) *
        (sc * sr * dA) = dC := by
    have hselected_rewrite := hselected
    rw [hdet_reindex] at hselected_rewrite
    simpa [dC, dA] using hselected_rewrite
  have hJ_mul_dA : dJ * dA = dC := by
    calc
      dJ * dA =
          (sr *
            Matrix.det
              (fun r c : Fin k =>
                (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (cols c)) *
            sc) * dA := by
              rw [hscale']
      _ =
          Matrix.det
            (fun r c : Fin k =>
              (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ (rows r) (cols c)) *
            (sc * sr * dA) := by
              ring
      _ = dC := hselected'
  have hdA_ne : dA ≠ 0 := by
    simpa [dA] using hA
  have hJ_eq : dJ = dC * dA⁻¹ := by
    calc
      dJ = dJ * (dA * dA⁻¹) := by
            rw [mul_inv_cancel₀ hdA_ne, mul_one]
      _ = (dJ * dA) * dA⁻¹ := by
            ring
      _ = dC * dA⁻¹ := by
            rw [hJ_mul_dA]
  have hcomp_nonneg : 0 ≤ dC := by
    dsimp [dC]
    exact higham9_8_totalNonnegative_complement_minor_nonneg
      hTN hrows hcols
  have hA_pos : 0 < dA := by
    dsimp [dA]
    exact higham9_6_totalNonnegative_det_pos_of_det_ne_zero hTN hA
  dsimp [dJ] at hJ_eq ⊢
  rw [hJ_eq]
  exact mul_nonneg hcomp_nonneg (inv_nonneg.mpr (le_of_lt hA_pos))

/-- **Problem 9.8**, checkerboard conjugation is an involution. -/
theorem higham9_8_checkerboardConjugate_involutive {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    higham9_8_checkerboardConjugate (higham9_8_checkerboardConjugate A) = A := by
  ext i j
  unfold higham9_8_checkerboardConjugate
  calc higham9_8_alternatingSign i *
        (higham9_8_alternatingSign i * A i j *
          higham9_8_alternatingSign j) *
        higham9_8_alternatingSign j
      = (higham9_8_alternatingSign i * higham9_8_alternatingSign i) *
          A i j *
          (higham9_8_alternatingSign j * higham9_8_alternatingSign j) := by
          ring
    _ = A i j := by
          rw [higham9_8_alternatingSign_sq i, higham9_8_alternatingSign_sq j]
          ring

/-- **Problem 9.8**, a nonnegative checkerboard conjugate equals the
componentwise absolute value of the original matrix. -/
theorem higham9_8_checkerboardConjugate_eq_abs_of_nonneg {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (h_nonneg : ∀ i j : Fin n, 0 ≤ higham9_8_checkerboardConjugate A i j) :
    ∀ i j : Fin n, higham9_8_checkerboardConjugate A i j = |A i j| := by
  intro i j
  rw [← higham9_8_abs_checkerboardConjugate A i j,
    abs_of_nonneg (h_nonneg i j)]

/-- **Problem 9.8**, checkerboard conjugation commutes with exact matrix
products.  This is the algebra behind `A = (J L J) (J U J)` from
`J A J = L U`. -/
theorem higham9_8_checkerboardConjugate_matMul {n : ℕ}
    (L U : Fin n → Fin n → ℝ) :
    matMul n (higham9_8_checkerboardConjugate L)
        (higham9_8_checkerboardConjugate U) =
      higham9_8_checkerboardConjugate (matMul n L U) := by
  ext i j
  unfold matMul higham9_8_checkerboardConjugate
  calc
    (∑ k : Fin n,
        (higham9_8_alternatingSign i * L i k *
            higham9_8_alternatingSign k) *
          (higham9_8_alternatingSign k * U k j *
            higham9_8_alternatingSign j))
        =
      ∑ k : Fin n,
        higham9_8_alternatingSign i * (L i k * U k j) *
          higham9_8_alternatingSign j := by
        apply Finset.sum_congr rfl
        intro k _
        calc
          (higham9_8_alternatingSign i * L i k *
                higham9_8_alternatingSign k) *
              (higham9_8_alternatingSign k * U k j *
                higham9_8_alternatingSign j)
              =
            (higham9_8_alternatingSign k * higham9_8_alternatingSign k) *
              (higham9_8_alternatingSign i * (L i k * U k j) *
                higham9_8_alternatingSign j) := by
              ring
          _ = higham9_8_alternatingSign i * (L i k * U k j) *
                higham9_8_alternatingSign j := by
              rw [higham9_8_alternatingSign_sq k]
              ring
    _ = higham9_8_alternatingSign i * (∑ k : Fin n, L i k * U k j) *
          higham9_8_alternatingSign j := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- **Problem 9.8**, checkerboard conjugation transports left inverses:
if `A_inv * A = I`, then `(J A_inv J) * (J A J) = I`. -/
theorem higham9_8_checkerboardConjugate_left_inverse {n : ℕ}
    {A A_inv : Fin n → Fin n → ℝ}
    (hLeft : IsLeftInverse n A A_inv) :
    IsLeftInverse n (higham9_8_checkerboardConjugate A)
      (higham9_8_checkerboardConjugate A_inv) := by
  intro i j
  change matMul n (higham9_8_checkerboardConjugate A_inv)
      (higham9_8_checkerboardConjugate A) i j = idMatrix n i j
  have hprod := congrFun (congrFun
    (higham9_8_checkerboardConjugate_matMul A_inv A) i) j
  have hAA : matMul n A_inv A = idMatrix n := by
    ext r s
    exact hLeft r s
  rw [hprod, hAA, higham9_8_checkerboardConjugate_id]

/-- **Problem 9.8**, checkerboard conjugation transports right inverses:
if `A * A_inv = I`, then `(J A J) * (J A_inv J) = I`. -/
theorem higham9_8_checkerboardConjugate_right_inverse {n : ℕ}
    {A A_inv : Fin n → Fin n → ℝ}
    (hRight : IsRightInverse n A A_inv) :
    IsRightInverse n (higham9_8_checkerboardConjugate A)
      (higham9_8_checkerboardConjugate A_inv) := by
  intro i j
  change matMul n (higham9_8_checkerboardConjugate A)
      (higham9_8_checkerboardConjugate A_inv) i j = idMatrix n i j
  have hprod := congrFun (congrFun
    (higham9_8_checkerboardConjugate_matMul A A_inv) i) j
  have hAA : matMul n A A_inv = idMatrix n := by
    ext r s
    exact hRight r s
  rw [hprod, hAA, higham9_8_checkerboardConjugate_id]

/-- **Problem 9.8**, checkerboard conjugation transports two-sided inverse
certificates. -/
theorem higham9_8_checkerboardConjugate_inverse {n : ℕ}
    {A A_inv : Fin n → Fin n → ℝ}
    (hInv : IsInverse n A A_inv) :
    IsInverse n (higham9_8_checkerboardConjugate A)
      (higham9_8_checkerboardConjugate A_inv) :=
  ⟨higham9_8_checkerboardConjugate_left_inverse hInv.1,
    higham9_8_checkerboardConjugate_right_inverse hInv.2⟩

/-- **Problem 9.8**, source-oriented inverse transport.  If `A_inv` is a
two-sided inverse of `A`, then `J A J` is a two-sided inverse of
`J A_inv J`.  This is the algebraic direction used when applying the source
Jacobi theorem to `C = A_inv`; it does not assert the Jacobi theorem itself. -/
theorem higham9_8_checkerboardConjugate_inverse_swapped {n : ℕ}
    {A A_inv : Fin n → Fin n → ℝ}
    (hInv : IsInverse n A A_inv) :
    IsInverse n (higham9_8_checkerboardConjugate A_inv)
      (higham9_8_checkerboardConjugate A) :=
  higham9_8_checkerboardConjugate_inverse (A := A_inv) (A_inv := A)
    ⟨hInv.2, hInv.1⟩

/-- **Problem 9.8 support**, deleting one row or column with `Fin.succAbove`
preserves strict source order.  This is the indexing bridge used by the
cofactor-level inverse sign-pattern theorem. -/
theorem higham9_8_succAbove_val_strictMono {n : ℕ} (p : Fin (n + 1)) :
    StrictMono (fun r : Fin n => (p.succAbove r).val) := by
  intro a b hab
  change (p.succAbove a).val < (p.succAbove b).val
  rcases Fin.castSucc_lt_or_lt_succ p a with ha | ha
  · rcases Fin.castSucc_lt_or_lt_succ p b with hb | hb
    · rw [Fin.succAbove_of_castSucc_lt p a ha,
        Fin.succAbove_of_castSucc_lt p b hb]
      simpa using hab
    · rw [Fin.succAbove_of_castSucc_lt p a ha,
        Fin.succAbove_of_lt_succ p b hb]
      omega
  · have hb : p < b.succ := lt_trans ha (Fin.succ_lt_succ_iff.mpr hab)
    rw [Fin.succAbove_of_lt_succ p a ha,
      Fin.succAbove_of_lt_succ p b hb]
    simpa using (Fin.succ_lt_succ_iff.mpr hab)

/-- **Problem 9.8 support**, the entrywise `1 by 1` case of the Jacobi
inverse-minor sign pattern.  If `A` is nonsingular and totally nonnegative,
then the checkerboard conjugate of the repository nonsingular inverse is
entrywise nonnegative.

This proves only the cofactor-level consequence needed for entries.  It does
not prove the full Jacobi complementary-minor theorem asserting total
nonnegativity of every square minor of `J A^{-1} J`. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_entry_nonneg_of_det_pos
    {n : ℕ} {A : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdet_pos :
      0 < Matrix.det
        (Matrix.of A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) :
    ∀ i j : Fin (n + 1),
      0 ≤ higham9_8_checkerboardConjugate
        (nonsingInv (n + 1) A) i j := by
  intro i j
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of A
  have hdet_unit : IsUnit (Matrix.det M) :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hdet_pos)
  have hinv :
      (M⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) =
        (↑hdet_unit.unit⁻¹ : ℝ) • M.adjugate :=
    Matrix.nonsing_inv_apply M hdet_unit
  let rows : Fin n → Fin (n + 1) := fun r => j.succAbove r
  let cols : Fin n → Fin (n + 1) := fun c => i.succAbove c
  have hrows : StrictMono (fun r : Fin n => (rows r).val) := by
    simpa [rows] using higham9_8_succAbove_val_strictMono j
  have hcols : StrictMono (fun c : Fin n => (cols c).val) := by
    simpa [cols] using higham9_8_succAbove_val_strictMono i
  have hminor_nonneg :
      0 ≤ Matrix.det (M.submatrix j.succAbove i.succAbove) := by
    have h := hTN n rows cols hrows hcols
    simpa [M, rows, cols] using h
  have hunit_pos : 0 < (↑hdet_unit.unit : ℝ) := by
    rw [hdet_unit.unit_spec]
    exact hdet_pos
  have hinvdet_pos : 0 < (↑hdet_unit.unit⁻¹ : ℝ) := by
    rw [Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hunit_pos
  have hentry :
      nonsingInv (n + 1) A i j =
        (↑hdet_unit.unit⁻¹ : ℝ) *
          (((-1 : ℝ) ^ (j.val + i.val)) *
            Matrix.det (M.submatrix j.succAbove i.succAbove)) := by
    unfold nonsingInv
    letI : Inv (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := Matrix.inv
    change (M⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j = _
    rw [hinv]
    simp [Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [higham9_8_checkerboardConjugate, hentry]
  have hsign :
      higham9_8_alternatingSign i *
          ((↑hdet_unit.unit⁻¹ : ℝ) *
            (((-1 : ℝ) ^ (j.val + i.val)) *
              Matrix.det (M.submatrix j.succAbove i.succAbove))) *
          higham9_8_alternatingSign j =
        (↑hdet_unit.unit⁻¹ : ℝ) *
          Matrix.det (M.submatrix j.succAbove i.succAbove) := by
    unfold higham9_8_alternatingSign
    calc
      (-1 : ℝ) ^ i.val *
          ((↑hdet_unit.unit⁻¹ : ℝ) *
            (((-1 : ℝ) ^ (j.val + i.val)) *
              Matrix.det (M.submatrix j.succAbove i.succAbove))) *
          (-1 : ℝ) ^ j.val
          =
        (↑hdet_unit.unit⁻¹ : ℝ) *
          ((-1 : ℝ) ^ i.val *
            (((-1 : ℝ) ^ (j.val + i.val)) *
              Matrix.det (M.submatrix j.succAbove i.succAbove)) *
            (-1 : ℝ) ^ j.val) := by
            ring
      _ = (↑hdet_unit.unit⁻¹ : ℝ) *
          Matrix.det (M.submatrix j.succAbove i.succAbove) := by
            rw [show
              (-1 : ℝ) ^ i.val *
                  (((-1 : ℝ) ^ (j.val + i.val)) *
                    Matrix.det (M.submatrix j.succAbove i.succAbove)) *
                  (-1 : ℝ) ^ j.val =
                Matrix.det (M.submatrix j.succAbove i.succAbove) from by
                  calc
                    (-1 : ℝ) ^ i.val *
                        (((-1 : ℝ) ^ (j.val + i.val)) *
                          Matrix.det (M.submatrix j.succAbove i.succAbove)) *
                        (-1 : ℝ) ^ j.val
                        = (((-1 : ℝ) ^ i.val *
                              (-1 : ℝ) ^ (j.val + i.val)) *
                            (-1 : ℝ) ^ j.val) *
                            Matrix.det
                              (M.submatrix j.succAbove i.succAbove) := by
                              ring
                    _ = ((-1 : ℝ) ^ (i.val + (j.val + i.val)) *
                            (-1 : ℝ) ^ j.val) *
                            Matrix.det
                              (M.submatrix j.succAbove i.succAbove) := by
                              rw [← pow_add]
                    _ = (-1 : ℝ) ^ (i.val + (j.val + i.val) + j.val) *
                            Matrix.det
                              (M.submatrix j.succAbove i.succAbove) := by
                              rw [← pow_add]
                    _ = (-1 : ℝ) ^ (2 * (i.val + j.val)) *
                            Matrix.det
                              (M.submatrix j.succAbove i.succAbove) := by
                              have h :
                                  i.val + (j.val + i.val) + j.val =
                                    2 * (i.val + j.val) := by omega
                              rw [h]
                    _ = Matrix.det
                          (M.submatrix j.succAbove i.succAbove) := by
                              rw [pow_mul]
                              simp]
  rw [hsign]
  exact mul_nonneg (le_of_lt hinvdet_pos) hminor_nonneg

/-- **Problem 9.8 support**, nonsingular source wrapper for the entrywise
checkerboard sign pattern of `A^{-1}` under total nonnegativity. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_entry_nonneg_of_det_ne_zero
    {n : ℕ} {A : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdet :
      Matrix.det
        (Matrix.of A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) ≠ 0) :
    ∀ i j : Fin (n + 1),
      0 ≤ higham9_8_checkerboardConjugate
        (nonsingInv (n + 1) A) i j :=
  higham9_8_checkerboardConjugate_nonsingInv_entry_nonneg_of_det_pos hTN
    (higham9_6_totalNonnegative_det_pos_of_det_ne_zero hTN hdet)

/-- **Problem 9.8 support**, the empty-minor case of total nonnegativity for
the checkerboard conjugate of the nonsingular inverse. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_empty_minor_nonneg
    {n : ℕ} {A : Fin (n + 1) → Fin (n + 1) → ℝ} :
    0 ≤ Matrix.det
      (fun r c : Fin 0 =>
        higham9_8_checkerboardConjugate
          (nonsingInv (n + 1) A) (Fin.elim0 r) (Fin.elim0 c)) := by
  rw [Matrix.det_fin_zero]
  norm_num

/-- **Problem 9.8 support**, the `1 by 1` minor case of total nonnegativity
for the checkerboard conjugate of the nonsingular inverse.  This packages the
cofactor-level sign theorem in the same row/column-selection shape as
`higham9_6_IsTotallyNonnegative`.

The full selected-minor theorem is
`higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg`. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_orderOne_minor_nonneg
    {n : ℕ} {A : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdet :
      Matrix.det
        (Matrix.of A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) ≠ 0) :
    ∀ rows cols : Fin 1 → Fin (n + 1),
      StrictMono (fun r : Fin 1 => (rows r).val) →
      StrictMono (fun c : Fin 1 => (cols c).val) →
        0 ≤ Matrix.det
          (fun r c : Fin 1 =>
            higham9_8_checkerboardConjugate
              (nonsingInv (n + 1) A) (rows r) (cols c)) := by
  intro rows cols _hrows _hcols
  rw [Matrix.det_fin_one]
  exact higham9_8_checkerboardConjugate_nonsingInv_entry_nonneg_of_det_ne_zero
    hTN hdet (rows 0) (cols 0)

private theorem higham9_8_succAbove_checkerboard_sign_products {n : ℕ}
    (p q : Fin (n + 1)) :
    (∏ r : Fin n, higham9_8_alternatingSign (p.succAbove r)) *
        ((-1 : ℝ) ^ (p.val + q.val)) *
        (∏ c : Fin n, higham9_8_alternatingSign (q.succAbove c)) = 1 := by
  let total : ℝ :=
    ∏ x : Fin (n + 1), higham9_8_alternatingSign x
  have htotal_sq : total * total = 1 := by
    calc
      total * total =
          ∏ x : Fin (n + 1),
            higham9_8_alternatingSign x * higham9_8_alternatingSign x := by
            simp [total, Finset.prod_mul_distrib]
      _ = 1 := by
            simp [higham9_8_alternatingSign_sq]
  have hrow :
      (∏ r : Fin n, higham9_8_alternatingSign (p.succAbove r)) =
        higham9_8_alternatingSign p * total := by
    have h :=
      Fin.prod_univ_succAbove
        (fun x : Fin (n + 1) => higham9_8_alternatingSign x) p
    have htotal :
        higham9_8_alternatingSign p *
          (∏ r : Fin n, higham9_8_alternatingSign (p.succAbove r)) =
            total := by
      simpa [total] using h.symm
    calc
      (∏ r : Fin n, higham9_8_alternatingSign (p.succAbove r))
          =
        (higham9_8_alternatingSign p *
            higham9_8_alternatingSign p) *
          (∏ r : Fin n, higham9_8_alternatingSign (p.succAbove r)) := by
            rw [higham9_8_alternatingSign_sq p]
            ring
      _ = higham9_8_alternatingSign p *
          (higham9_8_alternatingSign p *
            (∏ r : Fin n, higham9_8_alternatingSign (p.succAbove r))) := by
            ring
      _ = higham9_8_alternatingSign p * total := by
            rw [htotal]
  have hcol :
      (∏ c : Fin n, higham9_8_alternatingSign (q.succAbove c)) =
        higham9_8_alternatingSign q * total := by
    have h :=
      Fin.prod_univ_succAbove
        (fun x : Fin (n + 1) => higham9_8_alternatingSign x) q
    have htotal :
        higham9_8_alternatingSign q *
          (∏ c : Fin n, higham9_8_alternatingSign (q.succAbove c)) =
            total := by
      simpa [total] using h.symm
    calc
      (∏ c : Fin n, higham9_8_alternatingSign (q.succAbove c))
          =
        (higham9_8_alternatingSign q *
            higham9_8_alternatingSign q) *
          (∏ c : Fin n, higham9_8_alternatingSign (q.succAbove c)) := by
            rw [higham9_8_alternatingSign_sq q]
            ring
      _ = higham9_8_alternatingSign q *
          (higham9_8_alternatingSign q *
            (∏ c : Fin n, higham9_8_alternatingSign (q.succAbove c))) := by
            ring
      _ = higham9_8_alternatingSign q * total := by
            rw [htotal]
  have hpq :
      ((-1 : ℝ) ^ (p.val + q.val)) =
        higham9_8_alternatingSign p * higham9_8_alternatingSign q := by
    unfold higham9_8_alternatingSign
    rw [pow_add]
  rw [hrow, hcol, hpq]
  calc
    (higham9_8_alternatingSign p * total) *
        (higham9_8_alternatingSign p * higham9_8_alternatingSign q) *
        (higham9_8_alternatingSign q * total)
        =
      (higham9_8_alternatingSign p * higham9_8_alternatingSign p) *
        (higham9_8_alternatingSign q * higham9_8_alternatingSign q) *
        (total * total) := by
          ring
    _ = 1 := by
          rw [higham9_8_alternatingSign_sq p,
            higham9_8_alternatingSign_sq q, htotal_sq]
          ring

/-- **Problem 9.8 support**, adjugating the nonsingular inverse returns the
source matrix scaled by the inverse determinant.  This is the algebraic bridge
for the codimension-one Jacobi-minor case and uses the repository nonsingular
inverse, not an assumed inverse-minor theorem. -/
theorem higham9_8_adjugate_nonsingInv_eq_det_nonsingInv_smul
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.adjugate
        (Matrix.of (nonsingInv n A) : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.det
          (Matrix.of (nonsingInv n A) : Matrix (Fin n) (Fin n) ℝ) •
        (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of A
  let B : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (nonsingInv n A)
  have hB_eq : B = M⁻¹ := by
    ext i j
    rfl
  have hM_unit : IsUnit (Matrix.det M) :=
    isUnit_iff_ne_zero.mpr hdet
  have hB_unit : IsUnit (Matrix.det B) := by
    rw [hB_eq]
    exact Matrix.isUnit_nonsing_inv_det M hM_unit
  have hB_inv : B⁻¹ = M := by
    rw [hB_eq, Matrix.nonsing_inv_nonsing_inv M hM_unit]
  have hB_inv_apply :
      B⁻¹ = (↑hB_unit.unit⁻¹ : ℝ) • Matrix.adjugate B :=
    Matrix.nonsing_inv_apply B hB_unit
  ext i j
  have hentry :
      M i j = (↑hB_unit.unit⁻¹ : ℝ) *
        Matrix.adjugate B i j := by
    have h := congrFun (congrFun (hB_inv.symm.trans hB_inv_apply) i) j
    simpa [Matrix.smul_apply] using h
  have hmul :
      (↑hB_unit.unit : ℝ) * M i j =
        Matrix.adjugate B i j := by
    have hunit_mul :
        (↑hB_unit.unit : ℝ) * (↑hB_unit.unit⁻¹ : ℝ) = 1 := by
      exact Units.mul_inv hB_unit.unit
    calc
      (↑hB_unit.unit : ℝ) * M i j =
          (↑hB_unit.unit : ℝ) *
            ((↑hB_unit.unit⁻¹ : ℝ) * Matrix.adjugate B i j) := by
            rw [hentry]
      _ = ((↑hB_unit.unit : ℝ) * (↑hB_unit.unit⁻¹ : ℝ)) *
            Matrix.adjugate B i j := by
            ring
      _ = Matrix.adjugate B i j := by
            rw [hunit_mul]
            ring
  rw [Matrix.smul_apply]
  rw [← hB_unit.unit_spec]
  exact hmul.symm

/-- **Problem 9.8 support**, the codimension-one case of total
nonnegativity for the checkerboard conjugate of the nonsingular inverse.
For an `(n+1) by (n+1)` totally nonnegative nonsingular matrix, every
`n by n` minor obtained by deleting one row and one column from
`J A^{-1} J` is nonnegative.  This is the next cofactor-level Jacobi case
after the already proved entrywise inverse-minor theorem; the arbitrary
intermediate complementary-minor theorem remains the only missing source
case. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_codimOne_minor_nonneg
    {n : ℕ} {A : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdet :
      Matrix.det
        (Matrix.of A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) ≠ 0) :
    ∀ p q : Fin (n + 1),
      0 ≤ Matrix.det
        (fun r c : Fin n =>
          higham9_8_checkerboardConjugate
            (nonsingInv (n + 1) A) (p.succAbove r) (q.succAbove c)) := by
  intro p q
  classical
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of A
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of (nonsingInv (n + 1) A)
  have hB_eq : B = M⁻¹ := by
    ext i j
    rfl
  have hdetM_pos : 0 < Matrix.det M :=
    higham9_6_totalNonnegative_det_pos_of_det_ne_zero hTN hdet
  have hdetB_pos : 0 < Matrix.det B := by
    rw [hB_eq, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact inv_pos.mpr hdetM_pos
  have hAqp_nonneg : 0 ≤ A q p :=
    higham9_6_totalNonnegative_entry_nonneg hTN q p
  have hadj :
      Matrix.adjugate B =
        Matrix.det B • M := by
    simpa [B, M] using
      higham9_8_adjugate_nonsingInv_eq_det_nonsingInv_smul
        (n := n + 1) (A := A) hdet
  have hadj_entry :
      Matrix.adjugate B q p = Matrix.det B * A q p := by
    have h := congrFun (congrFun hadj q) p
    simpa [Matrix.smul_apply, M] using h
  let s : ℝ := (-1 : ℝ) ^ (p.val + q.val)
  have hs_sq : s * s = 1 := by
    calc
      s * s = (-1 : ℝ) ^ (p.val + q.val + (p.val + q.val)) := by
        simp [s, ← pow_add]
      _ = (-1 : ℝ) ^ (2 * (p.val + q.val)) := by
        have h : p.val + q.val + (p.val + q.val) =
            2 * (p.val + q.val) := by omega
        rw [h]
      _ = 1 := by
        rw [pow_mul]
        simp
  have hcofactor :
      Matrix.adjugate B q p =
        s * Matrix.det (B.submatrix p.succAbove q.succAbove) := by
    simpa [s, Nat.add_comm] using
      Matrix.adjugate_fin_succ_eq_det_submatrix B q p
  have hminor_B :
      Matrix.det (B.submatrix p.succAbove q.succAbove) =
        s * (Matrix.det B * A q p) := by
    calc
      Matrix.det (B.submatrix p.succAbove q.succAbove)
          = (s * s) * Matrix.det (B.submatrix p.succAbove q.succAbove) := by
            rw [hs_sq]
            ring
      _ = s * (s * Matrix.det (B.submatrix p.succAbove q.succAbove)) := by
            ring
      _ = s * (Matrix.det B * A q p) := by
            rw [← hcofactor, hadj_entry]
  have hscale :=
    higham9_8_checkerboardConjugate_minor_det_scale
      (n := n + 1) (k := n) (A := nonsingInv (n + 1) A)
      (rows := fun r : Fin n => p.succAbove r)
      (cols := fun c : Fin n => q.succAbove c)
  have hsign :=
    higham9_8_succAbove_checkerboard_sign_products p q
  have hminor_fn :
      Matrix.det
          (fun r c : Fin n =>
            nonsingInv (n + 1) A (p.succAbove r) (q.succAbove c)) =
        s * (Matrix.det B * A q p) := by
    simpa [B] using hminor_B
  have hdet_checker :
      Matrix.det
          (fun r c : Fin n =>
            higham9_8_checkerboardConjugate
              (nonsingInv (n + 1) A) (p.succAbove r) (q.succAbove c)) =
        Matrix.det B * A q p := by
    calc
      Matrix.det
          (fun r c : Fin n =>
            higham9_8_checkerboardConjugate
              (nonsingInv (n + 1) A) (p.succAbove r) (q.succAbove c))
          =
        (∏ r : Fin n, higham9_8_alternatingSign (p.succAbove r)) *
          Matrix.det
            (fun r c : Fin n =>
              nonsingInv (n + 1) A (p.succAbove r) (q.succAbove c)) *
          (∏ c : Fin n, higham9_8_alternatingSign (q.succAbove c)) := by
            simpa using hscale
      _ =
        (∏ r : Fin n, higham9_8_alternatingSign (p.succAbove r)) *
          (s * (Matrix.det B * A q p)) *
          (∏ c : Fin n, higham9_8_alternatingSign (q.succAbove c)) := by
            rw [hminor_fn]
      _ =
        ((∏ r : Fin n, higham9_8_alternatingSign (p.succAbove r)) *
          s *
          (∏ c : Fin n, higham9_8_alternatingSign (q.succAbove c))) *
          (Matrix.det B * A q p) := by
            ring
      _ = Matrix.det B * A q p := by
            rw [hsign]
            ring
  rw [hdet_checker]
  exact mul_nonneg (le_of_lt hdetB_pos) hAqp_nonneg

private theorem higham9_8_strictMono_fin_self_eq_id {n : ℕ}
    {f : Fin n → Fin n}
    (hf : StrictMono (fun i : Fin n => (f i).val)) :
    f = id := by
  classical
  have hf_fin : StrictMono f := by
    intro a b hab
    exact hf hab
  have hf_univ :
      f = (Finset.univ : Finset (Fin n)).orderEmbOfFin (by simp) := by
    exact
      Finset.orderEmbOfFin_unique
        (s := (Finset.univ : Finset (Fin n))) (h := by simp)
        (f := f) (by intro x; simp) hf_fin
  have hid_univ :
      (fun i : Fin n => i) =
        (Finset.univ : Finset (Fin n)).orderEmbOfFin (by simp) := by
    exact
      Finset.orderEmbOfFin_unique
        (s := (Finset.univ : Finset (Fin n))) (h := by simp)
        (f := fun i : Fin n => i) (by intro x; simp)
        (by intro a b hab; exact hab)
  exact hf_univ.trans hid_univ.symm

/-- **Problem 9.8 support**, checkerboard conjugation preserves the full
determinant.  The row- and column-sign products occur twice and cancel. -/
theorem higham9_8_checkerboardConjugate_det_eq {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    Matrix.det
        (Matrix.of (higham9_8_checkerboardConjugate A) :
          Matrix (Fin n) (Fin n) ℝ) =
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  let p : ℝ := ∏ r : Fin n, higham9_8_alternatingSign r
  have hp : p * p = 1 := by
    calc
      p * p = ∏ r : Fin n,
          higham9_8_alternatingSign r * higham9_8_alternatingSign r := by
            simp [p, Finset.prod_mul_distrib]
      _ = 1 := by
            simp [higham9_8_alternatingSign_sq]
  have hscale :=
    higham9_8_checkerboardConjugate_minor_det_scale
      (n := n) (k := n) A (fun i : Fin n => i) (fun i : Fin n => i)
  change Matrix.det
      (fun r c : Fin n => higham9_8_checkerboardConjugate A r c) =
    Matrix.det (fun r c : Fin n => A r c)
  calc
    Matrix.det
        (fun r c : Fin n => higham9_8_checkerboardConjugate A r c)
        = p * Matrix.det (fun r c : Fin n => A r c) * p := by
          simpa [p] using hscale
    _ = Matrix.det (fun r c : Fin n => A r c) := by
          calc
            p * Matrix.det (fun r c : Fin n => A r c) * p
                = (p * p) * Matrix.det (fun r c : Fin n => A r c) := by
                  ring
            _ = Matrix.det (fun r c : Fin n => A r c) := by
                  rw [hp]
                  ring

/-- **Problem 9.8 support**, the full determinant case of total
nonnegativity for the checkerboard conjugate of the nonsingular inverse. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_det_nonneg
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    0 ≤ Matrix.det
      (Matrix.of (higham9_8_checkerboardConjugate (nonsingInv n A)) :
        Matrix (Fin n) (Fin n) ℝ) := by
  classical
  have hdet_pos :
      0 < Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) :=
    higham9_6_totalNonnegative_det_pos_of_det_ne_zero hTN hdet
  have hinv_det :
      Matrix.det (Matrix.of (nonsingInv n A) :
          Matrix (Fin n) (Fin n) ℝ) =
        (Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))⁻¹ := by
    unfold nonsingInv
    letI : Inv (Matrix (Fin n) (Fin n) ℝ) := Matrix.inv
    change
      Matrix.det
          ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹) =
        (Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))⁻¹
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hinv_pos :
      0 < Matrix.det (Matrix.of (nonsingInv n A) :
          Matrix (Fin n) (Fin n) ℝ) := by
    rw [hinv_det]
    exact inv_pos.mpr hdet_pos
  rw [higham9_8_checkerboardConjugate_det_eq]
  exact le_of_lt hinv_pos

/-- **Problem 9.8 support**, the full-order minor case of total
nonnegativity for the checkerboard conjugate of the nonsingular inverse.  Any
strictly increasing self-selection of `Fin n` is the identity, so this reduces
to the full determinant theorem above. -/
theorem higham9_8_checkerboardConjugate_nonsingInv_full_order_minor_nonneg
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hTN : higham9_6_IsTotallyNonnegative A)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∀ rows cols : Fin n → Fin n,
      StrictMono (fun r : Fin n => (rows r).val) →
      StrictMono (fun c : Fin n => (cols c).val) →
        0 ≤ Matrix.det
          (fun r c : Fin n =>
            higham9_8_checkerboardConjugate
              (nonsingInv n A) (rows r) (cols c)) := by
  intro rows cols hrows hcols
  have hrows_id : rows = id :=
    higham9_8_strictMono_fin_self_eq_id hrows
  have hcols_id : cols = id :=
    higham9_8_strictMono_fin_self_eq_id hcols
  rw [hrows_id, hcols_id]
  exact higham9_8_checkerboardConjugate_nonsingInv_det_nonneg hTN hdet

/-- **Problem 9.8**, if `J A J = L U`, then the checkerboard-conjugated
factors multiply back to `A`. -/
theorem higham9_8_checkerboard_lu_product_eq {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n (higham9_8_checkerboardConjugate A) L U) :
    matMul n (higham9_8_checkerboardConjugate L)
        (higham9_8_checkerboardConjugate U) = A := by
  rw [higham9_8_checkerboardConjugate_matMul]
  have hprod : matMul n L U = higham9_8_checkerboardConjugate A := by
    ext i j
    exact hLU.product_eq i j
  rw [hprod, higham9_8_checkerboardConjugate_involutive]

/-- **Problem 9.8**, an LU factorization of `J A J` induces an LU
factorization of `A` by conjugating both factors with `J`.  This is only the
exact algebraic adapter; it does not assert the missing total-nonnegative LU
existence theorem. -/
theorem higham9_8_lu_of_checkerboard_lu {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n (higham9_8_checkerboardConjugate A) L U) :
    LUFactSpec n A
      (higham9_8_checkerboardConjugate L)
      (higham9_8_checkerboardConjugate U) where
  L_diag := by
    intro i
    unfold higham9_8_checkerboardConjugate
    rw [hLU.L_diag i]
    simpa [mul_assoc] using higham9_8_alternatingSign_sq i
  L_upper_zero := by
    intro i j hij
    unfold higham9_8_checkerboardConjugate
    rw [hLU.L_upper_zero i j hij]
    ring
  U_lower_zero := by
    intro i j hji
    unfold higham9_8_checkerboardConjugate
    rw [hLU.U_lower_zero i j hji]
    ring
  product_eq := by
    intro i j
    have hprod := congrFun (congrFun
      (higham9_8_checkerboard_lu_product_eq hLU) i) j
    simpa [matMul] using hprod

/-- **Problem 9.8**, source algebraic conclusion: if the checkerboard
conjugate `J A J` has nonnegative LU factors, then the induced factorization of
`A` satisfies `|J L J| |J U J| = |A|` componentwise. -/
theorem higham9_8_abs_conjugated_lu_product_eq_abs {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n (higham9_8_checkerboardConjugate A) L U)
    (hL_nonneg : ∀ i j : Fin n, 0 ≤ L i j)
    (hU_nonneg : ∀ i j : Fin n, 0 ≤ U i j) :
    ∀ i j : Fin n,
      ∑ k : Fin n,
        |higham9_8_checkerboardConjugate L i k| *
          |higham9_8_checkerboardConjugate U k j| = |A i j| := by
  have hJAJ_nonneg :
      ∀ i j : Fin n, 0 ≤ higham9_8_checkerboardConjugate A i j := by
    intro i j
    rw [← hLU.product_eq i j]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hL_nonneg i k) (hU_nonneg k j))
  intro i j
  calc
    (∑ k : Fin n,
        |higham9_8_checkerboardConjugate L i k| *
          |higham9_8_checkerboardConjugate U k j|)
        = ∑ k : Fin n, |L i k| * |U k j| := by
          apply Finset.sum_congr rfl
          intro k _
          rw [higham9_8_abs_checkerboardConjugate L i k,
            higham9_8_abs_checkerboardConjugate U k j]
    _ = ∑ k : Fin n, L i k * U k j := by
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_of_nonneg (hL_nonneg i k), abs_of_nonneg (hU_nonneg k j)]
    _ = higham9_8_checkerboardConjugate A i j := hLU.product_eq i j
    _ = |A i j| :=
          higham9_8_checkerboardConjugate_eq_abs_of_nonneg hJAJ_nonneg i j

/-- **Problem 9.8**, total-nonnegative checkerboard conjugate route.

If the checkerboard conjugate `J A J` is totally nonnegative and has positive
proper leading principal blocks, then the recursive Problem 9.6 LU theorem
supplies nonnegative factors for `J A J`; conjugating those factors gives an
exact LU certificate for `A` and the source algebraic conclusion
`|J L J| |J U J| = |A|`.  The theorem deliberately leaves the external
inverse-minor fact that would prove total nonnegativity of `J A J` from
properties of `A⁻¹` as an explicit upstream hypothesis. -/
theorem higham9_8_abs_lu_product_eq_abs_of_checkerboard_totalNonnegative_and_pos
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hTNJ : higham9_6_IsTotallyNonnegative
      (higham9_8_checkerboardConjugate A))
    (hdetJ :
      0 < Matrix.det
        (Matrix.of (higham9_8_checkerboardConjugate A) :
          Matrix (Fin n) (Fin n) ℝ))
    (hleadJ :
      ∀ k : ℕ, k < n → k ≠ 0 →
        0 < Matrix.det
          (higham9_2_leadingPrincipalBlock
            (Matrix.of (higham9_8_checkerboardConjugate A) :
              Matrix (Fin n) (Fin n) ℝ) k)) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A
        (higham9_8_checkerboardConjugate L)
        (higham9_8_checkerboardConjugate U) ∧
      (∀ i j : Fin n,
        ∑ k : Fin n,
          |higham9_8_checkerboardConjugate L i k| *
            |higham9_8_checkerboardConjugate U k j| = |A i j|) := by
  obtain ⟨L, U, hLU, hL_nonneg, hU_nonneg⟩ :=
    higham9_6_lu_exists_nonnegative_of_totalNonnegative_and_properLeadingPrincipalBlock_pos
      hTNJ hdetJ hleadJ
  exact ⟨L, U, higham9_8_lu_of_checkerboard_lu hLU,
    higham9_8_abs_conjugated_lu_product_eq_abs hLU hL_nonneg hU_nonneg⟩

/-- **Problem 9.8**, checkerboard route with the Appendix A determinant
inequality exposed.

This is the Problem 9.8 analogue of the Problem 9.6 principal-block route:
if total nonnegativity of `J A J`, nonsingularity, and the source-cited
principal-block determinant inequalities are supplied for the checkerboard
conjugate, then the nonnegative-LU adapter proves the source
`|L||U| = |A|` conclusion for `A`. -/
theorem higham9_8_abs_lu_product_eq_abs_of_checkerboard_principalBlock_inequalities
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hTNJ : higham9_6_IsTotallyNonnegative
      (higham9_8_checkerboardConjugate A))
    (hdetJ :
      0 < Matrix.det
        (Matrix.of (higham9_8_checkerboardConjugate A) :
          Matrix (Fin n) (Fin n) ℝ))
    (hineqJ :
      ∀ k : ℕ, k < n → k ≠ 0 →
        Matrix.det
            (Matrix.of (higham9_8_checkerboardConjugate A) :
              Matrix (Fin n) (Fin n) ℝ) ≤
          Matrix.det
              (higham9_2_leadingPrincipalBlock
                (Matrix.of (higham9_8_checkerboardConjugate A) :
                  Matrix (Fin n) (Fin n) ℝ) k) *
            Matrix.det
              (higham9_6_trailingPrincipalBlock
                (Matrix.of (higham9_8_checkerboardConjugate A) :
                  Matrix (Fin n) (Fin n) ℝ) k)) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A
        (higham9_8_checkerboardConjugate L)
        (higham9_8_checkerboardConjugate U) ∧
      (∀ i j : Fin n,
        ∑ k : Fin n,
          |higham9_8_checkerboardConjugate L i k| *
            |higham9_8_checkerboardConjugate U k j| = |A i j|) := by
  apply
    higham9_8_abs_lu_product_eq_abs_of_checkerboard_totalNonnegative_and_pos
      A hTNJ hdetJ
  intro k hk hk0
  exact
    higham9_6_leadingPrincipalBlock_det_pos_of_determinantal_inequality
      hTNJ (Nat.le_of_lt hk) hdetJ (hineqJ k hk hk0)

end LeanFpAnalysis.FP
