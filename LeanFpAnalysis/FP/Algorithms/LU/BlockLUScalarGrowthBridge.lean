/-
# Chapter 13 scalar-GE to block-Schur growth bridge

This module identifies the Schur complement of an arbitrary leading scalar
split with the corresponding equation (9.5) no-pivot GE reduced stage.  It
then places that Schur complement inside the common reduced-history growth
object used by Problem 13.4 and equation (13.23).

The scalar `LUFactSpec` hypothesis is essential: invertible block pivots alone
need not admit no-pivot scalar LU in the fixed within-block ordering.  The
point-row source route supplies this scalar certificate independently.
-/

import LeanFpAnalysis.FP.Algorithms.LU.BlockLUPointRowGrowthSourceClosure

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix

noncomputable section

private def leadFin {r s : ℕ} (i : Fin r) : Fin (r + s) := Fin.castAdd s i
private def tailFin {r s : ℕ} (i : Fin s) : Fin (r + s) := Fin.natAdd r i

private def leadingBlock {r s : ℕ}
    (M : Matrix (Fin (r + s)) (Fin (r + s)) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => M (leadFin i) (leadFin j)

private def upperRightBlock {r s : ℕ}
    (M : Matrix (Fin (r + s)) (Fin (r + s)) ℝ) : Matrix (Fin r) (Fin s) ℝ :=
  fun i j => M (leadFin i) (tailFin j)

private def lowerLeftBlock {r s : ℕ}
    (M : Matrix (Fin (r + s)) (Fin (r + s)) ℝ) : Matrix (Fin s) (Fin r) ℝ :=
  fun i j => M (tailFin i) (leadFin j)

private def trailingBlock {r s : ℕ}
    (M : Matrix (Fin (r + s)) (Fin (r + s)) ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  fun i j => M (tailFin i) (tailFin j)

private theorem lu_leading_block_product {r s : ℕ}
    {A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ}
    (hLU : LUFactSpec (r + s) A L U) :
    leadingBlock A = leadingBlock L * leadingBlock U := by
  ext i j
  change A (leadFin i) (leadFin j) = _
  rw [Matrix.mul_apply, ← hLU.product_eq (leadFin i) (leadFin j)]
  rw [Fin.sum_univ_add]
  simp only [leadingBlock, leadFin]
  have hzero : ∀ k : Fin s,
      L (Fin.castAdd s i) (Fin.natAdd r k) *
          U (Fin.natAdd r k) (Fin.castAdd s j) = 0 := by
    intro k
    rw [hLU.L_upper_zero]
    · simp
    · simp
      omega
  rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]

private theorem lu_upper_right_block_product {r s : ℕ}
    {A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ}
    (hLU : LUFactSpec (r + s) A L U) :
    upperRightBlock A = leadingBlock L * upperRightBlock U := by
  ext i j
  change A (leadFin i) (tailFin j) = _
  rw [Matrix.mul_apply, ← hLU.product_eq (leadFin i) (tailFin j)]
  rw [Fin.sum_univ_add]
  simp only [upperRightBlock, leadingBlock, leadFin, tailFin]
  have hzero : ∀ k : Fin s,
      L (Fin.castAdd s i) (Fin.natAdd r k) *
          U (Fin.natAdd r k) (Fin.natAdd r j) = 0 := by
    intro k
    rw [hLU.L_upper_zero]
    · simp
    · simp
      omega
  rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]

private theorem lu_lower_left_block_product {r s : ℕ}
    {A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ}
    (hLU : LUFactSpec (r + s) A L U) :
    lowerLeftBlock A = lowerLeftBlock L * leadingBlock U := by
  ext i j
  change A (tailFin i) (leadFin j) = _
  rw [Matrix.mul_apply, ← hLU.product_eq (tailFin i) (leadFin j)]
  rw [Fin.sum_univ_add]
  simp only [lowerLeftBlock, leadingBlock, leadFin, tailFin]
  have hzero : ∀ k : Fin s,
      L (Fin.natAdd r i) (Fin.natAdd r k) *
          U (Fin.natAdd r k) (Fin.castAdd s j) = 0 := by
    intro k
    rw [hLU.U_lower_zero]
    · simp
    · simp
      omega
  rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]

private theorem lu_trailing_block_product {r s : ℕ}
    {A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ}
    (hLU : LUFactSpec (r + s) A L U) :
    trailingBlock A =
      lowerLeftBlock L * upperRightBlock U + trailingBlock L * trailingBlock U := by
  ext i j
  change A (tailFin i) (tailFin j) = _
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← hLU.product_eq (tailFin i) (tailFin j)]
  rw [Fin.sum_univ_add]
  rfl

private theorem lu_schur_eq_trailing_product {r s : ℕ}
    {A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ}
    (hLU : LUFactSpec (r + s) A L U)
    [Invertible (leadingBlock A)] :
    trailingBlock A -
        lowerLeftBlock A * ⅟(leadingBlock A) * upperRightBlock A =
      trailingBlock L * trailingBlock U := by
  have h11 := lu_leading_block_product hLU
  have h12 := lu_upper_right_block_product hLU
  have h21 := lu_lower_left_block_product hLU
  have h22 := lu_trailing_block_product hLU
  have hdetA : Matrix.det (leadingBlock A) ≠ 0 :=
    (Matrix.isUnit_det_of_invertible (leadingBlock A)).ne_zero
  have hdetProd :
      Matrix.det (leadingBlock L) * Matrix.det (leadingBlock U) ≠ 0 := by
    rw [← Matrix.det_mul, ← h11]
    exact hdetA
  have hdetL : Matrix.det (leadingBlock L) ≠ 0 := by
    intro hzero
    apply hdetProd
    simp [hzero]
  letI : Invertible (Matrix.det (leadingBlock L)) :=
    invertibleOfNonzero hdetL
  letI : Invertible (leadingBlock L) :=
    Matrix.invertibleOfDetInvertible (leadingBlock L)
  have hLower :
      lowerLeftBlock A * ⅟(leadingBlock A) =
        lowerLeftBlock L * ⅟(leadingBlock L) := by
    have hmul :
        (lowerLeftBlock A * ⅟(leadingBlock A)) * leadingBlock A =
          (lowerLeftBlock L * ⅟(leadingBlock L)) * leadingBlock A := by
      rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
      rw [h21, h11]
      simp [Matrix.mul_assoc]
    calc
      lowerLeftBlock A * ⅟(leadingBlock A) =
          ((lowerLeftBlock A * ⅟(leadingBlock A)) * leadingBlock A) *
            ⅟(leadingBlock A) := by simp [Matrix.mul_assoc]
      _ = ((lowerLeftBlock L * ⅟(leadingBlock L)) * leadingBlock A) *
            ⅟(leadingBlock A) := by rw [hmul]
      _ = lowerLeftBlock L * ⅟(leadingBlock L) := by
        simp [Matrix.mul_assoc]
  rw [h22, hLower, h12]
  simp [Matrix.mul_assoc]

private theorem lu_reduced_tail_eq_trailing_product {r s : ℕ}
    {A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ}
    (hLU : LUFactSpec (r + s) A L U) (i j : Fin s) :
    higham9_5_rectGEReducedEntry A L U r (tailFin i) (tailFin j) =
      (trailingBlock L * trailingBlock U) i j := by
  rw [higham9_5_rectGEReducedEntry, ← hLU.product_eq]
  rw [Fin.sum_univ_add]
  unfold higham9_5_rectPrefixRange
  rw [Finset.sum_range]
  simp only [tailFin, Matrix.mul_apply, trailingBlock]
  have hprefix :
      (∑ x : Fin r,
          L (Fin.natAdd r i) (Fin.castAdd s x) *
            U (Fin.castAdd s x) (Fin.natAdd r j)) =
        ∑ x : Fin r,
          (if h : x.val < r + s then
            L (Fin.natAdd r i) ⟨x.val, h⟩ *
              U ⟨x.val, h⟩ (Fin.natAdd r j)
          else 0) := by
    apply Finset.sum_congr rfl
    intro x _hx
    have hxlt : x.val < r + s :=
      lt_of_lt_of_le x.isLt (Nat.le_add_right r s)
    have hxFin :
        (⟨x.val, hxlt⟩ : Fin (r + s)) =
          Fin.castAdd s x := Fin.ext rfl
    simp only [dif_pos hxlt]
    rw [hxFin]
  rw [← hprefix]
  ring

/-- Problem 13.4 scalar/block bridge: under an exact scalar no-pivot LU
certificate, the Schur complement after eliminating the first `r` coordinates
is exactly the equation (9.5) reduced matrix at step `r`, restricted to the
trailing coordinates. -/
theorem higham13_problem13_4_schur_eq_noPivotReducedStage
    {r s : ℕ}
    (A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11]
    (hA11_block : A11 = fun i j => A (leadFin i) (leadFin j))
    (hA12_block : A12 = fun i j => A (leadFin i) (tailFin j))
    (hA21_block : A21 = fun i j => A (tailFin i) (leadFin j))
    (hA22_block : A22 = fun i j => A (tailFin i) (tailFin j))
    (hLU : LUFactSpec (r + s) A L U) :
    ∀ i j : Fin s,
      (A22 - A21 * ⅟A11 * A12) i j =
        higham9_5_rectGEReducedEntry A L U r (tailFin i) (tailFin j) := by
  have h11 : leadingBlock A = A11 := by
    ext i j
    rw [hA11_block]
    rfl
  have h12 : upperRightBlock A = A12 := by
    ext i j
    rw [hA12_block]
    rfl
  have h21 : lowerLeftBlock A = A21 := by
    ext i j
    rw [hA21_block]
    rfl
  have h22 : trailingBlock A = A22 := by
    ext i j
    rw [hA22_block]
    rfl
  letI : Invertible (leadingBlock A) :=
    Invertible.copy (inferInstance : Invertible A11) _ h11
  have hSchur := lu_schur_eq_trailing_product hLU
  intro i j
  have hSchur' := congrFun (congrFun hSchur i) j
  calc
    (A22 - A21 * ⅟A11 * A12) i j =
        (trailingBlock L * trailingBlock U) i j := by
      simpa [h11, h12, h21, h22] using hSchur'
    _ = higham9_5_rectGEReducedEntry A L U r (tailFin i) (tailFin j) :=
      (lu_reduced_tail_eq_trailing_product hLU i j).symm

/-- The Problem 13.4 Schur complement is contained in the actual scalar
no-pivot reduced-history growth object. -/
theorem higham13_problem13_4_schur_le_noPivotReducedHistory
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11]
    (hA11_block : A11 = fun i j => A (leadFin i) (leadFin j))
    (hA12_block : A12 = fun i j => A (leadFin i) (tailFin j))
    (hA21_block : A21 = fun i j => A (tailFin i) (leadFin j))
    (hA22_block : A22 = fun i j => A (tailFin i) (tailFin j))
    (hLU : LUFactSpec (r + s) A L U) :
    maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
      maxEntryNorm (Nat.add_pos_left hr s)
        (higham13_noPivotReducedHistoryGrowthMatrix
          (Nat.add_pos_left hr s) A L U) := by
  let R : Matrix (Fin (r + s)) (Fin (r + s)) ℝ :=
    fun i j => higham9_5_rectGEReducedEntry A L U r i j
  have hSchur : ∀ i j : Fin s,
      (A22 - A21 * ⅟A11 * A12) i j = R (tailFin i) (tailFin j) := by
    simpa [R] using
      higham13_problem13_4_schur_eq_noPivotReducedStage
        A L U A11 A12 A21 A22
        hA11_block hA12_block hA21_block hA22_block hLU
  exact le_trans
    (maxEntryNormRect_le_maxEntryNorm_of_reindex_eq
      (Nat.add_pos_left hr s) hs hs (A22 - A21 * ⅟A11 * A12) R
      tailFin tailFin hSchur)
    (by
      simpa [R] using
        higham13_noPivotReducedHistoryGrowthMatrix_contains_stage
          (Nat.add_pos_left hr s) A L U
          (⟨r, Nat.lt_add_of_pos_right hs⟩ : Fin (r + s)))

/-- Equation (13.23), local source route: point-row diagonal dominance and an
exact scalar no-pivot LU certificate discharge the initial-matrix,
Schur-complement, and `rho <= 2` obligations for the common source growth
object.  The sole remaining block-algorithm bookkeeping hypothesis says that
the selected block upper factor occurs in that same scalar reduced history. -/
theorem higham13_eq13_23_local_block_product_from_pointRow_noPivotHistory_exact_kappa
    {r s mb rb : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hmb : 0 < mb) (hrb : 0 < rb)
    (A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ)
    (Ufac : Fin mb → Fin mb → Matrix (Fin rb) (Fin rb) ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hA11_block : A11 = fun i j => A (leadFin i) (leadFin j))
    (hA12_block : A12 = fun i j => A (leadFin i) (tailFin j))
    (hA21_block : A21 = fun i j => A (tailFin i) (leadFin j))
    (hA22_block : A22 = fun i j => A (tailFin i) (tailFin j))
    (hRow : IsRowDiagDominant (r + s) A)
    (hdet : Matrix.det A ≠ 0)
    (hLU : LUFactSpec (r + s) A L U)
    (n : ℕ) (hsn : (s : ℝ) ≤ (n : ℝ))
    (hU_le_history :
      blockMaxNorm hmb hrb Ufac ≤
        maxEntryNorm (Nat.add_pos_left hr s)
          (higham13_noPivotReducedHistoryGrowthMatrix
            (Nat.add_pos_left hr s) A L U)) :
    maxEntryNormRect hs hr (A21 * ⅟A11) *
        blockMaxNorm hmb hrb Ufac ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.add_pos_left hr s) (Nat.add_pos_left hr s) A *
          maxEntryNormRect (Nat.add_pos_left hr s) (Nat.add_pos_left hr s)
            (nonsingInv (r + s) A)) *
        maxEntryNormRect (Nat.add_pos_left hr s) (Nat.add_pos_left hr s) A := by
  let hn : 0 < r + s := Nat.add_pos_left hr s
  let G : Matrix (Fin (r + s)) (Fin (r + s)) ℝ :=
    higham13_noPivotReducedHistoryGrowthMatrix hn A L U
  let hApos : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdet
  have h11 : A11 = fun i j : Fin r =>
      A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) := by
    simpa [leadFin] using hA11_block
  have h12 : A12 = fun (i : Fin r) (j : Fin s) =>
      A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) := by
    simpa [leadFin, tailFin] using hA12_block
  have h21 : A21 = fun (i : Fin s) (j : Fin r) =>
      A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) := by
    simpa [leadFin, tailFin] using hA21_block
  have h22 : A22 = fun i j : Fin s =>
      A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) := by
    simpa [tailFin] using hA22_block
  have hA_le_G : maxEntryNorm hn A ≤ maxEntryNorm hn G := by
    simpa [G] using
      higham13_noPivotReducedHistoryGrowthMatrix_contains_initial hn A L U
  have hS_le_G :
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) ≤
        maxEntryNorm hn G := by
    simpa [G, hn] using
      higham13_problem13_4_schur_le_noPivotReducedHistory
        hr hs A L U A11 A12 A21 A22
        hA11_block hA12_block hA21_block hA22_block hLU
  have hRho : growthFactorEntry hn A G hApos ≤ 2 := by
    simpa [G] using
      higham13_eq13_23_pointRow_historyGrowthFactorEntry_le_two
        hn hRow hdet hLU hApos
  have hProduct :=
    higham13_eq13_23_local_block_product_from_source_growthFactorEntry_exact_kappa
      hr hs hn hmb hrb A G Ufac A11 A12 A21 A22
      h11 h12 h21 h22 hApos n hsn hA_le_G hS_le_G
      (by simpa [G, hn] using hU_le_history) hRho
  exact hProduct

end

end LeanFpAnalysis.FP
