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

private theorem factor_schur_eq_trailing_product {r s : ℕ}
    {A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ}
    (hprod : ∀ i j, A i j = ∑ k, L i k * U k j)
    (hL12 : ∀ i : Fin r, ∀ j : Fin s, L (leadFin i) (tailFin j) = 0)
    (hU21 : ∀ i : Fin s, ∀ j : Fin r, U (tailFin i) (leadFin j) = 0)
    [Invertible (leadingBlock A)] :
    trailingBlock A -
        lowerLeftBlock A * ⅟(leadingBlock A) * upperRightBlock A =
      trailingBlock L * trailingBlock U := by
  have h11 : leadingBlock A = leadingBlock L * leadingBlock U := by
    ext i j
    change A (leadFin i) (leadFin j) = _
    rw [hprod, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [leadingBlock, leadFin]
    have htail :
        (∑ k : Fin s,
          L (Fin.castAdd s i) (Fin.natAdd r k) *
            U (Fin.natAdd r k) (Fin.castAdd s j)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _hk
      rw [show L (Fin.castAdd s i) (Fin.natAdd r k) = 0 by
        exact hL12 i k]
      simp
    rw [htail, add_zero]
  have h12eq : upperRightBlock A = leadingBlock L * upperRightBlock U := by
    ext i j
    change A (leadFin i) (tailFin j) = _
    rw [hprod, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [upperRightBlock, leadingBlock, leadFin, tailFin]
    have htail :
        (∑ k : Fin s,
          L (Fin.castAdd s i) (Fin.natAdd r k) *
            U (Fin.natAdd r k) (Fin.natAdd r j)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _hk
      rw [show L (Fin.castAdd s i) (Fin.natAdd r k) = 0 by
        exact hL12 i k]
      simp
    rw [htail, add_zero]
  have h21eq : lowerLeftBlock A = lowerLeftBlock L * leadingBlock U := by
    ext i j
    change A (tailFin i) (leadFin j) = _
    rw [hprod, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [lowerLeftBlock, leadingBlock, leadFin, tailFin]
    have htail :
        (∑ k : Fin s,
          L (Fin.natAdd r i) (Fin.natAdd r k) *
            U (Fin.natAdd r k) (Fin.castAdd s j)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _hk
      rw [show U (Fin.natAdd r k) (Fin.castAdd s j) = 0 by
        exact hU21 k j]
      simp
    rw [htail, add_zero]
  have h22eq : trailingBlock A =
      lowerLeftBlock L * upperRightBlock U + trailingBlock L * trailingBlock U := by
    ext i j
    change A (tailFin i) (tailFin j) = _
    rw [hprod, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_add]
    rfl
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
  have hLower : lowerLeftBlock A * ⅟(leadingBlock A) =
      lowerLeftBlock L * ⅟(leadingBlock L) := by
    have hmul :
        (lowerLeftBlock A * ⅟(leadingBlock A)) * leadingBlock A =
          (lowerLeftBlock L * ⅟(leadingBlock L)) * leadingBlock A := by
      rw [Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
      rw [h21eq, h11]
      simp [Matrix.mul_assoc]
    calc
      lowerLeftBlock A * ⅟(leadingBlock A) =
          ((lowerLeftBlock A * ⅟(leadingBlock A)) * leadingBlock A) *
            ⅟(leadingBlock A) := by simp [Matrix.mul_assoc]
      _ = ((lowerLeftBlock L * ⅟(leadingBlock L)) * leadingBlock A) *
            ⅟(leadingBlock A) := by rw [hmul]
      _ = lowerLeftBlock L * ⅟(leadingBlock L) := by
        simp [Matrix.mul_assoc]
  rw [h22eq, hLower, h12eq]
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

/-- Flattening preserves the exact product equation of a uniform block LU
certificate. -/
theorem BlockLUFactSpec.blockMatrixFlatFin_product_eq {m r : ℕ}
    {A L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ}
    (hLU : BlockLUFactSpec m r A L U) (i j : Fin (m * r)) :
    blockMatrixFlatFin A i j =
      ∑ k : Fin (m * r), blockMatrixFlatFin L i k * blockMatrixFlatFin U k j := by
  let is := finProdFinEquiv.symm i
  let jt := finProdFinEquiv.symm j
  change A is.1 jt.1 is.2 jt.2 = _
  rw [← hLU.product_eq is.1 jt.1 is.2 jt.2]
  symm
  calc
    (∑ k : Fin (m * r),
        blockMatrixFlatFin L i k * blockMatrixFlatFin U k j) =
      ∑ ks : Fin m × Fin r,
        L is.1 ks.1 is.2 ks.2 * U ks.1 jt.1 ks.2 jt.2 := by
      rw [Fintype.sum_equiv finProdFinEquiv]
      intro ks
      have hi : finProdFinEquiv is = i := Equiv.apply_symm_apply _ i
      have hj : finProdFinEquiv jt = j := Equiv.apply_symm_apply _ j
      rw [← hi, ← hj]
      rw [blockMatrixFlatFin_apply, blockMatrixFlatFin_apply]
    _ = ∑ k : Fin m, ∑ l : Fin r,
        L is.1 k is.2 l * U k jt.1 l jt.2 := by
      rw [Fintype.sum_prod_type]

/-- Algebraic scalar/block stage bridge.  If a second exact factor product has
zero leading-to-trailing lower and trailing-to-leading upper rectangles, then
any unit row of its trailing lower factor selects an upper-factor entry equal
to the corresponding equation (9.5) reduced entry of a scalar no-pivot LU.

This isolates the representation fact needed to show that block-upper entries
occur in the scalar GE history; no growth estimate is assumed. -/
theorem higham13_factor_upper_entry_eq_noPivotReducedStage {r s : ℕ}
    {A Ls Us Lb Ub : Matrix (Fin (r + s)) (Fin (r + s)) ℝ}
    (hScalar : LUFactSpec (r + s) A Ls Us)
    (hBlockProd : ∀ i j, A i j = ∑ k, Lb i k * Ub k j)
    (hLb12 : ∀ i : Fin r, ∀ j : Fin s, Lb (leadFin i) (tailFin j) = 0)
    (hUb21 : ∀ i : Fin s, ∀ j : Fin r, Ub (tailFin i) (leadFin j) = 0)
    [Invertible (leadingBlock A)]
    (i j : Fin s)
    (hUnitRow : ∀ k : Fin s,
      Lb (tailFin i) (tailFin k) = if k = i then 1 else 0) :
    Ub (tailFin i) (tailFin j) =
      higham9_5_rectGEReducedEntry A Ls Us r (tailFin i) (tailFin j) := by
  have hScalarSchur := lu_schur_eq_trailing_product hScalar
  have hBlockSchur :=
    factor_schur_eq_trailing_product hBlockProd hLb12 hUb21
  have hTailProducts : trailingBlock Lb * trailingBlock Ub =
      trailingBlock Ls * trailingBlock Us := by
    rw [← hBlockSchur, ← hScalarSchur]
  calc
    Ub (tailFin i) (tailFin j) =
        (trailingBlock Lb * trailingBlock Ub) i j := by
      rw [Matrix.mul_apply]
      simp only [trailingBlock]
      rw [show (∑ k : Fin s,
          Lb (tailFin i) (tailFin k) * Ub (tailFin k) (tailFin j)) =
          ∑ k : Fin s, (if k = i then 1 else 0) *
            Ub (tailFin k) (tailFin j) by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [hUnitRow k]]
      simp
    _ = (trailingBlock Ls * trailingBlock Us) i j := by rw [hTailProducts]
    _ = higham9_5_rectGEReducedEntry A Ls Us r (tailFin i) (tailFin j) :=
      (lu_reduced_tail_eq_trailing_product hScalar i j).symm

private theorem leadingBlock_det_ne_zero_of_lu_det_ne_zero {r s : ℕ}
    {A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ}
    (hLU : LUFactSpec (r + s) A L U) (hdet : Matrix.det A ≠ 0) :
    Matrix.det (leadingBlock A) ≠ 0 := by
  have hpiv : ∀ i : Fin (r + s), U i i ≠ 0 :=
    hLU.det_ne_zero_iff_U_diag_ne_zero.mp (by simpa using hdet)
  have hprod :
      (∏ i : Fin r,
        U (Fin.castLE (Nat.le_add_right r s) i)
          (Fin.castLE (Nat.le_add_right r s) i)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i _hi
      exact hpiv (Fin.castLE (Nat.le_add_right r s) i))
  rw [← higham9_14_LUFactSpec_leadingSubmatrix_det_eq_prod_U_diag
    hLU (Nat.le_add_right r s)] at hprod
  simpa [leadingBlock, leadFin, Matrix.submatrix_apply] using hprod

private theorem blockMatrixFlatFin_lower_leading_trailing_zero {m r : ℕ}
    {A L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ}
    (hr : 0 < r) (hLU : BlockLUFactSpec m r A L U)
    (bi : Fin m) (p q : Fin (m * r))
    (hp : p.val < r * bi.val) (hq : r * bi.val ≤ q.val) :
    blockMatrixFlatFin L p q = 0 := by
  let ip := finProdFinEquiv.symm p
  let jq := finProdFinEquiv.symm q
  have hip : ip.1.val < bi.val := by
    apply (Nat.div_lt_iff_lt_mul hr).mpr
    simpa [ip, Nat.mul_comm] using hp
  have hqj : bi.val ≤ jq.1.val := by
    apply (Nat.le_div_iff_mul_le hr).mpr
    simpa [jq, Nat.mul_comm] using hq
  have hij : ip.1.val < jq.1.val := lt_of_lt_of_le hip hqj
  have hzero := hLU.L_upper_zero ip.1 jq.1 hij
  change L ip.1 jq.1 ip.2 jq.2 = 0
  rw [hzero]
  rfl

private theorem blockMatrixFlatFin_upper_trailing_leading_zero {m r : ℕ}
    {A L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ}
    (hr : 0 < r) (hLU : BlockLUFactSpec m r A L U)
    (bi : Fin m) (p q : Fin (m * r))
    (hp : r * bi.val ≤ p.val) (hq : q.val < r * bi.val) :
    blockMatrixFlatFin U p q = 0 := by
  let ip := finProdFinEquiv.symm p
  let jq := finProdFinEquiv.symm q
  have hip : bi.val ≤ ip.1.val := by
    apply (Nat.le_div_iff_mul_le hr).mpr
    simpa [ip, Nat.mul_comm] using hp
  have hqj : jq.1.val < bi.val := by
    apply (Nat.div_lt_iff_lt_mul hr).mpr
    simpa [jq, Nat.mul_comm] using hq
  have hji : jq.1.val < ip.1.val := lt_of_lt_of_le hqj hip
  have hzero := hLU.U_lower_zero ip.1 jq.1 hji
  change U ip.1 jq.1 ip.2 jq.2 = 0
  rw [hzero]
  rfl

private theorem blockMatrixFlatFin_lower_boundary_unit_row {m r : ℕ}
    {A L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ}
    (hr : 0 < r) (hLU : BlockLUFactSpec m r A L U)
    (bi : Fin m) (a : Fin r) (q : Fin (m * r))
    (hq : r * bi.val ≤ q.val) :
    blockMatrixFlatFin L (finProdFinEquiv (bi, a)) q =
      if q = finProdFinEquiv (bi, a) then 1 else 0 := by
  let jq := finProdFinEquiv.symm q
  have hq_repr : finProdFinEquiv jq = q := Equiv.apply_symm_apply _ q
  have hge : bi.val ≤ jq.1.val := by
    apply (Nat.le_div_iff_mul_le hr).mpr
    simpa [jq, Nat.mul_comm] using hq
  rw [← hq_repr, blockMatrixFlatFin_apply]
  by_cases hbi : jq.1 = bi
  · have hdiv : q.divNat = bi := by simpa [jq] using hbi
    rw [hbi]
    rw [hLU.L_diag]
    simp [jq, idBlock, Prod.ext_iff, hdiv, eq_comm]
  · have hne : bi.val ≠ jq.1.val := by
      intro hval
      exact hbi (Fin.ext hval.symm)
    have hlt : bi.val < jq.1.val := lt_of_le_of_ne hge hne
    have hpair : jq ≠ (bi, a) := by
      intro h
      exact hbi (congrArg Prod.fst h)
    rw [hLU.L_upper_zero bi jq.1 hlt]
    simp [zeroBlock, hpair]

private theorem LUFactSpec.castFin {n n' : ℕ} (h : n' = n)
    {A L U : Matrix (Fin n) (Fin n) ℝ} (hLU : LUFactSpec n A L U) :
    LUFactSpec n'
      (fun i j => A (Fin.cast h i) (Fin.cast h j))
      (fun i j => L (Fin.cast h i) (Fin.cast h j))
      (fun i j => U (Fin.cast h i) (Fin.cast h j)) := by
  subst n
  simpa using hLU

private theorem factor_product_castFin {n n' : ℕ} (h : n' = n)
    {A L U : Matrix (Fin n) (Fin n) ℝ}
    (hprod : ∀ i j, A i j = ∑ k, L i k * U k j) :
    ∀ i j : Fin n',
      A (Fin.cast h i) (Fin.cast h j) =
        ∑ k : Fin n',
          L (Fin.cast h i) (Fin.cast h k) *
            U (Fin.cast h k) (Fin.cast h j) := by
  subst n
  simpa using hprod

private theorem det_castFin_ne_zero {n n' : ℕ} (h : n' = n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hdet : Matrix.det A ≠ 0) :
    Matrix.det (fun i j : Fin n' => A (Fin.cast h i) (Fin.cast h j)) ≠ 0 := by
  subst n
  simpa using hdet

private theorem higham9_5_rectGEReducedEntry_castFin {n n' : ℕ}
    (h : n' = n) (A L U : Matrix (Fin n) (Fin n) ℝ)
    (step : ℕ) (i j : Fin n') :
    higham9_5_rectGEReducedEntry
        (fun p q : Fin n' => A (Fin.cast h p) (Fin.cast h q))
        (fun p q : Fin n' => L (Fin.cast h p) (Fin.cast h q))
        (fun p q : Fin n' => U (Fin.cast h p) (Fin.cast h q))
        step i j =
      higham9_5_rectGEReducedEntry A L U step
        (Fin.cast h i) (Fin.cast h j) := by
  subst n
  rfl

private theorem noPivotReducedHistory_maxEntryNorm_castFin {n n' : ℕ}
    (h : n' = n) (hn : 0 < n) (hn' : 0 < n')
    (A L U : Matrix (Fin n) (Fin n) ℝ) :
    maxEntryNorm hn'
        (higham13_noPivotReducedHistoryGrowthMatrix hn'
          (fun i j : Fin n' => A (Fin.cast h i) (Fin.cast h j))
          (fun i j : Fin n' => L (Fin.cast h i) (Fin.cast h j))
          (fun i j : Fin n' => U (Fin.cast h i) (Fin.cast h j))) =
      maxEntryNorm hn
        (higham13_noPivotReducedHistoryGrowthMatrix hn A L U) := by
  subst n
  rfl

/-- Every entry of the upper factor in a uniform exact block LU certificate
occurs at a block-boundary stage of the scalar equation (9.5) reduced
history.  Thus an independently supplied scalar no-pivot LU certificate for
the same flattened matrix controls the whole block upper factor. -/
theorem higham13_blockUpper_le_noPivotReducedHistory {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A Lb Ub : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (Ls Us : Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
    (hBlock : BlockLUFactSpec m r A Lb Ub)
    (hScalar : LUFactSpec (m * r) (blockMatrixFlatFin A) Ls Us)
    (hdet : Matrix.det (blockMatrixFlatFin A) ≠ 0) :
    blockMaxNorm hm hr Ub ≤
      maxEntryNorm (Nat.mul_pos hm hr)
        (higham13_noPivotReducedHistoryGrowthMatrix
          (Nat.mul_pos hm hr) (blockMatrixFlatFin A) Ls Us) := by
  apply blockMaxNorm_le_of_entry_abs_le
  intro bi bj a b
  by_cases hji : bj.val < bi.val
  · rw [hBlock.U_lower_zero bi bj hji]
    simp [zeroBlock]
    exact maxEntryNorm_nonneg (Nat.mul_pos hm hr)
      (higham13_noPivotReducedHistoryGrowthMatrix
        (Nat.mul_pos hm hr) (blockMatrixFlatFin A) Ls Us)
  · have hibj : bi.val ≤ bj.val := Nat.le_of_not_gt hji
    let cut := r * bi.val
    let tailBlocks := m - bi.val
    let suffix := tailBlocks * r
    have hbi_le : bi.val ≤ m := Nat.le_of_lt bi.isLt
    have hsplit : bi.val + (m - bi.val) = m := Nat.add_sub_of_le hbi_le
    have hdim : cut + suffix = m * r := by
      calc
        cut + suffix = r * bi.val + (m - bi.val) * r := by
          rfl
        _ = bi.val * r + (m - bi.val) * r := by
          rw [Nat.mul_comm r bi.val]
        _ = (bi.val + (m - bi.val)) * r := by
          rw [Nat.add_mul]
        _ = m * r := by rw [hsplit]
    have hTailBlocks : 0 < tailBlocks := by
      simpa [tailBlocks] using Nat.sub_pos_of_lt bi.isLt
    have hSuffix : 0 < suffix := by
      exact Nat.mul_pos hTailBlocks hr
    let Ac : Matrix (Fin (cut + suffix)) (Fin (cut + suffix)) ℝ :=
      fun i j => blockMatrixFlatFin A (Fin.cast hdim i) (Fin.cast hdim j)
    let Lsc : Matrix (Fin (cut + suffix)) (Fin (cut + suffix)) ℝ :=
      fun i j => Ls (Fin.cast hdim i) (Fin.cast hdim j)
    let Usc : Matrix (Fin (cut + suffix)) (Fin (cut + suffix)) ℝ :=
      fun i j => Us (Fin.cast hdim i) (Fin.cast hdim j)
    let Lbc : Matrix (Fin (cut + suffix)) (Fin (cut + suffix)) ℝ :=
      fun i j => blockMatrixFlatFin Lb (Fin.cast hdim i) (Fin.cast hdim j)
    let Ubc : Matrix (Fin (cut + suffix)) (Fin (cut + suffix)) ℝ :=
      fun i j => blockMatrixFlatFin Ub (Fin.cast hdim i) (Fin.cast hdim j)
    have hScalarC : LUFactSpec (cut + suffix) Ac Lsc Usc := by
      simpa [Ac, Lsc, Usc] using LUFactSpec.castFin hdim hScalar
    have hBlockProduct : ∀ i j : Fin (m * r),
        blockMatrixFlatFin A i j =
          ∑ k : Fin (m * r),
            blockMatrixFlatFin Lb i k * blockMatrixFlatFin Ub k j :=
      hBlock.blockMatrixFlatFin_product_eq
    have hBlockProductC : ∀ i j : Fin (cut + suffix),
        Ac i j = ∑ k, Lbc i k * Ubc k j := by
      simpa [Ac, Lbc, Ubc] using factor_product_castFin hdim hBlockProduct
    have hdetC : Matrix.det Ac ≠ 0 := by
      simpa [Ac] using det_castFin_ne_zero hdim hdet
    have hLeadDet : Matrix.det (leadingBlock Ac) ≠ 0 :=
      leadingBlock_det_ne_zero_of_lu_det_ne_zero hScalarC hdetC
    letI : Invertible (Matrix.det (leadingBlock Ac)) :=
      invertibleOfNonzero hLeadDet
    letI : Invertible (leadingBlock Ac) :=
      Matrix.invertibleOfDetInvertible (leadingBlock Ac)
    have hLbc12 : ∀ i : Fin cut, ∀ j : Fin suffix,
        Lbc (leadFin i) (tailFin j) = 0 := by
      intro i j
      apply blockMatrixFlatFin_lower_leading_trailing_zero hr hBlock bi
      · simpa [cut, leadFin] using i.isLt
      · simp [cut, tailFin]
    have hUbc21 : ∀ i : Fin suffix, ∀ j : Fin cut,
        Ubc (tailFin i) (leadFin j) = 0 := by
      intro i j
      apply blockMatrixFlatFin_upper_trailing_leading_zero hr hBlock bi
      · simp [cut, tailFin]
      · simpa [cut, leadFin] using j.isLt
    let firstTail : Fin tailBlocks := ⟨0, hTailBlocks⟩
    have hbjTail : bj.val - bi.val < tailBlocks := by
      simpa [tailBlocks] using Nat.sub_lt_sub_right hibj bj.isLt
    let bjTail : Fin tailBlocks := ⟨bj.val - bi.val, hbjTail⟩
    let ia : Fin suffix := finProdFinEquiv (firstTail, a)
    let ja : Fin suffix := finProdFinEquiv (bjTail, b)
    have hia : Fin.cast hdim (tailFin ia) = finProdFinEquiv (bi, a) := by
      apply Fin.ext
      change cut + (a.val + r * 0) = a.val + r * bi.val
      simp [cut, Nat.add_comm]
    have hmulSplit : r * bi.val + r * (bj.val - bi.val) = r * bj.val := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hibj]
    have hja : Fin.cast hdim (tailFin ja) = finProdFinEquiv (bj, b) := by
      apply Fin.ext
      change cut + (b.val + r * (bj.val - bi.val)) =
        b.val + r * bj.val
      dsimp [cut]
      omega
    have hUnit : ∀ k : Fin suffix,
        Lbc (tailFin ia) (tailFin k) = if k = ia then 1 else 0 := by
      intro k
      have hkBound : r * bi.val ≤ (Fin.cast hdim (tailFin k)).val := by
        change r * bi.val ≤ cut + k.val
        simp [cut]
      have hrow := blockMatrixFlatFin_lower_boundary_unit_row
        hr hBlock bi a (Fin.cast hdim (tailFin k)) hkBound
      rw [← hia] at hrow
      have htail_iff :
          Fin.cast hdim (@tailFin cut suffix k) =
              Fin.cast hdim (@tailFin cut suffix ia) ↔ k = ia := by
        constructor
        · intro h
          apply Fin.ext
          have hval := congrArg Fin.val h
          change cut + k.val = cut + ia.val at hval
          omega
        · rintro rfl
          rfl
      simp only [htail_iff] at hrow
      simpa [Lbc] using hrow
    have hentryC := higham13_factor_upper_entry_eq_noPivotReducedStage
      hScalarC hBlockProductC hLbc12 hUbc21 ia ja hUnit
    have hcastReduced := higham9_5_rectGEReducedEntry_castFin
      hdim (blockMatrixFlatFin A) Ls Us cut (tailFin ia) (tailFin ja)
    have hentry : Ub bi bj a b =
        higham9_5_rectGEReducedEntry (blockMatrixFlatFin A) Ls Us cut
          (finProdFinEquiv (bi, a)) (finProdFinEquiv (bj, b)) := by
      calc
        Ub bi bj a b = Ubc (tailFin ia) (tailFin ja) := by
          simp [Ubc, hia, hja]
        _ = higham9_5_rectGEReducedEntry Ac Lsc Usc cut
              (tailFin ia) (tailFin ja) := hentryC
        _ = higham9_5_rectGEReducedEntry (blockMatrixFlatFin A) Ls Us cut
              (Fin.cast hdim (tailFin ia)) (Fin.cast hdim (tailFin ja)) := by
          simpa [Ac, Lsc, Usc] using hcastReduced
        _ = higham9_5_rectGEReducedEntry (blockMatrixFlatFin A) Ls Us cut
              (finProdFinEquiv (bi, a)) (finProdFinEquiv (bj, b)) := by
          rw [hia, hja]
    rw [hentry]
    have hprefixLt : cut < m * r := by omega
    exact le_trans
      (entry_le_maxEntryNorm (Nat.mul_pos hm hr)
        (fun i j : Fin (m * r) =>
          higham9_5_rectGEReducedEntry (blockMatrixFlatFin A) Ls Us
            cut i j)
        (finProdFinEquiv (bi, a)) (finProdFinEquiv (bj, b)))
      (higham13_noPivotReducedHistoryGrowthMatrix_contains_stage
        (Nat.mul_pos hm hr) (blockMatrixFlatFin A) Ls Us
        (⟨cut, hprefixLt⟩ : Fin (m * r)))

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

/-- Equation (13.23), source-facing block-LU route.  Compared with the local
adapter above, the upper-history hypothesis is discharged from the exact
block factorization itself: after flattening, every block-upper entry is an
actual scalar equation (9.5) reduced-stage entry. -/
theorem higham13_eq13_23_local_block_product_from_pointRow_blockLU_exact_kappa
    {r s mb rb : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hmb : 0 < mb) (hrb : 0 < rb)
    (A L U : Matrix (Fin (r + s)) (Fin (r + s)) ℝ)
    (Ablk Lblk Ublk :
      Fin mb → Fin mb → Matrix (Fin rb) (Fin rb) ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hdim : r + s = mb * rb)
    (hAflat : ∀ i j : Fin (r + s),
      A i j = blockMatrixFlatFin Ablk (Fin.cast hdim i) (Fin.cast hdim j))
    (hBlock : BlockLUFactSpec mb rb Ablk Lblk Ublk)
    (hA11_block : A11 = fun i j => A (leadFin i) (leadFin j))
    (hA12_block : A12 = fun i j => A (leadFin i) (tailFin j))
    (hA21_block : A21 = fun i j => A (tailFin i) (leadFin j))
    (hA22_block : A22 = fun i j => A (tailFin i) (tailFin j))
    (hRow : IsRowDiagDominant (r + s) A)
    (hdet : Matrix.det A ≠ 0)
    (hLU : LUFactSpec (r + s) A L U)
    (n : ℕ) (hsn : (s : ℝ) ≤ (n : ℝ)) :
    maxEntryNormRect hs hr (A21 * ⅟A11) *
        blockMaxNorm hmb hrb Ublk ≤
      8 * (n : ℝ) *
        (maxEntryNormRect (Nat.add_pos_left hr s) (Nat.add_pos_left hr s) A *
          maxEntryNormRect (Nat.add_pos_left hr s) (Nat.add_pos_left hr s)
            (nonsingInv (r + s) A)) *
        maxEntryNormRect (Nat.add_pos_left hr s) (Nat.add_pos_left hr s) A := by
  let Af : Matrix (Fin (mb * rb)) (Fin (mb * rb)) ℝ :=
    fun i j => A (Fin.cast hdim.symm i) (Fin.cast hdim.symm j)
  let Lf : Matrix (Fin (mb * rb)) (Fin (mb * rb)) ℝ :=
    fun i j => L (Fin.cast hdim.symm i) (Fin.cast hdim.symm j)
  let Uf : Matrix (Fin (mb * rb)) (Fin (mb * rb)) ℝ :=
    fun i j => U (Fin.cast hdim.symm i) (Fin.cast hdim.symm j)
  have hAf : Af = blockMatrixFlatFin Ablk := by
    ext i j
    simpa [Af] using hAflat (Fin.cast hdim.symm i) (Fin.cast hdim.symm j)
  have hLUf : LUFactSpec (mb * rb) (blockMatrixFlatFin Ablk) Lf Uf := by
    have hcast := LUFactSpec.castFin hdim.symm hLU
    simpa [Af, Lf, Uf, hAf] using hcast
  have hdetAf : Matrix.det Af ≠ 0 := by
    simpa [Af] using det_castFin_ne_zero hdim.symm hdet
  have hdetFlat : Matrix.det (blockMatrixFlatFin Ablk) ≠ 0 := by
    simpa [hAf] using hdetAf
  have hUflat := higham13_blockUpper_le_noPivotReducedHistory
    hmb hrb Ablk Lblk Ublk Lf Uf hBlock hLUf hdetFlat
  have hHistoryCast := noPivotReducedHistory_maxEntryNorm_castFin
    hdim.symm (Nat.add_pos_left hr s) (Nat.mul_pos hmb hrb) A L U
  have hUhistory :
      blockMaxNorm hmb hrb Ublk ≤
        maxEntryNorm (Nat.add_pos_left hr s)
          (higham13_noPivotReducedHistoryGrowthMatrix
            (Nat.add_pos_left hr s) A L U) := by
    calc
      blockMaxNorm hmb hrb Ublk ≤
          maxEntryNorm (Nat.mul_pos hmb hrb)
            (higham13_noPivotReducedHistoryGrowthMatrix
              (Nat.mul_pos hmb hrb) (blockMatrixFlatFin Ablk) Lf Uf) := hUflat
      _ = maxEntryNorm (Nat.mul_pos hmb hrb)
            (higham13_noPivotReducedHistoryGrowthMatrix
              (Nat.mul_pos hmb hrb) Af Lf Uf) := by rw [hAf]
      _ = maxEntryNorm (Nat.add_pos_left hr s)
            (higham13_noPivotReducedHistoryGrowthMatrix
              (Nat.add_pos_left hr s) A L U) := by
        simpa [Af, Lf, Uf] using hHistoryCast
  exact
    higham13_eq13_23_local_block_product_from_pointRow_noPivotHistory_exact_kappa
      hr hs hmb hrb A L U Ublk A11 A12 A21 A22
      hA11_block hA12_block hA21_block hA22_block hRow hdet hLU n hsn hUhistory

end

end LeanFpAnalysis.FP
