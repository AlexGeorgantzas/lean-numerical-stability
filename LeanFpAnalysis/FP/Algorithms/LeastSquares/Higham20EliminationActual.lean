import LeanFpAnalysis.FP.Algorithms.LeastSquares.Higham20Theorem20_7
import LeanFpAnalysis.FP.Algorithms.LeastSquares.LSE

namespace LeanFpAnalysis.FP

open scoped BigOperators

namespace Higham20EliminationActual

/-!
# Higham, Chapter 20, page 399: constructed elimination method

The constraint matrix in the LSE elimination method is wide:
`B : p × (p+q)`.  The tall least-squares QR trace therefore cannot be reused
at its full column horizon.  This file runs the same executed active-max column
pivot and signed Householder construction for an explicit horizon `s` with
`s ≤ m,n`; the page-399 instance takes `s=m=p`.

This is exact algorithm algebra.  It has no Cox--Higham row-growth, sigma
history, or floating-point residual readiness hypothesis.
-/

/-- Exact active-max, column-pivoted signed-Householder trace through `s`
stages.  After the horizon the state is held fixed. -/
noncomputable def exactPivotedQRMatrixSeq {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ) :
    ℕ → Fin m → Fin n → ℝ
  | 0 => A
  | k + 1 =>
      if hk : k < s then
        let Aprev := exactPivotedQRMatrixSeq hsm hsn A k
        let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
        let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
        let pivot := householderActiveMaxPivotColumn row col Aprev
        let S : Equiv.Perm (Fin n) := Equiv.swap col pivot
        let As := Wave13.columnPermuteMatrix Aprev S
        let x : Fin m → ℝ := fun i => As i col
        let alpha := signedHouseholderAlpha
          (Real.sqrt (householderTrailingNorm2Sq m row x)) (x row)
        let v := householderTrailingActiveVector m row x alpha
        let beta := householderBetaSpec m v
        matMulRect m m n (householder m v beta) As
      else
        exactPivotedQRMatrixSeq hsm hsn A k

/-- Executed active-max column exchange at a generic-horizon exact stage. -/
noncomputable def exactPivotedQRSwapSeq {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Equiv.Perm (Fin n) :=
  if hk : k < s then
    let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
    let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
    Equiv.swap col
      (householderActiveMaxPivotColumn row col
        (exactPivotedQRMatrixSeq hsm hsn A k))
  else
    Equiv.refl _

/-- Panel after the actually executed exact-stage exchange. -/
noncomputable def exactPivotedQRSwappedPanel {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Fin m → Fin n → ℝ :=
  Wave13.columnPermuteMatrix (exactPivotedQRMatrixSeq hsm hsn A k)
    (exactPivotedQRSwapSeq hsm hsn A k)

/-- Raw signed reflector vector actually constructed at exact stage `k`. -/
noncomputable def exactPivotedQRRawVector {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Fin m → ℝ :=
  if hk : k < s then
    let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
    let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
    let As := exactPivotedQRSwappedPanel hsm hsn A k
    let x : Fin m → ℝ := fun i => As i col
    householderTrailingActiveVector m row x
      (signedHouseholderAlpha
        (Real.sqrt (householderTrailingNorm2Sq m row x)) (x row))
  else
    0

/-- Exact beta paired with the constructed raw vector. -/
noncomputable def exactPivotedQRBeta {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : ℝ :=
  householderBetaSpec m (exactPivotedQRRawVector hsm hsn A k)

/-- Exact reflector sequence of the constructed wide/tall prefix trace. -/
noncomputable def exactPivotedQRPseq {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Fin m → Fin m → ℝ :=
  householder m (exactPivotedQRRawVector hsm hsn A k)
    (exactPivotedQRBeta hsm hsn A k)

theorem exactPivotedQRMatrixSeq_succ_of_lt {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < s) :
    exactPivotedQRMatrixSeq hsm hsn A (k + 1) =
      matMulRect m m n (exactPivotedQRPseq hsm hsn A k)
        (exactPivotedQRSwappedPanel hsm hsn A k) := by
  simp [exactPivotedQRMatrixSeq, exactPivotedQRPseq,
    exactPivotedQRRawVector, exactPivotedQRBeta,
    exactPivotedQRSwappedPanel, exactPivotedQRSwapSeq, hk]

theorem exactPivotedQRPseq_orthogonal {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : IsOrthogonal m (exactPivotedQRPseq hsm hsn A k) := by
  exact Theorem20_7.householder_betaSpec_orthogonal m
    (exactPivotedQRRawVector hsm hsn A k)

/-- Executed exact-stage swaps fix all completed column positions. -/
theorem exactPivotedQRSwapSeq_fix_prefix {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (j : Fin n) (hj : j.val < k) :
    exactPivotedQRSwapSeq hsm hsn A k j = j := by
  by_cases hk : k < s
  · let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
    let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
    let pivot := householderActiveMaxPivotColumn row col
      (exactPivotedQRMatrixSeq hsm hsn A k)
    have hjc : j ≠ col := by
      intro h
      subst j
      exact (Nat.lt_irrefl k hj)
    have hpge : k ≤ pivot.val := by
      simpa [pivot, col] using
        householderActiveMaxPivotColumn_ge row col
          (exactPivotedQRMatrixSeq hsm hsn A k)
    have hjp : j ≠ pivot := by
      intro h
      subst j
      omega
    simp only [exactPivotedQRSwapSeq, dif_pos hk]
    exact Equiv.swap_apply_of_ne_of_ne hjc hjp
  · simp [exactPivotedQRSwapSeq, hk]

/-- Executed exact-stage swaps map the active column suffix to itself. -/
theorem exactPivotedQRSwapSeq_maps_active {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (j : Fin n) (hj : k ≤ j.val) :
    k ≤ (exactPivotedQRSwapSeq hsm hsn A k j).val := by
  by_cases hk : k < s
  · let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
    let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
    let pivot := householderActiveMaxPivotColumn row col
      (exactPivotedQRMatrixSeq hsm hsn A k)
    have hpge : k ≤ pivot.val := by
      simpa [pivot, col] using
        householderActiveMaxPivotColumn_ge row col
          (exactPivotedQRMatrixSeq hsm hsn A k)
    simp only [exactPivotedQRSwapSeq, dif_pos hk]
    by_cases hjc : j = col
    · subst j
      rw [Equiv.swap_apply_left]
      exact hpge
    · by_cases hjp : j = pivot
      · subst j
        rw [Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hjc hjp]
        exact hj
  · simp [exactPivotedQRSwapSeq, hk]
    exact hj

/-- With zero local residuals, the swap-aware perturbation accumulator is
identically zero. -/
theorem pivotDAacc_zero {m n : ℕ}
    (Pseq : ℕ → Fin m → Fin m → ℝ)
    (Sseq : ℕ → Equiv.Perm (Fin n)) :
    ∀ r i j,
      Theorem20_7.pivotDAacc Pseq Sseq (fun _ _ _ => 0) r i j = 0 := by
  intro r
  induction r with
  | zero => simp [Theorem20_7.pivotDAacc]
  | succ r ih =>
      intro i j
      simp [Theorem20_7.pivotDAacc, ih, Wave13.columnPermuteMatrix,
        matMulRect]

/-- Exact factorization identity for the constructed prefix trace. -/
theorem exactPivotedQR_telescope {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    exactPivotedQRMatrixSeq hsm hsn A s i j =
      matMulRect m m n
        (matTranspose (Wave19.Qacc (exactPivotedQRPseq hsm hsn A) s))
        (Wave13.columnPermuteMatrix A
          (Theorem20_7.pivotPermAcc (exactPivotedQRSwapSeq hsm hsn A) s)) i j := by
  have h :=
    Theorem20_7.pivoted_entrywise_residual_telescope s
      (exactPivotedQRMatrixSeq hsm hsn A)
      (exactPivotedQRPseq hsm hsn A)
      (exactPivotedQRSwapSeq hsm hsn A)
      (fun _ _ _ => 0)
      (fun k => exactPivotedQRPseq_orthogonal hsm hsn A k)
      (fun k hk i j => by
        rw [exactPivotedQRMatrixSeq_succ_of_lt hsm hsn A k hk]
        simp [exactPivotedQRSwappedPanel]) i j
  simpa [exactPivotedQRMatrixSeq,
    pivotDAacc_zero (exactPivotedQRPseq hsm hsn A)
      (exactPivotedQRSwapSeq hsm hsn A) s] using h

/-- Constructed exact active-max QR factorization, in the source orientation
`A Π = Q R`. -/
theorem exactPivotedQR_factorization {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ) :
    let Q := Wave19.Qacc (exactPivotedQRPseq hsm hsn A) s
    let R := exactPivotedQRMatrixSeq hsm hsn A s
    let pi := Theorem20_7.pivotPermAcc (exactPivotedQRSwapSeq hsm hsn A) s
    IsOrthogonal m Q ∧
      Wave13.columnPermuteMatrix A pi = matMulRect m m n Q R := by
  dsimp only
  let Q := Wave19.Qacc (exactPivotedQRPseq hsm hsn A) s
  let R := exactPivotedQRMatrixSeq hsm hsn A s
  let pi := Theorem20_7.pivotPermAcc (exactPivotedQRSwapSeq hsm hsn A) s
  let Bpi := Wave13.columnPermuteMatrix A pi
  have hQ : IsOrthogonal m Q :=
    Wave19.Qacc_orthogonal (exactPivotedQRPseq hsm hsn A)
      (fun k => exactPivotedQRPseq_orthogonal hsm hsn A k) s
  have hR : R = matMulRect m m n (matTranspose Q) Bpi := by
    funext i j
    simpa [Q, R, pi, Bpi] using exactPivotedQR_telescope hsm hsn A i j
  have hQQT : matMul m Q (matTranspose Q) = idMatrix m :=
    funext fun i => funext fun j => hQ.right_inv i j
  have hfact : matMulRect m m n Q R = Bpi := by
    rw [hR, ← matMulRect_assoc_square_left, hQQT, matMulRect_id_left]
  exact ⟨hQ, hfact.symm⟩

/-- The raw vector of an executed generic-horizon stage has a zero prefix. -/
theorem exactPivotedQRRawVector_zero_prefix {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < s) (i : Fin m) (hi : i.val < k) :
    exactPivotedQRRawVector hsm hsn A k i = 0 := by
  simp only [exactPivotedQRRawVector, dif_pos hk]
  exact householderTrailingActiveVector_zero_prefix m
    ⟨k, lt_of_lt_of_le hk hsm⟩
    (fun r => exactPivotedQRSwappedPanel hsm hsn A k r
      ⟨k, lt_of_lt_of_le hk hsn⟩)
    (signedHouseholderAlpha
      (Real.sqrt
        (householderTrailingNorm2Sq m ⟨k, lt_of_lt_of_le hk hsm⟩
          (fun r => exactPivotedQRSwappedPanel hsm hsn A k r
            ⟨k, lt_of_lt_of_le hk hsn⟩)))
      (exactPivotedQRSwappedPanel hsm hsn A k
        ⟨k, lt_of_lt_of_le hk hsm⟩ ⟨k, lt_of_lt_of_le hk hsn⟩)) i hi

/-- The exact signed reflector annihilates the displayed pivot-column tail.
The zero-trailing-norm branch is handled directly, so this algebraic theorem
has no nonbreakdown hypothesis. -/
theorem exactPivotedQRPseq_pivot_column_zero_below {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < s) (i : Fin m) (hi : k < i.val) :
    matMulVec m (exactPivotedQRPseq hsm hsn A k)
        (fun r => exactPivotedQRSwappedPanel hsm hsn A k r
          ⟨k, lt_of_lt_of_le hk hsn⟩) i = 0 := by
  let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
  let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
  let As := exactPivotedQRSwappedPanel hsm hsn A k
  let x : Fin m → ℝ := fun r => As r col
  let T := householderTrailingNorm2Sq m row x
  let alpha := signedHouseholderAlpha (Real.sqrt T) (x row)
  let v := householderTrailingActiveVector m row x alpha
  have hTnonneg : 0 ≤ T := by
    exact householderTrailingNorm2Sq_nonneg m row x
  by_cases hTpos : 0 < T
  · have halpha : alpha * alpha = T := by
      simpa [alpha, T] using
        signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq m row x
    have hsign : alpha * x row ≤ 0 := by
      simpa [alpha, T] using
        signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos m row x
    have hpivot_ne : x row ≠ alpha :=
      householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos
        m row x alpha halpha hTpos hsign
    have hden : (∑ r : Fin m, v r * v r) ≠ 0 := by
      simpa [v] using
        householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha
          m row x alpha hpivot_ne
    have hzero :=
      matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt
        m row x alpha halpha hden i (by simpa [row] using hi)
    simpa [exactPivotedQRPseq, exactPivotedQRRawVector,
      exactPivotedQRBeta, hk, row, col, As, x, T, alpha, v] using hzero
  · have hTzero : T = 0 := le_antisymm (le_of_not_gt hTpos) hTnonneg
    have hx_active : ∀ r : Fin m, k ≤ r.val → x r = 0 := by
      intro r hr
      by_contra hne
      have hpos := householderTrailingNorm2Sq_pos_of_exists_ne
        m row x ⟨r, by simpa [row] using hr, hne⟩
      change 0 < T at hpos
      linarith
    have hxrow : x row = 0 := hx_active row (by simp [row])
    have halpha : alpha = 0 := by
      simp [alpha, hTzero, hxrow, signedHouseholderAlpha]
    have hvzero : v = 0 := by
      funext r
      by_cases hr : r.val < k
      · simpa [v, row] using
          householderTrailingActiveVector_zero_prefix m row x alpha r
            (by simpa [row] using hr)
      · have hxr : x r = 0 := hx_active r (Nat.le_of_not_gt hr)
        simp [v, householderTrailingActiveVector, householderActiveVector,
          householderTrailingPart, row, hr, hxr, halpha]
    have hxi : x i = 0 := hx_active i (le_of_lt hi)
    have hraw : exactPivotedQRRawVector hsm hsn A k = 0 := by
      simpa [exactPivotedQRRawVector, hk, row, col, As, x, T, alpha, v]
        using hvzero
    have hP : exactPivotedQRPseq hsm hsn A k = idMatrix m := by
      ext a b
      simp [exactPivotedQRPseq, exactPivotedQRBeta, hraw,
        householderBetaSpec, householder]
    rw [hP, matMulVec_id]
    simpa [x, As, col] using hxi

/-- Exact active-max pivoting plus signed Householder application preserves the
completed lower-zero shape through every prefix of the chosen horizon. -/
theorem exactPivotedQRMatrixSeq_prefix_lower_zero {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ) :
    ∀ k, k ≤ s → ∀ (i : Fin m) (j : Fin n),
      j.val < k → j.val < i.val →
        exactPivotedQRMatrixSeq hsm hsn A k i j = 0 := by
  intro k
  induction k with
  | zero =>
      intro _hk i j hj _
      exact (Nat.not_lt_zero j.val hj).elim
  | succ k ih =>
      intro hkSucc i j hjSucc hji
      have hk : k < s := Nat.lt_of_succ_le hkSucc
      have hstepPoint :
          exactPivotedQRMatrixSeq hsm hsn A (k + 1) i j =
            matMulRect m m n (exactPivotedQRPseq hsm hsn A k)
              (exactPivotedQRSwappedPanel hsm hsn A k) i j := by
        exact congrFun (congrFun
          (exactPivotedQRMatrixSeq_succ_of_lt hsm hsn A k hk) i) j
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjSucc with hj | hj
      · let v := exactPivotedQRRawVector hsm hsn A k
        let beta := exactPivotedQRBeta hsm hsn A k
        let As := exactPivotedQRSwappedPanel hsm hsn A k
        let xcol : Fin m → ℝ := fun r => As r j
        have hfix := exactPivotedQRSwapSeq_fix_prefix hsm hsn A k j hj
        have hxcol : xcol = fun r => exactPivotedQRMatrixSeq hsm hsn A k r j := by
          funext r
          simp [xcol, As, exactPivotedQRSwappedPanel,
            Wave13.columnPermuteMatrix, hfix]
        have hvprefix : ∀ r : Fin m, r.val < k → v r = 0 := by
          intro r hr
          exact exactPivotedQRRawVector_zero_prefix hsm hsn A k hk r hr
        have hsupport : ∀ r : Fin m, k ≤ r.val → xcol r = 0 := by
          intro r hr
          rw [hxcol]
          exact ih (Nat.le_of_lt hk) r j hj (lt_of_lt_of_le hj hr)
        have hpres :
            matMulVec m (householder m v beta) xcol = xcol :=
          matMulVec_householder_eq_self_of_zero_prefix_support
            m k v xcol beta hvprefix hsupport
        rw [hstepPoint]
        change matMulVec m (householder m v beta) xcol i = 0
        rw [congrFun hpres i, hxcol]
        exact ih (Nat.le_of_lt hk) i j hj hji
      · let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
        have hjfin : j = col := Fin.ext hj
        subst j
        have hki : k < i.val := by simpa [col] using hji
        rw [hstepPoint]
        change
          matMulVec m (exactPivotedQRPseq hsm hsn A k)
            (fun r => exactPivotedQRSwappedPanel hsm hsn A k r col) i = 0
        exact exactPivotedQRPseq_pivot_column_zero_below
          hsm hsn A k hk i hki

/-- At the full row horizon, the exact wide active-max trace is upper
trapezoidal. -/
theorem exactPivotedQRMatrixSeq_upperTrapezoidal_fullRowHorizon
    {m n : ℕ} (hmn : m ≤ n) (A : Fin m → Fin n → ℝ) :
    IsUpperTrapezoidal m n
      (exactPivotedQRMatrixSeq (s := m) le_rfl hmn A m) := by
  intro i j hji
  exact exactPivotedQRMatrixSeq_prefix_lower_zero
    (s := m) le_rfl hmn A m le_rfl i j
      (lt_trans hji i.isLt) hji

/-- Full row rank is invariant under a column permutation. -/
theorem lseFullRowRank_columnPermuteMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (S : Equiv.Perm (Fin n))
    (hA : LSEFullRowRank A) :
    LSEFullRowRank (Wave13.columnPermuteMatrix A S) := by
  intro y
  obtain ⟨x, hx⟩ := hA y
  refine ⟨vecPermute S x, ?_⟩
  change rectMatMulVec (rectPermuteCols S A) (vecPermute S x) = y
  rw [rectMatMulVec_permuteCols]
  have hx' : rectMatMulVec A x = y := by
    simpa [lseConstraintLinearMap] using hx
  have hperm : vecPermute S.symm (vecPermute S x) = x := by
    funext i
    simp [vecPermute]
  rw [hperm]
  exact hx'

/-- Full row rank is invariant under an orthogonal left factor. -/
theorem lseFullRowRank_orthogonal_left {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hU : IsOrthogonal m U) (hA : LSEFullRowRank A) :
    LSEFullRowRank (matMulRect m m n U A) := by
  intro y
  obtain ⟨x, hx⟩ := hA (matMulVec m (matTranspose U) y)
  refine ⟨x, ?_⟩
  change rectMatMulVec (matMulRectLeft U A) x = y
  have hx' : rectMatMulVec A x = matMulVec m (matTranspose U) y := by
    simpa [lseConstraintLinearMap] using hx
  rw [rectMatMulVec_matMulRectLeft, hx']
  have hUU : matMul m U (matTranspose U) = idMatrix m :=
    funext fun i => funext fun j => hU.right_inv i j
  ext i
  rw [← matMulVec_matMul, hUU, matMulVec_id]

/-- Every exact constructed prefix retains source full row rank. -/
theorem exactPivotedQRMatrixSeq_fullRowRank {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (hA : LSEFullRowRank A) :
    ∀ k, k ≤ s → LSEFullRowRank (exactPivotedQRMatrixSeq hsm hsn A k) := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa [exactPivotedQRMatrixSeq] using hA
  | succ k ih =>
      intro hkSucc
      have hk : k < s := Nat.lt_of_succ_le hkSucc
      have hprev := ih (Nat.le_of_lt hk)
      have hswap : LSEFullRowRank (exactPivotedQRSwappedPanel hsm hsn A k) :=
        lseFullRowRank_columnPermuteMatrix _ _ hprev
      rw [exactPivotedQRMatrixSeq_succ_of_lt hsm hsn A k hk]
      exact lseFullRowRank_orthogonal_left _ _
        (exactPivotedQRPseq_orthogonal hsm hsn A k) hswap

/-- At every unfinished stage of a full-row-rank exact trace, the remaining
active block contains a nonzero entry. -/
theorem exactPivotedQR_exists_active_entry_ne_of_fullRowRank
    {m n s : ℕ} (hsm : s ≤ m) (hsn : s ≤ n)
    (A : Fin m → Fin n → ℝ) (hA : LSEFullRowRank A)
    (k : ℕ) (hk : k < s) :
    ∃ l : Fin n, k ≤ l.val ∧
      ∃ i : Fin m, k ≤ i.val ∧
        exactPivotedQRMatrixSeq hsm hsn A k i l ≠ 0 := by
  let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
  let Ak := exactPivotedQRMatrixSeq hsm hsn A k
  have hfull : LSEFullRowRank Ak :=
    exactPivotedQRMatrixSeq_fullRowRank hsm hsn A hA k (Nat.le_of_lt hk)
  by_contra hno
  have hrowzero : ∀ l : Fin n, Ak row l = 0 := by
    intro l
    by_cases hl : l.val < k
    · exact exactPivotedQRMatrixSeq_prefix_lower_zero hsm hsn A
        k (Nat.le_of_lt hk) row l hl (by simpa [row] using hl)
    · by_contra hne
      exact hno ⟨l, Nat.le_of_not_gt hl, row, by simp [row], hne⟩
  obtain ⟨x, hx⟩ := hfull (fun i : Fin m => idMatrix m i row)
  have hxrow := congrFun hx row
  simp [lseConstraintLinearMap, rectMatMulVec, hrowzero, idMatrix] at hxrow

/-- The actually executed swap places a trailing-norm-maximal active column in
the displayed pivot position. -/
theorem exactPivotedQRSwappedPanel_pivot_max {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < s) :
    ∀ l : Fin n, k ≤ l.val →
      householderTrailingColumnNorm2Sq
          ⟨k, lt_of_lt_of_le hk hsm⟩
          (exactPivotedQRSwappedPanel hsm hsn A k) l ≤
        householderTrailingColumnNorm2Sq
          ⟨k, lt_of_lt_of_le hk hsm⟩
          (exactPivotedQRSwappedPanel hsm hsn A k)
          ⟨k, lt_of_lt_of_le hk hsn⟩ := by
  let Ak := exactPivotedQRMatrixSeq hsm hsn A k
  let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
  let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
  let pivot := householderActiveMaxPivotColumn row col Ak
  have hswap : exactPivotedQRSwappedPanel hsm hsn A k =
      householderSwapColumns Ak col pivot := by
    unfold exactPivotedQRSwappedPanel
    have hS : exactPivotedQRSwapSeq hsm hsn A k = Equiv.swap col pivot := by
      simp [exactPivotedQRSwapSeq, hk, row, col, pivot, Ak]
    rw [hS]
    exact Theorem20_7.columnPermuteMatrix_swap_eq_householderSwapColumns
      Ak col pivot
  rw [hswap]
  exact householderSwapColumns_activeMaxPivotColumn_pivot_max row col Ak

/-- Source full row rank makes every executed active-max pivot norm positive. -/
theorem exactPivotedQR_pivot_trailingNorm_pos_of_fullRowRank
    {m n s : ℕ} (hsm : s ≤ m) (hsn : s ≤ n)
    (A : Fin m → Fin n → ℝ) (hA : LSEFullRowRank A)
    (k : ℕ) (hk : k < s) :
    0 < householderTrailingColumnNorm2Sq
      ⟨k, lt_of_lt_of_le hk hsm⟩
      (exactPivotedQRSwappedPanel hsm hsn A k)
      ⟨k, lt_of_lt_of_le hk hsn⟩ := by
  obtain ⟨l, hl, i, hi, hne⟩ :=
    exactPivotedQR_exists_active_entry_ne_of_fullRowRank
      hsm hsn A hA k hk
  let S := exactPivotedQRSwapSeq hsm hsn A k
  let l' : Fin n := S.symm l
  have hl' : k ≤ l'.val := by
    have hmap := exactPivotedQRSwapSeq_maps_active hsm hsn A k l hl
    have hSinv : S l = S.symm l := by
      simp [S, exactPivotedQRSwapSeq, hk]
    simpa [l', S, hSinv] using hmap
  have hentry : exactPivotedQRSwappedPanel hsm hsn A k i l' ≠ 0 := by
    simpa [exactPivotedQRSwappedPanel, l', S,
      Wave13.columnPermuteMatrix] using hne
  exact
    householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_active_entry_ne
      ⟨k, lt_of_lt_of_le hk hsm⟩
      ⟨k, lt_of_lt_of_le hk hsn⟩
      ⟨k, lt_of_lt_of_le hk hsn⟩
      (exactPivotedQRSwappedPanel hsm hsn A k)
      (exactPivotedQRSwappedPanel_pivot_max hsm hsn A k hk)
      ⟨l', hl', i, by simpa using hi, hentry⟩

/-- Under source full row rank, the diagonal written by the current exact
signed-Householder stage is nonzero. -/
theorem exactPivotedQRMatrixSeq_stage_pivot_ne_zero_of_fullRowRank
    {m n s : ℕ} (hsm : s ≤ m) (hsn : s ≤ n)
    (A : Fin m → Fin n → ℝ) (hA : LSEFullRowRank A)
    (k : ℕ) (hk : k < s) :
    exactPivotedQRMatrixSeq hsm hsn A (k + 1)
      ⟨k, lt_of_lt_of_le hk hsm⟩ ⟨k, lt_of_lt_of_le hk hsn⟩ ≠ 0 := by
  let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
  let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
  let As := exactPivotedQRSwappedPanel hsm hsn A k
  let x : Fin m → ℝ := fun r => As r col
  let T := householderTrailingNorm2Sq m row x
  let alpha := signedHouseholderAlpha (Real.sqrt T) (x row)
  let v := householderTrailingActiveVector m row x alpha
  have hTpos : 0 < T := by
    simpa [T, x, As, row, col, householderTrailingColumnNorm2Sq] using
      exactPivotedQR_pivot_trailingNorm_pos_of_fullRowRank
        hsm hsn A hA k hk
  have halpha : alpha * alpha = T := by
    simpa [alpha, T] using
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq m row x
  have hsign : alpha * x row ≤ 0 := by
    simpa [alpha, T] using
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos m row x
  have hpivot_ne : x row ≠ alpha :=
    householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos
      m row x alpha halpha hTpos hsign
  have hden : (∑ r : Fin m, v r * v r) ≠ 0 := by
    simpa [v] using
      householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha
        m row x alpha hpivot_ne
  have hshape :=
    matMulVec_householder_trailingActiveVector_eq_prefix_alpha_zero
      m row x alpha halpha hden row
  have hentry :
      exactPivotedQRMatrixSeq hsm hsn A (k + 1) row col = alpha := by
    rw [show exactPivotedQRMatrixSeq hsm hsn A (k + 1) =
        matMulRect m m n (exactPivotedQRPseq hsm hsn A k) As from
      exactPivotedQRMatrixSeq_succ_of_lt hsm hsn A k hk]
    change matMulVec m (exactPivotedQRPseq hsm hsn A k) x row = alpha
    simpa [exactPivotedQRPseq, exactPivotedQRRawVector,
      exactPivotedQRBeta, hk, row, col, As, x, T, alpha, v] using hshape
  have halpha_ne : alpha ≠ 0 := by
    intro hzero
    rw [hzero] at halpha
    nlinarith
  simpa [row, col, hentry] using halpha_ne

/-- Once column `j` is completed, every later exact stage preserves it. -/
theorem exactPivotedQRMatrixSeq_completed_column_stable_step
    {m n s : ℕ} (hsm : s ≤ m) (hsn : s ≤ n)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < s)
    (i : Fin m) (j : Fin n) (hj : j.val < k) :
    exactPivotedQRMatrixSeq hsm hsn A (k + 1) i j =
      exactPivotedQRMatrixSeq hsm hsn A k i j := by
  let v := exactPivotedQRRawVector hsm hsn A k
  let beta := exactPivotedQRBeta hsm hsn A k
  let As := exactPivotedQRSwappedPanel hsm hsn A k
  let xcol : Fin m → ℝ := fun r => As r j
  have hfix := exactPivotedQRSwapSeq_fix_prefix hsm hsn A k j hj
  have hxcol : xcol = fun r => exactPivotedQRMatrixSeq hsm hsn A k r j := by
    funext r
    simp [xcol, As, exactPivotedQRSwappedPanel,
      Wave13.columnPermuteMatrix, hfix]
  have hvprefix : ∀ r : Fin m, r.val < k → v r = 0 := by
    intro r hr
    exact exactPivotedQRRawVector_zero_prefix hsm hsn A k hk r hr
  have hsupport : ∀ r : Fin m, k ≤ r.val → xcol r = 0 := by
    intro r hr
    rw [hxcol]
    exact exactPivotedQRMatrixSeq_prefix_lower_zero hsm hsn A
      k (Nat.le_of_lt hk) r j hj (lt_of_lt_of_le hj hr)
  have hpres : matMulVec m (householder m v beta) xcol = xcol :=
    matMulVec_householder_eq_self_of_zero_prefix_support
      m k v xcol beta hvprefix hsupport
  rw [show exactPivotedQRMatrixSeq hsm hsn A (k + 1) =
      matMulRect m m n (exactPivotedQRPseq hsm hsn A k) As from
    exactPivotedQRMatrixSeq_succ_of_lt hsm hsn A k hk]
  change matMulVec m (householder m v beta) xcol i =
    exactPivotedQRMatrixSeq hsm hsn A k i j
  rw [congrFun hpres i, hxcol]

/-- A completed column is unchanged from its completion stage through any
later prefix. -/
theorem exactPivotedQRMatrixSeq_completed_column_stable
    {m n s : ℕ} (hsm : s ≤ m) (hsn : s ≤ n)
    (A : Fin m → Fin n → ℝ) (k t : ℕ) (hk : k < s)
    (hkt : k + 1 ≤ t) (ht : t ≤ s) (i : Fin m) :
    exactPivotedQRMatrixSeq hsm hsn A t i ⟨k, lt_of_lt_of_le hk hsn⟩ =
      exactPivotedQRMatrixSeq hsm hsn A (k + 1) i
        ⟨k, lt_of_lt_of_le hk hsn⟩ := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases htk : t = k
      · subst t
        rfl
      · have hkt' : k + 1 ≤ t := by omega
        have htlt : t < s := Nat.lt_of_succ_le ht
        calc
          exactPivotedQRMatrixSeq hsm hsn A (t + 1) i
              ⟨k, lt_of_lt_of_le hk hsn⟩ =
              exactPivotedQRMatrixSeq hsm hsn A t i
                ⟨k, lt_of_lt_of_le hk hsn⟩ :=
            exactPivotedQRMatrixSeq_completed_column_stable_step
              hsm hsn A t htlt i _ (by simp; omega)
          _ = exactPivotedQRMatrixSeq hsm hsn A (k + 1) i
                ⟨k, lt_of_lt_of_le hk hsn⟩ :=
            ih hkt' (Nat.le_of_lt htlt)

/-- Every leading diagonal entry of the final exact active-max trace is
nonzero under source full row rank. -/
theorem exactPivotedQRMatrixSeq_final_diag_ne_zero_of_fullRowRank
    {m n s : ℕ} (hsm : s ≤ m) (hsn : s ≤ n)
    (A : Fin m → Fin n → ℝ) (hA : LSEFullRowRank A)
    (k : ℕ) (hk : k < s) :
    exactPivotedQRMatrixSeq hsm hsn A s
      ⟨k, lt_of_lt_of_le hk hsm⟩ ⟨k, lt_of_lt_of_le hk hsn⟩ ≠ 0 := by
  rw [exactPivotedQRMatrixSeq_completed_column_stable
    hsm hsn A k s hk (Nat.succ_le_iff.mpr hk) le_rfl]
  exact exactPivotedQRMatrixSeq_stage_pivot_ne_zero_of_fullRowRank
    hsm hsn A hA k hk

/-! ## Page-399 `B`-over-`A` elimination data -/

noncomputable def lseEliminationActualQ {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) : Fin p → Fin p → ℝ :=
  Wave19.Qacc
    (exactPivotedQRPseq (s := p) le_rfl (Nat.le_add_right p q) B) p

noncomputable def lseEliminationActualR {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) : Fin p → Fin (p + q) → ℝ :=
  exactPivotedQRMatrixSeq (s := p) le_rfl (Nat.le_add_right p q) B p

noncomputable def lseEliminationActualPerm {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) : Equiv.Perm (Fin (p + q)) :=
  Theorem20_7.pivotPermAcc
    (exactPivotedQRSwapSeq (s := p) le_rfl (Nat.le_add_right p q) B) p

noncomputable def lseEliminationActualR1 {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) : Fin p → Fin p → ℝ :=
  fun i j => lseEliminationActualR B i (Fin.castAdd q j)

noncomputable def lseEliminationActualR2 {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) : Fin p → Fin q → ℝ :=
  fun i j => lseEliminationActualR B i (Fin.natAdd p j)

noncomputable def lseEliminationActualA1 {m p q : ℕ}
    (A : Fin m → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => Wave13.columnPermuteMatrix A (lseEliminationActualPerm B) i
    (Fin.castAdd q j)

noncomputable def lseEliminationActualA2 {m p q : ℕ}
    (A : Fin m → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) : Fin m → Fin q → ℝ :=
  fun i j => Wave13.columnPermuteMatrix A (lseEliminationActualPerm B) i
    (Fin.natAdd p j)

noncomputable def lseEliminationActualQtd {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) (d : Fin p → ℝ) :
    Fin p → ℝ :=
  matMulVec p (matTranspose (lseEliminationActualQ B)) d

noncomputable def lseEliminationActualR1Inv {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) : Fin p → Fin p → ℝ :=
  nonsingInv p (lseEliminationActualR1 B)

/-- The source back solve `R1 x1 = Qᵀd - R2 x2`, implemented with the
canonical inverse of the constructed nonsingular triangular block. -/
noncomputable def lseEliminationActualX1 {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) (d : Fin p → ℝ)
    (x2 : Fin q → ℝ) : Fin p → ℝ :=
  lseEliminationBackSubstitution (lseEliminationActualR1Inv B)
    (lseEliminationActualR2 B) (lseEliminationActualQtd B d) x2

/-- Original-coordinate vector returned by the exact page-399 elimination
method after the reduced unconstrained solve. -/
noncomputable def lseEliminationActualSolution {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) (d : Fin p → ℝ)
    (x2 : Fin q → ℝ) : Fin (p + q) → ℝ :=
  vecPermute (lseEliminationActualPerm B).symm
    (Fin.append (lseEliminationActualX1 B d x2) x2)

theorem lseEliminationActualR_block {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) :
    lseEliminationBlockMatrix (lseEliminationActualR1 B)
        (lseEliminationActualR2 B) =
      lseEliminationActualR B := by
  funext i j
  refine Fin.addCases ?_ ?_ j
  · intro a
    simp [lseEliminationBlockMatrix, lseEliminationActualR1]
  · intro b
    simp [lseEliminationBlockMatrix, lseEliminationActualR2]

theorem lseEliminationActualA_block {m p q : ℕ}
    (A : Fin m → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) :
    lseEliminationBlockMatrix (lseEliminationActualA1 A B)
        (lseEliminationActualA2 A B) =
      Wave13.columnPermuteMatrix A (lseEliminationActualPerm B) := by
  funext i j
  refine Fin.addCases ?_ ?_ j
  · intro a
    simp [lseEliminationBlockMatrix, lseEliminationActualA1]
  · intro b
    simp [lseEliminationBlockMatrix, lseEliminationActualA2]

/-- The literal wide active-max recursion constructs the page-399 factorization
`B Π = Q [R1 R2]`. -/
theorem lseEliminationActual_pivotedQR {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) :
    IsOrthogonal p (lseEliminationActualQ B) ∧
      rectPermuteCols (lseEliminationActualPerm B) B =
        matMulRect p p (p + q) (lseEliminationActualQ B)
          (lseEliminationBlockMatrix (lseEliminationActualR1 B)
            (lseEliminationActualR2 B)) := by
  have h := exactPivotedQR_factorization
    (s := p) le_rfl (Nat.le_add_right p q) B
  rw [lseEliminationActualR_block B]
  simpa [lseEliminationActualQ, lseEliminationActualR,
    lseEliminationActualPerm, rectPermuteCols,
    Wave13.columnPermuteMatrix] using h

theorem lseEliminationActualR1_upper {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) :
    ∀ i j : Fin p, j.val < i.val → lseEliminationActualR1 B i j = 0 := by
  intro i j hji
  exact exactPivotedQRMatrixSeq_upperTrapezoidal_fullRowHorizon
    (Nat.le_add_right p q) B i (Fin.castAdd q j) (by simpa using hji)

theorem lseEliminationActualR1_diag_ne_zero_of_fullRowRank {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) (hB : LSEFullRowRank B) :
    ∀ i : Fin p, lseEliminationActualR1 B i i ≠ 0 := by
  intro i
  simpa [lseEliminationActualR1, lseEliminationActualR] using
    exactPivotedQRMatrixSeq_final_diag_ne_zero_of_fullRowRank
      (s := p) le_rfl (Nat.le_add_right p q) B hB i.val i.isLt

/-- Column pivoting plus source full row rank makes the constructed triangular
leading block `R1` nonsingular, rather than postulating an inverse factor. -/
theorem lseEliminationActualR1_det_ne_zero_of_fullRowRank {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) (hB : LSEFullRowRank B) :
    Matrix.det (lseEliminationActualR1 B : Matrix (Fin p) (Fin p) ℝ) ≠ 0 :=
  det_ne_zero_of_upper_triangular_diag_ne_zero p
    (lseEliminationActualR1 B) (lseEliminationActualR1_upper B)
    (lseEliminationActualR1_diag_ne_zero_of_fullRowRank B hB)

/-- The canonical inverse of the constructed `R1` acts in both orders. -/
theorem lseEliminationActualR1_inverse_actions_of_fullRowRank {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) (hB : LSEFullRowRank B) :
    (∀ v : Fin p → ℝ,
      rectMatMulVec (lseEliminationActualR1 B)
          (rectMatMulVec (lseEliminationActualR1Inv B) v) = v) ∧
    (∀ v : Fin p → ℝ,
      rectMatMulVec (lseEliminationActualR1Inv B)
          (rectMatMulVec (lseEliminationActualR1 B) v) = v) := by
  have hInv := isInverse_nonsingInv_of_det_ne_zero p
    (lseEliminationActualR1 B)
    (lseEliminationActualR1_det_ne_zero_of_fullRowRank B hB)
  constructor
  · intro v
    have hmul : matMul p (lseEliminationActualR1 B)
        (lseEliminationActualR1Inv B) = idMatrix p :=
      funext fun i => funext fun j => hInv.2 i j
    ext i
    change matMulVec p (lseEliminationActualR1 B)
      (matMulVec p (lseEliminationActualR1Inv B) v) i = v i
    rw [← matMulVec_matMul, hmul, matMulVec_id]
  · intro v
    have hmul : matMul p (lseEliminationActualR1Inv B)
        (lseEliminationActualR1 B) = idMatrix p :=
      funext fun i => funext fun j => hInv.1 i j
    ext i
    change matMulVec p (lseEliminationActualR1Inv B)
      (matMulVec p (lseEliminationActualR1 B) v) i = v i
    rw [← matMulVec_matMul, hmul, matMulVec_id]

/-- The constructed `x1` back solve satisfies the transformed page-399
constraint `R1 x1 + R2 x2 = Qᵀd`. -/
theorem lseEliminationActual_backsolve_constraint_of_fullRowRank {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ) (d : Fin p → ℝ)
    (hB : LSEFullRowRank B) (x2 : Fin q → ℝ) :
    rectMatMulVec
        (lseEliminationBlockMatrix (lseEliminationActualR1 B)
          (lseEliminationActualR2 B))
        (Fin.append (lseEliminationActualX1 B d x2) x2) =
      lseEliminationActualQtd B d := by
  exact lseEliminationBlockConstraint_eq_qtd_of_left_inverse
    (lseEliminationActualR1 B) (lseEliminationActualR1Inv B)
    (lseEliminationActualR2 B) (lseEliminationActualQtd B d) x2
    (lseEliminationActualR1_inverse_actions_of_fullRowRank B hB).1

/-- An orthogonal row factor in the constraint matrix changes only the
constraint coordinates, not the feasible set. -/
theorem isLSEMinimizer_of_orthogonal_constraint_factor
    {m p n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B R : Fin p → Fin n → ℝ) (d qtd : Fin p → ℝ)
    (Q : Fin p → Fin p → ℝ) (x : Fin n → ℝ)
    (hQ : IsOrthogonal p Q)
    (hB : B = matMulRect p p n Q R)
    (hqtd : qtd = matMulVec p (matTranspose Q) d)
    (hmin : IsLSEMinimizer A b R qtd x) :
    IsLSEMinimizer A b B d x := by
  have hQQT : matMul p Q (matTranspose Q) = idMatrix p :=
    funext fun i => funext fun j => hQ.right_inv i j
  have hQTQ : matMul p (matTranspose Q) Q = idMatrix p :=
    funext fun i => funext fun j => hQ.left_inv i j
  refine ⟨?_, ?_⟩
  · have hRx : rectMatMulVec R x = qtd := funext hmin.1
    have hBx : rectMatMulVec B x = matMulVec p Q (rectMatMulVec R x) := by
      rw [hB]
      exact rectMatMulVec_matMulRectLeft Q R x
    intro i
    rw [congrFun hBx i, hRx, hqtd]
    rw [← matMulVec_matMul, hQQT, matMulVec_id]
  · intro y hy
    apply hmin.2 y
    have hyB : rectMatMulVec B y = d := funext hy
    have hQRY : matMulVec p Q (rectMatMulVec R y) = d := by
      have hB' : B = matMulRectLeft Q R := hB
      rw [← rectMatMulVec_matMulRectLeft, ← hB']
      exact hyB
    have hleft := congrArg (matMulVec p (matTranspose Q)) hQRY
    have hRy : rectMatMulVec R y = matMulVec p (matTranspose Q) d := by
      calc
        rectMatMulVec R y = matMulVec p (idMatrix p) (rectMatMulVec R y) := by
          rw [matMulVec_id]
        _ = matMulVec p (matMul p (matTranspose Q) Q)
            (rectMatMulVec R y) := by rw [hQTQ]
        _ = matMulVec p (matTranspose Q)
            (matMulVec p Q (rectMatMulVec R y)) := by
          ext i
          exact matMulVec_matMul p (matTranspose Q) Q
            (rectMatMulVec R y) i
        _ = matMulVec p (matTranspose Q) d := hleft
    intro i
    rw [congrFun hRy i, hqtd]

/-- Higham page 399, constructed exact elimination method.

For source-full-row-rank `B`, the theorem executes active-max pivoted QR of the
wide constraint matrix, proves the leading triangular block nonsingular,
performs the `x1` back solve with its derived inverse, and lifts any correct
solution of the displayed reduced unconstrained least-squares problem to an
exact minimizer of the original LSE problem.  No floating-point row-growth,
sigma-history, or residual-budget readiness field occurs. -/
theorem lseEliminationActual_isLSEMinimizer_of_reduced_minimizer
    {m p q : ℕ}
    (A : Fin m → Fin (p + q) → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) (d : Fin p → ℝ)
    (hB : LSEFullRowRank B) (x2 : Fin q → ℝ)
    (hmin : IsLSEEliminationReducedMinimizer
      (lseEliminationActualA1 A B) (lseEliminationActualA2 A B)
      (lseEliminationActualR1Inv B) (lseEliminationActualR2 B)
      (lseEliminationActualQtd B d) b x2) :
    IsLSEMinimizer A b B d (lseEliminationActualSolution B d x2) := by
  let pi := lseEliminationActualPerm B
  let Q := lseEliminationActualQ B
  let R := lseEliminationActualR B
  let R1 := lseEliminationActualR1 B
  let R1inv := lseEliminationActualR1Inv B
  let R2 := lseEliminationActualR2 B
  let A1 := lseEliminationActualA1 A B
  let A2 := lseEliminationActualA2 A B
  let qtd := lseEliminationActualQtd B d
  let x1 := lseEliminationActualX1 B d x2
  let z := Fin.append x1 x2
  have hQR := lseEliminationActual_pivotedQR B
  have hInv := lseEliminationActualR1_inverse_actions_of_fullRowRank B hB
  have hblock : IsLSEMinimizer
      (lseEliminationBlockMatrix A1 A2) b
      (lseEliminationBlockMatrix R1 R2) qtd z := by
    simpa [A1, A2, R1, R1inv, R2, qtd, x1, z,
      lseEliminationActualX1] using
      lseElimination_isLSEMinimizer_of_reduced_minimizer
        A1 A2 R1 R1inv R2 qtd b x2 hInv.1 hInv.2 hmin
  have hpermutedR : IsLSEMinimizer
      (Wave13.columnPermuteMatrix A pi) b R qtd z := by
    simpa [A1, A2, R1, R2, pi, R, qtd, z,
      lseEliminationActualA_block A B,
      lseEliminationActualR_block B] using hblock
  have hfact : rectPermuteCols pi B = matMulRect p p (p + q) Q R := by
    simpa [pi, Q, R, lseEliminationActualR_block B] using hQR.2
  have hpermuted : IsLSEMinimizer
      (rectPermuteCols pi A) b (rectPermuteCols pi B) d z := by
    apply isLSEMinimizer_of_orthogonal_constraint_factor
      (rectPermuteCols pi A) b (rectPermuteCols pi B) R d qtd Q z
      (by simpa [Q] using hQR.1) hfact
      (by rfl)
    simpa [rectPermuteCols, Wave13.columnPermuteMatrix] using hpermutedR
  have horiginal := IsLSEMinimizer.of_permuteCols pi hpermuted
  simpa [lseEliminationActualSolution, pi, z, x1] using horiginal

end Higham20EliminationActual

end LeanFpAnalysis.FP
