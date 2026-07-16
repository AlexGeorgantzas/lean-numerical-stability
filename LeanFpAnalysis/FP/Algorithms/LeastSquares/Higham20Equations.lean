-- Higham20Equations.lean
--
-- Finite, source-facing versions of Higham, 2nd ed., equations
-- (20.13a), (20.13b), and (20.16).

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Algorithms.LeastSquares.LSNormalEquations
import LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve
import LeanFpAnalysis.FP.Algorithms.HighamChapter12

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-! ## The explicit remainder replacing `O(u^2)` -/

/-- The exact quadratic-and-higher part of `gamma fp k`.

This is a rational expression, not asymptotic notation.  Under
`gammaValid fp k`, `gamma fp k = k*u + higham20GammaRemainder fp k`. -/
noncomputable def higham20GammaRemainder (fp : FPModel) (k : ℕ) : ℝ :=
  (((k : ℝ) * fp.u) ^ 2) / (1 - (k : ℝ) * fp.u)

theorem higham20_gamma_eq_linear_add_remainder (fp : FPModel) (k : ℕ)
    (hk : gammaValid fp k) :
    gamma fp k = (k : ℝ) * fp.u + higham20GammaRemainder fp k := by
  simpa [higham20GammaRemainder] using
    gamma_eq_linear_plus_quadratic_remainder fp k hk

/-- The printed first-order coefficient in (20.13a). -/
noncomputable def higham20Eq20_13aLeading
    (fp : FPModel) (m n : ℕ) (A_norm : ℝ) : ℝ :=
  ((m : ℝ) * (n : ℝ) + 3 * (n : ℝ) ^ 2 + (n : ℝ)) * fp.u * A_norm ^ 2

/-- The complete finite remainder accompanying (20.13a).

It is exactly the two gamma remainders arising from
`n*gamma_m + n*gamma_(3n+1)`; no term is hidden in `O(u^2)`. -/
noncomputable def higham20Eq20_13aRemainder
    (fp : FPModel) (m n : ℕ) (A_norm : ℝ) : ℝ :=
  ((n : ℝ) * higham20GammaRemainder fp m +
      (n : ℝ) * higham20GammaRemainder fp (3 * n + 1)) * A_norm ^ 2

/-- The printed first-order coefficient in (20.13b). -/
noncomputable def higham20Eq20_13bLeading
    (fp : FPModel) (m n : ℕ) (A_norm b_norm : ℝ) : ℝ :=
  (m : ℝ) * Real.sqrt (n : ℝ) * fp.u * A_norm * b_norm

/-- The complete finite remainder accompanying (20.13b). -/
noncomputable def higham20Eq20_13bRemainder
    (fp : FPModel) (m n : ℕ) (A_norm b_norm : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * higham20GammaRemainder fp m * A_norm * b_norm

/-- Scalar bridge behind equation (20.13a): the exact finite gamma coefficient
has the printed first-order coefficient
`(m*n + 3*n^2 + n)u`, followed by the displayed rational remainder. -/
theorem higham20_eq20_13a_gamma_coefficient_exact
    (fp : FPModel) (m n : ℕ) (A_norm : ℝ)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1)) :
    ((n : ℝ) * gamma fp m + (n : ℝ) * gamma fp (3 * n + 1)) * A_norm ^ 2 =
      higham20Eq20_13aLeading fp m n A_norm +
        higham20Eq20_13aRemainder fp m n A_norm := by
  rw [higham20_gamma_eq_linear_add_remainder fp m hm,
    higham20_gamma_eq_linear_add_remainder fp (3 * n + 1) h3n1]
  simp only [higham20Eq20_13aLeading, higham20Eq20_13aRemainder,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Scalar bridge behind equation (20.13b): the exact finite coefficient
`sqrt(n)*gamma_m` has printed first-order part `m*sqrt(n)*u`, followed by
the displayed rational remainder. -/
theorem higham20_eq20_13b_gamma_coefficient_exact
    (fp : FPModel) (m n : ℕ) (A_norm b_norm : ℝ)
    (hm : gammaValid fp m) :
    Real.sqrt (n : ℝ) * gamma fp m * A_norm * b_norm =
      higham20Eq20_13bLeading fp m n A_norm b_norm +
        higham20Eq20_13bRemainder fp m n A_norm b_norm := by
  rw [higham20_gamma_eq_linear_add_remainder fp m hm]
  simp only [higham20Eq20_13bLeading, higham20Eq20_13bRemainder]
  ring

/-! ## Equations (20.13a) and (20.13b) from the normal-equations analysis -/

/-- Absorb the expanded Cholesky-solve coefficient used by
`ls_normal_equations_backward` into `gamma_(3n+1)`. -/
private theorem higham20_cholesky_coefficient_le_gamma_3n1
    (fp : FPModel) (n : ℕ) (h3n1 : gammaValid fp (3 * n + 1)) :
    gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2 ≤
      gamma fp (3 * n + 1) := by
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega) h3n1
  have hstep1 :
      gamma fp n + gamma fp n + gamma fp n * gamma fp n ≤
        gamma fp (2 * n) := by
    have h := gamma_sum_le fp n n (gammaValid_mono fp (by omega) h3n1)
    simpa [show n + n = 2 * n by omega] using h
  have hstep2 : gamma fp (n + 1) + gamma fp (2 * n) ≤
      gamma fp (3 * n + 1) := by
    have heq : (n + 1) + 2 * n = 3 * n + 1 := by omega
    have h := gamma_sum_le fp (n + 1) (2 * n) (heq ▸ h3n1)
    have hnn1 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
    have hnn2 : 0 ≤ gamma fp (2 * n) :=
      gamma_nonneg fp (gammaValid_mono fp (by omega) h3n1)
    rw [heq] at h
    linarith [mul_nonneg hnn1 hnn2]
  nlinarith [hstep1, hstep2]

/-- Equations (20.13a)-(20.13b), as a finite theorem built on the concrete
normal-equations backward-error result.

The two norm-envelope hypotheses are the norm estimates used in Higham's
passage from the componentwise bound (20.12) to (20.13):

* `absATA` and `|Rhat^T||Rhat|` each have Frobenius norm at most
  `n * ||A||_2^2`;
* `absATb` has Euclidean norm at most `sqrt(n) * ||A||_2 * ||b||_2`.

They are kept explicit because their validity depends on how the supplied
majorants and the computed Cholesky factor are related to the source data.
The conclusions contain the source's leading coefficients and the exact
rational higher-order remainders, rather than an unspecified `O(u^2)` term. -/
theorem higham20_eq20_13a_b_normal_equations_finite
    (fp : FPModel) (m n : ℕ)
    (ATA : Fin n → Fin n → ℝ) (ATb : Fin n → ℝ)
    (absATA : Fin n → Fin n → ℝ) (absATb : Fin n → ℝ)
    (C_hat : Fin n → Fin n → ℝ) (c_hat : Fin n → ℝ)
    (R_hat : Fin n → Fin n → ℝ)
    (A_norm b_norm : ℝ)
    (habsATA_nonneg : ∀ i j, 0 ≤ absATA i j)
    (hGram : GramProductError n C_hat ATA absATA (gamma fp m))
    (hGramVec : GramVecError n c_hat ATb absATb (gamma fp m))
    (hChol : CholeskyBackwardError n C_hat R_hat (gamma fp (n + 1)))
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1))
    (habsATA_norm :
      frobNormRect absATA ≤ (n : ℝ) * A_norm ^ 2)
    (hRgram_norm :
      frobNormRect
          (fun i j : Fin n => ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ≤
        (n : ℝ) * A_norm ^ 2)
    (habsATb_norm :
      vecNorm2 absATb ≤ Real.sqrt (n : ℝ) * A_norm * b_norm) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT c_hat
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ (DeltaA : Fin n → Fin n → ℝ) (Deltac : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, (ATA i j + DeltaA i j) * x_hat j =
        ATb i + Deltac i) ∧
      complexMatrixOp2 (realRectToCMatrix DeltaA) ≤
        higham20Eq20_13aLeading fp m n A_norm +
          higham20Eq20_13aRemainder fp m n A_norm ∧
      vecNorm2 Deltac ≤
        higham20Eq20_13bLeading fp m n A_norm b_norm +
          higham20Eq20_13bRemainder fp m n A_norm b_norm := by
  dsimp
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega) h3n1
  obtain ⟨DeltaA, Deltac, hEq, hDeltaA, hDeltac⟩ :=
    ls_normal_equations_backward fp n ATA ATb absATA absATb C_hat c_hat
      R_hat hGram hGramVec hChol hR_diag hm hn1
  refine ⟨DeltaA, Deltac, hEq, ?_, ?_⟩
  · let Rgram : Fin n → Fin n → ℝ :=
      fun i j => ∑ k : Fin n, |R_hat k i| * |R_hat k j|
    let majorant : Fin n → Fin n → ℝ :=
      fun i j => gamma fp m * absATA i j + gamma fp (3 * n + 1) * Rgram i j
    have hgm : 0 ≤ gamma fp m := gamma_nonneg fp hm
    have hg3 : 0 ≤ gamma fp (3 * n + 1) := gamma_nonneg fp h3n1
    have hcholCoeff := higham20_cholesky_coefficient_le_gamma_3n1 fp n h3n1
    have hRgram_nonneg : ∀ i j, 0 ≤ Rgram i j := by
      intro i j
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hmajorant_nonneg : ∀ i j, 0 ≤ majorant i j := by
      intro i j
      exact add_nonneg (mul_nonneg hgm (habsATA_nonneg i j))
        (mul_nonneg hg3 (hRgram_nonneg i j))
    have hDeltaA_majorant : ∀ i j, |DeltaA i j| ≤ majorant i j := by
      intro i j
      calc
        |DeltaA i j| ≤
            gamma fp m * absATA i j +
              (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
                Rgram i j := hDeltaA i j
        _ ≤ gamma fp m * absATA i j + gamma fp (3 * n + 1) * Rgram i j := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right hcholCoeff (hRgram_nonneg i j)) _
        _ = majorant i j := rfl
    have hDeltaA_frob :
        frobNormRect DeltaA ≤
          ((n : ℝ) * gamma fp m + (n : ℝ) * gamma fp (3 * n + 1)) *
            A_norm ^ 2 := by
      calc
        frobNormRect DeltaA ≤ frobNormRect majorant :=
          frobNormRect_le_of_entry_abs_le DeltaA majorant hmajorant_nonneg
            hDeltaA_majorant
        _ ≤ frobNormRect (fun i j => gamma fp m * absATA i j) +
              frobNormRect (fun i j => gamma fp (3 * n + 1) * Rgram i j) := by
          exact frobNormRect_add_le _ _
        _ = gamma fp m * frobNormRect absATA +
              gamma fp (3 * n + 1) * frobNormRect Rgram := by
          rw [frobNormRect_smul, frobNormRect_smul,
            abs_of_nonneg hgm, abs_of_nonneg hg3]
        _ ≤ gamma fp m * ((n : ℝ) * A_norm ^ 2) +
              gamma fp (3 * n + 1) * ((n : ℝ) * A_norm ^ 2) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left habsATA_norm hgm)
            (mul_le_mul_of_nonneg_left hRgram_norm hg3)
        _ = ((n : ℝ) * gamma fp m + (n : ℝ) * gamma fp (3 * n + 1)) *
              A_norm ^ 2 := by ring
    have hfinite_nonneg :
        0 ≤ ((n : ℝ) * gamma fp m + (n : ℝ) * gamma fp (3 * n + 1)) *
          A_norm ^ 2 := by positivity
    have hop :
        complexMatrixOp2 (realRectToCMatrix DeltaA) ≤
          ((n : ℝ) * gamma fp m + (n : ℝ) * gamma fp (3 * n + 1)) *
            A_norm ^ 2 :=
      complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le DeltaA
        hfinite_nonneg (rectOpNorm2Le_of_frobNormRect_le DeltaA hDeltaA_frob)
    rw [higham20_eq20_13a_gamma_coefficient_exact fp m n A_norm hm h3n1] at hop
    exact hop
  · have hgm : 0 ≤ gamma fp m := gamma_nonneg fp hm
    have hnormDeltac : vecNorm2 Deltac ≤ gamma fp m * vecNorm2 absATb := by
      calc
        vecNorm2 Deltac ≤ vecNorm2 (fun i => gamma fp m * absATb i) :=
          vecNorm2_le_of_abs_le Deltac (fun i => gamma fp m * absATb i) hDeltac
        _ = gamma fp m * vecNorm2 absATb := by
          rw [vecNorm2_smul, abs_of_nonneg hgm]
    have hfinite :
        vecNorm2 Deltac ≤
          Real.sqrt (n : ℝ) * gamma fp m * A_norm * b_norm := by
      calc
        vecNorm2 Deltac ≤ gamma fp m * vecNorm2 absATb := hnormDeltac
        _ ≤ gamma fp m * (Real.sqrt (n : ℝ) * A_norm * b_norm) :=
          mul_le_mul_of_nonneg_left habsATb_norm hgm
        _ = Real.sqrt (n : ℝ) * gamma fp m * A_norm * b_norm := by ring
    rw [higham20_eq20_13b_gamma_coefficient_exact fp m n A_norm b_norm hm] at hfinite
    exact hfinite

/-- Source-norm specialization of equations (20.13a)-(20.13b).

Unlike the reusable envelope theorem above, this surface writes the two
scales literally as `||A||_2 = complexMatrixOp2 (realRectToCMatrix A)` and
`||b||_2 = vecNorm2 b`, matching the printed equations. -/
theorem higham20_eq20_13a_b_normal_equations_source_norms_finite
    (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (ATA : Fin n → Fin n → ℝ) (ATb : Fin n → ℝ)
    (absATA : Fin n → Fin n → ℝ) (absATb : Fin n → ℝ)
    (C_hat : Fin n → Fin n → ℝ) (c_hat : Fin n → ℝ)
    (R_hat : Fin n → Fin n → ℝ)
    (habsATA_nonneg : ∀ i j, 0 ≤ absATA i j)
    (hGram : GramProductError n C_hat ATA absATA (gamma fp m))
    (hGramVec : GramVecError n c_hat ATb absATb (gamma fp m))
    (hChol : CholeskyBackwardError n C_hat R_hat (gamma fp (n + 1)))
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1))
    (habsATA_norm :
      frobNormRect absATA ≤
        (n : ℝ) * complexMatrixOp2 (realRectToCMatrix A) ^ 2)
    (hRgram_norm :
      frobNormRect
          (fun i j : Fin n => ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ≤
        (n : ℝ) * complexMatrixOp2 (realRectToCMatrix A) ^ 2)
    (habsATb_norm :
      vecNorm2 absATb ≤ Real.sqrt (n : ℝ) *
        complexMatrixOp2 (realRectToCMatrix A) * vecNorm2 b) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT c_hat
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ (DeltaA : Fin n → Fin n → ℝ) (Deltac : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, (ATA i j + DeltaA i j) * x_hat j =
        ATb i + Deltac i) ∧
      complexMatrixOp2 (realRectToCMatrix DeltaA) ≤
        higham20Eq20_13aLeading fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) +
          higham20Eq20_13aRemainder fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) ∧
      vecNorm2 Deltac ≤
        higham20Eq20_13bLeading fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) (vecNorm2 b) +
          higham20Eq20_13bRemainder fp m n
            (complexMatrixOp2 (realRectToCMatrix A)) (vecNorm2 b) := by
  exact higham20_eq20_13a_b_normal_equations_finite fp m n ATA ATb
    absATA absATb C_hat c_hat R_hat
    (complexMatrixOp2 (realRectToCMatrix A)) (vecNorm2 b)
    habsATA_nonneg hGram hGramVec hChol hR_diag hm h3n1
    habsATA_norm hRgram_norm habsATb_norm

/-! ## Equation (20.16): one refinement step on the augmented system -/

/-- The source coefficient matrix in (20.16), literally
`[[I_m, A], [A^T, 0]]`, with total dimension `m+n`. -/
noncomputable def higham20Eq20_16Matrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin (m + n) → Fin (m + n) → ℝ :=
  Fin.append
    (fun i : Fin m => Fin.append (fun j : Fin m => idMatrix m i j) (A i))
    (fun j : Fin n => Fin.append (fun i : Fin m => A i j) (fun _ : Fin n => 0))

theorem higham20Eq20_16Matrix_eq_lsScaledAugmentedMatrix_one {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    higham20Eq20_16Matrix A = lsScaledAugmentedMatrix 1 A := by
  ext i j
  refine Fin.addCases (motive := fun i : Fin (m + n) =>
    higham20Eq20_16Matrix A i j = lsScaledAugmentedMatrix 1 A i j) ?_ ?_ i
  · intro i
    refine Fin.addCases (motive := fun j : Fin (m + n) =>
      higham20Eq20_16Matrix A (Fin.castAdd n i) j =
        lsScaledAugmentedMatrix 1 A (Fin.castAdd n i) j) ?_ ?_ j
    · intro j
      simp [higham20Eq20_16Matrix, lsScaledAugmentedMatrix,
        Fin.append_left]
    · intro j
      simp [higham20Eq20_16Matrix, lsScaledAugmentedMatrix,
        Fin.append_left, Fin.append_right]
  · intro i
    refine Fin.addCases (motive := fun j : Fin (m + n) =>
      higham20Eq20_16Matrix A (Fin.natAdd m i) j =
        lsScaledAugmentedMatrix 1 A (Fin.natAdd m i) j) ?_ ?_ j
    · intro j
      simp [higham20Eq20_16Matrix, lsScaledAugmentedMatrix,
        Fin.append_left, Fin.append_right]
    · intro j
      simp [higham20Eq20_16Matrix, lsScaledAugmentedMatrix,
        Fin.append_right]

/-- The exact higher-order remainder in the finite form of (20.16).

The first term comes from the `m*n*gamma_m` augmented solver defect.  The
second comes from conventional residual computation in dimension `m+n`, whose
accumulator is `gamma_(m+n+1)`. -/
noncomputable def higham20Eq20_16Remainder {m n : ℕ}
    (fp : FPModel) (A : Fin m → Fin n → ℝ)
    (H : Fin (m + n) → Fin (m + n) → ℝ)
    (rhs oldResidual z : Fin (m + n) → ℝ) (p : Fin (m + n)) : ℝ :=
  ((m : ℝ) * (n : ℝ)) * higham20GammaRemainder fp m *
      (∑ q : Fin (m + n), H p q * |oldResidual q|) +
    higham20GammaRemainder fp (m + n + 1) *
      (|rhs p| + ∑ q : Fin (m + n),
        |higham20Eq20_16Matrix A p q| * |z q|)

/-- Higham equation (20.16), with every higher-order term displayed.

This is an adapter of the exact Chapter 12 one-step residual theorem to the
least-squares augmented matrix `[[I,A],[A^T,0]]`.  The primitive hypotheses are
the correction-solve defect, conventional residual-computation error, and
rounded-update error; the desired post-refinement residual inequality is not
assumed.

`H` is the nonnegative solver majorant supplied by the augmented-system solve
analysis (Theorem 20.4).  Expanding the two gammas gives a first-order term in
`u` plus `higham20Eq20_16Remainder`, an explicit rational replacement for the
book's `O(u^2)`. -/
theorem higham20_eq20_16_augmented_one_refinement_finite
    (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (H : Fin (m + n) → Fin (m + n) → ℝ)
    (z d oldResidual computedResidual updateError y rhs :
      Fin (m + n) → ℝ)
    (hm : gammaValid fp m)
    (hdim : gammaValid fp (m + n + 1))
    (holdResidual : ∀ p : Fin (m + n),
      oldResidual p = rhs p -
        ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * z q)
    (hy : ∀ p : Fin (m + n),
      y p = z p + d p + updateError p)
    (hsolveDefect : ∀ p : Fin (m + n),
      |computedResidual p -
          ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * d q| ≤
        ((m : ℝ) * (n : ℝ)) * gamma fp m *
          ∑ q : Fin (m + n), H p q * |oldResidual q|)
    (hresidualComputation : ∀ p : Fin (m + n),
      |computedResidual p - oldResidual p| ≤
        gamma fp (m + n + 1) *
          (|rhs p| + ∑ q : Fin (m + n),
            |higham20Eq20_16Matrix A p q| * |z q|))
    (hupdate : ∀ q : Fin (m + n),
      |updateError q| ≤ fp.u * (|z q| + |d q|)) :
    ∀ p : Fin (m + n),
      |rhs p - ∑ q : Fin (m + n),
          higham20Eq20_16Matrix A p q * y q| ≤
        fp.u *
          (((m : ℝ) * (n : ℝ) * (m : ℝ)) *
              (∑ q : Fin (m + n), H p q * |oldResidual q|) +
            ((m + n + 1 : ℕ) : ℝ) *
              (|rhs p| + ∑ q : Fin (m + n),
                |higham20Eq20_16Matrix A p q| * |z q|) +
            ∑ q : Fin (m + n),
              |higham20Eq20_16Matrix A p q| * (|z q| + |d q|)) +
          higham20Eq20_16Remainder fp A H rhs oldResidual z p := by
  intro p
  have hbase := higham12_14_residual_bound (m + n)
    (higham20Eq20_16Matrix A) z d rhs oldResidual computedResidual
    updateError y holdResidual hy p
  have hupdateSum :
      (∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * |updateError q|) ≤
        fp.u * ∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * (|z q| + |d q|) := by
    calc
      (∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * |updateError q|) ≤
          ∑ q : Fin (m + n),
            |higham20Eq20_16Matrix A p q| *
              (fp.u * (|z q| + |d q|)) := by
        exact Finset.sum_le_sum (fun q _ =>
          mul_le_mul_of_nonneg_left (hupdate q) (abs_nonneg _))
      _ = fp.u * ∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * (|z q| + |d q|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
  calc
    |rhs p - ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * y q| ≤
        |computedResidual p -
          ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * d q| +
        |computedResidual p - oldResidual p| +
        ∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * |updateError q| := hbase
    _ ≤ ((m : ℝ) * (n : ℝ)) * gamma fp m *
          (∑ q : Fin (m + n), H p q * |oldResidual q|) +
        gamma fp (m + n + 1) *
          (|rhs p| + ∑ q : Fin (m + n),
            |higham20Eq20_16Matrix A p q| * |z q|) +
        fp.u * ∑ q : Fin (m + n),
          |higham20Eq20_16Matrix A p q| * (|z q| + |d q|) := by
      exact add_le_add (add_le_add (hsolveDefect p) (hresidualComputation p))
        hupdateSum
    _ = fp.u *
          (((m : ℝ) * (n : ℝ) * (m : ℝ)) *
              (∑ q : Fin (m + n), H p q * |oldResidual q|) +
            ((m + n + 1 : ℕ) : ℝ) *
              (|rhs p| + ∑ q : Fin (m + n),
                |higham20Eq20_16Matrix A p q| * |z q|) +
            ∑ q : Fin (m + n),
              |higham20Eq20_16Matrix A p q| * (|z q| + |d q|)) +
          higham20Eq20_16Remainder fp A H rhs oldResidual z p := by
      rw [higham20_gamma_eq_linear_add_remainder fp m hm,
        higham20_gamma_eq_linear_add_remainder fp (m + n + 1) hdim]
      simp only [higham20Eq20_16Remainder, Nat.cast_add, Nat.cast_one]
      ring

/-! ## Executed residual and rounded-update specialization of (20.16) -/

/-- The residual supplied to the augmented correction solve in one executed
fixed-precision refinement step.  This is the conventional Chapter 12 kernel,
applied to the square augmented matrix `[[I,A],[A^T,0]]`. -/
noncomputable def higham20Eq20_16ComputedResidual {m n : ℕ}
    (fp : FPModel) (A : Fin m → Fin n → ℝ)
    (z rhs : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  fl_residual fp (m + n) (higham20Eq20_16Matrix A) z rhs

/-- The actual componentwise rounded update used after the correction solve. -/
noncomputable def higham20Eq20_16RoundedUpdate {m n : ℕ}
    (fp : FPModel) (z d : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  fun q => fp.fl_add (z q) (d q)

/-- The exact additive error committed by the executed rounded update. -/
noncomputable def higham20Eq20_16UpdateError {m n : ℕ}
    (fp : FPModel) (z d : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  fun q => higham20Eq20_16RoundedUpdate fp z d q - z q - d q

theorem higham20Eq20_16RoundedUpdate_eq {m n : ℕ}
    (fp : FPModel) (z d : Fin (m + n) → ℝ) :
    ∀ q : Fin (m + n),
      higham20Eq20_16RoundedUpdate fp z d q =
        z q + d q + higham20Eq20_16UpdateError fp z d q := by
  intro q
  simp only [higham20Eq20_16RoundedUpdate, higham20Eq20_16UpdateError]
  ring

theorem higham20Eq20_16UpdateError_abs_le {m n : ℕ}
    (fp : FPModel) (z d : Fin (m + n) → ℝ) :
    ∀ q : Fin (m + n),
      |higham20Eq20_16UpdateError fp z d q| ≤
        fp.u * (|z q| + |d q|) := by
  intro q
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add (z q) (d q)
  have herr :
      higham20Eq20_16UpdateError fp z d q = (z q + d q) * δ := by
    simp only [higham20Eq20_16UpdateError, higham20Eq20_16RoundedUpdate, hadd]
    ring
  rw [herr, abs_mul]
  calc
    |z q + d q| * |δ| ≤ |z q + d q| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ ≤ (|z q| + |d q|) * fp.u :=
      mul_le_mul_of_nonneg_right (abs_add_le _ _) fp.u_nonneg
    _ = fp.u * (|z q| + |d q|) := by ring

/-- Equation (20.16) with its conventional residual formation and rounded
update instantiated by the repository's executable floating-point kernels.

Only the correction-solver defect remains as an input.  In particular, the
post-refinement residual, residual-computation error, and update error are no
longer assumed.  The theorem is the direct adapter used by the concrete
Theorem 20.4 correction-solve endpoint. -/
theorem higham20_eq20_16_augmented_one_refinement_actual_residual_update
    (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (H : Fin (m + n) → Fin (m + n) → ℝ)
    (z d rhs : Fin (m + n) → ℝ)
    (hm : gammaValid fp m)
    (hdim : gammaValid fp (m + n + 1))
    (hsolveDefect : ∀ p : Fin (m + n),
      |higham20Eq20_16ComputedResidual fp A z rhs p -
          ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q * d q| ≤
        ((m : ℝ) * (n : ℝ)) * gamma fp m *
          ∑ q : Fin (m + n), H p q *
            |rhs q - ∑ t : Fin (m + n),
              higham20Eq20_16Matrix A q t * z t|) :
    ∀ p : Fin (m + n),
      |rhs p - ∑ q : Fin (m + n), higham20Eq20_16Matrix A p q *
          higham20Eq20_16RoundedUpdate fp z d q| ≤
        fp.u *
          (((m : ℝ) * (n : ℝ) * (m : ℝ)) *
              (∑ q : Fin (m + n), H p q *
                |rhs q - ∑ t : Fin (m + n),
                  higham20Eq20_16Matrix A q t * z t|) +
            ((m + n + 1 : ℕ) : ℝ) *
              (|rhs p| + ∑ q : Fin (m + n),
                |higham20Eq20_16Matrix A p q| * |z q|) +
            ∑ q : Fin (m + n),
              |higham20Eq20_16Matrix A p q| * (|z q| + |d q|)) +
          higham20Eq20_16Remainder fp A H rhs
            (fun q => rhs q - ∑ t : Fin (m + n),
              higham20Eq20_16Matrix A q t * z t) z p := by
  have hdim0 : gammaValid fp (m + n) :=
    gammaValid_mono fp (by omega) hdim
  exact higham20_eq20_16_augmented_one_refinement_finite
    fp m n A H z d
    (fun q => rhs q - ∑ t : Fin (m + n),
      higham20Eq20_16Matrix A q t * z t)
    (higham20Eq20_16ComputedResidual fp A z rhs)
    (higham20Eq20_16UpdateError fp z d)
    (higham20Eq20_16RoundedUpdate fp z d) rhs hm hdim
    (fun _ => rfl)
    (higham20Eq20_16RoundedUpdate_eq fp z d)
    hsolveDefect
    (higham12_9_conventional_residual_error fp (m + n)
      (higham20Eq20_16Matrix A) z rhs hdim0 hdim)
    (higham20Eq20_16UpdateError_abs_le fp z d)

end LeanFpAnalysis.FP
