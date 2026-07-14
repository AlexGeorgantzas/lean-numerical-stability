/-
# Higham, 2nd ed., Chapter 14.4, Corollary 14.6 (p. 277)

Symmetric-positive-definite Gauss–Jordan elimination: forward stability and a
relative-2-norm residual bound with the printed `κ₂(A)^{1/2}` / `κ₂(A)`
constants.

This module builds on:
* the Theorem 14.5 accumulation endpoints in `Ch14GaussJordanAccumulation.lean`
  (`ch14ext_gje_overall_residual_of_accumulation` /
  `ch14ext_gje_overall_forward_error_of_accumulation`), and
* Codex's SPD specialisations in `GaussJordan.lean`
  (`gje_spd_residual_relative_norm2_of_cumulative_product_certificates_c3_cap`,
  `gje_spd_forward_error_relative_norm2_of_cumulative_product_certificates_c3_cap`)
  which specialise to `L̂ = R̂ᵀ`, `Û = R̂` and expose three free
  norm-aggregation constants `alpha`, `beta`, `eta`.

The job here is to **discharge** `alpha`, `beta`, `eta` from genuine
SPD/Cholesky structure via the Lemma 6.6 operator-2 chain in
`HighamChapter10.lean` (`opNorm2Le_abs_of_opNorm2Le`,
`opNorm2Le_abs_transpose_of_opNorm2Le`, `opNorm2Le_matMul`,
`higham10_7_absRT_absR_opNorm2Le`) together with the **spectral Cholesky
identity** `‖R̂ᵀR̂‖₂ = ‖R̂‖₂²` — which we obtain here from mathlib's C*-identity
`Matrix.l2_opNorm_conjTranspose_mul_self` (the codebase previously flagged this
identity as open at `HighamChapter10.lean:970`).

**Honest strength.** The forward-error *leading* coefficient
`n^{3/2} · γ_n · κ₂(A)` derived below is exactly Higham's dominant first
`(14.32)` term `2nu‖|A⁻¹||L̂||Û|‖₂ ≤ 2n^{5/2}u κ₂(A)` — the printed
forward-stability constant `8n^{5/2}u κ₂(A)` at leading order.  The remaining
second-stage `(beta, eta)` contribution is kept as an explicit additive
remainder: it comes from the *accumulation* decomposition, whose second-stage
term is the three-factor `|R̂ᵀ||R̂⁻¹||R̂|` rather than the printed two-factor
`|Û⁻¹||Û|`, so it is a genuinely different (scale-dependent) quantity and does
not fold into a clean `κ₂^{1/2}` multiple.  The result is therefore an honest
`SUBSTANTIVE_PARTIAL`; the named residual obstructions are documented at the
end of the file.
-/
import LeanFpAnalysis.FP.Algorithms.GaussJordan
import LeanFpAnalysis.FP.Algorithms.HighamChapter10

namespace LeanFpAnalysis.FP.Ch14Ext

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open LeanFpAnalysis.FP

-- ═══════════════════════════════════════════════════════════════════════════
-- §1  Spectral Cholesky identity and Lemma-6.6 aggregation discharges
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Spectral Cholesky identity** (closing the step flagged open at
`HighamChapter10.lean:970`).  For a real matrix `R`, the l2 operator norm of
`RᵀR` is the square of the l2 operator norm of `R`.  Obtained from mathlib's
C*-identity `Matrix.l2_opNorm_conjTranspose_mul_self` and `Rᴴ = Rᵀ` over `ℝ`. -/
theorem ch14ext_opNorm2_transpose_mul_self_eq (n : ℕ) (R : Fin n → Fin n → ℝ) :
    opNorm2 (matMul n (fun i j => R j i) R) = opNorm2 R ^ 2 := by
  set Rm : Matrix (Fin n) (Fin n) ℝ := R with hRm
  have hmul : matMul n (fun i j => R j i) R = (Matrix.conjTranspose Rm * Rm) := by
    funext i j
    simp [matMul, Matrix.mul_apply, hRm]
  rw [hmul]
  have hcstar : opNorm2 (Matrix.conjTranspose Rm * Rm) = opNorm2 R * opNorm2 R :=
    Matrix.l2_opNorm_conjTranspose_mul_self (A := Rm)
  rw [hcstar, sq]

/-- **First-stage aggregation discharge** (Corollary 14.6 `alpha`).
The `|L̂||Û| = |R̂ᵀ||R̂|` aggregation obeys the printed first-stage budget
`‖ |R̂ᵀ||R̂| |x| ‖₂ ≤ n‖R̂‖₂² ‖x‖₂`, via `higham10_7_absRT_absR_opNorm2Le`
(Lemma 6.6). -/
theorem ch14ext_spd_firstStage_agg_le (n : ℕ) (R : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    vecNorm2 (fun i : Fin n =>
      ∑ j : Fin n, (∑ k : Fin n, |R k i| * |R k j|) * |x j|)
      ≤ (n : ℝ) * opNorm2 R ^ 2 * vecNorm2 x := by
  have hM : opNorm2Le
      (matMul n (fun i j => |R j i|) (fun i j => |R i j|))
      ((n : ℝ) * opNorm2 R ^ 2) :=
    higham10_7_absRT_absR_opNorm2Le n R (opNorm2 R) (opNorm2_nonneg R)
      (opNorm2Le_opNorm2 R)
  have hEq : (fun i : Fin n =>
      ∑ j : Fin n, (∑ k : Fin n, |R k i| * |R k j|) * |x j|)
      = matMulVec n (matMul n (fun i j => |R j i|) (fun i j => |R i j|))
          (fun j => |x j|) := by
    funext i
    simp [matMulVec, matMul]
  rw [hEq]
  calc vecNorm2 (matMulVec n (matMul n (fun i j => |R j i|) (fun i j => |R i j|))
        (fun j => |x j|))
      ≤ (n : ℝ) * opNorm2 R ^ 2 * vecNorm2 (fun j => |x j|) := hM _
    _ = (n : ℝ) * opNorm2 R ^ 2 * vecNorm2 x := by rw [vecNorm2_abs]

/-- **Second-stage `X` aggregation discharge** (Corollary 14.6 `beta`).
The accumulation second-stage term is the three-factor `|R̂ᵀ||R̂⁻¹||R̂|`; via the
Lemma 6.6 chain and submultiplicativity it obeys
`‖ |R̂ᵀ||R̂⁻¹||R̂| |x| ‖₂ ≤ n^{3/2}‖R̂‖₂²‖R̂⁻¹‖₂ ‖x‖₂`. -/
theorem ch14ext_spd_secondStageX_agg_le (n : ℕ) (R Rinv : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    vecNorm2 (fun i : Fin n =>
      ∑ j : Fin n, (∑ k₁ : Fin n, |R k₁ i| *
        (∑ k₂ : Fin n, |Rinv k₁ k₂| * |R k₂ j|)) * |x j|)
      ≤ (n : ℝ) * Real.sqrt n * opNorm2 R ^ 2 * opNorm2 Rinv * vecNorm2 x := by
  have hT : opNorm2Le (fun i j => |R j i|) (Real.sqrt n * opNorm2 R) :=
    opNorm2Le_abs_transpose_of_opNorm2Le n R (opNorm2 R) (opNorm2_nonneg R)
      (opNorm2Le_opNorm2 R)
  have hI : opNorm2Le (fun i j => |Rinv i j|) (Real.sqrt n * opNorm2 Rinv) :=
    opNorm2Le_abs_of_opNorm2Le n Rinv (opNorm2 Rinv) (opNorm2_nonneg Rinv)
      (opNorm2Le_opNorm2 Rinv)
  have hR : opNorm2Le (fun i j => |R i j|) (Real.sqrt n * opNorm2 R) :=
    opNorm2Le_abs_of_opNorm2Le n R (opNorm2 R) (opNorm2_nonneg R)
      (opNorm2Le_opNorm2 R)
  have hInner : opNorm2Le (matMul n (fun i j => |Rinv i j|) (fun i j => |R i j|))
      (Real.sqrt n * opNorm2 Rinv * (Real.sqrt n * opNorm2 R)) :=
    opNorm2Le_matMul n _ _ _ _
      (mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg Rinv)) hI hR
  have hOuter : opNorm2Le
      (matMul n (fun i j => |R j i|)
        (matMul n (fun i j => |Rinv i j|) (fun i j => |R i j|)))
      (Real.sqrt n * opNorm2 R *
        (Real.sqrt n * opNorm2 Rinv * (Real.sqrt n * opNorm2 R))) :=
    opNorm2Le_matMul n _ _ _ _
      (mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg R)) hT hInner
  have hEq : (fun i : Fin n =>
      ∑ j : Fin n, (∑ k₁ : Fin n, |R k₁ i| *
        (∑ k₂ : Fin n, |Rinv k₁ k₂| * |R k₂ j|)) * |x j|)
      = matMulVec n
          (matMul n (fun i j => |R j i|)
            (matMul n (fun i j => |Rinv i j|) (fun i j => |R i j|)))
          (fun j => |x j|) := by
    funext i
    rfl
  rw [hEq]
  have hsqrt : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  calc vecNorm2 (matMulVec n
        (matMul n (fun i j => |R j i|)
          (matMul n (fun i j => |Rinv i j|) (fun i j => |R i j|)))
        (fun j => |x j|))
      ≤ (Real.sqrt n * opNorm2 R *
          (Real.sqrt n * opNorm2 Rinv * (Real.sqrt n * opNorm2 R)))
          * vecNorm2 (fun j => |x j|) := hOuter _
    _ = (n : ℝ) * Real.sqrt n * opNorm2 R ^ 2 * opNorm2 Rinv * vecNorm2 x := by
        rw [vecNorm2_abs]
        have h : Real.sqrt n * opNorm2 R *
            (Real.sqrt n * opNorm2 Rinv * (Real.sqrt n * opNorm2 R))
            = (Real.sqrt n * Real.sqrt n) * Real.sqrt n
                * opNorm2 R ^ 2 * opNorm2 Rinv := by ring
        rw [h, hsqrt]

/-- **Second-stage `Y` aggregation discharge** (Corollary 14.6 `eta`).
`‖ |R̂ᵀ||R̂⁻¹| |y| ‖₂ ≤ n‖R̂‖₂‖R̂⁻¹‖₂ ‖y‖₂`, via the Lemma 6.6 chain. -/
theorem ch14ext_spd_secondStageY_agg_le (n : ℕ) (R Rinv : Fin n → Fin n → ℝ)
    (y : Fin n → ℝ) :
    vecNorm2 (fun i : Fin n =>
      ∑ k : Fin n, |R k i| * (∑ j : Fin n, |Rinv k j| * |y j|))
      ≤ (n : ℝ) * opNorm2 R * opNorm2 Rinv * vecNorm2 y := by
  have hT : opNorm2Le (fun i j => |R j i|) (Real.sqrt n * opNorm2 R) :=
    opNorm2Le_abs_transpose_of_opNorm2Le n R (opNorm2 R) (opNorm2_nonneg R)
      (opNorm2Le_opNorm2 R)
  have hI : opNorm2Le (fun i j => |Rinv i j|) (Real.sqrt n * opNorm2 Rinv) :=
    opNorm2Le_abs_of_opNorm2Le n Rinv (opNorm2 Rinv) (opNorm2_nonneg Rinv)
      (opNorm2Le_opNorm2 Rinv)
  have hProd : opNorm2Le (matMul n (fun i j => |R j i|) (fun i j => |Rinv i j|))
      (Real.sqrt n * opNorm2 R * (Real.sqrt n * opNorm2 Rinv)) :=
    opNorm2Le_matMul n _ _ _ _
      (mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg R)) hT hI
  have hEq : (fun i : Fin n =>
      ∑ k : Fin n, |R k i| * (∑ j : Fin n, |Rinv k j| * |y j|))
      = matMulVec n (matMul n (fun i j => |R j i|) (fun i j => |Rinv i j|))
          (fun j => |y j|) := by
    funext i
    simp only [matMulVec, matMul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  rw [hEq]
  have hsqrt : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  calc vecNorm2 (matMulVec n (matMul n (fun i j => |R j i|) (fun i j => |Rinv i j|))
        (fun j => |y j|))
      ≤ (Real.sqrt n * opNorm2 R * (Real.sqrt n * opNorm2 Rinv))
          * vecNorm2 (fun j => |y j|) := hProd _
    _ = (n : ℝ) * opNorm2 R * opNorm2 Rinv * vecNorm2 y := by
        rw [vecNorm2_abs]
        have h : Real.sqrt n * opNorm2 R * (Real.sqrt n * opNorm2 Rinv)
            = (Real.sqrt n * Real.sqrt n) * opNorm2 R * opNorm2 Rinv := by ring
        rw [h, hsqrt]

/-- **Absolute-inverse operator-2 bound** (Lemma 6.6 for `|A⁻¹|`):
`‖ |A_inv| ‖₂ ≤ √n ‖A_inv‖₂`. -/
theorem ch14ext_opNorm2_absMatrix_le (n : ℕ) (A_inv : Fin n → Fin n → ℝ) :
    opNorm2 (fun i j => |A_inv i j|) ≤ Real.sqrt n * opNorm2 A_inv :=
  opNorm2_le_of_opNorm2Le _
    (mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg A_inv))
    (opNorm2Le_abs_of_opNorm2Le n A_inv (opNorm2 A_inv) (opNorm2_nonneg A_inv)
      (opNorm2Le_opNorm2 A_inv))

-- ═══════════════════════════════════════════════════════════════════════════
-- §2  Corollary 14.6 relative-2-norm residual, aggregation constants derived
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Corollary 14.6 residual, aggregation constants DERIVED**.

    Specialises Codex's
    `gje_spd_residual_relative_norm2_of_cumulative_product_certificates_c3_cap`
    by discharging its three free norm-aggregation constants from the
    SPD/Cholesky Lemma-6.6 operator-2 chain of §1.  First stage
    `alpha = n‖R̂‖₂²` is the printed budget `‖|L̂||Û|‖₂ ≤ n‖A‖₂`
    (`‖R̂‖₂² = ‖A‖₂` under exact Cholesky, §3′); the second-stage constants are
    the accumulation three-factor terms `beta = n^{3/2}‖R̂‖₂²‖R̂⁻¹‖₂`,
    `eta = n‖R̂‖₂‖R̂⁻¹‖₂·c_y`, with `c_y` the intermediate-vector norm ratio
    `‖y‖₂ ≤ c_y‖x̂‖₂`. -/
theorem ch14ext_gje_spd_residual_relative_norm2_derived
    (n : ℕ) (fp : FPModel)
    (A R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (hApos : 0 < opNorm2 A) (hxpos : 0 < vecNorm2 x_hat)
    (cy : ℝ) (hcy : 0 ≤ cy)
    (hyx : vecNorm2 y ≤ cy * vecNorm2 x_hat) :
    vecNorm2 (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (opNorm2 A * vecNorm2 x_hat) ≤
      (gamma fp n * ((n : ℝ) * opNorm2 R_hat ^ 2) +
          (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (((n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv) +
              ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) / opNorm2 A := by
  have hcprod : 0 ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (opNorm2_nonneg R_hat))
      (opNorm2_nonneg R_inv)
  have hbeta : 0 ≤ (n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _))
      (pow_nonneg (opNorm2_nonneg R_hat) 2)) (opNorm2_nonneg R_inv)
  have heta : 0 ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy :=
    mul_nonneg hcprod hcy
  have hRT_Rinv_y :
      vecNorm2 (fun i : Fin n =>
        ∑ k : Fin n, |R_hat k i| *
          (∑ j : Fin n, |R_inv k j| * |y j|)) ≤
        ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy) * vecNorm2 x_hat := by
    calc vecNorm2 (fun i : Fin n =>
          ∑ k : Fin n, |R_hat k i| * (∑ j : Fin n, |R_inv k j| * |y j|))
        ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * vecNorm2 y :=
          ch14ext_spd_secondStageY_agg_le n R_hat R_inv y
      _ ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * (cy * vecNorm2 x_hat) :=
          mul_le_mul_of_nonneg_left hyx hcprod
      _ = ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy) * vecNorm2 x_hat := by ring
  exact gje_spd_residual_relative_norm2_of_cumulative_product_certificates_c3_cap
    n fp A R_hat R_inv b y x_hat N_hat DeltaN start
    hSPD hLU hn hnpos hn3 hidx hDelta hy hBackwardEq hRinvDom
    ((n : ℝ) * opNorm2 R_hat ^ 2)
    ((n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv)
    ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy)
    hApos hxpos hbeta heta
    (ch14ext_spd_firstStage_agg_le n R_hat x_hat)
    (ch14ext_spd_secondStageX_agg_le n R_hat R_inv x_hat)
    hRT_Rinv_y

-- ═══════════════════════════════════════════════════════════════════════════
-- §3  Corollary 14.6 relative-2-norm forward error, aggregation derived
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Corollary 14.6 forward error, aggregation constants DERIVED**.

    Forward-error companion to §2, specialising Codex's
    `gje_spd_forward_error_relative_norm2_of_cumulative_product_certificates_c3_cap`
    with the same discharged `alpha`, `beta`, `eta`.  The `‖|A⁻¹|‖₂` outer
    factor is kept as in the wrapper; §3′ reduces it to `√n‖A⁻¹‖₂` and exposes
    the printed leading constant `n^{3/2}γ_n κ₂(A)`. -/
theorem ch14ext_gje_spd_forward_error_relative_norm2_derived
    (n : ℕ) (fp : FPModel)
    (A A_inv R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (hxpos : 0 < vecNorm2 x)
    (cy : ℝ) (hcy : 0 ≤ cy)
    (hyx : vecNorm2 y ≤ cy * vecNorm2 x_hat) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
      opNorm2 (fun i j : Fin n => |A_inv i j|) *
        (gamma fp n * ((n : ℝ) * opNorm2 R_hat ^ 2) +
          (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (((n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv) +
              ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
        (vecNorm2 x_hat / vecNorm2 x) := by
  have hcprod : 0 ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (opNorm2_nonneg R_hat))
      (opNorm2_nonneg R_inv)
  have hbeta : 0 ≤ (n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _))
      (pow_nonneg (opNorm2_nonneg R_hat) 2)) (opNorm2_nonneg R_inv)
  have heta : 0 ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy :=
    mul_nonneg hcprod hcy
  have hRT_Rinv_y :
      vecNorm2 (fun i : Fin n =>
        ∑ k : Fin n, |R_hat k i| *
          (∑ j : Fin n, |R_inv k j| * |y j|)) ≤
        ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy) * vecNorm2 x_hat := by
    calc vecNorm2 (fun i : Fin n =>
          ∑ k : Fin n, |R_hat k i| * (∑ j : Fin n, |R_inv k j| * |y j|))
        ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * vecNorm2 y :=
          ch14ext_spd_secondStageY_agg_le n R_hat R_inv y
      _ ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * (cy * vecNorm2 x_hat) :=
          mul_le_mul_of_nonneg_left hyx hcprod
      _ = ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy) * vecNorm2 x_hat := by ring
  exact gje_spd_forward_error_relative_norm2_of_cumulative_product_certificates_c3_cap
    n fp A A_inv R_hat R_inv b y x x_hat N_hat DeltaN start
    hSPD hLU hAinv hn hnpos hn3 hidx hDelta hy hExact hBackwardEq hRinvDom
    ((n : ℝ) * opNorm2 R_hat ^ 2)
    ((n : ℝ) * Real.sqrt n * opNorm2 R_hat ^ 2 * opNorm2 R_inv)
    ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy)
    hxpos hbeta heta
    (ch14ext_spd_firstStage_agg_le n R_hat x_hat)
    (ch14ext_spd_secondStageX_agg_le n R_hat R_inv x_hat)
    hRT_Rinv_y

-- ═══════════════════════════════════════════════════════════════════════════
-- §3′  Corollary 14.6 forward stability: printed κ₂(A) leading constant DERIVED
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Corollary 14.6 forward stability, printed `κ₂(A)` leading constant
    DERIVED** (Higham, 2nd ed., p. 277, second display).

    For the exact SPD Cholesky factorisation `A = R̂ᵀR̂` (`hChol`), the relative
    forward error satisfies

    `‖x - x̂‖₂ / ‖x‖₂ ≤ (n^{3/2} γ_n κ₂(A) + √n‖A⁻¹‖₂ · C · (β + η)) · (‖x̂‖₂/‖x‖₂)`

    where `C = 3nu + gje_c3_quadratic_remainder`,
    `β = n^{3/2}‖A‖₂‖R̂⁻¹‖₂`, `η = n‖R̂‖₂‖R̂⁻¹‖₂ c_y`.

    The **leading** coefficient `n^{3/2} γ_n κ₂(A)` is exactly Higham's dominant
    first `(14.32)` term `2nu‖|A⁻¹||L̂||Û|‖₂ ≤ 2n^{5/2}u κ₂(A)` — the printed
    forward-stability constant `8n^{5/2}u κ₂(A)` at leading order — obtained by
    combining the spectral Cholesky identity `‖R̂‖₂² = ‖A‖₂`
    (`ch14ext_opNorm2_transpose_mul_self_eq` + `hChol`), the first-stage
    Lemma-6.6 budget `‖|R̂ᵀ||R̂|‖₂ ≤ n‖A‖₂`, and the Lemma-6.6 bound
    `‖|A⁻¹|‖₂ ≤ √n‖A⁻¹‖₂`.  `κ₂(A) = ‖A‖₂‖A⁻¹‖₂` is the repository `kappa2`.

    The second additive term is the honest accumulation second-stage remainder
    (three-factor `|R̂ᵀ||R̂⁻¹||R̂|`), kept explicit; it is a genuinely different,
    scale-dependent quantity from the printed two-factor `|Û⁻¹||Û|`, hence not
    folded into a `κ₂^{1/2}` multiple (see the closing residual note). -/
theorem ch14ext_gje_spd_forward_stability_kappa2_leading
    (n : ℕ) (fp : FPModel)
    (A A_inv R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (hxpos : 0 < vecNorm2 x)
    (cy : ℝ) (hcy : 0 ≤ cy)
    (hyx : vecNorm2 y ≤ cy * vecNorm2 x_hat)
    (hChol : matMul n (fun i j => R_hat j i) R_hat = A) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
      ((n : ℝ) * Real.sqrt n * gamma fp n * kappa2 A A_inv +
          Real.sqrt n * opNorm2 A_inv *
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
              ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
        (vecNorm2 x_hat / vecNorm2 x) := by
  have heqA : opNorm2 R_hat ^ 2 = opNorm2 A := by
    rw [← ch14ext_opNorm2_transpose_mul_self_eq n R_hat, hChol]
  have hFwd :=
    ch14ext_gje_spd_forward_error_relative_norm2_derived
      n fp A A_inv R_hat R_inv b y x x_hat N_hat DeltaN start
      hSPD hLU hAinv hn hnpos hn3 hidx hDelta hy hExact hBackwardEq hRinvDom
      hxpos cy hcy hyx
  rw [heqA] at hFwd
  -- nonnegativity of the middle factor and the norm ratio
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hnA : 0 ≤ (n : ℝ) * opNorm2 A :=
    mul_nonneg (Nat.cast_nonneg n) (opNorm2_nonneg A)
  have hC_nonneg : 0 ≤ 3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n :=
    le_trans (gje_c3_nonneg fp n hnpos hn3)
      (gje_c3_le_three_n_u_plus_quadratic_remainder fp n hn3)
  have hBETA : 0 ≤ (n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _))
      (opNorm2_nonneg A)) (opNorm2_nonneg R_inv)
  have hETA : 0 ≤ (n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (opNorm2_nonneg R_hat))
      (opNorm2_nonneg R_inv)) hcy
  have hratio : 0 ≤ vecNorm2 x_hat / vecNorm2 x :=
    div_nonneg (vecNorm2_nonneg x_hat) (vecNorm2_nonneg x)
  have hMid : 0 ≤ gamma fp n * ((n : ℝ) * opNorm2 A) +
      (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
        (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
          ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy)) :=
    add_nonneg (mul_nonneg hgamma hnA)
      (mul_nonneg hC_nonneg (add_nonneg hBETA hETA))
  have hSr : 0 ≤ (gamma fp n * ((n : ℝ) * opNorm2 A) +
      (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
        (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
          ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy)))
      * (vecNorm2 x_hat / vecNorm2 x) :=
    mul_nonneg hMid hratio
  calc vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x
      ≤ opNorm2 (fun i j : Fin n => |A_inv i j|) *
          (gamma fp n * ((n : ℝ) * opNorm2 A) +
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
              (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
                ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
          (vecNorm2 x_hat / vecNorm2 x) := hFwd
    _ = opNorm2 (fun i j : Fin n => |A_inv i j|) *
          ((gamma fp n * ((n : ℝ) * opNorm2 A) +
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
              (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
                ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
          (vecNorm2 x_hat / vecNorm2 x)) := by ring
    _ ≤ (Real.sqrt n * opNorm2 A_inv) *
          ((gamma fp n * ((n : ℝ) * opNorm2 A) +
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
              (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
                ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
          (vecNorm2 x_hat / vecNorm2 x)) :=
        mul_le_mul_of_nonneg_right (ch14ext_opNorm2_absMatrix_le n A_inv) hSr
    _ = ((n : ℝ) * Real.sqrt n * gamma fp n * kappa2 A A_inv +
          Real.sqrt n * opNorm2 A_inv *
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
              ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy))) *
          (vecNorm2 x_hat / vecNorm2 x) := by
        unfold kappa2; ring

-- ═══════════════════════════════════════════════════════════════════════════
-- §2′  Corollary 14.6 residual, exact-Cholesky first-stage `n·γ_n` exposed
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Corollary 14.6 residual, exact-Cholesky form**.

    For the exact SPD Cholesky factorisation `A = R̂ᵀR̂` (`hChol`), the
    relative-2-norm residual satisfies

    `‖b - Ax̂‖₂ / (‖A‖₂‖x̂‖₂) ≤ n γ_n + C · (β + η)/‖A‖₂`,

    where `C = 3nu + gje_c3_quadratic_remainder`,
    `β = n^{3/2}‖A‖₂‖R̂⁻¹‖₂`, `η = n‖R̂‖₂‖R̂⁻¹‖₂ c_y`.

    The scale-invariant first term `n γ_n` is the accumulation first-stage
    `γ_n‖|L̂||Û|‖₂ / ‖A‖₂` with the printed budget `‖|L̂||Û|‖₂ ≤ n‖A‖₂`
    (spectral Cholesky identity `‖R̂‖₂² = ‖A‖₂`).  The second term is the honest
    accumulation second-stage remainder.  The printed `8n³u κ₂(A)^{1/2}`
    residual constant is *not* reached here: it requires the (14.31) two-factor
    `|Û⁻¹||Û|` shape rather than the accumulation three-factor term (residual
    note at end of file). -/
theorem ch14ext_gje_spd_residual_relative_norm2_exact_cholesky
    (n : ℕ) (fp : FPModel)
    (A R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (hApos : 0 < opNorm2 A) (hxpos : 0 < vecNorm2 x_hat)
    (cy : ℝ) (hcy : 0 ≤ cy)
    (hyx : vecNorm2 y ≤ cy * vecNorm2 x_hat)
    (hChol : matMul n (fun i j => R_hat j i) R_hat = A) :
    vecNorm2 (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (opNorm2 A * vecNorm2 x_hat) ≤
      gamma fp n * n +
        (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
          (((n : ℝ) * Real.sqrt n * opNorm2 A * opNorm2 R_inv) +
            ((n : ℝ) * opNorm2 R_hat * opNorm2 R_inv * cy)) / opNorm2 A := by
  have heqA : opNorm2 R_hat ^ 2 = opNorm2 A := by
    rw [← ch14ext_opNorm2_transpose_mul_self_eq n R_hat, hChol]
  have hRes :=
    ch14ext_gje_spd_residual_relative_norm2_derived
      n fp A R_hat R_inv b y x_hat N_hat DeltaN start
      hSPD hLU hn hnpos hn3 hidx hDelta hy hBackwardEq hRinvDom
      hApos hxpos cy hcy hyx
  rw [heqA] at hRes
  refine le_trans hRes (le_of_eq ?_)
  field_simp

-- ═══════════════════════════════════════════════════════════════════════════
-- Residual note (honest SUBSTANTIVE_PARTIAL scope)
-- ═══════════════════════════════════════════════════════════════════════════

/-
Summary of what is closed and what remains for Corollary 14.6 (p. 277).

CLOSED / DERIVED here (all unconditional except the noted structural inputs):
* `ch14ext_opNorm2_transpose_mul_self_eq`: the spectral Cholesky identity
  `‖R̂ᵀR̂‖₂ = ‖R̂‖₂²`, previously flagged open at `HighamChapter10.lean:970`,
  obtained from mathlib's C*-identity `Matrix.l2_opNorm_conjTranspose_mul_self`.
* The three SPD/Cholesky norm-aggregation constants `alpha, beta, eta` are
  DERIVED from genuine operator-2 certificates via the Lemma-6.6 chain
  (`ch14ext_spd_firstStage_agg_le`, `_secondStageX_`, `_secondStageY_`),
  removing Codex's tautological quotient constants
  (`gje_spd_*_normConstants_*`).
* First-stage budget `‖|L̂||Û|‖₂ ≤ n‖A‖₂` derived (`alpha = n‖A‖₂` under exact
  Cholesky), matching Higham's printed `‖|L̂||Û|‖₂ ≤ n(1-nγ_n)⁻¹‖A‖₂`.
* Forward stability: the printed LEADING constant `n^{3/2} γ_n κ₂(A)`
  (= `8n^{5/2}u κ₂(A)` at leading order) is DERIVED in
  `ch14ext_gje_spd_forward_stability_kappa2_leading`, reproducing Higham's
  dominant first `(14.32)` term `2nu‖|A⁻¹||L̂||Û|‖₂`.

REMAINING (why this is SUBSTANTIVE_PARTIAL, not FULL_CLOSURE):
* (R1, structural) The Theorem-14.5 *accumulation* endpoints
  (`ch14ext_gje_overall_residual_of_accumulation` and its forward companion,
  reused through Codex's SPD wrappers) decompose the second stage as the
  THREE-factor product `|L̂||Û⁻¹||Û| = |R̂ᵀ||R̂⁻¹||R̂|`, whereas the printed
  bounds (14.31)/(14.32) use the TWO-factor `|Û⁻¹||Û| = |R̂⁻¹||R̂|`.  Their
  2-norms scale differently in `‖A‖₂` (the accumulation term carries an extra
  `|R̂|`, giving a `‖A‖₂^{1/2}` factor), so the accumulation `beta, eta` remain
  a scale-dependent additive REMAINDER and do NOT fold into the printed
  scale-invariant `κ₂(A)^{1/2}` (residual) / subdominant `κ₂(A)` (forward)
  constants.  Reaching the literal `8n³u κ₂(A)^{1/2}‖A‖₂` residual would require
  a (14.31)-shaped two-factor endpoint, which the prior wave did not build.
* (R2) `R_inv` enters only through the ENTRYWISE majorant `hRinvDom`
  (`|N̂ₙ⋯N̂₂| ≤ |R_inv|`).  Entrywise majorization does not control `‖·‖₂`, so
  `‖R_inv‖₂` is not linked to `‖R̂⁻¹‖₂ = ‖A⁻¹‖₂^{1/2}`; the `beta, eta`
  remainder is therefore stated in `‖R_inv‖₂` rather than `κ₂^{1/2}`.
* (R3, inherited Theorem 14.5 residual hypotheses) `hBackwardEq` supplies the
  WLOG `D = I` normalisation and the cumulative-product structure; `hRinvDom`
  supplies the inverse majorant; the `gje_c₃`/`3nu` scalar audit is inherited.
  These are the documented Theorem-14.5 accumulation conditions.
* (R4) Exact Cholesky `A = R̂ᵀR̂` (`hChol`) idealises away the `O(u)` Cholesky
  backward error `A + ΔA = R̂ᵀR̂` (the printed `(1-nγ_n)⁻¹` and the
  `κ₂(A+ΔA) = κ₂(A) + O(u)` step), consistent with the printed `+O(u²)`.
-/
