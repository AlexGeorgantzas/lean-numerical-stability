/-
Copyright (c) 2026 LeanFpAnalysis contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import LeanFpAnalysis.FP.Algorithms.HighamChapter9

/-!
# Corollary 14.7 — Row Diagonally Dominant Gauss–Jordan Elimination Stability

Higham, *Accuracy and Stability of Numerical Algorithms* (2nd ed.),
Corollary 14.7 (p. 277–278).

> If GJE successfully computes an approximate solution `x̂` to `A x = b`, where
> `A ∈ ℝ^{n×n}` is row diagonally dominant, then
> ```
>   |b − A x̂|          ≤ 32 n² u |A| e eᵀ |x̂|      + O(u²)      (residual)
>   ‖x − x̂‖∞ / ‖x‖∞    ≤ 4 n³ u (κ∞(A) + 3)         + O(u²)      (forward error)
> ```

The book's proof is one sentence (p. 278):

> "The bounds follow from Theorem 14.5 on noting that `U` is row diagonally
> dominant and using Lemma 8.8 to bound cond(U) and (9.17) to bound `‖|L||U|‖∞`."

This file carries out that specialization.  The two structural facts that row
diagonal dominance supplies are proved / reused from Chapters 8 and 9:

* **Lemma 8.8** (`higham8_8_rowDiagDominantUpper_condSkeel_bound`): for a
  row-diagonally-dominant upper factor `U`, `cond(U) = ‖|U⁻¹||U|‖∞ ≤ 2n − 1`.
  Repackaged here in operator-`infNorm` form as
  `ch14ext_cor147_condU_infNorm_le`.
* **Equation (9.17)** (`higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec`): for
  `A = L̂ Û` with `Û` row diagonally dominant, `‖|L̂||Û|‖∞ ≤ (2n − 1)‖A‖∞`.
  Repackaged here as `ch14ext_cor147_absLU_infNorm_le`.

## What is DERIVED vs. INHERITED

The endpoint theorems `ch14ext_gje_overall_residual_of_accumulation` /
`ch14ext_gje_overall_forward_error_of_accumulation` (Theorem 14.5, eqs.
(14.31)/(14.32)) are the base results.  Corollary 14.7 is an *honest
specialization* of them: the row-dominant norm reduction below is fully derived
here from Lemma 8.8 + (9.17), while the componentwise Theorem-14.5 bound itself
enters as an explicit hypothesis (`hFwd` / `hRes`).  This is exactly the
inheritance the mandate flags as `SUBSTANTIVE_PARTIAL`: Theorem 14.5 carries its
own three documented residuals (Higham's WLOG `D = I`, the supplied cumulative
product inverse `Q`, and the `8nu`/`2nu` leading-order scalar audit — the latter
being precisely the `8 n u` / `2 n u` coefficients appearing in `hRes`/`hFwd`).

## Constant audit (honest)

* **Forward error.** The row-dominant reduction gives, from (14.32),
  `‖x − x̂‖∞ ≤ 2n(2n−1) u (κ∞(A) + 3) ‖x̂‖∞`.  The leading factor `2n(2n−1) =
  4n² − 2n` is *tighter* than the printed `4n³`; since `2n(2n−1) ≤ 4n³` for
  `n ≥ 1`, the printed constant `4 n³ u (κ∞(A) + 3)` is reached (as a weakening
  of the tighter derived bound).  The `‖x̂‖∞ / ‖x‖∞` factor — which equals
  `1 + O(u)` — is kept explicit rather than absorbed into `O(u²)`.
* **Residual.** The rigorous row-dominant reduction of (14.31) gives
  `‖b − A x̂‖∞ ≤ 8n(2n−1)² u ‖A‖∞ ‖x̂‖∞`, whose leading term is `32 n³ u`.  The
  printed residual constant `32 n²` is one power of `n` smaller and is *not*
  rigorously implied (the book drops one `(2n−1) ≈ 2n` factor coming from the
  second `‖·‖∞`).  We therefore state the residual at the honest `8n(2n−1)²`
  strength.
-/

namespace LeanFpAnalysis.FP.Ch14Ext

open LeanFpAnalysis.FP

-- ═══════════════════════════════════════════════════════════════════════════
-- §1  Row-dominant control facts (Lemma 8.8 and eq. (9.17) in infNorm form)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 8.8, operator-`infNorm` form.**

For a row-diagonally-dominant upper factor `U` with exact inverse `U_inv`, the
Skeel condition number `cond(U) = ‖|U⁻¹||U|‖∞` is at most `2n − 1`.  This is
`higham8_8_rowDiagDominantUpper_condSkeel_bound` repackaged as an `infNorm`
bound on the componentwise product `|U⁻¹||U|`, which is the shape Theorem 14.5's
residual/forward-error bounds consume. -/
theorem ch14ext_cor147_condU_infNorm_le (n : ℕ) (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (hURow : higham8_8_rowDiagDominantUpper n U)
    (hUinv : IsInverse n U U_inv) :
    infNorm (matMul n (absMatrix n U_inv) (absMatrix n U)) ≤ 2 * (n : ℝ) - 1 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hcond : condSkeel n hn U U_inv ≤ 2 * (n : ℝ) - 1 :=
    higham8_8_rowDiagDominantUpper_condSkeel_bound n hn U U_inv hURow hUinv
  apply infNorm_le_of_row_sum_le
  · intro i
    have hentry : ∀ j : Fin n,
        |matMul n (absMatrix n U_inv) (absMatrix n U) i j|
          = ∑ k : Fin n, |U_inv i k| * |U k j| := by
      intro j
      have hnn : 0 ≤ matMul n (absMatrix n U_inv) (absMatrix n U) i j := by
        simp only [matMul, absMatrix]
        exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      rw [abs_of_nonneg hnn]
      simp only [matMul, absMatrix]
    calc
      ∑ j : Fin n, |matMul n (absMatrix n U_inv) (absMatrix n U) i j|
          = ∑ j : Fin n, ∑ k : Fin n, |U_inv i k| * |U k j| :=
            Finset.sum_congr rfl (fun j _ => hentry j)
      _ = ∑ k : Fin n, ∑ j : Fin n, |U_inv i k| * |U k j| := Finset.sum_comm
      _ = ∑ k : Fin n, |U_inv i k| * ∑ j : Fin n, |U k j| := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [Finset.mul_sum]
      _ ≤ condSkeel n hn U U_inv := by
            unfold condSkeel
            exact Finset.le_sup'
              (fun i => ∑ j : Fin n, |U_inv i j| * (∑ k : Fin n, |U j k|))
              (Finset.mem_univ i)
      _ ≤ 2 * (n : ℝ) - 1 := hcond
  · linarith

/-- **Equation (9.17), operator-`infNorm` form.**

For an exact factorization `A = L̂ Û` whose upper factor `Û` is row diagonally
dominant, `‖|L̂||Û|‖∞ ≤ (2n − 1)‖A‖∞`.  A thin wrapper over
`higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec` unfolding the predicate to a
bare inequality. -/
theorem ch14ext_cor147_absLU_infNorm_le (n : ℕ) (hn : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat) :
    infNorm (matMul n (absMatrix n L_hat) (absMatrix n U_hat)) ≤
      (2 * (n : ℝ) - 1) * infNorm A :=
  higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec hn A L_hat U_hat hLU hURow

-- ═══════════════════════════════════════════════════════════════════════════
-- §2  Corollary 14.7 forward-error bound (printed constant `4 n³ (κ∞ + 3)`)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Corollary 14.7 — forward error (p. 278).**

`‖x − x̂‖∞ / ‖x‖∞ ≤ 4 n³ u (κ∞(A) + 3) · (‖x̂‖∞ / ‖x‖∞)`.

DERIVED from the inherited Theorem-14.5 forward-error bound (14.32) in the
printed leading-order form
```
  |x − x̂| ≤ 2 n u ( |A⁻¹||L̂||Û| + 3 |Û⁻¹||Û| ) |x̂|                         (hFwd)
```
via row diagonal dominance: `‖|Û⁻¹||Û|‖∞ ≤ 2n − 1` (Lemma 8.8) and
`‖|L̂||Û|‖∞ ≤ (2n − 1)‖A‖∞` (eq. 9.17), together with submultiplicativity of the
operator `infNorm` and `κ∞(A) = ‖A‖∞ ‖A⁻¹‖∞`.

The intermediate derived constant is the *tighter* `2n(2n − 1) (κ∞(A) + 3)`;
the headline states the printed `4 n³` (a valid weakening since
`2n(2n − 1) ≤ 4n³` for `n ≥ 1`).  The `‖x̂‖∞/‖x‖∞ = 1 + O(u)` factor is kept
explicit. -/
theorem ch14ext_cor147_forward_error_relative_infNorm
    (n : ℕ) (fp : FPModel) (hn : 0 < n)
    (A A_inv L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (x x_hat : Fin n → ℝ)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (_hAinv : IsLeftInverse n A A_inv)
    (hxpos : 0 < infNormVec x)
    (hFwd : ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u *
          (matMulVec n
              (matMul n (absMatrix n A_inv)
                (matMul n (absMatrix n L_hat) (absMatrix n U_hat)))
              (absVec n x_hat) i +
            3 * matMulVec n (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
                (absVec n x_hat) i)) :
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x ≤
      4 * (n : ℝ) ^ 3 * fp.u * (kappaInf n hn A A_inv + 3) *
        (infNormVec x_hat / infNormVec x) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hu : 0 ≤ fp.u := fp.u_nonneg
  -- Abbreviations for the two componentwise matrix factors of (14.32).
  set MLU : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat) with hMLU_def
  set M1 : Fin n → Fin n → ℝ := matMul n (absMatrix n A_inv) MLU with hM1_def
  set M2 : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n U_inv) (absMatrix n U_hat) with hM2_def
  set s : ℝ := infNormVec x_hat with hs_def
  set kap : ℝ := kappaInf n hn A A_inv with hkap_def
  have hs_nonneg : 0 ≤ s := infNormVec_nonneg x_hat
  have hkap_eq : kap = infNorm A * infNorm A_inv :=
    kappaInf_eq_infNorm_mul_infNorm n hn A A_inv
  have hkap_nonneg : 0 ≤ kap := kappaInf_nonneg n hn A A_inv
  -- Row-dominant control of the two factors.
  have hM2_norm : infNorm M2 ≤ 2 * (n : ℝ) - 1 :=
    ch14ext_cor147_condU_infNorm_le n hn U_hat U_inv hURow hUinv
  have hMLU_norm : infNorm MLU ≤ (2 * (n : ℝ) - 1) * infNorm A :=
    ch14ext_cor147_absLU_infNorm_le n hn A L_hat U_hat hLU hURow
  -- `‖|A⁻¹||L̂||Û|‖∞ ≤ (2n−1) κ∞(A)`.
  have hM1_norm : infNorm M1 ≤ (2 * (n : ℝ) - 1) * kap := by
    calc
      infNorm M1 ≤ infNorm (absMatrix n A_inv) * infNorm MLU :=
        infNorm_matMul_le hn _ _
      _ = infNorm A_inv * infNorm MLU := by rw [infNorm_absMatrix hn A_inv]
      _ ≤ infNorm A_inv * ((2 * (n : ℝ) - 1) * infNorm A) :=
        mul_le_mul_of_nonneg_left hMLU_norm (infNorm_nonneg A_inv)
      _ = (2 * (n : ℝ) - 1) * kap := by rw [hkap_eq]; ring
  -- Each componentwise matrix–vector term is bounded by `‖M‖∞ · ‖x̂‖∞`.
  have hMV : ∀ (M : Fin n → Fin n → ℝ) (i : Fin n),
      matMulVec n M (absVec n x_hat) i ≤ infNorm M * s := by
    intro M i
    calc
      matMulVec n M (absVec n x_hat) i
          ≤ |matMulVec n M (absVec n x_hat) i| := le_abs_self _
      _ ≤ infNormVec (matMulVec n M (absVec n x_hat)) :=
            abs_le_infNormVec _ i
      _ ≤ infNorm M * infNormVec (absVec n x_hat) :=
            infNormVec_matMulVec_le hn M _
      _ = infNorm M * s := by rw [infNormVec_absVec hn x_hat]
  -- Per-component forward-error bound at the tight constant `2n(2n−1)(κ+3)`.
  have h2nu : 0 ≤ 2 * (n : ℝ) * fp.u := by positivity
  have hrow_coeff : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
  have hstep : ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s := by
    intro i
    have hmv1 : matMulVec n M1 (absVec n x_hat) i ≤ (2 * (n : ℝ) - 1) * kap * s := by
      calc
        matMulVec n M1 (absVec n x_hat) i ≤ infNorm M1 * s := hMV M1 i
        _ ≤ ((2 * (n : ℝ) - 1) * kap) * s :=
              mul_le_mul_of_nonneg_right hM1_norm hs_nonneg
        _ = (2 * (n : ℝ) - 1) * kap * s := by ring
    have hmv2 : matMulVec n M2 (absVec n x_hat) i ≤ (2 * (n : ℝ) - 1) * s := by
      calc
        matMulVec n M2 (absVec n x_hat) i ≤ infNorm M2 * s := hMV M2 i
        _ ≤ (2 * (n : ℝ) - 1) * s :=
              mul_le_mul_of_nonneg_right hM2_norm hs_nonneg
    calc
      |x i - x_hat i|
          ≤ 2 * (n : ℝ) * fp.u *
              (matMulVec n M1 (absVec n x_hat) i +
                3 * matMulVec n M2 (absVec n x_hat) i) := hFwd i
      _ ≤ 2 * (n : ℝ) * fp.u *
              ((2 * (n : ℝ) - 1) * kap * s + 3 * ((2 * (n : ℝ) - 1) * s)) := by
            apply mul_le_mul_of_nonneg_left _ h2nu
            linarith [hmv1, hmv2]
      _ = 2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s := by ring
  -- Normwise, then weaken `2n(2n−1) ≤ 4n³`.
  have hRHS_nonneg :
      0 ≤ 2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s := by
    have : 0 ≤ kap + 3 := by linarith
    positivity
  have hnorm_tight :
      infNormVec (fun i : Fin n => x i - x_hat i) ≤
        2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s :=
    infNormVec_le_of_abs_le _ hstep hRHS_nonneg
  have hpoly : 2 * (n : ℝ) * (2 * (n : ℝ) - 1) ≤ 4 * (n : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) by linarith) (sq_nonneg ((n : ℝ) - 1)),
      mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) by linarith)
        (show (0 : ℝ) ≤ 2 * (n : ℝ) - 1 by linarith)]
  have hP : 0 ≤ fp.u * (kap + 3) * s :=
    mul_nonneg (mul_nonneg hu (by linarith)) hs_nonneg
  have hweak :
      2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s ≤
        4 * (n : ℝ) ^ 3 * fp.u * (kap + 3) * s := by
    have hL :
        2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s =
          (2 * (n : ℝ) * (2 * (n : ℝ) - 1)) * (fp.u * (kap + 3) * s) := by ring
    have hR :
        4 * (n : ℝ) ^ 3 * fp.u * (kap + 3) * s =
          (4 * (n : ℝ) ^ 3) * (fp.u * (kap + 3) * s) := by ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right hpoly hP
  have hnorm :
      infNormVec (fun i : Fin n => x i - x_hat i) ≤
        4 * (n : ℝ) ^ 3 * fp.u * (kap + 3) * s :=
    le_trans hnorm_tight hweak
  -- Divide by `‖x‖∞ > 0`.
  have hdiv := div_le_div_of_nonneg_right hnorm hxpos.le
  calc
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x
        ≤ (4 * (n : ℝ) ^ 3 * fp.u * (kap + 3) * s) / infNormVec x := hdiv
    _ = 4 * (n : ℝ) ^ 3 * fp.u * (kap + 3) * (s / infNormVec x) := by
          rw [mul_div_assoc]

-- ═══════════════════════════════════════════════════════════════════════════
-- §3  Corollary 14.7 residual bound (honest `8 n (2n−1)²` strength)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Corollary 14.7 — residual (p. 278), honest constant.**

`‖b − A x̂‖∞ / (‖A‖∞ ‖x̂‖∞) ≤ 8 n (2n − 1)² u`.

DERIVED from the inherited Theorem-14.5 residual bound (14.31) in the printed
leading-order form
```
  |b − A x̂| ≤ 8 n u · |L̂||Û| · |Û⁻¹||Û| · |x̂|                              (hRes)
```
via `‖|L̂||Û|‖∞ ≤ (2n − 1)‖A‖∞` (eq. 9.17) and `‖|Û⁻¹||Û|‖∞ ≤ 2n − 1`
(Lemma 8.8) with submultiplicativity of the operator `infNorm`.

The leading term of `8 n (2n − 1)²` is `32 n³ u`.  The book prints `32 n²`,
which drops one `(2n − 1) ≈ 2n` factor and is therefore *not* rigorously implied;
we state the honest `8 n (2n − 1)²` strength. -/
theorem ch14ext_cor147_residual_relative_infNorm
    (n : ℕ) (fp : FPModel) (hn : 0 < n)
    (A L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (b x_hat : Fin n → ℝ)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (hApos : 0 < infNorm A)
    (hxpos : 0 < infNormVec x_hat)
    (hRes : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat)))
            (absVec n x_hat) i) :
    infNormVec (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (infNorm A * infNormVec x_hat) ≤
      8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hu : 0 ≤ fp.u := fp.u_nonneg
  have hrow_coeff : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
  set MLU : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat) with hMLU_def
  set M2 : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n U_inv) (absMatrix n U_hat) with hM2_def
  set Mres : Fin n → Fin n → ℝ := matMul n MLU M2 with hMres_def
  set s : ℝ := infNormVec x_hat with hs_def
  have hs_nonneg : 0 ≤ s := infNormVec_nonneg x_hat
  have hApos' : 0 < infNorm A := hApos
  have hdenom_pos : 0 < infNorm A * s := mul_pos hApos hxpos
  have hM2_norm : infNorm M2 ≤ 2 * (n : ℝ) - 1 :=
    ch14ext_cor147_condU_infNorm_le n hn U_hat U_inv hURow hUinv
  have hMLU_norm : infNorm MLU ≤ (2 * (n : ℝ) - 1) * infNorm A :=
    ch14ext_cor147_absLU_infNorm_le n hn A L_hat U_hat hLU hURow
  -- `‖(|L̂||Û|)(|Û⁻¹||Û|)‖∞ ≤ (2n−1)² ‖A‖∞`.
  have hMres_norm : infNorm Mres ≤ (2 * (n : ℝ) - 1) ^ 2 * infNorm A := by
    calc
      infNorm Mres ≤ infNorm MLU * infNorm M2 := infNorm_matMul_le hn _ _
      _ ≤ ((2 * (n : ℝ) - 1) * infNorm A) * (2 * (n : ℝ) - 1) :=
            mul_le_mul hMLU_norm hM2_norm (infNorm_nonneg M2)
              (mul_nonneg hrow_coeff (infNorm_nonneg A))
      _ = (2 * (n : ℝ) - 1) ^ 2 * infNorm A := by ring
  -- Per-component: `matMulVec Mres |x̂| i ≤ ‖Mres‖∞ ‖x̂‖∞`.
  have hMV : ∀ i : Fin n,
      matMulVec n Mres (absVec n x_hat) i ≤ infNorm Mres * s := by
    intro i
    calc
      matMulVec n Mres (absVec n x_hat) i
          ≤ |matMulVec n Mres (absVec n x_hat) i| := le_abs_self _
      _ ≤ infNormVec (matMulVec n Mres (absVec n x_hat)) := abs_le_infNormVec _ i
      _ ≤ infNorm Mres * infNormVec (absVec n x_hat) := infNormVec_matMulVec_le hn Mres _
      _ = infNorm Mres * s := by rw [infNormVec_absVec hn x_hat]
  have h8nu : 0 ≤ 8 * (n : ℝ) * fp.u := by positivity
  -- Per-component residual bound at the honest constant.
  have hstep : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u * (infNorm A * s) := by
    intro i
    have hmv : matMulVec n Mres (absVec n x_hat) i ≤
        (2 * (n : ℝ) - 1) ^ 2 * infNorm A * s := by
      calc
        matMulVec n Mres (absVec n x_hat) i ≤ infNorm Mres * s := hMV i
        _ ≤ ((2 * (n : ℝ) - 1) ^ 2 * infNorm A) * s :=
              mul_le_mul_of_nonneg_right hMres_norm hs_nonneg
        _ = (2 * (n : ℝ) - 1) ^ 2 * infNorm A * s := by ring
    calc
      |b i - ∑ j : Fin n, A i j * x_hat j|
          ≤ 8 * (n : ℝ) * fp.u * matMulVec n Mres (absVec n x_hat) i := hRes i
      _ ≤ 8 * (n : ℝ) * fp.u * ((2 * (n : ℝ) - 1) ^ 2 * infNorm A * s) :=
            mul_le_mul_of_nonneg_left hmv h8nu
      _ = 8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u * (infNorm A * s) := by ring
  have hRHS_nonneg :
      0 ≤ 8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u * (infNorm A * s) := by
    have h1 : 0 ≤ infNorm A * s := hdenom_pos.le
    positivity
  have hnorm :
      infNormVec (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) ≤
        8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u * (infNorm A * s) :=
    infNormVec_le_of_abs_le _ hstep hRHS_nonneg
  -- Divide by `‖A‖∞ ‖x̂‖∞ > 0`.
  have hdiv := div_le_div_of_nonneg_right hnorm hdenom_pos.le
  calc
    infNormVec (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (infNorm A * s)
        ≤ (8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u * (infNorm A * s)) /
            (infNorm A * s) := hdiv
    _ = 8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u := by
          field_simp

end LeanFpAnalysis.FP.Ch14Ext
