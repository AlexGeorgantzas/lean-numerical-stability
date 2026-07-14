-- Algorithms/Ch14MethodDProductDischarge.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 14 (Matrix Inversion), §14.3.4 "Method D", equations (14.20)-(14.23),
-- pp. 270-271.
--
-- GOAL: discharge the fl-matmul product-formation hypothesis `hProd` that
-- `Ch14MethodDUpperCertificate.ch14ext_methodD_left_residual_both` still takes,
-- by INSTANTIATING it from the repo's concrete floating-point matrix-matrix
-- product `fl_matMul` and its proven forward-error bound
-- `matMul_error_bound` (Higham §3.5, eq 3.13, `MatMul.lean`).  The remaining
-- hypothesis after this file is the single genuine UPSTREAM certificate `hLU`
-- (LU backward error, Higham Thm 9.3); see the STRENGTH note below for why it
-- cannot be made unconditional with the repo's current GE producers.
--
-- ------------------------------------------------------------------------
-- What is CLOSED unconditionally here (hProd DISCHARGED, no longer assumed):
--   * `ch14ext_methodD_prod_error_flMatMul`      — the fl-matmul product
--       certificate `MatProdError` for the computed inverse
--       X̂ = fl(X_U X_L), DERIVED from `matMul_error_bound` at `gamma fp n`
--       and lifted to the shared accumulator `gamma fp (n+2)` by accumulator
--       monotonicity (`gamma_mono`).  No hypothesis: this is the concrete
--       column-by-column floating-point product of the two triangular inverses.
--   * `ch14ext_methodD_left_residual_prodFree`   — the printed (4γ+2γ²) Method D
--       componentwise envelope (14.23) for the CONCRETE computed inverse
--       X̂ = fl_matMul fp n n n X_U X_L, with BOTH triangular-inverse LEFT
--       residuals discharged (upper by the reversal-conjugated Method 2 loop,
--       lower by the wave-2 Method 2 loop) AND the product-formation hypothesis
--       hProd discharged by this file's fl-matmul certificate.  The ONLY
--       remaining hypothesis is `hLU`.
--   * `ch14ext_methodD_left_residual_prodFree_infNorm` — its ‖·‖_∞ companion.
--
-- ------------------------------------------------------------------------
-- HONEST STRENGTH — why `hLU` REMAINS a hypothesis (documented obstruction):
--
-- Higham's Method D forms A^{-1} from the GE factors L̂, Û of A, whose backward
-- error `LUBackwardError n A L̂ Û (γ_n)` (Thm 9.3, A = L̂Û + ΔA, |ΔA| ≤ γ_n|L̂||Û|)
-- is the upstream input.  The repo does have a CONCRETE rounded GE loop
-- (`higham9_2_rectRoundedLoopL/U`) and a producer chain
-- (`…rectRoundedLoop_square_to_DoolittleLU` → `DoolittleLU.to_LUBackwardError`)
-- that turns it into a `LUBackwardError` certificate FOR THE LOOP'S OWN FACTORS.
-- BUT that chain is NOT unconditional: it requires the per-stage
-- absolute-budget / component-dominance hypotheses
--   `higham9_2_rectDoolittleUAbsBudget … ≤ γ_n·|U k j|`,
--   `higham9_2_rectDoolittleLAbsBudget … ≤ γ_n·|L i k · U k k|`
-- (see `higham9_2_rectRoundedLoop_square_to_DoolittleLU` and
--  `higham9_2_rectDoolittleUAbsBudget_le_compression_of_component_dominance`,
--  whose own `hwork ≤ |U k j|`, `hprod ≤ |U k j|` premises encode the essence
--  of the Thm 9.3 growth-controlled analysis).  These per-stage bounds are
-- NEVER proved from the FP model in this repo; they are always assumed.
--
-- The only fully UNCONDITIONAL `LUBackwardError` producers in the repo are the
-- exact-factorization ones (`LUFactSpec.to_LUBackwardError_zero`,
-- `higham9_LUFactSpec_to_LUBackwardError_gamma`, ε = 0), which require
-- `∑_k L̂ᵢₖ Ûₖⱼ = Aᵢⱼ` exactly (A = L̂Û) and `L̂ᵢᵢ = 1`.  Using them for an
-- arbitrary A would force A := L̂Û and collapse the backward error to zero — a
-- trivialization, not a genuine discharge (forbidden by the honest-strength
-- constraint).  Hence `hLU` is left as the single genuine upstream hypothesis,
-- exactly as Higham states it, and only `hProd` is discharged here.
--
-- No new floating-point analysis is assumed for the product: every constant is
-- DERIVED, and X̂ is the concrete `fl_matMul` of the two concrete inverse loops.

import LeanFpAnalysis.FP.Algorithms.Ch14MethodDUpperCertificate

namespace LeanFpAnalysis.FP.Ch14Ext

open scoped BigOperators

-- ============================================================
-- fl-matmul product certificate for the two triangular inverses
-- ============================================================

/-- **Higham §3.5 (eq 3.13) fl-matmul certificate for Method D's product step.**

    The computed inverse `X̂ = fl_matMul fp X_U X_L` (the concrete column-by-column
    floating-point product of the reversal-conjugated upper Method 2 inverse
    `X_U = ch14ext_method2InvUpper n fp U` and the wave-2 lower Method 2 inverse
    `X_L = ch14ext_method2Inv n fp L`) satisfies the componentwise product-error
    certificate

        |X̂ᵢⱼ − (X_U X_L)ᵢⱼ| ≤ γ_{n+2} · (|X_U||X_L|)ᵢⱼ

    DERIVED from `matMul_error_bound` (which gives the bound at `γ_n`) and lifted
    to the shared Method D accumulator `γ_{n+2}` by accumulator monotonicity
    (`gamma_mono`, valid since `n ≤ n+2` and the weight `(|X_U||X_L|)ᵢⱼ ≥ 0`).
    This is exactly the `hProd` slot of `ch14ext_methodD_left_residual_both`,
    now DISCHARGED. -/
theorem ch14ext_methodD_prod_error_flMatMul (n : ℕ) (fp : FPModel)
    (L U : Fin n → Fin n → ℝ) (hn2 : gammaValid fp (n + 2)) :
    MatProdError n
      (fl_matMul fp n n n
        (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L))
      (matMul n (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L))
      (gamma fp (n + 2))
      (fun i j => ∑ k : Fin n,
        |ch14ext_method2InvUpper n fp U i k| * |ch14ext_method2Inv n fp L k j|) := by
  intro i j
  have hnv : gammaValid fp n := gammaValid_mono fp (by omega) hn2
  have hb := matMul_error_bound fp n n n
    (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) hnv i j
  have hw_nonneg :
      0 ≤ ∑ k : Fin n,
        |ch14ext_method2InvUpper n fp U i k| * |ch14ext_method2Inv n fp L k j| :=
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- `matMul n X_U X_L i j` is defeq `∑ k, X_U i k * X_L k j`, matching `matMul_error_bound`.
  show |fl_matMul fp n n n
        (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) i j -
      ∑ k : Fin n,
        ch14ext_method2InvUpper n fp U i k * ch14ext_method2Inv n fp L k j| ≤
      gamma fp (n + 2) *
        ∑ k : Fin n,
          |ch14ext_method2InvUpper n fp U i k| * |ch14ext_method2Inv n fp L k j|
  exact hb.trans (mul_le_mul_of_nonneg_right (gamma_mono fp (by omega) hn2) hw_nonneg)

-- ============================================================
-- Method D (14.23) with the product step also discharged
-- ============================================================

/-- **Higham (14.23), Method D left residual — product step DISCHARGED.**

    The printed `(4γ + 2γ²)` componentwise Method D envelope for the CONCRETE
    computed inverse

        X̂ := fl_matMul fp n n n X_U X_L ,
        X_U := ch14ext_method2InvUpper n fp U ,   X_L := ch14ext_method2Inv n fp L,

    with THREE of the four Method D certificates now discharged internally:

      * the UPPER-triangular inverse LEFT residual (reversal-conjugated Method 2
        loop, `ch14ext_method2Upper_left_residual`);
      * the LOWER-triangular inverse LEFT residual (wave-2 Method 2 loop,
        `ch14ext_method2_left_residual`);
      * the product-formation certificate (this file's
        `ch14ext_methodD_prod_error_flMatMul`).

    Compared with `ch14ext_methodD_left_residual_both`, the `hProd` hypothesis is
    ELIMINATED (X̂ is now the honest floating-point product, not a free matrix).

    The SINGLE remaining hypothesis is the genuine upstream LU backward-error
    certificate `hLU` (Higham Thm 9.3).  Per the file header's strength note, the
    repo has no unconditional `LUBackwardError` producer for arbitrary `A` from
    the GE loop (the concrete-loop chain needs undischarged per-stage
    budget/dominance bounds, and the exact producer would force `A = L̂Û`), so
    `hLU` is retained exactly as Higham states it. -/
theorem ch14ext_methodD_left_residual_prodFree (n : ℕ) (fp : FPModel)
    (A L U : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hLnz : ∀ j : Fin n, L j j ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUnz : ∀ j : Fin n, U j j ≠ 0)
    (hLU : LUBackwardError n A L U (gamma fp (n + 2))) :
    ∀ i j : Fin n,
      |∑ k : Fin n,
          fl_matMul fp n n n
            (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) i k
            * A k j - (if i = j then 1 else 0)| ≤
        (4 * gamma fp (n + 2) + 2 * gamma fp (n + 2) ^ 2) *
          ∑ p : Fin n,
            (∑ q : Fin n, |ch14ext_method2InvUpper n fp U i q|
                * |ch14ext_method2Inv n fp L q p|) *
              (∑ r : Fin n, |L p r| * |U r j|) :=
  ch14ext_methodD_left_residual_both n fp A L U
    (fl_matMul fp n n n
      (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L))
    hn2 hLT hLnz hUT hUnz hLU
    (ch14ext_methodD_prod_error_flMatMul n fp L U hn2)

/-- **Higham (14.23), Method D left residual — product step DISCHARGED, normwise.**

    Infinity-norm companion of `ch14ext_methodD_left_residual_prodFree`: same
    concrete computed inverse `X̂ = fl_matMul fp X_U X_L`, same three internally
    discharged certificates, same single remaining `hLU` hypothesis. -/
theorem ch14ext_methodD_left_residual_prodFree_infNorm (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel) (A L U : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hLnz : ∀ j : Fin n, L j j ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUnz : ∀ j : Fin n, U j j ≠ 0)
    (hLU : LUBackwardError n A L U (gamma fp (n + 2))) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n,
        fl_matMul fp n n n
          (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) i k
          * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp (n + 2) + 2 * gamma fp (n + 2) ^ 2) *
        infNorm (matMul n (absMatrix n (ch14ext_method2InvUpper n fp U))
          (absMatrix n (ch14ext_method2Inv n fp L))) *
          infNorm (matMul n (absMatrix n L) (absMatrix n U)) :=
  ch14ext_methodD_left_residual_both_infNorm n hn0 fp A L U
    (fl_matMul fp n n n
      (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L))
    hn2 hLT hLnz hUT hUnz hLU
    (ch14ext_methodD_prod_error_flMatMul n fp L U hn2)

end LeanFpAnalysis.FP.Ch14Ext
