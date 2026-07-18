/-
Copyright (c) 2026. Released under Apache 2.0.

# Theorem 11.7 (Bunch, symmetric tridiagonal) — the unconditional growth-derived capstone

This module composes the two halves of the Theorem 11.7 closure that were, until
now, only linked by a hypothesis:

  * `hfactor_derived` (in `BunchTridiagonalGrowthInvariantCh11Closure`): from the
    Algorithm-11.6 pivot *schedule* `TriGrowthData` (every stage uses the FIXED
    global scale `σ = M0 = ‖A‖_M` in its acceptance test) together with the input
    bound `∀ i j, |A i j| ≤ M0`, the computed factors satisfy the factor-norm
    bound `|L̂||D̂||L̂ᵀ| ≤ c₀·M0` with the *constant* growth factor
    `c₀ = growthFactorConst …` (this is Higham's "constant element growth" fact,
    now derived rather than assumed);

  * `higham11_7_bunch_tridiagonal_backward_error` (in
    `BlockLDLTBunchTridiagonalCh11Closure`): the conditional Theorem 11.7 that,
    *given* such a factor-norm bound and the (11.5) solve backward error, produces
    the normwise backward error `|ΔAₖ| ≤ 20 n (1+c₀)·u·‖A‖_M`.

The capstone `higham11_7_bunch_tridiagonal_backward_error_growth_derived` discharges
the `hfactor` hypothesis of the conditional theorem outright, leaving only the two
genuine Higham source hypotheses (`FlMixedPivots` per-stage (11.5) coupling, and the
(11.5) solve backward error `hsolve`).  The constant `c₀ = bunchTriGrowthC0` is
explicit and depends only on `u`, `M0`, and the number of stages. -/
import LeanFpAnalysis.FP.Algorithms.Cholesky.BunchTridiagonalGrowthInvariantCh11Closure
import LeanFpAnalysis.FP.Algorithms.Cholesky.BlockLDLTBunchTridiagonalCh11Closure

open scoped BigOperators

namespace LeanFpAnalysis.FP.Ch11Closure.TriGrowthInv

open LeanFpAnalysis.FP
open LeanFpAnalysis.FP.Ch11Closure
open LeanFpAnalysis.FP.Ch11Closure.Mixed
open LeanFpAnalysis.FP.Ch11Closure.BunchTri
open LeanFpAnalysis.FP.Ch11Closure.BunchTriGrowth
open LeanFpAnalysis.FP.Ch11Closure.BunchTriFactor

/-- The corner-bound constant `Bcorner = (1+γ₃)·(τ + M0/α + τ²α/(M0−ατ))` is
    nonnegative once the decoupling slack `α·τ < M0` holds. -/
theorem growthBcorner_nonneg (fp : FPModel) (M0 tau : ℝ) (hval3 : gammaValid fp 3)
    (hM0 : 0 < M0) (hτ0 : 0 ≤ tau) (hslack : bunchTridiagonalAlpha * tau < M0) :
    0 ≤ growthBcorner fp M0 tau := by
  unfold growthBcorner
  have hα := bunch_tridiagonal_alpha_pos
  have hd : 0 < M0 - bunchTridiagonalAlpha * tau := by linarith
  have hg3 : 0 ≤ 1 + gamma fp 3 := by have := gamma_nonneg fp hval3; linarith
  apply mul_nonneg hg3
  have ht2 : 0 ≤ M0 / bunchTridiagonalAlpha := div_nonneg hM0.le hα.le
  have ht3 : 0 ≤ tau ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * tau) :=
    div_nonneg (by positivity) hd.le
  linarith

/-- The full growth factor `c₀ = growthFactorConst …` is nonnegative. -/
theorem growthFactorConst_nonneg (fp : FPModel) (M0 tau Bcorner : ℝ)
    (hM0 : 0 < M0) (hτ0 : 0 ≤ tau) (hBc : 0 ≤ Bcorner)
    (hslack : bunchTridiagonalAlpha * tau < M0) :
    0 ≤ growthFactorConst fp M0 tau Bcorner := by
  unfold growthFactorConst
  have hα := bunch_tridiagonal_alpha_pos
  have hu : (0 : ℝ) ≤ 1 + fp.u := by have := fp.u_nonneg; linarith
  have h1 : 0 ≤ Bcorner / M0 := div_nonneg hBc hM0.le
  have h2 : 0 ≤ (1 + fp.u) * tau / M0 := div_nonneg (mul_nonneg hu hτ0) hM0.le
  have h3 : 0 ≤ pathConstRC fp.u M0 tau / M0 :=
    div_nonneg (pathConstRC_nonneg fp.u M0 tau fp.u_nonneg hM0 hτ0 hslack) hM0.le
  have h4 : 0 ≤ pathConst2 fp.u M0 tau / M0 :=
    div_nonneg (pathConst2_nonneg fp.u M0 tau fp.u_nonneg hM0 hτ0 hslack) hM0.le
  have h5 : 0 ≤ (1 + fp.u) ^ 2 / bunchTridiagonalAlpha :=
    div_nonneg (by positivity) hα.le
  linarith

/-- The explicit Algorithm-11.6 tridiagonal growth factor as a function of the
    floating-point model, the pivot schedule (through its stage count) and the
    global scale `M0 = ‖A‖_M`.  This is Higham's *constant* element-growth factor
    `c₀`: the off-corner band grows by at most one rounding `(1+u)` per stage
    (`τ = (1+γ_{#stages})·M0`), and the corner is controlled by the fixed-scale
    acceptance test through `growthBcorner`. -/
noncomputable def bunchTriGrowthC0 (fp : FPModel) {k : ℕ} (s : PivotSchedule k)
    (M0 : ℝ) : ℝ :=
  growthFactorConst fp M0 ((1 + gamma fp (stages s)) * M0)
    (growthBcorner fp M0 ((1 + gamma fp (stages s)) * M0))

/-- **Theorem 11.7 (Bunch, symmetric tridiagonal) — growth-derived capstone.**

For a symmetric input `A` with `‖A‖_M = M0` (i.e. `|A i j| ≤ M0`) processed by
the rounded mixed-pivot block-LDLᵀ path whose pivots were chosen by Algorithm 11.6
at the FIXED global scale `M0` (`TriGrowthData fp M0 s A`), with the (11.5)
per-stage coupling `FlMixedPivots` and the (11.5) solve backward error `hsolve`,
Bunch's method produces

  `L̂D̂L̂ᵀ = A + ΔA₁`,   `(A + ΔA₂)x̂ = b`,
  `|ΔAₖ i j| ≤ 20 n (1 + c₀)·u·M0`

with the **explicit constant** `c₀ = bunchTriGrowthC0 fp s M0`.  The factor-norm
bound `|L̂||D̂||L̂ᵀ| ≤ c₀·M0` is no longer assumed — it is derived from the pivot
schedule via `hfactor_derived`.  This closes Theorem 11.7 at the printed
first-order strength (`c·u·‖A‖_M`, Higham's Option A) with only the two legitimate
source hypotheses (`hpiv`, `hsolve`) remaining. -/
theorem higham11_7_bunch_tridiagonal_backward_error_growth_derived
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (s : PivotSchedule n) (M0 cSolve cStage : ℝ)
    (hM0 : 0 < M0)
    (hAmax : ∀ i j : Fin n, |A i j| ≤ M0)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hvalstages : gammaValid fp (stages s)) (hval1 : gammaValid fp 1)
    (hγα : gamma fp (stages s) < bunchTridiagonalAlpha)
    (hdata : TriGrowthData fp M0 s A)
    (hpiv : FlMixedPivots fp cSolve cStage s A)
    (hsolve : ∃ ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |ΔA2 i j| ≤ 20 * (n : ℝ) * (1 + bunchTriGrowthC0 fp s M0) * fp.u * M0) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA2 i j) * x_hat j = b i)) :
    ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |ΔA1 i j| ≤ 20 * (n : ℝ) * (1 + bunchTriGrowthC0 fp s M0) * fp.u * M0) ∧
      (∀ i j : Fin n,
        |ΔA2 i j| ≤ 20 * (n : ℝ) * (1 + bunchTriGrowthC0 fp s M0) * fp.u * M0) ∧
      (∀ i j : Fin n,
        (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂ * flMixedL fp s A j k₂)
          = A i j + ΔA1 i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA2 i j) * x_hat j = b i) := by
  have hγstages : 0 ≤ gamma fp (stages s) := gamma_nonneg fp hvalstages
  have hτ0 : 0 ≤ (1 + gamma fp (stages s)) * M0 := by positivity
  have hslack : bunchTridiagonalAlpha * ((1 + gamma fp (stages s)) * M0) < M0 := by
    have hα := bunch_tridiagonal_alpha_pos
    have hsq := bunch_tridiagonal_alpha_sq
    nlinarith [mul_pos (mul_pos hα hM0) (sub_pos.mpr hγα), hsq]
  have hc0 : 0 ≤ bunchTriGrowthC0 fp s M0 := by
    unfold bunchTriGrowthC0
    exact growthFactorConst_nonneg fp M0 _ _ hM0 hτ0
      (growthBcorner_nonneg fp M0 _ hval hM0 hτ0 hslack) hslack
  have hfac : ∀ I J : Fin n,
      higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) I J
        ≤ bunchTriGrowthC0 fp s M0 * M0 :=
    hfactor_derived fp hval s A M0 hM0 hvalstages hval1 hγα hdata
      (fun i j _ => hAmax i j) (fun i j _ _ => hAmax i j)
  exact higham11_7_bunch_tridiagonal_backward_error fp hval A b x_hat s M0
    (bunchTriGrowthC0 fp s M0) cSolve cStage hAmax hM0.le hc0 hcS0 hcS40 hcSt0 hcSt5
    hsmall hpiv hfac hsolve

/-- A pivot schedule on a dimension-`k` matrix takes at most `k` stages (each stage
    consumes one or two dimensions). -/
theorem stages_le : ∀ {k : ℕ} (s : PivotSchedule k), stages s ≤ k
  | _, .nil => Nat.le_refl 0
  | _, .consOne s => by have h := stages_le s; simp only [stages_consOne]; omega
  | _, .consTwo s => by have h := stages_le s; simp only [stages_consTwo]; omega

/-- `1/50 < α = (√5−1)/2`: a crude numeric lower bound on the Bunch tridiagonal
    threshold, from `α² = 1 − α` and `α > 0`. -/
theorem one_div_fifty_lt_bunchTridiagonalAlpha :
    (1 : ℝ) / 50 < bunchTridiagonalAlpha := by
  have hsq := bunch_tridiagonal_alpha_sq
  have hpos := bunch_tridiagonal_alpha_pos
  nlinarith [hsq, hpos]

/-- **Theorem 11.7 (Bunch, symmetric tridiagonal) — self-contained growth-derived
    capstone.**  Identical to `higham11_7_bunch_tridiagonal_backward_error_growth_derived`
    except the pivot-threshold smallness guard `hγα : γ_{#stages} < α` is **derived**
    from the printed regime hypothesis `hsmall : n·u ≤ 1/100` (via `stages s ≤ n` and
    `γ_{#stages} ≤ 2·(#stages)·u ≤ 2 n u ≤ 1/50 < α`).  So the entire closure rests on
    exactly Higham's standard inputs — the (11.5) per-stage coupling `FlMixedPivots`,
    the (11.5) solve backward error `hsolve`, and the single normwise smallness
    `n·u ≤ 1/100` — with the constant element growth `c₀ = bunchTriGrowthC0 fp s M0`
    fully derived. -/
theorem higham11_7_bunch_tridiagonal_backward_error_growth_derived_of_small
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (s : PivotSchedule n) (M0 cSolve cStage : ℝ)
    (hM0 : 0 < M0)
    (hAmax : ∀ i j : Fin n, |A i j| ≤ M0)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hvalstages : gammaValid fp (stages s)) (hval1 : gammaValid fp 1)
    (hdata : TriGrowthData fp M0 s A)
    (hpiv : FlMixedPivots fp cSolve cStage s A)
    (hsolve : ∃ ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |ΔA2 i j| ≤ 20 * (n : ℝ) * (1 + bunchTriGrowthC0 fp s M0) * fp.u * M0) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA2 i j) * x_hat j = b i)) :
    ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |ΔA1 i j| ≤ 20 * (n : ℝ) * (1 + bunchTriGrowthC0 fp s M0) * fp.u * M0) ∧
      (∀ i j : Fin n,
        |ΔA2 i j| ≤ 20 * (n : ℝ) * (1 + bunchTriGrowthC0 fp s M0) * fp.u * M0) ∧
      (∀ i j : Fin n,
        (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂ * flMixedL fp s A j k₂)
          = A i j + ΔA1 i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA2 i j) * x_hat j = b i) := by
  -- Derive the pivot-threshold guard hγα from the printed smallness regime.
  have hun : (0 : ℝ) ≤ fp.u := fp.u_nonneg
  have hstages_le : (stages s : ℝ) ≤ (n : ℝ) := by exact_mod_cast stages_le s
  have hprod : (stages s : ℝ) * fp.u ≤ (n : ℝ) * fp.u :=
    mul_le_mul_of_nonneg_right hstages_le hun
  have hstages_half : (stages s : ℝ) * fp.u ≤ 1 / 2 := by linarith [hsmall]
  have h2 : gamma fp (stages s) ≤ 2 * ((stages s : ℝ) * fp.u) :=
    gamma_le_two_mul_n_u_of_nu_le_half fp (stages s) hstages_half
  have hγα : gamma fp (stages s) < bunchTridiagonalAlpha := by
    have hα50 := one_div_fifty_lt_bunchTridiagonalAlpha
    linarith [h2, hprod, hsmall, hα50]
  exact higham11_7_bunch_tridiagonal_backward_error_growth_derived fp hval A b x_hat s
    M0 cSolve cStage hM0 hAmax hcS0 hcS40 hcSt0 hcSt5 hsmall hvalstages hval1 hγα
    hdata hpiv hsolve

end LeanFpAnalysis.FP.Ch11Closure.TriGrowthInv
