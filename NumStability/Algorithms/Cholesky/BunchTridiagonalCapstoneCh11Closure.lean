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
import NumStability.Algorithms.Cholesky.BunchTridiagonalGrowthInvariantCh11Closure
import NumStability.Algorithms.Cholesky.BlockLDLTBunchTridiagonalCh11Closure
import NumStability.Algorithms.Cholesky.BunchTridiagonalSparseFactorCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.TriGrowthInv

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed
open NumStability.Ch11Closure.BunchTri
open NumStability.Ch11Closure.BunchTriGrowth
open NumStability.Ch11Closure.BunchTriFactor
open NumStability.Ch11Closure.Solve
open NumStability.Ch11Closure.BunchTriActual
open NumStability.Ch11Closure.SparseSolve
open NumStability.Ch11Closure.SparseFactor

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

/-! ## Actual schedule and actual `2 × 2` middle solve

The preceding historical capstones accept the complete solve endpoint as an
input.  The next theorem instead runs the schedule-local scalar/GEPP producer
from `BunchTridiagonalActualSolveCh11Closure`.  Its result is the genuine
computed solve returned by the rounded outer substitutions and actual middle
block solves; no `hsolve`, global middle residual, or local `(11.5)` witness is
an assumption.
-/

/-- **Theorem 11.7, actual Algorithm 11.6 schedule and middle-solve producer.**
The printed pivot schedule is computed by `bunchTridiagonalSchedule`; accepted
`2 × 2` blocks are solved by the actual rounded GEPP kernel.  The only solve
domain condition is `BunchMiddleSolveNoBreakdown`, requiring each computed
second GEPP pivot to be nonzero.  The remaining `FlMixedPivots` premise belongs
to the rounded factorization path, not to the linear-system solve.

This theorem deliberately exposes the current dense outer-substitution
coefficient `gamma fp n`.  Replacing those dense sweeps by a support-aware
block-bidiagonal sweep is the remaining step needed to turn this exact radius
into Higham's dimension-independent printed constant. -/
theorem higham11_7_bunch_tridiagonal_actual_schedule_middle_solve
    (fp : FPModel) (hval9 : gammaValid fp 9)
    {n : ℕ} (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvaln : gammaValid fp n)
    (M0 : ℝ) (hM0 : 0 < M0)
    (hAtri : IsSymTridiagonal n A)
    (hAmax : ∀ i j : Fin n, |A i j| ≤ M0)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hsmall9 : (9 : ℝ) * fp.u ≤ 1 / 2)
    (hscalarNB : BunchTridiagonalScalarNoBreakdown fp
      (bunchTridiagonalSchedule fp M0 A) A)
    (hpiv : FlMixedPivots fp 36 5 (bunchTridiagonalSchedule fp M0 A) A)
    (hmiddleNB : BunchMiddleSolveNoBreakdown fp
      (bunchTridiagonalSchedule fp M0 A) A) :
    let s := bunchTridiagonalSchedule fp M0 A
    let c0 := bunchTriGrowthC0 fp s M0
    ∃ w_hat : Fin n → ℝ, ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |ΔA1 i j| ≤ pPoly n * fp.u * ((1 + c0) * M0)) ∧
      (∀ i j : Fin n,
        |ΔA2 i j| ≤ pPoly n * fp.u * ((1 + c0) * M0)
          + ((2 * gamma fp n + gamma fp n ^ 2)
              + (1 + 2 * gamma fp n + gamma fp n ^ 2) * (36 * fp.u))
            * (c0 * M0)) ∧
      (∀ i j : Fin n,
        (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂ *
          flMixedL fp s A j k₂) = A i j + ΔA1 i j) ∧
      (∀ i : Fin n,
        ∑ j : Fin n, (A i j + ΔA2 i j) *
          fl_backSub fp n (fun r c => flMixedL fp s A c r) w_hat j = b i) := by
  dsimp only
  let s := bunchTridiagonalSchedule fp M0 A
  have hdata : TriGrowthData fp M0 s A :=
    TriGrowthData_bunchTridiagonalSchedule fp M0 hM0.le A hAtri hscalarNB
  have hval3 : gammaValid fp 3 := gammaValid_mono fp (by omega) hval9
  have hval1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hval9
  have hvalstages : gammaValid fp (stages s) :=
    gammaValid_mono fp (stages_le s) hvaln
  have hstages_le : (stages s : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast stages_le s
  have hprod : (stages s : ℝ) * fp.u ≤ (n : ℝ) * fp.u :=
    mul_le_mul_of_nonneg_right hstages_le fp.u_nonneg
  have hstageHalf : (stages s : ℝ) * fp.u ≤ 1 / 2 := by
    linarith [hsmall, hprod]
  have hgammaStages : gamma fp (stages s) ≤
      2 * ((stages s : ℝ) * fp.u) :=
    gamma_le_two_mul_n_u_of_nu_le_half fp (stages s) hstageHalf
  have hgammaAlpha : gamma fp (stages s) < bunchTridiagonalAlpha := by
    linarith [hgammaStages, hprod, hsmall,
      one_div_fifty_lt_bunchTridiagonalAlpha]
  let tau : ℝ := (1 + gamma fp (stages s)) * M0
  have htau0 : 0 ≤ tau := by
    dsimp [tau]
    exact mul_nonneg (by linarith [gamma_nonneg fp hvalstages]) hM0.le
  have hslack : bunchTridiagonalAlpha * tau < M0 := by
    dsimp [tau]
    have hα := bunch_tridiagonal_alpha_pos
    have hsq := bunch_tridiagonal_alpha_sq
    nlinarith [mul_pos (mul_pos hα hM0) (sub_pos.mpr hgammaAlpha), hsq]
  have hpow : (1 + fp.u) ^ stages s ≤ 1 + gamma fp (stages s) :=
    one_add_u_pow_le fp (le_refl (stages s)) hvalstages hval1
  have hbudget : (1 + fp.u) ^ stages s * M0 ≤ tau := by
    dsimp [tau]
    exact mul_le_mul_of_nonneg_right hpow hM0.le
  have hbounded : TriGrowthBounded fp M0 tau s A :=
    growth_offcorner fp M0 tau s A M0 hdata
      (fun i j _ => hAmax i j) hM0.le hbudget
  have hblocks : MixedMiddleSolveHigham115Blocks fp 36 s A
      (fl_forwardSub fp n (flMixedL fp s A) b) :=
    mixedMiddleSolveHigham115Blocks_of_bunch_actual fp hval9 hsmall9
      M0 tau hM0 htau0 hslack s A
      (fl_forwardSub fp n (flMixedL fp s A) b) hbounded hmiddleNB
  have hgamma1 : gamma fp 1 ≤ 36 * fp.u := by
    have huHalf : (1 : ℝ) * fp.u ≤ 1 / 2 := by
      nlinarith [hsmall9, fp.u_nonneg]
    have hg := gamma_le_two_mul_n_u_of_nu_le_half fp 1 (by simpa using huHalf)
    calc
      gamma fp 1 ≤ 2 * ((1 : ℝ) * fp.u) := by simpa using hg
      _ ≤ 36 * fp.u := by nlinarith [fp.u_nonneg]
  have hc0 : 0 ≤ bunchTriGrowthC0 fp s M0 := by
    unfold bunchTriGrowthC0
    exact growthFactorConst_nonneg fp M0 _ _ hM0 htau0
      (growthBcorner_nonneg fp M0 _ hval3 hM0 htau0 hslack) hslack
  have hfactor : ∀ I J : Fin n,
      higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A)
        (flMixedD fp s A) I J ≤ bunchTriGrowthC0 fp s M0 * M0 :=
    hfactor_derived fp hval3 s A M0 hM0 hvalstages hval1 hgammaAlpha hdata
      (fun i j _ => hAmax i j) (fun i j _ _ => hAmax i j)
  exact higham11_7_bunch_tridiagonal_solve_backward_error_normwise_of_higham115_middle
    fp hval3 s A b hvaln M0 (bunchTriGrowthC0 fp s M0) 36 5 (36 * fp.u)
    hAmax hM0.le hc0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hgamma1 (le_refl _) hsmall hpiv hfactor hblocks

/-! ## The support-aware source endpoint

The next endpoint replaces both dense outer substitutions by the actual
bandwidth-two kernels from `BunchTridiagonalSparseSolveCh11Closure`.  Thus the
solve-chain contribution is controlled by `bunchTriSparseSolveCoeff`, which is
independent of `n`; there is no `gamma fp n` premise or term. -/

/-- **Theorem 11.7, computed Algorithm 11.6 schedule and support-aware solve.**
The schedule, tridiagonal growth bound, factor-product bridge, actual rounded
2x2 middle solves, and sparse outer substitutions are all produced inside the
theorem.  No global solve residual, local (11.5) solve witness, or dense
triangular-solve hypothesis is accepted.

The first summand in the displayed radius is the repository's existing mixed
factorization envelope.  The second summand is the newly closed solve-side
constant: `C_sparse c0 M0`, with `C_sparse` independent of the dimension. -/
theorem higham11_7_bunch_tridiagonal_actual_schedule_sparse_solve
    (fp : FPModel) (hval9 : gammaValid fp 9)
    {n : ℕ} (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (M0 : ℝ) (hM0 : 0 < M0)
    (hAtri : IsSymTridiagonal n A)
    (hAmax : ∀ i j : Fin n, |A i j| ≤ M0)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hsmall9 : (9 : ℝ) * fp.u ≤ 1 / 2)
    (hscalarNB : BunchTridiagonalScalarNoBreakdown fp
      (bunchTridiagonalSchedule fp M0 A) A)
    (hpiv : FlMixedPivots fp 36 5 (bunchTridiagonalSchedule fp M0 A) A)
    (hmiddleNB : BunchMiddleSolveNoBreakdown fp
      (bunchTridiagonalSchedule fp M0 A) A) :
    let s := bunchTridiagonalSchedule fp M0 A
    let c0 := bunchTriGrowthC0 fp s M0
    ∃ w : Fin n → ℝ, ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |ΔA1 i j| ≤ pPoly n * fp.u * ((1 + c0) * M0)) ∧
      (∀ i j : Fin n,
        |ΔA2 i j| ≤ pPoly n * fp.u * ((1 + c0) * M0) +
          bunchTriSparseSolveCoeff fp * (c0 * M0)) ∧
      (∀ i j : Fin n,
        (∑ p : Fin n, ∑ q : Fin n,
          flMixedL fp s A i p * flMixedD fp s A p q * flMixedL fp s A j q) =
            A i j + ΔA1 i j) ∧
      (∀ i : Fin n,
        ∑ j : Fin n, (A i j + ΔA2 i j) *
          flBand2BackSub fp n (fun r c => flMixedL fp s A c r) w j = b i) := by
  dsimp only
  let s := bunchTridiagonalSchedule fp M0 A
  have hdata : TriGrowthData fp M0 s A :=
    TriGrowthData_bunchTridiagonalSchedule fp M0 hM0.le A hAtri hscalarNB
  have hval3 : gammaValid fp 3 := gammaValid_mono fp (by omega) hval9
  have hval1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hval9
  have hstages_le : (stages s : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast stages_le s
  have hprod : (stages s : ℝ) * fp.u ≤ (n : ℝ) * fp.u :=
    mul_le_mul_of_nonneg_right hstages_le fp.u_nonneg
  have hvalstages : gammaValid fp (stages s) := by
    unfold gammaValid
    linarith [hprod, hsmall]
  have hstageHalf : (stages s : ℝ) * fp.u ≤ 1 / 2 := by
    linarith [hprod, hsmall]
  have hgammaStages : gamma fp (stages s) ≤
      2 * ((stages s : ℝ) * fp.u) :=
    gamma_le_two_mul_n_u_of_nu_le_half fp (stages s) hstageHalf
  have hgammaAlpha : gamma fp (stages s) < bunchTridiagonalAlpha := by
    linarith [hgammaStages, hprod, hsmall,
      one_div_fifty_lt_bunchTridiagonalAlpha]
  let tau : ℝ := (1 + gamma fp (stages s)) * M0
  have htau0 : 0 ≤ tau := by
    dsimp [tau]
    exact mul_nonneg (by linarith [gamma_nonneg fp hvalstages]) hM0.le
  have hslack : bunchTridiagonalAlpha * tau < M0 := by
    dsimp [tau]
    have hα := bunch_tridiagonal_alpha_pos
    have hsq := bunch_tridiagonal_alpha_sq
    nlinarith [mul_pos (mul_pos hα hM0) (sub_pos.mpr hgammaAlpha), hsq]
  have hpow : (1 + fp.u) ^ stages s ≤ 1 + gamma fp (stages s) :=
    one_add_u_pow_le fp (le_refl (stages s)) hvalstages hval1
  have hbudget : (1 + fp.u) ^ stages s * M0 ≤ tau := by
    dsimp [tau]
    exact mul_le_mul_of_nonneg_right hpow hM0.le
  have hbounded : TriGrowthBounded fp M0 tau s A :=
    growth_offcorner fp M0 tau s A M0 hdata
      (fun i j _ => hAmax i j) hM0.le hbudget
  have hc0 : 0 ≤ bunchTriGrowthC0 fp s M0 := by
    unfold bunchTriGrowthC0
    exact growthFactorConst_nonneg fp M0 _ _ hM0 htau0
      (growthBcorner_nonneg fp M0 _ hval3 hM0 htau0 hslack) hslack
  have hfactor : ∀ I J : Fin n,
      higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A)
        (flMixedD fp s A) I J ≤ bunchTriGrowthC0 fp s M0 * M0 :=
    hfactor_derived fp hval3 s A M0 hM0 hvalstages hval1 hgammaAlpha hdata
      (fun i j _ => hAmax i j) (fun i j _ _ => hAmax i j)
  obtain ⟨w, ΔS, hΔS, hsolveFactor⟩ :=
    bunch_tridiagonal_sparse_actual_solve_chain_norm_bridge
      fp hval9 hsmall9 s A b M0 tau (bunchTriGrowthC0 fp s M0)
      hM0 htau0 hslack hdata hbounded hmiddleNB hfactor
  let Afact : Fin n → Fin n → ℝ := fun i j =>
    ∑ p : Fin n, ∑ q : Fin n,
      flMixedL fp s A i p * flMixedD fp s A p q * flMixedL fp s A j q
  let Bfactor : Fin n → Fin n → ℝ :=
    higham11_3_printedFirstOrderBound n A (flMixedL fp s A)
      (flMixedD fp s A) id (pPoly n) fp.u
  have hfactorBound : ∀ i j : Fin n, |Afact i j - A i j| ≤ Bfactor i j := by
    intro i j
    exact le_trans (fl_blockLDLT_mixed_bound fp hval3 36 5 s A hpiv i j)
      (flMixed_envelope_le_printed fp hval3 36 5
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        s A hsmall hpiv i j)
  have hpu : 0 ≤ pPoly n * fp.u :=
    mul_nonneg (by unfold pPoly; positivity) fp.u_nonneg
  have hfactorRelax : ∀ i j : Fin n,
      Bfactor i j ≤ pPoly n * fp.u *
        ((1 + bunchTriGrowthC0 fp s M0) * M0) := by
    intro i j
    unfold Bfactor higham11_3_printedFirstOrderBound
    refine mul_le_mul_of_nonneg_left ?_ hpu
    have hsum : |A (id i) (id j)| +
        higham11_4_bunchKaufmanProductEntry n
          (flMixedL fp s A) (flMixedD fp s A) i j
        ≤ M0 + bunchTriGrowthC0 fp s M0 * M0 :=
      add_le_add (hAmax i j) (hfactor i j)
    calc
      |A (id i) (id j)| + higham11_4_bunchKaufmanProductEntry n
          (flMixedL fp s A) (flMixedD fp s A) i j
          ≤ M0 + bunchTriGrowthC0 fp s M0 * M0 := hsum
      _ = (1 + bunchTriGrowthC0 fp s M0) * M0 := by ring
  obtain ⟨ΔA2, hΔA2, hsource⟩ :=
    higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals
      n A Afact ΔS Bfactor
      (fun _ _ => bunchTriSparseSolveCoeff fp *
        (bunchTriGrowthC0 fp s M0 * M0))
      b (flBand2BackSub fp n (fun r c => flMixedL fp s A c r) w)
      hfactorBound hΔS (by intro i; simpa [Afact] using hsolveFactor i)
  refine ⟨w, fun i j => Afact i j - A i j, ΔA2, ?_, ?_, ?_, hsource⟩
  · intro i j
    exact (hfactorBound i j).trans (hfactorRelax i j)
  · intro i j
    have h := (hΔA2 i j).trans
      (add_le_add (hfactorRelax i j)
        (le_refl (bunchTriSparseSolveCoeff fp *
          (bunchTriGrowthC0 fp s M0 * M0))))
    simpa [s] using h
  · intro i j
    show Afact i j = A i j + (Afact i j - A i j)
    ring

/-! ## Fully support-aware factorization-and-solve endpoint -/

/-- **Theorem 11.7, actual support-aware Algorithm 11.6 implementation.**

`skipZeroSubFP fp` is the concrete sparse arithmetic policy: it delegates every
genuine operation to `fp` and copies an entry when tridiagonal structure makes
the Schur subtrahend exactly zero.  This is itself an `FPModel` with the same
unit roundoff.  The theorem computes the Bunch schedule, its rounded explicit-
inverse factors, the rounded block middle solves, and both bandwidth-two outer
substitutions.

The factor radius `bunchTriSparseFactorRadius fp M0` and the solve coefficient
`bunchTriSparseSolveCoeff q` contain no dimension parameter.  In particular,
there is no `FlMixedPivots` premise and no generic `pPoly n = 20n` envelope. -/
theorem higham11_7_bunch_tridiagonal_support_aware
    (fp : FPModel) (hval9 : gammaValid fp 9)
    {n : ℕ} (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (M0 : ℝ) (hM0 : 0 < M0)
    (hAtri : IsSymTridiagonal n A)
    (hAmax : ∀ i j : Fin n, |A i j| ≤ M0)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hsmall9 : (9 : ℝ) * fp.u ≤ 1 / 2)
    (hscalarNB :
      let q := skipZeroSubFP fp
      BunchTridiagonalScalarNoBreakdown q (bunchTridiagonalSchedule q M0 A) A)
    (hmiddleNB :
      let q := skipZeroSubFP fp
      BunchMiddleSolveNoBreakdown q (bunchTridiagonalSchedule q M0 A) A) :
    let q := skipZeroSubFP fp
    let s := bunchTridiagonalSchedule q M0 A
    let c0 := bunchTriGrowthC0 q s M0
    ∃ w : Fin n → ℝ, ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j| ≤ bunchTriSparseFactorRadius fp M0) ∧
      (∀ i j : Fin n, |ΔA2 i j| ≤ bunchTriSparseFactorRadius fp M0 +
        bunchTriSparseSolveCoeff q * (c0 * M0)) ∧
      (∀ i j : Fin n,
        (∑ p : Fin n, ∑ r : Fin n,
          flMixedL q s A i p * flMixedD q s A p r * flMixedL q s A j r) =
            A i j + ΔA1 i j) ∧
      (∀ i : Fin n,
        ∑ j : Fin n, (A i j + ΔA2 i j) *
          flBand2BackSub q n (fun r c => flMixedL q s A c r) w j = b i) := by
  dsimp only
  let q := skipZeroSubFP fp
  let s := bunchTridiagonalSchedule q M0 A
  have hval3 : gammaValid q 3 := gammaValid_mono q (by omega) hval9
  have hval1 : gammaValid q 1 := gammaValid_mono q (by omega) hval9
  have hdata : TriGrowthData q M0 s A :=
    TriGrowthData_bunchTridiagonalSchedule q M0 hM0.le A hAtri hscalarNB
  have hstages_le : (stages s : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast stages_le s
  have hprod : (stages s : ℝ) * q.u ≤ (n : ℝ) * fp.u := by
    change (stages s : ℝ) * fp.u ≤ (n : ℝ) * fp.u
    exact mul_le_mul_of_nonneg_right hstages_le fp.u_nonneg
  have hvalstages : gammaValid q (stages s) := by
    unfold gammaValid
    linarith [hprod, hsmall]
  have hstageHalf : (stages s : ℝ) * q.u ≤ 1 / 2 := by
    linarith [hprod, hsmall]
  have hgammaStages : gamma q (stages s) ≤ 2 * ((stages s : ℝ) * q.u) :=
    gamma_le_two_mul_n_u_of_nu_le_half q (stages s) hstageHalf
  have hgammaCap : gamma q (stages s) ≤ 1 / 50 := by
    change gamma q (stages s) ≤ 1 / 50
    linarith [hgammaStages, hprod, hsmall]
  have hgammaAlpha : gamma q (stages s) < bunchTridiagonalAlpha :=
    lt_of_le_of_lt hgammaCap one_div_fifty_lt_bunchTridiagonalAlpha
  have hpow : (1 + q.u) ^ stages s ≤ 1 + gamma q (stages s) :=
    one_add_u_pow_le q (le_refl (stages s)) hvalstages hval1
  have hbudget : (1 + q.u) ^ stages s * M0 ≤ bunchTriTauCap M0 := by
    have h1 : (1 + q.u) ^ stages s ≤ (51 / 50 : ℝ) := by linarith [hpow, hgammaCap]
    unfold bunchTriTauCap
    exact mul_le_mul_of_nonneg_right h1 hM0.le
  have hbounded : TriGrowthBounded q M0 (bunchTriTauCap M0) s A :=
    growth_offcorner q M0 (bunchTriTauCap M0) s A M0 hdata
      (fun i j _ => hAmax i j) hM0.le hbudget
  have hc0 : 0 ≤ bunchTriGrowthC0 q s M0 := by
    unfold bunchTriGrowthC0
    exact growthFactorConst_nonneg q M0 _ _ hM0
      (by
        exact mul_nonneg (by linarith [gamma_nonneg q hvalstages]) hM0.le)
      (growthBcorner_nonneg q M0 _ hval3 hM0
        (by exact mul_nonneg (by linarith [gamma_nonneg q hvalstages]) hM0.le)
        (by
          have hα := bunch_tridiagonal_alpha_pos
          have hαsq := bunch_tridiagonal_alpha_sq
          nlinarith [mul_pos (mul_pos hα hM0) (sub_pos.mpr hgammaAlpha), hαsq]))
      (by
        have hα := bunch_tridiagonal_alpha_pos
        have hαsq := bunch_tridiagonal_alpha_sq
        nlinarith [mul_pos (mul_pos hα hM0) (sub_pos.mpr hgammaAlpha), hαsq])
  have hfactor : ∀ I J : Fin n,
      higham11_4_bunchKaufmanProductEntry n (flMixedL q s A) (flMixedD q s A) I J
        ≤ bunchTriGrowthC0 q s M0 * M0 :=
    hfactor_derived q hval3 s A M0 hM0 hvalstages hval1 hgammaAlpha hdata
      (fun i j _ => hAmax i j) (fun i j _ _ => hAmax i j)
  obtain ⟨w, ΔS, hΔS, hsolveFactor⟩ :=
    bunch_tridiagonal_sparse_actual_solve_chain_norm_bridge
      q hval9 hsmall9 s A b M0 (bunchTriTauCap M0) (bunchTriGrowthC0 q s M0)
      hM0 (bunchTriTauCap_nonneg M0 hM0) (bunchTriTauCap_slack M0 hM0)
      hdata hbounded hmiddleNB hfactor
  let Afact : Fin n → Fin n → ℝ := fun i j =>
    ∑ p : Fin n, ∑ r : Fin n,
      flMixedL q s A i p * flMixedD q s A p r * flMixedL q s A j r
  have huHalf : fp.u ≤ 1 / 2 := by nlinarith [hsmall9, fp.u_nonneg]
  have hfactorBound : ∀ i j : Fin n,
      |Afact i j - A i j| ≤ bunchTriSparseFactorRadius fp M0 := by
    intro i j
    exact bunch_tridiagonal_sparse_factor_residual fp hval3 huHalf M0 hM0
      s A hbounded i j
  obtain ⟨ΔA2, hΔA2, hsource⟩ :=
    higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals
      n A Afact ΔS (fun _ _ => bunchTriSparseFactorRadius fp M0)
      (fun _ _ => bunchTriSparseSolveCoeff q * (bunchTriGrowthC0 q s M0 * M0))
      b (flBand2BackSub q n (fun r c => flMixedL q s A c r) w)
      hfactorBound hΔS (by intro i; simpa [Afact] using hsolveFactor i)
  refine ⟨w, fun i j => Afact i j - A i j, ΔA2, hfactorBound, ?_, ?_, hsource⟩
  · intro i j
    exact (hΔA2 i j).trans (le_refl _)
  · intro i j
    show Afact i j = A i j + (Afact i j - A i j)
    ring

end NumStability.Ch11Closure.TriGrowthInv
