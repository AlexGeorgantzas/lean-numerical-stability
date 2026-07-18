/-
Chapter 11, Theorem 11.7 — **bounded element growth for Bunch's symmetric
tridiagonal pivoting (Algorithm 11.6), the derivation of `hfactor`.**

This module begins the multi-session derivation that discharges the tridiagonal
factor-norm hypothesis `hfactor` of `higham11_7_bunch_tridiagonal_backward_error`
*from the algorithm* (Route B of
`docs/source_coverage/higham_ch11_thm117_growth_blueprint.md`), replacing the
assumed `TriPivotData`.

Higham's Algorithm 11.6 uses a **fixed** scale `σ = ‖A‖_M =: M₀`, computed once at
the start, in every stage's pivot test.  With that fixed scale the element growth
is bounded by the **constant** `K = (1+γ₃)(1 + 1/α)` (α = (√5−1)/2), independent
of `n`, because:

  * each reduced-matrix corner is `(a non-corner diagonal ≤ M₀) − (correction)`
    (no compounding — the correction uses the fixed `M₀`, not the grown corner);
  * the per-step correction is `≤ M₀/α` for both pivot sizes
    (`flSchurCompl_corner_bound`, `flSchurCompl2_corner_bound`, already proved).

This file (session 1) establishes the foundational pieces:
  * `growthK` and its positivity;
  * `twoByTwo_corner_small` — a 2×2 pivot is chosen only when the corner is small
    (`|a₁₁| < α·M₀`), so a grown corner always forces a 1×1 step;
  * `oneByOne_corner_growth` / `twoByTwo_corner_growth` — the single-stage corner
    growth bounds at the fixed scale `σ = M₀`, packaging the existing per-step
    corner bounds into the uniform `≤ K·M₀` form.

The schedule-level induction (the growth invariant) and the product-entry
assembly are the subsequent sessions (see the blueprint).

No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import LeanFpAnalysis.FP.Algorithms.Cholesky.BunchTridiagonalFactorBoundCh11Closure

open scoped BigOperators

namespace LeanFpAnalysis.FP.Ch11Closure.TriGrowthInv

open LeanFpAnalysis.FP
open LeanFpAnalysis.FP.Ch11Closure
open LeanFpAnalysis.FP.Ch11Closure.Mixed
open LeanFpAnalysis.FP.Ch11Closure.BunchTri
open LeanFpAnalysis.FP.Ch11Closure.BunchTriGrowth

/-- The tridiagonal-Bunch growth constant `K = (1+γ₃)(1 + 1/α)` (≈ 2.618·(1+γ₃)),
independent of the matrix dimension. -/
noncomputable def growthK (fp : FPModel) : ℝ :=
  (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha)

theorem growthK_pos (fp : FPModel) (hval : gammaValid fp 3) : 0 < growthK fp := by
  have hγ : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have hinv : 0 < 1 / bunchTridiagonalAlpha := by positivity
  have : 0 < 1 + gamma fp 3 := by linarith
  have : 0 < 1 + 1 / bunchTridiagonalAlpha := by linarith
  unfold growthK; positivity

/-- **2×2 ⇒ small corner.**  If Algorithm 11.6 with the fixed scale `σ = M₀`
selects a 2×2 pivot, the pivot corner is small: `|a₁₁| < α·M₀ < M₀`.  Hence a
grown (`> α·M₀`) corner always triggers a 1×1 step — the mechanism that stops the
growth from compounding. -/
theorem twoByTwo_corner_small (M0 a11 a21 : ℝ) (hM0 : 0 < M0)
    (ha21 : |a21| ≤ M0)
    (hchoice : BunchTridiagonalPivotChoice M0 a11 a21 PivotSize.two) :
    |a11| < bunchTridiagonalAlpha * M0 := by
  have hthr : M0 * |a11| < bunchTridiagonalAlpha * a21 ^ 2 :=
    bunch_tridiagonal_pivot_choice_two_threshold M0 a11 a21 hchoice
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have hsq : a21 ^ 2 ≤ M0 ^ 2 := by
    nlinarith [ha21, abs_nonneg a21, sq_abs a21]
  nlinarith [hthr, hsq, hα, hM0, mul_pos hM0 hM0]

/-- Helper: `(1+γ₃)·(M₀ + M₀/α) = K·M₀`.  (Pure ring identity — `M₀/α = M₀·α⁻¹`
is treated atomically, no `α ≠ 0` needed.) -/
theorem growth_rhs_eq (fp : FPModel) (M0 : ℝ) :
    (1 + gamma fp 3) * (M0 + M0 / bunchTridiagonalAlpha) = growthK fp * M0 := by
  unfold growthK; ring

/-- **Single-stage 1×1 corner growth (fixed scale).**  For a symmetric tridiagonal
stage whose fed diagonal `A₁₁` (the entry that becomes the new corner) is `≤ M₀`
and whose 1×1 pivot is accepted at the fixed scale `σ = M₀`, the reduced corner
satisfies `|flSchurCompl A 0 0| ≤ K·M₀`. -/
theorem oneByOne_corner_growth (fp : FPModel) (hval : gammaValid fp 3) {n : ℕ}
    (A : Fin (n + 2) → Fin (n + 2) → ℝ) (hA : IsSymTridiagonal (n + 2) A)
    (M0 : ℝ) (hM0 : 0 < M0)
    (hfed : |A ((0 : Fin (n + 1)).succ) ((0 : Fin (n + 1)).succ)| ≤ M0)
    (hchoice : BunchTridiagonalPivotChoice M0 (A 0 0)
      (A ((0 : Fin (n + 1)).succ) 0) PivotSize.one)
    (ha11 : A 0 0 ≠ 0) :
    |flSchurCompl (n + 1) fp A 0 0| ≤ growthK fp * M0 := by
  have hb := flSchurCompl_corner_bound fp hval A hA M0 M0 (le_refl M0) hchoice ha11
  have hγ : 0 ≤ 1 + gamma fp 3 := by have := gamma_nonneg fp hval; linarith
  calc |flSchurCompl (n + 1) fp A 0 0|
      ≤ (1 + gamma fp 3) *
          (|A ((0 : Fin (n + 1)).succ) ((0 : Fin (n + 1)).succ)|
            + M0 / bunchTridiagonalAlpha) := hb
    _ ≤ (1 + gamma fp 3) * (M0 + M0 / bunchTridiagonalAlpha) := by
        apply mul_le_mul_of_nonneg_left _ hγ
        linarith [hfed]
    _ = growthK fp * M0 := growth_rhs_eq fp M0

/-- **Single-stage 2×2 corner growth (fixed scale).**  For a symmetric tridiagonal
stage whose fed diagonal `A₂₂` and off-corner coupling `anext = A₂₁` are `≤ M₀` and
whose 2×2 pivot is accepted at the fixed scale `σ = M₀`, the reduced corner
satisfies `|flSchurCompl2 A 0 0| ≤ K·M₀`.  (The `anext²/(M₀·α)` correction is
`≤ M₀/α` because `anext ≤ M₀`.) -/
theorem twoByTwo_corner_growth (fp : FPModel) (hval : gammaValid fp 3) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (M0 : ℝ) (hM0 : 0 < M0)
    (hfed : |A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ)| ≤ M0)
    (hanext : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| ≤ M0)
    (ha22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ M0)
    (hchoice : BunchTridiagonalPivotChoice M0 (A 0 0)
      (A (oneIdx (m + 1)) 0) PivotSize.two) :
    |flSchurCompl2 (m + 1) fp A 0 0| ≤ growthK fp * M0 := by
  have hb := flSchurCompl2_corner_bound fp hval A hA M0 hM0 hchoice ha22
  have hγ : 0 ≤ 1 + gamma fp 3 := by have := gamma_nonneg fp hval; linarith
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have hden : 0 < M0 * bunchTridiagonalAlpha := mul_pos hM0 hα
  set anext := A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)) with hanextdef
  have hsq : anext ^ 2 ≤ M0 ^ 2 := by nlinarith [hanext, abs_nonneg anext, sq_abs anext]
  have hcorr : anext ^ 2 / (M0 * bunchTridiagonalAlpha) ≤ M0 / bunchTridiagonalAlpha := by
    have heq : M0 / bunchTridiagonalAlpha - anext ^ 2 / (M0 * bunchTridiagonalAlpha)
        = (M0 ^ 2 - anext ^ 2) / (M0 * bunchTridiagonalAlpha) := by
      field_simp [ne_of_gt hM0, ne_of_gt hα]
    have hnn : 0 ≤ (M0 ^ 2 - anext ^ 2) / (M0 * bunchTridiagonalAlpha) :=
      div_nonneg (by linarith [hsq]) (le_of_lt hden)
    have : 0 ≤ M0 / bunchTridiagonalAlpha - anext ^ 2 / (M0 * bunchTridiagonalAlpha) := by
      rw [heq]; exact hnn
    linarith
  calc |flSchurCompl2 (m + 1) fp A 0 0|
      ≤ (1 + gamma fp 3) *
          (|A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ)|
            + anext ^ 2 / (M0 * bunchTridiagonalAlpha)) := hb
    _ ≤ (1 + gamma fp 3) * (M0 + M0 / bunchTridiagonalAlpha) := by
        apply mul_le_mul_of_nonneg_left _ hγ
        linarith [hfed, hcorr]
    _ = growthK fp * M0 := growth_rhs_eq fp M0

/-! ## Session 2 building block — the decoupled determinant lower bound

For the schedule induction the pivot test is at the fixed scale `σ = M₀`, but the
reduced-matrix entries at stage `ℓ` are only bounded by `τ := (1+u)^ℓ M₀ ≥ σ` (each
off-corner entry picks up one `(1+u)` per stage).  The existing 2×2 determinant lower
bound requires `|a₂₂| ≤ σ` (the test scale); here we **decouple** the entry bound `τ`
from the test scale `σ`.  Because `|a₁₁| ≤ α a₂₁²/σ` (2×2 test) and `|a₂₂| ≤ τ`,

  `|det| = |a₁₁a₂₂ − a₂₁²| ≥ a₂₁² − |a₁₁||a₂₂| ≥ a₂₁²·(1 − α·τ/σ)`,

which stays positive as long as `α·τ/σ < 1` (e.g. `τ/σ = (1+u)^ℓ ≤ 1.01 < 1/α`). -/
theorem twoByTwo_absdet_lower_decoupled (σ τ a11 a21 a22 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσ : 0 < σ) (hτ : |a22| ≤ τ) :
    a21 ^ 2 * (1 - bunchTridiagonalAlpha * τ / σ) ≤ |a11 * a22 - a21 ^ 2| := by
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have htest := bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice
  have ha11 : |a11| ≤ bunchTridiagonalAlpha * a21 ^ 2 / σ := by
    rw [le_div_iff₀ hσ]; nlinarith [htest]
  have hb_nonneg : (0 : ℝ) ≤ bunchTridiagonalAlpha * a21 ^ 2 / σ :=
    div_nonneg (mul_nonneg (le_of_lt hα) (sq_nonneg a21)) (le_of_lt hσ)
  have hprod : |a11 * a22| ≤ bunchTridiagonalAlpha * a21 ^ 2 / σ * τ := by
    rw [abs_mul]; exact mul_le_mul ha11 hτ (abs_nonneg _) hb_nonneg
  have hrev : a21 ^ 2 - |a11 * a22| ≤ |a11 * a22 - a21 ^ 2| := by
    have h := abs_sub_abs_le_abs_sub (a21 ^ 2) (a11 * a22)
    rwa [abs_of_nonneg (sq_nonneg a21), abs_sub_comm] at h
  calc a21 ^ 2 * (1 - bunchTridiagonalAlpha * τ / σ)
      = a21 ^ 2 - bunchTridiagonalAlpha * a21 ^ 2 / σ * τ := by ring
    _ ≤ a21 ^ 2 - |a11 * a22| := by linarith [hprod]
    _ ≤ |a11 * a22 - a21 ^ 2| := hrev

/-- Division-free form of the decoupled determinant lower bound:
`a₂₁²·(σ − α·τ) ≤ σ·|det|` (nlinarith-friendly for downstream use). -/
theorem twoByTwo_absdet_lower_decoupled' (σ τ a11 a21 a22 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσ : 0 < σ) (hτ : |a22| ≤ τ) :
    a21 ^ 2 * (σ - bunchTridiagonalAlpha * τ) ≤ σ * |a11 * a22 - a21 ^ 2| := by
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have htest := bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice
  have hrev : a21 ^ 2 - |a11 * a22| ≤ |a11 * a22 - a21 ^ 2| := by
    have h := abs_sub_abs_le_abs_sub (a21 ^ 2) (a11 * a22)
    rwa [abs_of_nonneg (sq_nonneg a21), abs_sub_comm] at h
  have hprod : σ * |a11 * a22| ≤ bunchTridiagonalAlpha * a21 ^ 2 * τ := by
    rw [abs_mul]
    calc σ * (|a11| * |a22|) = (σ * |a11|) * |a22| := by ring
      _ ≤ (bunchTridiagonalAlpha * a21 ^ 2) * τ :=
          mul_le_mul (le_of_lt htest) hτ (abs_nonneg _)
            (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hrev (le_of_lt hσ), hprod]

/-- **Decoupled 2×2 corner correction bound.**  With the pivot test at scale `σ`
and the block diagonal `a₂₂` bounded by `τ ≥ σ` (the entry scale), the exact 2×2
Schur correction satisfies

  `|anext²·(a₁₁/det)| ≤ anext²·α / (σ − α·τ)`,

provided `α·τ < σ` (so `det ≠ 0`).  This is the `(1+u)`-slack-tolerant analogue of
`tridiag_twoByTwo_corner_correction_le_of_choice`; with `τ = σ` it reduces to
`anext²·α/(σ(1−α)) = anext²/(σα)` (using `α² = 1−α`). -/
theorem tridiag_twoByTwo_corner_correction_le_decoupled
    (σ τ a11 a21 a22 anext : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσ : 0 < σ) (hτ : |a22| ≤ τ) (hslack : bunchTridiagonalAlpha * τ < σ) :
    |anext * anext * (a11 / (a11 * a22 - a21 ^ 2))|
      ≤ anext ^ 2 * bunchTridiagonalAlpha / (σ - bunchTridiagonalAlpha * τ) := by
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have htest := bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice
  have ha21 : a21 ≠ 0 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ a11 a21 hchoice (le_of_lt hσ)
  have ha21sq : 0 < a21 ^ 2 := sq_pos_of_ne_zero ha21
  have hd : 0 < σ - bunchTridiagonalAlpha * τ := by linarith
  have hdet_lb : a21 ^ 2 * (σ - bunchTridiagonalAlpha * τ) ≤ σ * |a11 * a22 - a21 ^ 2| :=
    twoByTwo_absdet_lower_decoupled' σ τ a11 a21 a22 hchoice hσ hτ
  have hσdet : 0 < σ * |a11 * a22 - a21 ^ 2| := lt_of_lt_of_le (mul_pos ha21sq hd) hdet_lb
  have hdetpos : 0 < |a11 * a22 - a21 ^ 2| := by
    rcases (abs_nonneg (a11 * a22 - a21 ^ 2)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hσdet; exact absurd hσdet (lt_irrefl 0)
  -- key scalar inequality |a11|·(σ−ατ) ≤ α·|det|
  have hkey : |a11| * (σ - bunchTridiagonalAlpha * τ)
      ≤ bunchTridiagonalAlpha * |a11 * a22 - a21 ^ 2| := by
    have h1 : σ * (|a11| * (σ - bunchTridiagonalAlpha * τ))
        ≤ σ * (bunchTridiagonalAlpha * |a11 * a22 - a21 ^ 2|) := by
      nlinarith [mul_le_mul_of_nonneg_right (le_of_lt htest) (le_of_lt hd),
        mul_le_mul_of_nonneg_left hdet_lb (le_of_lt hα)]
    exact le_of_mul_le_mul_left h1 hσ
  have hLHS : |anext * anext * (a11 / (a11 * a22 - a21 ^ 2))|
      = anext ^ 2 * |a11| / |a11 * a22 - a21 ^ 2| := by
    rw [abs_mul, abs_div]
    have hsq : |anext * anext| = anext ^ 2 := by
      rw [← pow_two, abs_of_nonneg (sq_nonneg anext)]
    rw [hsq]; ring
  rw [hLHS, div_le_iff₀ hdetpos, div_mul_eq_mul_div, le_div_iff₀ hd]
  nlinarith [mul_le_mul_of_nonneg_left hkey (sq_nonneg anext)]

/-- **Decoupled per-step corner bound (2×2).**  The `(1+u)`-slack-tolerant analogue
of `flSchurCompl2_corner_bound`: the pivot test is at scale `σ` (the fixed `M₀`),
while the fed diagonal `a₂₂` is only bounded by `τ ≥ σ`.  The reduced corner then
satisfies

  `|flSchurCompl2 A 0 0| ≤ (1+γ₃)·(|A₂₂| + anext²·α/(σ − α·τ))`,

with `anext = A₂₁` the off-corner coupling.  This is the schedule-induction-ready
2×2 corner bound (Route B step 2). -/
theorem flSchurCompl2_corner_bound_decoupled (fp : FPModel) (hval : gammaValid fp 3) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (σ τ : ℝ) (hσpos : 0 < σ)
    (hchoice : BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx (m + 1)) 0) PivotSize.two)
    (hτa22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ τ)
    (hslack : bunchTridiagonalAlpha * τ < σ) :
    |flSchurCompl2 (m + 1) fp A 0 0|
      ≤ (1 + gamma fp 3) *
          (|A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ)|
            + (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))) ^ 2
                * bunchTridiagonalAlpha / (σ - bunchTridiagonalAlpha * τ)) := by
  set b := A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ) with hb
  set anext := A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)) with hanext
  set a11 := A 0 0 with ha11
  set a22 := A (oneIdx (m + 1)) (oneIdx (m + 1)) with ha22
  set a21 := A (oneIdx (m + 1)) 0 with ha21
  have hsym : A 0 (oneIdx (m + 1)) = a21 := hA.1 0 (oneIdx (m + 1))
  have hdeteq : mixedDet2 (m + 1) A = a11 * a22 - a21 ^ 2 := by
    unfold mixedDet2; rw [hsym]; ring
  have hcorner := flSchurCompl2_corner_eq fp A hA
  rw [hdeteq] at hcorner
  obtain ⟨Δ, hΔ, hstep⟩ :=
    fl_tridiagonal_twoByTwo_schur_step_error fp b anext (a11 / (a11 * a22 - a21 ^ 2)) hval
  rw [hstep] at hcorner
  have hcorr : |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|
      ≤ anext ^ 2 * bunchTridiagonalAlpha / (σ - bunchTridiagonalAlpha * τ) := by
    have hcomm : anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext
        = anext * anext * (a11 / (a11 * a22 - a21 ^ 2)) := by ring
    rw [hcomm]
    exact tridiag_twoByTwo_corner_correction_le_decoupled σ τ a11 a21 a22 anext
      hchoice hσpos hτa22 hslack
  have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  rw [hcorner]
  have htri : |(b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext) + Δ|
      ≤ |b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext| + |Δ| := abs_add_le _ _
  have hsub : |b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|
      ≤ |b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext| := abs_sub _ _
  calc |(b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext) + Δ|
      ≤ |b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext| + |Δ| := htri
    _ ≤ (|b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|)
          + gamma fp 3 * (|b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|) :=
        add_le_add hsub hΔ
    _ = (1 + gamma fp 3) * (|b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|) := by ring
    _ ≤ (1 + gamma fp 3) *
          (|b| + anext ^ 2 * bunchTridiagonalAlpha / (σ - bunchTridiagonalAlpha * τ)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith [hcorr]

/-! ## Session 3 — growth-invariant prerequisites

Building blocks for the schedule-level growth induction (Route B): the sharper `α`
bound needed for the slack condition, the `(1+u)^ℓ` band-growth cap, the 1×1
off-corner reduction (the missing analogue of `flSchurCompl2_eq_sub_zero_of_ne_corner`),
and the fixed-`M₀` run predicate `TriGrowthData`. -/

/-- Sharper bound `α < 3/4` (from `√5 < 5/2`), needed for the slack
`α·(1+u)^ℓ < 1` (since `α·(1+γₙ) ≤ (3/4)(1+1/99) < 1`). -/
theorem alpha_lt_three_quarters : bunchTridiagonalAlpha < 3 / 4 := by
  unfold bunchTridiagonalAlpha
  have h : Real.sqrt 5 < 5 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- **Band-growth cap.**  Off-corner entries pick up one `(1+u)` per stage, so over
`ℓ ≤ n` stages the accumulated factor is `≤ 1 + γₙ`. -/
theorem one_add_u_pow_le (fp : FPModel) {n l : ℕ} (hln : l ≤ n)
    (hvaln : gammaValid fp n) (hval1 : gammaValid fp 1) :
    (1 + fp.u) ^ l ≤ 1 + gamma fp n := by
  have hu1 : fp.u < 1 := by have h := hval1; unfold gammaValid at h; simpa using h
  have hu_le : fp.u ≤ gamma fp 1 := by
    unfold gamma
    rw [Nat.cast_one, one_mul, le_div_iff₀ (by linarith : (0 : ℝ) < 1 - fp.u)]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hvaln1 : gammaValid fp (n * 1) := by rw [Nat.mul_one]; exact hvaln
  have hn := one_add_pow_sub_one_le_gamma_mul_of_le_gamma fp n 1 fp.u_nonneg hu_le hvaln1
  rw [Nat.mul_one] at hn
  have hbase : (1 : ℝ) ≤ 1 + fp.u := by have := fp.u_nonneg; linarith
  have hpow : (1 + fp.u) ^ l ≤ (1 + fp.u) ^ n := pow_le_pow_right₀ hbase hln
  linarith [hpow, hn]

/-- **1×1 off-corner reduction** (the missing analogue of
`flSchurCompl2_eq_sub_zero_of_ne_corner`).  For a symmetric tridiagonal `A` with
nonzero pivot, every non-corner entry of the 1×1 Schur complement is the trailing
datum through a single subtraction from zero. -/
theorem flSchurCompl_eq_sub_zero_of_ne_corner (fp : FPModel) {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (hA : IsSymTridiagonal (n + 1) A)
    (hA00 : A 0 0 ≠ 0) (i j : Fin n) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
    flSchurCompl n fp A i j = fp.fl_sub (A i.succ j.succ) 0 := by
  have hcorr : fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ) = 0 := by
    rcases Nat.eq_zero_or_pos j.val with hj | hj
    · have hi1 : 1 ≤ i.val := by rcases hne with h | h <;> omega
      have hci0 : A i.succ 0 = 0 := by
        apply hA.2; right; simp only [Fin.val_succ, Fin.val_zero]; omega
      rw [hci0, fl_div_zero_left fp (A 0 0) hA00, fl_mul_left_zero]
    · have hcj : A 0 j.succ = 0 := by
        apply hA.2; left; simp only [Fin.val_succ, Fin.val_zero]; omega
      rw [hcj, fl_mul_right_zero]
  unfold flSchurCompl
  rw [hcorr]

/-- **Off-corner band-growth step (1×1).**  `|flSchurCompl A i j| ≤ (1+u)·|A_{i+1,j+1}|`
for `(i,j) ≠ (0,0)` — the 1×1 analogue of `flSchurCompl2_offcorner_bound`. -/
theorem flSchurCompl_offcorner_bound (fp : FPModel) {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (hA : IsSymTridiagonal (n + 1) A)
    (hA00 : A 0 0 ≠ 0) (i j : Fin n) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
    |flSchurCompl n fp A i j| ≤ (1 + fp.u) * |A i.succ j.succ| := by
  rw [flSchurCompl_eq_sub_zero_of_ne_corner fp A hA hA00 i j hne]
  obtain ⟨δ, hδ, heq⟩ := fl_sub_zero_right fp (A i.succ j.succ)
  rw [heq, abs_mul]
  have h1 : |1 + δ| ≤ 1 + fp.u := by
    calc |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by rw [abs_one]; linarith
  calc |A i.succ j.succ| * |1 + δ| ≤ |A i.succ j.succ| * (1 + fp.u) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = (1 + fp.u) * |A i.succ j.succ| := by ring

/-- **Fixed-`M₀` Bunch run predicate.**  Records, along the schedule, only the
structural facts and the Algorithm-11.6 pivot choices *at the fixed scale
`σ = M₀ = ‖A‖_M`* (Higham's "compute σ once").  Unlike `TriPivotData` it does NOT
bundle a per-stage "σ bounds all entries" clause — the entry bound `(1+u)^ℓ·M₀` is
the *conclusion* of the growth induction, not a hypothesis. -/
def TriGrowthData (fp : FPModel) (M0 : ℝ) :
    {k : ℕ} → PivotSchedule k → (Fin k → Fin k → ℝ) → Prop
  | 0, .nil, _ => True
  | n + 1, .consOne s, A =>
      IsSymTridiagonal (n + 1) A ∧ A 0 0 ≠ 0 ∧
      (∀ i : Fin n, BunchTridiagonalPivotChoice M0 (A 0 0) (A i.succ 0) PivotSize.one) ∧
      TriGrowthData fp M0 s (flSchurCompl n fp A)
  | n + 2, .consTwo s, A =>
      IsSymTridiagonal (n + 2) A ∧
      BunchTridiagonalPivotChoice M0 (A 0 0) (A (oneIdx n) 0) PivotSize.two ∧
      TriGrowthData fp M0 s (flSchurCompl2 n fp A)

@[simp] theorem TriGrowthData_consOne (fp : FPModel) (M0 : ℝ) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    TriGrowthData fp M0 s.consOne A ↔
      (IsSymTridiagonal (n + 1) A ∧ A 0 0 ≠ 0 ∧
        (∀ i : Fin n, BunchTridiagonalPivotChoice M0 (A 0 0) (A i.succ 0) PivotSize.one) ∧
        TriGrowthData fp M0 s (flSchurCompl n fp A)) := Iff.rfl

@[simp] theorem TriGrowthData_consTwo (fp : FPModel) (M0 : ℝ) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 2) → Fin (n + 2) → ℝ) :
    TriGrowthData fp M0 s.consTwo A ↔
      (IsSymTridiagonal (n + 2) A ∧
        BunchTridiagonalPivotChoice M0 (A 0 0) (A (oneIdx n) 0) PivotSize.two ∧
        TriGrowthData fp M0 s (flSchurCompl2 n fp A)) := Iff.rfl

/-! ## Session 4 — decoupled 2x2 product-path arithmetic cores
(σ = fixed test scale M0; τ ≥ σ = entry bound; adapted from the coupled
`corner_quadform_core` / `corner_rowcol_le_core` via the decoupled determinant
identity `a21²·(σ−ατ) ≤ σ·D`.  At τ=σ they reduce to the coupled bounds via α²=1−α.) -/

theorem corner_quadform_core_decoupled
    (u σ τ a11abs a21abs a22abs anextabs w0 w1 D : ℝ)
    (hu : 0 ≤ u) (hσ : 0 < σ)
    (ha11abs : 0 ≤ a11abs) (ha21abs : 0 < a21abs)
    (ha22abs : 0 ≤ a22abs) (hanextabs : 0 ≤ anextabs)
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hDpos : 0 < D)
    (hslack : bunchTridiagonalAlpha * τ < σ)
    (hDlow : a21abs ^ 2 * (σ - bunchTridiagonalAlpha * τ) ≤ σ * D)
    (htest : σ * a11abs ≤ bunchTridiagonalAlpha * a21abs ^ 2)
    (ha22 : a22abs ≤ τ) (hanext : anextabs ≤ τ) :
    w0 * D ≤ (1 + u) * anextabs * a21abs → w1 * D ≤ (1 + u) * anextabs * a11abs →
    w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs
      ≤ (1 + u) ^ 2 * bunchTridiagonalAlpha * τ ^ 2 * (3 * σ + bunchTridiagonalAlpha * τ)
          / (σ - bunchTridiagonalAlpha * τ) ^ 2 := by
  intro hw0D hw1D
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have hα1 : bunchTridiagonalAlpha < 1 := bunch_tridiagonal_alpha_lt_one
  set α := bunchTridiagonalAlpha with hαdef
  have h1u : (0 : ℝ) ≤ 1 + u := by linarith
  have hσ0 : 0 ≤ σ := le_of_lt hσ
  have hτ : (0 : ℝ) ≤ τ := le_trans ha22abs ha22
  -- local squaring monotonicity (the private helper is inaccessible)
  have sqmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → a ^ 2 ≤ b ^ 2 := by
    intro a b ha hab; rw [pow_two, pow_two]; exact mul_self_le_mul_self ha hab
  set s := σ - α * τ with hsdef
  have hs : (0 : ℝ) < s := by rw [hsdef]; linarith
  set R := (1 + u) ^ 2 * α * τ ^ 2 * (3 * σ + α * τ) with hR
  have hRHSnn : 0 ≤ R := by rw [hR]; positivity
  have hw0Dnn : 0 ≤ w0 * D := mul_nonneg hw0 hDpos.le
  have hw1Dnn : 0 ≤ w1 * D := mul_nonneg hw1 hDpos.le
  have hP0nn : 0 ≤ (1 + u) * anextabs * a21abs :=
    mul_nonneg (mul_nonneg h1u hanextabs) ha21abs.le
  -- squared / cross multiplier bounds (clearing `D`)
  have e0 : (w0 * D) ^ 2 ≤ ((1 + u) * anextabs * a21abs) ^ 2 := sqmono hw0Dnn hw0D
  have e1 : (w1 * D) ^ 2 ≤ ((1 + u) * anextabs * a11abs) ^ 2 := sqmono hw1Dnn hw1D
  have ecross : (w0 * D) * (w1 * D)
      ≤ ((1 + u) * anextabs * a21abs) * ((1 + u) * anextabs * a11abs) :=
    mul_le_mul hw0D hw1D hw1Dnn hP0nn
  -- STEP (i): `Q · D² ≤ N`
  have hA : w0 ^ 2 * a11abs * D ^ 2 ≤ ((1 + u) * anextabs * a21abs) ^ 2 * a11abs := by
    have h := mul_le_mul_of_nonneg_right e0 ha11abs
    calc w0 ^ 2 * a11abs * D ^ 2 = (w0 * D) ^ 2 * a11abs := by ring
      _ ≤ ((1 + u) * anextabs * a21abs) ^ 2 * a11abs := h
  have hC : w1 ^ 2 * a22abs * D ^ 2 ≤ ((1 + u) * anextabs * a11abs) ^ 2 * a22abs := by
    have h := mul_le_mul_of_nonneg_right e1 ha22abs
    calc w1 ^ 2 * a22abs * D ^ 2 = (w1 * D) ^ 2 * a22abs := by ring
      _ ≤ ((1 + u) * anextabs * a11abs) ^ 2 * a22abs := h
  have hB : 2 * w0 * w1 * a21abs * D ^ 2
      ≤ 2 * (((1 + u) * anextabs * a21abs) * ((1 + u) * anextabs * a11abs)) * a21abs := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ecross ha21abs.le)
      (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * w0 * w1 * a21abs * D ^ 2 = 2 * ((w0 * D) * (w1 * D) * a21abs) := by ring
      _ ≤ 2 * (((1 + u) * anextabs * a21abs) * ((1 + u) * anextabs * a11abs) * a21abs) := h
      _ = 2 * (((1 + u) * anextabs * a21abs) * ((1 + u) * anextabs * a11abs)) * a21abs := by ring
  set N := (1 + u) ^ 2 * anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs + a11abs ^ 2 * a22abs) with hN
  have stepi :
      (w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs) * D ^ 2 ≤ N := by
    have hsum : (w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs) * D ^ 2
        = w0 ^ 2 * a11abs * D ^ 2 + 2 * w0 * w1 * a21abs * D ^ 2 + w1 ^ 2 * a22abs * D ^ 2 := by
      ring
    have hNeq : ((1 + u) * anextabs * a21abs) ^ 2 * a11abs
        + 2 * (((1 + u) * anextabs * a21abs) * ((1 + u) * anextabs * a11abs)) * a21abs
        + ((1 + u) * anextabs * a11abs) ^ 2 * a22abs = N := by rw [hN]; ring
    rw [hsum, ← hNeq]
    exact add_le_add (add_le_add hA hB) hC
  -- STEP (ii): `Q ≤ N / D²`
  have hD2pos : (0 : ℝ) < D ^ 2 := by positivity
  have stepii : w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs ≤ N / D ^ 2 :=
    (le_div_iff₀ hD2pos).mpr stepi
  -- reduced polynomial (numerator, scaled by σ²)
  have hanextsq : anextabs ^ 2 ≤ τ ^ 2 := sqmono hanextabs hanext
  have htestsq : (σ * a11abs) ^ 2 ≤ (α * a21abs ^ 2) ^ 2 :=
    sqmono (mul_nonneg hσ0 ha11abs) htest
  -- term 1
  have t1 : anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs) * σ ^ 2 ≤ 3 * α * σ * τ ^ 2 * a21abs ^ 4 := by
    have hX : 0 ≤ 3 * a21abs ^ 2 * a11abs * σ ^ 2 := by positivity
    have stepA : anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs * σ ^ 2)
        ≤ τ ^ 2 * (3 * a21abs ^ 2 * a11abs * σ ^ 2) := mul_le_mul_of_nonneg_right hanextsq hX
    have hσa : 3 * a21abs ^ 2 * τ ^ 2 * (σ * (σ * a11abs))
        ≤ 3 * a21abs ^ 2 * τ ^ 2 * (σ * (α * a21abs ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htest hσ0)
        (by positivity : (0 : ℝ) ≤ 3 * a21abs ^ 2 * τ ^ 2)
    calc anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs) * σ ^ 2
        = anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs * σ ^ 2) := by ring
      _ ≤ τ ^ 2 * (3 * a21abs ^ 2 * a11abs * σ ^ 2) := stepA
      _ = 3 * a21abs ^ 2 * τ ^ 2 * (σ * (σ * a11abs)) := by ring
      _ ≤ 3 * a21abs ^ 2 * τ ^ 2 * (σ * (α * a21abs ^ 2)) := hσa
      _ = 3 * α * σ * τ ^ 2 * a21abs ^ 4 := by ring
  -- term 2
  have t2 : anextabs ^ 2 * (a11abs ^ 2 * a22abs) * σ ^ 2 ≤ α ^ 2 * τ ^ 3 * a21abs ^ 4 := by
    have hY : 0 ≤ a11abs ^ 2 * a22abs * σ ^ 2 := by positivity
    have stepA' : anextabs ^ 2 * (a11abs ^ 2 * a22abs * σ ^ 2)
        ≤ τ ^ 2 * (a11abs ^ 2 * a22abs * σ ^ 2) := mul_le_mul_of_nonneg_right hanextsq hY
    have hstep1 : a22abs * (σ * a11abs) ^ 2 ≤ a22abs * (α * a21abs ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left htestsq ha22abs
    have hstep2 : a22abs * (α ^ 2 * a21abs ^ 4) ≤ τ * (α ^ 2 * a21abs ^ 4) :=
      mul_le_mul_of_nonneg_right ha22 (by positivity : (0 : ℝ) ≤ α ^ 2 * a21abs ^ 4)
    calc anextabs ^ 2 * (a11abs ^ 2 * a22abs) * σ ^ 2
        = anextabs ^ 2 * (a11abs ^ 2 * a22abs * σ ^ 2) := by ring
      _ ≤ τ ^ 2 * (a11abs ^ 2 * a22abs * σ ^ 2) := stepA'
      _ = τ ^ 2 * (a22abs * (σ * a11abs) ^ 2) := by ring
      _ ≤ τ ^ 2 * (a22abs * (α * a21abs ^ 2) ^ 2) := mul_le_mul_of_nonneg_left hstep1 (sq_nonneg τ)
      _ = τ ^ 2 * (a22abs * (α ^ 2 * a21abs ^ 4)) := by ring
      _ ≤ τ ^ 2 * (τ * (α ^ 2 * a21abs ^ 4)) := mul_le_mul_of_nonneg_left hstep2 (sq_nonneg τ)
      _ = α ^ 2 * τ ^ 3 * a21abs ^ 4 := by ring
  have hcore : anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs + a11abs ^ 2 * a22abs) * σ ^ 2
      ≤ α * τ ^ 2 * (3 * σ + α * τ) * a21abs ^ 4 := by
    have hdist : anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs + a11abs ^ 2 * a22abs) * σ ^ 2
        = anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs) * σ ^ 2
          + anextabs ^ 2 * (a11abs ^ 2 * a22abs) * σ ^ 2 := by ring
    have hrhs : α * τ ^ 2 * (3 * σ + α * τ) * a21abs ^ 4
        = 3 * α * σ * τ ^ 2 * a21abs ^ 4 + α ^ 2 * τ ^ 3 * a21abs ^ 4 := by ring
    rw [hdist, hrhs]; exact add_le_add t1 t2
  -- (A): N·σ² ≤ R·a21⁴
  have hAineq : N * σ ^ 2 ≤ R * a21abs ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hcore (by positivity : (0 : ℝ) ≤ (1 + u) ^ 2)
    calc N * σ ^ 2
        = (1 + u) ^ 2 * (anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs + a11abs ^ 2 * a22abs) * σ ^ 2) := by
          rw [hN]; ring
      _ ≤ (1 + u) ^ 2 * (α * τ ^ 2 * (3 * σ + α * τ) * a21abs ^ 4) := h
      _ = R * a21abs ^ 4 := by rw [hR]; ring
  -- (B): a21⁴·s² ≤ σ²·D²   (from hDlow squared)
  have hBineq : a21abs ^ 4 * s ^ 2 ≤ σ ^ 2 * D ^ 2 := by
    have hDlow_nn : 0 ≤ a21abs ^ 2 * s := mul_nonneg (sq_nonneg _) hs.le
    have hsq : (a21abs ^ 2 * s) ^ 2 ≤ (σ * D) ^ 2 := sqmono hDlow_nn hDlow
    calc a21abs ^ 4 * s ^ 2 = (a21abs ^ 2 * s) ^ 2 := by ring
      _ ≤ (σ * D) ^ 2 := hsq
      _ = σ ^ 2 * D ^ 2 := by ring
  -- combine (A) and (B), then cancel σ²
  have hσsq : (0 : ℝ) < σ ^ 2 := pow_pos hσ 2
  have combined : (N * s ^ 2) * σ ^ 2 ≤ (R * D ^ 2) * σ ^ 2 := by
    have hA' : N * σ ^ 2 * s ^ 2 ≤ R * a21abs ^ 4 * s ^ 2 :=
      mul_le_mul_of_nonneg_right hAineq (sq_nonneg s)
    have hB' : R * (a21abs ^ 4 * s ^ 2) ≤ R * (σ ^ 2 * D ^ 2) :=
      mul_le_mul_of_nonneg_left hBineq hRHSnn
    calc (N * s ^ 2) * σ ^ 2 = N * σ ^ 2 * s ^ 2 := by ring
      _ ≤ R * a21abs ^ 4 * s ^ 2 := hA'
      _ = R * (a21abs ^ 4 * s ^ 2) := by ring
      _ ≤ R * (σ ^ 2 * D ^ 2) := hB'
      _ = (R * D ^ 2) * σ ^ 2 := by ring
  have hNs : N * s ^ 2 ≤ R * D ^ 2 := le_of_mul_le_mul_right combined hσsq
  -- STEP (iii): assemble
  have hs2pos : (0 : ℝ) < s ^ 2 := pow_pos hs 2
  refine (le_div_iff₀ hs2pos).mpr ?_
  calc (w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs) * s ^ 2
      ≤ (N / D ^ 2) * s ^ 2 := mul_le_mul_of_nonneg_right stepii (sq_nonneg s)
    _ = N * s ^ 2 / D ^ 2 := by ring
    _ ≤ R := (div_le_iff₀ hD2pos).mpr hNs

theorem corner_rowcol_le_core_decoupled
    (u σ τ a11abs a21abs a22abs anextabs w0 w1 D : ℝ)
    (hu : 0 ≤ u) (hσ : 0 < σ)
    (ha11abs : 0 ≤ a11abs) (ha21abs : 0 < a21abs)
    (ha22abs : 0 ≤ a22abs) (hanextabs : 0 ≤ anextabs)
    (hDpos : 0 < D)
    (hslack : bunchTridiagonalAlpha * τ < σ)
    (hDlow : a21abs ^ 2 * (σ - bunchTridiagonalAlpha * τ) ≤ σ * D)
    (htest : σ * a11abs ≤ bunchTridiagonalAlpha * a21abs ^ 2)
    (ha21 : a21abs ≤ τ) (ha22 : a22abs ≤ τ) (hanext : anextabs ≤ τ)
    (hw0D : w0 * D ≤ (1 + u) * anextabs * a21abs)
    (hw1D : w1 * D ≤ (1 + u) * anextabs * a11abs) :
    a11abs * w0 + a21abs * w1
        ≤ 2 * (1 + u) * bunchTridiagonalAlpha * τ ^ 2 / (σ - bunchTridiagonalAlpha * τ)
      ∧ a21abs * w0 + a22abs * w1
        ≤ 2 * (1 + u) * σ * τ / (σ - bunchTridiagonalAlpha * τ) := by
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  set α := bunchTridiagonalAlpha with hαdef
  set γ := σ - α * τ with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith [hslack]
  have h1u : (0 : ℝ) ≤ 1 + u := by linarith
  have hσ0 : 0 ≤ σ := hσ.le
  have hτ0 : 0 ≤ τ := le_trans ha21abs.le ha21
  -- KA : linear cancellation numerator for the pivot-row a11/a21 paths
  have KA : a11abs * anextabs * a21abs * γ ≤ α * τ ^ 2 * D := by
    have hστ : σ * (a11abs * anextabs * a21abs * γ) ≤ σ * (α * τ ^ 2 * D) := by
      calc σ * (a11abs * anextabs * a21abs * γ)
          = (σ * a11abs) * (anextabs * a21abs * γ) := by ring
        _ ≤ (α * a21abs ^ 2) * (anextabs * a21abs * γ) :=
            mul_le_mul_of_nonneg_right htest
              (mul_nonneg (mul_nonneg hanextabs ha21abs.le) hγ.le)
        _ = (α * anextabs * a21abs) * (a21abs ^ 2 * γ) := by ring
        _ ≤ (α * anextabs * a21abs) * (σ * D) :=
            mul_le_mul_of_nonneg_left hDlow
              (mul_nonneg (mul_nonneg hα.le hanextabs) ha21abs.le)
        _ = σ * (α * (anextabs * a21abs) * D) := by ring
        _ ≤ σ * (α * (τ * τ) * D) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (mul_le_mul hanext ha21 ha21abs.le hτ0) hα.le)
                hDpos.le)
              hσ0
        _ = σ * (α * τ ^ 2 * D) := by ring
    exact le_of_mul_le_mul_left hστ hσ
  -- KC : linear cancellation numerator for the pivot-column a21 path
  have KC : anextabs * a21abs ^ 2 * γ ≤ σ * τ * D := by
    calc anextabs * a21abs ^ 2 * γ
        = anextabs * (a21abs ^ 2 * γ) := by ring
      _ ≤ anextabs * (σ * D) := mul_le_mul_of_nonneg_left hDlow hanextabs
      _ ≤ τ * (σ * D) := mul_le_mul_of_nonneg_right hanext (mul_nonneg hσ0 hDpos.le)
      _ = σ * τ * D := by ring
  -- KD : linear cancellation numerator for the pivot-column a22 path
  have KD : a22abs * anextabs * a11abs * γ ≤ α * τ ^ 2 * D := by
    have hστ : σ * (a22abs * anextabs * a11abs * γ) ≤ σ * (α * τ ^ 2 * D) := by
      calc σ * (a22abs * anextabs * a11abs * γ)
          = (σ * a11abs) * (a22abs * anextabs * γ) := by ring
        _ ≤ (α * a21abs ^ 2) * (a22abs * anextabs * γ) :=
            mul_le_mul_of_nonneg_right htest
              (mul_nonneg (mul_nonneg ha22abs hanextabs) hγ.le)
        _ = (α * a22abs * anextabs) * (a21abs ^ 2 * γ) := by ring
        _ ≤ (α * a22abs * anextabs) * (σ * D) :=
            mul_le_mul_of_nonneg_left hDlow
              (mul_nonneg (mul_nonneg hα.le ha22abs) hanextabs)
        _ = σ * (α * (a22abs * anextabs) * D) := by ring
        _ ≤ σ * (α * (τ * τ) * D) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (mul_le_mul ha22 hanext hanextabs hτ0) hα.le)
                hDpos.le)
              hσ0
        _ = σ * (α * τ ^ 2 * D) := by ring
    exact le_of_mul_le_mul_left hστ hσ
  -- the four term bounds
  have ta : a11abs * w0 ≤ (1 + u) * α * τ ^ 2 / γ := by
    have hmul : a11abs * w0 * γ * D ≤ (1 + u) * α * τ ^ 2 * D := by
      calc a11abs * w0 * γ * D
          = γ * a11abs * (w0 * D) := by ring
        _ ≤ γ * a11abs * ((1 + u) * anextabs * a21abs) :=
            mul_le_mul_of_nonneg_left hw0D (mul_nonneg hγ.le ha11abs)
        _ = (1 + u) * (a11abs * anextabs * a21abs * γ) := by ring
        _ ≤ (1 + u) * (α * τ ^ 2 * D) := mul_le_mul_of_nonneg_left KA h1u
        _ = (1 + u) * α * τ ^ 2 * D := by ring
    have h2 : a11abs * w0 * γ ≤ (1 + u) * α * τ ^ 2 := le_of_mul_le_mul_right hmul hDpos
    exact (le_div_iff₀ hγ).mpr h2
  have tb : a21abs * w1 ≤ (1 + u) * α * τ ^ 2 / γ := by
    have hmul : a21abs * w1 * γ * D ≤ (1 + u) * α * τ ^ 2 * D := by
      calc a21abs * w1 * γ * D
          = γ * a21abs * (w1 * D) := by ring
        _ ≤ γ * a21abs * ((1 + u) * anextabs * a11abs) :=
            mul_le_mul_of_nonneg_left hw1D (mul_nonneg hγ.le ha21abs.le)
        _ = (1 + u) * (a11abs * anextabs * a21abs * γ) := by ring
        _ ≤ (1 + u) * (α * τ ^ 2 * D) := mul_le_mul_of_nonneg_left KA h1u
        _ = (1 + u) * α * τ ^ 2 * D := by ring
    have h2 : a21abs * w1 * γ ≤ (1 + u) * α * τ ^ 2 := le_of_mul_le_mul_right hmul hDpos
    exact (le_div_iff₀ hγ).mpr h2
  have tc : a21abs * w0 ≤ (1 + u) * σ * τ / γ := by
    have hmul : a21abs * w0 * γ * D ≤ (1 + u) * σ * τ * D := by
      calc a21abs * w0 * γ * D
          = γ * a21abs * (w0 * D) := by ring
        _ ≤ γ * a21abs * ((1 + u) * anextabs * a21abs) :=
            mul_le_mul_of_nonneg_left hw0D (mul_nonneg hγ.le ha21abs.le)
        _ = (1 + u) * (anextabs * a21abs ^ 2 * γ) := by ring
        _ ≤ (1 + u) * (σ * τ * D) := mul_le_mul_of_nonneg_left KC h1u
        _ = (1 + u) * σ * τ * D := by ring
    have h2 : a21abs * w0 * γ ≤ (1 + u) * σ * τ := le_of_mul_le_mul_right hmul hDpos
    exact (le_div_iff₀ hγ).mpr h2
  have td : a22abs * w1 ≤ (1 + u) * α * τ ^ 2 / γ := by
    have hmul : a22abs * w1 * γ * D ≤ (1 + u) * α * τ ^ 2 * D := by
      calc a22abs * w1 * γ * D
          = γ * a22abs * (w1 * D) := by ring
        _ ≤ γ * a22abs * ((1 + u) * anextabs * a11abs) :=
            mul_le_mul_of_nonneg_left hw1D (mul_nonneg hγ.le ha22abs)
        _ = (1 + u) * (a22abs * anextabs * a11abs * γ) := by ring
        _ ≤ (1 + u) * (α * τ ^ 2 * D) := mul_le_mul_of_nonneg_left KD h1u
        _ = (1 + u) * α * τ ^ 2 * D := by ring
    have h2 : a22abs * w1 * γ ≤ (1 + u) * α * τ ^ 2 := le_of_mul_le_mul_right hmul hDpos
    exact (le_div_iff₀ hγ).mpr h2
  -- α·τ² ≤ σ·τ (from α·τ < σ), so the a22 path relaxes into the a21 constant
  have relax : (1 + u) * α * τ ^ 2 / γ ≤ (1 + u) * σ * τ / γ := by
    have hnum : (1 + u) * α * τ ^ 2 ≤ (1 + u) * σ * τ := by
      nlinarith [mul_nonneg h1u (mul_nonneg (sub_nonneg.mpr hslack.le) hτ0)]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_pos.mpr hγ).le
  refine ⟨?_, ?_⟩
  · calc a11abs * w0 + a21abs * w1
        ≤ (1 + u) * α * τ ^ 2 / γ + (1 + u) * α * τ ^ 2 / γ := add_le_add ta tb
      _ = 2 * (1 + u) * α * τ ^ 2 / γ := by ring
  · calc a21abs * w0 + a22abs * w1
        ≤ (1 + u) * σ * τ / γ + (1 + u) * σ * τ / γ := add_le_add tc (le_trans td relax)
      _ = 2 * (1 + u) * σ * τ / γ := by ring

/-! ## Session 5 — decoupled corner pivot-path bounds -/

theorem pivotPath2Abs_corner_le_decoupled (fp : FPModel) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (σ τ : ℝ) (hσpos : 0 < σ) (hslack : bunchTridiagonalAlpha * τ < σ)
    (hchoice : BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx (m + 1)) 0) PivotSize.two)
    (hτa22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ τ)
    (hτanext : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| ≤ τ) :
    pivotPath2Abs (m + 1) fp A 0 0
      ≤ (1 + fp.u) ^ 2 * bunchTridiagonalAlpha * τ ^ 2
          * (3 * σ + bunchTridiagonalAlpha * τ) / (σ - bunchTridiagonalAlpha * τ) ^ 2 := by
  have hu0 := fp.u_nonneg
  have hsym : A 0 (oneIdx (m + 1)) = A (oneIdx (m + 1)) 0 := hA.1 0 (oneIdx (m + 1))
  have ha21ne : A (oneIdx (m + 1)) 0 ≠ 0 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ (A 0 0)
      (A (oneIdx (m + 1)) 0) hchoice hσpos.le
  have ha21abspos : 0 < |A (oneIdx (m + 1)) 0| := abs_pos.mpr ha21ne
  have hd : 0 < σ - bunchTridiagonalAlpha * τ := by linarith [hslack]
  -- determinant identity and decoupled lower bound
  have hdeteq : mixedDet2 (m + 1) A
      = A 0 0 * A (oneIdx (m + 1)) (oneIdx (m + 1)) - A (oneIdx (m + 1)) 0 ^ 2 := by
    unfold mixedDet2; rw [hsym]; ring
  have hDlow_raw := twoByTwo_absdet_lower_decoupled' σ τ (A 0 0)
    (A (oneIdx (m + 1)) 0) (A (oneIdx (m + 1)) (oneIdx (m + 1))) hchoice hσpos hτa22
  have hDlow : |A (oneIdx (m + 1)) 0| ^ 2 * (σ - bunchTridiagonalAlpha * τ)
      ≤ σ * |mixedDet2 (m + 1) A| := by
    rw [sq_abs, hdeteq]; exact hDlow_raw
  have hσdet : 0 < σ * |mixedDet2 (m + 1) A| :=
    lt_of_lt_of_le (mul_pos (pow_pos ha21abspos 2) hd) hDlow
  have hDgt : 0 < |mixedDet2 (m + 1) A| := by
    rcases (abs_nonneg (mixedDet2 (m + 1) A)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hσdet; exact absurd hσdet (lt_irrefl 0)
  have htest : σ * |A 0 0| ≤ bunchTridiagonalAlpha * |A (oneIdx (m + 1)) 0| ^ 2 := by
    rw [sq_abs]
    exact le_of_lt (bunch_tridiagonal_pivot_choice_two_threshold σ (A 0 0)
      (A (oneIdx (m + 1)) 0) hchoice)
  -- multiplier rounding bounds (clearing `det`) — unchanged from the coupled proof
  obtain ⟨δ0, hδ0, hm0⟩ := fp.model_mul (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))
    (-A (oneIdx (m + 1)) 0 / mixedDet2 (m + 1) A)
  obtain ⟨δ1, hδ1, hm1⟩ := fp.model_mul (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))
    (A 0 0 / mixedDet2 (m + 1) A)
  have hw0val : flMixedMult2 (m + 1) fp A 0 0
      = A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))
          * (-A (oneIdx (m + 1)) 0 / mixedDet2 (m + 1) A) * (1 + δ0) := by
    rw [flMixedMult2_corner0 fp A hA]; exact hm0
  have hw1val : flMixedMult2 (m + 1) fp A 0 1
      = A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))
          * (A 0 0 / mixedDet2 (m + 1) A) * (1 + δ1) := by
    rw [flMixedMult2_corner1 fp A hA]; exact hm1
  have hcancel0 : |(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|
      = |A (oneIdx (m + 1)) 0| := by
    rw [abs_div, abs_neg, div_mul_cancel₀ _ hDgt.ne']
  have hcancel1 : |A 0 0 / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A| = |A 0 0| := by
    rw [abs_div, div_mul_cancel₀ _ hDgt.ne']
  have hw0D : |flMixedMult2 (m + 1) fp A 0 0| * |mixedDet2 (m + 1) A|
      ≤ (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |A (oneIdx (m + 1)) 0| := by
    rw [hw0val, abs_mul, abs_mul]
    have hrw : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |1 + δ0|
          * |mixedDet2 (m + 1) A|
        = |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * (|(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|)
          * |1 + δ0| := by ring
    rw [hrw, hcancel0]
    calc |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A (oneIdx (m + 1)) 0| * |1 + δ0|
        ≤ |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A (oneIdx (m + 1)) 0|
            * (1 + fp.u) :=
          mul_le_mul_of_nonneg_left (abs_one_add_le fp hδ0)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
            * |A (oneIdx (m + 1)) 0| := by ring
  have hw1D : |flMixedMult2 (m + 1) fp A 0 1| * |mixedDet2 (m + 1) A|
      ≤ (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| := by
    rw [hw1val, abs_mul, abs_mul]
    have hrw : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |A 0 0 / mixedDet2 (m + 1) A| * |1 + δ1| * |mixedDet2 (m + 1) A|
        = |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * (|A 0 0 / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|) * |1 + δ1| := by ring
    rw [hrw, hcancel1]
    calc |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| * |1 + δ1|
        ≤ |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| * (1 + fp.u) :=
          mul_le_mul_of_nonneg_left (abs_one_add_le fp hδ1)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| := by ring
  -- expand `pivotPath2Abs` at the corner — unchanged
  have hexpand : pivotPath2Abs (m + 1) fp A 0 0
      = |flMixedMult2 (m + 1) fp A 0 0| ^ 2 * |A 0 0|
        + 2 * |flMixedMult2 (m + 1) fp A 0 0| * |flMixedMult2 (m + 1) fp A 0 1|
            * |A (oneIdx (m + 1)) 0|
        + |flMixedMult2 (m + 1) fp A 0 1| ^ 2 * |A (oneIdx (m + 1)) (oneIdx (m + 1))| := by
    rw [pivotPath2Abs, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
    rw [hsym]; ring
  rw [hexpand]
  exact corner_quadform_core_decoupled fp.u σ τ |A 0 0| |A (oneIdx (m + 1)) 0|
    |A (oneIdx (m + 1)) (oneIdx (m + 1))|
    |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
    |flMixedMult2 (m + 1) fp A 0 0| |flMixedMult2 (m + 1) fp A 0 1|
    |mixedDet2 (m + 1) A|
    hu0 hσpos (abs_nonneg _) ha21abspos (abs_nonneg _) (abs_nonneg _)
    (abs_nonneg _) (abs_nonneg _) hDgt hslack hDlow htest hτa22 hτanext hw0D hw1D

theorem pivotRowColPathAbs_corner_le_decoupled (fp : FPModel) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (σ τ : ℝ) (hσpos : 0 < σ) (hslack : bunchTridiagonalAlpha * τ < σ)
    (hchoice : BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx (m + 1)) 0) PivotSize.two)
    (hτa21 : |A (oneIdx (m + 1)) 0| ≤ τ)
    (hτa22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ τ)
    (hτanext : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| ≤ τ) :
    pivotRowPathAbs (m + 1) fp A 0 0
        ≤ 2 * (1 + fp.u) * bunchTridiagonalAlpha * τ ^ 2 / (σ - bunchTridiagonalAlpha * τ)
      ∧ pivotRowPathAbs (m + 1) fp A 1 0
        ≤ 2 * (1 + fp.u) * σ * τ / (σ - bunchTridiagonalAlpha * τ)
      ∧ pivotColPathAbs (m + 1) fp A 0 0
        ≤ 2 * (1 + fp.u) * bunchTridiagonalAlpha * τ ^ 2 / (σ - bunchTridiagonalAlpha * τ)
      ∧ pivotColPathAbs (m + 1) fp A 0 1
        ≤ 2 * (1 + fp.u) * σ * τ / (σ - bunchTridiagonalAlpha * τ) := by
  have hu0 := fp.u_nonneg
  have hgap : 0 < σ - bunchTridiagonalAlpha * τ := by linarith [hslack]
  have hsym : A 0 (oneIdx (m + 1)) = A (oneIdx (m + 1)) 0 := hA.1 0 (oneIdx (m + 1))
  have ha21ne : A (oneIdx (m + 1)) 0 ≠ 0 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ (A 0 0)
      (A (oneIdx (m + 1)) 0) hchoice hσpos.le
  have hdeteq : mixedDet2 (m + 1) A
      = A 0 0 * A (oneIdx (m + 1)) (oneIdx (m + 1)) - A (oneIdx (m + 1)) 0 ^ 2 := by
    unfold mixedDet2; rw [hsym]; ring
  have hDlow : |A (oneIdx (m + 1)) 0| ^ 2 * (σ - bunchTridiagonalAlpha * τ)
      ≤ σ * |mixedDet2 (m + 1) A| := by
    rw [sq_abs, hdeteq]
    exact twoByTwo_absdet_lower_decoupled' σ τ (A 0 0) (A (oneIdx (m + 1)) 0)
      (A (oneIdx (m + 1)) (oneIdx (m + 1))) hchoice hσpos hτa22
  have hσD : 0 < σ * |mixedDet2 (m + 1) A| :=
    lt_of_lt_of_le (mul_pos (pow_pos (abs_pos.mpr ha21ne) 2) hgap) hDlow
  have hDgt : 0 < |mixedDet2 (m + 1) A| := by
    rcases (abs_nonneg (mixedDet2 (m + 1) A)).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hσD; exact lt_irrefl 0 hσD
  have htest : σ * |A 0 0| ≤ bunchTridiagonalAlpha * |A (oneIdx (m + 1)) 0| ^ 2 := by
    rw [sq_abs]
    exact le_of_lt (bunch_tridiagonal_pivot_choice_two_threshold σ (A 0 0)
      (A (oneIdx (m + 1)) 0) hchoice)
  obtain ⟨δ0, hδ0, hm0⟩ := fp.model_mul (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))
    (-A (oneIdx (m + 1)) 0 / mixedDet2 (m + 1) A)
  obtain ⟨δ1, hδ1, hm1⟩ := fp.model_mul (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))
    (A 0 0 / mixedDet2 (m + 1) A)
  have hw0val : flMixedMult2 (m + 1) fp A 0 0
      = A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))
          * (-A (oneIdx (m + 1)) 0 / mixedDet2 (m + 1) A) * (1 + δ0) := by
    rw [flMixedMult2_corner0 fp A hA]; exact hm0
  have hw1val : flMixedMult2 (m + 1) fp A 0 1
      = A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))
          * (A 0 0 / mixedDet2 (m + 1) A) * (1 + δ1) := by
    rw [flMixedMult2_corner1 fp A hA]; exact hm1
  have hcancel0 : |(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|
      = |A (oneIdx (m + 1)) 0| := by
    rw [abs_div, abs_neg, div_mul_cancel₀ _ hDgt.ne']
  have hcancel1 : |A 0 0 / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A| = |A 0 0| := by
    rw [abs_div, div_mul_cancel₀ _ hDgt.ne']
  have hw0D : |flMixedMult2 (m + 1) fp A 0 0| * |mixedDet2 (m + 1) A|
      ≤ (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |A (oneIdx (m + 1)) 0| := by
    rw [hw0val, abs_mul, abs_mul]
    have hrw : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |1 + δ0|
          * |mixedDet2 (m + 1) A|
        = |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * (|(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|)
          * |1 + δ0| := by ring
    rw [hrw, hcancel0]
    calc |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A (oneIdx (m + 1)) 0| * |1 + δ0|
        ≤ |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A (oneIdx (m + 1)) 0|
            * (1 + fp.u) :=
          mul_le_mul_of_nonneg_left (abs_one_add_le fp hδ0)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
            * |A (oneIdx (m + 1)) 0| := by ring
  have hw1D : |flMixedMult2 (m + 1) fp A 0 1| * |mixedDet2 (m + 1) A|
      ≤ (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| := by
    rw [hw1val, abs_mul, abs_mul]
    have hrw : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |A 0 0 / mixedDet2 (m + 1) A| * |1 + δ1| * |mixedDet2 (m + 1) A|
        = |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * (|A 0 0 / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|) * |1 + δ1| := by ring
    rw [hrw, hcancel1]
    calc |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| * |1 + δ1|
        ≤ |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| * (1 + fp.u) :=
          mul_le_mul_of_nonneg_left (abs_one_add_le fp hδ1)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| := by ring
  obtain ⟨hrow0, hrow1⟩ := corner_rowcol_le_core_decoupled fp.u σ τ |A 0 0|
    |A (oneIdx (m + 1)) 0|
    |A (oneIdx (m + 1)) (oneIdx (m + 1))|
    |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
    |flMixedMult2 (m + 1) fp A 0 0| |flMixedMult2 (m + 1) fp A 0 1|
    |mixedDet2 (m + 1) A|
    hu0 hσpos (abs_nonneg _) (abs_pos.mpr ha21ne) (abs_nonneg _) (abs_nonneg _)
    hDgt hslack hDlow htest hτa21 hτa22 hτanext hw0D hw1D
  have hexpRow0 : pivotRowPathAbs (m + 1) fp A 0 0
      = |A 0 0| * |flMixedMult2 (m + 1) fp A 0 0|
        + |A (oneIdx (m + 1)) 0| * |flMixedMult2 (m + 1) fp A 0 1| := by
    rw [pivotRowPathAbs, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
    rw [hsym]
  have hexpRow1 : pivotRowPathAbs (m + 1) fp A 1 0
      = |A (oneIdx (m + 1)) 0| * |flMixedMult2 (m + 1) fp A 0 0|
        + |A (oneIdx (m + 1)) (oneIdx (m + 1))| * |flMixedMult2 (m + 1) fp A 0 1| := by
    rw [pivotRowPathAbs, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
  have hexpCol0 : pivotColPathAbs (m + 1) fp A 0 0
      = |A 0 0| * |flMixedMult2 (m + 1) fp A 0 0|
        + |A (oneIdx (m + 1)) 0| * |flMixedMult2 (m + 1) fp A 0 1| := by
    rw [pivotColPathAbs, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
    ring
  have hexpCol1 : pivotColPathAbs (m + 1) fp A 0 1
      = |A (oneIdx (m + 1)) 0| * |flMixedMult2 (m + 1) fp A 0 0|
        + |A (oneIdx (m + 1)) (oneIdx (m + 1))| * |flMixedMult2 (m + 1) fp A 0 1| := by
    rw [pivotColPathAbs, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
    rw [show A 0 (oneIdx (m + 1)) = A (oneIdx (m + 1)) 0 from hsym]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hexpRow0]; exact hrow0
  · rw [hexpRow1]; exact hrow1
  · rw [hexpCol0]; exact hrow0
  · rw [hexpCol1]; exact hrow1

end LeanFpAnalysis.FP.Ch11Closure.TriGrowthInv
