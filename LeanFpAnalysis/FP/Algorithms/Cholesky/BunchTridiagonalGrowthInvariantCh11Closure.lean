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

end LeanFpAnalysis.FP.Ch11Closure.TriGrowthInv
