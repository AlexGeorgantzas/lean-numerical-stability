import LeanFpAnalysis.HDP.Probability.Concentration.BerryEsseen
import LeanFpAnalysis.HDP.Probability.Inequalities
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Topology.Order.IntermediateValue

/-!
# Berry-Esseen Fourier Smoothing

Local Fourier-analytic building blocks for the Durrett/Feller proof of the
Berry-Esseen theorem.  The file deliberately separates the analytic objects
from the book-facing Berry-Esseen statement:

* the triangular Fourier multiplier of Polya's kernel,
* the Polya density formula,
* convolution/smoothing of measures and its characteristic function,
* the inversion-integral majorization used in Esseen smoothing,
* the algebraic smoothing budget, and
* the Gaussian integral constant used in Durrett's final estimate.

The file keeps conditional smoothing lemmas as reusable API, but also proves
the local Polya-smoothed inversion identities needed for the normalized-sum
Berry-Esseen theorem and derives the book-facing CDF and tail conclusions with
an explicit absolute constant `C = 3`.  The Prawitz/Shevtsova exact-constant
route is retained as proved local structure and conditional promotion theorems;
the final unconditional `C = 1` sharpening is intentionally left for a later
formalization pass.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology FourierTransform

namespace LeanFpAnalysis.HDP

section PolyaKernel

/-- The triangular multiplier `θ ↦ (1 - |θ| / L)_+` appearing as the
characteristic function of Polya's smoothing kernel. -/
def triangleMultiplier (L θ : ℝ) : ℝ :=
  max (1 - |θ| / L) 0

lemma triangleMultiplier_nonneg (L θ : ℝ) :
    0 ≤ triangleMultiplier L θ := by
  rw [triangleMultiplier]
  exact le_max_right _ _

lemma triangleMultiplier_le_one {L θ : ℝ} (hL : 0 < L) :
    triangleMultiplier L θ ≤ 1 := by
  rw [triangleMultiplier]
  refine max_le ?_ zero_le_one
  have hdiv : 0 ≤ |θ| / L := div_nonneg (abs_nonneg θ) hL.le
  linarith

lemma triangleMultiplier_eq_of_abs_le {L θ : ℝ} (hL : 0 < L)
    (hθ : |θ| ≤ L) :
    triangleMultiplier L θ = 1 - |θ| / L := by
  rw [triangleMultiplier]
  have hdiv : |θ| / L ≤ 1 := by
    rw [div_le_iff₀ hL]
    simpa using hθ
  exact max_eq_left (by linarith)

lemma triangleMultiplier_eq_zero_of_le_abs {L θ : ℝ} (hL : 0 < L)
    (hθ : L ≤ |θ|) :
    triangleMultiplier L θ = 0 := by
  rw [triangleMultiplier]
  have hdiv : 1 ≤ |θ| / L := by
    rw [le_div_iff₀ hL]
    simpa using hθ
  exact max_eq_right (by linarith)

lemma abs_le_of_triangleMultiplier_ne_zero {L θ : ℝ} (hL : 0 < L)
    (hθ : triangleMultiplier L θ ≠ 0) :
    |θ| < L := by
  by_contra hnot
  have hle : L ≤ |θ| := le_of_not_gt hnot
  exact hθ (triangleMultiplier_eq_zero_of_le_abs hL hle)

lemma continuous_triangleMultiplier (L : ℝ) :
    Continuous (triangleMultiplier L) := by
  unfold triangleMultiplier
  fun_prop

lemma support_triangleMultiplier_subset {L : ℝ} (hL : 0 < L) :
    Function.support (triangleMultiplier L) ⊆ Set.Icc (-L) L := by
  intro θ hθ
  have hne : triangleMultiplier L θ ≠ 0 := by
    simpa [Function.mem_support] using hθ
  have hlt : |θ| < L := abs_le_of_triangleMultiplier_ne_zero hL hne
  exact ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩

lemma support_triangleMultiplier_subset_Ioo {L : ℝ} (hL : 0 < L) :
    Function.support (triangleMultiplier L) ⊆ Set.Ioo (-L) L := by
  intro θ hθ
  have hne : triangleMultiplier L θ ≠ 0 := by
    simpa [Function.mem_support] using hθ
  have hlt : |θ| < L := abs_le_of_triangleMultiplier_ne_zero hL hne
  exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2⟩

lemma hasCompactSupport_triangleMultiplier {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (triangleMultiplier L) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_triangleMultiplier_subset hL)

lemma integrable_triangleMultiplier {L : ℝ} (hL : 0 < L) :
    Integrable (triangleMultiplier L) :=
  (continuous_triangleMultiplier L).integrable_of_hasCompactSupport
    (hasCompactSupport_triangleMultiplier hL)

lemma integral_one_sub_div_mul_cos {L α : ℝ} (hL : 0 < L) (hα : α ≠ 0) :
    ∫ x in 0..L, (1 - x / L) * Real.cos (α * x) =
      (1 - Real.cos (α * L)) / (L * α ^ 2) := by
  let F : ℝ → ℝ := fun y =>
    (1 - y / L) * Real.sin (α * y) / α -
      Real.cos (α * y) / (L * α ^ 2)
  have hLne : L ≠ 0 := hL.ne'
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) L,
        HasDerivAt F ((1 - x / L) * Real.cos (α * x)) x := by
    intro x _hx
    have hleft : HasDerivAt (fun y : ℝ => 1 - y / L) (-(1 / L)) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).div_const L) using 1
      ring
    have hsin : HasDerivAt (fun y : ℝ => Real.sin (α * y))
        (α * Real.cos (α * x)) x := by
      convert (Real.hasDerivAt_sin (α * x)).comp x
        ((hasDerivAt_id x).const_mul α) using 1
      ring
    have hcos : HasDerivAt (fun y : ℝ => Real.cos (α * y))
        (-(α * Real.sin (α * x))) x := by
      convert (Real.hasDerivAt_cos (α * x)).comp x
        ((hasDerivAt_id x).const_mul α) using 1
      ring
    have hder :
        HasDerivAt F
          (((-(1 / L)) * Real.sin (α * x) +
                (1 - x / L) * (α * Real.cos (α * x))) / α -
              (-(α * Real.sin (α * x))) / (L * α ^ 2)) x := by
      exact ((hleft.mul hsin).div_const α).sub (hcos.div_const (L * α ^ 2))
    convert hder using 1
    field_simp [hLne, hα]
    ring
  have hint :
      IntervalIntegrable (fun x : ℝ => (1 - x / L) * Real.cos (α * x))
        volume 0 L := by
    exact (by
      fun_prop :
        Continuous fun x : ℝ => (1 - x / L) * Real.cos (α * x)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  change (∫ x in 0..L, (1 - x / L) * Real.cos (α * x)) = _ at hFTC
  rw [hFTC]
  simp [F, hLne]
  field_simp [hLne, hα]
  ring

lemma integral_one_sub_div {L : ℝ} (hL : 0 < L) :
    ∫ x in 0..L, 1 - x / L = L / 2 := by
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id]
    field_simp [hL.ne']
    ring
  · exact intervalIntegrable_const
  · exact (continuous_id.div_const L).intervalIntegrable _ _

lemma integral_triangleMultiplier {L : ℝ} (hL : 0 < L) :
    ∫ x in -L..L, triangleMultiplier L x = L := by
  let f : ℝ → ℝ := fun x => triangleMultiplier L x
  let g : ℝ → ℝ := fun x => 1 - x / L
  have hneg_int : IntervalIntegrable f volume (-L) 0 := by
    exact (continuous_triangleMultiplier L).intervalIntegrable _ _
  have hpos_int : IntervalIntegrable f volume 0 L := by
    exact (continuous_triangleMultiplier L).intervalIntegrable _ _
  have hsplit :
      (∫ x in -L..0, f x) + (∫ x in 0..L, f x) =
        ∫ x in -L..L, f x :=
    intervalIntegral.integral_add_adjacent_intervals hneg_int hpos_int
  rw [← hsplit]
  have hpos_eq : (∫ x in 0..L, f x) = ∫ x in 0..L, g x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) L := by
      simpa [Set.uIcc_of_le hL.le] using hx
    have htri : triangleMultiplier L x = 1 - x / L := by
      rw [triangleMultiplier_eq_of_abs_le hL
        (by rw [abs_of_nonneg hxIcc.1]; exact hxIcc.2),
        abs_of_nonneg hxIcc.1]
    simp [f, g, htri]
  have hneg_eq : (∫ x in -L..0, f x) = ∫ x in 0..L, g x := by
    calc
      (∫ x in -L..0, f x) = ∫ x in 0..L, f (-x) := by
        simp
      _ = ∫ x in 0..L, g x := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) L := by
          simpa [Set.uIcc_of_le hL.le] using hx
        have htri : triangleMultiplier L (-x) = 1 - x / L := by
          rw [triangleMultiplier_eq_of_abs_le hL
            (by rw [abs_neg, abs_of_nonneg hxIcc.1]; exact hxIcc.2),
            abs_neg, abs_of_nonneg hxIcc.1]
        simp [f, g, htri]
  rw [hneg_eq, hpos_eq]
  rw [show (∫ x in 0..L, g x) + ∫ x in 0..L, g x =
      2 * ∫ x in 0..L, g x by ring]
  rw [show (∫ x in 0..L, g x) = L / 2 by
    dsimp [g]
    exact integral_one_sub_div hL]
  ring

lemma integral_triangleMultiplier_exp_mul_I_of_ne {L α : ℝ}
    (hL : 0 < L) (hα : α ≠ 0) :
    (∫ x in -L..L,
      (triangleMultiplier L x : ℂ) *
        Complex.exp (((α * x : ℝ) : ℂ) * Complex.I)) =
      (2 * ((1 - Real.cos (α * L)) / (L * α ^ 2)) : ℂ) := by
  let f : ℝ → ℂ := fun x =>
    (triangleMultiplier L x : ℂ) *
      Complex.exp (((α * x : ℝ) : ℂ) * Complex.I)
  let g : ℝ → ℂ := fun x =>
    ((1 - x / L : ℝ) : ℂ) *
      Complex.exp (((α * x : ℝ) : ℂ) * Complex.I)
  let gm : ℝ → ℂ := fun x =>
    ((1 - x / L : ℝ) : ℂ) *
      Complex.exp (((-(α * x) : ℝ) : ℂ) * Complex.I)
  have hneg_int : IntervalIntegrable f volume (-L) 0 := by
    exact ((Complex.continuous_ofReal.comp (continuous_triangleMultiplier L)).mul
      (by fun_prop)).intervalIntegrable _ _
  have hpos_int : IntervalIntegrable f volume 0 L := by
    exact ((Complex.continuous_ofReal.comp (continuous_triangleMultiplier L)).mul
      (by fun_prop)).intervalIntegrable _ _
  have hsplit :
      (∫ x in -L..0, f x) + (∫ x in 0..L, f x) =
        ∫ x in -L..L, f x :=
    intervalIntegral.integral_add_adjacent_intervals hneg_int hpos_int
  rw [← hsplit]
  have hpos_eq : (∫ x in 0..L, f x) = ∫ x in 0..L, g x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) L := by
      simpa [Set.uIcc_of_le hL.le] using hx
    have htri : triangleMultiplier L x = 1 - x / L := by
      rw [triangleMultiplier_eq_of_abs_le hL
        (by rw [abs_of_nonneg hxIcc.1]; exact hxIcc.2),
        abs_of_nonneg hxIcc.1]
    simp [f, g, htri]
  have hneg_eq : (∫ x in -L..0, f x) = ∫ x in 0..L, gm x := by
    calc
      (∫ x in -L..0, f x) = ∫ x in 0..L, f (-x) := by
        simp
      _ = ∫ x in 0..L, gm x := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) L := by
          simpa [Set.uIcc_of_le hL.le] using hx
        have htri : triangleMultiplier L (-x) = 1 - x / L := by
          rw [triangleMultiplier_eq_of_abs_le hL
            (by rw [abs_neg, abs_of_nonneg hxIcc.1]; exact hxIcc.2),
            abs_neg, abs_of_nonneg hxIcc.1]
        simp [f, gm, htri]
  rw [hneg_eq, hpos_eq]
  have hgm_int : IntervalIntegrable gm volume 0 L := by
    exact (by fun_prop : Continuous gm).intervalIntegrable _ _
  have hg_int : IntervalIntegrable g volume 0 L := by
    exact (by fun_prop : Continuous g).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add hgm_int hg_int]
  have hsum :
      (∫ x in 0..L, gm x + g x) =
        ∫ x in 0..L, ((2 * ((1 - x / L) * Real.cos (α * x)) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr ?_
    intro x _hx
    have hexp :
        Complex.exp (((-(α * x) : ℝ) : ℂ) * Complex.I) +
            Complex.exp (((α * x : ℝ) : ℂ) * Complex.I) =
          (2 * Real.cos (α * x) : ℂ) := by
      rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
        Real.cos_neg, Real.sin_neg]
      apply Complex.ext <;> simp <;> ring
    calc
      gm x + g x =
          ((1 - x / L : ℝ) : ℂ) *
            (Complex.exp (((-(α * x) : ℝ) : ℂ) * Complex.I) +
              Complex.exp (((α * x : ℝ) : ℂ) * Complex.I)) := by
            simp only [gm, g]
            ring
      _ = ((2 * ((1 - x / L) * Real.cos (α * x)) : ℝ) : ℂ) := by
            rw [hexp]
            norm_cast
            ring
  rw [hsum, intervalIntegral.integral_ofReal]
  rw [show (∫ x in 0..L, 2 * ((1 - x / L) * Real.cos (α * x))) =
      2 * ∫ x in 0..L, (1 - x / L) * Real.cos (α * x) by
    rw [intervalIntegral.integral_const_mul]]
  rw [integral_one_sub_div_mul_cos hL hα]
  norm_cast

lemma integral_triangleMultiplier_exp_mul_I_eq_sinc_sq_of_ne {L α : ℝ}
    (hL : 0 < L) (hα : α ≠ 0) :
    (∫ x in -L..L,
      (triangleMultiplier L x : ℂ) *
        Complex.exp (((α * x : ℝ) : ℂ) * Complex.I)) =
      (L * Real.sinc (α * L / 2) ^ 2 : ℂ) := by
  rw [integral_triangleMultiplier_exp_mul_I_of_ne hL hα]
  have harg : α * L / 2 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hα hL.ne') (by norm_num)
  norm_cast
  have hcos : 1 - Real.cos (α * L) = 2 * Real.sin (α * L / 2) ^ 2 := by
    rw [show α * L = 2 * (α * L / 2) by ring, Real.cos_two_mul_eq_one_sub]
    ring_nf
  rw [hcos, Real.sinc_of_ne_zero harg]
  field_simp [hL.ne', hα]

lemma integral_triangleMultiplier_exp_mul_I_eq_sinc_sq {L α : ℝ}
    (hL : 0 < L) :
    (∫ x in -L..L,
      (triangleMultiplier L x : ℂ) *
        Complex.exp (((α * x : ℝ) : ℂ) * Complex.I)) =
      (L * Real.sinc (α * L / 2) ^ 2 : ℂ) := by
  by_cases hα : α = 0
  · subst α
    simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
    rw [intervalIntegral.integral_ofReal, integral_triangleMultiplier hL]
    simp [Real.sinc_zero]
  · exact integral_triangleMultiplier_exp_mul_I_eq_sinc_sq_of_ne hL hα

lemma triangleMultiplier_zero {L : ℝ} (hL : 0 < L) :
    triangleMultiplier L 0 = 1 := by
  rw [triangleMultiplier_eq_of_abs_le hL]
  · simp
  · simpa using hL.le

lemma integral_triangleMultiplier_exp_mul_I_full {L α : ℝ} (hL : 0 < L) :
    (∫ x : ℝ,
      (triangleMultiplier L x : ℂ) *
        Complex.exp (((α * x : ℝ) : ℂ) * Complex.I)) =
      ∫ x in -L..L,
        (triangleMultiplier L x : ℂ) *
          Complex.exp (((α * x : ℝ) : ℂ) * Complex.I) := by
  let f : ℝ → ℂ := fun x =>
    (triangleMultiplier L x : ℂ) *
      Complex.exp (((α * x : ℝ) : ℂ) * Complex.I)
  have hsupport : Function.support f ⊆ Set.Ioc (-L) L := by
    intro x hx
    have htriC : (triangleMultiplier L x : ℂ) ≠ 0 := by
      intro hzero
      exact hx (by simp [f, hzero])
    have htri : triangleMultiplier L x ≠ 0 := by
      intro hzero
      exact htriC (by exact_mod_cast hzero)
    have hxtri : x ∈ Function.support (triangleMultiplier L) := by
      simpa [Function.mem_support] using htri
    have hxIoo := support_triangleMultiplier_subset_Ioo hL hxtri
    exact ⟨hxIoo.1, hxIoo.2.le⟩
  exact (intervalIntegral.integral_eq_integral_of_support_subset
    (μ := volume) (f := f) hsupport).symm

lemma fourier_triangleMultiplier_eq_sinc_sq {L ξ : ℝ} (hL : 0 < L) :
    𝓕 (fun x : ℝ => (triangleMultiplier L x : ℂ)) ξ =
      (L * Real.sinc ((-2 * Real.pi * ξ) * L / 2) ^ 2 : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    (∫ v : ℝ,
        Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) •
          (triangleMultiplier L v : ℂ))
        = ∫ v : ℝ,
            (triangleMultiplier L v : ℂ) *
              Complex.exp ((((-2 * Real.pi * ξ) * v : ℝ) : ℂ) * Complex.I) := by
            refine integral_congr_ae ?_
            exact Eventually.of_forall fun v => by
              have harg : -2 * Real.pi * v * ξ = (-2 * Real.pi * ξ) * v := by ring
              have hargC :
                  ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) =
                    ((((-2 * Real.pi * ξ) * v : ℝ) : ℂ) * Complex.I) := by
                rw [harg]
              change
                Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
                    (triangleMultiplier L v : ℂ) =
                  (triangleMultiplier L v : ℂ) *
                    Complex.exp ((((-2 * Real.pi * ξ) * v : ℝ) : ℂ) * Complex.I)
              rw [hargC]
              ring
    _ = ∫ v in -L..L,
          (triangleMultiplier L v : ℂ) *
            Complex.exp ((((-2 * Real.pi * ξ) * v : ℝ) : ℂ) * Complex.I) := by
          exact integral_triangleMultiplier_exp_mul_I_full
            (L := L) (α := -2 * Real.pi * ξ) hL
    _ = (L * Real.sinc ((-2 * Real.pi * ξ) * L / 2) ^ 2 : ℂ) := by
          exact integral_triangleMultiplier_exp_mul_I_eq_sinc_sq
            (L := L) (α := -2 * Real.pi * ξ) hL

lemma fourier_triangleMultiplier_eq {L ξ : ℝ} (hL : 0 < L) :
    𝓕 (fun x : ℝ => (triangleMultiplier L x : ℂ)) ξ =
      (L * Real.sinc (Real.pi * L * ξ) ^ 2 : ℂ) := by
  rw [fourier_triangleMultiplier_eq_sinc_sq hL]
  have harg : (-2 * Real.pi * ξ) * L / 2 = -(Real.pi * L * ξ) := by ring
  rw [harg, Real.sinc_neg]

/-- Polya's smoothing density
`h_L x = (1 - cos (L x)) / (π L x^2)`, with the removable value at zero
filled in as `L / (2π)`. -/
def polyaKernel (L x : ℝ) : ℝ :=
  if x = 0 then L / (2 * Real.pi)
  else (1 - Real.cos (L * x)) / (Real.pi * L * x ^ 2)

@[simp]
lemma polyaKernel_zero (L : ℝ) :
    polyaKernel L 0 = L / (2 * Real.pi) := by
  simp [polyaKernel]

lemma polyaKernel_of_ne {L x : ℝ} (hx : x ≠ 0) :
    polyaKernel L x =
      (1 - Real.cos (L * x)) / (Real.pi * L * x ^ 2) := by
  simp [polyaKernel, hx]

lemma one_sub_cos_nonneg (x : ℝ) :
    0 ≤ 1 - Real.cos x := by
  exact sub_nonneg.mpr (Real.cos_le_one x)

lemma one_sub_cos_le_two (x : ℝ) :
    1 - Real.cos x ≤ 2 := by
  linarith [Real.neg_one_le_cos x]

lemma one_sub_cos_le_sq_div_two (x : ℝ) :
    1 - Real.cos x ≤ x ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

lemma one_sub_cos_eq_two_mul_sin_sq_half (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul_eq_one_sub]
  ring_nf

lemma polyaKernel_eq_sinc_sq {L x : ℝ} (hL : 0 < L) :
    polyaKernel L x =
      (L / (2 * Real.pi)) * (Real.sinc (L * x / 2)) ^ 2 := by
  by_cases hx : x = 0
  · subst x
    simp [polyaKernel]
  · have harg : L * x / 2 ≠ 0 := by
      exact div_ne_zero (mul_ne_zero hL.ne' hx) (by norm_num)
    rw [polyaKernel_of_ne hx, one_sub_cos_eq_two_mul_sin_sq_half,
      Real.sinc_of_ne_zero harg]
    field_simp [Real.pi_ne_zero, hL.ne', hx, harg]

lemma continuous_polyaKernel {L : ℝ} (hL : 0 < L) :
    Continuous (polyaKernel L) := by
  have hfun :
      polyaKernel L =
        fun x : ℝ => (L / (2 * Real.pi)) *
          (Real.sinc (L * x / 2)) ^ 2 := by
    funext x
    exact polyaKernel_eq_sinc_sq (L := L) (x := x) hL
  rw [hfun]
  fun_prop

lemma hasDerivAt_integral_polyaKernel_zero_to {L x : ℝ} (hL : 0 < L) :
    HasDerivAt
      (fun y : ℝ => ∫ z in (0 : ℝ)..y, polyaKernel L z)
      (polyaKernel L x) x :=
  ((continuous_polyaKernel hL).integral_hasStrictDerivAt (0 : ℝ) x).hasDerivAt

lemma sinc_abs (x : ℝ) :
    Real.sinc |x| = Real.sinc x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, Real.sinc_neg]

lemma integral_sinc_sq_comp_mul_left (c : ℝ) :
    (∫ x : ℝ, Real.sinc (c * x) ^ 2) =
      |c⁻¹| * ∫ y : ℝ, Real.sinc y ^ 2 := by
  simpa [smul_eq_mul] using
    (Measure.integral_comp_mul_left (g := fun y : ℝ ↦ Real.sinc y ^ 2) c)

/-- Symmetric finite-window Fourier integral with an explicit frequency.
This is the interval calculation behind the characteristic function of a
uniform law on a symmetric interval. -/
lemma integral_exp_mul_I_eq_sinc_scaled (r θ : ℝ) :
    (∫ x in -r..r, Complex.exp (((θ * x : ℝ) : ℂ) * Complex.I)) =
      (2 * r * Real.sinc (θ * r) : ℂ) := by
  by_cases hθ : θ = 0
  · subst θ
    simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, Real.sinc_zero]
    rw [intervalIntegral.integral_const]
    change ((r - -r : ℝ) : ℂ) * (1 : ℂ) = 2 * (r : ℂ) * (1 : ℂ)
    norm_cast
    ring
  · have hθc : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ
    have hscale :
        (θ : ℂ) *
          (∫ x in -r..r, Complex.exp (((θ * x : ℝ) : ℂ) * Complex.I)) =
            θ * (2 * r * Real.sinc (θ * r) : ℂ) := by
      calc
        (θ : ℂ) *
            (∫ x in -r..r, Complex.exp (((θ * x : ℝ) : ℂ) * Complex.I))
            = θ •
                (∫ x in -r..r,
                  Complex.exp (((θ * x : ℝ) : ℂ) * Complex.I)) := by
              simp [Complex.real_smul]
        _ = ∫ y in θ * (-r)..θ * r, Complex.exp ((y : ℂ) * Complex.I) := by
              simpa only [Complex.real_smul] using
                (intervalIntegral.smul_integral_comp_mul_left
                  (f := fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I))
                  (a := -r) (b := r) θ)
        _ = ∫ y in -(θ * r)..θ * r, Complex.exp ((y : ℂ) * Complex.I) := by
              congr 1
              ring
        _ = (2 * ((θ * r : ℝ) : ℂ) * Real.sinc (θ * r) : ℂ) := by
              exact integral_exp_mul_I_eq_sinc (θ * r)
        _ = θ * (2 * r * Real.sinc (θ * r) : ℂ) := by
              norm_cast
              ring
    exact mul_left_cancel₀ hθc hscale

lemma hasDerivAt_sin_sq_div_id {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.sin y ^ 2 / y)
      (2 * Real.sin x * Real.cos x / x - Real.sin x ^ 2 / x ^ 2) x := by
  have h :=
    ((Real.hasDerivAt_sin x).pow 2).div (hasDerivAt_id x) hx
  convert h using 1
  simp only [Pi.pow_apply, id_eq]
  field_simp [hx]
  ring_nf

lemma integral_sin_sq_div_sq_eq_boundary_add_sin_two_mul_div
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, Real.sin x ^ 2 / x ^ 2 =
      Real.sin a ^ 2 / a - Real.sin b ^ 2 / b +
        ∫ x in a..b, Real.sin (2 * x) / x := by
  have hne : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    exact ne_of_gt (ha.trans_le hxIcc.1)
  have hu :
      ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun y : ℝ ↦ Real.sin y ^ 2)
          (2 * Real.sin x * Real.cos x) x := by
    intro x hx
    simpa using (Real.hasDerivAt_sin x).pow 2
  have hv :
      ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun y : ℝ ↦ -y⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    simpa [pow_two] using (hasDerivAt_inv (hne x hx)).neg
  have hu_int :
      IntervalIntegrable (fun x : ℝ ↦ 2 * Real.sin x * Real.cos x)
        volume a b := by
    exact (by fun_prop : Continuous fun x : ℝ ↦ 2 * Real.sin x * Real.cos x).intervalIntegrable _ _
  have hv_cont :
      ContinuousOn (fun x : ℝ ↦ (x ^ 2)⁻¹) (Set.uIcc a b) := by
    refine ((continuous_id.pow 2).continuousOn).inv₀ ?_
    intro x hx
    exact pow_ne_zero 2 (hne x hx)
  have hv_int :
      IntervalIntegrable (fun x : ℝ ↦ (x ^ 2)⁻¹) volume a b :=
    hv_cont.intervalIntegrable
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x : ℝ ↦ Real.sin x ^ 2)
      (u' := fun x : ℝ ↦ 2 * Real.sin x * Real.cos x)
      (v := fun x : ℝ ↦ -x⁻¹)
      (v' := fun x : ℝ ↦ (x ^ 2)⁻¹)
      hu hv hu_int hv_int
  have hg :
      (∫ x in a..b, (2 * Real.sin x * Real.cos x) * (-x⁻¹)) =
        -∫ x in a..b, Real.sin (2 * x) / x := by
    calc
      (∫ x in a..b, (2 * Real.sin x * Real.cos x) * (-x⁻¹))
          = ∫ x in a..b, -(Real.sin (2 * x) / x) := by
            refine intervalIntegral.integral_congr ?_
            intro x hx
            change 2 * Real.sin x * Real.cos x * -x⁻¹ =
              -(Real.sin (2 * x) / x)
            rw [Real.sin_two_mul]
            field_simp [hne x hx]
      _ = -∫ x in a..b, Real.sin (2 * x) / x := by
            rw [intervalIntegral.integral_neg]
  have hb : 0 < b := ha.trans_le hab
  calc
    ∫ x in a..b, Real.sin x ^ 2 / x ^ 2
        = ∫ x in a..b, Real.sin x ^ 2 * (x ^ 2)⁻¹ := by
            refine intervalIntegral.integral_congr ?_
            intro x hx
            field_simp [hne x hx]
    _ = Real.sin b ^ 2 * (-b⁻¹) - Real.sin a ^ 2 * (-a⁻¹) -
          ∫ x in a..b, (2 * Real.sin x * Real.cos x) * (-x⁻¹) := by
            simpa using hparts
    _ = Real.sin a ^ 2 / a - Real.sin b ^ 2 / b +
          ∫ x in a..b, Real.sin (2 * x) / x := by
            rw [hg]
            field_simp [ha.ne', hb.ne']
            ring

lemma integral_sinc_sq_eq_boundary_add_sin_two_mul_div
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, Real.sinc x ^ 2 =
      Real.sin a ^ 2 / a - Real.sin b ^ 2 / b +
        ∫ x in a..b, Real.sin (2 * x) / x := by
  rw [← integral_sin_sq_div_sq_eq_boundary_add_sin_two_mul_div ha hab]
  refine intervalIntegral.integral_congr ?_
  intro x hx
  have hxIcc : x ∈ Set.Icc a b := by
    simpa [Set.uIcc_of_le hab] using hx
  have hne : x ≠ 0 := ne_of_gt (ha.trans_le hxIcc.1)
  change Real.sinc x ^ 2 = Real.sin x ^ 2 / x ^ 2
  rw [Real.sinc_of_ne_zero hne]
  field_simp [hne]

lemma tendsto_sin_sq_div_id_atTop_zero :
    Tendsto (fun x : ℝ ↦ Real.sin x ^ 2 / x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x ↦ norm_nonneg _) ?_ tendsto_inv_atTop_zero
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hsq_abs : |Real.sin x ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact Real.sin_sq_le_one _
  calc
    ‖Real.sin x ^ 2 / x‖ = |Real.sin x ^ 2| / x := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hxpos]
    _ ≤ 1 / x := by
      exact div_le_div_of_nonneg_right hsq_abs hxpos.le
    _ = x⁻¹ := by
      rw [one_div]

lemma tendsto_integral_sinc_sq_atTop_of_tendsto_dirichlet
    {a I : ℝ} (ha : 0 < a)
    (hdir :
      Tendsto (fun b : ℝ ↦ ∫ x in a..b, Real.sin (2 * x) / x) atTop (𝓝 I)) :
    Tendsto (fun b : ℝ ↦ ∫ x in a..b, Real.sinc x ^ 2) atTop
      (𝓝 (Real.sin a ^ 2 / a + I)) := by
  have hboundary :
      Tendsto (fun b : ℝ ↦ Real.sin a ^ 2 / a - Real.sin b ^ 2 / b) atTop
        (𝓝 (Real.sin a ^ 2 / a)) := by
    simpa using
      ((tendsto_const_nhds (x := Real.sin a ^ 2 / a)).sub
        tendsto_sin_sq_div_id_atTop_zero)
  have htotal :
      Tendsto
        (fun b : ℝ ↦
          Real.sin a ^ 2 / a - Real.sin b ^ 2 / b +
            ∫ x in a..b, Real.sin (2 * x) / x)
        atTop (𝓝 (Real.sin a ^ 2 / a + I)) := by
    simpa [sub_eq_add_neg, add_assoc] using hboundary.add hdir
  refine htotal.congr' ?_
  filter_upwards [eventually_ge_atTop a] with b hb
  rw [integral_sinc_sq_eq_boundary_add_sin_two_mul_div ha hb]

lemma tendsto_sin_sq_div_id_nhds_zero :
    Tendsto (fun x : ℝ ↦ Real.sin x ^ 2 / x) (𝓝 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun x : ℝ ↦ ‖x‖)
    (Eventually.of_forall fun x ↦ norm_nonneg _) ?_ ?_
  · exact Eventually.of_forall fun x ↦ by
      by_cases hx : x = 0
      · simp [hx]
      · have hsin : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs (x := x)
        have hpow : |Real.sin x| ^ 2 ≤ |x| ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hsin 2
        calc
          ‖Real.sin x ^ 2 / x‖ = |Real.sin x| ^ 2 / |x| := by
            rw [Real.norm_eq_abs, abs_div, abs_pow]
          _ ≤ |x| ^ 2 / |x| := by
            exact div_le_div_of_nonneg_right hpow (abs_nonneg x)
          _ = ‖x‖ := by
            rw [Real.norm_eq_abs]
            field_simp [abs_ne_zero.mpr hx]
  · simpa using
      ((tendsto_id : Tendsto (fun x : ℝ ↦ x) (𝓝 0) (𝓝 0)).norm)

lemma tendsto_integral_sinc_sq_nhdsGT_zero_of_tendsto_dirichlet
    {b I : ℝ} (hb : 0 < b)
    (hdir :
      Tendsto (fun a : ℝ ↦ ∫ x in a..b, Real.sin (2 * x) / x) (𝓝[>] 0) (𝓝 I)) :
    Tendsto (fun a : ℝ ↦ ∫ x in a..b, Real.sinc x ^ 2) (𝓝[>] 0)
      (𝓝 (-(Real.sin b ^ 2 / b) + I)) := by
  have hleft :
      Tendsto (fun a : ℝ ↦ Real.sin a ^ 2 / a) (𝓝[>] 0) (𝓝 0) :=
    tendsto_sin_sq_div_id_nhds_zero.mono_left nhdsWithin_le_nhds
  have hboundary :
      Tendsto (fun a : ℝ ↦ Real.sin a ^ 2 / a - Real.sin b ^ 2 / b) (𝓝[>] 0)
        (𝓝 (-(Real.sin b ^ 2 / b))) := by
    simpa using
      (hleft.sub (tendsto_const_nhds (x := Real.sin b ^ 2 / b)))
  have htotal :
      Tendsto
        (fun a : ℝ ↦
          Real.sin a ^ 2 / a - Real.sin b ^ 2 / b +
            ∫ x in a..b, Real.sin (2 * x) / x)
        (𝓝[>] 0) (𝓝 (-(Real.sin b ^ 2 / b) + I)) := by
    simpa [sub_eq_add_neg, add_assoc] using hboundary.add hdir
  refine htotal.congr' ?_
  have hsmall : ∀ᶠ a in 𝓝[>] (0 : ℝ), a ≤ b := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_lt_nhds hb] with a ha _ha_pos
    exact ha.le
  filter_upwards [self_mem_nhdsWithin, hsmall] with a ha_pos hab
  rw [integral_sinc_sq_eq_boundary_add_sin_two_mul_div ha_pos hab]

lemma measurable_polyaKernel (L : ℝ) :
    Measurable (polyaKernel L) := by
  unfold polyaKernel
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  fun_prop

lemma polyaKernel_nonneg {L x : ℝ} (hL : 0 ≤ L) :
    0 ≤ polyaKernel L x := by
  by_cases hx : x = 0
  · subst hx
    rw [polyaKernel_zero]
    exact div_nonneg hL (mul_nonneg (by norm_num) Real.pi_pos.le)
  · rw [polyaKernel_of_ne hx]
    refine div_nonneg (one_sub_cos_nonneg (L * x)) ?_
    exact mul_nonneg (mul_nonneg Real.pi_pos.le hL) (sq_nonneg x)

/-- The elementary inverse-square envelope used for Polya's tail estimate on
the positive half-line. -/
def polyaTailEnvelope (L x : ℝ) : ℝ :=
  (2 / (Real.pi * L)) * x ^ (-2 : ℝ)

lemma polyaTailEnvelope_nonneg_of_pos {L x : ℝ}
    (hL : 0 < L) (hx : 0 < x) :
    0 ≤ polyaTailEnvelope L x := by
  unfold polyaTailEnvelope
  positivity

lemma polyaKernel_even (L x : ℝ) :
    polyaKernel L (-x) = polyaKernel L x := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [polyaKernel_of_ne (neg_ne_zero.mpr hx), polyaKernel_of_ne hx]
    have hcos : Real.cos (L * -x) = Real.cos (L * x) := by
      rw [show L * -x = -(L * x) by ring, Real.cos_neg]
    rw [hcos]
    ring

lemma polyaKernel_le_tailEnvelope_of_pos {L x : ℝ}
    (hL : 0 < L) (hx : 0 < x) :
    polyaKernel L x ≤ polyaTailEnvelope L x := by
  rw [polyaKernel_of_ne hx.ne']
  have hden_pos : 0 < Real.pi * L * x ^ 2 := by
    positivity
  have hnum : 1 - Real.cos (L * x) ≤ 2 := one_sub_cos_le_two (L * x)
  calc
    (1 - Real.cos (L * x)) / (Real.pi * L * x ^ 2)
        ≤ 2 / (Real.pi * L * x ^ 2) :=
          div_le_div_of_nonneg_right hnum hden_pos.le
    _ = polyaTailEnvelope L x := by
          rw [polyaTailEnvelope, Real.rpow_neg hx.le]
          ring_nf
          have hpow : x⁻¹ ^ (2 : ℕ) = (x ^ (2 : ℕ))⁻¹ := by
            rw [inv_pow]
          rw [hpow]
          have hsq : x ^ (2 : ℝ) = x ^ (2 : ℕ) := Real.rpow_natCast x 2
          rw [hsq]

lemma polyaKernel_le_centerBound {L x : ℝ} (hL : 0 < L) :
    polyaKernel L x ≤ L / (2 * Real.pi) := by
  by_cases hx : x = 0
  · subst hx
    rw [polyaKernel_zero]
  · rw [polyaKernel_of_ne hx]
    have hden_pos : 0 < Real.pi * L * x ^ 2 := by
      positivity
    have hnum :
        1 - Real.cos (L * x) ≤ (L * x) ^ 2 / 2 :=
      one_sub_cos_le_sq_div_two (L * x)
    calc
      (1 - Real.cos (L * x)) / (Real.pi * L * x ^ 2)
          ≤ ((L * x) ^ 2 / 2) / (Real.pi * L * x ^ 2) :=
            div_le_div_of_nonneg_right hnum hden_pos.le
      _ = L / (2 * Real.pi) := by
            field_simp [Real.pi_ne_zero, hL.ne', hx]

lemma integral_Ioi_polyaTailEnvelope {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    ∫ x in Set.Ioi a, polyaTailEnvelope L x = 2 / (Real.pi * L * a) := by
  unfold polyaTailEnvelope
  rw [integral_const_mul,
    integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := a) (by norm_num) ha]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp [Real.pi_ne_zero, hL.ne', ha.ne']

lemma two_mul_integral_Ioi_polyaTailEnvelope {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    2 * (∫ x in Set.Ioi a, polyaTailEnvelope L x) =
      4 / (Real.pi * L * a) := by
  rw [integral_Ioi_polyaTailEnvelope hL ha]
  field_simp [Real.pi_ne_zero, hL.ne', ha.ne']
  ring

lemma integrableOn_Ioi_polyaTailEnvelope {L a : ℝ}
    (_hL : 0 < L) (ha : 0 < a) :
    IntegrableOn (polyaTailEnvelope L) (Set.Ioi a) := by
  unfold polyaTailEnvelope
  exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).const_mul _

lemma integrableOn_Iio_neg_polyaTailEnvelope {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    IntegrableOn (fun x => polyaTailEnvelope L (-x)) (Set.Iio (-a)) := by
  have hbase :
      IntegrableOn (polyaTailEnvelope L) (Set.Ioi (-(-a))) := by
    simpa only [neg_neg] using integrableOn_Ioi_polyaTailEnvelope hL ha
  exact hbase.comp_neg_Iio

lemma integral_Iio_neg_polyaTailEnvelope {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    ∫ x in Set.Iio (-a), polyaTailEnvelope L (-x) =
      2 / (Real.pi * L * a) := by
  rw [← integral_Iic_eq_integral_Iio
    (μ := volume) (x := -a) (f := fun x : ℝ => polyaTailEnvelope L (-x))]
  rw [integral_comp_neg_Iic]
  simpa using integral_Ioi_polyaTailEnvelope hL ha

/-- The concrete measure obtained by putting Polya's density against Lebesgue
measure.  Its characteristic function and total mass are formalized as
separate theorems; this definition is the local density-level object used for
tail estimates. -/
def polyaKernelMeasure (L : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (polyaKernel L x)

lemma measureReal_withDensity_ofReal_eq_integral
    {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hf : IntegrableOn f s)
    (hnonneg : 0 ≤ᵐ[volume.restrict s] f) :
    (volume.withDensity fun x => ENNReal.ofReal (f x)).real s =
      ∫ x in s, f x := by
  rw [measureReal_def, withDensity_apply _ hs]
  have hlintegral :
      ENNReal.ofReal (∫ x in s, f x) =
        ∫⁻ x in s, ENNReal.ofReal (f x) :=
    ofReal_integral_eq_lintegral_ofReal hf hnonneg
  have hnonneg_int : 0 ≤ ∫ x in s, f x :=
    integral_nonneg_of_ae hnonneg
  rw [← hlintegral, ENNReal.toReal_ofReal hnonneg_int]

lemma polyaKernelMeasure_apply_Ioi (L a : ℝ) :
    polyaKernelMeasure L (Set.Ioi a) =
      ∫⁻ x in Set.Ioi a, ENNReal.ofReal (polyaKernel L x) := by
  rw [polyaKernelMeasure, withDensity_apply _ measurableSet_Ioi]

lemma polyaKernelMeasure_apply_Iio (L a : ℝ) :
    polyaKernelMeasure L (Set.Iio a) =
      ∫⁻ x in Set.Iio a, ENNReal.ofReal (polyaKernel L x) := by
  rw [polyaKernelMeasure, withDensity_apply _ measurableSet_Iio]

lemma polyaKernelMeasure_Ioi_le_tailEnvelope_lintegral {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    polyaKernelMeasure L (Set.Ioi a) ≤
      ∫⁻ x in Set.Ioi a, ENNReal.ofReal (polyaTailEnvelope L x) := by
  rw [polyaKernelMeasure_apply_Ioi]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact ENNReal.ofReal_le_ofReal
    (polyaKernel_le_tailEnvelope_of_pos hL (ha.trans hx))

lemma polyaKernelMeasure_Iio_neg_le_tailEnvelope_neg_lintegral {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    polyaKernelMeasure L (Set.Iio (-a)) ≤
      ∫⁻ x in Set.Iio (-a), ENNReal.ofReal (polyaTailEnvelope L (-x)) := by
  rw [polyaKernelMeasure_apply_Iio]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
  have hxlt : x < -a := hx
  have hneg_pos : 0 < -x := by linarith
  have hkernel :
      polyaKernel L x = polyaKernel L (-x) := by
    rw [← polyaKernel_even L x]
  rw [hkernel]
  exact ENNReal.ofReal_le_ofReal
    (polyaKernel_le_tailEnvelope_of_pos hL hneg_pos)

lemma polyaKernelMeasure_real_Ioi_le_integral_tailEnvelope {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    (polyaKernelMeasure L).real (Set.Ioi a) ≤
      ∫ x in Set.Ioi a, polyaTailEnvelope L x := by
  have hlin :
      polyaKernelMeasure L (Set.Ioi a) ≤
        ∫⁻ x in Set.Ioi a, ENNReal.ofReal (polyaTailEnvelope L x) :=
    polyaKernelMeasure_Ioi_le_tailEnvelope_lintegral hL ha
  have henv_int : IntegrableOn (polyaTailEnvelope L) (Set.Ioi a) :=
    integrableOn_Ioi_polyaTailEnvelope hL ha
  have henv_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi a)] polyaTailEnvelope L := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact polyaTailEnvelope_nonneg_of_pos hL (ha.trans hx)
  have hlintegral :
      ENNReal.ofReal (∫ x in Set.Ioi a, polyaTailEnvelope L x) =
        ∫⁻ x in Set.Ioi a, ENNReal.ofReal (polyaTailEnvelope L x) :=
    ofReal_integral_eq_lintegral_ofReal henv_int henv_nonneg
  have hfinite :
      (∫⁻ x in Set.Ioi a, ENNReal.ofReal (polyaTailEnvelope L x)) ≠ ∞ := by
    rw [← hlintegral]
    exact ENNReal.ofReal_ne_top
  have htoReal := ENNReal.toReal_mono hfinite hlin
  have hnonneg_int : 0 ≤ ∫ x in Set.Ioi a, polyaTailEnvelope L x :=
    integral_nonneg_of_ae henv_nonneg
  have htoReal' :
      (polyaKernelMeasure L (Set.Ioi a)).toReal ≤
      (ENNReal.ofReal (∫ x in Set.Ioi a, polyaTailEnvelope L x)).toReal := by
    simpa [← hlintegral] using htoReal
  simpa [measureReal_def, ENNReal.toReal_ofReal hnonneg_int] using htoReal'

lemma polyaKernelMeasure_real_Iio_neg_le_integral_tailEnvelope {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    (polyaKernelMeasure L).real (Set.Iio (-a)) ≤
      ∫ x in Set.Iio (-a), polyaTailEnvelope L (-x) := by
  have hlin :
      polyaKernelMeasure L (Set.Iio (-a)) ≤
        ∫⁻ x in Set.Iio (-a), ENNReal.ofReal (polyaTailEnvelope L (-x)) :=
    polyaKernelMeasure_Iio_neg_le_tailEnvelope_neg_lintegral hL ha
  have henv_int :
      IntegrableOn (fun x => polyaTailEnvelope L (-x)) (Set.Iio (-a)) :=
    integrableOn_Iio_neg_polyaTailEnvelope hL ha
  have henv_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Iio (-a))]
        fun x : ℝ => polyaTailEnvelope L (-x) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    have hxlt : x < -a := hx
    have hneg_pos : 0 < -x := by linarith
    exact polyaTailEnvelope_nonneg_of_pos hL hneg_pos
  have hlintegral :
      ENNReal.ofReal (∫ x in Set.Iio (-a), polyaTailEnvelope L (-x)) =
        ∫⁻ x in Set.Iio (-a), ENNReal.ofReal (polyaTailEnvelope L (-x)) :=
    ofReal_integral_eq_lintegral_ofReal henv_int henv_nonneg
  have hfinite :
      (∫⁻ x in Set.Iio (-a), ENNReal.ofReal (polyaTailEnvelope L (-x))) ≠ ∞ := by
    rw [← hlintegral]
    exact ENNReal.ofReal_ne_top
  have htoReal := ENNReal.toReal_mono hfinite hlin
  have hnonneg_int :
      0 ≤ ∫ x in Set.Iio (-a), polyaTailEnvelope L (-x) :=
    integral_nonneg_of_ae henv_nonneg
  have htoReal' :
      (polyaKernelMeasure L (Set.Iio (-a))).toReal ≤
        (ENNReal.ofReal (∫ x in Set.Iio (-a), polyaTailEnvelope L (-x))).toReal := by
    simpa [← hlintegral] using htoReal
  simpa [measureReal_def, ENNReal.toReal_ofReal hnonneg_int] using htoReal'

lemma polyaKernelMeasure_real_Ioi_le_explicit {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    (polyaKernelMeasure L).real (Set.Ioi a) ≤
      2 / (Real.pi * L * a) := by
  calc
    (polyaKernelMeasure L).real (Set.Ioi a)
        ≤ ∫ x in Set.Ioi a, polyaTailEnvelope L x :=
          polyaKernelMeasure_real_Ioi_le_integral_tailEnvelope hL ha
    _ = 2 / (Real.pi * L * a) :=
          integral_Ioi_polyaTailEnvelope hL ha

lemma polyaKernelMeasure_real_Iio_neg_le_explicit {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    (polyaKernelMeasure L).real (Set.Iio (-a)) ≤
      2 / (Real.pi * L * a) := by
  calc
    (polyaKernelMeasure L).real (Set.Iio (-a))
        ≤ ∫ x in Set.Iio (-a), polyaTailEnvelope L (-x) :=
          polyaKernelMeasure_real_Iio_neg_le_integral_tailEnvelope hL ha
    _ = 2 / (Real.pi * L * a) :=
          integral_Iio_neg_polyaTailEnvelope hL ha

lemma integrableOn_Ioi_polyaKernel {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    IntegrableOn (polyaKernel L) (Set.Ioi a) := by
  have henv : IntegrableOn (polyaTailEnvelope L) (Set.Ioi a) :=
    integrableOn_Ioi_polyaTailEnvelope hL ha
  refine henv.integrable.mono' (measurable_polyaKernel L).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (polyaKernel_nonneg hL.le)]
  exact polyaKernel_le_tailEnvelope_of_pos hL (ha.trans hx)

lemma integrableOn_Iio_neg_polyaKernel {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    IntegrableOn (polyaKernel L) (Set.Iio (-a)) := by
  have henv :
      IntegrableOn (fun x => polyaTailEnvelope L (-x)) (Set.Iio (-a)) :=
    integrableOn_Iio_neg_polyaTailEnvelope hL ha
  refine henv.integrable.mono' (measurable_polyaKernel L).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
  have hxlt : x < -a := hx
  have hx0 : x < 0 := by linarith
  have hneg_pos : 0 < -x := neg_pos.mpr hx0
  rw [Real.norm_eq_abs, abs_of_nonneg (polyaKernel_nonneg hL.le),
    ← polyaKernel_even L x]
  exact polyaKernel_le_tailEnvelope_of_pos hL hneg_pos

lemma integrableOn_Icc_polyaKernel {L : ℝ} (hL : 0 < L) :
    IntegrableOn (polyaKernel L) (Set.Icc (-1) 1) := by
  refine IntegrableOn.of_bound (measure_Icc_lt_top (μ := volume))
    (measurable_polyaKernel L).aestronglyMeasurable (L / (2 * Real.pi)) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (polyaKernel_nonneg hL.le)]
  exact polyaKernel_le_centerBound hL

lemma integrable_polyaKernel {L : ℝ} (hL : 0 < L) :
    Integrable (polyaKernel L) := by
  have hneg : IntegrableOn (polyaKernel L) (Set.Iio (-1)) :=
    integrableOn_Iio_neg_polyaKernel hL zero_lt_one
  have hcenter : IntegrableOn (polyaKernel L) (Set.Icc (-1) 1) :=
    integrableOn_Icc_polyaKernel hL
  have hpos : IntegrableOn (polyaKernel L) (Set.Ioi 1) :=
    integrableOn_Ioi_polyaKernel hL zero_lt_one
  have hcover :
      (Set.Iio (-1) ∪ Set.Icc (-1) 1) ∪ Set.Ioi 1 = (Set.univ : Set ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi, Set.mem_univ, iff_true]
    by_cases hxlt : x < -1
    · exact Or.inl (Or.inl hxlt)
    · by_cases hxle : x ≤ 1
      · exact Or.inl (Or.inr ⟨le_of_not_gt hxlt, hxle⟩)
      · exact Or.inr (lt_of_not_ge hxle)
  have hall :
      IntegrableOn (polyaKernel L)
        ((Set.Iio (-1) ∪ Set.Icc (-1) 1) ∪ Set.Ioi 1) :=
    (hneg.union hcenter).union hpos
  rw [hcover, integrableOn_univ] at hall
  exact hall

lemma intervalIntegrable_mul_polyaKernel {L a : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) :
    IntervalIntegrable (fun x : ℝ => x * polyaKernel L x) volume (-a) a := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  refine Measure.integrableOn_of_bounded
    (μ := volume) (s := Set.Ioc (-a) a) measure_Ioc_lt_top.ne
    ((measurable_id.mul (measurable_polyaKernel L)).aestronglyMeasurable)
    (M := a * (L / (2 * Real.pi))) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hxabs : |x| ≤ a := by
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  calc
    ‖x * polyaKernel L x‖ = |x| * polyaKernel L x := by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (polyaKernel_nonneg hL.le)]
    _ ≤ a * (L / (2 * Real.pi)) :=
      mul_le_mul hxabs (polyaKernel_le_centerBound hL)
        (polyaKernel_nonneg hL.le) ha

lemma intervalIntegral_mul_polyaKernel_eq_zero {L a : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) :
    ∫ x in -a..a, x * polyaKernel L x = 0 := by
  let f : ℝ → ℝ := fun x => x * polyaKernel L x
  have hneg_int : IntervalIntegrable f volume (-a) 0 := by
    have h := intervalIntegrable_mul_polyaKernel (L := L) (a := a) hL ha
    simpa [f] using h.mono_set
      (Set.uIcc_subset_uIcc (by simp)
        (Set.mem_uIcc_of_le (by linarith) ha))
  have hpos_int : IntervalIntegrable f volume 0 a := by
    have h := intervalIntegrable_mul_polyaKernel (L := L) (a := a) hL ha
    simpa [f] using h.mono_set
      (Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le (by linarith) ha)
        (by simp))
  have hsplit :
      (∫ x in -a..0, f x) + (∫ x in 0..a, f x) =
        ∫ x in -a..a, f x :=
    intervalIntegral.integral_add_adjacent_intervals hneg_int hpos_int
  rw [← hsplit]
  have hneg_eq : (∫ x in -a..0, f x) = -∫ x in 0..a, f x := by
    calc
      (∫ x in -a..0, f x) = ∫ x in 0..a, f (-x) := by
        simp
      _ = ∫ x in 0..a, -f x := by
        refine intervalIntegral.integral_congr ?_
        intro x _hx
        dsimp [f]
        rw [polyaKernel_even L x]
        ring
      _ = -∫ x in 0..a, f x := by
        rw [intervalIntegral.integral_neg]
  rw [hneg_eq]
  ring

lemma integral_Icc_mul_polyaKernel_eq_zero {L a : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) :
    ∫ x in Set.Icc (-a) a, x * polyaKernel L x = 0 := by
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (μ := volume) (f := fun x : ℝ => x * polyaKernel L x)
    (by linarith)]
  exact intervalIntegral_mul_polyaKernel_eq_zero hL ha

lemma polyaKernelMeasure_integral_id_Icc_eq_zero {L a : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) :
    ∫ x in Set.Icc (-a) a, x ∂(polyaKernelMeasure L) = 0 := by
  rw [polyaKernelMeasure]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    ((measurable_polyaKernel L).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (fun x : ℝ => x) measurableSet_Icc]
  calc
    (∫ x in Set.Icc (-a) a,
        (ENNReal.ofReal (polyaKernel L x)).toReal • x ∂volume)
        = ∫ x in Set.Icc (-a) a, x * polyaKernel L x := by
          refine setIntegral_congr_fun measurableSet_Icc ?_
          intro x _hx
          simp [ENNReal.toReal_ofReal (polyaKernel_nonneg hL.le), mul_comm]
    _ = 0 := integral_Icc_mul_polyaKernel_eq_zero hL ha

lemma integrableOn_id_Icc_of_finite
    (H : Measure ℝ) [IsFiniteMeasure H] {a : ℝ} :
    IntegrableOn (fun x : ℝ => x) (Set.Icc (-a) a) H := by
  refine Measure.integrableOn_of_bounded
    (μ := H) (s := Set.Icc (-a) a) (measure_ne_top H _)
    measurable_id.aestronglyMeasurable (M := a) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hx.1, hx.2⟩

lemma polyaKernelMeasure_integral_affine_Icc {L a c m : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) :
    ∫ x in Set.Icc (-a) a, (c + m * x) ∂(polyaKernelMeasure L) =
      c * (polyaKernelMeasure L).real (Set.Icc (-a) a) := by
  letI : IsFiniteMeasure (polyaKernelMeasure L) :=
    by
      rw [polyaKernelMeasure]
      exact isFiniteMeasure_withDensity_ofReal
        (integrable_polyaKernel hL).hasFiniteIntegral
  have hconst :
      IntegrableOn (fun _ : ℝ => c) (Set.Icc (-a) a) (polyaKernelMeasure L) :=
    (integrable_const c).integrableOn
  have hid :
      IntegrableOn (fun x : ℝ => m * x) (Set.Icc (-a) a) (polyaKernelMeasure L) :=
    ((integrableOn_id_Icc_of_finite (polyaKernelMeasure L)).const_mul m)
  rw [integral_add hconst hid, integral_const, integral_const_mul,
    polyaKernelMeasure_integral_id_Icc_eq_zero hL ha, mul_zero, add_zero]
  rw [measureReal_restrict_apply₀
    (μ := polyaKernelMeasure L) (s := Set.Icc (-a) a) (t := Set.univ)
    MeasurableSet.univ.nullMeasurableSet]
  simp [mul_comm]

lemma polyaKernelMeasure_real_Iic_eq_integral {L t : ℝ} (hL : 0 < L) :
    (polyaKernelMeasure L).real (Set.Iic t) =
      ∫ x in Set.Iic t, polyaKernel L x := by
  rw [polyaKernelMeasure]
  refine measureReal_withDensity_ofReal_eq_integral measurableSet_Iic
    (Integrable.integrableOn (integrable_polyaKernel hL)) ?_
  exact Eventually.of_forall fun x => polyaKernel_nonneg hL.le

lemma polyaKernelMeasure_real_Ici_eq_integral {L t : ℝ} (hL : 0 < L) :
    (polyaKernelMeasure L).real (Set.Ici t) =
      ∫ x in Set.Ici t, polyaKernel L x := by
  rw [polyaKernelMeasure]
  refine measureReal_withDensity_ofReal_eq_integral measurableSet_Ici
    (Integrable.integrableOn (integrable_polyaKernel hL)) ?_
  exact Eventually.of_forall fun x => polyaKernel_nonneg hL.le

lemma integrable_sinc_sq :
    Integrable (fun x : ℝ ↦ Real.sinc x ^ 2) := by
  have hpolya : Integrable (fun x : ℝ ↦ Real.pi * polyaKernel 2 x) :=
    (integrable_polyaKernel (by norm_num : (0 : ℝ) < 2)).const_mul Real.pi
  refine hpolya.congr ?_
  filter_upwards with x
  have hkernel := polyaKernel_eq_sinc_sq (L := 2) (x := x) (by norm_num : (0 : ℝ) < 2)
  rw [hkernel]
  field_simp [Real.pi_ne_zero]

lemma fourier_triangleMultiplier_eq_scaled_polyaKernel {L ξ : ℝ} (hL : 0 < L) :
    𝓕 (fun x : ℝ => (triangleMultiplier L x : ℂ)) ξ =
      (2 * Real.pi * polyaKernel L (2 * Real.pi * ξ) : ℂ) := by
  rw [fourier_triangleMultiplier_eq hL, polyaKernel_eq_sinc_sq hL]
  norm_cast
  have harg : L * (2 * Real.pi * ξ) / 2 = Real.pi * L * ξ := by ring
  rw [harg]
  field_simp [Real.pi_ne_zero]

lemma integrable_fourier_triangleMultiplier {L : ℝ} (hL : 0 < L) :
    Integrable (𝓕 (fun x : ℝ => (triangleMultiplier L x : ℂ))) := by
  have hscale : Real.pi * L ≠ 0 := mul_ne_zero Real.pi_ne_zero hL.ne'
  have hreal :
      Integrable (fun ξ : ℝ => L * Real.sinc ((Real.pi * L) * ξ) ^ 2) :=
    (integrable_sinc_sq.comp_mul_left' hscale).const_mul L
  have hcomplex :
      Integrable (fun ξ : ℝ =>
        ((L * Real.sinc ((Real.pi * L) * ξ) ^ 2 : ℝ) : ℂ)) := by
    refine (hreal.smul_const (1 : ℂ)).congr ?_
    exact Eventually.of_forall fun ξ => by
      change
        (L * Real.sinc (Real.pi * L * ξ) ^ 2) • (1 : ℂ) =
          ((L * Real.sinc (Real.pi * L * ξ) ^ 2 : ℝ) : ℂ)
      rw [Algebra.smul_def]
      simp
  exact hcomplex.congr (Eventually.of_forall fun ξ => by
    rw [fourier_triangleMultiplier_eq hL]
    norm_cast)

lemma integral_sinc_sq_eq_two_mul_integral_Ioi :
    (∫ x : ℝ, Real.sinc x ^ 2) =
      2 * ∫ x in Set.Ioi (0 : ℝ), Real.sinc x ^ 2 := by
  rw [← integral_comp_abs (f := fun x : ℝ ↦ Real.sinc x ^ 2)]
  refine integral_congr_ae ?_
  exact Eventually.of_forall fun x ↦ by
    change Real.sinc x ^ 2 = Real.sinc |x| ^ 2
    rw [sinc_abs]

lemma tendsto_integral_sinc_sq_zero_to_atTop :
    Tendsto (fun b : ℝ ↦ ∫ x in (0 : ℝ)..b, Real.sinc x ^ 2) atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ), Real.sinc x ^ 2)) := by
  exact intervalIntegral_tendsto_integral_Ioi 0 integrable_sinc_sq.integrableOn tendsto_id

lemma integral_sinc_sq_eq_pi_of_integral_Ioi_eq_pi_div_two
    (hIoi : ∫ x in Set.Ioi (0 : ℝ), Real.sinc x ^ 2 = Real.pi / 2) :
    (∫ x : ℝ, Real.sinc x ^ 2) = Real.pi := by
  rw [integral_sinc_sq_eq_two_mul_integral_Ioi, hIoi]
  ring

lemma isFiniteMeasure_polyaKernelMeasure {L : ℝ} (hL : 0 < L) :
    IsFiniteMeasure (polyaKernelMeasure L) := by
  rw [polyaKernelMeasure]
  exact isFiniteMeasure_withDensity_ofReal (integrable_polyaKernel hL).hasFiniteIntegral

lemma polyaKernelMeasure_univ_eq_integral {L : ℝ} (hL : 0 < L) :
    (polyaKernelMeasure L) Set.univ =
      ENNReal.ofReal (∫ x, polyaKernel L x) := by
  rw [polyaKernelMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_polyaKernel hL)
    (Eventually.of_forall fun x ↦ polyaKernel_nonneg hL.le)).symm

lemma isProbabilityMeasure_polyaKernelMeasure_of_integral_eq_one {L : ℝ}
    (hL : 0 < L) (hmass : ∫ x, polyaKernel L x = 1) :
    IsProbabilityMeasure (polyaKernelMeasure L) := by
  constructor
  rw [polyaKernelMeasure_univ_eq_integral hL, hmass]
  simp

lemma integral_polyaKernel_eq_one_of_integral_sinc_sq_eq_pi {L : ℝ}
    (hL : 0 < L) (hsinc : ∫ x : ℝ, Real.sinc x ^ 2 = Real.pi) :
    ∫ x : ℝ, polyaKernel L x = 1 := by
  have hkernel :
      (∫ x : ℝ, polyaKernel L x) =
        ∫ x : ℝ, (L / (2 * Real.pi)) * (Real.sinc (L * x / 2)) ^ 2 := by
    refine integral_congr_ae ?_
    exact Eventually.of_forall fun x ↦ polyaKernel_eq_sinc_sq hL
  have harg :
      (∫ x : ℝ, Real.sinc (L * x / 2) ^ 2) =
        ∫ x : ℝ, Real.sinc ((L / 2) * x) ^ 2 := by
    refine integral_congr_ae ?_
    exact Eventually.of_forall fun x ↦ by
      have h : L * x / 2 = (L / 2) * x := by ring
      change Real.sinc (L * x / 2) ^ 2 = Real.sinc (L / 2 * x) ^ 2
      rw [h]
  have hscale :
      (∫ x : ℝ, Real.sinc (L * x / 2) ^ 2) = (2 / L) * Real.pi := by
    have hpos : 0 < L / 2 := by positivity
    rw [harg, integral_sinc_sq_comp_mul_left (c := L / 2), hsinc]
    have habs : |(L / 2)⁻¹| = 2 / L := by
      rw [abs_of_pos (inv_pos.mpr hpos)]
      field_simp [hL.ne']
    rw [habs]
  rw [hkernel, integral_const_mul, hscale]
  field_simp [hL.ne', Real.pi_ne_zero]

lemma integral_polyaKernel_eq_one_of_integral_Ioi_sinc_sq_eq_pi_div_two {L : ℝ}
    (hL : 0 < L)
    (hIoi : ∫ x in Set.Ioi (0 : ℝ), Real.sinc x ^ 2 = Real.pi / 2) :
    ∫ x : ℝ, polyaKernel L x = 1 :=
  integral_polyaKernel_eq_one_of_integral_sinc_sq_eq_pi hL
    (integral_sinc_sq_eq_pi_of_integral_Ioi_eq_pi_div_two hIoi)

lemma isProbabilityMeasure_polyaKernelMeasure_of_integral_sinc_sq_eq_pi {L : ℝ}
    (hL : 0 < L) (hsinc : ∫ x : ℝ, Real.sinc x ^ 2 = Real.pi) :
    IsProbabilityMeasure (polyaKernelMeasure L) :=
  isProbabilityMeasure_polyaKernelMeasure_of_integral_eq_one hL
    (integral_polyaKernel_eq_one_of_integral_sinc_sq_eq_pi hL hsinc)

lemma charFun_polyaKernelMeasure_eq_integral_smul {L θ : ℝ} (hL : 0 < L) :
    charFun (polyaKernelMeasure L) θ =
      ∫ x, (polyaKernel L x) • Complex.exp (θ * x * Complex.I) := by
  rw [charFun_apply_real, polyaKernelMeasure]
  have hmeas : Measurable (fun x : ℝ ↦ ENNReal.ofReal (polyaKernel L x)) := by
    exact (measurable_polyaKernel L).ennreal_ofReal
  have htop :
      ∀ᵐ x ∂(volume : Measure ℝ),
        ENNReal.ofReal (polyaKernel L x) < ∞ := by
    simp
  rw [integral_withDensity_eq_integral_toReal_smul hmeas htop]
  refine integral_congr_ae ?_
  exact Eventually.of_forall fun x ↦ by
    change
      (ENNReal.ofReal (polyaKernel L x)).toReal •
          Complex.exp (θ * x * Complex.I) =
        (polyaKernel L x) • Complex.exp (θ * x * Complex.I)
    rw [ENNReal.toReal_ofReal (polyaKernel_nonneg hL.le)]

lemma charFun_polyaKernelMeasure_eq_integral_mul {L θ : ℝ} (hL : 0 < L) :
    charFun (polyaKernelMeasure L) θ =
      ∫ x, (polyaKernel L x : ℂ) * Complex.exp (θ * x * Complex.I) := by
  rw [charFun_polyaKernelMeasure_eq_integral_smul hL]
  refine integral_congr_ae ?_
  exact Eventually.of_forall fun x ↦ by
    simp

lemma integral_polyaKernel_exp_mul_I_eq_triangle {L θ : ℝ} (hL : 0 < L) :
    (∫ x : ℝ,
      (polyaKernel L x : ℂ) *
        Complex.exp (((θ * x : ℝ) : ℂ) * Complex.I)) =
      (triangleMultiplier L θ : ℂ) := by
  let f : ℝ → ℂ := fun x => (triangleMultiplier L x : ℂ)
  let g : ℝ → ℂ := fun x =>
    (polyaKernel L x : ℂ) *
      Complex.exp (((θ * x : ℝ) : ℂ) * Complex.I)
  have hcont : Continuous f := by
    exact Complex.continuous_ofReal.comp (continuous_triangleMultiplier L)
  have hfint : Integrable f := by
    refine ((integrable_triangleMultiplier hL).smul_const (1 : ℂ)).congr ?_
    exact Eventually.of_forall fun x => by
      change triangleMultiplier L x • (1 : ℂ) = (triangleMultiplier L x : ℂ)
      rw [Algebra.smul_def]
      simp
  have hfourier_int : Integrable (𝓕 f) := by
    simpa [f] using integrable_fourier_triangleMultiplier hL
  have hinv :
      𝓕⁻ (𝓕 f) θ = f θ :=
    congr_fun (Continuous.fourierInv_fourier_eq hcont hfint hfourier_int) θ
  have hscale :
      (∫ v : ℝ,
        Complex.exp ((↑(2 * Real.pi * v * θ) : ℂ) * Complex.I) •
          𝓕 f v) =
        ∫ x : ℝ, g x := by
    have htwoπ_pos : 0 < 2 * Real.pi := by positivity
    calc
      (∫ v : ℝ,
          Complex.exp ((↑(2 * Real.pi * v * θ) : ℂ) * Complex.I) •
            𝓕 f v)
          = ∫ v : ℝ, (2 * Real.pi : ℝ) • g ((2 * Real.pi) * v) := by
              refine integral_congr_ae ?_
              exact Eventually.of_forall fun v => by
                have hfour :
                    𝓕 f v =
                      (2 * Real.pi * polyaKernel L (2 * Real.pi * v) : ℂ) := by
                  dsimp [f]
                  exact fourier_triangleMultiplier_eq_scaled_polyaKernel
                    (L := L) (ξ := v) hL
                have harg :
                    2 * Real.pi * v * θ = θ * ((2 * Real.pi) * v) := by ring
                have hargC :
                    (2 * (Real.pi : ℂ) * (v : ℂ) * (θ : ℂ) * Complex.I) =
                      ((θ : ℂ) * (2 * (Real.pi : ℂ) * (v : ℂ)) * Complex.I) := by
                  ring
                change
                  Complex.exp ((↑(2 * Real.pi * v * θ) : ℂ) * Complex.I) *
                      𝓕 f v =
                    (2 * Real.pi : ℝ) • g ((2 * Real.pi) * v)
                rw [hfour]
                simp [g]
                rw [hargC]
                ring
      _ = (2 * Real.pi : ℝ) •
            (∫ v : ℝ, g ((2 * Real.pi) * v)) := by
              exact integral_smul (𝕜 := ℝ)
                (c := 2 * Real.pi)
                (f := fun v : ℝ => g ((2 * Real.pi) * v))
      _ = (2 * Real.pi : ℝ) •
            (|(2 * Real.pi)⁻¹| • ∫ y : ℝ, g y) := by
              exact congrArg (fun z : ℂ => (2 * Real.pi : ℝ) • z)
                (Measure.integral_comp_mul_left g (2 * Real.pi))
      _ = ∫ y : ℝ, g y := by
              rw [abs_of_pos (inv_pos.mpr htwoπ_pos)]
              calc
                (2 * Real.pi : ℝ) • (2 * Real.pi)⁻¹ • (∫ y : ℝ, g y)
                    = ((2 * Real.pi) * (2 * Real.pi)⁻¹ : ℝ) •
                        (∫ y : ℝ, g y) := by
                      exact smul_smul (2 * Real.pi) ((2 * Real.pi)⁻¹)
                        (∫ y : ℝ, g y)
                _ = ∫ y : ℝ, g y := by
                      simp [Algebra.smul_def, mul_comm, mul_left_comm]
  calc
    (∫ x : ℝ,
      (polyaKernel L x : ℂ) *
        Complex.exp (((θ * x : ℝ) : ℂ) * Complex.I))
        = ∫ x : ℝ, g x := rfl
    _ = ∫ v : ℝ,
          Complex.exp ((↑(2 * Real.pi * v * θ) : ℂ) * Complex.I) •
            𝓕 f v := hscale.symm
    _ = 𝓕⁻ (𝓕 f) θ := by
          rw [Real.fourierInv_eq']
          refine integral_congr_ae ?_
          exact Eventually.of_forall fun v => by
            have hinner : inner ℝ v θ = v * θ := by
              simp [inner]
              ring_nf
            have harg :
                ((↑(2 * Real.pi * v * θ) : ℂ) * Complex.I) =
                  ((↑(2 * Real.pi * inner ℝ v θ) : ℂ) * Complex.I) := by
              rw [hinner]
              ring_nf
            change
              Complex.exp ((↑(2 * Real.pi * v * θ) : ℂ) * Complex.I) •
                  𝓕 f v =
                Complex.exp ((↑(2 * Real.pi * inner ℝ v θ) : ℂ) * Complex.I) •
                  𝓕 f v
            rw [harg]
    _ = f θ := hinv
    _ = (triangleMultiplier L θ : ℂ) := rfl

lemma integral_polyaKernel_eq_one {L : ℝ} (hL : 0 < L) :
    ∫ x : ℝ, polyaKernel L x = 1 := by
  have h :=
    integral_polyaKernel_exp_mul_I_eq_triangle (L := L) (θ := 0) hL
  simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one] at h
  have h' :
      (↑(∫ x : ℝ, polyaKernel L x) : ℂ) =
        (triangleMultiplier L 0 : ℂ) := by
    have hleft :
        (∫ x : ℝ, (polyaKernel L x : ℂ)) =
          (↑(∫ x : ℝ, polyaKernel L x) : ℂ) := by
      exact (integral_ofReal (𝕜 := ℂ)
        (f := fun x : ℝ => polyaKernel L x) (μ := volume))
    rwa [hleft] at h
  have htri : triangleMultiplier L 0 = 1 := triangleMultiplier_zero hL
  rw [htri] at h'
  exact Complex.ofReal_injective h'

lemma isProbabilityMeasure_polyaKernelMeasure {L : ℝ} (hL : 0 < L) :
    IsProbabilityMeasure (polyaKernelMeasure L) :=
  isProbabilityMeasure_polyaKernelMeasure_of_integral_eq_one hL
    (integral_polyaKernel_eq_one hL)

lemma integral_Iic_zero_polyaKernel_eq_half {L : ℝ} (hL : 0 < L) :
    ∫ x in Set.Iic (0 : ℝ), polyaKernel L x = 1 / 2 := by
  have hleft : IntegrableOn (polyaKernel L) (Set.Iic (0 : ℝ)) :=
    (integrable_polyaKernel hL).integrableOn
  have hright : IntegrableOn (polyaKernel L) (Set.Ioi (0 : ℝ)) :=
    (integrable_polyaKernel hL).integrableOn
  have hsymm :
      ∫ x in Set.Iic (0 : ℝ), polyaKernel L x =
        ∫ x in Set.Ioi (0 : ℝ), polyaKernel L x := by
    calc
      ∫ x in Set.Iic (0 : ℝ), polyaKernel L x
          = ∫ x in Set.Iic (0 : ℝ), polyaKernel L (-x) := by
              refine setIntegral_congr_fun measurableSet_Iic ?_
              intro x _hx
              exact (polyaKernel_even L x).symm
      _ = ∫ x in Set.Ioi (-(0 : ℝ)), polyaKernel L x := by
            rw [integral_comp_neg_Iic]
      _ = ∫ x in Set.Ioi (0 : ℝ), polyaKernel L x := by simp
  have hsplit :=
    intervalIntegral.integral_Iic_add_Ioi
      (f := polyaKernel L) (b := (0 : ℝ)) hleft hright
  rw [← hsymm, integral_polyaKernel_eq_one hL] at hsplit
  linarith

lemma polyaKernelMeasure_real_Iic_zero_eq_half {L : ℝ} (hL : 0 < L) :
    (polyaKernelMeasure L).real (Set.Iic (0 : ℝ)) = 1 / 2 := by
  rw [polyaKernelMeasure_real_Iic_eq_integral (L := L) (t := 0) hL,
    integral_Iic_zero_polyaKernel_eq_half hL]

/-- The concrete Polya CDF is `1/2` plus the signed integral of its density
from `0` to `x`. -/
lemma polyaKernelMeasure_real_Iic_eq_half_add_integral
    {L x : ℝ} (hL : 0 < L) :
    (polyaKernelMeasure L).real (Set.Iic x) =
      1 / 2 + ∫ y in (0 : ℝ)..x, polyaKernel L y := by
  have hIicx : IntegrableOn (polyaKernel L) (Set.Iic x) :=
    (integrable_polyaKernel hL).integrableOn
  have hIic0 : IntegrableOn (polyaKernel L) (Set.Iic (0 : ℝ)) :=
    (integrable_polyaKernel hL).integrableOn
  have hsub :=
    intervalIntegral.integral_Iic_sub_Iic
      (f := polyaKernel L) (a := (0 : ℝ)) (b := x) hIic0 hIicx
  let A : ℝ := ∫ y in Set.Iic x, polyaKernel L y
  let B : ℝ := ∫ y in Set.Iic (0 : ℝ), polyaKernel L y
  let C : ℝ := ∫ y in (0 : ℝ)..x, polyaKernel L y
  have hsub' : A - B = C := by simpa [A, B, C] using hsub
  have hA : A = B + C := by linarith
  have hB : B = 1 / 2 := by
    simpa [B] using integral_Iic_zero_polyaKernel_eq_half hL
  rw [polyaKernelMeasure_real_Iic_eq_integral (L := L) (t := x) hL]
  calc
    ∫ y in Set.Iic x, polyaKernel L y = B + C := by
      simpa [A] using hA
    _ = 1 / 2 + ∫ y in (0 : ℝ)..x, polyaKernel L y := by
      rw [hB]

end PolyaKernel

section PolyaSmoothing

/-- A measure whose characteristic function is Polya's triangular multiplier.
This local predicate lets the Fourier smoothing proof use the kernel abstractly
while the density-level existence proof is formalized separately. -/
structure IsPolyaKernelMeasure (H : Measure ℝ) (L : ℝ) : Prop where
  probability : IsProbabilityMeasure H
  charFun_eq : ∀ θ : ℝ, charFun H θ = (triangleMultiplier L θ : ℂ)

lemma isPolyaKernelMeasure_polyaKernelMeasure_of_integral_eq_one_of_charFun_eq
    {L : ℝ} (hL : 0 < L) (hmass : ∫ x, polyaKernel L x = 1)
    (hchar :
      ∀ θ : ℝ,
        (∫ x, (polyaKernel L x : ℂ) * Complex.exp (θ * x * Complex.I)) =
          (triangleMultiplier L θ : ℂ)) :
    IsPolyaKernelMeasure (polyaKernelMeasure L) L := by
  refine ⟨isProbabilityMeasure_polyaKernelMeasure_of_integral_eq_one hL hmass, ?_⟩
  intro θ
  rw [charFun_polyaKernelMeasure_eq_integral_mul hL, hchar θ]

lemma isPolyaKernelMeasure_polyaKernelMeasure {L : ℝ} (hL : 0 < L) :
    IsPolyaKernelMeasure (polyaKernelMeasure L) L := by
  refine ⟨isProbabilityMeasure_polyaKernelMeasure hL, ?_⟩
  intro θ
  rw [charFun_polyaKernelMeasure_eq_integral_mul hL]
  simpa [mul_assoc] using
    integral_polyaKernel_exp_mul_I_eq_triangle (L := L) (θ := θ) hL

/-- Smoothing a law by convolution with a Polya kernel law. -/
def polyaSmooth (μ H : Measure ℝ) : Measure ℝ :=
  μ ∗ H

lemma polyaKernelMeasure_absolutelyContinuous_volume (L : ℝ) :
    polyaKernelMeasure L ≪ volume := by
  rw [polyaKernelMeasure]
  exact withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (polyaKernel L x))

lemma polyaSmooth_polyaKernelMeasure_absolutelyContinuous_volume
    (μ : Measure ℝ) {L : ℝ} (hL : 0 < L) :
    polyaSmooth μ (polyaKernelMeasure L) ≪ volume := by
  letI : IsProbabilityMeasure (polyaKernelMeasure L) :=
    isProbabilityMeasure_polyaKernelMeasure hL
  dsimp [polyaSmooth]
  exact Measure.conv_absolutelyContinuous
    (polyaKernelMeasure_absolutelyContinuous_volume L)

lemma hasPDF_id_polyaSmooth_polyaKernelMeasure
    (μ : Measure ℝ) [IsFiniteMeasure μ] {L : ℝ} (hL : 0 < L) :
    HasPDF (fun x : ℝ => x)
      (polyaSmooth μ (polyaKernelMeasure L)) volume := by
  letI : IsProbabilityMeasure (polyaKernelMeasure L) :=
    isProbabilityMeasure_polyaKernelMeasure hL
  haveI : IsFiniteMeasure (polyaSmooth μ (polyaKernelMeasure L)) := by
    dsimp [polyaSmooth]
    infer_instance
  have hac : polyaSmooth μ (polyaKernelMeasure L) ≪ volume :=
    polyaSmooth_polyaKernelMeasure_absolutelyContinuous_volume μ hL
  rw [Real.hasPDF_iff_of_aemeasurable (by simpa using measurable_id.aemeasurable)]
  simpa using hac

lemma isProbabilityMeasure_polyaSmooth
    (μ H : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure H] :
    IsProbabilityMeasure (polyaSmooth μ H) := by
  dsimp [polyaSmooth]
  infer_instance

lemma charFun_polyaSmooth_eq
    (μ H : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure H] (θ : ℝ) :
    charFun (polyaSmooth μ H) θ = charFun μ θ * charFun H θ := by
  rw [polyaSmooth, charFun_conv]

lemma charFun_polyaSmooth_eq_triangle
    (μ H : Measure ℝ) [IsFiniteMeasure μ] {L θ : ℝ}
    (hH : IsPolyaKernelMeasure H L) :
    charFun (polyaSmooth μ H) θ =
      charFun μ θ * (triangleMultiplier L θ : ℂ) := by
  letI : IsProbabilityMeasure H := hH.probability
  rw [charFun_polyaSmooth_eq, hH.charFun_eq]

lemma polyaSmoothed_charFun_sub_eq
    (μ ν H : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {L θ : ℝ}
    (hH : IsPolyaKernelMeasure H L) :
    charFun (polyaSmooth μ H) θ - charFun (polyaSmooth ν H) θ =
      (charFun μ θ - charFun ν θ) * (triangleMultiplier L θ : ℂ) := by
  letI : IsProbabilityMeasure H := hH.probability
  rw [charFun_polyaSmooth_eq_triangle μ H hH,
    charFun_polyaSmooth_eq_triangle ν H hH]
  ring

lemma polyaSmoothed_fourierIntegrand_le
    (μ ν H : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {L θ : ℝ} (hL : 0 < L) (hH : IsPolyaKernelMeasure H L) :
    ‖charFun (polyaSmooth μ H) θ - charFun (polyaSmooth ν H) θ‖ / |θ|
      ≤ ‖charFun μ θ - charFun ν θ‖ / |θ| := by
  have htri_nonneg : 0 ≤ triangleMultiplier L θ :=
    triangleMultiplier_nonneg L θ
  have htri_norm :
      ‖(triangleMultiplier L θ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htri_nonneg]
    exact triangleMultiplier_le_one hL
  rw [polyaSmoothed_charFun_sub_eq μ ν H hH, norm_mul]
  have hmul :
      ‖charFun μ θ - charFun ν θ‖ * ‖(triangleMultiplier L θ : ℂ)‖
        ≤ ‖charFun μ θ - charFun ν θ‖ := by
    simpa [mul_one] using
      mul_le_mul_of_nonneg_left htri_norm
        (norm_nonneg (charFun μ θ - charFun ν θ))
  exact div_le_div_of_nonneg_right
    hmul (abs_nonneg θ)

lemma integrableOn_polyaSmoothed_fourierIntegrand_of_integrable
    (μ ν H : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {L : ℝ} (hL : 0 < L) (hH : IsPolyaKernelMeasure H L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    IntegrableOn
      (fun θ : ℝ =>
        ‖charFun (polyaSmooth μ H) θ - charFun (polyaSmooth ν H) θ‖ / |θ|)
      (Set.Icc (-L) L) := by
  letI : IsProbabilityMeasure H := hH.probability
  haveI : IsFiniteMeasure (polyaSmooth μ H) := by
    dsimp [polyaSmooth]
    infer_instance
  haveI : IsFiniteMeasure (polyaSmooth ν H) := by
    dsimp [polyaSmooth]
    infer_instance
  refine hOrigInt.integrable.mono' ?_ ?_
  · exact ((measurable_charFun.sub measurable_charFun).norm.div measurable_abs).aestronglyMeasurable
  · exact Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (norm_nonneg _) (abs_nonneg θ))]
      exact polyaSmoothed_fourierIntegrand_le μ ν H hL hH

end PolyaSmoothing

section FourierInversion

/-- The nonnegative truncated Fourier distance integral from Esseen's smoothing
inequality.  At `θ = 0` Lean's real division convention gives value `0`; the
analytic proof supplies separate regularity hypotheses when this integral is
used as an improper/singular integral. -/
def fourierDistanceIntegralOfFns (φ ψ : ℝ → ℂ) (L : ℝ) : ℝ :=
  ∫ θ in Set.Icc (-L) L, ‖φ θ - ψ θ‖ / |θ|

/-- The measure-level version using characteristic functions. -/
def fourierDistanceIntegral (μ ν : Measure ℝ) (L : ℝ) : ℝ :=
  fourierDistanceIntegralOfFns (charFun μ) (charFun ν) L

lemma fourierDistanceIntegrand_nonneg (φ ψ : ℝ → ℂ) (θ : ℝ) :
    0 ≤ ‖φ θ - ψ θ‖ / |θ| := by
  exact div_nonneg (norm_nonneg _) (abs_nonneg θ)

lemma fourierDistanceIntegralOfFns_nonneg (φ ψ : ℝ → ℂ) (L : ℝ) :
    0 ≤ fourierDistanceIntegralOfFns φ ψ L := by
  unfold fourierDistanceIntegralOfFns
  exact integral_nonneg fun θ => fourierDistanceIntegrand_nonneg φ ψ θ

lemma fourierDistanceIntegral_nonneg (μ ν : Measure ℝ) (L : ℝ) :
    0 ≤ fourierDistanceIntegral μ ν L :=
  fourierDistanceIntegralOfFns_nonneg (charFun μ) (charFun ν) L

/-- Integrating the triangular-multiplier bound: Polya smoothing cannot
increase the truncated Fourier distance.  The integrability hypotheses are
kept explicit because the integrand has the usual removable singularity at
`θ = 0`. -/
lemma fourierDistanceIntegral_polyaSmooth_le
    (μ ν H : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {L : ℝ} (hL : 0 < L) (hH : IsPolyaKernelMeasure H L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    fourierDistanceIntegral (polyaSmooth μ H) (polyaSmooth ν H) L ≤
      fourierDistanceIntegral μ ν L := by
  unfold fourierDistanceIntegral fourierDistanceIntegralOfFns
  have hSmoothInt :
      IntegrableOn
        (fun θ : ℝ =>
          ‖charFun (polyaSmooth μ H) θ - charFun (polyaSmooth ν H) θ‖ / |θ|)
        (Set.Icc (-L) L) :=
    integrableOn_polyaSmoothed_fourierIntegrand_of_integrable μ ν H hL hH hOrigInt
  exact setIntegral_mono_on hSmoothInt hOrigInt measurableSet_Icc
    (fun θ _hθ => polyaSmoothed_fourierIntegrand_le μ ν H hL hH)

/-- The inversion integrand
`- e^{-i θ x} (φ θ - ψ θ) / (i θ)`.

The minus sign matches the positive characteristic-function convention
`φ(t) = ∫ exp(i t x) dμ(x)`: differentiating the CDF inversion integral in
`x` then gives the inverse Fourier density with the correct sign. -/
def inversionKernelIntegrand (φ ψ : ℝ → ℂ) (x θ : ℝ) : ℂ :=
  - (Complex.exp (((-(θ * x)) : ℝ) * Complex.I) *
      ((φ θ - ψ θ) / (Complex.I * (θ : ℂ))))

lemma norm_inversionKernelIntegrand (φ ψ : ℝ → ℂ) (x θ : ℝ) :
    ‖inversionKernelIntegrand φ ψ x θ‖ =
      ‖φ θ - ψ θ‖ / |θ| := by
  rw [inversionKernelIntegrand, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_div, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs]
  ring

/-- The truncated inversion integral over `[-L,L]`. -/
def inversionIntegral (φ ψ : ℝ → ℂ) (x L : ℝ) : ℂ :=
  ∫ θ in Set.Icc (-L) L, inversionKernelIntegrand φ ψ x θ

lemma norm_inversionIntegral_le_fourierDistance
    (φ ψ : ℝ → ℂ) (x L : ℝ) :
    ‖inversionIntegral φ ψ x L‖ ≤
      fourierDistanceIntegralOfFns φ ψ L := by
  unfold inversionIntegral fourierDistanceIntegralOfFns
  calc
    ‖∫ θ in Set.Icc (-L) L, inversionKernelIntegrand φ ψ x θ‖
        ≤ ∫ θ in Set.Icc (-L) L, ‖inversionKernelIntegrand φ ψ x θ‖ :=
          norm_integral_le_integral_norm _
    _ = ∫ θ in Set.Icc (-L) L, ‖φ θ - ψ θ‖ / |θ| := by
          refine integral_congr_ae ?_
          exact Eventually.of_forall fun θ => norm_inversionKernelIntegrand φ ψ x θ

lemma abs_re_inversionIntegral_le_fourierDistance
    (φ ψ : ℝ → ℂ) (x L : ℝ) :
    |(inversionIntegral φ ψ x L).re| ≤
      fourierDistanceIntegralOfFns φ ψ L :=
  (Complex.abs_re_le_norm _).trans
    (norm_inversionIntegral_le_fourierDistance φ ψ x L)

/-- Book-form inversion identity for a pair of CDFs and two characteristic
functions after smoothing/truncation. -/
def inversionCDFFormulaFor
    (μ ν : Measure ℝ) (φ ψ : ℝ → ℂ) (L : ℝ) : Prop :=
  ∀ x : ℝ,
    μ.real (Set.Iic x) - ν.real (Set.Iic x) =
      (1 / (2 * Real.pi)) * (inversionIntegral φ ψ x L).re

lemma measureCDFErrorLE_of_inversionCDFFormula
    {μ ν : Measure ℝ} {φ ψ : ℝ → ℂ} {L : ℝ}
    (hInv : inversionCDFFormulaFor μ ν φ ψ L) :
    measureCDFErrorLE μ ν
      ((1 / (2 * Real.pi)) * fourierDistanceIntegralOfFns φ ψ L) := by
  intro x
  rw [hInv x, abs_mul]
  have hcoef_nonneg : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  rw [abs_of_nonneg hcoef_nonneg]
  exact mul_le_mul_of_nonneg_left
    (abs_re_inversionIntegral_le_fourierDistance φ ψ x L)
    hcoef_nonneg

lemma measureCDFErrorLE_of_measure_inversionCDFFormula
    {μ ν : Measure ℝ} {L : ℝ}
    (hInv : inversionCDFFormulaFor μ ν (charFun μ) (charFun ν) L) :
    measureCDFErrorLE μ ν
      ((1 / (2 * Real.pi)) * fourierDistanceIntegral μ ν L) := by
  simpa [fourierDistanceIntegral] using
    measureCDFErrorLE_of_inversionCDFFormula (μ := μ) (ν := ν) hInv

lemma re_inversionKernelIntegrand_polyaKernelMeasure
    {L x θ : ℝ} (hL : 0 < L) :
    (inversionKernelIntegrand
      (charFun (polyaKernelMeasure L)) (fun _ : ℝ => 0) x θ).re =
      triangleMultiplier L θ * (Real.sin (θ * x) / θ) := by
  have hchar :
      charFun (polyaKernelMeasure L) θ = (triangleMultiplier L θ : ℂ) :=
    (isPolyaKernelMeasure_polyaKernelMeasure hL).charFun_eq θ
  by_cases hθ : θ = 0
  · subst θ
    simp [inversionKernelIntegrand, hchar]
  · rw [inversionKernelIntegrand, hchar]
    have hden :
        ((triangleMultiplier L θ : ℂ) / (Complex.I * (θ : ℂ))) =
          -(((triangleMultiplier L θ / θ : ℝ) : ℂ) * Complex.I) := by
      field_simp [hθ, Complex.I_ne_zero]
      rw [Complex.I_sq]
      norm_cast
      field_simp [hθ]
      norm_num
    simp only [sub_zero]
    rw [hden]
    rw [Complex.neg_re, Complex.mul_re]
    have hEim :
        (Complex.exp (((-(θ * x)) : ℝ) * Complex.I)).im =
          -Real.sin (θ * x) := by
      rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    have hDre :
        (-(↑(triangleMultiplier L θ / θ) * Complex.I)).re = 0 := by
      simp
    have hDim :
        (-(↑(triangleMultiplier L θ / θ) * Complex.I)).im =
          -(triangleMultiplier L θ / θ) := by
      simp
    rw [hDre, hDim, hEim]
    ring

/-- The removable real sine kernel `sin(θ x) / θ`, with value `x` at
`θ = 0`.  This is the real part of the CDF inversion kernel after the
point-mass value at `θ = 0` is repaired. -/
def sineDivKernel (x θ : ℝ) : ℝ :=
  if θ = 0 then x else Real.sin (θ * x) / θ

lemma sineDivKernel_zero_left (x : ℝ) :
    sineDivKernel x 0 = x := by
  simp [sineDivKernel]

lemma sineDivKernel_of_ne {x θ : ℝ} (hθ : θ ≠ 0) :
    sineDivKernel x θ = Real.sin (θ * x) / θ := by
  simp [sineDivKernel, hθ]

lemma sineDivKernel_eq_mul_sinc (x θ : ℝ) :
    sineDivKernel x θ = x * Real.sinc (θ * x) := by
  by_cases hθ : θ = 0
  · subst θ
    simp [sineDivKernel]
  · by_cases hx : x = 0
    · subst x
      simp [sineDivKernel, hθ]
    · have hprod : θ * x ≠ 0 := mul_ne_zero hθ hx
      rw [sineDivKernel_of_ne hθ, Real.sinc_of_ne_zero hprod]
      field_simp [hθ, hx]

lemma continuous_sineDivKernel_left (x : ℝ) :
    Continuous (fun θ : ℝ => sineDivKernel x θ) := by
  have hfun :
      (fun θ : ℝ => sineDivKernel x θ) =
        fun θ : ℝ => x * Real.sinc (θ * x) := by
    funext θ
    exact sineDivKernel_eq_mul_sinc x θ
  rw [hfun]
  exact continuous_const.mul
    (Real.continuous_sinc.comp (continuous_id.mul continuous_const))

lemma continuous_sineDivKernel :
    Continuous (fun p : ℝ × ℝ => sineDivKernel p.1 p.2) := by
  have hfun :
      (fun p : ℝ × ℝ => sineDivKernel p.1 p.2) =
        fun p : ℝ × ℝ => p.1 * Real.sinc (p.2 * p.1) := by
    funext p
    exact sineDivKernel_eq_mul_sinc p.1 p.2
  rw [hfun]
  exact continuous_fst.mul
    (Real.continuous_sinc.comp (continuous_snd.mul continuous_fst))

lemma abs_sineDivKernel_le_abs_left (x θ : ℝ) :
    |sineDivKernel x θ| ≤ |x| := by
  rw [sineDivKernel_eq_mul_sinc, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg x) (Real.abs_sinc_le_one (θ * x))

lemma abs_sineDivKernel_sub_le (t x θ : ℝ) :
    |sineDivKernel (t - x) θ| ≤ |t| + |x| := by
  have hsub : |t - x| ≤ |t| + |x| := by
    simpa [sub_eq_add_neg] using abs_add_le t (-x)
  exact (abs_sineDivKernel_le_abs_left (t - x) θ).trans hsub

lemma hasDerivAt_sineDivKernel (x θ : ℝ) :
    HasDerivAt (fun y : ℝ => sineDivKernel y θ)
      (Real.cos (θ * x)) x := by
  by_cases hθ : θ = 0
  · subst θ
    simpa [sineDivKernel] using (hasDerivAt_id x)
  · have hsin :
        HasDerivAt (fun y : ℝ => Real.sin (θ * y))
          (θ * Real.cos (θ * x)) x := by
      convert (Real.hasDerivAt_sin (θ * x)).comp x
        ((hasDerivAt_id x).const_mul θ) using 1
      ring
    have hdiv := hsin.div_const θ
    have hfun :
        (fun y : ℝ => sineDivKernel y θ) =
          fun y : ℝ => Real.sin (θ * y) / θ := by
      funext y
      exact sineDivKernel_of_ne hθ
    rw [hfun]
    convert hdiv using 1
    field_simp [hθ]

lemma hasDerivAt_integral_triangleMultiplier_sineDivKernel
    {L x : ℝ} (hL : 0 < L) :
    HasDerivAt
      (fun y : ℝ =>
        ∫ θ in -L..L, triangleMultiplier L θ * sineDivKernel y θ)
      (∫ θ in -L..L, triangleMultiplier L θ * Real.cos (θ * x)) x := by
  let F : ℝ → ℝ → ℝ := fun y θ =>
    triangleMultiplier L θ * sineDivKernel y θ
  let F' : ℝ → ℝ → ℝ := fun y θ =>
    triangleMultiplier L θ * Real.cos (θ * y)
  have hF_meas :
      ∀ᶠ y in 𝓝 x,
        AEStronglyMeasurable (F y) (volume.restrict (Set.uIoc (-L) L)) := by
    refine Eventually.of_forall ?_
    intro y
    exact ((continuous_triangleMultiplier L).mul
      (continuous_sineDivKernel_left y)).aestronglyMeasurable
  have hF_int :
      IntervalIntegrable (F x) volume (-L) L := by
    exact ((continuous_triangleMultiplier L).mul
      (continuous_sineDivKernel_left x)).intervalIntegrable _ _
  have hF'_meas :
      AEStronglyMeasurable (F' x) (volume.restrict (Set.uIoc (-L) L)) := by
    exact ((continuous_triangleMultiplier L).mul
      (Real.continuous_cos.comp (continuous_id.mul continuous_const))).aestronglyMeasurable
  have h_bound :
      ∀ᵐ θ ∂volume, θ ∈ Set.uIoc (-L) L →
        ∀ y ∈ (Set.univ : Set ℝ), ‖F' y θ‖ ≤ (1 : ℝ) := by
    refine Eventually.of_forall ?_
    intro θ _hθ y _hy
    dsimp [F']
    rw [abs_mul, abs_of_nonneg (triangleMultiplier_nonneg L θ)]
    exact mul_le_one₀ (triangleMultiplier_le_one hL)
      (abs_nonneg _) (Real.abs_cos_le_one (θ * y))
  have h_bound_int :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-L) L :=
    intervalIntegrable_const
  have h_diff :
      ∀ᵐ θ ∂volume, θ ∈ Set.uIoc (-L) L →
        ∀ y ∈ (Set.univ : Set ℝ),
          HasDerivAt (fun z : ℝ => F z θ) (F' y θ) y := by
    refine Eventually.of_forall ?_
    intro θ _hθ y _hy
    dsimp [F, F']
    exact (hasDerivAt_sineDivKernel y θ).const_mul (triangleMultiplier L θ)
  exact
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := -L) (b := L)
      (F := F) (F' := F') (x₀ := x)
      (s := (Set.univ : Set ℝ)) (bound := fun _ : ℝ => (1 : ℝ))
      univ_mem hF_meas hF_int hF'_meas h_bound h_bound_int h_diff).2

/-- The derivative kernel obtained from the triangular Fourier multiplier is
exactly `2π` times Polya's density.  This is the real-cosine specialization of
`integral_triangleMultiplier_exp_mul_I_eq_sinc_sq`. -/
lemma integral_triangleMultiplier_mul_cos_eq_scaled_polyaKernel
    {L x : ℝ} (hL : 0 < L) :
    ∫ θ in -L..L, triangleMultiplier L θ * Real.cos (θ * x) =
      2 * Real.pi * polyaKernel L x := by
  have hcomplex :=
    integral_triangleMultiplier_exp_mul_I_eq_sinc_sq (L := L) (α := x) hL
  have hIntC :
      IntervalIntegrable
        (fun θ : ℝ =>
          (triangleMultiplier L θ : ℂ) *
            Complex.exp (((x * θ : ℝ) : ℂ) * Complex.I))
        volume (-L) L := by
    exact ((Complex.continuous_ofReal.comp (continuous_triangleMultiplier L)).mul
      (by fun_prop)).intervalIntegrable _ _
  have hreC :
      ∫ θ in -L..L,
          ((triangleMultiplier L θ : ℂ) *
            Complex.exp (((x * θ : ℝ) : ℂ) * Complex.I)).re =
        L * Real.sinc (x * L / 2) ^ 2 := by
    calc
      ∫ θ in -L..L,
          ((triangleMultiplier L θ : ℂ) *
            Complex.exp (((x * θ : ℝ) : ℂ) * Complex.I)).re
          = RCLike.re
              (∫ θ in -L..L,
                (triangleMultiplier L θ : ℂ) *
                  Complex.exp (((x * θ : ℝ) : ℂ) * Complex.I)) := by
              exact intervalIntegral.intervalIntegral_re hIntC
      _ = RCLike.re ((L * Real.sinc (x * L / 2) ^ 2 : ℝ) : ℂ) := by
            rw [hcomplex]
            congr 1
            norm_cast
      _ = L * Real.sinc (x * L / 2) ^ 2 := by
            exact RCLike.ofReal_re (K := ℂ) (L * Real.sinc (x * L / 2) ^ 2)
  have hre :
      ∫ θ in -L..L, triangleMultiplier L θ * Real.cos (θ * x) =
        L * Real.sinc (x * L / 2) ^ 2 := by
    calc
      ∫ θ in -L..L, triangleMultiplier L θ * Real.cos (θ * x)
          = ∫ θ in -L..L,
              ((triangleMultiplier L θ : ℂ) *
                Complex.exp (((x * θ : ℝ) : ℂ) * Complex.I)).re := by
              refine intervalIntegral.integral_congr ?_
              intro θ _hθ
              change triangleMultiplier L θ * Real.cos (θ * x) =
                ((triangleMultiplier L θ : ℂ) *
                  Complex.exp (((x * θ : ℝ) : ℂ) * Complex.I)).re
              rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
              rw [show x * θ = θ * x by ring]
              ring
      _ = L * Real.sinc (x * L / 2) ^ 2 := hreC
  calc
    ∫ θ in -L..L, triangleMultiplier L θ * Real.cos (θ * x)
        = L * Real.sinc (x * L / 2) ^ 2 := hre
    _ = 2 * Real.pi * polyaKernel L x := by
          rw [polyaKernel_eq_sinc_sq hL]
          have harg : L * x / 2 = x * L / 2 := by ring
          rw [harg]
          field_simp [Real.pi_ne_zero]

/-- Differentiating the truncated sine kernel gives the Polya density with the
expected `2π` Fourier-inversion factor. -/
lemma hasDerivAt_integral_triangleMultiplier_sineDivKernel_scaled_polyaKernel
    {L x : ℝ} (hL : 0 < L) :
    HasDerivAt
      (fun y : ℝ =>
        ∫ θ in -L..L, triangleMultiplier L θ * sineDivKernel y θ)
      (2 * Real.pi * polyaKernel L x) x := by
  simpa [integral_triangleMultiplier_mul_cos_eq_scaled_polyaKernel
      (L := L) (x := x) hL] using
    hasDerivAt_integral_triangleMultiplier_sineDivKernel
      (L := L) (x := x) hL

/-- The normalized inversion kernel is an antiderivative of Polya's density. -/
lemma hasDerivAt_normalized_integral_triangleMultiplier_sineDivKernel
    {L x : ℝ} (hL : 0 < L) :
    HasDerivAt
      (fun y : ℝ =>
        (1 / (2 * Real.pi)) *
          ∫ θ in -L..L, triangleMultiplier L θ * sineDivKernel y θ)
      (polyaKernel L x) x := by
  have h :=
    (hasDerivAt_integral_triangleMultiplier_sineDivKernel_scaled_polyaKernel
      (L := L) (x := x) hL).const_mul (1 / (2 * Real.pi))
  convert h using 1
  field_simp [Real.pi_ne_zero]

lemma integral_triangleMultiplier_sineDivKernel_zero (L : ℝ) :
    ∫ θ in -L..L, triangleMultiplier L θ * sineDivKernel 0 θ = 0 := by
  simp [sineDivKernel_eq_mul_sinc]

/-- Integrated form of the Polya inversion kernel identity:
the finite-window sine kernel is the antiderivative of `2π h_L`. -/
lemma integral_scaled_polyaKernel_eq_integral_triangleMultiplier_sineDivKernel
    {L x : ℝ} (hL : 0 < L) :
    ∫ y in (0 : ℝ)..x, 2 * Real.pi * polyaKernel L y =
      ∫ θ in -L..L, triangleMultiplier L θ * sineDivKernel x θ := by
  let F : ℝ → ℝ := fun y =>
    ∫ θ in -L..L, triangleMultiplier L θ * sineDivKernel y θ
  have hderiv :
      ∀ y ∈ Set.uIcc (0 : ℝ) x,
        HasDerivAt F (2 * Real.pi * polyaKernel L y) y := by
    intro y _hy
    exact hasDerivAt_integral_triangleMultiplier_sineDivKernel_scaled_polyaKernel
      (L := L) (x := y) hL
  have hint :
      IntervalIntegrable
        (fun y : ℝ => 2 * Real.pi * polyaKernel L y) volume (0 : ℝ) x := by
    exact ((continuous_const.mul (continuous_polyaKernel hL))).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    ∫ y in (0 : ℝ)..x, 2 * Real.pi * polyaKernel L y
        = F x - F 0 := hFTC
    _ = ∫ θ in -L..L, triangleMultiplier L θ * sineDivKernel x θ := by
          simp [F, integral_triangleMultiplier_sineDivKernel_zero]

/-- Normalized form of the finite-window sine-kernel identity. -/
lemma normalized_integral_triangleMultiplier_sineDivKernel_eq_integral_polyaKernel
    {L x : ℝ} (hL : 0 < L) :
    (1 / (2 * Real.pi)) *
        ∫ θ in -L..L, triangleMultiplier L θ * sineDivKernel x θ =
      ∫ y in (0 : ℝ)..x, polyaKernel L y := by
  have hscaled :=
    integral_scaled_polyaKernel_eq_integral_triangleMultiplier_sineDivKernel
      (L := L) (x := x) hL
  have hconst :
      ∫ y in (0 : ℝ)..x, 2 * Real.pi * polyaKernel L y =
        (2 * Real.pi) * ∫ y in (0 : ℝ)..x, polyaKernel L y := by
    rw [intervalIntegral.integral_const_mul]
  rw [hconst] at hscaled
  rw [← hscaled]
  field_simp [Real.pi_ne_zero]

/-- Polya's CDF written directly as the normalized finite-window sine kernel. -/
lemma polyaKernelMeasure_real_Iic_eq_half_add_normalized_sineDivKernel
    {L x : ℝ} (hL : 0 < L) :
    (polyaKernelMeasure L).real (Set.Iic x) =
      1 / 2 +
        (1 / (2 * Real.pi)) *
          ∫ θ in -L..L, triangleMultiplier L θ * sineDivKernel x θ := by
  rw [polyaKernelMeasure_real_Iic_eq_half_add_integral hL,
    ← normalized_integral_triangleMultiplier_sineDivKernel_eq_integral_polyaKernel
      (L := L) (x := x) hL]

/-- Centered form of the Polya CDF inversion kernel. -/
lemma polyaKernelMeasure_real_Iic_sub_half_eq_normalized_sineDivKernel
    {L x : ℝ} (hL : 0 < L) :
    (polyaKernelMeasure L).real (Set.Iic x) - 1 / 2 =
      (1 / (2 * Real.pi)) *
        ∫ θ in -L..L, triangleMultiplier L θ * sineDivKernel x θ := by
  rw [polyaKernelMeasure_real_Iic_eq_half_add_normalized_sineDivKernel
    (L := L) (x := x) hL]
  ring

end FourierInversion

section TaylorBounds

/-- Lagrange-remainder bound `|sin x - x| ≤ |x|^3 / 6`, used for the
sharp pure-imaginary characteristic-function Taylor estimate. -/
lemma abs_sin_sub_id_le_abs_cube_div_six (x : ℝ) :
    |Real.sin x - x| ≤ |x| ^ 3 / 6 := by
  by_cases hx0 : x = 0
  · subst x
    norm_num
  have hcd : ContDiffOn ℝ (2 + 1 : ℕ) Real.sin (Set.uIcc (0 : ℝ) x) :=
    Real.contDiff_sin.contDiffOn
  obtain ⟨y, _hy, hy_eq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.sin) (x := x) (x₀ := 0) (n := 2)
      (by exact fun h => hx0 h.symm) hcd
  have hpoly :
      taylorWithinEval Real.sin 2 (Set.uIcc (0 : ℝ) x) 0 x = x := by
    have hxlt : 0 < x ∨ x < 0 := by
      exact lt_or_gt_of_ne (by exact fun h => hx0 h.symm)
    have hder0 :
        iteratedDerivWithin 0 Real.sin (Set.uIcc (0 : ℝ) x) 0 = 0 := by
      simp
    have hder1 :
        iteratedDerivWithin 1 Real.sin (Set.uIcc (0 : ℝ) x) 0 = 1 := by
      rcases hxlt with hpos | hneg
      · rw [Set.uIcc_of_le hpos.le]
        simpa using
          (Real.iteratedDerivWithin_sin_Icc 1 hpos
            (x := 0) (by simp [hpos.le]))
      · rw [Set.uIcc_of_ge hneg.le]
        simpa using
          (Real.iteratedDerivWithin_sin_Icc 1 hneg
            (x := 0) (by simp [hneg.le]))
    have hder2 :
        iteratedDerivWithin 2 Real.sin (Set.uIcc (0 : ℝ) x) 0 = 0 := by
      rcases hxlt with hpos | hneg
      · rw [Set.uIcc_of_le hpos.le]
        simpa using
          (Real.iteratedDerivWithin_sin_Icc 2 hpos
            (x := 0) (by simp [hpos.le]))
      · rw [Set.uIcc_of_ge hneg.le]
        simpa using
          (Real.iteratedDerivWithin_sin_Icc 2 hneg
            (x := 0) (by simp [hneg.le]))
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hder0, hder1, hder2]
  have hrem :
      Real.sin x - x = -(Real.cos y * x ^ 3) / 6 := by
    have h := hy_eq
    rw [hpoly] at h
    norm_num [Nat.factorial] at h
    exact h
  rw [hrem]
  have hder : |Real.cos y| ≤ 1 :=
    Real.abs_cos_le_one y
  calc
    |-(Real.cos y * x ^ 3) / 6|
        = |Real.cos y| * |x| ^ 3 / 6 := by
          rw [abs_div, abs_neg, abs_mul, abs_pow,
            abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    _ ≤ 1 * |x| ^ 3 / 6 := by
          gcongr
    _ = |x| ^ 3 / 6 := by ring

/-- Lagrange-remainder bound for the quadratic cosine approximation. -/
lemma abs_cos_sub_one_sub_sq_div_two_le_abs_cube_div_six (x : ℝ) :
    |Real.cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 3 / 6 := by
  by_cases hx0 : x = 0
  · subst x
    norm_num
  have hcd : ContDiffOn ℝ (2 + 1 : ℕ) Real.cos (Set.uIcc (0 : ℝ) x) :=
    Real.contDiff_cos.contDiffOn
  obtain ⟨y, _hy, hy_eq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.cos) (x := x) (x₀ := 0) (n := 2)
      (by exact fun h => hx0 h.symm) hcd
  have hpoly :
      taylorWithinEval Real.cos 2 (Set.uIcc (0 : ℝ) x) 0 x =
        1 - x ^ 2 / 2 := by
    have hxlt : 0 < x ∨ x < 0 := by
      exact lt_or_gt_of_ne (by exact fun h => hx0 h.symm)
    have hder0 :
        iteratedDerivWithin 0 Real.cos (Set.uIcc (0 : ℝ) x) 0 = 1 := by
      simp
    have hder1 :
        iteratedDerivWithin 1 Real.cos (Set.uIcc (0 : ℝ) x) 0 = 0 := by
      rcases hxlt with hpos | hneg
      · rw [Set.uIcc_of_le hpos.le]
        simpa using
          (Real.iteratedDerivWithin_cos_Icc 1 hpos
            (x := 0) (by simp [hpos.le]))
      · rw [Set.uIcc_of_ge hneg.le]
        simpa using
          (Real.iteratedDerivWithin_cos_Icc 1 hneg
            (x := 0) (by simp [hneg.le]))
    have hder2 :
        iteratedDerivWithin 2 Real.cos (Set.uIcc (0 : ℝ) x) 0 = -1 := by
      rcases hxlt with hpos | hneg
      · rw [Set.uIcc_of_le hpos.le]
        simpa using
          (Real.iteratedDerivWithin_cos_Icc 2 hpos
            (x := 0) (by simp [hpos.le]))
      · rw [Set.uIcc_of_ge hneg.le]
        simpa using
          (Real.iteratedDerivWithin_cos_Icc 2 hneg
            (x := 0) (by simp [hneg.le]))
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hder0, hder1, hder2]
    ring
  have hrem :
      Real.cos x - (1 - x ^ 2 / 2) = Real.sin y * x ^ 3 / 6 := by
    have h := hy_eq
    rw [hpoly] at h
    norm_num [Nat.factorial] at h
    exact h
  rw [hrem]
  have hder : |Real.sin y| ≤ 1 :=
    Real.abs_sin_le_one y
  calc
    |Real.sin y * x ^ 3 / 6|
        = |Real.sin y| * |x| ^ 3 / 6 := by
          rw [abs_div, abs_mul, abs_pow,
            abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    _ ≤ 1 * |x| ^ 3 / 6 := by
          gcongr
    _ = |x| ^ 3 / 6 := by ring

/-- The real one-parameter curve `t ↦ exp(i t)` used in the exact complex
Taylor integral-remainder proof. -/
def expI (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * Complex.I)

lemma hasDerivAt_expI (t : ℝ) :
    HasDerivAt expI (expI t * Complex.I) t := by
  have hlin :
      HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) Complex.I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
  simpa [expI] using hlin.cexp

lemma deriv_expI (t : ℝ) :
    deriv expI t = expI t * Complex.I :=
  (hasDerivAt_expI t).deriv

lemma hasDerivAt_const_mul_expI (c : ℂ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => c * expI y) (c * expI t * Complex.I) t := by
  have h := (hasDerivAt_expI t).const_mul c
  simpa [mul_assoc] using h

lemma deriv_const_mul_expI (c : ℂ) (t : ℝ) :
    deriv (fun y : ℝ => c * expI y) t = c * expI t * Complex.I :=
  (hasDerivAt_const_mul_expI c t).deriv

lemma iteratedDeriv_expI (n : ℕ) (t : ℝ) :
    iteratedDeriv n expI t = Complex.I ^ n * expI t := by
  induction n generalizing t with
  | zero =>
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      change deriv (fun y : ℝ => iteratedDeriv n expI y) t =
        Complex.I ^ (n + 1) * expI t
      rw [show (fun y : ℝ => iteratedDeriv n expI y) =
          fun y : ℝ => Complex.I ^ n * expI y by
            funext y
            exact ih y]
      rw [deriv_const_mul_expI]
      ring

lemma contDiff_expI {n : WithTop ℕ∞} :
    ContDiff ℝ n expI := by
  have hOf : ContDiff ℝ n (fun t : ℝ => Complex.ofRealCLM t) :=
    Complex.ofRealCLM.contDiff
  have hlin : ContDiff ℝ n (fun t : ℝ => (t : ℂ) * Complex.I) := by
    simpa [Complex.ofRealCLM_apply] using
      hOf.mul (contDiff_const : ContDiff ℝ n (fun _ : ℝ => Complex.I))
  simpa [expI] using hlin.cexp

lemma contDiffOn_expI (x : ℝ) :
    ContDiffOn ℝ (3 : ℕ) expI (Set.uIcc (0 : ℝ) x) :=
  (contDiff_expI (n := (3 : ℕ))).contDiffOn

lemma iteratedDerivWithin_expI_uIcc_zero {x : ℝ} (hx : x ≠ 0) (k : ℕ) :
    iteratedDerivWithin k expI (Set.uIcc (0 : ℝ) x) 0 =
      Complex.I ^ k := by
  have hxlt : 0 < x ∨ x < 0 := by
    exact lt_or_gt_of_ne (by exact fun h => hx h.symm)
  have hcd : ContDiffAt ℝ (k : WithTop ℕ∞) expI 0 :=
    (contDiff_expI (n := (k : WithTop ℕ∞))).contDiffAt
  rcases hxlt with hpos | hneg
  · rw [Set.uIcc_of_le hpos.le]
    have hmem : 0 ∈ Set.Icc (0 : ℝ) x := by
      simp [hpos.le]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hpos) hcd hmem]
    simp [iteratedDeriv_expI, expI]
  · rw [Set.uIcc_of_ge hneg.le]
    have hmem : 0 ∈ Set.Icc x (0 : ℝ) := by
      simp [hneg.le]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hneg) hcd hmem]
    simp [iteratedDeriv_expI, expI]

lemma taylorWithinEval_expI_two_zero (x : ℝ) :
    taylorWithinEval expI 2 (Set.uIcc (0 : ℝ) x) 0 x =
      1 + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2 := by
  by_cases hx : x = 0
  · subst x
    simp [expI]
  have hder0 :
      iteratedDerivWithin 0 expI (Set.uIcc (0 : ℝ) x) 0 = 1 := by
    simpa using iteratedDerivWithin_expI_uIcc_zero (x := x) hx 0
  have hder1 :
      iteratedDerivWithin 1 expI (Set.uIcc (0 : ℝ) x) 0 = Complex.I := by
    simpa using iteratedDerivWithin_expI_uIcc_zero (x := x) hx 1
  have hder2 :
      iteratedDerivWithin 2 expI (Set.uIcc (0 : ℝ) x) 0 = -1 := by
    simpa [Complex.I_mul_I] using iteratedDerivWithin_expI_uIcc_zero (x := x) hx 2
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, hder0, hder1, hder2, Complex.real_smul]
  apply Complex.ext
  · simp [Complex.add_re, Complex.sub_re, Complex.neg_re]
    have hIre : (x • Complex.I).re = 0 := by simp
    have hOneRe : (((2⁻¹ * x ^ 2 : ℝ)) • (1 : ℂ)).re = 2⁻¹ * x ^ 2 := by
      rw [Complex.smul_re]
      simp
    have hPowRe : ((x : ℂ) ^ 2).re = x ^ 2 := by
      norm_num [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hleft :
        1 + (x • Complex.I).re + -(((2⁻¹ * x ^ 2 : ℝ)) • (1 : ℂ)).re =
          1 + 0 + -(2⁻¹ * x ^ 2) :=
      congrArg₂ (fun a b : ℝ => 1 + a + -b) hIre hOneRe
    have hmid :
        1 + 0 + -(2⁻¹ * x ^ 2) = 1 - x ^ 2 / 2 := by
      ring_nf
    have hright :
        1 - x ^ 2 / 2 = 1 - ((x : ℂ) ^ 2).re / 2 :=
      congrArg (fun c : ℝ => 1 - c / 2) hPowRe.symm
    exact hleft.trans (hmid.trans hright)
  · simp [Complex.add_im, Complex.sub_im, Complex.neg_im]
    have hIim : (x • Complex.I).im = x := by simp
    have hOneIm : (((2⁻¹ * x ^ 2 : ℝ)) • (1 : ℂ)).im = 0 := by
      rw [Complex.smul_im]
      simp
    have hPowIm : ((x : ℂ) ^ 2).im = 0 := by
      norm_num [pow_two, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have hleft :
        (x • Complex.I).im + -(((2⁻¹ * x ^ 2 : ℝ)) • (1 : ℂ)).im =
          x + -0 :=
      congrArg₂ (fun a b : ℝ => a + -b) hIim hOneIm
    have hmid : x + -0 = x - 0 / 2 := by
      ring_nf
    have hright :
        x - 0 / 2 = x - ((x : ℂ) ^ 2).im / 2 :=
      congrArg (fun c : ℝ => x - c / 2) hPowIm.symm
    exact hleft.trans (hmid.trans hright)

lemma norm_iteratedDerivWithin_expI_three_le_one
    {x t : ℝ} (hx : x ≠ 0) (ht : t ∈ Set.uIcc (0 : ℝ) x) :
    ‖iteratedDerivWithin 3 expI (Set.uIcc (0 : ℝ) x) t‖ ≤ 1 := by
  have hxlt : 0 < x ∨ x < 0 := by
    exact lt_or_gt_of_ne (by exact fun h => hx h.symm)
  have hcd : ContDiffAt ℝ (3 : WithTop ℕ∞) expI t :=
    (contDiff_expI (n := (3 : WithTop ℕ∞))).contDiffAt
  rcases hxlt with hpos | hneg
  · rw [Set.uIcc_of_le hpos.le] at ht ⊢
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hpos) hcd ht]
    rw [iteratedDeriv_expI]
    simp [expI, Complex.norm_I]
  · rw [Set.uIcc_of_ge hneg.le] at ht ⊢
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hneg) hcd ht]
    rw [iteratedDeriv_expI]
    simp [expI, Complex.norm_I]

lemma abs_intervalIntegral_abs_sub_sq_div_two (x : ℝ) :
    |∫ t in (0 : ℝ)..x, |x - t| ^ 2 / 2| = |x| ^ 3 / 6 := by
  have hnonneg :
      0 ≤ ∫ t in Set.uIoc (0 : ℝ) x, |x - t| ^ 2 / 2 := by
    exact integral_nonneg fun t =>
      div_nonneg (pow_nonneg (abs_nonneg (x - t)) 2) (by norm_num)
  have hset :
      (∫ t in Set.uIoc (0 : ℝ) x, |x - t| ^ 2) = |x| ^ 3 / 3 := by
    have hpow := integral_pow_abs_sub_uIoc (a := x) (b := (0 : ℝ)) (n := 2)
    rw [Set.uIoc_comm]
    calc
      (∫ t in Set.uIoc x (0 : ℝ), |x - t| ^ 2)
          = ∫ t in Set.uIoc x (0 : ℝ), |t - x| ^ 2 := by
            refine integral_congr_ae ?_
            filter_upwards with t
            rw [abs_sub_comm]
      _ = |(0 : ℝ) - x| ^ 3 / ((2 : ℝ) + 1) := hpow
      _ = |(0 : ℝ) - x| ^ 3 / 3 := by norm_num
      _ = |x| ^ 3 / 3 := by
            rw [zero_sub, abs_neg]
  calc
    |∫ t in (0 : ℝ)..x, |x - t| ^ 2 / 2|
        = |∫ t in Set.uIoc (0 : ℝ) x, |x - t| ^ 2 / 2| := by
          rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
    _ = ∫ t in Set.uIoc (0 : ℝ) x, |x - t| ^ 2 / 2 :=
          abs_of_nonneg hnonneg
    _ = (∫ t in Set.uIoc (0 : ℝ) x, |x - t| ^ 2) / 2 := by
          rw [integral_div]
    _ = |x| ^ 3 / 6 := by
          rw [hset]
          ring

/-- Exact vector-valued Taylor integral-remainder bound for the
pure-imaginary exponential, with the Durrett/Feller constant `1 / 6`. -/
lemma complex_exp_I_taylor_two_remainder_bound_exact (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2)‖ ≤
      |x| ^ 3 / 6 := by
  by_cases hx0 : x = 0
  · subst x
    norm_num
  let integrand : ℝ → ℂ := fun t =>
    ((x - t) ^ 2 / ((2 : ℕ).factorial : ℝ)) •
      iteratedDerivWithin 3 expI (Set.uIcc (0 : ℝ) x) t
  have hTaylor :=
    taylor_integral_remainder (F := ℂ) (f := expI)
      (x := x) (x₀ := (0 : ℝ)) (n := 2) (contDiffOn_expI x)
  rw [taylorWithinEval_expI_two_zero] at hTaylor
  have hBoundAE :
      ∀ᵐ t ∂(volume.restrict (Set.uIoc (0 : ℝ) x)),
        ‖integrand t‖ ≤ |x - t| ^ 2 / 2 := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_uIoc] with t ht
    have ht_uIcc : t ∈ Set.uIcc (0 : ℝ) x :=
      Set.uIoc_subset_uIcc ht
    have hD :
        ‖iteratedDerivWithin 3 expI (Set.uIcc (0 : ℝ) x) t‖ ≤ 1 :=
      norm_iteratedDerivWithin_expI_three_le_one hx0 ht_uIcc
    have hcoef_nonneg : 0 ≤ (x - t) ^ 2 / ((2 : ℕ).factorial : ℝ) := by
      positivity
    have hcoef_eq :
        (x - t) ^ 2 / ((2 : ℕ).factorial : ℝ) = |x - t| ^ 2 / 2 := by
      norm_num [sq_abs]
    calc
      ‖integrand t‖
          = |(x - t) ^ 2 / ((2 : ℕ).factorial : ℝ)| *
              ‖iteratedDerivWithin 3 expI (Set.uIcc (0 : ℝ) x) t‖ := by
            dsimp [integrand]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ = ((x - t) ^ 2 / ((2 : ℕ).factorial : ℝ)) *
              ‖iteratedDerivWithin 3 expI (Set.uIcc (0 : ℝ) x) t‖ := by
            rw [abs_of_nonneg hcoef_nonneg]
      _ = (|x - t| ^ 2 / 2) *
              ‖iteratedDerivWithin 3 expI (Set.uIcc (0 : ℝ) x) t‖ := by
            rw [hcoef_eq]
      _ ≤ |x - t| ^ 2 / 2 := by
            exact mul_le_of_le_one_right
              (div_nonneg (pow_nonneg (abs_nonneg (x - t)) 2) (by norm_num)) hD
  have hBoundInt :
      IntervalIntegrable (fun t : ℝ => |x - t| ^ 2 / 2) volume (0 : ℝ) x := by
    exact (by fun_prop :
      Continuous fun t : ℝ => |x - t| ^ 2 / 2).intervalIntegrable _ _
  have hNorm :=
    intervalIntegral.norm_integral_le_abs_of_norm_le
      (a := (0 : ℝ)) (b := x) (μ := volume)
      (f := integrand) (g := fun t : ℝ => |x - t| ^ 2 / 2)
      hBoundAE hBoundInt
  calc
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2)‖
        = ‖expI x - (1 + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2)‖ := by
          rfl
    _ = ‖∫ t in (0 : ℝ)..x, integrand t‖ := by
          rw [hTaylor]
          rfl
    _ ≤ |∫ t in (0 : ℝ)..x, |x - t| ^ 2 / 2| := hNorm
    _ = |x| ^ 3 / 6 := abs_intervalIntegral_abs_sub_sq_div_two x

/-- Global pure-imaginary second-order exponential remainder, kept at the
older `1 / 3` constant for compatibility with downstream estimates.  The
sharper local theorem is `complex_exp_I_taylor_two_remainder_bound_exact`. -/
lemma complex_exp_I_taylor_two_remainder_bound_cubic (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2)‖ ≤
      (1 / 3 : ℝ) * |x| ^ 3 := by
  exact (complex_exp_I_taylor_two_remainder_bound_exact x).trans
    (by
      have hnonneg : 0 ≤ |x| ^ 3 := pow_nonneg (abs_nonneg x) 3
      nlinarith)

/-- A local second-order Taylor remainder bound for the complex exponential,
specialized to the polynomial used in characteristic-function estimates. -/
lemma complex_exp_taylor_two_remainder_bound {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z -
        ∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℂ)‖ ≤
      (2 / 9 : ℝ) * ‖z‖ ^ 3 := by
  have h :=
    Complex.exp_bound (x := z) hz (n := 3) (by norm_num : 0 < 3)
  calc
    ‖Complex.exp z -
        ∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℂ)‖
        ≤ ‖z‖ ^ 3 * (((3 : ℕ).succ : ℝ) * (((3 : ℕ).factorial * 3 : ℝ)⁻¹)) := h
    _ = (2 / 9 : ℝ) * ‖z‖ ^ 3 := by
          norm_num
          ring

/-- Pure-imaginary specialization of `complex_exp_taylor_two_remainder_bound`. -/
lemma complex_exp_I_taylor_two_remainder_bound {x : ℝ} (hx : |x| ≤ 1) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        ∑ m ∈ Finset.range 3,
          (((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))‖ ≤
      (2 / 9 : ℝ) * |x| ^ 3 := by
  have hz : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by
    simpa [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs] using hx
  simpa [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs] using
    complex_exp_taylor_two_remainder_bound hz

lemma complex_exp_I_taylor_two_sum (x : ℝ) :
    (∑ m ∈ Finset.range 3,
        (((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))) =
      1 + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2 := by
  norm_num [Finset.sum_range_succ, pow_succ]
  rw [show (x : ℂ) * Complex.I * ((x : ℂ) * Complex.I) =
      -(x ^ 2 : ℂ) by
    rw [mul_assoc, ← mul_assoc Complex.I (x : ℂ) Complex.I,
      mul_comm Complex.I (x : ℂ), mul_assoc, Complex.I_mul_I]
    ring]
  ring

lemma norm_complex_exp_I_taylor_two_polynomial_le (x : ℝ) :
    ‖(1 : ℂ) + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2‖ ≤
      1 + |x| + |x| ^ 2 / 2 := by
  calc
    ‖(1 : ℂ) + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2‖
        ≤ ‖(1 : ℂ) + (x : ℂ) * Complex.I‖ +
            ‖(x ^ 2 : ℂ) / 2‖ := norm_sub_le _ _
    _ ≤ (‖(1 : ℂ)‖ + ‖(x : ℂ) * Complex.I‖) +
          ‖(x ^ 2 : ℂ) / 2‖ := by
          gcongr
          exact norm_add_le _ _
    _ = 1 + |x| + |x| ^ 2 / 2 := by
          simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A global, non-sharp third-order remainder bound for the pure-imaginary
exponential.  The small-argument case uses `Complex.exp_bound`; the large
argument case is a crude triangle-inequality estimate dominated by `|x|^3`. -/
lemma complex_exp_I_taylor_two_remainder_bound_global (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2)‖ ≤
      4 * |x| ^ 3 := by
  by_cases hx : |x| ≤ 1
  · have hlocal := complex_exp_I_taylor_two_remainder_bound (x := x) hx
    rw [complex_exp_I_taylor_two_sum x] at hlocal
    calc
      ‖Complex.exp ((x : ℂ) * Complex.I) -
          (1 + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2)‖
          ≤ (2 / 9 : ℝ) * |x| ^ 3 := hlocal
      _ ≤ 4 * |x| ^ 3 := by
            gcongr
            norm_num
  · have hxge : 1 ≤ |x| := le_of_not_ge hx
    have hnorm :
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            (1 + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2)‖
          ≤ 2 + |x| + |x| ^ 2 / 2 := by
      calc
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            (1 + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2)‖
            ≤ ‖Complex.exp ((x : ℂ) * Complex.I)‖ +
                ‖(1 : ℂ) + (x : ℂ) * Complex.I - (x ^ 2 : ℂ) / 2‖ :=
              norm_sub_le _ _
        _ ≤ 1 + (1 + |x| + |x| ^ 2 / 2) := by
              gcongr
              · rw [Complex.norm_exp_ofReal_mul_I]
              · exact norm_complex_exp_I_taylor_two_polynomial_le x
        _ = 2 + |x| + |x| ^ 2 / 2 := by ring
    have hpoly : 2 + |x| + |x| ^ 2 / 2 ≤ 4 * |x| ^ 3 := by
      nlinarith [hxge, sq_nonneg (|x|)]
    exact hnorm.trans hpoly

lemma abs_le_one_add_abs_cube (x : ℝ) :
    |x| ≤ 1 + |x| ^ 3 := by
  by_cases hx : |x| ≤ 1
  · have h3 : 0 ≤ |x| ^ 3 := pow_nonneg (abs_nonneg x) 3
    linarith
  · have hxge : 1 ≤ |x| := le_of_not_ge hx
    nlinarith [hxge, sq_nonneg (|x|)]

lemma sq_le_one_add_abs_cube (x : ℝ) :
    x ^ 2 ≤ 1 + |x| ^ 3 := by
  have hx0 : 0 ≤ |x| := abs_nonneg x
  by_cases hx : |x| ≤ 1
  · have : x ^ 2 = |x| ^ 2 := by rw [sq_abs]
    rw [this]
    nlinarith [hx, hx0]
  · have hxge : 1 ≤ |x| := le_of_not_ge hx
    have : x ^ 2 = |x| ^ 2 := by rw [sq_abs]
    rw [this]
    nlinarith [hxge, sq_nonneg (|x|)]

lemma integrable_id_of_integrable_abs_cube
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Integrable (fun x : ℝ => x) μ := by
  refine ((integrable_const (c := (1 : ℝ))).add h3).mono'
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x) μ) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact abs_le_one_add_abs_cube x

lemma integrable_sq_of_integrable_abs_cube
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Integrable (fun x : ℝ => x ^ 2) μ := by
  refine ((integrable_const (c := (1 : ℝ))).add h3).mono'
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) μ) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
  exact sq_le_one_add_abs_cube x

/-- The second-order Taylor polynomial of `exp (i t x)` in the characteristic
function estimate, written with real moments. -/
def charFunTaylorTwoIntegrand (t x : ℝ) : ℂ :=
  (1 : ℂ) + (((t * x : ℝ) : ℂ) * Complex.I) -
    ((t ^ 2 * x ^ 2 : ℝ) : ℂ) / 2

lemma integrable_exp_I_mul
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable
      (fun x : ℝ => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) μ := by
  refine Integrable.of_bound
    (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) μ) 1 ?_
  filter_upwards with x
  rw [Complex.norm_exp_ofReal_mul_I]

lemma integrable_charFunTaylorTwoIntegrand
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) (t : ℝ) :
    Integrable (fun x : ℝ => charFunTaylorTwoIntegrand t x) μ := by
  have h1 : Integrable (fun x : ℝ => x) μ :=
    integrable_id_of_integrable_abs_cube μ h3
  have h2 : Integrable (fun x : ℝ => x ^ 2) μ :=
    integrable_sq_of_integrable_abs_cube μ h3
  have hlin :
      Integrable (fun x : ℝ => (((t * x : ℝ) : ℂ) * Complex.I)) μ := by
    simpa using ((h1.const_mul t).ofReal (𝕜 := ℂ)).mul_const Complex.I
  have hquad :
      Integrable (fun x : ℝ => (((t ^ 2 * x ^ 2 : ℝ) : ℂ) / 2)) μ := by
    have hbase :
        Integrable (fun x : ℝ => ((t ^ 2 * x ^ 2 : ℝ) : ℂ)) μ := by
      convert ((h2.const_mul (t ^ 2)).ofReal (𝕜 := ℂ)) using 1
    simpa [div_eq_mul_inv] using hbase.mul_const ((2 : ℂ)⁻¹)
  exact (integrable_const (c := (1 : ℂ))).add hlin |>.sub hquad

lemma norm_exp_I_sub_charFunTaylorTwoIntegrand_le
    (t x : ℝ) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
        charFunTaylorTwoIntegrand t x‖ ≤
      4 * |t| ^ 3 * |x| ^ 3 := by
  have h := complex_exp_I_taylor_two_remainder_bound_global (t * x)
  simpa [charFunTaylorTwoIntegrand, mul_pow, abs_mul,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- Integrated third-moment Taylor estimate for characteristic functions:
`φ(t)` differs from the integrated second-order Taylor polynomial by at most
`4 |t|^3 E|X|^3`.  The constant is deliberately non-sharp but global. -/
lemma norm_charFun_sub_integral_taylor_two_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) (t : ℝ) :
    ‖charFun μ t - ∫ x, charFunTaylorTwoIntegrand t x ∂μ‖ ≤
      4 * |t| ^ 3 * ∫ x, |x| ^ 3 ∂μ := by
  have hExp := integrable_exp_I_mul μ t
  have hPoly := integrable_charFunTaylorTwoIntegrand μ h3 t
  have hExpEq :
      (∫ x, Complex.exp (↑t * ↑x * Complex.I) ∂μ) =
        ∫ x, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    congr 2
    norm_num
  have hEq :
      charFun μ t - ∫ x, charFunTaylorTwoIntegrand t x ∂μ =
        ∫ x, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
          charFunTaylorTwoIntegrand t x) ∂μ := by
    rw [charFun_apply_real, hExpEq]
    rw [integral_sub hExp hPoly]
  rw [hEq]
  have hBoundInt :
      Integrable (fun x : ℝ => 4 * |t| ^ 3 * |x| ^ 3) μ := by
    convert h3.const_mul (4 * |t| ^ 3) using 1
  calc
    ‖∫ x, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
          charFunTaylorTwoIntegrand t x) ∂μ‖
        ≤ ∫ x, ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
          charFunTaylorTwoIntegrand t x‖ ∂μ :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ x, 4 * |t| ^ 3 * |x| ^ 3 ∂μ := by
          exact integral_mono (hExp.sub hPoly).norm hBoundInt
            (fun x => norm_exp_I_sub_charFunTaylorTwoIntegrand_le t x)
    _ = 4 * |t| ^ 3 * ∫ x, |x| ^ 3 ∂μ := by
          rw [integral_const_mul]

lemma integral_charFunTaylorTwoIntegrand_eq
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (t : ℝ) :
    ∫ x, charFunTaylorTwoIntegrand t x ∂μ =
      (1 : ℂ) - (t ^ 2 : ℂ) / 2 := by
  have h1 : Integrable (fun x : ℝ => x) μ :=
    integrable_id_of_integrable_abs_cube μ h3
  have h2 : Integrable (fun x : ℝ => x ^ 2) μ :=
    integrable_sq_of_integrable_abs_cube μ h3
  have hlin :
      Integrable (fun x : ℝ => (((t * x : ℝ) : ℂ) * Complex.I)) μ := by
    simpa using ((h1.const_mul t).ofReal (𝕜 := ℂ)).mul_const Complex.I
  have hquad :
      Integrable (fun x : ℝ => (((t ^ 2 * x ^ 2 : ℝ) : ℂ) / 2)) μ := by
    have hbase :
        Integrable (fun x : ℝ => ((t ^ 2 * x ^ 2 : ℝ) : ℂ)) μ := by
      convert ((h2.const_mul (t ^ 2)).ofReal (𝕜 := ℂ)) using 1
    simpa [div_eq_mul_inv] using hbase.mul_const ((2 : ℂ)⁻¹)
  have hmulconst :
      (∫ x, (((t * x : ℝ) : ℂ) * Complex.I) ∂μ) =
        (∫ x, ((t * x : ℝ) : ℂ) ∂μ) * Complex.I := by
    simpa using (integral_mul_const (μ := μ) (r := Complex.I)
      (f := fun x : ℝ => ((t * x : ℝ) : ℂ)))
  have hofreal_lin :
      (∫ x, ((t * x : ℝ) : ℂ) ∂μ) =
        ((∫ x, t * x ∂μ : ℝ) : ℂ) := by
    simpa using (integral_ofReal (μ := μ) (𝕜 := ℂ)
      (f := fun x : ℝ => t * x))
  have hconstmul_lin :
      (∫ x, t * x ∂μ) = t * ∫ x, x ∂μ := by
    simpa using (integral_const_mul (μ := μ) (r := t)
      (f := fun x : ℝ => x))
  have hlin_int :
      (∫ x, (((t * x : ℝ) : ℂ) * Complex.I) ∂μ) = 0 := by
    rw [hmulconst, hofreal_lin, hconstmul_lin, hmean]
    simp
  have hdivconst :
      (∫ x, (((t ^ 2 * x ^ 2 : ℝ) : ℂ) / 2) ∂μ) =
        (∫ x, ((t ^ 2 * x ^ 2 : ℝ) : ℂ) ∂μ) / 2 := by
    convert (integral_div (μ := μ) (r := (2 : ℂ))
      (f := fun x : ℝ => ((t ^ 2 * x ^ 2 : ℝ) : ℂ))) using 1
  have hofreal_quad :
      (∫ x, ((t ^ 2 * x ^ 2 : ℝ) : ℂ) ∂μ) =
        ((∫ x, t ^ 2 * x ^ 2 ∂μ : ℝ) : ℂ) := by
    convert (integral_ofReal (μ := μ) (𝕜 := ℂ)
      (f := fun x : ℝ => t ^ 2 * x ^ 2)) using 1
  have hconstmul_quad :
      (∫ x, t ^ 2 * x ^ 2 ∂μ) = t ^ 2 * ∫ x, x ^ 2 ∂μ := by
    simpa using (integral_const_mul (μ := μ) (r := t ^ 2)
      (f := fun x : ℝ => x ^ 2))
  have hquad_int :
      (∫ x, (((t ^ 2 * x ^ 2 : ℝ) : ℂ) / 2) ∂μ) =
        (t ^ 2 : ℂ) / 2 := by
    rw [hdivconst, hofreal_quad, hconstmul_quad, hsecond]
    simp
  change (∫ x, (1 : ℂ) + (((t * x : ℝ) : ℂ) * Complex.I) -
      ((t ^ 2 * x ^ 2 : ℝ) : ℂ) / 2 ∂μ) =
    (1 : ℂ) - (t ^ 2 : ℂ) / 2
  have hsum :
      (∫ x, (1 : ℂ) + (((t * x : ℝ) : ℂ) * Complex.I) ∂μ) =
        (∫ x, (1 : ℂ) ∂μ) +
          ∫ x, (((t * x : ℝ) : ℂ) * Complex.I) ∂μ := by
    simpa using integral_add (integrable_const (c := (1 : ℂ))) hlin
  have hsub :
      (∫ x, ((1 : ℂ) + (((t * x : ℝ) : ℂ) * Complex.I)) -
          ((t ^ 2 * x ^ 2 : ℝ) : ℂ) / 2 ∂μ) =
        (∫ x, (1 : ℂ) + (((t * x : ℝ) : ℂ) * Complex.I) ∂μ) -
          ∫ x, (((t ^ 2 * x ^ 2 : ℝ) : ℂ) / 2) ∂μ := by
    simpa using integral_sub ((integrable_const (c := (1 : ℂ))).add hlin) hquad
  rw [hsub, hsum, hlin_int, hquad_int]
  simp

lemma norm_charFun_sub_quadratic_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (t : ℝ) :
    ‖charFun μ t - ((1 : ℂ) - (t ^ 2 : ℂ) / 2)‖ ≤
      4 * |t| ^ 3 * ∫ x, |x| ^ 3 ∂μ := by
  simpa [integral_charFunTaylorTwoIntegrand_eq μ h3 hmean hsecond t] using
    norm_charFun_sub_integral_taylor_two_le μ h3 t

/-- Cubic pure-imaginary Taylor bound in the integrand form used by
characteristic functions. -/
lemma norm_exp_I_sub_charFunTaylorTwoIntegrand_le_cubic
    (t x : ℝ) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
        charFunTaylorTwoIntegrand t x‖ ≤
      (1 / 6 : ℝ) * |t| ^ 3 * |x| ^ 3 := by
  have h := complex_exp_I_taylor_two_remainder_bound_exact (t * x)
  have hpoly :
      (1 + (((t * x : ℝ) : ℂ) * Complex.I) -
          (((t * x : ℝ) : ℂ) ^ 2) / 2) =
        charFunTaylorTwoIntegrand t x := by
    simp [charFunTaylorTwoIntegrand]
    ring
  have hrhs :
      |t * x| ^ 3 / 6 = (1 / 6 : ℝ) * |t| ^ 3 * |x| ^ 3 := by
    rw [abs_mul, mul_pow]
    ring
  have hbound :
      ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
          (1 + (((t * x : ℝ) : ℂ) * Complex.I) -
            (((t * x : ℝ) : ℂ) ^ 2) / 2)‖ ≤
        (1 / 6 : ℝ) * |t| ^ 3 * |x| ^ 3 :=
    h.trans_eq hrhs
  rw [hpoly] at hbound
  exact hbound

/-- Integrated cubic Taylor estimate for characteristic functions.  This is
the sharper replacement for the older global `4 |t|^3 E|X|^3` estimate, kept
under a separate name while the Durrett/Feller finite-window constants are
ported. -/
lemma norm_charFun_sub_integral_taylor_two_le_cubic
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) (t : ℝ) :
    ‖charFun μ t - ∫ x, charFunTaylorTwoIntegrand t x ∂μ‖ ≤
      (1 / 6 : ℝ) * |t| ^ 3 * ∫ x, |x| ^ 3 ∂μ := by
  have hExp := integrable_exp_I_mul μ t
  have hPoly := integrable_charFunTaylorTwoIntegrand μ h3 t
  have hExpEq :
      (∫ x, Complex.exp (↑t * ↑x * Complex.I) ∂μ) =
        ∫ x, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    congr 2
    norm_num
  have hEq :
      charFun μ t - ∫ x, charFunTaylorTwoIntegrand t x ∂μ =
        ∫ x, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
          charFunTaylorTwoIntegrand t x) ∂μ := by
    rw [charFun_apply_real, hExpEq]
    rw [integral_sub hExp hPoly]
  rw [hEq]
  have hBoundInt :
      Integrable (fun x : ℝ => (1 / 6 : ℝ) * |t| ^ 3 * |x| ^ 3) μ := by
    convert h3.const_mul ((1 / 6 : ℝ) * |t| ^ 3) using 1
  calc
    ‖∫ x, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
          charFunTaylorTwoIntegrand t x) ∂μ‖
        ≤ ∫ x, ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
          charFunTaylorTwoIntegrand t x‖ ∂μ :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ x, (1 / 6 : ℝ) * |t| ^ 3 * |x| ^ 3 ∂μ := by
          exact integral_mono (hExp.sub hPoly).norm hBoundInt
            (fun x => norm_exp_I_sub_charFunTaylorTwoIntegrand_le_cubic t x)
    _ = (1 / 6 : ℝ) * |t| ^ 3 * ∫ x, |x| ^ 3 ∂μ := by
          rw [integral_const_mul]

/-- Cubic characteristic-function Taylor estimate against the quadratic
variance-one approximation. -/
lemma norm_charFun_sub_quadratic_le_cubic
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (t : ℝ) :
    ‖charFun μ t - ((1 : ℂ) - (t ^ 2 : ℂ) / 2)‖ ≤
      (1 / 6 : ℝ) * |t| ^ 3 * ∫ x, |x| ^ 3 ∂μ := by
  simpa [integral_charFunTaylorTwoIntegrand_eq μ h3 hmean hsecond t] using
    norm_charFun_sub_integral_taylor_two_le_cubic μ h3 t

lemma integral_abs_cube_nonneg (μ : Measure ℝ) :
    0 ≤ ∫ x, |x| ^ 3 ∂μ := by
  exact MeasureTheory.integral_nonneg fun x =>
    pow_nonneg (abs_nonneg x) 3

/-- A small-frequency decay estimate for a centered variance-one
characteristic function.  The hypothesis `(2 / 3) E|X|³ |t| ≤ 1` makes the
third-order Taylor remainder small enough that the quadratic term forces
Gaussian-type decay. -/
lemma norm_charFun_le_exp_neg_sq_div_four
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {t : ℝ} (ht_sq : t ^ 2 ≤ 1)
    (ht_small : (2 / 3 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ≤ 1) :
    ‖charFun μ t‖ ≤ Real.exp (-(t ^ 2) / 4) := by
  let M : ℝ := ∫ x, |x| ^ 3 ∂μ
  let q : ℂ := (1 : ℂ) - (t ^ 2 : ℂ) / 2
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_abs_cube_nonneg μ
  have hrem_le : (1 / 6 : ℝ) * |t| ^ 3 * M ≤ t ^ 2 / 4 := by
    by_cases ht0 : t = 0
    · subst t
      simp
    · have ht_abs_pos : 0 < |t| := abs_pos.mpr ht0
      have ht_abs_sq : |t| ^ 2 = t ^ 2 := sq_abs t
      have hsmall' : (1 / 6 : ℝ) * M * |t| ≤ 1 / 4 := by
        have hsmallM : (2 / 3 : ℝ) * M * |t| ≤ 1 := by
          simpa [M, mul_assoc] using ht_small
        nlinarith
      calc
        (1 / 6 : ℝ) * |t| ^ 3 * M
            = t ^ 2 * ((1 / 6 : ℝ) * M * |t|) := by
              rw [← ht_abs_sq]
              ring
        _ ≤ t ^ 2 * (1 / 4) :=
              mul_le_mul_of_nonneg_left hsmall' (sq_nonneg t)
        _ = t ^ 2 / 4 := by ring
  have hTaylor :
      ‖charFun μ t - q‖ ≤ t ^ 2 / 4 := by
    exact (norm_charFun_sub_quadratic_le_cubic μ h3 hmean hsecond t).trans
      (by simpa [M, q, mul_comm, mul_left_comm, mul_assoc] using hrem_le)
  have hq_nonneg : 0 ≤ 1 - t ^ 2 / 2 := by
    nlinarith [sq_nonneg t, ht_sq]
  have hq_norm : ‖q‖ = 1 - t ^ 2 / 2 := by
    dsimp [q]
    have hcast :
        (1 : ℂ) - (t ^ 2 : ℂ) / 2 =
          ((1 - t ^ 2 / 2 : ℝ) : ℂ) := by
      norm_cast
    rw [hcast]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
  have hdecomp : charFun μ t = q + (charFun μ t - q) := by
    ring
  calc
    ‖charFun μ t‖
        = ‖q + (charFun μ t - q)‖ :=
          congrArg (fun z : ℂ => ‖z‖) hdecomp
    _ ≤ ‖q‖ + ‖charFun μ t - q‖ := norm_add_le _ _
    _ ≤ (1 - t ^ 2 / 2) + t ^ 2 / 4 :=
          add_le_add (le_of_eq hq_norm) hTaylor
    _ = -(t ^ 2) / 4 + 1 := by ring
    _ ≤ Real.exp (-(t ^ 2) / 4) := by
          simpa [add_comm] using Real.add_one_le_exp (-(t ^ 2) / 4)

/-- Durrett's larger-window decay estimate for a centered variance-one
characteristic function.  It uses the weaker decay `exp(-5 t² / 18)`, but is
valid on the larger window `t² ≤ 2` under the corresponding
`E|X|³ |t| ≤ 4/3` small-frequency hypothesis. -/
lemma norm_charFun_le_exp_neg_five_sq_div_eighteen
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {t : ℝ} (ht_sq : t ^ 2 ≤ 2)
    (ht_small : (∫ x, |x| ^ 3 ∂μ) * |t| ≤ 4 / 3) :
    ‖charFun μ t‖ ≤ Real.exp (-(5 / 18 : ℝ) * t ^ 2) := by
  let M : ℝ := ∫ x, |x| ^ 3 ∂μ
  let q : ℂ := (1 : ℂ) - (t ^ 2 : ℂ) / 2
  have hrem_le : (1 / 6 : ℝ) * |t| ^ 3 * M ≤ (2 / 9 : ℝ) * t ^ 2 := by
    by_cases ht0 : t = 0
    · subst t
      simp
    · have ht_abs_sq : |t| ^ 2 = t ^ 2 := sq_abs t
      calc
        (1 / 6 : ℝ) * |t| ^ 3 * M
            = t ^ 2 * ((1 / 6 : ℝ) * M * |t|) := by
              rw [← ht_abs_sq]
              ring
        _ ≤ t ^ 2 * (2 / 9 : ℝ) := by
              have hsmall' : (1 / 6 : ℝ) * M * |t| ≤ 2 / 9 := by
                have hmul :=
                  mul_le_mul_of_nonneg_left ht_small
                    (by norm_num : (0 : ℝ) ≤ 1 / 6)
                nlinarith
              exact mul_le_mul_of_nonneg_left hsmall' (sq_nonneg t)
        _ = (2 / 9 : ℝ) * t ^ 2 := by ring
  have hTaylor :
      ‖charFun μ t - q‖ ≤ (2 / 9 : ℝ) * t ^ 2 := by
    exact (norm_charFun_sub_quadratic_le_cubic μ h3 hmean hsecond t).trans
      (by simpa [M, q, mul_comm, mul_left_comm, mul_assoc] using hrem_le)
  have hq_nonneg : 0 ≤ 1 - t ^ 2 / 2 := by
    nlinarith [sq_nonneg t, ht_sq]
  have hq_norm : ‖q‖ = 1 - t ^ 2 / 2 := by
    dsimp [q]
    have hcast :
        (1 : ℂ) - (t ^ 2 : ℂ) / 2 =
          ((1 - t ^ 2 / 2 : ℝ) : ℂ) := by
      norm_cast
    rw [hcast]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
  have hdecomp : charFun μ t = q + (charFun μ t - q) := by
    ring
  calc
    ‖charFun μ t‖
        = ‖q + (charFun μ t - q)‖ :=
          congrArg (fun z : ℂ => ‖z‖) hdecomp
    _ ≤ ‖q‖ + ‖charFun μ t - q‖ := norm_add_le _ _
    _ ≤ (1 - t ^ 2 / 2) + (2 / 9 : ℝ) * t ^ 2 :=
          add_le_add (le_of_eq hq_norm) hTaylor
    _ = 1 + (-(5 / 18 : ℝ) * t ^ 2) := by ring
    _ ≤ Real.exp (-(5 / 18 : ℝ) * t ^ 2) := by
          have h := Real.add_one_le_exp (-(5 / 18 : ℝ) * t ^ 2)
          linarith

end TaylorBounds

section PowerComparison

/-- Telescoping estimate for powers in the unit disk:
`‖z^n - w^n‖ ≤ n ‖z - w‖`.  This is the algebraic step used when the
characteristic function of a normalized sum is written as an `n`th power. -/
lemma norm_pow_sub_pow_le_of_norm_le_one {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤ (n : ℝ) * ‖z - w‖ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hpowz : ‖z ^ n‖ ≤ 1 := by
        rw [norm_pow]
        exact pow_le_one₀ (n := n) (norm_nonneg z) hz
      have hdecomp :
          z ^ (n + 1) - w ^ (n + 1) =
            z ^ n * (z - w) + (z ^ n - w ^ n) * w := by
        rw [pow_succ, pow_succ]
        ring
      rw [hdecomp]
      calc
        ‖z ^ n * (z - w) + (z ^ n - w ^ n) * w‖
            ≤ ‖z ^ n * (z - w)‖ + ‖(z ^ n - w ^ n) * w‖ :=
              norm_add_le _ _
        _ = ‖z ^ n‖ * ‖z - w‖ + ‖z ^ n - w ^ n‖ * ‖w‖ := by
              rw [norm_mul, norm_mul]
        _ ≤ 1 * ‖z - w‖ + ((n : ℝ) * ‖z - w‖) * 1 := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul_of_nonneg_right hpowz (norm_nonneg _)
              · exact mul_le_mul ih hw (norm_nonneg _) <|
                  mul_nonneg (Nat.cast_nonneg n) (norm_nonneg _)
        _ = ((n + 1 : ℕ) : ℝ) * ‖z - w‖ := by
              norm_num
              ring

/-- Weighted telescoping estimate for complex powers.  This is the
Prawitz/Shevtsova form before specializing both bases to the unit disk or to a
common damping radius. -/
lemma norm_pow_sub_pow_le_geom_sum {z w : ℂ} (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤
      ‖z - w‖ *
        (Finset.range n).sum
          (fun k => ‖z‖ ^ k * ‖w‖ ^ (n - 1 - k)) := by
  have hgeom :
      (z - w) *
          (Finset.range n).sum
            (fun k => z ^ k * w ^ (n - 1 - k)) =
        z ^ n - w ^ n :=
    (Commute.all z w).mul_geom_sum₂ n
  rw [← hgeom, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc
    ‖(Finset.range n).sum (fun k => z ^ k * w ^ (n - 1 - k))‖
        ≤ (Finset.range n).sum
            (fun k => ‖z ^ k * w ^ (n - 1 - k)‖) :=
          norm_sum_le _ _
    _ = (Finset.range n).sum
          (fun k => ‖z‖ ^ k * ‖w‖ ^ (n - 1 - k)) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          simp [norm_pow]

/-- Damped telescoping estimate for powers.  If both bases are bounded by
`r`, then the power difference gains the factor `r^(n-1)`. -/
lemma norm_pow_succ_sub_pow_succ_le_of_norm_le {z w : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) (n : ℕ) :
    ‖z ^ (n + 1) - w ^ (n + 1)‖ ≤
      ((n + 1 : ℕ) : ℝ) * ‖z - w‖ * r ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hpowz : ‖z ^ (n + 1)‖ ≤ r ^ (n + 1) := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg z) hz (n + 1)
      have hright_nonneg :
          0 ≤ ((n + 1 : ℕ) : ℝ) * ‖z - w‖ * r ^ n := by
        positivity
      have hdecomp :
          z ^ (n + 1 + 1) - w ^ (n + 1 + 1) =
            z ^ (n + 1) * (z - w) +
              (z ^ (n + 1) - w ^ (n + 1)) * w := by
        rw [pow_succ, pow_succ]
        ring
      rw [hdecomp]
      calc
        ‖z ^ (n + 1) * (z - w) +
            (z ^ (n + 1) - w ^ (n + 1)) * w‖
            ≤ ‖z ^ (n + 1) * (z - w)‖ +
                ‖(z ^ (n + 1) - w ^ (n + 1)) * w‖ :=
              norm_add_le _ _
        _ = ‖z ^ (n + 1)‖ * ‖z - w‖ +
              ‖z ^ (n + 1) - w ^ (n + 1)‖ * ‖w‖ := by
              rw [norm_mul, norm_mul]
        _ ≤ r ^ (n + 1) * ‖z - w‖ +
              (((n + 1 : ℕ) : ℝ) * ‖z - w‖ * r ^ n) * r := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul_of_nonneg_right hpowz (norm_nonneg _)
              · exact mul_le_mul ih hw (norm_nonneg _) hright_nonneg
        _ = ((n + 1 + 1 : ℕ) : ℝ) * ‖z - w‖ * r ^ (n + 1) := by
              rw [pow_succ]
              ring_nf
              let A : ℝ := r * r ^ n * ‖z - w‖
              change A + A * ((1 + n : ℕ) : ℝ) =
                A * ((2 + n : ℕ) : ℝ)
              have hcast :
                  ((2 + n : ℕ) : ℝ) = ((1 + n : ℕ) : ℝ) + 1 := by
                norm_num
                ring
              rw [hcast]
              ring

lemma norm_one_sub_real_le_one {u : ℝ} (hu0 : 0 ≤ u) (hu2 : u ≤ 2) :
    ‖(1 : ℂ) - (u : ℂ)‖ ≤ 1 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_le]
  constructor <;> linarith

lemma norm_exp_neg_real_le_one {u : ℝ} (hu0 : 0 ≤ u) :
    ‖Complex.exp (-(u : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hre : (-(u : ℂ)).re = -u := by simp
  rw [hre]
  exact Real.exp_le_one_iff.mpr (by linarith)

lemma norm_one_sub_real_le_exp_neg {u : ℝ} (_hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(1 : ℂ) - (u : ℂ)‖ ≤ Real.exp (-u) := by
  have hnonneg : 0 ≤ 1 - u := by linarith
  have hnorm :
      ‖(1 : ℂ) - (u : ℂ)‖ = 1 - u := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [hnorm]
  have hExp : -u + 1 ≤ Real.exp (-u) := Real.add_one_le_exp (-u)
  linarith

lemma real_sqrt_one_sub_le_exp_neg_half {a : ℝ} :
    Real.sqrt (1 - a) ≤ Real.exp (-(a / 2)) := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact (Real.exp_pos _).le
  · have hbase : 1 - a ≤ Real.exp (-a) := by
      have h := Real.add_one_le_exp (-a)
      linarith
    have hexp_sq :
        Real.exp (-(a / 2)) ^ 2 = Real.exp (-a) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rwa [hexp_sq]

lemma real_sqrt_one_sub_pow_le_exp_neg_mul_of_ge
    {a b : ℝ} (hb_le : b ≤ a) (n : ℕ) :
    (Real.sqrt (1 - a)) ^ n ≤ Real.exp (-((n : ℝ) * b) / 2) := by
  have hsqrt :
      Real.sqrt (1 - a) ≤ Real.exp (-(a / 2)) :=
    real_sqrt_one_sub_le_exp_neg_half
  have hpow :
      (Real.sqrt (1 - a)) ^ n ≤
        (Real.exp (-(a / 2))) ^ n :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt n
  have hexp_pow :
      (Real.exp (-(a / 2))) ^ n =
        Real.exp (-((n : ℝ) * a) / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hexp_mono :
      Real.exp (-((n : ℝ) * a) / 2) ≤
        Real.exp (-((n : ℝ) * b) / 2) := by
    apply Real.exp_le_exp.mpr
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  exact hpow.trans (hexp_pow ▸ hexp_mono)

/-- A global, deliberately non-sharp estimate for the real exponential piece
used to compare the quadratic characteristic-function approximation with the
Gaussian exponential. -/
lemma norm_one_sub_sub_exp_neg_le_sq {u : ℝ} (hu0 : 0 ≤ u) :
    ‖((1 : ℂ) - (u : ℂ)) - Complex.exp (-(u : ℂ))‖ ≤ u ^ 2 := by
  by_cases hu1 : u ≤ 1
  · have hz : ‖-(u : ℂ)‖ ≤ 1 := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      exact hu1
    have h := Complex.norm_exp_sub_one_sub_id_le (x := -(u : ℂ)) hz
    have hEq :
        ((1 : ℂ) - (u : ℂ)) - Complex.exp (-(u : ℂ)) =
          -(Complex.exp (-(u : ℂ)) - 1 - (-(u : ℂ))) := by
      ring
    rw [hEq, norm_neg]
    simpa [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      using h
  · have hge1 : 1 ≤ u := le_of_not_ge hu1
    have hexp_eq :
        Complex.exp (-(u : ℂ)) = (Real.exp (-u) : ℂ) := by
      rw [show -(u : ℂ) = ((-u : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_exp]
    rw [hexp_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have he0 : 0 ≤ Real.exp (-u) := Real.exp_nonneg _
    have he1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    constructor <;> nlinarith [hge1, hu0, he0, he1, sq_nonneg u]

lemma exp_neg_le_one_sub_add_sq_div_two {u : ℝ} (hu0 : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  let g : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hg_deriv :
      ∀ x : ℝ, HasDerivAt g (-1 + x + Real.exp (-x)) x := by
    intro x
    dsimp [g]
    convert
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
        (((hasDerivAt_id x).pow 2).div_const 2)).sub
        ((Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)) using 1
    simp [id]
  have hg_nonneg :
      (0 : ℝ → ℝ) ≤ (fun x : ℝ => -1 + x + Real.exp (-x)) := by
    intro x
    change 0 ≤ -1 + x + Real.exp (-x)
    have h := Real.add_one_le_exp (-x)
    nlinarith
  have hg_mono : Monotone g :=
    monotone_of_hasDerivAt_nonneg hg_deriv hg_nonneg
  have h0u : g 0 ≤ g u := hg_mono hu0
  have hg0 : g 0 = 0 := by simp [g]
  have hgu : 0 ≤ g u := by simpa [hg0] using h0u
  dsimp [g] at hgu
  nlinarith

lemma norm_one_sub_sub_exp_neg_le_sq_div_two {u : ℝ} (hu0 : 0 ≤ u) :
    ‖((1 : ℂ) - (u : ℂ)) - Complex.exp (-(u : ℂ))‖ ≤ u ^ 2 / 2 := by
  have hupper := exp_neg_le_one_sub_add_sq_div_two (u := u) hu0
  have hlower : 1 - u ≤ Real.exp (-u) := by
    have h := Real.add_one_le_exp (-u)
    linarith
  have hexp_eq : Complex.exp (-(u : ℂ)) = (Real.exp (-u) : ℂ) := by
    rw [show -(u : ℂ) = ((-u : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_exp]
  rw [hexp_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonpos]
  · linarith
  · linarith

/-- One-summand characteristic-function error against the matching normal
characteristic function.  This is the local Taylor piece used in the
Shevtsova/Prawitz `r_n` telescoping estimate. -/
lemma norm_charFun_sub_standardNormalCharFun_le_cubic_quartic
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (t : ℝ) :
    ‖charFun μ t - charFun standardNormalMeasure t‖ ≤
      (1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 3 +
        t ^ 4 / 8 := by
  let q : ℂ := (1 : ℂ) - (t ^ 2 : ℂ) / 2
  let s : ℝ := t ^ 2 / 2
  have hTaylor :
      ‖charFun μ t - q‖ ≤
        (1 / 6 : ℝ) * |t| ^ 3 * ∫ x, |x| ^ 3 ∂μ := by
    dsimp [q]
    exact norm_charFun_sub_quadratic_le_cubic μ h3 hmean hsecond t
  have hnormal :
      charFun standardNormalMeasure t = Complex.exp (-(s : ℂ)) := by
    rw [standardNormal_charFun]
    congr 1
    norm_cast
    dsimp [s]
    ring
  have hq : q = (1 : ℂ) - (s : ℂ) := by
    dsimp [q, s]
    norm_num
  have hExpDiff :
      ‖q - charFun standardNormalMeasure t‖ ≤ t ^ 4 / 8 := by
    have hs0 : 0 ≤ s := by
      dsimp [s]
      positivity
    have h := norm_one_sub_sub_exp_neg_le_sq_div_two (u := s) hs0
    have hsq : s ^ 2 / 2 = t ^ 4 / 8 := by
      dsimp [s]
      ring
    rw [hq, hnormal]
    simpa [hsq] using h
  calc
    ‖charFun μ t - charFun standardNormalMeasure t‖
        = ‖(charFun μ t - q) +
            (q - charFun standardNormalMeasure t)‖ := by
          congr 1
          ring
    _ ≤ ‖charFun μ t - q‖ +
          ‖q - charFun standardNormalMeasure t‖ :=
          norm_add_le _ _
    _ ≤ (1 / 6 : ℝ) * |t| ^ 3 * ∫ x, |x| ^ 3 ∂μ +
          t ^ 4 / 8 :=
          add_le_add hTaylor hExpDiff
    _ = (1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 3 +
          t ^ 4 / 8 := by ring

lemma norm_one_sub_pow_sub_exp_neg_pow_le {u : ℝ}
    (hu0 : 0 ≤ u) (hu2 : u ≤ 2) (n : ℕ) :
    ‖((1 : ℂ) - (u : ℂ)) ^ n - (Complex.exp (-(u : ℂ))) ^ n‖ ≤
      (n : ℝ) * u ^ 2 := by
  have hpow :=
    norm_pow_sub_pow_le_of_norm_le_one
      (norm_one_sub_real_le_one hu0 hu2)
      (norm_exp_neg_real_le_one hu0) n
  exact hpow.trans
    (mul_le_mul_of_nonneg_left
      (norm_one_sub_sub_exp_neg_le_sq hu0) (Nat.cast_nonneg n))

lemma norm_one_sub_pow_succ_sub_exp_neg_pow_succ_le_exp {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    ‖((1 : ℂ) - (u : ℂ)) ^ (n + 1) -
        (Complex.exp (-(u : ℂ))) ^ (n + 1)‖ ≤
      ((n + 1 : ℕ) : ℝ) * (u ^ 2 / 2) *
        (Real.exp (-u)) ^ n := by
  have hr : 0 ≤ Real.exp (-u) := Real.exp_nonneg _
  have hExpNorm :
      ‖Complex.exp (-(u : ℂ))‖ ≤ Real.exp (-u) := by
    rw [Complex.norm_exp]
    have hre : (-(u : ℂ)).re = -u := by simp
    rw [hre]
  have hpow :=
    norm_pow_succ_sub_pow_succ_le_of_norm_le
      (z := (1 : ℂ) - (u : ℂ))
      (w := Complex.exp (-(u : ℂ)))
      (r := Real.exp (-u))
      hr (norm_one_sub_real_le_exp_neg hu0 hu1) hExpNorm n
  have hdiff := norm_one_sub_sub_exp_neg_le_sq_div_two hu0
  calc
    ‖((1 : ℂ) - (u : ℂ)) ^ (n + 1) -
        (Complex.exp (-(u : ℂ))) ^ (n + 1)‖
        ≤ ((n + 1 : ℕ) : ℝ) *
            ‖((1 : ℂ) - (u : ℂ)) - Complex.exp (-(u : ℂ))‖ *
              (Real.exp (-u)) ^ n := hpow
    _ ≤ ((n + 1 : ℕ) : ℝ) * (u ^ 2 / 2) *
          (Real.exp (-u)) ^ n := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg (n + 1)))
            (pow_nonneg hr n)

/-- Damped quantitative comparison between `(1-u)^(n+1)` and
`exp (-(n+1)u)`.  The bound keeps the Gaussian decay that is needed for the
final Esseen integral. -/
lemma norm_one_sub_pow_succ_sub_exp_neg_nmul_le_exp {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    ‖((1 : ℂ) - (u : ℂ)) ^ (n + 1) -
        Complex.exp ((-(((n + 1 : ℕ) : ℝ) * u) : ℝ) : ℂ)‖ ≤
      ((n + 1 : ℕ) : ℝ) * (u ^ 2 / 2) *
        (Real.exp (-u)) ^ n := by
  have h :=
    norm_one_sub_pow_succ_sub_exp_neg_pow_succ_le_exp
      (u := u) hu0 hu1 n
  have hexp :
      (Complex.exp (-(u : ℂ))) ^ (n + 1) =
        Complex.exp ((-(((n + 1 : ℕ) : ℝ) * u) : ℝ) : ℂ) := by
    rw [← Complex.exp_nat_mul (-(u : ℂ)) (n + 1)]
    congr 1
    norm_cast
    ring
  simpa [hexp] using h

/-- Quantitative comparison between `(1-u)^n` and `exp(-nu)`, valid while
`0 ≤ u ≤ 2`.  This is the local replacement for the usual informal
`(1 - y/n)^n ≈ e^{-y}` step. -/
lemma norm_one_sub_pow_sub_exp_neg_nmul_le {u : ℝ}
    (hu0 : 0 ≤ u) (hu2 : u ≤ 2) (n : ℕ) :
    ‖((1 : ℂ) - (u : ℂ)) ^ n -
        Complex.exp ((-((n : ℝ) * u) : ℝ) : ℂ)‖ ≤
      (n : ℝ) * u ^ 2 := by
  have h :=
    norm_one_sub_pow_sub_exp_neg_pow_le (u := u) hu0 hu2 n
  have hexp :
      (Complex.exp (-(u : ℂ))) ^ n =
        Complex.exp ((-((n : ℝ) * u) : ℝ) : ℂ) := by
    rw [← Complex.exp_nat_mul (-(u : ℂ)) n]
    congr 1
    norm_cast
    ring
  simpa [hexp] using h

/-- Central-window specialization of the Gaussian power comparison:
for `u = t²/(2n)`, `(1-u)^n` is within `t⁴/(4n)` of `exp(-t²/2)`,
provided `t² ≤ 4n`. -/
lemma norm_one_sub_quadratic_scaled_pow_sub_gaussian_exp_le
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ^ 2 ≤ 4 * (n : ℝ)) :
    ‖((1 : ℂ) - ((t ^ 2 / (2 * (n : ℝ)) : ℝ) : ℂ)) ^ n -
        Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ)‖ ≤
      t ^ 4 / (4 * (n : ℝ)) := by
  let u : ℝ := t ^ 2 / (2 * (n : ℝ))
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hden : 0 < 2 * (n : ℝ) := by positivity
  have hu0 : 0 ≤ u := by
    dsimp [u]
    positivity
  have hu2 : u ≤ 2 := by
    dsimp [u]
    rw [div_le_iff₀ hden]
    nlinarith
  have h :=
    norm_one_sub_pow_sub_exp_neg_nmul_le (u := u) hu0 hu2 n
  have hexp_arg : -((n : ℝ) * u) = -(t ^ 2 / 2) := by
    dsimp [u]
    field_simp [hnR.ne']
  have hbudget : (n : ℝ) * u ^ 2 = t ^ 4 / (4 * (n : ℝ)) := by
    dsimp [u]
    field_simp [hnR.ne']
    ring
  simpa [u, hexp_arg, hbudget] using h

/-- Damped central-window specialization of the Gaussian power comparison:
for `u = t²/(2(n+1))`, `(1-u)^(n+1)` is close to `exp(-t²/2)` with a
remnant exponential factor. -/
lemma norm_one_sub_quadratic_scaled_pow_succ_sub_gaussian_exp_le_exp
    (n : ℕ) {t : ℝ}
    (ht : t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ)) :
    ‖((1 : ℂ) -
        ((t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ)) ^ (n + 1) -
        Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ)‖ ≤
      t ^ 4 / (8 * ((n + 1 : ℕ) : ℝ)) *
        (Real.exp (-(t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))))) ^ n := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let u : ℝ := t ^ 2 / (2 * N)
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hden : 0 < 2 * N := by positivity
  have hu0 : 0 ≤ u := by
    dsimp [u]
    positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_iff₀ hden]
    simpa [N] using ht
  have h :=
    norm_one_sub_pow_succ_sub_exp_neg_nmul_le_exp (u := u) hu0 hu1 n
  have hexp_arg :
      -(((n + 1 : ℕ) : ℝ) * u) = -(t ^ 2 / 2) := by
    dsimp [u, N]
    field_simp [hN_pos.ne']
  have hbudget :
      ((n + 1 : ℕ) : ℝ) * (u ^ 2 / 2) =
        t ^ 4 / (8 * ((n + 1 : ℕ) : ℝ)) := by
    dsimp [u, N]
    field_simp [hN_pos.ne']
    ring
  rw [hexp_arg, hbudget] at h
  simpa [u, N] using h

/-- Pointwise Berry-Esseen Fourier estimate on the central window.  The first
term is the telescoped third-moment Taylor error for one summand; the second
term is the quantitative comparison of `(1 - t²/(2n))^n` with
`exp (-t²/2)`. -/
lemma norm_charFun_scaled_pow_sub_standardNormal_charFun_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ^ 2 ≤ 4 * (n : ℝ)) :
    ‖charFun μ (t / Real.sqrt (n : ℝ)) ^ n -
        charFun standardNormalMeasure t‖ ≤
      (n : ℝ) *
          (4 * |t / Real.sqrt (n : ℝ)| ^ 3 *
            ∫ x, |x| ^ 3 ∂μ) +
        t ^ 4 / (4 * (n : ℝ)) := by
  let u : ℝ := t / Real.sqrt (n : ℝ)
  let q : ℂ := (1 : ℂ) - ((t ^ 2 / (2 * (n : ℝ)) : ℝ) : ℂ)
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hq_arg_nonneg : 0 ≤ t ^ 2 / (2 * (n : ℝ)) := by positivity
  have hq_arg_le : t ^ 2 / (2 * (n : ℝ)) ≤ 2 := by
    have hden : 0 < 2 * (n : ℝ) := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hq_norm : ‖q‖ ≤ 1 := by
    dsimp [q]
    exact norm_one_sub_real_le_one hq_arg_nonneg hq_arg_le
  have hquad_eq :
      ((1 : ℂ) - (u ^ 2 : ℂ) / 2) = q := by
    have hu_sq_div : u ^ 2 / 2 = t ^ 2 / ((2 * n : ℕ) : ℝ) := by
      dsimp [u]
      rw [div_pow, Real.sq_sqrt hnR.le]
      have hden_cast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by
        norm_num
      rw [hden_cast]
      field_simp [hnR.ne']
    dsimp [q]
    norm_cast
    exact congrArg (fun y : ℝ => 1 - y) hu_sq_div
  have hTaylor :
      ‖charFun μ u - q‖ ≤
        4 * |u| ^ 3 * ∫ x, |x| ^ 3 ∂μ := by
    simpa [hquad_eq] using
      norm_charFun_sub_quadratic_le μ h3 hmean hsecond u
  have hfirst :
      ‖charFun μ u ^ n - q ^ n‖ ≤
        (n : ℝ) *
          (4 * |u| ^ 3 * ∫ x, |x| ^ 3 ∂μ) := by
    have hpow :=
      norm_pow_sub_pow_le_of_norm_le_one
        (MeasureTheory.norm_charFun_le_one (μ := μ) u) hq_norm n
    exact hpow.trans
      (mul_le_mul_of_nonneg_left hTaylor (Nat.cast_nonneg n))
  have hsecond_pow :
      ‖q ^ n - Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ)‖ ≤
        t ^ 4 / (4 * (n : ℝ)) := by
    dsimp [q]
    exact norm_one_sub_quadratic_scaled_pow_sub_gaussian_exp_le hn ht
  have hgauss :
      Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ) =
        charFun standardNormalMeasure t := by
    rw [standardNormal_charFun]
    congr 1
    norm_cast
    ring
  calc
    ‖charFun μ (t / Real.sqrt (n : ℝ)) ^ n -
        charFun standardNormalMeasure t‖
        = ‖charFun μ u ^ n -
            Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ)‖ := by
          rw [hgauss]
    _ = ‖(charFun μ u ^ n - q ^ n) +
            (q ^ n - Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ))‖ := by
          congr 1
          ring
    _ ≤ ‖charFun μ u ^ n - q ^ n‖ +
          ‖q ^ n - Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ)‖ :=
          norm_add_le _ _
    _ ≤ (n : ℝ) *
          (4 * |u| ^ 3 * ∫ x, |x| ^ 3 ∂μ) +
        t ^ 4 / (4 * (n : ℝ)) :=
          add_le_add hfirst hsecond_pow
    _ = (n : ℝ) *
          (4 * |t / Real.sqrt (n : ℝ)| ^ 3 *
            ∫ x, |x| ^ 3 ∂μ) +
        t ^ 4 / (4 * (n : ℝ)) := by
          simp [u]

/-- Damped Taylor-power estimate for a centered variance-one law.  This is
the sharpened version of the first term in
`norm_charFun_scaled_pow_sub_standardNormal_charFun_le`: small frequencies
give an additional Gaussian decay factor. -/
lemma norm_charFun_pow_succ_sub_quadratic_pow_succ_le_exp
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {u : ℝ} (hu_sq : u ^ 2 ≤ 1)
    (hu_small : (2 / 3 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |u| ≤ 1)
    (n : ℕ) :
    ‖charFun μ u ^ (n + 1) -
        ((1 : ℂ) - (u ^ 2 : ℂ) / 2) ^ (n + 1)‖ ≤
      ((n + 1 : ℕ) : ℝ) *
        ((1 / 6 : ℝ) * |u| ^ 3 * ∫ x, |x| ^ 3 ∂μ) *
          (Real.exp (-(u ^ 2) / 4)) ^ n := by
  let q : ℂ := (1 : ℂ) - (u ^ 2 : ℂ) / 2
  let r : ℝ := Real.exp (-(u ^ 2) / 4)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.exp_nonneg _
  have hz : ‖charFun μ u‖ ≤ r := by
    dsimp [r]
    exact norm_charFun_le_exp_neg_sq_div_four
      (μ := μ) h3 hmean hsecond hu_sq hu_small
  have hq_nonneg : 0 ≤ 1 - u ^ 2 / 2 := by
    nlinarith [sq_nonneg u, hu_sq]
  have hq_norm_eq : ‖q‖ = 1 - u ^ 2 / 2 := by
    dsimp [q]
    have hcast :
        (1 : ℂ) - (u ^ 2 : ℂ) / 2 =
          ((1 - u ^ 2 / 2 : ℝ) : ℂ) := by
      norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hq_nonneg]
  have hq : ‖q‖ ≤ r := by
    rw [hq_norm_eq]
    have hlin : 1 - u ^ 2 / 2 ≤ -(u ^ 2) / 4 + 1 := by
      nlinarith [sq_nonneg u]
    have hexp : -(u ^ 2) / 4 + 1 ≤ r := by
      dsimp [r]
      simpa [add_comm] using Real.add_one_le_exp (-(u ^ 2) / 4)
    exact hlin.trans hexp
  have hdiff :
      ‖charFun μ u - q‖ ≤
        (1 / 6 : ℝ) * |u| ^ 3 * ∫ x, |x| ^ 3 ∂μ := by
    dsimp [q]
    exact norm_charFun_sub_quadratic_le_cubic μ h3 hmean hsecond u
  have htel :=
    norm_pow_succ_sub_pow_succ_le_of_norm_le
      (z := charFun μ u) (w := q) (r := r)
      hr_nonneg hz hq n
  have hmul :
      ((n + 1 : ℕ) : ℝ) * ‖charFun μ u - q‖ ≤
        ((n + 1 : ℕ) : ℝ) *
          ((1 / 6 : ℝ) * |u| ^ 3 * ∫ x, |x| ^ 3 ∂μ) :=
    mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg (n + 1))
  have hmul' :
      ((n + 1 : ℕ) : ℝ) * ‖charFun μ u - q‖ * r ^ n ≤
        ((n + 1 : ℕ) : ℝ) *
          ((1 / 6 : ℝ) * |u| ^ 3 * ∫ x, |x| ^ 3 ∂μ) * r ^ n :=
    mul_le_mul_of_nonneg_right hmul (pow_nonneg hr_nonneg n)
  exact htel.trans (by simpa [q, r, mul_assoc] using hmul')

/-- Damped pointwise comparison of the normalized-sum characteristic-function
power with the standard normal characteristic function.  This is the
Fourier-side estimate that is ready to be integrated in the final Esseen
assembly, stated for `n + 1` summands to avoid a predecessor in the exponent
of the damping factor. -/
lemma norm_charFun_scaled_pow_succ_sub_standardNormal_charFun_le_exp
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (n : ℕ) {t : ℝ}
    (ht_window : t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (ht_small :
      (2 / 3 : ℝ) * (∫ x, |x| ^ 3 ∂μ) *
        |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    ‖charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) -
        charFun standardNormalMeasure t‖ ≤
      ((n + 1 : ℕ) : ℝ) *
        ((1 / 6 : ℝ) * |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ^ 3 *
          ∫ x, |x| ^ 3 ∂μ) *
        (Real.exp
            (-((t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2) / 4)) ^ n +
        t ^ 4 / (8 * ((n + 1 : ℕ) : ℝ)) *
          (Real.exp
            (-(t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))))) ^ n := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let u : ℝ := t / Real.sqrt N
  let q : ℂ := (1 : ℂ) - ((t ^ 2 / (2 * N) : ℝ) : ℂ)
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
  have hu_sq : u ^ 2 ≤ 1 := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt hN_pos.le]
    rw [div_le_iff₀ hN_pos]
    simpa [N] using ht_window
  have ht_window_four : t ^ 2 ≤ 4 * ((n + 1 : ℕ) : ℝ) := by
    have hN_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg (n + 1)
    nlinarith
  have ht_window_two : t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
    have hN_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg (n + 1)
    nlinarith
  have hquad_eq :
      ((1 : ℂ) - (u ^ 2 : ℂ) / 2) = q := by
    have hu_sq_div : u ^ 2 / 2 = t ^ 2 / (2 * N) := by
      dsimp [u]
      rw [div_pow, Real.sq_sqrt hN_pos.le]
      field_simp [hN_pos.ne']
    dsimp [q]
    norm_cast
    exact congrArg (fun y : ℝ => 1 - y) hu_sq_div
  have hfirst :
      ‖charFun μ u ^ (n + 1) - q ^ (n + 1)‖ ≤
        ((n + 1 : ℕ) : ℝ) *
          ((1 / 6 : ℝ) * |u| ^ 3 * ∫ x, |x| ^ 3 ∂μ) *
            (Real.exp (-(u ^ 2) / 4)) ^ n := by
    have h :=
      norm_charFun_pow_succ_sub_quadratic_pow_succ_le_exp
        (μ := μ) h3 hmean hsecond hu_sq (by simpa [u, N] using ht_small) n
    simpa [hquad_eq, q] using h
  have hsecond_pow :
      ‖q ^ (n + 1) - Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ)‖ ≤
        t ^ 4 / (8 * ((n + 1 : ℕ) : ℝ)) *
          (Real.exp
            (-(t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))))) ^ n := by
    dsimp [q, N]
    exact norm_one_sub_quadratic_scaled_pow_succ_sub_gaussian_exp_le_exp
      (n := n) ht_window_two
  have hgauss :
      Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ) =
        charFun standardNormalMeasure t := by
    rw [standardNormal_charFun]
    congr 1
    norm_cast
    ring
  calc
    ‖charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) -
        charFun standardNormalMeasure t‖
        = ‖charFun μ u ^ (n + 1) -
            Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ)‖ := by
          rw [hgauss]
    _ = ‖(charFun μ u ^ (n + 1) - q ^ (n + 1)) +
            (q ^ (n + 1) -
              Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ))‖ := by
          congr 1
          ring
    _ ≤ ‖charFun μ u ^ (n + 1) - q ^ (n + 1)‖ +
          ‖q ^ (n + 1) -
            Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ)‖ :=
          norm_add_le _ _
    _ ≤ ((n + 1 : ℕ) : ℝ) *
          ((1 / 6 : ℝ) * |u| ^ 3 * ∫ x, |x| ^ 3 ∂μ) *
            (Real.exp (-(u ^ 2) / 4)) ^ n +
          t ^ 4 / (8 * ((n + 1 : ℕ) : ℝ)) *
            (Real.exp
              (-(t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))))) ^ n :=
          add_le_add hfirst hsecond_pow
    _ = ((n + 1 : ℕ) : ℝ) *
          ((1 / 6 : ℝ) * |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ^ 3 *
            ∫ x, |x| ^ 3 ∂μ) *
            (Real.exp
              (-((t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2) / 4)) ^ n +
          t ^ 4 / (8 * ((n + 1 : ℕ) : ℝ)) *
            (Real.exp
              (-(t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))))) ^ n := by
          simp [u, N]

/-- A removable pointwise majorant for the Berry-Esseen Fourier integrand
on the central/small-frequency window.  It is the divided form of
`norm_charFun_scaled_pow_succ_sub_standardNormal_charFun_le_exp` after
cancelling the factor `|t|` at the origin. -/
def berryEsseenDampedFourierBound (μ : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
      Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (Real.exp
        (-((t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2) / 4)) ^ n +
    |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ)) *
      (Real.exp (-(t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))))) ^ n

lemma berryEsseenDampedFourierBound_nonneg
    (μ : Measure ℝ) (n : ℕ) (t : ℝ) :
    0 ≤ berryEsseenDampedFourierBound μ n t := by
  have hM : 0 ≤ ∫ x, |x| ^ 3 ∂μ := integral_abs_cube_nonneg μ
  unfold berryEsseenDampedFourierBound
  positivity

lemma continuous_berryEsseenDampedFourierBound
    (μ : Measure ℝ) (n : ℕ) :
    Continuous (berryEsseenDampedFourierBound μ n) := by
  unfold berryEsseenDampedFourierBound
  fun_prop

lemma integrableOn_berryEsseenDampedFourierBound
    (μ : Measure ℝ) (n : ℕ) (L : ℝ) :
    IntegrableOn (berryEsseenDampedFourierBound μ n) (Set.Icc (-L) L) :=
  (continuous_berryEsseenDampedFourierBound μ n).integrableOn_Icc

/-- Durrett's larger-window Fourier majorant.  Compared with
`berryEsseenDampedFourierBound`, it uses the weaker but wider decay
`exp(-t²/4)` and is paired with the cutoff `L = 4√N/(3ρ)`. -/
def berryEsseenDurrettFourierBound (μ : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
      Real.sqrt ((n + 1 : ℕ) : ℝ) +
    |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ))) *
    Real.exp (-(1 / 4 : ℝ) * t ^ 2)

lemma berryEsseenDurrettFourierBound_nonneg
    (μ : Measure ℝ) (n : ℕ) (t : ℝ) :
    0 ≤ berryEsseenDurrettFourierBound μ n t := by
  have hM : 0 ≤ ∫ x, |x| ^ 3 ∂μ := integral_abs_cube_nonneg μ
  unfold berryEsseenDurrettFourierBound
  positivity

lemma continuous_berryEsseenDurrettFourierBound
    (μ : Measure ℝ) (n : ℕ) :
    Continuous (berryEsseenDurrettFourierBound μ n) := by
  unfold berryEsseenDurrettFourierBound
  fun_prop

lemma integrableOn_berryEsseenDurrettFourierBound
    (μ : Measure ℝ) (n : ℕ) (L : ℝ) :
    IntegrableOn (berryEsseenDurrettFourierBound μ n) (Set.Icc (-L) L) :=
  (continuous_berryEsseenDurrettFourierBound μ n).integrableOn_Icc

/-- Durrett's `n ≥ 10` exponential simplification:
`exp(-5 t² n/(18(n+1))) ≤ exp(-t²/4)`.  The theorem is stated for `n+1`
summands, so the hypothesis is `9 ≤ n`. -/
lemma durrett_exp_scaled_pow_le_exp_neg_sq_div_four
    {n : ℕ} (hn : 9 ≤ n) (t : ℝ) :
    (Real.exp (-(5 / 18 : ℝ) *
        (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2)) ^ n ≤
      Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hnR : 9 ≤ (n : ℝ) := by exact_mod_cast hn
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hcoef : (1 / 4 : ℝ) ≤ (5 * (n : ℝ)) / (18 * ((n : ℝ) + 1)) := by
    have hden : 0 < 18 * ((n : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hden]
    nlinarith [hnR]
  have hN_eq : N = (n : ℝ) + 1 := by
    dsimp [N]
    norm_num
  have harg :
      (n : ℝ) *
          (-(5 / 18 : ℝ) *
            (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2) =
        -(((5 * (n : ℝ)) / (18 * ((n : ℝ) + 1))) * t ^ 2) := by
    rw [div_pow, Real.sq_sqrt hN_pos.le]
    rw [hN_eq]
    field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
  rw [harg]
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
  nlinarith

/-- Durrett's pointwise characteristic-function estimate on the larger
central window `t² ≤ 2N`, with `N = n+1`. -/
lemma norm_charFun_scaled_pow_succ_sub_standardNormal_charFun_le_durrett
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {n : ℕ} (hn : 9 ≤ n) {t : ℝ}
    (ht_window : t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (ht_small :
      (∫ x, |x| ^ 3 ∂μ) *
        |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    ‖charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) -
        charFun standardNormalMeasure t‖ ≤
      ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 3 /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        t ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) *
        Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let u : ℝ := t / Real.sqrt N
  let q : ℂ := (1 : ℂ) - (u ^ 2 : ℂ) / 2
  let w : ℂ := Complex.exp ((-(u ^ 2 / 2) : ℝ) : ℂ)
  let r : ℝ := Real.exp (-(5 / 18 : ℝ) * u ^ 2)
  let M : ℝ := ∫ x, |x| ^ 3 ∂μ
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.exp_nonneg _
  have hu_sq : u ^ 2 ≤ 2 := by
    dsimp [u, N]
    rw [div_pow, Real.sq_sqrt hN_pos.le]
    rw [div_le_iff₀ hN_pos]
    simpa [N] using ht_window
  have hz : ‖charFun μ u‖ ≤ r := by
    dsimp [r]
    exact norm_charFun_le_exp_neg_five_sq_div_eighteen
      (μ := μ) h3 hmean hsecond hu_sq (by simpa [u, N, M] using ht_small)
  have hw : ‖w‖ ≤ r := by
    have hw_norm : ‖w‖ = Real.exp (-(u ^ 2 / 2)) := by
      dsimp [w]
      rw [← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _)]
    rw [hw_norm]
    dsimp [r]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])
  have hTaylor :
      ‖charFun μ u - q‖ ≤
        (1 / 6 : ℝ) * |u| ^ 3 * M := by
    dsimp [q, M]
    exact norm_charFun_sub_quadratic_le_cubic μ h3 hmean hsecond u
  have hExpDiff :
      ‖q - w‖ ≤ u ^ 4 / 8 := by
    let s : ℝ := u ^ 2 / 2
    have hs0 : 0 ≤ s := by
      dsimp [s]
      positivity
    have h := norm_one_sub_sub_exp_neg_le_sq_div_two (u := s) hs0
    have hsq : s ^ 2 / 2 = u ^ 4 / 8 := by
      dsimp [s]
      ring
    have hqw :
        q - w = ((1 : ℂ) - (s : ℂ)) - Complex.exp (-(s : ℂ)) := by
      dsimp [q, w, s]
      norm_num
    rw [hqw]
    simpa [hsq] using h
  have hdiff :
      ‖charFun μ u - w‖ ≤
        (1 / 6 : ℝ) * |u| ^ 3 * M + u ^ 4 / 8 := by
    calc
      ‖charFun μ u - w‖
          = ‖(charFun μ u - q) + (q - w)‖ := by
            congr 1
            ring
      _ ≤ ‖charFun μ u - q‖ + ‖q - w‖ := norm_add_le _ _
      _ ≤ (1 / 6 : ℝ) * |u| ^ 3 * M + u ^ 4 / 8 :=
            add_le_add hTaylor hExpDiff
  have hpow :
      ‖charFun μ u ^ (n + 1) - w ^ (n + 1)‖ ≤
        ((n + 1 : ℕ) : ℝ) *
          ((1 / 6 : ℝ) * |u| ^ 3 * M + u ^ 4 / 8) * r ^ n := by
    exact (norm_pow_succ_sub_pow_succ_le_of_norm_le
      (z := charFun μ u) (w := w) (r := r) hr_nonneg hz hw n).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg (n + 1)))
        (pow_nonneg hr_nonneg n))
  have hscale :
      N *
          ((1 / 6 : ℝ) * |u| ^ 3 * M + u ^ 4 / 8) =
        (1 / 6 : ℝ) * M * |t| ^ 3 / Real.sqrt N +
          t ^ 4 / (8 * N) := by
    have hsqrt_sq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN_pos.le
    have hsqrt_cube : Real.sqrt N ^ 3 = N * Real.sqrt N := by
      calc
        Real.sqrt N ^ 3 = Real.sqrt N ^ 2 * Real.sqrt N := by ring
        _ = N * Real.sqrt N := by rw [hsqrt_sq]
    have hsqrt_four : Real.sqrt N ^ 4 = N ^ 2 := by
      calc
        Real.sqrt N ^ 4 = (Real.sqrt N ^ 2) ^ 2 := by ring
        _ = N ^ 2 := by rw [hsqrt_sq]
    have hA :
        N * ((1 / 6 : ℝ) * |u| ^ 3 * M) =
          (1 / 6 : ℝ) * M * |t| ^ 3 / Real.sqrt N := by
      dsimp [u]
      rw [abs_div, abs_of_pos hsqrt_pos, div_pow, hsqrt_cube]
      field_simp [hN_pos.ne', hsqrt_pos.ne']
    have hB :
        N * (u ^ 4 / 8) = t ^ 4 / (8 * N) := by
      dsimp [u]
      rw [div_pow, hsqrt_four]
      field_simp [hN_pos.ne']
    calc
      N * ((1 / 6 : ℝ) * |u| ^ 3 * M + u ^ 4 / 8)
          = N * ((1 / 6 : ℝ) * |u| ^ 3 * M) +
              N * (u ^ 4 / 8) := by ring
      _ = (1 / 6 : ℝ) * M * |t| ^ 3 / Real.sqrt N +
            t ^ 4 / (8 * N) := by rw [hA, hB]
  have hrpow : r ^ n ≤ Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
    dsimp [r, u, N]
    exact durrett_exp_scaled_pow_le_exp_neg_sq_div_four hn t
  have hmain :
      ‖charFun μ u ^ (n + 1) - w ^ (n + 1)‖ ≤
        ((1 / 6 : ℝ) * M * |t| ^ 3 / Real.sqrt N +
          t ^ 4 / (8 * N)) *
          Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
    have hpowN :
        ‖charFun μ u ^ (n + 1) - w ^ (n + 1)‖ ≤
          N * ((1 / 6 : ℝ) * |u| ^ 3 * M + u ^ 4 / 8) * r ^ n := by
      simpa [N] using hpow
    have hcoef_nonneg :
        0 ≤ (1 / 6 : ℝ) * M * |t| ^ 3 / Real.sqrt N +
          t ^ 4 / (8 * N) := by
      have hM : 0 ≤ M := by
        dsimp [M]
        exact integral_abs_cube_nonneg μ
      positivity
    calc
      ‖charFun μ u ^ (n + 1) - w ^ (n + 1)‖
          ≤ N * ((1 / 6 : ℝ) * |u| ^ 3 * M + u ^ 4 / 8) * r ^ n := hpowN
      _ = ((1 / 6 : ℝ) * M * |t| ^ 3 / Real.sqrt N +
            t ^ 4 / (8 * N)) * r ^ n := by rw [hscale]
      _ ≤ ((1 / 6 : ℝ) * M * |t| ^ 3 / Real.sqrt N +
            t ^ 4 / (8 * N)) *
            Real.exp (-(1 / 4 : ℝ) * t ^ 2) :=
              mul_le_mul_of_nonneg_left hrpow hcoef_nonneg
  have hw_pow :
      w ^ (n + 1) = Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ) := by
    dsimp [w, u, N]
    rw [← Complex.exp_nat_mul]
    congr 1
    norm_cast
    rw [div_pow, Real.sq_sqrt hN_pos.le]
    field_simp [hN_pos.ne']
    ring
  have hgauss :
      Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ) =
        charFun standardNormalMeasure t := by
    rw [standardNormal_charFun]
    congr 1
    norm_cast
    ring
  have hmain' := hmain
  rw [hw_pow, hgauss] at hmain'
  simpa [u, N, M, mul_comm, mul_left_comm, mul_assoc] using hmain'

/-- Pointwise Fourier-integrand estimate for Durrett's larger-window
Berry-Esseen bound. -/
lemma fourierDistanceIntegrand_scaled_pow_succ_standardNormal_le_durrettBound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {n : ℕ} (hn : 9 ≤ n) {t : ℝ}
    (ht_window : t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (ht_small :
      (∫ x, |x| ^ 3 ∂μ) *
        |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    ‖charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) -
        charFun standardNormalMeasure t‖ / |t| ≤
      berryEsseenDurrettFourierBound μ n t := by
  by_cases ht0 : t = 0
  · subst t
    simp [berryEsseenDurrettFourierBound]
  · have hpoint :=
      norm_charFun_scaled_pow_succ_sub_standardNormal_charFun_le_durrett
        (μ := μ) h3 hmean hsecond hn ht_window ht_small
    have hdiv :=
      div_le_div_of_nonneg_right hpoint (abs_nonneg t)
    have hquot :
        (((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 3 /
              Real.sqrt ((n + 1 : ℕ) : ℝ) +
            t ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) *
            Real.exp (-(1 / 4 : ℝ) * t ^ 2)) / |t| =
          berryEsseenDurrettFourierBound μ n t := by
      have ht_abs_ne : |t| ≠ 0 := abs_ne_zero.mpr ht0
      have hpow4 : t ^ 4 = |t| ^ 4 := by
        calc
          t ^ 4 = (t ^ 2) ^ 2 := by ring
          _ = (|t| ^ 2) ^ 2 := by rw [sq_abs]
          _ = |t| ^ 4 := by ring
      unfold berryEsseenDurrettFourierBound
      rw [hpow4]
      field_simp [ht_abs_ne]
    exact hdiv.trans_eq hquot

lemma integrableOn_fourierDistanceIntegrand_scaled_pow_succ_standardNormal_durrett
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {n : ℕ} (hn : 9 ≤ n) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (∫ x, |x| ^ 3 ∂μ) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    IntegrableOn
      (fun t : ℝ =>
        ‖charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) -
          charFun standardNormalMeasure t‖ / |t|)
      (Set.Icc (-L) L) := by
  have hBoundInt :
      IntegrableOn (berryEsseenDurrettFourierBound μ n) (Set.Icc (-L) L) :=
    integrableOn_berryEsseenDurrettFourierBound μ n L
  have hscale :
      Measurable fun t : ℝ =>
        t / Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    measurable_id.div_const _
  have hφ :
      Measurable fun t : ℝ =>
        charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
    measurable_charFun.comp hscale
  have hψ :
      Measurable fun t : ℝ => charFun standardNormalMeasure t :=
    measurable_charFun
  have hMeas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          ‖charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) -
            charFun standardNormalMeasure t‖ / |t|)
        (volume.restrict (Set.Icc (-L) L)) :=
    (((hφ.pow_const (n + 1)).sub hψ).norm.div measurable_abs).aestronglyMeasurable
  refine hBoundInt.integrable.mono' hMeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (norm_nonneg _) (abs_nonneg t))]
  exact fourierDistanceIntegrand_scaled_pow_succ_standardNormal_le_durrettBound
    (μ := μ) h3 hmean hsecond hn (hWindow t ht) (hSmall t ht)

/-- Integrated Durrett/Feller Fourier estimate on a window where the larger
central-window and small-frequency assumptions hold pointwise. -/
lemma fourierDistanceIntegralOfFns_scaled_pow_succ_standardNormal_le_durrettBound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {n : ℕ} (hn : 9 ≤ n) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (∫ x, |x| ^ 3 ∂μ) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    fourierDistanceIntegralOfFns
      (fun t : ℝ =>
        charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1))
      (charFun standardNormalMeasure) L ≤
      ∫ t in Set.Icc (-L) L, berryEsseenDurrettFourierBound μ n t := by
  unfold fourierDistanceIntegralOfFns
  have hOrigInt :
      IntegrableOn
        (fun t : ℝ =>
          ‖charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) -
            charFun standardNormalMeasure t‖ / |t|)
        (Set.Icc (-L) L) :=
    integrableOn_fourierDistanceIntegrand_scaled_pow_succ_standardNormal_durrett
      (μ := μ) h3 hmean hsecond hn hWindow hSmall
  have hBoundInt :
      IntegrableOn (berryEsseenDurrettFourierBound μ n) (Set.Icc (-L) L) :=
    integrableOn_berryEsseenDurrettFourierBound μ n L
  exact setIntegral_mono_on hOrigInt hBoundInt measurableSet_Icc
    (fun t ht =>
      fourierDistanceIntegrand_scaled_pow_succ_standardNormal_le_durrettBound
        (μ := μ) h3 hmean hsecond hn (hWindow t ht) (hSmall t ht))

/-- Pointwise Fourier-integrand estimate for the normalized `n+1`-fold sum
against the standard Gaussian, with the removable damped majorant. -/
lemma fourierDistanceIntegrand_scaled_pow_succ_standardNormal_le_dampedBound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (n : ℕ) {t : ℝ}
    (ht_window : t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (ht_small :
      (2 / 3 : ℝ) * (∫ x, |x| ^ 3 ∂μ) *
        |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    ‖charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) -
        charFun standardNormalMeasure t‖ / |t| ≤
      berryEsseenDampedFourierBound μ n t := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  by_cases ht0 : t = 0
  · subst t
    simp [berryEsseenDampedFourierBound]
  · have hpoint :=
      norm_charFun_scaled_pow_succ_sub_standardNormal_charFun_le_exp
        (μ := μ) h3 hmean hsecond n ht_window ht_small
    have hdiv :=
      div_le_div_of_nonneg_right hpoint (abs_nonneg t)
    have hquot :
        (((n + 1 : ℕ) : ℝ) *
            ((1 / 6 : ℝ) * |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ^ 3 *
              ∫ x, |x| ^ 3 ∂μ) *
              (Real.exp
                (-((t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2) / 4)) ^ n +
            t ^ 4 / (8 * ((n + 1 : ℕ) : ℝ)) *
              (Real.exp
                (-(t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))))) ^ n) / |t| =
          berryEsseenDampedFourierBound μ n t := by
      rw [add_div]
      have hfirst :
          (((n + 1 : ℕ) : ℝ) *
            ((1 / 6 : ℝ) * |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ^ 3 *
              ∫ x, |x| ^ 3 ∂μ) *
              (Real.exp
                (-((t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2) / 4)) ^ n) / |t| =
            (1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
              Real.sqrt ((n + 1 : ℕ) : ℝ) *
              (Real.exp
                (-((t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2) / 4)) ^ n := by
        have hsqrt_pos :
            0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by positivity
        have ht_abs_ne : |t| ≠ 0 := abs_ne_zero.mpr ht0
        rw [abs_div, abs_of_pos hsqrt_pos, div_pow]
        field_simp [ht_abs_ne, hsqrt_pos.ne']
        rw [Real.sq_sqrt (Nat.cast_nonneg (n + 1))]
      have hsecond' :
          (t ^ 4 / (8 * ((n + 1 : ℕ) : ℝ)) *
              (Real.exp
                (-(t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))))) ^ n) / |t| =
            |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ)) *
              (Real.exp
                (-(t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))))) ^ n := by
        have ht_abs_ne : |t| ≠ 0 := abs_ne_zero.mpr ht0
        have hpow4 : t ^ 4 = |t| ^ 4 := by
          calc
            t ^ 4 = (t ^ 2) ^ 2 := by ring
            _ = (|t| ^ 2) ^ 2 := by rw [sq_abs]
            _ = |t| ^ 4 := by ring
        rw [hpow4]
        field_simp [ht_abs_ne]
      rw [hfirst, hsecond']
      rfl
    exact hdiv.trans_eq hquot

lemma integrableOn_fourierDistanceIntegrand_scaled_pow_succ_standardNormal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (n : ℕ) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * (∫ x, |x| ^ 3 ∂μ) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    IntegrableOn
      (fun t : ℝ =>
        ‖charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) -
          charFun standardNormalMeasure t‖ / |t|)
      (Set.Icc (-L) L) := by
  have hBoundInt :
      IntegrableOn (berryEsseenDampedFourierBound μ n) (Set.Icc (-L) L) :=
    integrableOn_berryEsseenDampedFourierBound μ n L
  have hscale :
      Measurable fun t : ℝ =>
        t / Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    measurable_id.div_const _
  have hφ :
      Measurable fun t : ℝ =>
        charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
    measurable_charFun.comp hscale
  have hψ :
      Measurable fun t : ℝ => charFun standardNormalMeasure t :=
    measurable_charFun
  have hMeas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          ‖charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) -
            charFun standardNormalMeasure t‖ / |t|)
        (volume.restrict (Set.Icc (-L) L)) :=
    (((hφ.pow_const (n + 1)).sub hψ).norm.div measurable_abs).aestronglyMeasurable
  refine hBoundInt.integrable.mono' hMeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (norm_nonneg _) (abs_nonneg t))]
  exact fourierDistanceIntegrand_scaled_pow_succ_standardNormal_le_dampedBound
    (μ := μ) h3 hmean hsecond n (hWindow t ht) (hSmall t ht)

/-- Integrated Berry-Esseen Fourier estimate on a window where the
central-window and small-frequency assumptions hold pointwise. -/
lemma fourierDistanceIntegralOfFns_scaled_pow_succ_standardNormal_le_dampedBound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (n : ℕ) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * (∫ x, |x| ^ 3 ∂μ) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    fourierDistanceIntegralOfFns
      (fun t : ℝ =>
        charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1))
      (charFun standardNormalMeasure) L ≤
      ∫ t in Set.Icc (-L) L, berryEsseenDampedFourierBound μ n t := by
  unfold fourierDistanceIntegralOfFns
  have hOrigInt :
      IntegrableOn
        (fun t : ℝ =>
          ‖charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) -
            charFun standardNormalMeasure t‖ / |t|)
        (Set.Icc (-L) L) :=
    integrableOn_fourierDistanceIntegrand_scaled_pow_succ_standardNormal
      (μ := μ) h3 hmean hsecond n hWindow hSmall
  have hBoundInt :
      IntegrableOn (berryEsseenDampedFourierBound μ n) (Set.Icc (-L) L) :=
    integrableOn_berryEsseenDampedFourierBound μ n L
  exact setIntegral_mono_on hOrigInt hBoundInt measurableSet_Icc
    (fun t ht =>
      fourierDistanceIntegrand_scaled_pow_succ_standardNormal_le_dampedBound
        (μ := μ) h3 hmean hsecond n (hWindow t ht) (hSmall t ht))

/-- Characteristic-function version of `norm_pow_sub_pow_le_of_norm_le_one`.
Both characteristic functions are bounded by one for probability measures. -/
lemma norm_charFun_pow_sub_pow_le
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (θ : ℝ) (n : ℕ) :
    ‖charFun μ θ ^ n - charFun ν θ ^ n‖ ≤
      (n : ℝ) * ‖charFun μ θ - charFun ν θ‖ :=
  norm_pow_sub_pow_le_of_norm_le_one
    (MeasureTheory.norm_charFun_le_one (μ := μ) θ)
    (MeasureTheory.norm_charFun_le_one (μ := ν) θ) n

/-- Pointwise Fourier-integrand comparison for `n`th powers of two
unit-disk-valued functions. -/
lemma fourierDistanceIntegrand_pow_le
    {φ ψ : ℝ → ℂ} (hφ : ∀ θ, ‖φ θ‖ ≤ 1) (hψ : ∀ θ, ‖ψ θ‖ ≤ 1)
    (θ : ℝ) (n : ℕ) :
    ‖φ θ ^ n - ψ θ ^ n‖ / |θ| ≤
      (n : ℝ) * (‖φ θ - ψ θ‖ / |θ|) := by
  calc
    ‖φ θ ^ n - ψ θ ^ n‖ / |θ|
        ≤ ((n : ℝ) * ‖φ θ - ψ θ‖) / |θ| :=
          div_le_div_of_nonneg_right
            (norm_pow_sub_pow_le_of_norm_le_one (hφ θ) (hψ θ) n)
            (abs_nonneg θ)
    _ = (n : ℝ) * (‖φ θ - ψ θ‖ / |θ|) := by ring

/-- Characteristic-function specialization of the pointwise power comparison. -/
lemma charFun_fourierDistanceIntegrand_pow_le
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (θ : ℝ) (n : ℕ) :
    ‖charFun μ θ ^ n - charFun ν θ ^ n‖ / |θ| ≤
      (n : ℝ) * (‖charFun μ θ - charFun ν θ‖ / |θ|) :=
  fourierDistanceIntegrand_pow_le
    (fun θ => MeasureTheory.norm_charFun_le_one (μ := μ) θ)
    (fun θ => MeasureTheory.norm_charFun_le_one (μ := ν) θ) θ n

end PowerComparison

section ConvolutionSmoothing

/-- The two-sided tail set used in the smoothing estimates. -/
def absTailSet (a : ℝ) : Set ℝ :=
  {y : ℝ | a < |y|}

/-- Difference of two distribution functions at a point. -/
def measureCDFDiff (μ ν : Measure ℝ) (x : ℝ) : ℝ :=
  μ.real (Set.Iic x) - ν.real (Set.Iic x)

/-- `η` is the least global CDF/Kolmogorov error bound for the pair
`(μ,ν)`.  This is a local order-theoretic replacement for talking about
`sup_x |F(x)-G(x)|` directly. -/
def measureCDFErrorIsLeast (μ ν : Measure ℝ) (η : ℝ) : Prop :=
  measureCDFErrorLE μ ν η ∧
    ∀ δ : ℝ, measureCDFErrorLE μ ν δ → η ≤ δ

/-- The set of pointwise absolute CDF errors. -/
def measureCDFErrorSet (μ ν : Measure ℝ) : Set ℝ :=
  Set.range fun x : ℝ => |measureCDFDiff μ ν x|

/-- The Kolmogorov/CDF error as the supremum of pointwise errors. -/
def measureCDFErrorSup (μ ν : Measure ℝ) : ℝ :=
  sSup (measureCDFErrorSet μ ν)

lemma abs_measureCDFDiff_le_one
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : ℝ) :
    |measureCDFDiff μ ν x| ≤ 1 := by
  have hμnonneg : 0 ≤ μ.real (Set.Iic x) := measureReal_nonneg
  have hνnonneg : 0 ≤ ν.real (Set.Iic x) := measureReal_nonneg
  have hμle : μ.real (Set.Iic x) ≤ 1 := by
    simpa using measureReal_mono (μ := μ) (s₁ := Set.Iic x)
      (s₂ := Set.univ) (Set.subset_univ _)
  have hνle : ν.real (Set.Iic x) ≤ 1 := by
    simpa using measureReal_mono (μ := ν) (s₁ := Set.Iic x)
      (s₂ := Set.univ) (Set.subset_univ _)
  rw [measureCDFDiff, abs_sub_le_iff]
  constructor <;> linarith

lemma measureCDFErrorSet_nonempty (μ ν : Measure ℝ) :
    (measureCDFErrorSet μ ν).Nonempty :=
  Set.range_nonempty _

lemma measureCDFErrorSet_bddAbove
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove (measureCDFErrorSet μ ν) := by
  refine ⟨1, ?_⟩
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact abs_measureCDFDiff_le_one μ ν x

lemma measureCDFErrorSup_isLeast
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    measureCDFErrorIsLeast μ ν (measureCDFErrorSup μ ν) := by
  constructor
  · intro x
    change |measureCDFDiff μ ν x| ≤ measureCDFErrorSup μ ν
    exact le_csSup (measureCDFErrorSet_bddAbove μ ν) (Set.mem_range_self x)
  · intro δ hδ
    unfold measureCDFErrorSup
    refine csSup_le (measureCDFErrorSet_nonempty μ ν) ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    simpa [measureCDFDiff, measureCDFErrorLE] using hδ x

lemma abs_measureCDFDiff_le_of_measureCDFErrorLE
    {μ ν : Measure ℝ} {ε x : ℝ}
    (h : measureCDFErrorLE μ ν ε) :
    |measureCDFDiff μ ν x| ≤ ε := by
  simpa [measureCDFDiff, measureCDFErrorLE] using h x

lemma measureCDFDiff_le_of_measureCDFErrorLE
    {μ ν : Measure ℝ} {ε x : ℝ}
    (h : measureCDFErrorLE μ ν ε) :
    measureCDFDiff μ ν x ≤ ε :=
  (le_abs_self _).trans (abs_measureCDFDiff_le_of_measureCDFErrorLE h)

lemma neg_le_measureCDFDiff_of_measureCDFErrorLE
    {μ ν : Measure ℝ} {ε x : ℝ}
    (h : measureCDFErrorLE μ ν ε) :
    -ε ≤ measureCDFDiff μ ν x :=
  (neg_le_neg (abs_measureCDFDiff_le_of_measureCDFErrorLE h)).trans
    (neg_abs_le _)

lemma exists_abs_measureCDFDiff_gt_sub_of_measureCDFErrorIsLeast
    {μ ν : Measure ℝ} {η ε : ℝ}
    (hLeast : measureCDFErrorIsLeast μ ν η) (hε : 0 < ε) :
    ∃ x : ℝ, η - ε < |measureCDFDiff μ ν x| := by
  by_contra hnot
  have hbound : measureCDFErrorLE μ ν (η - ε) := by
    intro x
    exact le_of_not_gt (fun hx => hnot ⟨x, hx⟩)
  have hle : η ≤ η - ε := hLeast.2 (η - ε) hbound
  linarith

lemma exists_measureCDFDiff_pos_or_neg_gt_sub_of_measureCDFErrorIsLeast
    {μ ν : Measure ℝ} {η ε : ℝ}
    (hLeast : measureCDFErrorIsLeast μ ν η) (hε : 0 < ε) :
    ∃ x : ℝ,
      η - ε < measureCDFDiff μ ν x ∨
        η - ε < -measureCDFDiff μ ν x := by
  rcases exists_abs_measureCDFDiff_gt_sub_of_measureCDFErrorIsLeast
      (μ := μ) (ν := ν) hLeast hε with ⟨x, hx⟩
  rw [lt_abs] at hx
  exact ⟨x, hx⟩

lemma absTailSet_eq_Iio_union_Ioi (a : ℝ) :
    absTailSet a = Set.Iio (-a) ∪ Set.Ioi a := by
  ext x
  rw [absTailSet]
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  rw [lt_abs]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl (by linarith)
  · intro h
    rcases h with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl h

lemma absTailSet_eq_compl_Icc (a : ℝ) :
    absTailSet a = (Set.Icc (-a) a)ᶜ := by
  ext x
  rw [absTailSet]
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Icc]
  rw [lt_abs]
  constructor
  · intro h hx
    rcases h with h | h
    · exact not_le_of_gt h hx.2
    · linarith
  · intro h
    by_cases hleft : -a ≤ x
    · exact Or.inl (lt_of_not_ge fun hxa => h ⟨hleft, hxa⟩)
    · exact Or.inr (by linarith [lt_of_not_ge hleft])

lemma measureReal_absTailSet_le_Iio_add_Ioi
    (H : Measure ℝ) (a : ℝ) :
    H.real (absTailSet a) ≤
      H.real (Set.Iio (-a)) + H.real (Set.Ioi a) := by
  rw [absTailSet_eq_Iio_union_Ioi]
  exact measureReal_union_le (μ := H) (Set.Iio (-a)) (Set.Ioi a)

lemma polyaKernelMeasure_real_absTailSet_le_explicit {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    (polyaKernelMeasure L).real (absTailSet a) ≤
      4 / (Real.pi * L * a) := by
  calc
    (polyaKernelMeasure L).real (absTailSet a)
        ≤ (polyaKernelMeasure L).real (Set.Iio (-a)) +
            (polyaKernelMeasure L).real (Set.Ioi a) :=
          measureReal_absTailSet_le_Iio_add_Ioi (polyaKernelMeasure L) a
    _ ≤ 2 / (Real.pi * L * a) + 2 / (Real.pi * L * a) :=
          add_le_add
            (polyaKernelMeasure_real_Iio_neg_le_explicit hL ha)
            (polyaKernelMeasure_real_Ioi_le_explicit hL ha)
    _ = 4 / (Real.pi * L * a) := by
          field_simp [Real.pi_ne_zero, hL.ne', ha.ne']
          ring

lemma polyaKernelMeasure_real_Icc_ge_one_sub_explicit {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    1 - 4 / (Real.pi * L * a) ≤
      (polyaKernelMeasure L).real (Set.Icc (-a) a) := by
  letI : IsProbabilityMeasure (polyaKernelMeasure L) :=
    isProbabilityMeasure_polyaKernelMeasure hL
  have htail :=
    polyaKernelMeasure_real_absTailSet_le_explicit (L := L) (a := a) hL ha
  have hcompl :
      (Set.Icc (-a) a)ᶜ = absTailSet a := by
    rw [absTailSet_eq_compl_Icc]
  have htail_eq :
      (polyaKernelMeasure L).real (absTailSet a) =
        1 - (polyaKernelMeasure L).real (Set.Icc (-a) a) := by
    have h :=
      measureReal_compl (μ := polyaKernelMeasure L)
        (s := Set.Icc (-a) a) measurableSet_Icc
    rw [hcompl] at h
    simpa using h
  linarith

lemma polyaKernelMeasure_real_absTailSet_le_two_mul_integral_tailEnvelope
    {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    (polyaKernelMeasure L).real (absTailSet a) ≤
      2 * (∫ x in Set.Ioi a, polyaTailEnvelope L x) := by
  rw [two_mul_integral_Ioi_polyaTailEnvelope hL ha]
  exact polyaKernelMeasure_real_absTailSet_le_explicit hL ha

/-- A measure-level Lipschitz bound for a real CDF. -/
def measureCDFLipschitz (ν : Measure ℝ) (lam : ℝ) : Prop :=
  ∀ x y : ℝ, x ≤ y →
    ν.real (Set.Iic y) - ν.real (Set.Iic x) ≤ lam * (y - x)

lemma measureCDFDiff_right_lower_of_lipschitz
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] {lam x s : ℝ}
    (hLip : measureCDFLipschitz ν lam) (hs : 0 ≤ s) :
    measureCDFDiff μ ν (x + s) ≥ measureCDFDiff μ ν x - lam * s := by
  have hμ :
      μ.real (Set.Iic x) ≤ μ.real (Set.Iic (x + s)) :=
    measureReal_mono (μ := μ) (Set.Iic_subset_Iic.2 (by linarith))
  have hν :
      ν.real (Set.Iic (x + s)) - ν.real (Set.Iic x) ≤ lam * s := by
    simpa using hLip x (x + s) (by linarith)
  dsimp [measureCDFDiff]
  linarith

lemma measureCDFDiff_left_upper_of_lipschitz
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] {lam x s : ℝ}
    (hLip : measureCDFLipschitz ν lam) (hs : 0 ≤ s) :
    measureCDFDiff μ ν (x - s) ≤ measureCDFDiff μ ν x + lam * s := by
  have hμ :
      μ.real (Set.Iic (x - s)) ≤ μ.real (Set.Iic x) :=
    measureReal_mono (μ := μ) (Set.Iic_subset_Iic.2 (by linarith))
  have hν :
      ν.real (Set.Iic x) - ν.real (Set.Iic (x - s)) ≤ lam * s := by
    simpa using hLip (x - s) x (by linarith)
  dsimp [measureCDFDiff]
  linarith

lemma measureCDFDiff_central_lower_of_pos_witness_ge
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] {lam β x0 y : ℝ}
    (hlam : 0 < lam) (hLip : measureCDFLipschitz ν lam)
    (hWitness : β ≤ measureCDFDiff μ ν x0)
    (hy : y ≤ β / (2 * lam)) :
    β / 2 + lam * y ≤
      measureCDFDiff μ ν (x0 + β / (2 * lam) - y) := by
  let s : ℝ := β / (2 * lam) - y
  have hs : 0 ≤ s := by
    dsimp [s]
    linarith
  have h :=
    measureCDFDiff_right_lower_of_lipschitz
      (μ := μ) (ν := ν) (lam := lam) (x := x0) (s := s) hLip hs
  have harg : x0 + s = x0 + β / (2 * lam) - y := by
    dsimp [s]
    ring
  have hlow :
      measureCDFDiff μ ν (x0 + β / (2 * lam) - y) ≥
        β - lam * s := by
    rw [harg] at h
    linarith
  have halg : β - lam * s = β / 2 + lam * y := by
    dsimp [s]
    field_simp [hlam.ne']
    ring
  linarith

lemma measureCDFDiff_central_lower_of_pos_witness
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] {lam η x0 y : ℝ}
    (hlam : 0 < lam) (hLip : measureCDFLipschitz ν lam)
    (hWitness : measureCDFDiff μ ν x0 = η)
    (hy : y ≤ η / (2 * lam)) :
    η / 2 + lam * y ≤
      measureCDFDiff μ ν (x0 + η / (2 * lam) - y) := by
  let s : ℝ := η / (2 * lam) - y
  have hs : 0 ≤ s := by
    dsimp [s]
    linarith
  have h :=
    measureCDFDiff_right_lower_of_lipschitz
      (μ := μ) (ν := ν) (lam := lam) (x := x0) (s := s) hLip hs
  have harg : x0 + s = x0 + η / (2 * lam) - y := by
    dsimp [s]
    ring
  have hlow :
      measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ≥
        η - lam * s := by
    rwa [harg, hWitness] at h
  have halg : η - lam * s = η / 2 + lam * y := by
    dsimp [s]
    field_simp [hlam.ne']
    ring
  linarith

lemma measureCDFDiff_central_lower_of_pos_approx_witness
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] {lam η ε x0 y : ℝ}
    (hlam : 0 < lam) (hLip : measureCDFLipschitz ν lam)
    (hWitness : η - ε ≤ measureCDFDiff μ ν x0)
    (hy : y ≤ η / (2 * lam)) :
    η / 2 - ε + lam * y ≤
      measureCDFDiff μ ν (x0 + η / (2 * lam) - y) := by
  let s : ℝ := η / (2 * lam) - y
  have hs : 0 ≤ s := by
    dsimp [s]
    linarith
  have h :=
    measureCDFDiff_right_lower_of_lipschitz
      (μ := μ) (ν := ν) (lam := lam) (x := x0) (s := s) hLip hs
  have harg : x0 + s = x0 + η / (2 * lam) - y := by
    dsimp [s]
    ring
  have hlow :
      measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ≥
        η - ε - lam * s := by
    rw [harg] at h
    linarith
  have halg : η - ε - lam * s = η / 2 - ε + lam * y := by
    dsimp [s]
    field_simp [hlam.ne']
    ring
  linarith

lemma measureCDFDiff_central_upper_of_neg_witness_le
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] {lam β x0 y : ℝ}
    (hlam : 0 < lam) (hLip : measureCDFLipschitz ν lam)
    (hWitness : measureCDFDiff μ ν x0 ≤ -β)
    (hy : -(β / (2 * lam)) ≤ y) :
    measureCDFDiff μ ν (x0 - β / (2 * lam) - y) ≤
      -β / 2 + lam * y := by
  let s : ℝ := β / (2 * lam) + y
  have hs : 0 ≤ s := by
    dsimp [s]
    linarith
  have h :=
    measureCDFDiff_left_upper_of_lipschitz
      (μ := μ) (ν := ν) (lam := lam) (x := x0) (s := s) hLip hs
  have harg : x0 - s = x0 - β / (2 * lam) - y := by
    dsimp [s]
    ring
  have hupper :
      measureCDFDiff μ ν (x0 - β / (2 * lam) - y) ≤
        -β + lam * s := by
    rw [harg] at h
    linarith
  have halg : -β + lam * s = -β / 2 + lam * y := by
    dsimp [s]
    field_simp [hlam.ne']
    ring
  linarith

lemma measureCDFDiff_central_upper_of_neg_approx_witness
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] {lam η ε x0 y : ℝ}
    (hlam : 0 < lam) (hLip : measureCDFLipschitz ν lam)
    (hWitness : measureCDFDiff μ ν x0 ≤ -(η - ε))
    (hy : -(η / (2 * lam)) ≤ y) :
    measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ≤
      -η / 2 + ε + lam * y := by
  let s : ℝ := η / (2 * lam) + y
  have hs : 0 ≤ s := by
    dsimp [s]
    linarith
  have h :=
    measureCDFDiff_left_upper_of_lipschitz
      (μ := μ) (ν := ν) (lam := lam) (x := x0) (s := s) hLip hs
  have harg : x0 - s = x0 - η / (2 * lam) - y := by
    dsimp [s]
    ring
  have hupper :
      measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ≤
        -(η - ε) + lam * s := by
    rw [harg] at h
    linarith
  have halg : -(η - ε) + lam * s = -η / 2 + ε + lam * y := by
    dsimp [s]
    field_simp [hlam.ne']
    ring
  linarith

lemma measureCDFDiff_central_upper_of_neg_witness
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] {lam η x0 y : ℝ}
    (hlam : 0 < lam) (hLip : measureCDFLipschitz ν lam)
    (hWitness : measureCDFDiff μ ν x0 = -η)
    (hy : -(η / (2 * lam)) ≤ y) :
    measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ≤
      -η / 2 + lam * y := by
  let s : ℝ := η / (2 * lam) + y
  have hs : 0 ≤ s := by
    dsimp [s]
    linarith
  have h :=
    measureCDFDiff_left_upper_of_lipschitz
      (μ := μ) (ν := ν) (lam := lam) (x := x0) (s := s) hLip hs
  have harg : x0 - s = x0 - η / (2 * lam) - y := by
    dsimp [s]
    ring
  have hupper :
      measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ≤
        -η + lam * s := by
    rwa [harg, hWitness] at h
  have halg : -η + lam * s = -η / 2 + lam * y := by
    dsimp [s]
    field_simp [hlam.ne']
    ring
  linarith

lemma standardNormalConstant_le_one : standardNormalConstant ≤ 1 := by
  dsimp [standardNormalConstant]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.two_le_pi]
  simpa [one_div] using inv_le_one_of_one_le₀ hsqrt

/-- Durrett's numerical bound on the maximum standard-normal density,
`(2π)⁻¹/² < 0.4`, recorded as a non-strict inequality. -/
lemma standardNormalConstant_le_two_fifths :
    standardNormalConstant ≤ (2 / 5 : ℝ) := by
  dsimp [standardNormalConstant]
  have hsqrt : (5 / 2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num : 0 ≤ (5 / 2 : ℝ)) (by positivity : 0 ≤ 2 * Real.pi)]
    nlinarith [Real.pi_gt_d2]
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have htarget_pos : 0 < (2 / 5 : ℝ) := by norm_num
  exact (inv_le_comm₀ hsqrt_pos htarget_pos).mpr (by
    simpa using hsqrt)

lemma standardNormalDensity_le_one (x : ℝ) :
    standardNormalDensity x ≤ 1 := by
  have hexp : Real.exp (-(x ^ 2) / 2) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hconst : standardNormalConstant ≤ 1 := standardNormalConstant_le_one
  calc
    standardNormalDensity x
        = standardNormalConstant * Real.exp (-(x ^ 2) / 2) := by
          simp [standardNormalDensity_eq, standardNormalConstant]
    _ ≤ standardNormalConstant * 1 :=
          mul_le_mul_of_nonneg_left hexp standardNormalConstant_nonneg
    _ ≤ 1 := by nlinarith

lemma standardNormalDensity_le_two_fifths (x : ℝ) :
    standardNormalDensity x ≤ (2 / 5 : ℝ) := by
  have hexp : Real.exp (-(x ^ 2) / 2) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hconst : standardNormalConstant ≤ (2 / 5 : ℝ) :=
    standardNormalConstant_le_two_fifths
  calc
    standardNormalDensity x
        = standardNormalConstant * Real.exp (-(x ^ 2) / 2) := by
          simp [standardNormalDensity_eq, standardNormalConstant]
    _ ≤ standardNormalConstant * 1 :=
          mul_le_mul_of_nonneg_left hexp standardNormalConstant_nonneg
    _ ≤ (2 / 5 : ℝ) := by nlinarith

lemma standardNormalMeasure_le_volume :
    standardNormalMeasure ≤ volume := by
  rw [standardNormalMeasure,
    ProbabilityTheory.gaussianReal_of_var_ne_zero 0
      (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have hDensity :
      ProbabilityTheory.gaussianPDF 0 1 ≤ᵐ[volume] (fun _ : ℝ => (1 : ℝ≥0∞)) := by
    exact Eventually.of_forall fun x => by
      simpa [ProbabilityTheory.gaussianPDF, standardNormalDensity, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (standardNormalDensity_le_one x)
  simpa using withDensity_mono hDensity

lemma measureCDFLipschitz_one_of_le_volume
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≤ volume) :
    measureCDFLipschitz ν 1 := by
  intro x y hxy
  have hsub : Set.Iic x ⊆ Set.Iic y := Set.Iic_subset_Iic.mpr hxy
  have hdiff :
      ν.real (Set.Iic y) - ν.real (Set.Iic x) =
        ν.real (Set.Ioc x y) := by
    have h := measureReal_diff (μ := ν) hsub measurableSet_Iic
    rw [← h]
    congr 1
    ext z
    simp only [Set.mem_diff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · intro hz
      exact ⟨lt_of_not_ge hz.2, hz.1⟩
    · intro hz
      exact ⟨hz.2, not_le_of_gt hz.1⟩
  calc
    ν.real (Set.Iic y) - ν.real (Set.Iic x)
        = ν.real (Set.Ioc x y) := hdiff
    _ ≤ volume.real (Set.Ioc x y) := by
          have hvol_ne_top : volume (Set.Ioc x y) ≠ ∞ := by
            rw [Real.volume_Ioc]
            exact ENNReal.ofReal_ne_top
          exact ENNReal.toReal_mono hvol_ne_top (hν (Set.Ioc x y))
    _ = 1 * (y - x) := by
          rw [Real.volume_real_Ioc_of_le hxy]
          ring

lemma standardNormal_measureCDFLipschitz :
    measureCDFLipschitz standardNormalMeasure 1 :=
  measureCDFLipschitz_one_of_le_volume standardNormalMeasure standardNormalMeasure_le_volume

lemma standardNormalMeasure_real_Ioc_le_two_fifths {x y : ℝ} (hxy : x ≤ y) :
    standardNormalMeasure.real (Set.Ioc x y) ≤ (2 / 5 : ℝ) * (y - x) := by
  have hμ :
      standardNormalMeasure (Set.Ioc x y) =
        ENNReal.ofReal (∫ z in Set.Ioc x y, standardNormalDensity z) := by
    simpa [standardNormalMeasure, standardNormalDensity] using
      ProbabilityTheory.gaussianReal_apply_eq_integral
        (μ := 0) (v := (1 : ℝ≥0))
        (by norm_num : (1 : ℝ≥0) ≠ 0) (Set.Ioc x y)
  have hint_nonneg :
      0 ≤ ∫ z in Set.Ioc x y, standardNormalDensity z :=
    integral_nonneg fun z => standardNormalDensity_nonneg z
  have hreal :
      standardNormalMeasure.real (Set.Ioc x y) =
        ∫ z in Set.Ioc x y, standardNormalDensity z := by
    rw [measureReal_def, hμ, ENNReal.toReal_ofReal hint_nonneg]
  have hstd_int :
      IntegrableOn standardNormalDensity (Set.Ioc x y) volume := by
    exact (by
      simpa [standardNormalDensity] using
        (ProbabilityTheory.integrable_gaussianPDFReal 0 (1 : ℝ≥0)).integrableOn)
  have hIoc_ne_top : volume (Set.Ioc x y) ≠ ∞ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hconst_int :
      IntegrableOn (fun _ : ℝ => (2 / 5 : ℝ)) (Set.Ioc x y) volume :=
    integrableOn_const hIoc_ne_top
  have hbound :
      ∫ z in Set.Ioc x y, standardNormalDensity z ≤
        ∫ z in Set.Ioc x y, (2 / 5 : ℝ) := by
    exact setIntegral_mono_on hstd_int hconst_int measurableSet_Ioc
      (fun z _hz => standardNormalDensity_le_two_fifths z)
  rw [hreal]
  calc
    ∫ z in Set.Ioc x y, standardNormalDensity z
        ≤ ∫ z in Set.Ioc x y, (2 / 5 : ℝ) := hbound
    _ = (2 / 5 : ℝ) * (y - x) := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hxy]
          ring

lemma standardNormal_measureCDFLipschitz_two_fifths :
    measureCDFLipschitz standardNormalMeasure (2 / 5) := by
  intro x y hxy
  have hsub : Set.Iic x ⊆ Set.Iic y := Set.Iic_subset_Iic.mpr hxy
  have hdiff :
      standardNormalMeasure.real (Set.Iic y) -
          standardNormalMeasure.real (Set.Iic x) =
        standardNormalMeasure.real (Set.Ioc x y) := by
    have h := measureReal_diff (μ := standardNormalMeasure) hsub measurableSet_Iic
    rw [← h]
    congr 1
    ext z
    simp only [Set.mem_diff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · intro hz
      exact ⟨lt_of_not_ge hz.2, hz.1⟩
    · intro hz
      exact ⟨hz.2, not_le_of_gt hz.1⟩
  rw [hdiff]
  exact standardNormalMeasure_real_Ioc_le_two_fifths hxy

/-- Exact CDF formula for an additive convolution, oriented by first sampling
`x ~ μ` and then measuring the right law below `t - x`. -/
lemma conv_cdf_eq_integral_right_cdf
    (μ H : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure H]
    (t : ℝ) :
    (μ ∗ H).real (Set.Iic t) =
      ∫ x, H.real (Set.Iic (t - x)) ∂μ := by
  let f : ℝ → ℝ := fun z => (Set.Iic t).indicator (fun _ : ℝ => (1 : ℝ)) z
  have hf_int : Integrable f (μ ∗ H) := by
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hconv :
      ∫ z, f z ∂(μ ∗ H) =
        ∫ x, ∫ y, f (x + y) ∂H ∂μ :=
    integral_conv (μ := μ) (ν := H) (f := f) hf_int
  rw [← integral_indicator_one (μ := μ ∗ H) (s := Set.Iic t) measurableSet_Iic]
  change ∫ z, f z ∂(μ ∗ H) = ∫ x, H.real (Set.Iic (t - x)) ∂μ
  rw [hconv]
  refine integral_congr_ae ?_
  exact Eventually.of_forall fun x => by
    have hfun :
        (fun y : ℝ => f (x + y)) =
          fun y : ℝ => (Set.Iic (t - x)).indicator (fun _ : ℝ => (1 : ℝ)) y := by
      funext y
      by_cases hy : y ≤ t - x
      · have hxy : x + y ≤ t := by linarith
        simp [f, hy, hxy]
      · have hxy : ¬ x + y ≤ t := by linarith
        simp [f, hy, hxy]
    change (∫ y, f (x + y) ∂H) = H.real (Set.Iic (t - x))
    rw [hfun]
    simp

/-- Exact CDF formula for an additive convolution, oriented by first sampling
`y ~ H` and then measuring the left law below `t - y`. -/
lemma conv_cdf_eq_integral_left_cdf
    (μ H : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure H]
    (t : ℝ) :
    (μ ∗ H).real (Set.Iic t) =
      ∫ y, μ.real (Set.Iic (t - y)) ∂H := by
  rw [Measure.conv_comm μ H]
  exact conv_cdf_eq_integral_right_cdf H μ t

/-- The exact convolution-CDF formula specialized to `polyaSmooth`, in the
orientation used by distribution-function smoothing arguments. -/
lemma polyaSmooth_cdf_eq_integral_left_cdf
    (μ H : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure H]
    (t : ℝ) :
    (polyaSmooth μ H).real (Set.Iic t) =
      ∫ y, μ.real (Set.Iic (t - y)) ∂H := by
  simpa [polyaSmooth] using conv_cdf_eq_integral_left_cdf μ H t

lemma measurable_measureReal_Iic_sub
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    Measurable (fun y : ℝ => μ.real (Set.Iic (t - y))) := by
  have hmeas : Measurable (fun y : ℝ => ProbabilityTheory.cdf μ (t - y)) :=
    (ProbabilityTheory.monotone_cdf μ).measurable.comp
      (measurable_const.sub measurable_id)
  convert hmeas using 1
  funext y
  rw [ProbabilityTheory.cdf_eq_real]

lemma integrable_measureReal_Iic_sub
    (μ H : Measure ℝ) [IsProbabilityMeasure μ] [IsFiniteMeasure H] (t : ℝ) :
    Integrable (fun y : ℝ => μ.real (Set.Iic (t - y))) H := by
  refine Integrable.of_bound
    (measurable_measureReal_Iic_sub μ t).aestronglyMeasurable 1 ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  simpa using measureReal_mono (μ := μ) (s₁ := Set.Iic (t - y))
    (s₂ := Set.univ) (Set.subset_univ _)

/-- The smoothed CDF difference is the convolution of the original CDF
difference with the smoothing law.  This is the measure-level `Δ_L = Δ * H_L`
identity used in Durrett's proof of Esseen's smoothing lemma. -/
lemma polyaSmooth_cdf_sub_eq_integral_cdf_sub
    (μ ν H : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure H] (t : ℝ) :
    (polyaSmooth μ H).real (Set.Iic t) -
        (polyaSmooth ν H).real (Set.Iic t) =
      ∫ y, (μ.real (Set.Iic (t - y)) -
        ν.real (Set.Iic (t - y))) ∂H := by
  rw [polyaSmooth_cdf_eq_integral_left_cdf μ H t,
    polyaSmooth_cdf_eq_integral_left_cdf ν H t]
  rw [integral_sub
    (integrable_measureReal_Iic_sub μ H t)
    (integrable_measureReal_Iic_sub ν H t)]

lemma measureCDFDiff_polyaSmooth_eq_integral
    (μ ν H : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure H] (t : ℝ) :
    measureCDFDiff (polyaSmooth μ H) (polyaSmooth ν H) t =
      ∫ y, measureCDFDiff μ ν (t - y) ∂H := by
  simpa [measureCDFDiff] using
    polyaSmooth_cdf_sub_eq_integral_cdf_sub μ ν H t

lemma integrable_measureCDFDiff_sub
    (μ ν H : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsFiniteMeasure H] (t : ℝ) :
    Integrable (fun y : ℝ => measureCDFDiff μ ν (t - y)) H := by
  simpa [measureCDFDiff] using
    (integrable_measureReal_Iic_sub μ H t).sub
      (integrable_measureReal_Iic_sub ν H t)

lemma integrableOn_affine_Icc_of_finite
    (H : Measure ℝ) [IsFiniteMeasure H] {a c m : ℝ} :
    IntegrableOn (fun x : ℝ => c + m * x) (Set.Icc (-a) a) H := by
  have hconst : IntegrableOn (fun _ : ℝ => c) (Set.Icc (-a) a) H :=
    integrableOn_const
  have hid : IntegrableOn (fun x : ℝ => m * x) (Set.Icc (-a) a) H := by
    have hidx : IntegrableOn (fun x : ℝ => x) (Set.Icc (-a) a) H :=
      integrableOn_id_Icc_of_finite H
    rw [IntegrableOn] at hidx ⊢
    exact hidx.const_mul m
  simpa [Pi.add_def] using hconst.add hid

/-- Exact CDF formula for smoothing a probability law with the concrete Polya
density, oriented by first sampling `x ~ μ` and then integrating the Polya
kernel below `t - x`.  This is the density-level CDF bridge used by the
Durrett/Feller smoothing proof before applying Fourier inversion. -/
lemma polyaSmooth_polyaKernelMeasure_cdf_eq_integral_kernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {L t : ℝ} (hL : 0 < L) :
    (polyaSmooth μ (polyaKernelMeasure L)).real (Set.Iic t) =
      ∫ x, (∫ y in Set.Iic (t - x), polyaKernel L y) ∂μ := by
  letI : IsProbabilityMeasure (polyaKernelMeasure L) :=
    isProbabilityMeasure_polyaKernelMeasure hL
  calc
    (polyaSmooth μ (polyaKernelMeasure L)).real (Set.Iic t)
        = ∫ x, (polyaKernelMeasure L).real (Set.Iic (t - x)) ∂μ := by
          simpa [polyaSmooth] using
            conv_cdf_eq_integral_right_cdf μ (polyaKernelMeasure L) t
    _ = ∫ x, (∫ y in Set.Iic (t - x), polyaKernel L y) ∂μ := by
          refine integral_congr_ae ?_
          exact Eventually.of_forall fun x =>
            polyaKernelMeasure_real_Iic_eq_integral (L := L) (t := t - x) hL

/-- The finite-window sine primitive that represents the centered Polya CDF
at the shifted point `t - x`. -/
def polyaSineWindow (L t x : ℝ) : ℝ :=
  ∫ θ in -L..L, triangleMultiplier L θ * sineDivKernel (t - x) θ

lemma isFiniteMeasure_volume_restrict_uIoc (a b : ℝ) :
    IsFiniteMeasure (volume.restrict (Set.uIoc a b)) := by
  rw [MeasureTheory.isFiniteMeasure_restrict]
  simp [Real.volume_uIoc]

lemma polyaKernelMeasure_real_Iic_eq_half_add_polyaSineWindow
    {L t x : ℝ} (hL : 0 < L) :
    (polyaKernelMeasure L).real (Set.Iic (t - x)) =
      1 / 2 + (1 / (2 * Real.pi)) * polyaSineWindow L t x := by
  simpa [polyaSineWindow] using
    polyaKernelMeasure_real_Iic_eq_half_add_normalized_sineDivKernel
      (L := L) (x := t - x) hL

lemma integrable_polyaSineWindow_scaled
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {L t : ℝ} (hL : 0 < L) :
    Integrable
      (fun x : ℝ => (1 / (2 * Real.pi)) * polyaSineWindow L t x) μ := by
  letI : IsProbabilityMeasure (polyaKernelMeasure L) :=
    isProbabilityMeasure_polyaKernelMeasure hL
  have hcdf :
      Integrable (fun x : ℝ =>
        (polyaKernelMeasure L).real (Set.Iic (t - x))) μ :=
    integrable_measureReal_Iic_sub (polyaKernelMeasure L) μ t
  have hsum :
      Integrable
        (fun x : ℝ =>
          1 / 2 + (1 / (2 * Real.pi)) * polyaSineWindow L t x) μ :=
    hcdf.congr <| Eventually.of_forall fun x =>
      polyaKernelMeasure_real_Iic_eq_half_add_polyaSineWindow
        (L := L) (t := t) (x := x) hL
  have hconst : Integrable (fun _ : ℝ => (1 / 2 : ℝ)) μ := integrable_const _
  have hdiff := hsum.sub hconst
  refine hdiff.congr <| Eventually.of_forall ?_
  intro x
  simp [Pi.sub_apply]

lemma integrable_polyaSineWindow_product
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {L t : ℝ}
    (hL : 0 < L) (hμ1 : Integrable (fun x : ℝ => x) μ) :
    Integrable
      (fun p : ℝ × ℝ =>
        triangleMultiplier L p.1 * sineDivKernel (t - p.2) p.1)
      ((volume.restrict (Set.uIoc (-L) L)).prod μ) := by
  let θWindow : Measure ℝ := volume.restrict (Set.uIoc (-L) L)
  haveI : IsFiniteMeasure θWindow :=
    isFiniteMeasure_volume_restrict_uIoc (-L) L
  have hAbsX : Integrable (fun x : ℝ => |x|) μ := by
    simpa [Real.norm_eq_abs] using hμ1.norm
  have hBoundInt :
      Integrable (fun p : ℝ × ℝ => |t| + |p.2|)
        (θWindow.prod μ) := by
    exact (integrable_const _).add (hAbsX.comp_snd θWindow)
  have hSineCont :
      Continuous (fun p : ℝ × ℝ => sineDivKernel (t - p.2) p.1) := by
    exact continuous_sineDivKernel.comp
      ((continuous_const.sub continuous_snd).prodMk continuous_fst)
  have hMeas :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          triangleMultiplier L p.1 * sineDivKernel (t - p.2) p.1)
        (θWindow.prod μ) := by
    exact (((continuous_triangleMultiplier L).comp continuous_fst).mul
      hSineCont).aestronglyMeasurable
  refine hBoundInt.mono' hMeas (Eventually.of_forall ?_)
  intro p
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (triangleMultiplier_nonneg L p.1)]
  exact (mul_le_mul_of_nonneg_right
      (triangleMultiplier_le_one hL)
      (abs_nonneg (sineDivKernel (t - p.2) p.1))).trans
    (by simpa using abs_sineDivKernel_sub_le t p.2 p.1)

lemma integral_polyaSineWindow_eq_interval_integral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {L t : ℝ}
    (hL : 0 < L) (hμ1 : Integrable (fun x : ℝ => x) μ) :
    ∫ x, polyaSineWindow L t x ∂μ =
      ∫ θ in -L..L,
        ∫ x, triangleMultiplier L θ * sineDivKernel (t - x) θ ∂μ := by
  have hprod :=
    integrable_polyaSineWindow_product
      (μ := μ) (L := L) (t := t) hL hμ1
  simpa [polyaSineWindow, Function.uncurry] using
    (intervalIntegral_integral_swap
      (μ := μ) (a := -L) (b := L)
      (f := fun θ x =>
        triangleMultiplier L θ * sineDivKernel (t - x) θ)
      hprod).symm

lemma neg_div_I_mul_real_re (z : ℂ) {θ : ℝ} (hθ : θ ≠ 0) :
    (-(z / (Complex.I * (θ : ℂ)))).re = -z.im / θ := by
  rw [Complex.neg_re, Complex.div_re]
  simp [Complex.normSq]
  field_simp [hθ]

lemma charFun_shift_mul_eq_integral_exp_sub
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t θ : ℝ) :
    Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I) * charFun μ θ =
      ∫ x, Complex.exp (((θ * (x - t) : ℝ) : ℂ) * Complex.I) ∂μ := by
  calc
    Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I) * charFun μ θ
        = Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I) *
            ∫ x, Complex.exp ((θ : ℂ) * (x : ℂ) * Complex.I) ∂μ := by
            rw [charFun_apply_real]
    _ = ∫ x,
          Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I) *
            Complex.exp ((θ : ℂ) * (x : ℂ) * Complex.I) ∂μ := by
          exact (integral_const_mul
            (μ := μ)
            (r := Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I))
            (f := fun x : ℝ => Complex.exp ((θ : ℂ) * (x : ℂ) * Complex.I))).symm
    _ = ∫ x, Complex.exp (((θ * (x - t) : ℝ) : ℂ) * Complex.I) ∂μ := by
          refine integral_congr_ae ?_
          exact Eventually.of_forall fun x => by
            change
              Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I) *
                  Complex.exp ((θ : ℂ) * (x : ℂ) * Complex.I) =
                Complex.exp (((θ * (x - t) : ℝ) : ℂ) * Complex.I)
            rw [← Complex.exp_add]
            congr 1
            rw [show θ * (x - t) = -(θ * t) + θ * x by ring]
            rw [Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_mul,
              Complex.ofReal_mul]
            ring

lemma integral_sineDivKernel_eq_re_inversionKernelIntegrand_charFun
    (μ : Measure ℝ) [IsFiniteMeasure μ] {t θ : ℝ} (hθ : θ ≠ 0) :
    ∫ x, sineDivKernel (t - x) θ ∂μ =
      (inversionKernelIntegrand (charFun μ) (fun _ : ℝ => 0) t θ).re := by
  let z : ℂ :=
    Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I) * charFun μ θ
  have hShift :
      z =
        ∫ x, Complex.exp (((θ * (x - t) : ℝ) : ℂ) * Complex.I) ∂μ := by
    dsimp [z]
    exact charFun_shift_mul_eq_integral_exp_sub μ t θ
  have hShiftInt :
      Integrable
        (fun x : ℝ =>
          Complex.exp (((θ * (x - t) : ℝ) : ℂ) * Complex.I)) μ := by
    refine Integrable.of_bound
      (by fun_prop : AEStronglyMeasurable
        (fun x : ℝ =>
          Complex.exp (((θ * (x - t) : ℝ) : ℂ) * Complex.I)) μ) 1 ?_
    filter_upwards with x
    rw [Complex.norm_exp_ofReal_mul_I]
  have hZim :
      z.im = ∫ x, Real.sin (θ * (x - t)) ∂μ := by
    calc
      z.im
          = (∫ x, Complex.exp (((θ * (x - t) : ℝ) : ℂ) * Complex.I) ∂μ).im := by
              rw [hShift]
      _ = ∫ x,
            RCLike.im (Complex.exp (((θ * (x - t) : ℝ) : ℂ) * Complex.I)) ∂μ := by
            exact (integral_im hShiftInt).symm
      _ = ∫ x, Real.sin (θ * (x - t)) ∂μ := by
            refine integral_congr_ae ?_
            exact Eventually.of_forall fun x => by
              change
                (Complex.exp (((θ * (x - t) : ℝ) : ℂ) * Complex.I)).im =
                  Real.sin (θ * (x - t))
              rw [Complex.exp_ofReal_mul_I_im]
  have hleft :
      ∫ x, sineDivKernel (t - x) θ ∂μ =
        - (∫ x, Real.sin (θ * (x - t)) ∂μ) / θ := by
    calc
      ∫ x, sineDivKernel (t - x) θ ∂μ
          = ∫ x, Real.sin (θ * (t - x)) / θ ∂μ := by
              refine integral_congr_ae ?_
              exact Eventually.of_forall fun x => sineDivKernel_of_ne hθ
      _ = (∫ x, Real.sin (θ * (t - x)) ∂μ) / θ := by
            rw [integral_div]
      _ = (∫ x, -Real.sin (θ * (x - t)) ∂μ) / θ := by
            congr 1
            refine integral_congr_ae ?_
            exact Eventually.of_forall fun x => by
              change Real.sin (θ * (t - x)) = -Real.sin (θ * (x - t))
              rw [show θ * (t - x) = -(θ * (x - t)) by ring, Real.sin_neg]
      _ = - (∫ x, Real.sin (θ * (x - t)) ∂μ) / θ := by
            rw [integral_neg]
  rw [inversionKernelIntegrand, sub_zero]
  have hden :
      Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I) *
          (charFun μ θ / (Complex.I * (θ : ℂ))) =
        z / (Complex.I * (θ : ℂ)) := by
    dsimp [z]
    ring
  rw [hden]
  rw [hleft, neg_div_I_mul_real_re z hθ, hZim]

lemma re_inversionKernelIntegrand_sub_zero
    (φ ψ : ℝ → ℂ) (t θ : ℝ) :
    (inversionKernelIntegrand φ ψ t θ).re =
      (inversionKernelIntegrand φ (fun _ : ℝ => 0) t θ).re -
        (inversionKernelIntegrand ψ (fun _ : ℝ => 0) t θ).re := by
  have h :
      inversionKernelIntegrand φ ψ t θ =
        inversionKernelIntegrand φ (fun _ : ℝ => 0) t θ -
          inversionKernelIntegrand ψ (fun _ : ℝ => 0) t θ := by
    unfold inversionKernelIntegrand
    ring
  rw [h, Complex.sub_re]

lemma re_inversionKernelIntegrand_mul_real
    (φ ψ : ℝ → ℂ) (c t θ : ℝ) :
    (-(Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I) *
        (((φ θ - ψ θ) * (c : ℂ)) / (Complex.I * (θ : ℂ))))).re =
      c * (inversionKernelIntegrand φ ψ t θ).re := by
  unfold inversionKernelIntegrand
  have h :
      -(Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I) *
          (((φ θ - ψ θ) * (c : ℂ)) / (Complex.I * (θ : ℂ)))) =
        (c : ℂ) *
          (-(Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I) *
            ((φ θ - ψ θ) / (Complex.I * (θ : ℂ))))) := by
    ring
  rw [h]
  simp [Complex.mul_re]
  ring

lemma re_inversionKernelIntegrand_polyaSmooth_eq_mul
    (μ ν H : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {L t θ : ℝ} (hH : IsPolyaKernelMeasure H L) :
    (inversionKernelIntegrand
        (charFun (polyaSmooth μ H)) (charFun (polyaSmooth ν H)) t θ).re =
      triangleMultiplier L θ *
        (inversionKernelIntegrand (charFun μ) (charFun ν) t θ).re := by
  unfold inversionKernelIntegrand
  rw [polyaSmoothed_charFun_sub_eq μ ν H hH]
  exact re_inversionKernelIntegrand_mul_real
    (charFun μ) (charFun ν) (triangleMultiplier L θ) t θ

lemma integral_triangle_sineDivKernel_sub_eq_re_inversionKernelIntegrand_polyaSmooth
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L t θ : ℝ} (hL : 0 < L) (hθ : θ ≠ 0) :
    (∫ x, triangleMultiplier L θ * sineDivKernel (t - x) θ ∂μ) -
        (∫ x, triangleMultiplier L θ * sineDivKernel (t - x) θ ∂ν) =
      (inversionKernelIntegrand
        (charFun (polyaSmooth μ (polyaKernelMeasure L)))
        (charFun (polyaSmooth ν (polyaKernelMeasure L))) t θ).re := by
  let H : Measure ℝ := polyaKernelMeasure L
  letI : IsProbabilityMeasure H := by
    dsimp [H]
    exact isProbabilityMeasure_polyaKernelMeasure hL
  have hH : IsPolyaKernelMeasure H L := by
    dsimp [H]
    exact isPolyaKernelMeasure_polyaKernelMeasure hL
  have hμ :=
    integral_sineDivKernel_eq_re_inversionKernelIntegrand_charFun
      (μ := μ) (t := t) hθ
  have hν :=
    integral_sineDivKernel_eq_re_inversionKernelIntegrand_charFun
      (μ := ν) (t := t) hθ
  calc
    (∫ x, triangleMultiplier L θ * sineDivKernel (t - x) θ ∂μ) -
        (∫ x, triangleMultiplier L θ * sineDivKernel (t - x) θ ∂ν)
        = triangleMultiplier L θ *
            (∫ x, sineDivKernel (t - x) θ ∂μ) -
          triangleMultiplier L θ *
            (∫ x, sineDivKernel (t - x) θ ∂ν) := by
            rw [integral_const_mul, integral_const_mul]
    _ = triangleMultiplier L θ *
            (inversionKernelIntegrand (charFun μ) (fun _ : ℝ => 0) t θ).re -
          triangleMultiplier L θ *
            (inversionKernelIntegrand (charFun ν) (fun _ : ℝ => 0) t θ).re := by
            rw [hμ, hν]
    _ = triangleMultiplier L θ *
          (inversionKernelIntegrand (charFun μ) (charFun ν) t θ).re := by
            rw [re_inversionKernelIntegrand_sub_zero
              (charFun μ) (charFun ν) t θ]
            ring
    _ = (inversionKernelIntegrand
          (charFun (polyaSmooth μ (polyaKernelMeasure L)))
          (charFun (polyaSmooth ν (polyaKernelMeasure L))) t θ).re := by
            rw [← re_inversionKernelIntegrand_polyaSmooth_eq_mul
              (μ := μ) (ν := ν) (H := H) (L := L) (t := t) (θ := θ) hH]

/-- One-law Polya smoothing CDF formula written directly with the truncated
sine primitive.  This is the first half of the Feller/Esseen inversion bridge:
the constant `1/2` is still visible and will cancel between two laws. -/
lemma polyaSmooth_polyaKernelMeasure_cdf_eq_half_add_sineWindow
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {L t : ℝ} (hL : 0 < L) :
    (polyaSmooth μ (polyaKernelMeasure L)).real (Set.Iic t) =
      1 / 2 +
        (1 / (2 * Real.pi)) *
          ∫ x, polyaSineWindow L t x ∂μ := by
  letI : IsProbabilityMeasure (polyaKernelMeasure L) :=
    isProbabilityMeasure_polyaKernelMeasure hL
  have hscaled :
      Integrable
        (fun x : ℝ => (1 / (2 * Real.pi)) * polyaSineWindow L t x) μ :=
    integrable_polyaSineWindow_scaled μ hL
  have hconst : Integrable (fun _ : ℝ => (1 / 2 : ℝ)) μ := integrable_const _
  calc
    (polyaSmooth μ (polyaKernelMeasure L)).real (Set.Iic t)
        = ∫ x, (polyaKernelMeasure L).real (Set.Iic (t - x)) ∂μ := by
          simpa [polyaSmooth] using
            conv_cdf_eq_integral_right_cdf μ (polyaKernelMeasure L) t
    _ = ∫ x,
          (1 / 2 + (1 / (2 * Real.pi)) * polyaSineWindow L t x) ∂μ := by
          refine integral_congr_ae ?_
          exact Eventually.of_forall fun x =>
            polyaKernelMeasure_real_Iic_eq_half_add_polyaSineWindow
              (L := L) (t := t) (x := x) hL
    _ = ∫ x, (1 / 2 : ℝ) ∂μ +
          ∫ x, (1 / (2 * Real.pi)) * polyaSineWindow L t x ∂μ := by
          rw [integral_add hconst hscaled]
    _ = 1 / 2 +
          (1 / (2 * Real.pi)) *
            ∫ x, polyaSineWindow L t x ∂μ := by
          rw [integral_const, integral_const_mul]
          simp [measureReal_def]

/-- Two-law Polya-smoothed CDF difference after the `1/2` constants cancel. -/
lemma measureCDFDiff_polyaSmooth_polyaKernelMeasure_eq_sineWindow
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L t : ℝ} (hL : 0 < L) :
    measureCDFDiff
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) t =
      (1 / (2 * Real.pi)) *
        (∫ x, polyaSineWindow L t x ∂μ -
          ∫ x, polyaSineWindow L t x ∂ν) := by
  rw [measureCDFDiff,
    polyaSmooth_polyaKernelMeasure_cdf_eq_half_add_sineWindow
      (μ := μ) (L := L) (t := t) hL,
    polyaSmooth_polyaKernelMeasure_cdf_eq_half_add_sineWindow
      (μ := ν) (L := L) (t := t) hL]
  ring

theorem inversionCDFFormulaFor_polyaSmooth_polyaKernelMeasure_of_integrable_id
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L : ℝ} (hL : 0 < L)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hν1 : Integrable (fun x : ℝ => x) ν)
    (hInvInt :
      ∀ t : ℝ,
        IntervalIntegrable
          (fun θ : ℝ =>
            inversionKernelIntegrand
              (charFun (polyaSmooth μ (polyaKernelMeasure L)))
              (charFun (polyaSmooth ν (polyaKernelMeasure L))) t θ)
          volume (-L) L) :
    inversionCDFFormulaFor
      (polyaSmooth μ (polyaKernelMeasure L))
      (polyaSmooth ν (polyaKernelMeasure L))
      (charFun (polyaSmooth μ (polyaKernelMeasure L)))
      (charFun (polyaSmooth ν (polyaKernelMeasure L))) L := by
  intro t
  let Aμ : ℝ → ℝ := fun θ =>
    ∫ x, triangleMultiplier L θ * sineDivKernel (t - x) θ ∂μ
  let Aν : ℝ → ℝ := fun θ =>
    ∫ x, triangleMultiplier L θ * sineDivKernel (t - x) θ ∂ν
  let Inv : ℝ → ℂ := fun θ =>
    inversionKernelIntegrand
      (charFun (polyaSmooth μ (polyaKernelMeasure L)))
      (charFun (polyaSmooth ν (polyaKernelMeasure L))) t θ
  have hle : -L ≤ L := by linarith
  have hAμInt : IntervalIntegrable Aμ volume (-L) L := by
    rw [intervalIntegrable_iff]
    simpa [Aμ, IntegrableOn, Function.uncurry] using
      (integrable_polyaSineWindow_product
        (μ := μ) (L := L) (t := t) hL hμ1).integral_prod_left
  have hAνInt : IntervalIntegrable Aν volume (-L) L := by
    rw [intervalIntegrable_iff]
    simpa [Aν, IntegrableOn, Function.uncurry] using
      (integrable_polyaSineWindow_product
        (μ := ν) (L := L) (t := t) hL hν1).integral_prod_left
  have hAE :
      ∀ᵐ θ ∂volume, θ ∈ Set.uIoc (-L) L →
        Aμ θ - Aν θ = (Inv θ).re := by
    have hz : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hz] with θ hθ _hθmem
    exact
      integral_triangle_sineDivKernel_sub_eq_re_inversionKernelIntegrand_polyaSmooth
        (μ := μ) (ν := ν) (L := L) (t := t) (θ := θ) hL hθ
  have hIntervalSet :
      ∫ θ in -L..L, Inv θ =
        inversionIntegral
          (charFun (polyaSmooth μ (polyaKernelMeasure L)))
          (charFun (polyaSmooth ν (polyaKernelMeasure L))) t L := by
    unfold inversionIntegral
    rw [intervalIntegral.integral_of_le hle]
    rw [integral_Icc_eq_integral_Ioc]
  have hRe :
      ∫ θ in -L..L, (Inv θ).re =
        (inversionIntegral
          (charFun (polyaSmooth μ (polyaKernelMeasure L)))
          (charFun (polyaSmooth ν (polyaKernelMeasure L))) t L).re := by
    calc
      ∫ θ in -L..L, (Inv θ).re
          = (∫ θ in -L..L, Inv θ).re := by
              exact intervalIntegral.intervalIntegral_re (hInvInt t)
      _ = (inversionIntegral
            (charFun (polyaSmooth μ (polyaKernelMeasure L)))
            (charFun (polyaSmooth ν (polyaKernelMeasure L))) t L).re := by
            rw [hIntervalSet]
  calc
    (polyaSmooth μ (polyaKernelMeasure L)).real (Set.Iic t) -
        (polyaSmooth ν (polyaKernelMeasure L)).real (Set.Iic t)
        = measureCDFDiff
            (polyaSmooth μ (polyaKernelMeasure L))
            (polyaSmooth ν (polyaKernelMeasure L)) t := by
            rfl
    _ = (1 / (2 * Real.pi)) *
        (∫ x, polyaSineWindow L t x ∂μ -
          ∫ x, polyaSineWindow L t x ∂ν) := by
          rw [measureCDFDiff_polyaSmooth_polyaKernelMeasure_eq_sineWindow
            (μ := μ) (ν := ν) (L := L) (t := t) hL]
    _ = (1 / (2 * Real.pi)) *
        ((∫ θ in -L..L, Aμ θ) - (∫ θ in -L..L, Aν θ)) := by
          rw [integral_polyaSineWindow_eq_interval_integral
              (μ := μ) (L := L) (t := t) hL hμ1,
            integral_polyaSineWindow_eq_interval_integral
              (μ := ν) (L := L) (t := t) hL hν1]
    _ = (1 / (2 * Real.pi)) *
        (∫ θ in -L..L, Aμ θ - Aν θ) := by
          rw [intervalIntegral.integral_sub hAμInt hAνInt]
    _ = (1 / (2 * Real.pi)) *
        (∫ θ in -L..L, (Inv θ).re) := by
          rw [intervalIntegral.integral_congr_ae hAE]
    _ = (1 / (2 * Real.pi)) *
        (inversionIntegral
          (charFun (polyaSmooth μ (polyaKernelMeasure L)))
          (charFun (polyaSmooth ν (polyaKernelMeasure L))) t L).re := by
          rw [hRe]

lemma intervalIntegrable_inversionKernelIntegrand_polyaSmooth_of_integrable
    (μ ν H : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {L t : ℝ} (hL : 0 < L) (hH : IsPolyaKernelMeasure H L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    IntervalIntegrable
      (fun θ : ℝ =>
        inversionKernelIntegrand
          (charFun (polyaSmooth μ H)) (charFun (polyaSmooth ν H)) t θ)
      volume (-L) L := by
  letI : IsProbabilityMeasure H := hH.probability
  haveI : IsFiniteMeasure (polyaSmooth μ H) := by
    dsimp [polyaSmooth]
    infer_instance
  haveI : IsFiniteMeasure (polyaSmooth ν H) := by
    dsimp [polyaSmooth]
    infer_instance
  have hle : -L ≤ L := by linarith
  have hSmoothInt :
      IntegrableOn
        (fun θ : ℝ =>
          ‖charFun (polyaSmooth μ H) θ -
            charFun (polyaSmooth ν H) θ‖ / |θ|)
        (Set.Icc (-L) L) :=
    integrableOn_polyaSmoothed_fourierIntegrand_of_integrable
      μ ν H hL hH hOrigInt
  have hMeas :
      AEStronglyMeasurable
        (fun θ : ℝ =>
          inversionKernelIntegrand
            (charFun (polyaSmooth μ H)) (charFun (polyaSmooth ν H)) t θ)
        (volume.restrict (Set.Icc (-L) L)) := by
    unfold inversionKernelIntegrand
    have hExp :
        AEStronglyMeasurable
          (fun θ : ℝ => Complex.exp (((-(θ * t) : ℝ) : ℂ) * Complex.I))
          (volume.restrict (Set.Icc (-L) L)) := by
      fun_prop
    have hφ :
        AEStronglyMeasurable
          (fun θ : ℝ => charFun (polyaSmooth μ H) θ)
          (volume.restrict (Set.Icc (-L) L)) :=
      (continuous_charFun (μ := polyaSmooth μ H)).aestronglyMeasurable
    have hψ :
        AEStronglyMeasurable
          (fun θ : ℝ => charFun (polyaSmooth ν H) θ)
          (volume.restrict (Set.Icc (-L) L)) :=
      (continuous_charFun (μ := polyaSmooth ν H)).aestronglyMeasurable
    have hden :
        AEStronglyMeasurable
          (fun θ : ℝ => Complex.I * (θ : ℂ))
          (volume.restrict (Set.Icc (-L) L)) := by
      fun_prop
    exact (hExp.mul ((hφ.sub hψ).div₀ hden)).neg
  have hOnIcc :
      IntegrableOn
        (fun θ : ℝ =>
          inversionKernelIntegrand
            (charFun (polyaSmooth μ H)) (charFun (polyaSmooth ν H)) t θ)
        (Set.Icc (-L) L) := by
    rw [IntegrableOn] at hSmoothInt ⊢
    exact hSmoothInt.mono' hMeas (Eventually.of_forall fun θ => by
      rw [norm_inversionKernelIntegrand])
  rw [intervalIntegrable_iff]
  have hOnU :
      IntegrableOn
        (fun θ : ℝ =>
          inversionKernelIntegrand
            (charFun (polyaSmooth μ H)) (charFun (polyaSmooth ν H)) t θ)
        (Set.uIcc (-L) L) := by
    simpa [Set.uIcc_of_le hle] using hOnIcc
  exact hOnU.mono_set Set.uIoc_subset_uIcc

theorem inversionCDFFormulaFor_polyaSmooth_polyaKernelMeasure_of_integrable
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L : ℝ} (hL : 0 < L)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hν1 : Integrable (fun x : ℝ => x) ν)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    inversionCDFFormulaFor
      (polyaSmooth μ (polyaKernelMeasure L))
      (polyaSmooth ν (polyaKernelMeasure L))
      (charFun (polyaSmooth μ (polyaKernelMeasure L)))
      (charFun (polyaSmooth ν (polyaKernelMeasure L))) L := by
  refine
    inversionCDFFormulaFor_polyaSmooth_polyaKernelMeasure_of_integrable_id
      (μ := μ) (ν := ν) (L := L) hL hμ1 hν1 ?_
  intro t
  exact
    intervalIntegrable_inversionKernelIntegrand_polyaSmooth_of_integrable
      (μ := μ) (ν := ν) (H := polyaKernelMeasure L)
      (L := L) (t := t) hL
      (isPolyaKernelMeasure_polyaKernelMeasure hL) hOrigInt

/-- Durrett/Feller smoothed inversion lemma in book-facing naming:
after convolution with the concrete Polya kernel, finite first moments and
local Fourier-distance integrability give the truncated inversion formula for
the smoothed CDFs. -/
theorem durrettFeller_smoothedInversion_polyaKernelMeasure
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L : ℝ} (hL : 0 < L)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hν1 : Integrable (fun x : ℝ => x) ν)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    inversionCDFFormulaFor
      (polyaSmooth μ (polyaKernelMeasure L))
      (polyaSmooth ν (polyaKernelMeasure L))
      (charFun (polyaSmooth μ (polyaKernelMeasure L)))
      (charFun (polyaSmooth ν (polyaKernelMeasure L))) L :=
  inversionCDFFormulaFor_polyaSmooth_polyaKernelMeasure_of_integrable
    (μ := μ) (ν := ν) (L := L) hL hμ1 hν1 hOrigInt

/-- Durrett's positive-witness half of the sharper Polya smoothing estimate.

If the CDF difference reaches the positive value `η` at `x0`, the smoothed
CDF difference at `x0 + η/(2λ)` is still at least
`η/2 - 12λ/(πL)`.  This is the integrated form of the central-window
argument in Lemma 3.4.18. -/
lemma measureCDFDiff_polyaSmooth_lower_of_pos_witness
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η x0 : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hLip : measureCDFLipschitz ν lam)
    (hGlobal : measureCDFErrorLE μ ν η)
    (hWitness : measureCDFDiff μ ν x0 = η) :
    η / 2 - 12 * lam / (Real.pi * L) ≤
      measureCDFDiff
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L))
        (x0 + η / (2 * lam)) := by
  let H : Measure ℝ := polyaKernelMeasure L
  let δ : ℝ := η / (2 * lam)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  letI : IsProbabilityMeasure H := by
    dsimp [H]
    exact isProbabilityMeasure_polyaKernelMeasure hL
  have hfi :
      Integrable
        (fun y : ℝ => measureCDFDiff μ ν (x0 + η / (2 * lam) - y)) H :=
    integrable_measureCDFDiff_sub μ ν H (x0 + η / (2 * lam))
  have hsplit :
      (∫ y in Set.Icc (-δ) δ,
          measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H) +
        (∫ y in (Set.Icc (-δ) δ)ᶜ,
          measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H) =
        ∫ y, measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H :=
    integral_add_compl measurableSet_Icc hfi
  have hcentral :
      ∫ y in Set.Icc (-δ) δ, η / 2 + lam * y ∂H ≤
        ∫ y in Set.Icc (-δ) δ,
          measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H := by
    refine setIntegral_mono_on
      (integrableOn_affine_Icc_of_finite H)
      hfi.integrableOn measurableSet_Icc ?_
    intro y hy
    exact measureCDFDiff_central_lower_of_pos_witness
      (μ := μ) (ν := ν) (lam := lam) (η := η) (x0 := x0) (y := y)
      hlam hLip hWitness (by
        dsimp [δ] at hy
        exact hy.2)
  have hcomp :
      ∫ y in (Set.Icc (-δ) δ)ᶜ, (-η) ∂H ≤
        ∫ y in (Set.Icc (-δ) δ)ᶜ,
          measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H := by
    refine setIntegral_mono_on
      integrableOn_const hfi.integrableOn measurableSet_Icc.compl ?_
    intro y _hy
    exact neg_le_measureCDFDiff_of_measureCDFErrorLE
      (μ := μ) (ν := ν) (ε := η)
      (x := x0 + η / (2 * lam) - y) hGlobal
  have hcentral_eval :
      ∫ y in Set.Icc (-δ) δ, η / 2 + lam * y ∂H =
        (η / 2) * H.real (Set.Icc (-δ) δ) := by
    dsimp [H]
    simpa [δ] using
      polyaKernelMeasure_integral_affine_Icc
        (L := L) (a := δ) (c := η / 2) (m := lam) hL hδ.le
  have hcomp_eval :
      ∫ y in (Set.Icc (-δ) δ)ᶜ, (-η) ∂H =
        H.real ((Set.Icc (-δ) δ)ᶜ) * (-η) := by
    rw [setIntegral_const]
    simp [smul_eq_mul]
  have htail_eq :
      (Set.Icc (-δ) δ)ᶜ = absTailSet δ := by
    rw [absTailSet_eq_compl_Icc]
  have hcentral_mass :
      1 - 4 / (Real.pi * L * δ) ≤ H.real (Set.Icc (-δ) δ) := by
    dsimp [H]
    exact polyaKernelMeasure_real_Icc_ge_one_sub_explicit hL hδ
  have htail_mass :
      H.real ((Set.Icc (-δ) δ)ᶜ) ≤ 4 / (Real.pi * L * δ) := by
    rw [htail_eq]
    dsimp [H]
    exact polyaKernelMeasure_real_absTailSet_le_explicit hL hδ
  have hcentral_part :
      (η / 2) * (1 - 4 / (Real.pi * L * δ)) ≤
        (η / 2) * H.real (Set.Icc (-δ) δ) := by
    exact mul_le_mul_of_nonneg_left hcentral_mass (by positivity)
  have htail_part :
      (4 / (Real.pi * L * δ)) * (-η) ≤
        H.real ((Set.Icc (-δ) δ)ᶜ) * (-η) := by
    exact mul_le_mul_of_nonpos_right htail_mass (by linarith)
  have hpieces :
      (η / 2) * (1 - 4 / (Real.pi * L * δ)) +
          (4 / (Real.pi * L * δ)) * (-η) ≤
        (η / 2) * H.real (Set.Icc (-δ) δ) +
          H.real ((Set.Icc (-δ) δ)ᶜ) * (-η) :=
    add_le_add hcentral_part htail_part
  have hintegral_lower :
      (η / 2) * H.real (Set.Icc (-δ) δ) +
          H.real ((Set.Icc (-δ) δ)ᶜ) * (-η) ≤
        ∫ y, measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H := by
    rw [← hsplit]
    exact add_le_add
      (by simpa [hcentral_eval] using hcentral)
      (by simpa [hcomp_eval] using hcomp)
  have halg :
      (η / 2) * (1 - 4 / (Real.pi * L * δ)) +
          (4 / (Real.pi * L * δ)) * (-η) =
        η / 2 - 12 * lam / (Real.pi * L) := by
    dsimp [δ]
    field_simp [Real.pi_ne_zero, hL.ne', hlam.ne', hη.ne']
    ring
  rw [measureCDFDiff_polyaSmooth_eq_integral μ ν H (x0 + η / (2 * lam))]
  calc
    η / 2 - 12 * lam / (Real.pi * L)
        = (η / 2) * (1 - 4 / (Real.pi * L * δ)) +
            (4 / (Real.pi * L * δ)) * (-η) := halg.symm
    _ ≤ (η / 2) * H.real (Set.Icc (-δ) δ) +
          H.real ((Set.Icc (-δ) δ)ᶜ) * (-η) := hpieces
    _ ≤ ∫ y, measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H :=
          hintegral_lower

/-- Durrett's negative-witness half of the sharper Polya smoothing estimate.

If the CDF difference reaches `-η` at `x0`, the smoothed CDF difference at
`x0 - η/(2λ)` is at most `-η/2 + 12λ/(πL)`. -/
lemma measureCDFDiff_polyaSmooth_upper_of_neg_witness
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η x0 : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hLip : measureCDFLipschitz ν lam)
    (hGlobal : measureCDFErrorLE μ ν η)
    (hWitness : measureCDFDiff μ ν x0 = -η) :
    measureCDFDiff
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L))
        (x0 - η / (2 * lam)) ≤
      -η / 2 + 12 * lam / (Real.pi * L) := by
  let H : Measure ℝ := polyaKernelMeasure L
  let δ : ℝ := η / (2 * lam)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  letI : IsProbabilityMeasure H := by
    dsimp [H]
    exact isProbabilityMeasure_polyaKernelMeasure hL
  have hfi :
      Integrable
        (fun y : ℝ => measureCDFDiff μ ν (x0 - η / (2 * lam) - y)) H :=
    integrable_measureCDFDiff_sub μ ν H (x0 - η / (2 * lam))
  have hsplit :
      (∫ y in Set.Icc (-δ) δ,
          measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H) +
        (∫ y in (Set.Icc (-δ) δ)ᶜ,
          measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H) =
        ∫ y, measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H :=
    integral_add_compl measurableSet_Icc hfi
  have hcentral :
      ∫ y in Set.Icc (-δ) δ,
          measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H ≤
        ∫ y in Set.Icc (-δ) δ, -η / 2 + lam * y ∂H := by
    refine setIntegral_mono_on
      hfi.integrableOn (integrableOn_affine_Icc_of_finite H)
      measurableSet_Icc ?_
    intro y hy
    exact measureCDFDiff_central_upper_of_neg_witness
      (μ := μ) (ν := ν) (lam := lam) (η := η) (x0 := x0) (y := y)
      hlam hLip hWitness (by
        dsimp [δ] at hy
        exact hy.1)
  have hcomp :
      ∫ y in (Set.Icc (-δ) δ)ᶜ,
          measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H ≤
        ∫ y in (Set.Icc (-δ) δ)ᶜ, η ∂H := by
    refine setIntegral_mono_on
      hfi.integrableOn integrableOn_const measurableSet_Icc.compl ?_
    intro y _hy
    exact measureCDFDiff_le_of_measureCDFErrorLE
      (μ := μ) (ν := ν) (ε := η)
      (x := x0 - η / (2 * lam) - y) hGlobal
  have hcentral_eval :
      ∫ y in Set.Icc (-δ) δ, -η / 2 + lam * y ∂H =
        (-η / 2) * H.real (Set.Icc (-δ) δ) := by
    dsimp [H]
    simpa [δ] using
      polyaKernelMeasure_integral_affine_Icc
        (L := L) (a := δ) (c := -η / 2) (m := lam) hL hδ.le
  have hcomp_eval :
      ∫ y in (Set.Icc (-δ) δ)ᶜ, η ∂H =
        H.real ((Set.Icc (-δ) δ)ᶜ) * η := by
    rw [setIntegral_const]
    simp [smul_eq_mul]
  have htail_eq :
      (Set.Icc (-δ) δ)ᶜ = absTailSet δ := by
    rw [absTailSet_eq_compl_Icc]
  have hcentral_mass :
      1 - 4 / (Real.pi * L * δ) ≤ H.real (Set.Icc (-δ) δ) := by
    dsimp [H]
    exact polyaKernelMeasure_real_Icc_ge_one_sub_explicit hL hδ
  have htail_mass :
      H.real ((Set.Icc (-δ) δ)ᶜ) ≤ 4 / (Real.pi * L * δ) := by
    rw [htail_eq]
    dsimp [H]
    exact polyaKernelMeasure_real_absTailSet_le_explicit hL hδ
  have hcentral_part :
      (-η / 2) * H.real (Set.Icc (-δ) δ) ≤
        (-η / 2) * (1 - 4 / (Real.pi * L * δ)) := by
    exact mul_le_mul_of_nonpos_left hcentral_mass (by linarith)
  have htail_part :
      H.real ((Set.Icc (-δ) δ)ᶜ) * η ≤
        (4 / (Real.pi * L * δ)) * η := by
    exact mul_le_mul_of_nonneg_right htail_mass hη.le
  have hpieces :
      (-η / 2) * H.real (Set.Icc (-δ) δ) +
          H.real ((Set.Icc (-δ) δ)ᶜ) * η ≤
        (-η / 2) * (1 - 4 / (Real.pi * L * δ)) +
          (4 / (Real.pi * L * δ)) * η :=
    add_le_add hcentral_part htail_part
  have hintegral_upper :
      ∫ y, measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H ≤
        (-η / 2) * H.real (Set.Icc (-δ) δ) +
          H.real ((Set.Icc (-δ) δ)ᶜ) * η := by
    rw [← hsplit]
    exact add_le_add
      (by simpa [hcentral_eval] using hcentral)
      (by simpa [hcomp_eval] using hcomp)
  have halg :
      (-η / 2) * (1 - 4 / (Real.pi * L * δ)) +
          (4 / (Real.pi * L * δ)) * η =
        -η / 2 + 12 * lam / (Real.pi * L) := by
    dsimp [δ]
    field_simp [Real.pi_ne_zero, hL.ne', hlam.ne', hη.ne']
    ring
  rw [measureCDFDiff_polyaSmooth_eq_integral μ ν H (x0 - η / (2 * lam))]
  calc
    ∫ y, measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H
        ≤ (-η / 2) * H.real (Set.Icc (-δ) δ) +
          H.real ((Set.Icc (-δ) δ)ᶜ) * η := hintegral_upper
    _ ≤ (-η / 2) * (1 - 4 / (Real.pi * L * δ)) +
          (4 / (Real.pi * L * δ)) * η := hpieces
    _ = -η / 2 + 12 * lam / (Real.pi * L) := halg

/-- Positive approximate-witness version of Durrett's smoothing estimate.

If the CDF difference is at least `η - ε` at `x0`, the smoothed difference
at the usual `η/(2λ)` shift is at least
`η/2 - ε - 12λ/(πL)`. -/
lemma measureCDFDiff_polyaSmooth_lower_of_pos_approx_witness
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η ε x0 : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hε0 : 0 ≤ ε) (hεle : ε ≤ η / 2)
    (hLip : measureCDFLipschitz ν lam)
    (hGlobal : measureCDFErrorLE μ ν η)
    (hWitness : η - ε ≤ measureCDFDiff μ ν x0) :
    η / 2 - ε - 12 * lam / (Real.pi * L) ≤
      measureCDFDiff
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L))
        (x0 + η / (2 * lam)) := by
  let H : Measure ℝ := polyaKernelMeasure L
  let δ : ℝ := η / (2 * lam)
  let B : ℝ := 4 / (Real.pi * L * δ)
  let c : ℝ := η / 2 - ε
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  letI : IsProbabilityMeasure H := by
    dsimp [H]
    exact isProbabilityMeasure_polyaKernelMeasure hL
  have hfi :
      Integrable
        (fun y : ℝ => measureCDFDiff μ ν (x0 + η / (2 * lam) - y)) H :=
    integrable_measureCDFDiff_sub μ ν H (x0 + η / (2 * lam))
  have hsplit :
      (∫ y in Set.Icc (-δ) δ,
          measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H) +
        (∫ y in (Set.Icc (-δ) δ)ᶜ,
          measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H) =
        ∫ y, measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H :=
    integral_add_compl measurableSet_Icc hfi
  have hcentral :
      ∫ y in Set.Icc (-δ) δ, c + lam * y ∂H ≤
        ∫ y in Set.Icc (-δ) δ,
          measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H := by
    refine setIntegral_mono_on
      (integrableOn_affine_Icc_of_finite H)
      hfi.integrableOn measurableSet_Icc ?_
    intro y hy
    dsimp [c]
    exact measureCDFDiff_central_lower_of_pos_approx_witness
      (μ := μ) (ν := ν) (lam := lam) (η := η) (ε := ε)
      (x0 := x0) (y := y) hlam hLip hWitness (by
        dsimp [δ] at hy
        exact hy.2)
  have hcomp :
      ∫ y in (Set.Icc (-δ) δ)ᶜ, (-η) ∂H ≤
        ∫ y in (Set.Icc (-δ) δ)ᶜ,
          measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H := by
    refine setIntegral_mono_on
      integrableOn_const hfi.integrableOn measurableSet_Icc.compl ?_
    intro y _hy
    exact neg_le_measureCDFDiff_of_measureCDFErrorLE
      (μ := μ) (ν := ν) (ε := η)
      (x := x0 + η / (2 * lam) - y) hGlobal
  have hcentral_eval :
      ∫ y in Set.Icc (-δ) δ, c + lam * y ∂H =
        c * H.real (Set.Icc (-δ) δ) := by
    dsimp [H]
    simpa [δ, c] using
      polyaKernelMeasure_integral_affine_Icc
        (L := L) (a := δ) (c := c) (m := lam) hL hδ.le
  have hcomp_eval :
      ∫ y in (Set.Icc (-δ) δ)ᶜ, (-η) ∂H =
        H.real ((Set.Icc (-δ) δ)ᶜ) * (-η) := by
    rw [setIntegral_const]
    simp [smul_eq_mul]
  have htail_eq :
      (Set.Icc (-δ) δ)ᶜ = absTailSet δ := by
    rw [absTailSet_eq_compl_Icc]
  have hcentral_mass :
      1 - B ≤ H.real (Set.Icc (-δ) δ) := by
    dsimp [B, H]
    exact polyaKernelMeasure_real_Icc_ge_one_sub_explicit hL hδ
  have htail_mass :
      H.real ((Set.Icc (-δ) δ)ᶜ) ≤ B := by
    rw [htail_eq]
    dsimp [B, H]
    exact polyaKernelMeasure_real_absTailSet_le_explicit hL hδ
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    linarith
  have hcentral_part :
      c * (1 - B) ≤ c * H.real (Set.Icc (-δ) δ) :=
    mul_le_mul_of_nonneg_left hcentral_mass hc_nonneg
  have htail_part :
      B * (-η) ≤ H.real ((Set.Icc (-δ) δ)ᶜ) * (-η) :=
    mul_le_mul_of_nonpos_right htail_mass (by linarith)
  have hpieces :
      c * (1 - B) + B * (-η) ≤
        c * H.real (Set.Icc (-δ) δ) +
          H.real ((Set.Icc (-δ) δ)ᶜ) * (-η) :=
    add_le_add hcentral_part htail_part
  have hintegral_lower :
      c * H.real (Set.Icc (-δ) δ) +
          H.real ((Set.Icc (-δ) δ)ᶜ) * (-η) ≤
        ∫ y, measureCDFDiff μ ν (x0 + η / (2 * lam) - y) ∂H := by
    rw [← hsplit]
    exact add_le_add
      (by simpa [hcentral_eval] using hcentral)
      (by simpa [hcomp_eval] using hcomp)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hfactor_le : c + η ≤ 3 * η / 2 := by
    dsimp [c]
    linarith
  have hprod_le : B * (c + η) ≤ 12 * lam / (Real.pi * L) := by
    have h1 : B * (c + η) ≤ B * (3 * η / 2) :=
      mul_le_mul_of_nonneg_left hfactor_le hB_nonneg
    have h2 : B * (3 * η / 2) = 12 * lam / (Real.pi * L) := by
      dsimp [B, δ]
      field_simp [Real.pi_ne_zero, hL.ne', hlam.ne', hη.ne']
      ring
    exact h1.trans_eq h2
  have htarget :
      η / 2 - ε - 12 * lam / (Real.pi * L) ≤ c * (1 - B) + B * (-η) := by
    have hrewrite : c * (1 - B) + B * (-η) = c - B * (c + η) := by
      ring
    have hprod_le' :
        B * (η / 2 - ε + η) ≤ 12 * lam / (Real.pi * L) := by
      simpa [c] using hprod_le
    rw [hrewrite]
    dsimp [c]
    nlinarith
  rw [measureCDFDiff_polyaSmooth_eq_integral μ ν H (x0 + η / (2 * lam))]
  exact htarget.trans (hpieces.trans hintegral_lower)

/-- Negative approximate-witness version of Durrett's smoothing estimate. -/
lemma measureCDFDiff_polyaSmooth_upper_of_neg_approx_witness
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η ε x0 : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hε0 : 0 ≤ ε) (hεle : ε ≤ η / 2)
    (hLip : measureCDFLipschitz ν lam)
    (hGlobal : measureCDFErrorLE μ ν η)
    (hWitness : measureCDFDiff μ ν x0 ≤ -(η - ε)) :
    measureCDFDiff
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L))
        (x0 - η / (2 * lam)) ≤
      -η / 2 + ε + 12 * lam / (Real.pi * L) := by
  let H : Measure ℝ := polyaKernelMeasure L
  let δ : ℝ := η / (2 * lam)
  let B : ℝ := 4 / (Real.pi * L * δ)
  let c : ℝ := -η / 2 + ε
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  letI : IsProbabilityMeasure H := by
    dsimp [H]
    exact isProbabilityMeasure_polyaKernelMeasure hL
  have hfi :
      Integrable
        (fun y : ℝ => measureCDFDiff μ ν (x0 - η / (2 * lam) - y)) H :=
    integrable_measureCDFDiff_sub μ ν H (x0 - η / (2 * lam))
  have hsplit :
      (∫ y in Set.Icc (-δ) δ,
          measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H) +
        (∫ y in (Set.Icc (-δ) δ)ᶜ,
          measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H) =
        ∫ y, measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H :=
    integral_add_compl measurableSet_Icc hfi
  have hcentral :
      ∫ y in Set.Icc (-δ) δ,
          measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H ≤
        ∫ y in Set.Icc (-δ) δ, c + lam * y ∂H := by
    refine setIntegral_mono_on
      hfi.integrableOn (integrableOn_affine_Icc_of_finite H)
      measurableSet_Icc ?_
    intro y hy
    dsimp [c]
    exact measureCDFDiff_central_upper_of_neg_approx_witness
      (μ := μ) (ν := ν) (lam := lam) (η := η) (ε := ε)
      (x0 := x0) (y := y) hlam hLip hWitness (by
        dsimp [δ] at hy
        exact hy.1)
  have hcomp :
      ∫ y in (Set.Icc (-δ) δ)ᶜ,
          measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H ≤
        ∫ y in (Set.Icc (-δ) δ)ᶜ, η ∂H := by
    refine setIntegral_mono_on
      hfi.integrableOn integrableOn_const measurableSet_Icc.compl ?_
    intro y _hy
    exact measureCDFDiff_le_of_measureCDFErrorLE
      (μ := μ) (ν := ν) (ε := η)
      (x := x0 - η / (2 * lam) - y) hGlobal
  have hcentral_eval :
      ∫ y in Set.Icc (-δ) δ, c + lam * y ∂H =
        c * H.real (Set.Icc (-δ) δ) := by
    dsimp [H]
    simpa [δ, c] using
      polyaKernelMeasure_integral_affine_Icc
        (L := L) (a := δ) (c := c) (m := lam) hL hδ.le
  have hcomp_eval :
      ∫ y in (Set.Icc (-δ) δ)ᶜ, η ∂H =
        H.real ((Set.Icc (-δ) δ)ᶜ) * η := by
    rw [setIntegral_const]
    simp [smul_eq_mul]
  have htail_eq :
      (Set.Icc (-δ) δ)ᶜ = absTailSet δ := by
    rw [absTailSet_eq_compl_Icc]
  have hcentral_mass :
      1 - B ≤ H.real (Set.Icc (-δ) δ) := by
    dsimp [B, H]
    exact polyaKernelMeasure_real_Icc_ge_one_sub_explicit hL hδ
  have htail_mass :
      H.real ((Set.Icc (-δ) δ)ᶜ) ≤ B := by
    rw [htail_eq]
    dsimp [B, H]
    exact polyaKernelMeasure_real_absTailSet_le_explicit hL hδ
  have hc_nonpos : c ≤ 0 := by
    dsimp [c]
    linarith
  have hcentral_part :
      c * H.real (Set.Icc (-δ) δ) ≤ c * (1 - B) :=
    mul_le_mul_of_nonpos_left hcentral_mass hc_nonpos
  have htail_part :
      H.real ((Set.Icc (-δ) δ)ᶜ) * η ≤ B * η :=
    mul_le_mul_of_nonneg_right htail_mass hη.le
  have hpieces :
      c * H.real (Set.Icc (-δ) δ) +
          H.real ((Set.Icc (-δ) δ)ᶜ) * η ≤
        c * (1 - B) + B * η :=
    add_le_add hcentral_part htail_part
  have hintegral_upper :
      ∫ y, measureCDFDiff μ ν (x0 - η / (2 * lam) - y) ∂H ≤
        c * H.real (Set.Icc (-δ) δ) +
          H.real ((Set.Icc (-δ) δ)ᶜ) * η := by
    rw [← hsplit]
    exact add_le_add
      (by simpa [hcentral_eval] using hcentral)
      (by simpa [hcomp_eval] using hcomp)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hfactor_le : η - c ≤ 3 * η / 2 := by
    dsimp [c]
    linarith
  have hprod_le : B * (η - c) ≤ 12 * lam / (Real.pi * L) := by
    have h1 : B * (η - c) ≤ B * (3 * η / 2) :=
      mul_le_mul_of_nonneg_left hfactor_le hB_nonneg
    have h2 : B * (3 * η / 2) = 12 * lam / (Real.pi * L) := by
      dsimp [B, δ]
      field_simp [Real.pi_ne_zero, hL.ne', hlam.ne', hη.ne']
      ring
    exact h1.trans_eq h2
  have htarget :
      c * (1 - B) + B * η ≤ -η / 2 + ε + 12 * lam / (Real.pi * L) := by
    have hrewrite : c * (1 - B) + B * η = c + B * (η - c) := by
      ring
    have hprod_le' :
        B * (η - (-η / 2 + ε)) ≤ 12 * lam / (Real.pi * L) := by
      simpa [c] using hprod_le
    rw [hrewrite]
    dsimp [c]
    nlinarith
  rw [measureCDFDiff_polyaSmooth_eq_integral μ ν H (x0 - η / (2 * lam))]
  exact (hintegral_upper.trans hpieces).trans htarget

/-- Positive-witness corollary of Durrett's sharper smoothing lemma.

If the original CDF difference is globally bounded by `η` and attains `η`,
then a smoothed error bound `ηL` forces
`η ≤ 2 ηL + 24λ/(πL)`. -/
lemma eta_le_of_polyaSmooth_error_pos_witness
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η ηL x0 : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hLip : measureCDFLipschitz ν lam)
    (hGlobal : measureCDFErrorLE μ ν η)
    (hWitness : measureCDFDiff μ ν x0 = η)
    (hSmooth :
      measureCDFErrorLE
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) ηL) :
    η ≤ 2 * ηL + 24 * lam / (Real.pi * L) := by
  have hlower :=
    measureCDFDiff_polyaSmooth_lower_of_pos_witness
      (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η) (x0 := x0)
      hL hlam hη hLip hGlobal hWitness
  have hupper :
      measureCDFDiff
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L))
        (x0 + η / (2 * lam)) ≤ ηL :=
    measureCDFDiff_le_of_measureCDFErrorLE
      (μ := polyaSmooth μ (polyaKernelMeasure L))
      (ν := polyaSmooth ν (polyaKernelMeasure L))
      (ε := ηL) (x := x0 + η / (2 * lam)) hSmooth
  let C : ℝ := 12 * lam / (Real.pi * L)
  have hη_le : η ≤ 2 * ηL + 2 * C := by
    have hineq : η / 2 - C ≤ ηL := by
      dsimp [C]
      exact hlower.trans hupper
    nlinarith
  calc
    η ≤ 2 * ηL + 2 * C := hη_le
    _ = 2 * ηL + 24 * lam / (Real.pi * L) := by
          dsimp [C]
          ring

/-- Negative-witness corollary of Durrett's sharper smoothing lemma.

If the original CDF difference is globally bounded by `η` and attains `-η`,
then a smoothed error bound `ηL` forces
`η ≤ 2 ηL + 24λ/(πL)`. -/
lemma eta_le_of_polyaSmooth_error_neg_witness
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η ηL x0 : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hLip : measureCDFLipschitz ν lam)
    (hGlobal : measureCDFErrorLE μ ν η)
    (hWitness : measureCDFDiff μ ν x0 = -η)
    (hSmooth :
      measureCDFErrorLE
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) ηL) :
    η ≤ 2 * ηL + 24 * lam / (Real.pi * L) := by
  have hupper :=
    measureCDFDiff_polyaSmooth_upper_of_neg_witness
      (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η) (x0 := x0)
      hL hlam hη hLip hGlobal hWitness
  have hlower :
      -ηL ≤
        measureCDFDiff
          (polyaSmooth μ (polyaKernelMeasure L))
          (polyaSmooth ν (polyaKernelMeasure L))
          (x0 - η / (2 * lam)) :=
    neg_le_measureCDFDiff_of_measureCDFErrorLE
      (μ := polyaSmooth μ (polyaKernelMeasure L))
      (ν := polyaSmooth ν (polyaKernelMeasure L))
      (ε := ηL) (x := x0 - η / (2 * lam)) hSmooth
  let C : ℝ := 12 * lam / (Real.pi * L)
  have hη_le : η ≤ 2 * ηL + 2 * C := by
    have hineq : -ηL ≤ -η / 2 + C := by
      dsimp [C]
      exact hlower.trans hupper
    nlinarith
  calc
    η ≤ 2 * ηL + 2 * C := hη_le
    _ = 2 * ηL + 24 * lam / (Real.pi * L) := by
          dsimp [C]
          ring

/-- Witness-form Durrett smoothing estimate.  The assumption
`∃ x0, Δ(x0) = η ∨ Δ(x0) = -η` is the explicit attainment hypothesis for
the original Kolmogorov error. -/
lemma eta_le_of_polyaSmooth_error_witness
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η ηL : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hLip : measureCDFLipschitz ν lam)
    (hGlobal : measureCDFErrorLE μ ν η)
    (hWitness : ∃ x0 : ℝ,
      measureCDFDiff μ ν x0 = η ∨ measureCDFDiff μ ν x0 = -η)
    (hSmooth :
      measureCDFErrorLE
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) ηL) :
    η ≤ 2 * ηL + 24 * lam / (Real.pi * L) := by
  rcases hWitness with ⟨x0, hpos | hneg⟩
  · exact eta_le_of_polyaSmooth_error_pos_witness
      (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η) (ηL := ηL)
      (x0 := x0) hL hlam hη hLip hGlobal hpos hSmooth
  · exact eta_le_of_polyaSmooth_error_neg_witness
      (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η) (ηL := ηL)
      (x0 := x0) hL hlam hη hLip hGlobal hneg hSmooth

/-- Sharp Polya smoothing bound under an explicit attained-error hypothesis.

This is Durrett's Lemma 3.4.18 in the form used by Esseen smoothing, except
that the global supremum/attainment reduction is kept as a transparent
hypothesis. -/
lemma measureCDFErrorLE_of_polyaSmooth_error_attained
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η ηL : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hLip : measureCDFLipschitz ν lam)
    (hGlobal : measureCDFErrorLE μ ν η)
    (hWitness : ∃ x0 : ℝ,
      measureCDFDiff μ ν x0 = η ∨ measureCDFDiff μ ν x0 = -η)
    (hSmooth :
      measureCDFErrorLE
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) ηL) :
    measureCDFErrorLE μ ν (2 * ηL + 24 * lam / (Real.pi * L)) := by
  exact measureCDFErrorLE_mono hGlobal
    (eta_le_of_polyaSmooth_error_witness
      (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η) (ηL := ηL)
      hL hlam hη hLip hGlobal hWitness hSmooth)

/-- Positive approximate-witness corollary of the sharper smoothing lemma. -/
lemma eta_le_of_polyaSmooth_error_pos_approx_witness
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η ηL ε x0 : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hε0 : 0 ≤ ε) (hεle : ε ≤ η / 2)
    (hLip : measureCDFLipschitz ν lam)
    (hGlobal : measureCDFErrorLE μ ν η)
    (hWitness : η - ε ≤ measureCDFDiff μ ν x0)
    (hSmooth :
      measureCDFErrorLE
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) ηL) :
    η ≤ 2 * ηL + 24 * lam / (Real.pi * L) + 2 * ε := by
  have hlower :=
    measureCDFDiff_polyaSmooth_lower_of_pos_approx_witness
      (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η) (ε := ε)
      (x0 := x0) hL hlam hη hε0 hεle hLip hGlobal hWitness
  have hupper :
      measureCDFDiff
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L))
        (x0 + η / (2 * lam)) ≤ ηL :=
    measureCDFDiff_le_of_measureCDFErrorLE
      (μ := polyaSmooth μ (polyaKernelMeasure L))
      (ν := polyaSmooth ν (polyaKernelMeasure L))
      (ε := ηL) (x := x0 + η / (2 * lam)) hSmooth
  let C : ℝ := 12 * lam / (Real.pi * L)
  have hη_le : η ≤ 2 * ηL + 2 * C + 2 * ε := by
    have hineq : η / 2 - ε - C ≤ ηL := by
      dsimp [C]
      exact hlower.trans hupper
    nlinarith
  calc
    η ≤ 2 * ηL + 2 * C + 2 * ε := hη_le
    _ = 2 * ηL + 24 * lam / (Real.pi * L) + 2 * ε := by
          dsimp [C]
          ring

/-- Negative approximate-witness corollary of the sharper smoothing lemma. -/
lemma eta_le_of_polyaSmooth_error_neg_approx_witness
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η ηL ε x0 : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hε0 : 0 ≤ ε) (hεle : ε ≤ η / 2)
    (hLip : measureCDFLipschitz ν lam)
    (hGlobal : measureCDFErrorLE μ ν η)
    (hWitness : measureCDFDiff μ ν x0 ≤ -(η - ε))
    (hSmooth :
      measureCDFErrorLE
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) ηL) :
    η ≤ 2 * ηL + 24 * lam / (Real.pi * L) + 2 * ε := by
  have hupper :=
    measureCDFDiff_polyaSmooth_upper_of_neg_approx_witness
      (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η) (ε := ε)
      (x0 := x0) hL hlam hη hε0 hεle hLip hGlobal hWitness
  have hlower :
      -ηL ≤
        measureCDFDiff
          (polyaSmooth μ (polyaKernelMeasure L))
          (polyaSmooth ν (polyaKernelMeasure L))
          (x0 - η / (2 * lam)) :=
    neg_le_measureCDFDiff_of_measureCDFErrorLE
      (μ := polyaSmooth μ (polyaKernelMeasure L))
      (ν := polyaSmooth ν (polyaKernelMeasure L))
      (ε := ηL) (x := x0 - η / (2 * lam)) hSmooth
  let C : ℝ := 12 * lam / (Real.pi * L)
  have hη_le : η ≤ 2 * ηL + 2 * C + 2 * ε := by
    have hineq : -ηL ≤ -η / 2 + ε + C := by
      dsimp [C]
      exact hlower.trans hupper
    nlinarith
  calc
    η ≤ 2 * ηL + 2 * C + 2 * ε := hη_le
    _ = 2 * ηL + 24 * lam / (Real.pi * L) + 2 * ε := by
          dsimp [C]
          ring

/-- Approximate-witness form of Durrett's sharper smoothing estimate. -/
lemma eta_le_of_polyaSmooth_error_approx_witness
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η ηL ε : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hε0 : 0 ≤ ε) (hεle : ε ≤ η / 2)
    (hLip : measureCDFLipschitz ν lam)
    (hGlobal : measureCDFErrorLE μ ν η)
    (hWitness : ∃ x0 : ℝ,
      η - ε ≤ measureCDFDiff μ ν x0 ∨
        measureCDFDiff μ ν x0 ≤ -(η - ε))
    (hSmooth :
      measureCDFErrorLE
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) ηL) :
    η ≤ 2 * ηL + 24 * lam / (Real.pi * L) + 2 * ε := by
  rcases hWitness with ⟨x0, hpos | hneg⟩
  · exact eta_le_of_polyaSmooth_error_pos_approx_witness
      (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η) (ηL := ηL)
      (ε := ε) (x0 := x0) hL hlam hη hε0 hεle hLip hGlobal hpos hSmooth
  · exact eta_le_of_polyaSmooth_error_neg_approx_witness
      (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η) (ηL := ηL)
      (ε := ε) (x0 := x0) hL hlam hη hε0 hεle hLip hGlobal hneg hSmooth

/-- Unconditional epsilon-supremum assembly of Durrett's sharper Polya
smoothing lemma, expressed with `measureCDFErrorIsLeast`.

This removes the explicit attained-error hypothesis: the proof chooses
approximate witnesses from leastness and lets the approximation parameter go
to zero. -/
lemma eta_le_of_polyaSmooth_error_isLeast
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η ηL : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hLip : measureCDFLipschitz ν lam)
    (hLeast : measureCDFErrorIsLeast μ ν η)
    (hSmooth :
      measureCDFErrorLE
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) ηL) :
    η ≤ 2 * ηL + 24 * lam / (Real.pi * L) := by
  refine le_of_forall_pos_le_add ?_
  intro γ hγ
  let ε : ℝ := min (γ / 2) (η / 2)
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min (by positivity) (by positivity)
  have hε0 : 0 ≤ ε := hεpos.le
  have hεle : ε ≤ η / 2 := by
    dsimp [ε]
    exact min_le_right _ _
  have hεγ : 2 * ε ≤ γ := by
    have hεγ' : ε ≤ γ / 2 := by
      dsimp [ε]
      exact min_le_left _ _
    linarith
  rcases exists_measureCDFDiff_pos_or_neg_gt_sub_of_measureCDFErrorIsLeast
      (μ := μ) (ν := ν) hLeast hεpos with ⟨x0, hpos | hneg⟩
  · have hWitness :
        η - ε ≤ measureCDFDiff μ ν x0 := le_of_lt hpos
    have hmain :=
      eta_le_of_polyaSmooth_error_pos_approx_witness
        (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η)
        (ηL := ηL) (ε := ε) (x0 := x0)
        hL hlam hη hε0 hεle hLip hLeast.1 hWitness hSmooth
    nlinarith
  · have hWitness :
        measureCDFDiff μ ν x0 ≤ -(η - ε) := by
      linarith
    have hmain :=
      eta_le_of_polyaSmooth_error_neg_approx_witness
        (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η)
        (ηL := ηL) (ε := ε) (x0 := x0)
        hL hlam hη hε0 hεle hLip hLeast.1 hWitness hSmooth
    nlinarith

/-- Sharp Polya smoothing bound when `η` is the least original CDF-error
bound. -/
lemma measureCDFErrorLE_of_polyaSmooth_error_isLeast
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam η ηL : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hLip : measureCDFLipschitz ν lam)
    (hLeast : measureCDFErrorIsLeast μ ν η)
    (hSmooth :
      measureCDFErrorLE
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) ηL) :
    measureCDFErrorLE μ ν (2 * ηL + 24 * lam / (Real.pi * L)) := by
  exact measureCDFErrorLE_mono hLeast.1
    (eta_le_of_polyaSmooth_error_isLeast
      (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η) (ηL := ηL)
      hL hlam hη hLip hLeast hSmooth)

lemma measureCDFErrorSup_nonneg
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ measureCDFErrorSup μ ν := by
  have hmem : |measureCDFDiff μ ν 0| ∈ measureCDFErrorSet μ ν :=
    Set.mem_range_self 0
  exact (abs_nonneg _).trans
    (le_csSup (measureCDFErrorSet_bddAbove μ ν) hmem)

lemma measureCDFErrorLE_zero_of_sup_nonpos
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hη : measureCDFErrorSup μ ν ≤ 0) :
    measureCDFErrorLE μ ν 0 :=
  measureCDFErrorLE_mono (measureCDFErrorSup_isLeast μ ν).1 hη

/-- Supremum-form Durrett smoothing estimate.  Unlike the `isLeast` version,
this does not require an externally supplied least-error witness: the
Kolmogorov error is constructed as `measureCDFErrorSup`. -/
lemma measureCDFErrorLE_of_polyaSmooth_error_sup
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam ηL : ℝ}
    (hL : 0 < L) (hlam : 0 < lam)
    (hLip : measureCDFLipschitz ν lam)
    (hSmooth :
      measureCDFErrorLE
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) ηL) :
    measureCDFErrorLE μ ν (2 * ηL + 24 * lam / (Real.pi * L)) := by
  by_cases hηpos : 0 < measureCDFErrorSup μ ν
  · exact measureCDFErrorLE_of_polyaSmooth_error_isLeast
      (μ := μ) (ν := ν) (L := L) (lam := lam)
      (η := measureCDFErrorSup μ ν) (ηL := ηL)
      hL hlam hηpos hLip (measureCDFErrorSup_isLeast μ ν) hSmooth
  · have hzero : measureCDFErrorLE μ ν 0 :=
      measureCDFErrorLE_zero_of_sup_nonpos μ ν (le_of_not_gt hηpos)
    have hηL_nonneg : 0 ≤ ηL := (abs_nonneg _).trans (hSmooth 0)
    exact measureCDFErrorLE_mono hzero
      (by
        exact add_nonneg (mul_nonneg (by norm_num) hηL_nonneg)
          (div_nonneg (mul_nonneg (by norm_num) hlam.le)
            (mul_nonneg Real.pi_pos.le hL.le)))

/-- Durrett/Feller's Polya-convolution smoothing lemma in supremum form:
if the Polya-smoothed CDFs differ by at most `η_L`, then the original CDFs
differ by at most `2η_L + 24λ/(πL)`. -/
theorem durrettFeller_polyaConvolutionSmoothing
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L lam ηL : ℝ}
    (hL : 0 < L) (hlam : 0 < lam)
    (hLip : measureCDFLipschitz ν lam)
    (hSmooth :
      measureCDFErrorLE
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L)) ηL) :
    measureCDFErrorLE μ ν (2 * ηL + 24 * lam / (Real.pi * L)) :=
  measureCDFErrorLE_of_polyaSmooth_error_sup
    (μ := μ) (ν := ν) (L := L) (lam := lam) (ηL := ηL)
    hL hlam hLip hSmooth

lemma conv_cdf_le_shift_add_tail
    (μ H : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure H]
    {a x : ℝ} :
    μ.real (Set.Iic x) ≤
      (μ ∗ H).real (Set.Iic (x + a)) + H.real (absTailSet a) := by
  let A : Set (ℝ × ℝ) := {p | p.1 ≤ x}
  let B : Set (ℝ × ℝ) := {p | p.1 + p.2 ≤ x + a}
  let C : Set (ℝ × ℝ) := {p | a < |p.2|}
  have hAeq : (μ.prod H).real A = μ.real (Set.Iic x) := by
    have hApre : A = Prod.fst ⁻¹' Set.Iic x := by
      ext p
      simp [A]
    rw [hApre, ← map_measureReal_apply (μ := μ.prod H) measurable_fst measurableSet_Iic]
    simp
  have hBeq : (μ.prod H).real B = (μ ∗ H).real (Set.Iic (x + a)) := by
    have hBpre : B = (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iic (x + a) := by
      ext p
      simp [B]
    rw [hBpre, ← map_measureReal_apply (μ := μ.prod H)
      (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 + p.2)
      measurableSet_Iic]
    simp [Measure.conv]
  have hCeq : (μ.prod H).real C = H.real (absTailSet a) := by
    have hCpre : C = Prod.snd ⁻¹' absTailSet a := by
      ext p
      simp [C, absTailSet]
    have hTailMeas : MeasurableSet (absTailSet a) := by
      exact measurableSet_lt measurable_const measurable_abs
    rw [hCpre, ← map_measureReal_apply (μ := μ.prod H) measurable_snd hTailMeas]
    simp [absTailSet]
  have hsubset : A ⊆ B ∪ C := by
    intro p hpA
    dsimp [A] at hpA
    by_cases hpC : a < |p.2|
    · exact Or.inr hpC
    · left
      have hp_abs : |p.2| ≤ a := le_of_not_gt hpC
      have hp2_le : p.2 ≤ a := (abs_le.mp hp_abs).2
      dsimp [B]
      linarith
  calc
    μ.real (Set.Iic x)
        = (μ.prod H).real A := hAeq.symm
    _ ≤ (μ.prod H).real (B ∪ C) := measureReal_mono hsubset
    _ ≤ (μ.prod H).real B + (μ.prod H).real C := measureReal_union_le B C
    _ = (μ ∗ H).real (Set.Iic (x + a)) + H.real (absTailSet a) := by
          rw [hBeq, hCeq]

lemma conv_cdf_shift_le_cdf_add_tail
    (μ H : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure H]
    {a x : ℝ} :
    (μ ∗ H).real (Set.Iic (x - a)) ≤
      μ.real (Set.Iic x) + H.real (absTailSet a) := by
  let A : Set (ℝ × ℝ) := {p | p.1 + p.2 ≤ x - a}
  let B : Set (ℝ × ℝ) := {p | p.1 ≤ x}
  let C : Set (ℝ × ℝ) := {p | a < |p.2|}
  have hAeq : (μ.prod H).real A = (μ ∗ H).real (Set.Iic (x - a)) := by
    have hApre : A = (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iic (x - a) := by
      ext p
      simp [A]
    rw [hApre, ← map_measureReal_apply (μ := μ.prod H)
      (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 + p.2)
      measurableSet_Iic]
    simp [Measure.conv]
  have hBeq : (μ.prod H).real B = μ.real (Set.Iic x) := by
    have hBpre : B = Prod.fst ⁻¹' Set.Iic x := by
      ext p
      simp [B]
    rw [hBpre, ← map_measureReal_apply (μ := μ.prod H) measurable_fst measurableSet_Iic]
    simp
  have hCeq : (μ.prod H).real C = H.real (absTailSet a) := by
    have hCpre : C = Prod.snd ⁻¹' absTailSet a := by
      ext p
      simp [C, absTailSet]
    have hTailMeas : MeasurableSet (absTailSet a) := by
      exact measurableSet_lt measurable_const measurable_abs
    rw [hCpre, ← map_measureReal_apply (μ := μ.prod H) measurable_snd hTailMeas]
    simp [absTailSet]
  have hsubset : A ⊆ B ∪ C := by
    intro p hpA
    by_cases hpC : a < |p.2|
    · exact Or.inr hpC
    · left
      have hp_abs : |p.2| ≤ a := le_of_not_gt hpC
      have hp2_ge : -a ≤ p.2 := (abs_le.mp hp_abs).1
      dsimp [B]
      dsimp [A] at hpA
      linarith
  calc
    (μ ∗ H).real (Set.Iic (x - a))
        = (μ.prod H).real A := hAeq.symm
    _ ≤ (μ.prod H).real (B ∪ C) := measureReal_mono hsubset
    _ ≤ (μ.prod H).real B + (μ.prod H).real C := measureReal_union_le B C
    _ = μ.real (Set.Iic x) + H.real (absTailSet a) := by
          rw [hBeq, hCeq]

lemma measureCDFErrorLE_of_conv_smoothing
    {μ ν H : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure H] {a τ η lam : ℝ}
    (ha : 0 ≤ a)
    (hTail : H.real (absTailSet a) ≤ τ)
    (hLip : measureCDFLipschitz ν lam)
    (hSmooth : measureCDFErrorLE (polyaSmooth μ H) (polyaSmooth ν H) η) :
    measureCDFErrorLE μ ν (η + 2 * τ + 2 * lam * a) := by
  intro x
  rw [abs_sub_le_iff]
  constructor
  · have hμ_shift :
        μ.real (Set.Iic x) ≤ (polyaSmooth μ H).real (Set.Iic (x + a)) + τ :=
      (conv_cdf_le_shift_add_tail μ H (a := a) (x := x)).trans (by
        simp [polyaSmooth]
        linarith)
    have hsm :
        (polyaSmooth μ H).real (Set.Iic (x + a)) ≤
          (polyaSmooth ν H).real (Set.Iic (x + a)) + η := by
      have h := hSmooth (x + a)
      exact (sub_le_iff_le_add'.mp (le_trans (le_abs_self _) h))
    have hν_shift :
        (polyaSmooth ν H).real (Set.Iic (x + a)) ≤
          ν.real (Set.Iic (x + 2 * a)) + τ := by
      have h :=
        conv_cdf_shift_le_cdf_add_tail ν H (a := a) (x := x + 2 * a)
      have hrewrite : x + 2 * a - a = x + a := by ring
      have h' :
          (polyaSmooth ν H).real (Set.Iic (x + a)) ≤
            ν.real (Set.Iic (x + 2 * a)) + H.real (absTailSet a) := by
        simpa [polyaSmooth, hrewrite] using h
      exact h'.trans (by linarith)
    have hlip :
        ν.real (Set.Iic (x + 2 * a)) - ν.real (Set.Iic x) ≤
          lam * (2 * a) := by
      have hxle : x ≤ x + 2 * a := by nlinarith
      simpa using hLip x (x + 2 * a) hxle
    calc
      μ.real (Set.Iic x) - ν.real (Set.Iic x)
          ≤ ((polyaSmooth μ H).real (Set.Iic (x + a)) + τ) -
              ν.real (Set.Iic x) := sub_le_sub_right hμ_shift _
      _ ≤ (((polyaSmooth ν H).real (Set.Iic (x + a)) + η) + τ) -
              ν.real (Set.Iic x) := by linarith
      _ ≤ ((ν.real (Set.Iic (x + 2 * a)) + τ) + η + τ) -
              ν.real (Set.Iic x) := by linarith
      _ ≤ η + 2 * τ + 2 * lam * a := by
            nlinarith
  · have hμ_shift :
        (polyaSmooth μ H).real (Set.Iic (x - a)) ≤
      μ.real (Set.Iic x) + τ :=
      (conv_cdf_shift_le_cdf_add_tail μ H (a := a) (x := x)).trans (by
        simp
        linarith)
    have hsm :
        (polyaSmooth ν H).real (Set.Iic (x - a)) ≤
          (polyaSmooth μ H).real (Set.Iic (x - a)) + η := by
      have h := hSmooth (x - a)
      have h' :
          |(polyaSmooth ν H).real (Set.Iic (x - a)) -
            (polyaSmooth μ H).real (Set.Iic (x - a))| ≤ η := by
        simpa [abs_sub_comm] using h
      exact (sub_le_iff_le_add'.mp (le_trans (le_abs_self _) h'))
    have hν_shift :
        ν.real (Set.Iic (x - 2 * a)) ≤
          (polyaSmooth ν H).real (Set.Iic (x - a)) + τ := by
      have h :=
        conv_cdf_le_shift_add_tail ν H (a := a) (x := x - 2 * a)
      have hrewrite : x - 2 * a + a = x - a := by ring
      have h' :
          ν.real (Set.Iic (x - 2 * a)) ≤
            (polyaSmooth ν H).real (Set.Iic (x - a)) + H.real (absTailSet a) := by
        simpa [polyaSmooth, hrewrite] using h
      exact h'.trans (by linarith)
    have hlip :
        ν.real (Set.Iic x) - ν.real (Set.Iic (x - 2 * a)) ≤
          lam * (2 * a) := by
      have hxle : x - 2 * a ≤ x := by nlinarith
      have h := hLip (x - 2 * a) x hxle
      simpa using h
    calc
      ν.real (Set.Iic x) - μ.real (Set.Iic x)
          ≤ ν.real (Set.Iic x) -
              ((polyaSmooth μ H).real (Set.Iic (x - a)) - τ) := by
            linarith
      _ ≤ ν.real (Set.Iic x) -
              (((polyaSmooth ν H).real (Set.Iic (x - a)) - η) - τ) := by
            linarith
      _ ≤ ν.real (Set.Iic x) -
              ((ν.real (Set.Iic (x - 2 * a)) - τ) - η - τ) := by
            linarith
      _ ≤ η + 2 * τ + 2 * lam * a := by
            nlinarith

end ConvolutionSmoothing

section EsseenBudget

/-- The tail/Lipschitz budget `24 λ / (π L)` in Durrett's Polya smoothing
lemma. -/
def polyaTailBudget (lam L : ℝ) : ℝ :=
  24 * lam / (Real.pi * L)

/-- The abstract Esseen smoothing budget `2 η_L + 24 λ/(π L)`. -/
def esseenSmoothingBudget (lam L ηL : ℝ) : ℝ :=
  2 * ηL + polyaTailBudget lam L

/-- The Fourier version after applying inversion:
`π⁻¹ ∫ |φ-ψ|/|θ| + 24λ/(πL)`. -/
def esseenFourierBudget (μ ν : Measure ℝ) (lam L : ℝ) : ℝ :=
  (1 / Real.pi) * fourierDistanceIntegral μ ν L + polyaTailBudget lam L

lemma polyaTailBudget_nonneg {lam L : ℝ} (hlam : 0 ≤ lam) (hL : 0 < L) :
    0 ≤ polyaTailBudget lam L := by
  unfold polyaTailBudget
  exact div_nonneg (mul_nonneg (by norm_num) hlam)
    (mul_nonneg Real.pi_pos.le hL.le)

lemma esseenSmoothingBudget_nonneg {lam L ηL : ℝ}
    (hlam : 0 ≤ lam) (hL : 0 < L) (hη : 0 ≤ ηL) :
    0 ≤ esseenSmoothingBudget lam L ηL := by
  unfold esseenSmoothingBudget
  exact add_nonneg (mul_nonneg (by norm_num) hη)
    (polyaTailBudget_nonneg hlam hL)

lemma esseenFourierBudget_nonneg {μ ν : Measure ℝ} {lam L : ℝ}
    (hlam : 0 ≤ lam) (hL : 0 < L) :
    0 ≤ esseenFourierBudget μ ν lam L := by
  unfold esseenFourierBudget
  exact add_nonneg
    (mul_nonneg (by positivity) (fourierDistanceIntegral_nonneg μ ν L))
    (polyaTailBudget_nonneg hlam hL)

lemma esseenFourierBudget_polyaSmooth_le
    (μ ν H : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {lam L : ℝ} (hL : 0 < L) (hH : IsPolyaKernelMeasure H L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    esseenFourierBudget (polyaSmooth μ H) (polyaSmooth ν H) lam L ≤
      esseenFourierBudget μ ν lam L := by
  unfold esseenFourierBudget
  have hcoef : 0 ≤ (1 / Real.pi : ℝ) := by positivity
  have hI :
      fourierDistanceIntegral (polyaSmooth μ H) (polyaSmooth ν H) L ≤
        fourierDistanceIntegral μ ν L :=
    fourierDistanceIntegral_polyaSmooth_le μ ν H hL hH hOrigInt
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right
      (mul_le_mul_of_nonneg_left hI hcoef)
      (polyaTailBudget lam L)

lemma esseenSmoothingBudget_inversion_eq_fourier
    (I lam L : ℝ) :
    esseenSmoothingBudget lam L ((1 / (2 * Real.pi)) * I) =
      (1 / Real.pi) * I + polyaTailBudget lam L := by
  unfold esseenSmoothingBudget
  field_simp [Real.pi_ne_zero]

/-- The distribution-function step supplied by Esseen's Polya smoothing lemma:
if the smoothed CDFs differ by at most `ηL`, then the original CDFs differ by
at most `2 ηL + 24 λ/(πL)`. -/
def esseenSmoothingStep (μ ν H : Measure ℝ) (lam L : ℝ) : Prop :=
  ∀ ηL : ℝ,
    measureCDFErrorLE (polyaSmooth μ H) (polyaSmooth ν H) ηL →
      measureCDFErrorLE μ ν (esseenSmoothingBudget lam L ηL)

/-- A proved Esseen smoothing step from elementary convolution estimates:
if the smoothing law has two-sided tail at most `τ`, and the comparison law has
CDF Lipschitz constant `lam`, then any smoothed CDF error transfers to the
original CDFs with Durrett's smoothing budget once
`2τ + 2 lam a` is bounded by the chosen Polya budget. -/
theorem esseenSmoothingStep_of_tail_lipschitz
    {μ ν H : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure H] {lam L a τ : ℝ}
    (ha : 0 ≤ a)
    (hTail : H.real (absTailSet a) ≤ τ)
    (hLip : measureCDFLipschitz ν lam)
    (hBudget : 2 * τ + 2 * lam * a ≤ polyaTailBudget lam L) :
    esseenSmoothingStep μ ν H lam L := by
  intro ηL hSmooth
  have hη : 0 ≤ ηL := by
    exact (abs_nonneg _).trans (hSmooth 0)
  have hBound :
      measureCDFErrorLE μ ν (ηL + 2 * τ + 2 * lam * a) :=
    measureCDFErrorLE_of_conv_smoothing
      (μ := μ) (ν := ν) (H := H) ha hTail hLip hSmooth
  refine measureCDFErrorLE_mono hBound ?_
  unfold esseenSmoothingBudget
  nlinarith [hBudget, hη]

/-- Standard-normal specialization of the elementary Esseen smoothing step.
The Lipschitz hypothesis is discharged by the Gaussian density bound
`standardNormalDensity ≤ 1`. -/
theorem esseenSmoothingStep_standardNormal_of_tail
    {μ H : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure H]
    {L a τ : ℝ}
    (ha : 0 ≤ a)
    (hTail : H.real (absTailSet a) ≤ τ)
    (hBudget : 2 * τ + 2 * a ≤ polyaTailBudget 1 L) :
    esseenSmoothingStep μ standardNormalMeasure H 1 L := by
  refine esseenSmoothingStep_of_tail_lipschitz
    (μ := μ) (ν := standardNormalMeasure) (H := H)
    (lam := 1) (L := L) (a := a) (τ := τ)
    ha hTail standardNormal_measureCDFLipschitz ?_
  nlinarith [hBudget]

/-- Standard-normal smoothing step using the explicit inverse-square Polya
tail envelope.  The only measure-specific hypothesis is the two-sided tail
domination by `2 ∫_a^∞ 2/(π L x²) dx`; the integral is evaluated locally as
`4/(π L a)`. -/
theorem esseenSmoothingStep_standardNormal_of_tail_envelope
    {μ H : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure H]
    {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a)
    (hTail :
      H.real (absTailSet a) ≤
        2 * (∫ x in Set.Ioi a, polyaTailEnvelope L x))
    (hBudget :
      2 * (4 / (Real.pi * L * a)) + 2 * a ≤ polyaTailBudget 1 L) :
    esseenSmoothingStep μ standardNormalMeasure H 1 L := by
  have hTail' :
      H.real (absTailSet a) ≤ 4 / (Real.pi * L * a) := by
    rw [two_mul_integral_Ioi_polyaTailEnvelope hL ha] at hTail
    exact hTail
  exact esseenSmoothingStep_standardNormal_of_tail
    (μ := μ) (H := H) (L := L) (a := a)
    (τ := 4 / (Real.pi * L * a))
    ha.le hTail' hBudget

/-- Standard-normal smoothing step for the concrete Polya density measure.
The density-level two-sided tail estimate and mass-one theorem are discharged
locally. -/
theorem esseenSmoothingStep_standardNormal_polyaKernelMeasure
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {L a : ℝ} (hL : 0 < L) (ha : 0 < a)
    (hBudget :
      2 * (4 / (Real.pi * L * a)) + 2 * a ≤ polyaTailBudget 1 L) :
    esseenSmoothingStep μ standardNormalMeasure (polyaKernelMeasure L) 1 L := by
  letI : IsProbabilityMeasure (polyaKernelMeasure L) :=
    isProbabilityMeasure_polyaKernelMeasure hL
  exact esseenSmoothingStep_standardNormal_of_tail_envelope
    (μ := μ) (H := polyaKernelMeasure L) (L := L) (a := a)
    hL ha
    (polyaKernelMeasure_real_absTailSet_le_two_mul_integral_tailEnvelope hL ha)
    hBudget

/-- Esseen's smoothing chain once the Polya smoothing lemma and the inversion
formula for the smoothed laws are available. -/
theorem esseenFourierSmoothing_from_inversion
    {μ ν H : Measure ℝ} {lam L : ℝ}
    (hSmooth : esseenSmoothingStep μ ν H lam L)
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth μ H) (polyaSmooth ν H)
        (charFun (polyaSmooth μ H)) (charFun (polyaSmooth ν H)) L) :
    measureCDFErrorLE μ ν
      (esseenFourierBudget (polyaSmooth μ H) (polyaSmooth ν H) lam L) := by
  have hInvBound :
      measureCDFErrorLE (polyaSmooth μ H) (polyaSmooth ν H)
        ((1 / (2 * Real.pi)) *
          fourierDistanceIntegral (polyaSmooth μ H) (polyaSmooth ν H) L) :=
    measureCDFErrorLE_of_measure_inversionCDFFormula hInv
  have h :=
    hSmooth
      ((1 / (2 * Real.pi)) *
        fourierDistanceIntegral (polyaSmooth μ H) (polyaSmooth ν H) L)
      hInvBound
  rw [esseenFourierBudget,
    ← esseenSmoothingBudget_inversion_eq_fourier
      (fourierDistanceIntegral (polyaSmooth μ H) (polyaSmooth ν H) L) lam L]
  simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using h

/-- Esseen's smoothing chain with a Polya kernel, stated using the original
Fourier distance rather than the Fourier distance after smoothing. -/
theorem esseenFourierSmoothing_from_inversion_polya
    {μ ν H : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {lam L : ℝ} (hL : 0 < L) (hH : IsPolyaKernelMeasure H L)
    (hSmooth : esseenSmoothingStep μ ν H lam L)
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth μ H) (polyaSmooth ν H)
        (charFun (polyaSmooth μ H)) (charFun (polyaSmooth ν H)) L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ ν (esseenFourierBudget μ ν lam L) := by
  exact measureCDFErrorLE_mono
    (esseenFourierSmoothing_from_inversion hSmooth hInv)
    (esseenFourierBudget_polyaSmooth_le μ ν H hL hH hOrigInt)

/-- Esseen's Polya/Fourier smoothing chain with the Durrett/Feller smoothed
inversion identity discharged locally.  The remaining analytic side
conditions are finite first moments and the original truncated Fourier
integrability. -/
theorem esseenFourierSmoothing_from_integrable_polya
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {lam L : ℝ} (hL : 0 < L)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hν1 : Integrable (fun x : ℝ => x) ν)
    (hSmooth :
      esseenSmoothingStep μ ν (polyaKernelMeasure L) lam L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ ν (esseenFourierBudget μ ν lam L) := by
  have hH : IsPolyaKernelMeasure (polyaKernelMeasure L) L :=
    isPolyaKernelMeasure_polyaKernelMeasure hL
  letI : IsProbabilityMeasure (polyaKernelMeasure L) := hH.probability
  have hInv :
      inversionCDFFormulaFor
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L))
        (charFun (polyaSmooth μ (polyaKernelMeasure L)))
        (charFun (polyaSmooth ν (polyaKernelMeasure L))) L :=
    inversionCDFFormulaFor_polyaSmooth_polyaKernelMeasure_of_integrable
      (μ := μ) (ν := ν) (L := L) hL hμ1 hν1 hOrigInt
  exact esseenFourierSmoothing_from_inversion_polya
    (μ := μ) (ν := ν) (H := polyaKernelMeasure L)
    (lam := lam) (L := L) hL hH hSmooth hInv hOrigInt

/-- Sharp Esseen/Fourier smoothing from smoothed inversion, using the
least-error form of Durrett's Polya smoothing lemma for the concrete Polya
kernel.  This gives the book's `π⁻¹` Fourier coefficient and
`24λ/(πL)` smoothing term once the smoothed inversion identity is supplied. -/
theorem esseenFourierSmoothing_from_inversion_polya_isLeast
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {lam L η : ℝ} (hL : 0 < L) (hlam : 0 < lam) (hη : 0 < η)
    (hLip : measureCDFLipschitz ν lam)
    (hLeast : measureCDFErrorIsLeast μ ν η)
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L))
        (charFun (polyaSmooth μ (polyaKernelMeasure L)))
        (charFun (polyaSmooth ν (polyaKernelMeasure L))) L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ ν (esseenFourierBudget μ ν lam L) := by
  let H : Measure ℝ := polyaKernelMeasure L
  letI : IsProbabilityMeasure H := by
    dsimp [H]
    exact isProbabilityMeasure_polyaKernelMeasure hL
  let ηL : ℝ :=
    (1 / (2 * Real.pi)) *
      fourierDistanceIntegral (polyaSmooth μ H) (polyaSmooth ν H) L
  have hInvBound :
      measureCDFErrorLE (polyaSmooth μ H) (polyaSmooth ν H) ηL := by
    dsimp [ηL, H]
    exact measureCDFErrorLE_of_measure_inversionCDFFormula hInv
  have hSharp :
      measureCDFErrorLE μ ν (esseenSmoothingBudget lam L ηL) := by
    have h :=
      measureCDFErrorLE_of_polyaSmooth_error_isLeast
        (μ := μ) (ν := ν) (L := L) (lam := lam) (η := η) (ηL := ηL)
        hL hlam hη hLip hLeast hInvBound
    simpa [esseenSmoothingBudget, polyaTailBudget, ηL] using h
  have hSharpFourier :
      measureCDFErrorLE μ ν
        (esseenFourierBudget (polyaSmooth μ H) (polyaSmooth ν H) lam L) := by
    unfold esseenFourierBudget
    rw [← esseenSmoothingBudget_inversion_eq_fourier
      (fourierDistanceIntegral (polyaSmooth μ H) (polyaSmooth ν H) L) lam L]
    simpa [ηL] using hSharp
  have hH : IsPolyaKernelMeasure H L := by
    dsimp [H]
    exact isPolyaKernelMeasure_polyaKernelMeasure hL
  exact measureCDFErrorLE_mono hSharpFourier
    (esseenFourierBudget_polyaSmooth_le μ ν H hL hH hOrigInt)

/-- Sharp Esseen/Fourier smoothing from smoothed inversion, using the
constructed supremum `measureCDFErrorSup` rather than an externally supplied
least-error witness.  The remaining analytic input is the smoothed inversion
identity. -/
theorem esseenFourierSmoothing_from_inversion_polya_sup
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {lam L : ℝ} (hL : 0 < L) (hlam : 0 < lam)
    (hLip : measureCDFLipschitz ν lam)
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L))
        (charFun (polyaSmooth μ (polyaKernelMeasure L)))
        (charFun (polyaSmooth ν (polyaKernelMeasure L))) L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ ν (esseenFourierBudget μ ν lam L) := by
  let H : Measure ℝ := polyaKernelMeasure L
  letI : IsProbabilityMeasure H := by
    dsimp [H]
    exact isProbabilityMeasure_polyaKernelMeasure hL
  let ηL : ℝ :=
    (1 / (2 * Real.pi)) *
      fourierDistanceIntegral (polyaSmooth μ H) (polyaSmooth ν H) L
  have hInvBound :
      measureCDFErrorLE (polyaSmooth μ H) (polyaSmooth ν H) ηL := by
    dsimp [ηL, H]
    exact measureCDFErrorLE_of_measure_inversionCDFFormula hInv
  have hSharp :
      measureCDFErrorLE μ ν (esseenSmoothingBudget lam L ηL) := by
    have h :=
      measureCDFErrorLE_of_polyaSmooth_error_sup
        (μ := μ) (ν := ν) (L := L) (lam := lam) (ηL := ηL)
        hL hlam hLip hInvBound
    simpa [esseenSmoothingBudget, polyaTailBudget, ηL] using h
  have hSharpFourier :
      measureCDFErrorLE μ ν
        (esseenFourierBudget (polyaSmooth μ H) (polyaSmooth ν H) lam L) := by
    unfold esseenFourierBudget
    rw [← esseenSmoothingBudget_inversion_eq_fourier
      (fourierDistanceIntegral (polyaSmooth μ H) (polyaSmooth ν H) L) lam L]
    simpa [ηL] using hSharp
  have hH : IsPolyaKernelMeasure H L := by
    dsimp [H]
    exact isPolyaKernelMeasure_polyaKernelMeasure hL
  exact measureCDFErrorLE_mono hSharpFourier
    (esseenFourierBudget_polyaSmooth_le μ ν H hL hH hOrigInt)

/-- Standard-normal version of the Polya/Fourier smoothing chain.  The only
remaining smoothing-side input is the concrete Polya tail estimate. -/
theorem esseenFourierSmoothing_standardNormal_from_tail_inversion_polya
    {μ H : Measure ℝ} [IsProbabilityMeasure μ]
    {L a τ : ℝ} (hL : 0 < L) (hH : IsPolyaKernelMeasure H L)
    (ha : 0 ≤ a)
    (hTail : H.real (absTailSet a) ≤ τ)
    (hBudget : 2 * τ + 2 * a ≤ polyaTailBudget 1 L)
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth μ H) (polyaSmooth standardNormalMeasure H)
        (charFun (polyaSmooth μ H))
        (charFun (polyaSmooth standardNormalMeasure H)) L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun standardNormalMeasure θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ standardNormalMeasure
      (esseenFourierBudget μ standardNormalMeasure 1 L) := by
  letI : IsProbabilityMeasure H := hH.probability
  have hSmooth :
      esseenSmoothingStep μ standardNormalMeasure H 1 L :=
    esseenSmoothingStep_standardNormal_of_tail
      (μ := μ) (H := H) (L := L) (a := a) (τ := τ)
      ha hTail hBudget
  exact esseenFourierSmoothing_from_inversion_polya
    (μ := μ) (ν := standardNormalMeasure) (H := H)
    (lam := 1) (L := L) hL hH hSmooth hInv hOrigInt

/-- Standard-normal Polya/Fourier smoothing chain for the concrete Polya
density measure.  The density tail, mass-one theorem, and triangular
characteristic function are all discharged locally. -/
theorem esseenFourierSmoothing_standardNormal_polyaKernelMeasure_from_inversion
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {L a : ℝ} (hL : 0 < L)
    (ha : 0 < a)
    (hBudget :
      2 * (4 / (Real.pi * L * a)) + 2 * a ≤ polyaTailBudget 1 L)
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))
        (charFun (polyaSmooth μ (polyaKernelMeasure L)))
        (charFun (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))) L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun standardNormalMeasure θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ standardNormalMeasure
      (esseenFourierBudget μ standardNormalMeasure 1 L) := by
  have hH : IsPolyaKernelMeasure (polyaKernelMeasure L) L :=
    isPolyaKernelMeasure_polyaKernelMeasure hL
  letI : IsProbabilityMeasure (polyaKernelMeasure L) := hH.probability
  have hSmooth :
      esseenSmoothingStep μ standardNormalMeasure (polyaKernelMeasure L) 1 L :=
    esseenSmoothingStep_standardNormal_polyaKernelMeasure
      (μ := μ) (L := L) (a := a) hL ha hBudget
  exact esseenFourierSmoothing_from_inversion_polya
    (μ := μ) (ν := standardNormalMeasure) (H := polyaKernelMeasure L)
    (lam := 1) (L := L) hL hH hSmooth hInv hOrigInt

/-- Standard-normal specialization of the sharp least-error Polya/Fourier
smoothing chain.  The only remaining analytic input is the smoothed inversion
identity for the concrete Polya-smoothed laws. -/
theorem esseenFourierSmoothing_standardNormal_polyaKernelMeasure_from_inversion_isLeast
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hLeast : measureCDFErrorIsLeast μ standardNormalMeasure η)
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))
        (charFun (polyaSmooth μ (polyaKernelMeasure L)))
        (charFun (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))) L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun standardNormalMeasure θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ standardNormalMeasure
      (esseenFourierBudget μ standardNormalMeasure 1 L) := by
  exact esseenFourierSmoothing_from_inversion_polya_isLeast
    (μ := μ) (ν := standardNormalMeasure) (lam := 1) (L := L) (η := η)
    hL (by norm_num) hη standardNormal_measureCDFLipschitz hLeast hInv hOrigInt

/-- Standard-normal specialization of the supremum-form Polya/Fourier
smoothing chain.  This removes the least-error parameter from the interface;
only smoothed inversion and the original Fourier integral remain. -/
theorem esseenFourierSmoothing_standardNormal_polyaKernelMeasure_from_inversion_sup
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {L : ℝ} (hL : 0 < L)
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))
        (charFun (polyaSmooth μ (polyaKernelMeasure L)))
        (charFun (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))) L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun standardNormalMeasure θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ standardNormalMeasure
      (esseenFourierBudget μ standardNormalMeasure 1 L) := by
  exact esseenFourierSmoothing_from_inversion_polya_sup
    (μ := μ) (ν := standardNormalMeasure) (lam := 1) (L := L)
    hL (by norm_num) standardNormal_measureCDFLipschitz hInv hOrigInt

/-- Standard-normal Polya/Fourier smoothing chain using the explicit
inverse-square envelope for Polya's tail. -/
theorem esseenFourierSmoothing_standardNormal_from_tail_envelope_inversion_polya
    {μ H : Measure ℝ} [IsProbabilityMeasure μ]
    {L a : ℝ} (hL : 0 < L) (hH : IsPolyaKernelMeasure H L)
    (ha : 0 < a)
    (hTail :
      H.real (absTailSet a) ≤
        2 * (∫ x in Set.Ioi a, polyaTailEnvelope L x))
    (hBudget :
      2 * (4 / (Real.pi * L * a)) + 2 * a ≤ polyaTailBudget 1 L)
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth μ H) (polyaSmooth standardNormalMeasure H)
        (charFun (polyaSmooth μ H))
        (charFun (polyaSmooth standardNormalMeasure H)) L)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun standardNormalMeasure θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ standardNormalMeasure
      (esseenFourierBudget μ standardNormalMeasure 1 L) := by
  letI : IsProbabilityMeasure H := hH.probability
  have hSmooth :
      esseenSmoothingStep μ standardNormalMeasure H 1 L :=
    esseenSmoothingStep_standardNormal_of_tail_envelope
      (μ := μ) (H := H) (L := L) (a := a)
      hL ha hTail hBudget
  exact esseenFourierSmoothing_from_inversion_polya
    (μ := μ) (ν := standardNormalMeasure) (H := H)
    (lam := 1) (L := L) hL hH hSmooth hInv hOrigInt

end EsseenBudget

section DurrettConstants

/-- Durrett's final integral constant:
`2 ∫_0^∞ x^3 exp(-x^2/4) dx = 16`.  This is the normalized value before the
last numerical simplification in the Berry-Esseen proof. -/
lemma integral_Ioi_cube_exp_neg_sq_div_four :
    ∫ x in Set.Ioi (0 : ℝ),
      x ^ (3 : ℝ) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℝ)) = 8 := by
  have h :=
    integral_rpow_mul_exp_neg_mul_rpow
      (p := (2 : ℝ)) (q := (3 : ℝ)) (b := (1 / 4 : ℝ))
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (-1 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 1 / 4)
  rw [h]
  norm_num [Real.Gamma_two]

lemma two_mul_integral_Ioi_cube_exp_neg_sq_div_four :
    2 * (∫ x in Set.Ioi (0 : ℝ),
      x ^ (3 : ℝ) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℝ))) = 16 := by
  rw [integral_Ioi_cube_exp_neg_sq_div_four]
  norm_num

lemma gamma_three_halves_le_one :
    Real.Gamma (3 / 2 : ℝ) ≤ 1 := by
  have hGammaEq : Real.Gamma (3 / 2 : ℝ) = (1 / 2 : ℝ) * √Real.pi := by
    have h := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
    have hhalf : Real.Gamma (1 / 2 : ℝ) = √Real.pi := Real.Gamma_one_half_eq
    norm_num at h ⊢
    rw [h, hhalf]
  rw [hGammaEq]
  have hsqrt_pi_le_two : √Real.pi ≤ 2 := by
    have hpi : Real.pi < (2 : ℝ) ^ 2 := by
      norm_num
      exact Real.pi_lt_four
    exact ((Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).mpr hpi).le
  nlinarith [hsqrt_pi_le_two]

lemma gamma_three_halves_le_nine_tenths :
    Real.Gamma (3 / 2 : ℝ) ≤ 9 / 10 := by
  have hGammaEq : Real.Gamma (3 / 2 : ℝ) = (1 / 2 : ℝ) * √Real.pi := by
    have h := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
    have hhalf : Real.Gamma (1 / 2 : ℝ) = √Real.pi := Real.Gamma_one_half_eq
    norm_num at h ⊢
    rw [h, hhalf]
  rw [hGammaEq]
  have hsqrt_pi_le : √Real.pi ≤ 9 / 5 := by
    have hpi : Real.pi < (9 / 5 : ℝ) ^ 2 := by
      nlinarith [Real.pi_lt_d2]
    exact ((Real.sqrt_lt' (by norm_num : (0 : ℝ) < 9 / 5)).mpr hpi).le
  nlinarith [hsqrt_pi_le]

lemma gamma_three_halves_nonneg :
    0 ≤ Real.Gamma (3 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num]
  rw [Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)]
  rw [Real.Gamma_one_half_eq]
  positivity

lemma rpow_one_eighth_neg_three_halves_le :
    (1 / 8 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 64 := by
  rw [Real.rpow_neg (by norm_num : 0 ≤ (1 / 8 : ℝ))]
  rw [← Real.inv_rpow (by norm_num : 0 ≤ (1 / 8 : ℝ))]
  norm_num
  calc
    (8 : ℝ) ^ (3 / 2 : ℝ) ≤ (8 : ℝ) ^ (2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 8)
        (by norm_num : (3 / 2 : ℝ) ≤ 2)
    _ = 64 := by norm_num [Real.rpow_natCast]

lemma rpow_one_eighth_neg_three_halves_le_twenty_four :
    (1 / 8 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 24 := by
  rw [Real.rpow_neg (by norm_num : 0 ≤ (1 / 8 : ℝ))]
  rw [← Real.inv_rpow (by norm_num : 0 ≤ (1 / 8 : ℝ))]
  norm_num
  have hpoweq : (8 : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt (8 ^ 3 : ℝ) := by
    rw [show (3 / 2 : ℝ) = (3 : ℝ) * (1 / 2 : ℝ) by norm_num]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
    rw [Real.sqrt_eq_rpow]
    norm_num [Real.rpow_natCast]
  rw [hpoweq, Real.sqrt_le_iff]
  norm_num

lemma integral_Ioi_sq_exp_neg_sq_div_eight_le :
    ∫ x in Set.Ioi (0 : ℝ),
      x ^ (2 : ℝ) * Real.exp (-(1 / 8 : ℝ) * x ^ (2 : ℝ)) ≤ 32 := by
  have h :=
    integral_rpow_mul_exp_neg_mul_rpow
      (p := (2 : ℝ)) (q := (2 : ℝ)) (b := (1 / 8 : ℝ))
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (-1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1 / 8)
  rw [h]
  norm_num
  have hmul :=
    mul_le_mul rpow_one_eighth_neg_three_halves_le
      gamma_three_halves_le_one gamma_three_halves_nonneg
      (by norm_num : (0 : ℝ) ≤ 64)
  nlinarith

lemma integral_Ioi_sq_exp_neg_sq_div_eight_le_fifty_four_fifths :
    ∫ x in Set.Ioi (0 : ℝ),
      x ^ (2 : ℝ) * Real.exp (-(1 / 8 : ℝ) * x ^ (2 : ℝ)) ≤ 54 / 5 := by
  have h :=
    integral_rpow_mul_exp_neg_mul_rpow
      (p := (2 : ℝ)) (q := (2 : ℝ)) (b := (1 / 8 : ℝ))
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (-1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1 / 8)
  rw [h]
  norm_num
  have hmul :=
    mul_le_mul rpow_one_eighth_neg_three_halves_le_twenty_four
      gamma_three_halves_le_nine_tenths gamma_three_halves_nonneg
      (by norm_num : (0 : ℝ) ≤ 24)
  nlinarith

lemma integral_univ_abs_sq_exp_neg_sq_div_eight_le :
    ∫ x : ℝ, |x| ^ 2 * Real.exp (-(1 / 8 : ℝ) * x ^ 2) ≤ 64 := by
  have hcomp :=
    integral_comp_abs
      (f := fun x : ℝ => x ^ 2 * Real.exp (-(1 / 8 : ℝ) * x ^ 2))
  have hleft :
      (∫ x : ℝ, |x| ^ 2 * Real.exp (-(1 / 8 : ℝ) * x ^ 2)) =
        ∫ x : ℝ,
          (fun y : ℝ => y ^ 2 * Real.exp (-(1 / 8 : ℝ) * y ^ 2)) |x| := by
    refine integral_congr_ae ?_
    exact Eventually.of_forall fun x => by
      simp [sq_abs]
  rw [hleft, hcomp]
  have hpos :
      ∫ x in Set.Ioi (0 : ℝ),
        x ^ 2 * Real.exp (-(1 / 8 : ℝ) * x ^ 2) ≤ 32 := by
    simpa [Real.rpow_two] using integral_Ioi_sq_exp_neg_sq_div_eight_le
  have hpos' :
      2 * (∫ x in Set.Ioi (0 : ℝ),
        x ^ 2 * Real.exp (-(1 / 8 : ℝ) * x ^ 2)) ≤ 64 := by
    nlinarith
  simpa using hpos'

lemma integral_univ_abs_sq_exp_neg_sq_div_eight_le_108_fifths :
    ∫ x : ℝ, |x| ^ 2 * Real.exp (-(1 / 8 : ℝ) * x ^ 2) ≤ 108 / 5 := by
  have hcomp :=
    integral_comp_abs
      (f := fun x : ℝ => x ^ 2 * Real.exp (-(1 / 8 : ℝ) * x ^ 2))
  have hleft :
      (∫ x : ℝ, |x| ^ 2 * Real.exp (-(1 / 8 : ℝ) * x ^ 2)) =
        ∫ x : ℝ,
          (fun y : ℝ => y ^ 2 * Real.exp (-(1 / 8 : ℝ) * y ^ 2)) |x| := by
    refine integral_congr_ae ?_
    exact Eventually.of_forall fun x => by
      simp [sq_abs]
  rw [hleft, hcomp]
  have hpos :
      ∫ x in Set.Ioi (0 : ℝ),
        x ^ 2 * Real.exp (-(1 / 8 : ℝ) * x ^ 2) ≤ 54 / 5 := by
    simpa [Real.rpow_two] using
      integral_Ioi_sq_exp_neg_sq_div_eight_le_fifty_four_fifths
  have hpos' :
      2 * (∫ x in Set.Ioi (0 : ℝ),
        x ^ 2 * Real.exp (-(1 / 8 : ℝ) * x ^ 2)) ≤ 108 / 5 := by
    nlinarith
  simpa using hpos'

lemma integral_univ_abs_cube_exp_neg_sq_div_four :
    ∫ x : ℝ, |x| ^ 3 * Real.exp (-(1 / 4 : ℝ) * x ^ 2) = 16 := by
  have hcomp :=
    integral_comp_abs
      (f := fun x : ℝ => x ^ 3 * Real.exp (-(1 / 4 : ℝ) * x ^ 2))
  have hleft :
      (∫ x : ℝ, |x| ^ 3 * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) =
        ∫ x : ℝ,
          (fun y : ℝ => y ^ 3 * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) |x| := by
    refine integral_congr_ae ?_
    exact Eventually.of_forall fun x => by
      simp [sq_abs]
  rw [hleft, hcomp]
  have hpos :
      ∫ x in Set.Ioi (0 : ℝ),
        x ^ 3 * Real.exp (-(1 / 4 : ℝ) * x ^ 2) = 8 := by
    simpa [Real.rpow_natCast] using integral_Ioi_cube_exp_neg_sq_div_four
  rw [hpos]
  norm_num

lemma rpow_one_fourth_neg_three_halves_le_eight :
    (1 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 8 := by
  rw [Real.rpow_neg (by norm_num : 0 ≤ (1 / 4 : ℝ))]
  rw [← Real.inv_rpow (by norm_num : 0 ≤ (1 / 4 : ℝ))]
  norm_num

lemma integral_Ioi_sq_exp_neg_sq_div_four_le_eighteen_fifths :
    ∫ x in Set.Ioi (0 : ℝ),
      x ^ (2 : ℝ) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℝ)) ≤ 18 / 5 := by
  have h :=
    integral_rpow_mul_exp_neg_mul_rpow
      (p := (2 : ℝ)) (q := (2 : ℝ)) (b := (1 / 4 : ℝ))
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (-1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1 / 4)
  rw [h]
  norm_num
  have hmul :=
    mul_le_mul rpow_one_fourth_neg_three_halves_le_eight
      gamma_three_halves_le_nine_tenths gamma_three_halves_nonneg
      (by norm_num : (0 : ℝ) ≤ 8)
  nlinarith

lemma integral_univ_abs_sq_exp_neg_sq_div_four_le_36_fifths :
    ∫ x : ℝ, |x| ^ 2 * Real.exp (-(1 / 4 : ℝ) * x ^ 2) ≤ 36 / 5 := by
  have hcomp :=
    integral_comp_abs
      (f := fun x : ℝ => x ^ 2 * Real.exp (-(1 / 4 : ℝ) * x ^ 2))
  have hleft :
      (∫ x : ℝ, |x| ^ 2 * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) =
        ∫ x : ℝ,
          (fun y : ℝ => y ^ 2 * Real.exp (-(1 / 4 : ℝ) * y ^ 2)) |x| := by
    refine integral_congr_ae ?_
    exact Eventually.of_forall fun x => by
      simp [sq_abs]
  rw [hleft, hcomp]
  have hpos :
      ∫ x in Set.Ioi (0 : ℝ),
        x ^ 2 * Real.exp (-(1 / 4 : ℝ) * x ^ 2) ≤ 18 / 5 := by
    simpa [Real.rpow_two] using
      integral_Ioi_sq_exp_neg_sq_div_four_le_eighteen_fifths
  have hpos' :
      2 * (∫ x in Set.Ioi (0 : ℝ),
        x ^ 2 * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) ≤ 36 / 5 := by
    nlinarith
  simpa using hpos'

lemma integrable_abs_sq_exp_neg_sq_div_four :
    Integrable
      (fun x : ℝ => |x| ^ 2 * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) := by
  have h :
      Integrable
        (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (-1 : ℝ) < 2)
  simpa [Real.rpow_two, abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_pow]
    using h.norm

lemma integrable_abs_sq_exp_neg_sq_div_eight :
    Integrable
      (fun x : ℝ => |x| ^ 2 * Real.exp (-(1 / 8 : ℝ) * x ^ 2)) := by
  have h :
      Integrable
        (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-(1 / 8 : ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (-1 : ℝ) < 2)
  simpa [Real.rpow_two, sq_abs] using h

lemma integrable_abs_cube_exp_neg_sq_div_four :
    Integrable
      (fun x : ℝ => |x| ^ 3 * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) := by
  have h :
      Integrable
        (fun x : ℝ => x ^ (3 : ℝ) * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (-1 : ℝ) < 3)
  simpa [Real.rpow_natCast, abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_pow]
    using h.norm

lemma integrable_berryEsseenDurrettFourierBound
    (μ : Measure ℝ) (n : ℕ) :
    Integrable (berryEsseenDurrettFourierBound μ n) := by
  have hsq := integrable_abs_sq_exp_neg_sq_div_four
  have hcube := integrable_abs_cube_exp_neg_sq_div_four
  unfold berryEsseenDurrettFourierBound
  change Integrable
    (fun t : ℝ =>
      (((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ))) *
        Real.exp (-(1 / 4 : ℝ) * t ^ 2)))
  rw [show
      (fun t : ℝ =>
        (((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
              Real.sqrt ((n + 1 : ℕ) : ℝ) +
            |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ))) *
          Real.exp (-(1 / 4 : ℝ) * t ^ 2))) =
      (fun t : ℝ =>
        (((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
              Real.sqrt ((n + 1 : ℕ) : ℝ)) *
            (|t| ^ 2 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) +
          (1 / (8 * ((n + 1 : ℕ) : ℝ))) *
            (|t| ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)))) by
        funext t
        ring]
  exact
    (hsq.const_mul
      ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ))).add
      (hcube.const_mul (1 / (8 * ((n + 1 : ℕ) : ℝ))))

/-- Integrated Durrett/Feller Fourier majorant. -/
lemma integral_berryEsseenDurrettFourierBound_le
    (μ : Measure ℝ) (n : ℕ) :
    ∫ t : ℝ, berryEsseenDurrettFourierBound μ n t ≤
      (6 / 5) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
  have hsq := integrable_abs_sq_exp_neg_sq_div_four
  have hcube := integrable_abs_cube_exp_neg_sq_div_four
  have hM : 0 ≤ ∫ x, |x| ^ 3 ∂μ := integral_abs_cube_nonneg μ
  have hN_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr hN_pos
  unfold berryEsseenDurrettFourierBound
  change
    ∫ t : ℝ,
      (((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ))) *
        Real.exp (-(1 / 4 : ℝ) * t ^ 2)) ≤
      (6 / 5) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ)
  rw [show
      (fun t : ℝ =>
        (((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
              Real.sqrt ((n + 1 : ℕ) : ℝ) +
            |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ))) *
          Real.exp (-(1 / 4 : ℝ) * t ^ 2))) =
      (fun t : ℝ =>
        (((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
              Real.sqrt ((n + 1 : ℕ) : ℝ)) *
            (|t| ^ 2 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) +
          (1 / (8 * ((n + 1 : ℕ) : ℝ))) *
            (|t| ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)))) by
        funext t
        ring]
  rw [integral_add
    (hsq.const_mul
      ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ)))
    (hcube.const_mul (1 / (8 * ((n + 1 : ℕ) : ℝ))))]
  rw [integral_const_mul, integral_const_mul]
  have hcoef1_nonneg :
      0 ≤ (1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    positivity
  have hfirst :
      ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ)) *
        (∫ t : ℝ, |t| ^ 2 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) ≤
      (6 / 5) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    have h :=
      mul_le_mul_of_nonneg_left
        integral_univ_abs_sq_exp_neg_sq_div_four_le_36_fifths
        hcoef1_nonneg
    have heq :
        ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
            Real.sqrt ((n + 1 : ℕ) : ℝ)) * (36 / 5) =
          (6 / 5) * (∫ x, |x| ^ 3 ∂μ) /
            Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      ring
    exact h.trans_eq heq
  have hsecond :
      (1 / (8 * ((n + 1 : ℕ) : ℝ))) *
        (∫ t : ℝ, |t| ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) ≤
      2 / ((n + 1 : ℕ) : ℝ) := by
    rw [integral_univ_abs_cube_exp_neg_sq_div_four]
    field_simp [hN_pos.ne']
    norm_num
  exact add_le_add hfirst hsecond

lemma integral_Icc_berryEsseenDurrettFourierBound_le
    (μ : Measure ℝ) (n : ℕ) (L : ℝ) :
    ∫ t in Set.Icc (-L) L, berryEsseenDurrettFourierBound μ n t ≤
      (6 / 5) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
  have hsq := integrable_abs_sq_exp_neg_sq_div_four
  have hcube := integrable_abs_cube_exp_neg_sq_div_four
  have hBoundInt : Integrable (berryEsseenDurrettFourierBound μ n) := by
    unfold berryEsseenDurrettFourierBound
    change Integrable
      (fun t : ℝ =>
        (((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
              Real.sqrt ((n + 1 : ℕ) : ℝ) +
            |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ))) *
          Real.exp (-(1 / 4 : ℝ) * t ^ 2)))
    rw [show
        (fun t : ℝ =>
          (((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
                Real.sqrt ((n + 1 : ℕ) : ℝ) +
              |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ))) *
            Real.exp (-(1 / 4 : ℝ) * t ^ 2))) =
        (fun t : ℝ =>
          (((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
                Real.sqrt ((n + 1 : ℕ) : ℝ)) *
              (|t| ^ 2 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) +
            (1 / (8 * ((n + 1 : ℕ) : ℝ))) *
              (|t| ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)))) by
          funext t
          ring]
    exact
      (hsq.const_mul
        ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ))).add
        (hcube.const_mul (1 / (8 * ((n + 1 : ℕ) : ℝ))))
  -- The global Gaussian majorants are integrable, so it is enough to use
  -- the nonnegative set-integral comparison against the whole-space integral.
  have hSet :
      ∫ t in Set.Icc (-L) L, berryEsseenDurrettFourierBound μ n t ≤
        ∫ t : ℝ, berryEsseenDurrettFourierBound μ n t := by
    conv_rhs => rw [← setIntegral_univ]
    exact setIntegral_mono_set hBoundInt.integrableOn
      (Eventually.of_forall fun t => berryEsseenDurrettFourierBound_nonneg μ n t)
      (Eventually.of_forall fun t _ht => Set.mem_univ t)
  exact hSet.trans (integral_berryEsseenDurrettFourierBound_le μ n)

def berryEsseenUniformFourierBound (μ : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
      Real.sqrt ((n + 1 : ℕ) : ℝ)) *
      (|t| ^ 2 * Real.exp (-(1 / 8 : ℝ) * t ^ 2)) +
    (1 / (8 * ((n + 1 : ℕ) : ℝ))) *
      (|t| ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2))

lemma berryEsseenUniformFourierBound_nonneg
    (μ : Measure ℝ) (n : ℕ) (t : ℝ) :
    0 ≤ berryEsseenUniformFourierBound μ n t := by
  have hM : 0 ≤ ∫ x, |x| ^ 3 ∂μ := integral_abs_cube_nonneg μ
  unfold berryEsseenUniformFourierBound
  positivity

lemma integrable_berryEsseenUniformFourierBound
    (μ : Measure ℝ) (n : ℕ) :
    Integrable (berryEsseenUniformFourierBound μ n) := by
  have hsq := integrable_abs_sq_exp_neg_sq_div_eight
  have hcube := integrable_abs_cube_exp_neg_sq_div_four
  change Integrable
    (fun t : ℝ =>
      ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ)) *
          (|t| ^ 2 * Real.exp (-(1 / 8 : ℝ) * t ^ 2)) +
        (1 / (8 * ((n + 1 : ℕ) : ℝ))) *
          (|t| ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)))
  exact
    (hsq.const_mul
      ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ))).add
      (hcube.const_mul (1 / (8 * ((n + 1 : ℕ) : ℝ))))

lemma berryEsseen_exp_scaled_pow_le_exp_neg_sq_div_eight
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (Real.exp (-((t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2) / 4)) ^ n ≤
      Real.exp (-(1 / 8 : ℝ) * t ^ 2) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp_arg : -((t / Real.sqrt N) ^ 2) / 4 = -(t ^ 2 / (4 * N)) := by
    rw [div_pow, Real.sq_sqrt hN_pos.le]
    ring
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  rw [hexp_arg]
  have hN_eq : N = (n : ℝ) + 1 := by
    dsimp [N]
    norm_num
  rw [hN_eq]
  have hcoef : (1 / 8 : ℝ) ≤ (n : ℝ) / (4 * ((n : ℝ) + 1)) := by
    have hden : 0 < 4 * ((n : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hden]
    nlinarith [hnR]
  have hsq : 0 ≤ t ^ 2 := sq_nonneg t
  have hmul := mul_le_mul_of_nonneg_right hcoef hsq
  have heq :
      (n : ℝ) * -(t ^ 2 / (4 * ((n : ℝ) + 1))) =
        -(((n : ℝ) / (4 * ((n : ℝ) + 1))) * t ^ 2) := by
    ring
  rw [heq]
  nlinarith

lemma berryEsseen_exp_quadratic_pow_le_exp_neg_sq_div_four
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (Real.exp (-(t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))))) ^ n ≤
      Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hcoef : (1 / 4 : ℝ) ≤ (n : ℝ) / (2 * ((n : ℝ) + 1)) := by
    have hden : 0 < 2 * ((n : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hden]
    nlinarith [hnR]
  have hsq : 0 ≤ t ^ 2 := sq_nonneg t
  have hmul := mul_le_mul_of_nonneg_right hcoef hsq
  have heq :
      (n : ℝ) * -(t ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))) =
        -(((n : ℝ) / (2 * ((n : ℝ) + 1))) * t ^ 2) := by
    norm_num
    ring
  rw [heq]
  nlinarith

lemma berryEsseenDampedFourierBound_le_uniform
    (μ : Measure ℝ) {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    berryEsseenDampedFourierBound μ n t ≤
      berryEsseenUniformFourierBound μ n t := by
  have hM : 0 ≤ ∫ x, |x| ^ 3 ∂μ := integral_abs_cube_nonneg μ
  unfold berryEsseenDampedFourierBound berryEsseenUniformFourierBound
  rw [show
      ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ)) *
          (|t| ^ 2 * Real.exp (-(1 / 8 : ℝ) * t ^ 2)) =
        (1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
          Real.sqrt ((n + 1 : ℕ) : ℝ) *
          Real.exp (-(1 / 8 : ℝ) * t ^ 2) by ring]
  rw [show
      (1 / (8 * ((n + 1 : ℕ) : ℝ))) *
          (|t| ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) =
        |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ)) *
          Real.exp (-(1 / 4 : ℝ) * t ^ 2) by ring]
  gcongr
  · exact berryEsseen_exp_scaled_pow_le_exp_neg_sq_div_eight hn t
  · exact berryEsseen_exp_quadratic_pow_le_exp_neg_sq_div_four hn t

lemma integral_berryEsseenUniformFourierBound_le
    (μ : Measure ℝ) (n : ℕ) :
    ∫ t : ℝ, berryEsseenUniformFourierBound μ n t ≤
      (18 / 5) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
  have hsq := integrable_abs_sq_exp_neg_sq_div_eight
  have hcube := integrable_abs_cube_exp_neg_sq_div_four
  have hM : 0 ≤ ∫ x, |x| ^ 3 ∂μ := integral_abs_cube_nonneg μ
  have hN_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  unfold berryEsseenUniformFourierBound
  rw [integral_add
    (hsq.const_mul
      ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ)))
    (hcube.const_mul (1 / (8 * ((n + 1 : ℕ) : ℝ))))]
  rw [integral_const_mul, integral_const_mul]
  have hcoef1_nonneg :
      0 ≤ (1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
        Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    positivity
  have hcoef2_nonneg :
      0 ≤ (1 / (8 * ((n + 1 : ℕ) : ℝ)) : ℝ) := by
    positivity
  have hfirst :
      ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ)) *
        (∫ t : ℝ, |t| ^ 2 * Real.exp (-(1 / 8 : ℝ) * t ^ 2)) ≤
      (18 / 5) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    have h :=
      mul_le_mul_of_nonneg_left
        integral_univ_abs_sq_exp_neg_sq_div_eight_le_108_fifths
        hcoef1_nonneg
    have heq :
        ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) /
            Real.sqrt ((n + 1 : ℕ) : ℝ)) * (108 / 5) =
          (18 / 5) * (∫ x, |x| ^ 3 ∂μ) /
            Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      ring
    exact h.trans_eq heq
  have hsecond :
      (1 / (8 * ((n + 1 : ℕ) : ℝ))) *
        (∫ t : ℝ, |t| ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) ≤
      2 / ((n + 1 : ℕ) : ℝ) := by
    rw [integral_univ_abs_cube_exp_neg_sq_div_four]
    field_simp [hN_pos.ne']
    norm_num
  exact add_le_add hfirst hsecond

lemma integral_Icc_berryEsseenDampedFourierBound_le
    (μ : Measure ℝ) {n : ℕ} (hn : 1 ≤ n) (L : ℝ) :
    ∫ t in Set.Icc (-L) L, berryEsseenDampedFourierBound μ n t ≤
      (18 / 5) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
  have hDampedInt :
      IntegrableOn (berryEsseenDampedFourierBound μ n) (Set.Icc (-L) L) :=
    integrableOn_berryEsseenDampedFourierBound μ n L
  have hUniformInt : Integrable (berryEsseenUniformFourierBound μ n) :=
    integrable_berryEsseenUniformFourierBound μ n
  have hIcc :
      ∫ t in Set.Icc (-L) L, berryEsseenDampedFourierBound μ n t ≤
        ∫ t in Set.Icc (-L) L, berryEsseenUniformFourierBound μ n t := by
    exact setIntegral_mono_on hDampedInt hUniformInt.integrableOn measurableSet_Icc
      (fun t _ht => berryEsseenDampedFourierBound_le_uniform μ hn t)
  have hSet :
      ∫ t in Set.Icc (-L) L, berryEsseenUniformFourierBound μ n t ≤
        ∫ t : ℝ, berryEsseenUniformFourierBound μ n t := by
    conv_rhs => rw [← setIntegral_univ]
    exact setIntegral_mono_set hUniformInt.integrableOn
      (Eventually.of_forall fun t => berryEsseenUniformFourierBound_nonneg μ n t)
      (Eventually.of_forall fun t _ht => Set.mem_univ t)
  exact hIcc.trans (hSet.trans (integral_berryEsseenUniformFourierBound_le μ n))

/-- Fully integrated central-window Fourier estimate for the Durrett/Feller
Berry-Esseen proof.  The hypotheses `hWindow` and `hSmall` are exactly the
window restrictions needed by the pointwise Taylor/decay estimate. -/
lemma fourierDistanceIntegralOfFns_scaled_pow_succ_standardNormal_le_rate
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * (∫ x, |x| ^ 3 ∂μ) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    fourierDistanceIntegralOfFns
      (fun t : ℝ =>
        charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1))
      (charFun standardNormalMeasure) L ≤
      (18 / 5) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
  exact
    (fourierDistanceIntegralOfFns_scaled_pow_succ_standardNormal_le_dampedBound
      (μ := μ) h3 hmean hsecond n hWindow hSmall).trans
      (integral_Icc_berryEsseenDampedFourierBound_le μ hn L)

/-- Fully integrated Durrett/Feller Fourier estimate on the larger window
`t² ≤ 2N`, valid for `N = n+1 ≥ 10`. -/
lemma fourierDistanceIntegralOfFns_scaled_pow_succ_standardNormal_le_durrett_rate
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {n : ℕ} (hn : 9 ≤ n) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (∫ x, |x| ^ 3 ∂μ) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    fourierDistanceIntegralOfFns
      (fun t : ℝ =>
        charFun μ (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1))
      (charFun standardNormalMeasure) L ≤
      (6 / 5) * (∫ x, |x| ^ 3 ∂μ) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
  exact
    (fourierDistanceIntegralOfFns_scaled_pow_succ_standardNormal_le_durrettBound
      (μ := μ) h3 hmean hsecond hn hWindow hSmall).trans
      (integral_Icc_berryEsseenDurrettFourierBound_le μ n L)

/-- A centered finite third absolute moment implies integrability of the
original variable. -/
lemma integrable_of_integrable_centered_abs_cube
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Y : Ω → ℝ} {m : ℝ}
    (hY : AEMeasurable Y P)
    (h3 : Integrable (fun ω => |Y ω - m| ^ 3) P) :
    Integrable Y P := by
  have hbound_int :
      Integrable (fun ω => (1 : ℝ) + |Y ω - m| ^ 3 + |m|) P := by
    exact ((integrable_const (c := (1 : ℝ))).add h3).add
      (integrable_const (c := |m|))
  refine hbound_int.mono' hY.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  calc
    |Y ω| = |(Y ω - m) + m| := by ring_nf
    _ ≤ |Y ω - m| + |m| := abs_add_le _ _
    _ ≤ (1 + |Y ω - m| ^ 3) + |m| := by
          gcongr
          exact abs_le_one_add_abs_cube (Y ω - m)
    _ = 1 + |Y ω - m| ^ 3 + |m| := by ring

/-- A centered finite third absolute moment implies square integrability of
the original variable. -/
lemma integrable_sq_of_integrable_centered_abs_cube
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Y : Ω → ℝ} {m : ℝ}
    (hY : AEMeasurable Y P)
    (h3 : Integrable (fun ω => |Y ω - m| ^ 3) P) :
    Integrable (fun ω => Y ω ^ 2) P := by
  have hbound_int :
      Integrable (fun ω => 2 * (1 + |Y ω - m| ^ 3 + |m| ^ 2)) P := by
    exact (((integrable_const (c := (1 : ℝ))).add h3).add
      (integrable_const (c := |m| ^ 2))).const_mul 2
  refine hbound_int.mono'
    (by fun_prop : AEStronglyMeasurable (fun ω => Y ω ^ 2) P) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y ω))]
  have htri : |Y ω| ≤ |Y ω - m| + |m| := by
    calc
      |Y ω| = |(Y ω - m) + m| := by ring_nf
      _ ≤ |Y ω - m| + |m| := abs_add_le _ _
  have hsqtri : (Y ω) ^ 2 ≤ (|Y ω - m| + |m|) ^ 2 := by
    rw [← sq_abs (Y ω)]
    exact (sq_le_sq₀ (abs_nonneg (Y ω))
      (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr htri
  have hcenter_sq : |Y ω - m| ^ 2 ≤ 1 + |Y ω - m| ^ 3 := by
    simpa [sq_abs] using sq_le_one_add_abs_cube (Y ω - m)
  calc
    Y ω ^ 2 ≤ (|Y ω - m| + |m|) ^ 2 := hsqtri
    _ ≤ 2 * (|Y ω - m| ^ 2 + |m| ^ 2) := by
          nlinarith [sq_nonneg (|Y ω - m| - |m|)]
    _ ≤ 2 * (1 + |Y ω - m| ^ 3 + |m| ^ 2) := by
          nlinarith [hcenter_sq]

lemma memLp_two_of_integrable_centered_abs_cube
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Y : Ω → ℝ} {m : ℝ}
    (hY : AEMeasurable Y P)
    (h3 : Integrable (fun ω => |Y ω - m| ^ 3) P) :
    MemLp Y 2 P := by
  rw [memLp_two_iff_integrable_sq hY.aestronglyMeasurable]
  exact integrable_sq_of_integrable_centered_abs_cube hY h3

/-- Finite first moments of the summands imply finite first moment of the
normalized sum. -/
lemma integrable_normalizedSum_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ} {N : ℕ}
    (hX : ∀ i ∈ Finset.range N, Integrable (X i) P) :
    Integrable (normalizedSum X m σ N) P := by
  have hsum :
      Integrable (fun ω => ∑ i ∈ Finset.range N, X i ω) P :=
    integrable_finset_sum (s := Finset.range N)
      (f := fun i ω => X i ω) hX
  have hcenter :
      Integrable
        (fun ω => (∑ i ∈ Finset.range N, X i ω) - (N : ℝ) * m) P :=
    hsum.sub (integrable_const _)
  exact (hcenter.const_mul ((σ * Real.sqrt (N : ℝ))⁻¹)).congr
    (ae_of_all P fun ω => by
      simp [normalizedSum, div_eq_mul_inv, mul_comm, mul_assoc])

/-- The standard normal law has finite first moment. -/
lemma integrable_id_standardNormalMeasure :
    Integrable (fun x : ℝ => x) standardNormalMeasure := by
  have hmem :
      MemLp (fun x : ℝ => x) (1 : ℝ≥0∞) standardNormalMeasure := by
    simpa [standardNormalMeasure, id] using
      (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := 0) (v := (1 : ℝ≥0)) (p := (1 : ℝ≥0∞)) (by simp))
  exact hmem.integrable (by norm_num : 1 ≤ (1 : ℝ≥0∞))

/-- Under Berry-Esseen hypotheses, the normalized-sum law has finite first
moment. -/
lemma integrable_id_normalizedSumLaw_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) :
    Integrable (fun x : ℝ => x) (P.map (normalizedSum X m σ N)) := by
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hXi_int : ∀ i ∈ Finset.range N, Integrable (X i) P := by
    intro i _hi
    exact (hBE.identDistrib i).integrable_iff.mpr hX0_int
  have hZ : AEMeasurable (normalizedSum X m σ N) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable N
  have hNorm : Integrable (normalizedSum X m σ N) P :=
    integrable_normalizedSum_of_integrable (P := P) (X := X)
      (m := m) (σ := σ) (N := N) hXi_int
  change Integrable id (P.map (normalizedSum X m σ N))
  rw [integrable_map_measure measurable_id.aestronglyMeasurable hZ]
  simpa [Function.comp_def, id] using hNorm

/-- Sharp Esseen/Fourier smoothing with the local Polya-smoothed inversion
identity discharged from finite first moments and original Fourier
integrability. -/
theorem esseenFourierSmoothing_from_integrable_polya_sup
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {lam L : ℝ} (hL : 0 < L) (hlam : 0 < lam)
    (hLip : measureCDFLipschitz ν lam)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hν1 : Integrable (fun x : ℝ => x) ν)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ ν (esseenFourierBudget μ ν lam L) := by
  have hInv :
      inversionCDFFormulaFor
        (polyaSmooth μ (polyaKernelMeasure L))
        (polyaSmooth ν (polyaKernelMeasure L))
        (charFun (polyaSmooth μ (polyaKernelMeasure L)))
        (charFun (polyaSmooth ν (polyaKernelMeasure L))) L :=
    inversionCDFFormulaFor_polyaSmooth_polyaKernelMeasure_of_integrable
      (μ := μ) (ν := ν) (L := L) hL hμ1 hν1 hOrigInt
  exact
    esseenFourierSmoothing_from_inversion_polya_sup
      (μ := μ) (ν := ν) (lam := lam) (L := L)
      hL hlam hLip hInv hOrigInt

/-- Durrett/Feller Esseen smoothing inequality with all local analytic
side conditions discharged: finite first moments and truncated Fourier
integrability imply the usual Fourier budget
`π⁻¹ ∫ |φ - ψ| / |θ| + 24λ/(πL)`. -/
theorem durrettFeller_esseenSmoothing
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {lam L : ℝ} (hL : 0 < L) (hlam : 0 < lam)
    (hLip : measureCDFLipschitz ν lam)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hν1 : Integrable (fun x : ℝ => x) ν)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun ν θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ ν (esseenFourierBudget μ ν lam L) :=
  esseenFourierSmoothing_from_integrable_polya_sup
    (μ := μ) (ν := ν) (lam := lam) (L := L)
    hL hlam hLip hμ1 hν1 hOrigInt

/-- Standard-normal specialization of the sharp Polya/Fourier smoothing chain
with the local inversion identity discharged from first moments, for any
available CDF Lipschitz constant of the normal target. -/
theorem esseenFourierSmoothing_standardNormal_polyaKernelMeasure_from_integrable_sup_lipschitz
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {lam L : ℝ} (hL : 0 < L) (hlam : 0 < lam)
    (hLip : measureCDFLipschitz standardNormalMeasure lam)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun standardNormalMeasure θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ standardNormalMeasure
      (esseenFourierBudget μ standardNormalMeasure lam L) := by
  exact
    esseenFourierSmoothing_from_integrable_polya_sup
      (μ := μ) (ν := standardNormalMeasure) (lam := lam) (L := L)
      hL hlam hLip
      hμ1 integrable_id_standardNormalMeasure hOrigInt

/-- Standard-normal specialization of the sharp Polya/Fourier smoothing chain
with the local inversion identity discharged from first moments. -/
theorem esseenFourierSmoothing_standardNormal_polyaKernelMeasure_from_integrable_sup
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {L : ℝ} (hL : 0 < L)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun standardNormalMeasure θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ standardNormalMeasure
      (esseenFourierBudget μ standardNormalMeasure 1 L) := by
  exact
    esseenFourierSmoothing_standardNormal_polyaKernelMeasure_from_integrable_sup_lipschitz
      (μ := μ) (lam := 1) (L := L) hL (by norm_num)
      standardNormal_measureCDFLipschitz hμ1 hOrigInt

/-- Standard-normal Polya/Fourier smoothing with the sharp elementary
Gaussian density bound `φ(x) ≤ 2 / 5`. -/
theorem esseenFourierSmoothing_standardNormal_polyaKernelMeasure_from_integrable_sup_two_fifths
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {L : ℝ} (hL : 0 < L)
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hOrigInt :
      IntegrableOn
        (fun θ : ℝ => ‖charFun μ θ - charFun standardNormalMeasure θ‖ / |θ|)
        (Set.Icc (-L) L)) :
    measureCDFErrorLE μ standardNormalMeasure
      (esseenFourierBudget μ standardNormalMeasure (2 / 5) L) := by
  exact
    esseenFourierSmoothing_standardNormal_polyaKernelMeasure_from_integrable_sup_lipschitz
      (μ := μ) (lam := 2 / 5) (L := L) hL (by norm_num)
      standardNormal_measureCDFLipschitz_two_fifths hμ1 hOrigInt

/-- The standardized one-summand law has finite absolute third moment if the
centered summand has finite absolute third moment. -/
lemma integrable_standardizedLaw_abs_cube
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {m σ : ℝ}
    (hY : AEMeasurable Y P)
    (h3 : Integrable (fun ω => |Y ω - m| ^ 3) P) :
    Integrable (fun x : ℝ => |x| ^ 3)
      (P.map (fun ω => (Y ω - m) / σ)) := by
  have hstd : AEMeasurable (fun ω => (Y ω - m) / σ) P :=
    (hY.sub aemeasurable_const).div_const σ
  have hgm :
      AEStronglyMeasurable (fun x : ℝ => |x| ^ 3)
        (P.map (fun ω => (Y ω - m) / σ)) := by
    exact (by fun_prop : Measurable (fun x : ℝ => |x| ^ 3)).aestronglyMeasurable
  rw [integrable_map_measure hgm hstd]
  by_cases hσ : σ = 0
  · subst σ
    convert (integrable_const (μ := P) (c := (0 : ℝ))) using 1
    ext ω
    simp
  · have hbase := h3.const_mul (|σ| ^ 3)⁻¹
    convert hbase using 1
    ext ω
    change |(Y ω - m) / σ| ^ 3 = (|σ| ^ 3)⁻¹ * |Y ω - m| ^ 3
    rw [abs_div, div_eq_mul_inv, mul_pow]
    ring

/-- Exact scaling of the absolute third moment under centering and
standardization. -/
lemma integral_standardizedLaw_abs_cube_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {m σ : ℝ}
    (hY : AEMeasurable Y P) (hσ : 0 < σ) :
    ∫ x : ℝ, |x| ^ 3 ∂(P.map (fun ω => (Y ω - m) / σ)) =
      (∫ ω, |Y ω - m| ^ 3 ∂P) / σ ^ 3 := by
  have hstd : AEMeasurable (fun ω => (Y ω - m) / σ) P :=
    (hY.sub aemeasurable_const).div_const σ
  rw [integral_map hstd]
  · have heq_fun :
        (fun ω => |(Y ω - m) / σ| ^ 3) =
          fun ω => (σ ^ 3)⁻¹ * |Y ω - m| ^ 3 := by
      funext ω
      rw [abs_div, abs_of_pos hσ, div_eq_mul_inv, mul_pow]
      ring
    rw [heq_fun, integral_const_mul]
    ring
  · exact (by fun_prop : Measurable (fun x : ℝ => |x| ^ 3)).aestronglyMeasurable

/-- The standardized one-summand law is centered. -/
lemma integral_standardizedLaw_id_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {m σ : ℝ}
    (hY : AEMeasurable Y P)
    (hY_int : Integrable Y P)
    (hmean : P[Y] = m)
    (hσ : σ ≠ 0) :
    ∫ x : ℝ, x ∂(P.map (fun ω => (Y ω - m) / σ)) = 0 := by
  have hstd : AEMeasurable (fun ω => (Y ω - m) / σ) P :=
    (hY.sub aemeasurable_const).div_const σ
  rw [integral_map hstd]
  · exact lindebergLevy_standardized_mean_eq_zero (μ := P) hY_int hmean hσ
  · exact measurable_id.aestronglyMeasurable

/-- The standardized one-summand law has second moment one. -/
lemma integral_standardizedLaw_sq_eq_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {m σ : ℝ}
    (hY : AEMeasurable Y P)
    (hY_mlp : MemLp Y 2 P)
    (hmean : P[Y] = m)
    (hvar : Var[Y; P] = σ ^ 2)
    (hσ : σ ≠ 0) :
    ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => (Y ω - m) / σ)) = 1 := by
  have hstd : AEMeasurable (fun ω => (Y ω - m) / σ) P :=
    (hY.sub aemeasurable_const).div_const σ
  rw [integral_map hstd]
  · exact lindebergLevy_standardized_second_moment_eq_one
      (μ := P) hY_mlp hmean hvar hσ
  · exact (by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aestronglyMeasurable

lemma sq_le_sixty_four_mul_cube_add_half_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    y ^ 2 ≤ 64 * y ^ 3 + 1 / 2 := by
  by_cases hsmall : y ≤ 1 / 2
  · have hsq : y ^ 2 ≤ 1 / 2 := by
      nlinarith [hy, hsmall, sq_nonneg (y - 1 / 2)]
    have hcube : 0 ≤ 64 * y ^ 3 := by
      nlinarith [pow_nonneg hy 3]
    nlinarith
  · have hyhalf : (1 / 2 : ℝ) ≤ y := (lt_of_not_ge hsmall).le
    have hsq_le_cube : y ^ 2 ≤ 2 * y ^ 3 := by
      have hcoef : 1 ≤ 2 * y := by nlinarith
      calc
        y ^ 2 = y ^ 2 * 1 := by ring
        _ ≤ y ^ 2 * (2 * y) :=
          mul_le_mul_of_nonneg_left hcoef (sq_nonneg y)
        _ = 2 * y ^ 3 := by ring
    nlinarith [hsq_le_cube, pow_nonneg hy 3]

lemma integral_sq_le_sixty_four_integral_abs_cube_add_half
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    ∫ x : ℝ, x ^ 2 ∂ν ≤
      64 * ∫ x : ℝ, |x| ^ 3 ∂ν + 1 / 2 := by
  have hsq_int : Integrable (fun x : ℝ => x ^ 2) ν :=
    integrable_sq_of_integrable_abs_cube ν h3
  have hbound_int : Integrable (fun x : ℝ => 64 * |x| ^ 3 + 1 / 2) ν :=
    (h3.const_mul 64).add (integrable_const (c := (1 / 2 : ℝ)))
  have hpoint :
      ∀ᵐ x ∂ν, x ^ 2 ≤ 64 * |x| ^ 3 + 1 / 2 := by
    filter_upwards with x
    simpa [sq_abs] using
      sq_le_sixty_four_mul_cube_add_half_of_nonneg (abs_nonneg x)
  have hle := integral_mono_ae hsq_int hbound_int hpoint
  have hrewrite :
      ∫ x : ℝ, (64 * |x| ^ 3 + 1 / 2) ∂ν =
        64 * ∫ x : ℝ, |x| ^ 3 ∂ν + 1 / 2 := by
    rw [integral_add (h3.const_mul 64) (integrable_const (c := (1 / 2 : ℝ))),
      integral_const_mul]
    simp
  exact hle.trans_eq hrewrite

lemma one_div_128_le_integral_abs_cube_of_integral_sq_eq_one
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂ν = 1) :
    1 / 128 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := by
  have hle :=
    integral_sq_le_sixty_four_integral_abs_cube_add_half (ν := ν) h3
  rw [hsecond] at hle
  nlinarith

lemma one_div_128_le_berryEsseenRho_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    1 / 128 ≤ berryEsseenRho X P m σ := by
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure (P.map (fun ω => (X 0 ω - m) / σ)) :=
    Measure.isProbabilityMeasure_map hstd_meas
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3)
        (P.map (fun ω => (X 0 ω - m) / σ)) :=
    integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => (X 0 ω - m) / σ)) = 1 :=
    integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hlower :=
    one_div_128_le_integral_abs_cube_of_integral_sq_eq_one
      (ν := P.map (fun ω => (X 0 ω - m) / σ)) h3 hsecond
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂(P.map (fun ω => (X 0 ω - m) / σ)) =
        berryEsseenRho X P m σ := by
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  rwa [hM] at hlower

lemma sq_rpow_three_halves_eq_abs_cube (x : ℝ) :
    (x ^ 2) ^ (3 / 2 : ℝ) = |x| ^ 3 := by
  rw [← sq_abs x]
  have hx : 0 ≤ |x| := abs_nonneg x
  rw [← Real.rpow_natCast (|x|) 2]
  rw [← Real.rpow_mul hx]
  norm_num [Real.rpow_natCast]

lemma one_le_integral_abs_cube_of_integral_sq_eq_one
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂ν = 1) :
    1 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := by
  have hsq_int : Integrable (fun x : ℝ => x ^ 2) ν :=
    integrable_sq_of_integrable_abs_cube ν h3
  have hphi_int :
      Integrable ((fun y : ℝ => y ^ (3 / 2 : ℝ)) ∘ fun x : ℝ => x ^ 2) ν := by
    refine h3.congr ?_
    filter_upwards with x
    simp [sq_rpow_three_halves_eq_abs_cube]
  have hjensen :
      (∫ x : ℝ, x ^ 2 ∂ν) ^ (3 / 2 : ℝ) ≤
        ∫ x : ℝ, (x ^ 2) ^ (3 / 2 : ℝ) ∂ν := by
    have hconv :
        ConvexOn ℝ (Set.Ici (0 : ℝ)) fun y : ℝ => y ^ (3 / 2 : ℝ) :=
      convexOn_rpow (by norm_num : (1 : ℝ) ≤ 3 / 2)
    have hcont :
        ContinuousOn (fun y : ℝ => y ^ (3 / 2 : ℝ)) (Set.Ici (0 : ℝ)) :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).continuousOn
    have hXs :
        ∀ᵐ x ∂ν, x ^ 2 ∈ Set.Ici (0 : ℝ) :=
      Eventually.of_forall fun x => sq_nonneg x
    exact
      jensen_integral
        (μ := ν) (s := Set.Ici (0 : ℝ))
        (φ := fun y : ℝ => y ^ (3 / 2 : ℝ))
        (X := fun x : ℝ => x ^ 2)
        hconv hcont isClosed_Ici hXs hsq_int hphi_int
  have hright :
      (∫ x : ℝ, (x ^ 2) ^ (3 / 2 : ℝ) ∂ν) =
        ∫ x : ℝ, |x| ^ 3 ∂ν := by
    exact integral_congr_ae
      (Eventually.of_forall fun x => sq_rpow_three_halves_eq_abs_cube x)
  calc
    1 = (∫ x : ℝ, x ^ 2 ∂ν) ^ (3 / 2 : ℝ) := by
          rw [hsecond]
          norm_num
    _ ≤ ∫ x : ℝ, (x ^ 2) ^ (3 / 2 : ℝ) ∂ν := hjensen
    _ = ∫ x : ℝ, |x| ^ 3 ∂ν := hright

lemma one_le_berryEsseenRho_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    1 ≤ berryEsseenRho X P m σ := by
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure (P.map (fun ω => (X 0 ω - m) / σ)) :=
    Measure.isProbabilityMeasure_map hstd_meas
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3)
        (P.map (fun ω => (X 0 ω - m) / σ)) :=
    integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => (X 0 ω - m) / σ)) = 1 :=
    integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hlower :=
    one_le_integral_abs_cube_of_integral_sq_eq_one
      (ν := P.map (fun ω => (X 0 ω - m) / σ)) h3 hsecond
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂(P.map (fun ω => (X 0 ω - m) / σ)) =
        berryEsseenRho X P m σ := by
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  rwa [hM] at hlower

/-! ### Shevtsova/Prawitz proof-spine anchors already discharged locally -/

/-- Shevtsova's normalized third-absolute-moment lower bound in the unit
variance form.  This is just the local Jensen argument packaged under the
classical `β₃` name used in Prawitz/Shevtsova proofs. -/
lemma shevtsovaBeta3_ge_one_of_unit_secondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂ν = 1) :
    1 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν :=
  one_le_integral_abs_cube_of_integral_sq_eq_one ν h3 hsecond

/-- The same `β₃ ≥ 1` lower bound specialized to the standardized summand law
from the HDP Berry-Esseen hypotheses. -/
lemma shevtsovaBeta3_ge_one_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    1 ≤
      ∫ x : ℝ, |x| ^ 3 ∂(P.map (fun ω => (X 0 ω - m) / σ)) := by
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure (P.map (fun ω => (X 0 ω - m) / σ)) :=
    Measure.isProbabilityMeasure_map hstd_meas
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3)
        (P.map (fun ω => (X 0 ω - m) / σ)) :=
    integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => (X 0 ω - m) / σ)) = 1 :=
    integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  exact shevtsovaBeta3_ge_one_of_unit_secondMoment
    (P.map (fun ω => (X 0 ω - m) / σ)) h3 hsecond

/-- Prawitz/Shevtsova-facing name for the normalized-sum characteristic
function factorization into the `N`th power of the standardized one-summand
characteristic function. -/
theorem shevtsovaCharFun_normalizedSum_eq_power
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hX : ∀ n, AEMeasurable (X n) P)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (N : ℕ) (t : ℝ) :
    charFun (P.map (normalizedSum X m σ N)) t =
      (charFun (P.map (fun ω => (X 0 ω - m) / σ))
        (t / Real.sqrt (N : ℝ))) ^ N :=
  charFun_normalizedSum_eq_standardized_pow
    (μ := P) hX hindep hident N t

/-- Hypotheses-level Prawitz/Shevtsova characteristic-function factorization
for the HDP normalized sum. -/
theorem shevtsovaCharFun_normalizedSum_eq_power_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (t : ℝ) :
    charFun (P.map (normalizedSum X m σ N)) t =
      (charFun (P.map (fun ω => (X 0 ω - m) / σ))
        (t / Real.sqrt (N : ℝ))) ^ N :=
  shevtsovaCharFun_normalizedSum_eq_power
    (P := P) (X := X) (m := m) (σ := σ)
    hBE.aemeasurable hBE.independent hBE.identDistrib N t

/-- Shevtsova-facing name for the law of the normalized sum. -/
def shevtsovaNormalizedSumLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) : Measure ℝ :=
  P.map (normalizedSum X m σ N)

lemma shevtsovaNormalizedSumLaw_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) :
    shevtsovaNormalizedSumLaw P X m σ N =
      P.map (normalizedSum X m σ N) := rfl

/-- Characteristic function `f_n` of the normalized sum in the
Prawitz/Shevtsova notation. -/
def shevtsovaFn
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  charFun (shevtsovaNormalizedSumLaw P X m σ N) t

/-- Absolute value `|f_n(t)|` in the Prawitz/Shevtsova notation. -/
def shevtsovaFnAbs
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ‖shevtsovaFn P X m σ N t‖

/-- Characteristic-function error
`r_n(t) = |f_n(t) - exp(-t^2/2)|`, expressed against the standard-normal
characteristic function already available in the local library. -/
def shevtsovaRn
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ‖shevtsovaFn P X m σ N t - charFun standardNormalMeasure t‖

/-- Shevtsova's `Δ_n`, represented by the existing supremum CDF error. -/
def shevtsovaDelta
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) : ℝ :=
  measureCDFErrorSup (shevtsovaNormalizedSumLaw P X m σ N)
    standardNormalMeasure

lemma shevtsovaFnAbs_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t : ℝ) :
    0 ≤ shevtsovaFnAbs P X m σ N t :=
  norm_nonneg _

lemma shevtsovaRn_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t : ℝ) :
    0 ≤ shevtsovaRn P X m σ N t :=
  norm_nonneg _

lemma shevtsovaFn_eq_power_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (t : ℝ) :
    shevtsovaFn P X m σ N t =
      (charFun (P.map (fun ω => (X 0 ω - m) / σ))
        (t / Real.sqrt (N : ℝ))) ^ N := by
  simpa [shevtsovaFn, shevtsovaNormalizedSumLaw] using
    shevtsovaCharFun_normalizedSum_eq_power_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N t

lemma shevtsovaFnAbs_eq_norm_power_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (t : ℝ) :
    shevtsovaFnAbs P X m σ N t =
      ‖charFun (P.map (fun ω => (X 0 ω - m) / σ))
        (t / Real.sqrt (N : ℝ))‖ ^ N := by
  rw [shevtsovaFnAbs, shevtsovaFn_eq_power_of_hypotheses
    (P := P) (X := X) (m := m) (σ := σ) hBE N t, norm_pow]

lemma isProbabilityMeasure_shevtsovaNormalizedSumLaw_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) :
    IsProbabilityMeasure (shevtsovaNormalizedSumLaw P X m σ N) := by
  have hZ : AEMeasurable (normalizedSum X m σ N) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable N
  unfold shevtsovaNormalizedSumLaw
  exact Measure.isProbabilityMeasure_map hZ

lemma shevtsovaFnAbs_le_one_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) (t : ℝ) :
    shevtsovaFnAbs P X m σ N t ≤ 1 := by
  letI : IsProbabilityMeasure (shevtsovaNormalizedSumLaw P X m σ N) :=
    isProbabilityMeasure_shevtsovaNormalizedSumLaw_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N
  simpa [shevtsovaFnAbs, shevtsovaFn] using
    MeasureTheory.norm_charFun_le_one
      (μ := shevtsovaNormalizedSumLaw P X m σ N) t

lemma shevtsovaFnAbs_le_exp_neg_quarter_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) {t : ℝ}
    (hWindow : (t / Real.sqrt (N : ℝ)) ^ 2 ≤ 1)
    (hSmall :
      (2 / 3 : ℝ) * berryEsseenRho X P m σ *
        |t / Real.sqrt (N : ℝ)| ≤ 1) :
    shevtsovaFnAbs P X m σ N t ≤ Real.exp (-(t ^ 2) / 4) := by
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hstd_meas
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3) ν := by
    dsimp [ν]
    exact integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hmean :
      ∫ x : ℝ, x ∂ν = 0 := by
    dsimp [ν]
    exact integral_standardizedLaw_id_eq_zero
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_int (hBE.mean_eq 0) hBE.sigma_pos.ne'
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂ν = 1 := by
    dsimp [ν]
    exact integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂ν = berryEsseenRho X P m σ := by
    dsimp [ν]
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  have hbase :
      ‖charFun ν (t / Real.sqrt (N : ℝ))‖ ≤
        Real.exp (-((t / Real.sqrt (N : ℝ)) ^ 2) / 4) := by
    exact norm_charFun_le_exp_neg_sq_div_four
      (μ := ν) h3 hmean hsecond hWindow (by simpa [hM] using hSmall)
  have hpow :
      ‖charFun ν (t / Real.sqrt (N : ℝ))‖ ^ N ≤
        (Real.exp (-((t / Real.sqrt (N : ℝ)) ^ 2) / 4)) ^ N :=
    pow_le_pow_left₀ (norm_nonneg _) hbase N
  have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hexp_pow :
      (Real.exp (-((t / Real.sqrt (N : ℝ)) ^ 2) / 4)) ^ N =
        Real.exp (-(t ^ 2) / 4) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [div_pow, Real.sq_sqrt hN_real.le]
    field_simp [hN_real.ne']
  calc
    shevtsovaFnAbs P X m σ N t
        = ‖charFun ν (t / Real.sqrt (N : ℝ))‖ ^ N := by
          simpa [ν] using
            shevtsovaFnAbs_eq_norm_power_of_hypotheses
              (P := P) (X := X) (m := m) (σ := σ) hBE N t
    _ ≤ (Real.exp (-((t / Real.sqrt (N : ℝ)) ^ 2) / 4)) ^ N := hpow
    _ = Real.exp (-(t ^ 2) / 4) := hexp_pow

lemma shevtsovaNormalCharFun_eq (t : ℝ) :
    charFun standardNormalMeasure t =
      Complex.exp (((-(t ^ 2 / 2)) : ℝ) : ℂ) := by
  rw [standardNormal_charFun]
  congr 1
  norm_cast
  ring

lemma shevtsovaNormalCharFun_scaled_pow_eq
    {N : ℕ} (hN : 0 < N) (t : ℝ) :
    (charFun standardNormalMeasure (t / Real.sqrt (N : ℝ))) ^ N =
      charFun standardNormalMeasure t := by
  have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [shevtsovaNormalCharFun_eq (t / Real.sqrt (N : ℝ)),
    shevtsovaNormalCharFun_eq t, ← Complex.exp_nat_mul]
  congr 1
  norm_cast
  rw [div_pow, Real.sq_sqrt hN_real.le]
  field_simp [hN_real.ne']

lemma shevtsovaRn_eq_norm_power_sub_normal_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (t : ℝ) :
    shevtsovaRn P X m σ N t =
      ‖(charFun (P.map (fun ω => (X 0 ω - m) / σ))
          (t / Real.sqrt (N : ℝ))) ^ N -
        Complex.exp (((-(t ^ 2 / 2)) : ℝ) : ℂ)‖ := by
  rw [shevtsovaRn, shevtsovaFn_eq_power_of_hypotheses
    (P := P) (X := X) (m := m) (σ := σ) hBE N t,
    shevtsovaNormalCharFun_eq]

/-- Hypotheses-level one-summand Taylor error against the standard normal
characteristic function. -/
lemma standardizedCharFun_sub_standardNormalCharFun_le_cubic_quartic_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ t : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    ‖charFun (P.map (fun ω => (X 0 ω - m) / σ)) t -
        charFun standardNormalMeasure t‖ ≤
      (1 / 6 : ℝ) * berryEsseenRho X P m σ * |t| ^ 3 +
        t ^ 4 / 8 := by
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hstd_meas
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3) ν := by
    dsimp [ν]
    exact integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hmean :
      ∫ x : ℝ, x ∂ν = 0 := by
    dsimp [ν]
    exact integral_standardizedLaw_id_eq_zero
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_int (hBE.mean_eq 0)
      hBE.sigma_pos.ne'
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂ν = 1 := by
    dsimp [ν]
    exact integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂ν = berryEsseenRho X P m σ := by
    dsimp [ν]
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  have h :=
    norm_charFun_sub_standardNormalCharFun_le_cubic_quartic
      (μ := ν) h3 hmean hsecond t
  simpa [ν, hM] using h

/-- Shevtsova Lemma 2, algebraic telescoping form: the normalized-sum
characteristic-function error is controlled by the one-summand normal error
times the exact geometric damping sum. -/
lemma shevtsovaRn_le_geom_sum_oneStep_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t : ℝ) :
    shevtsovaRn P X m σ N t ≤
      ‖charFun (P.map (fun ω => (X 0 ω - m) / σ))
          (t / Real.sqrt (N : ℝ)) -
        charFun standardNormalMeasure (t / Real.sqrt (N : ℝ))‖ *
        (Finset.range N).sum
          (fun k =>
            ‖charFun (P.map (fun ω => (X 0 ω - m) / σ))
                (t / Real.sqrt (N : ℝ))‖ ^ k *
              ‖charFun standardNormalMeasure
                (t / Real.sqrt (N : ℝ))‖ ^ (N - 1 - k)) := by
  rw [shevtsovaRn, shevtsovaFn_eq_power_of_hypotheses
    (P := P) (X := X) (m := m) (σ := σ) hBE N t,
    ← shevtsovaNormalCharFun_scaled_pow_eq (N := N) hN t]
  exact norm_pow_sub_pow_le_geom_sum N

/-- Shevtsova Lemma 2 with the locally proved cubic/quartic one-summand
Taylor error substituted into the geometric-sum form. -/
lemma shevtsovaRn_le_geom_sum_cubic_quartic_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t : ℝ) :
    shevtsovaRn P X m σ N t ≤
      ((1 / 6 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt (N : ℝ)| ^ 3 +
        (t / Real.sqrt (N : ℝ)) ^ 4 / 8) *
        (Finset.range N).sum
          (fun k =>
            ‖charFun (P.map (fun ω => (X 0 ω - m) / σ))
                (t / Real.sqrt (N : ℝ))‖ ^ k *
              ‖charFun standardNormalMeasure
                (t / Real.sqrt (N : ℝ))‖ ^ (N - 1 - k)) := by
  have hgeom :=
    shevtsovaRn_le_geom_sum_oneStep_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE hN t
  have hstep :=
    standardizedCharFun_sub_standardNormalCharFun_le_cubic_quartic_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      (t := t / Real.sqrt (N : ℝ)) hBE
  have hsum_nonneg :
      0 ≤ (Finset.range N).sum
        (fun k =>
          ‖charFun (P.map (fun ω => (X 0 ω - m) / σ))
              (t / Real.sqrt (N : ℝ))‖ ^ k *
            ‖charFun standardNormalMeasure
              (t / Real.sqrt (N : ℝ))‖ ^ (N - 1 - k)) := by
    exact Finset.sum_nonneg fun k _hk =>
      mul_nonneg
        (pow_nonneg (norm_nonneg _) k)
        (pow_nonneg (norm_nonneg _) (N - 1 - k))
  exact hgeom.trans
    (mul_le_mul_of_nonneg_right hstep hsum_nonneg)

lemma shevtsovaRn_le_durrett_bound_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t : ℝ}
    (hWindow : t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      berryEsseenRho X P m σ *
        |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    shevtsovaRn P X m σ (n + 1) t ≤
      ((1 / 6 : ℝ) * berryEsseenRho X P m σ * |t| ^ 3 /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        t ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) *
        Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hstd_meas
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3) ν := by
    dsimp [ν]
    exact integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hmean :
      ∫ x : ℝ, x ∂ν = 0 := by
    dsimp [ν]
    exact integral_standardizedLaw_id_eq_zero
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_int (hBE.mean_eq 0) hBE.sigma_pos.ne'
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂ν = 1 := by
    dsimp [ν]
    exact integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂ν = berryEsseenRho X P m σ := by
    dsimp [ν]
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  have hSmall' :
      (∫ x, |x| ^ 3 ∂ν) *
        |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3 := by
    simpa [hM] using hSmall
  have hpoint :=
    norm_charFun_scaled_pow_succ_sub_standardNormal_charFun_le_durrett
      (μ := ν) h3 hmean hsecond hn hWindow hSmall'
  simpa [ν, hM, shevtsovaRn,
    shevtsovaFn_eq_power_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE (n + 1) t]
    using hpoint

lemma shevtsovaRn_div_abs_le_durrett_bound_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t : ℝ}
    (hWindow : t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      berryEsseenRho X P m σ *
        |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    shevtsovaRn P X m σ (n + 1) t / |t| ≤
      berryEsseenDurrettFourierBound
        (P.map (fun ω => (X 0 ω - m) / σ)) n t := by
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hstd_meas
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3) ν := by
    dsimp [ν]
    exact integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hmean :
      ∫ x : ℝ, x ∂ν = 0 := by
    dsimp [ν]
    exact integral_standardizedLaw_id_eq_zero
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_int (hBE.mean_eq 0) hBE.sigma_pos.ne'
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂ν = 1 := by
    dsimp [ν]
    exact integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂ν = berryEsseenRho X P m σ := by
    dsimp [ν]
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  have hSmall' :
      (∫ x, |x| ^ 3 ∂ν) *
        |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3 := by
    simpa [hM] using hSmall
  have hpoint :=
    fourierDistanceIntegrand_scaled_pow_succ_standardNormal_le_durrettBound
      (μ := ν) h3 hmean hsecond hn hWindow hSmall'
  simpa [ν, hM, shevtsovaRn,
    shevtsovaFn_eq_power_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE (n + 1) t]
    using hpoint

lemma shevtsovaNormalCharFun_norm_le_one (t : ℝ) :
    ‖charFun standardNormalMeasure t‖ ≤ 1 :=
  MeasureTheory.norm_charFun_le_one (μ := standardNormalMeasure) t

lemma charFun_zero_of_probabilityMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    charFun μ 0 = 1 := by
  rw [charFun_apply_real]
  simp

lemma shevtsovaFn_zero_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) :
    shevtsovaFn P X m σ N 0 = 1 := by
  letI : IsProbabilityMeasure (shevtsovaNormalizedSumLaw P X m σ N) :=
    isProbabilityMeasure_shevtsovaNormalizedSumLaw_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N
  simp [shevtsovaFn]

lemma shevtsovaFnAbs_zero_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) :
    shevtsovaFnAbs P X m σ N 0 = 1 := by
  rw [shevtsovaFnAbs, shevtsovaFn_zero_of_hypotheses
    (P := P) (X := X) (m := m) (σ := σ) hBE N]
  norm_num

lemma shevtsovaNormalCharFun_zero :
    charFun standardNormalMeasure 0 = 1 :=
  charFun_zero_of_probabilityMeasure standardNormalMeasure

lemma shevtsovaRn_zero_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) :
    shevtsovaRn P X m σ N 0 = 0 := by
  rw [shevtsovaRn, shevtsovaFn_zero_of_hypotheses
    (P := P) (X := X) (m := m) (σ := σ) hBE N,
    shevtsovaNormalCharFun_zero]
  simp

lemma shevtsovaRn_le_abs_mul_durrett_bound_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t : ℝ}
    (hWindow : t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      berryEsseenRho X P m σ *
        |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    shevtsovaRn P X m σ (n + 1) t ≤
      |t| *
        berryEsseenDurrettFourierBound
          (P.map (fun ω => (X 0 ω - m) / σ)) n t := by
  by_cases ht : t = 0
  · subst t
    rw [shevtsovaRn_zero_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE (n + 1)]
    simp
  · have hdiv :=
      shevtsovaRn_div_abs_le_durrett_bound_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE hn
        (t := t) hWindow hSmall
    have hmul := mul_le_mul_of_nonneg_right hdiv (abs_nonneg t)
    calc
      shevtsovaRn P X m σ (n + 1) t =
          (shevtsovaRn P X m σ (n + 1) t / |t|) * |t| := by
        field_simp [abs_ne_zero.mpr ht]
      _ ≤ berryEsseenDurrettFourierBound
            (P.map (fun ω => (X 0 ω - m) / σ)) n t * |t| := hmul
      _ = |t| *
            berryEsseenDurrettFourierBound
              (P.map (fun ω => (X 0 ω - m) / σ)) n t := by
        ring

lemma shevtsovaRn_le_two_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) (t : ℝ) :
    shevtsovaRn P X m σ N t ≤ 2 := by
  have hfn : ‖shevtsovaFn P X m σ N t‖ ≤ 1 := by
    simpa [shevtsovaFnAbs] using
      shevtsovaFnAbs_le_one_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE N t
  have hnormal : ‖charFun standardNormalMeasure t‖ ≤ 1 :=
    shevtsovaNormalCharFun_norm_le_one t
  calc
    shevtsovaRn P X m σ N t
        = ‖shevtsovaFn P X m σ N t - charFun standardNormalMeasure t‖ := rfl
    _ ≤ ‖shevtsovaFn P X m σ N t‖ +
        ‖charFun standardNormalMeasure t‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add hfn hnormal
    _ = 2 := by norm_num

lemma continuous_shevtsovaFn_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) :
    Continuous (shevtsovaFn P X m σ N) := by
  letI : IsProbabilityMeasure (shevtsovaNormalizedSumLaw P X m σ N) :=
    isProbabilityMeasure_shevtsovaNormalizedSumLaw_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N
  simpa [shevtsovaFn] using
    (continuous_charFun (μ := shevtsovaNormalizedSumLaw P X m σ N))

lemma continuous_shevtsovaFnAbs_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) :
    Continuous (shevtsovaFnAbs P X m σ N) := by
  simpa [shevtsovaFnAbs] using
    (continuous_shevtsovaFn_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N).norm

lemma continuous_shevtsovaNormalCharFun :
    Continuous (fun t : ℝ => charFun standardNormalMeasure t) :=
  continuous_charFun (μ := standardNormalMeasure)

lemma continuous_shevtsovaRn_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) :
    Continuous (shevtsovaRn P X m σ N) := by
  simpa [shevtsovaRn] using
    ((continuous_shevtsovaFn_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N).sub
        continuous_shevtsovaNormalCharFun).norm

lemma integrableOn_shevtsovaFnAbs_comp_mul_Icc_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (T a b : ℝ) :
    IntegrableOn
      (fun t : ℝ => shevtsovaFnAbs P X m σ N (T * t))
      (Set.Icc a b) := by
  exact
    ((continuous_shevtsovaFnAbs_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N).comp
        (continuous_const.mul continuous_id)).integrableOn_Icc

lemma integrableOn_shevtsovaRn_comp_mul_Icc_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (T a b : ℝ) :
    IntegrableOn
      (fun t : ℝ => shevtsovaRn P X m σ N (T * t))
      (Set.Icc a b) := by
  exact
    ((continuous_shevtsovaRn_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N).comp
        (continuous_const.mul continuous_id)).integrableOn_Icc

lemma shevtsovaDelta_isLeast_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) :
    measureCDFErrorIsLeast
      (shevtsovaNormalizedSumLaw P X m σ N) standardNormalMeasure
      (shevtsovaDelta P X m σ N) := by
  have hZ : AEMeasurable (normalizedSum X m σ N) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable N
  letI : IsProbabilityMeasure (shevtsovaNormalizedSumLaw P X m σ N) := by
    unfold shevtsovaNormalizedSumLaw
    exact Measure.isProbabilityMeasure_map hZ
  unfold shevtsovaDelta
  exact measureCDFErrorSup_isLeast _ _

lemma shevtsovaDelta_nonneg_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ) :
    0 ≤ shevtsovaDelta P X m σ N := by
  have hbound := (shevtsovaDelta_isLeast_of_hypotheses hBE N).1 0
  exact (abs_nonneg _).trans hbound

lemma shevtsovaDelta_le_of_measureCDFErrorLE
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ δ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) {N : ℕ}
    (hδ :
      measureCDFErrorLE
        (shevtsovaNormalizedSumLaw P X m σ N) standardNormalMeasure δ) :
    shevtsovaDelta P X m σ N ≤ δ :=
  (shevtsovaDelta_isLeast_of_hypotheses hBE N).2 δ hδ

lemma measureCDFErrorLE_of_shevtsovaDelta_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ δ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) {N : ℕ}
    (hδ : shevtsovaDelta P X m σ N ≤ δ) :
    measureCDFErrorLE
      (shevtsovaNormalizedSumLaw P X m σ N) standardNormalMeasure δ :=
  measureCDFErrorLE_mono
    (shevtsovaDelta_isLeast_of_hypotheses hBE N).1 hδ

/-- Lyapunov fraction `ρ / √N`, separated from the eventual absolute
Berry-Esseen constant. -/
def shevtsovaLyapunovFraction (rho : ℝ) (N : ℕ) : ℝ :=
  rho / Real.sqrt (N : ℝ)

lemma shevtsovaLyapunovFraction_nonneg {rho : ℝ} {N : ℕ}
    (hrho : 0 ≤ rho) :
    0 ≤ shevtsovaLyapunovFraction rho N := by
  unfold shevtsovaLyapunovFraction
  exact div_nonneg hrho (Real.sqrt_nonneg _)

lemma shevtsovaLyapunovFraction_eq_berryEsseenRate_one
    (rho : ℝ) (N : ℕ) :
    shevtsovaLyapunovFraction rho N = berryEsseenRate 1 rho N := by
  unfold shevtsovaLyapunovFraction berryEsseenRate
  ring

/-- Fourier integral estimate for the actual HDP normalized-sum law, after
rewriting its characteristic function as the power of the standardized
one-summand law.  This is the measure-level bridge from independence to the
integrated Durrett/Feller Fourier estimate. -/
lemma fourierDistanceIntegral_normalizedSum_standardNormal_le_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hX : ∀ n, AEMeasurable (X n) P)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h3 :
      Integrable (fun x : ℝ => |x| ^ 3)
        (P.map (fun ω => (X 0 ω - m) / σ)))
    (hmean :
      ∫ x : ℝ, x ∂(P.map (fun ω => (X 0 ω - m) / σ)) = 0)
    (hsecond :
      ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => (X 0 ω - m) / σ)) = 1)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) *
          (∫ x, |x| ^ 3 ∂(P.map (fun ω => (X 0 ω - m) / σ))) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    fourierDistanceIntegral
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure L ≤
      (18 / 5) *
          (∫ x, |x| ^ 3 ∂(P.map (fun ω => (X 0 ω - m) / σ))) /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hX 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hstd_meas
  have hrate :
      fourierDistanceIntegralOfFns
        (fun t : ℝ =>
          charFun ν (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1))
        (charFun standardNormalMeasure) L ≤
        (18 / 5) * (∫ x, |x| ^ 3 ∂ν) /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ) := by
    exact fourierDistanceIntegralOfFns_scaled_pow_succ_standardNormal_le_rate
      (μ := ν) (by simpa [ν] using h3) (by simpa [ν] using hmean)
      (by simpa [ν] using hsecond) hn
      (by simpa [ν] using hWindow)
      (by simpa [ν] using hSmall)
  have hcf :
      (fun t : ℝ =>
        charFun (P.map (normalizedSum X m σ (n + 1))) t) =
      fun t : ℝ =>
        charFun ν (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
    funext t
    simpa [ν] using
      charFun_normalizedSum_eq_standardized_pow
        (μ := P) hX hindep hident (n + 1) t
  simpa [fourierDistanceIntegral, hcf, ν] using hrate

/-- Durrett/Feller Fourier integral estimate for the actual HDP normalized-sum
law, using the larger `t² ≤ 2N` window and the `N ≥ 10` decay step. -/
lemma fourierDistanceIntegral_normalizedSum_standardNormal_le_durrett_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hX : ∀ n, AEMeasurable (X n) P)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h3 :
      Integrable (fun x : ℝ => |x| ^ 3)
        (P.map (fun ω => (X 0 ω - m) / σ)))
    (hmean :
      ∫ x : ℝ, x ∂(P.map (fun ω => (X 0 ω - m) / σ)) = 0)
    (hsecond :
      ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => (X 0 ω - m) / σ)) = 1)
    {n : ℕ} (hn : 9 ≤ n) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (∫ x, |x| ^ 3 ∂(P.map (fun ω => (X 0 ω - m) / σ))) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    fourierDistanceIntegral
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure L ≤
      (6 / 5) *
          (∫ x, |x| ^ 3 ∂(P.map (fun ω => (X 0 ω - m) / σ))) /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hX 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hstd_meas
  have hrate :
      fourierDistanceIntegralOfFns
        (fun t : ℝ =>
          charFun ν (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1))
        (charFun standardNormalMeasure) L ≤
        (6 / 5) * (∫ x, |x| ^ 3 ∂ν) /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ) := by
    exact fourierDistanceIntegralOfFns_scaled_pow_succ_standardNormal_le_durrett_rate
      (μ := ν) (by simpa [ν] using h3) (by simpa [ν] using hmean)
      (by simpa [ν] using hsecond) hn
      (by simpa [ν] using hWindow)
      (by simpa [ν] using hSmall)
  have hcf :
      (fun t : ℝ =>
        charFun (P.map (normalizedSum X m σ (n + 1))) t) =
      fun t : ℝ =>
        charFun ν (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
    funext t
    simpa [ν] using
      charFun_normalizedSum_eq_standardized_pow
        (μ := P) hX hindep hident (n + 1) t
  simpa [fourierDistanceIntegral, hcf, ν] using hrate

/-- The normalized-sum Fourier integral estimate specialized to the
book-facing Berry-Esseen hypotheses.  The remaining assumptions are only the
frequency-window inequalities used to choose the Esseen cutoff. -/
lemma fourierDistanceIntegral_normalizedSum_standardNormal_le_rate_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    fourierDistanceIntegral
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure L ≤
      (18 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3)
        (P.map (fun ω => (X 0 ω - m) / σ)) :=
    integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hmean :
      ∫ x : ℝ, x ∂(P.map (fun ω => (X 0 ω - m) / σ)) = 0 :=
    integral_standardizedLaw_id_eq_zero
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_int (hBE.mean_eq 0) hBE.sigma_pos.ne'
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => (X 0 ω - m) / σ)) = 1 :=
    integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂(P.map (fun ω => (X 0 ω - m) / σ)) =
        berryEsseenRho X P m σ := by
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  have hSmall' :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) *
          (∫ x, |x| ^ 3 ∂(P.map (fun ω => (X 0 ω - m) / σ))) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1 := by
    intro t ht
    simpa [hM] using hSmall t ht
  have hrate :=
    fourierDistanceIntegral_normalizedSum_standardNormal_le_rate
      (P := P) (X := X) (m := m) (σ := σ)
      hBE.aemeasurable hBE.independent hBE.identDistrib
      h3 hmean hsecond hn hWindow hSmall'
  simpa [hM] using hrate

/-- Durrett/Feller Fourier integral estimate specialized to the book-facing
Berry-Esseen hypotheses, with the larger `t² ≤ 2N` window. -/
lemma fourierDistanceIntegral_normalizedSum_standardNormal_le_durrett_rate_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    fourierDistanceIntegral
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure L ≤
      (6 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3)
        (P.map (fun ω => (X 0 ω - m) / σ)) :=
    integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hmean :
      ∫ x : ℝ, x ∂(P.map (fun ω => (X 0 ω - m) / σ)) = 0 :=
    integral_standardizedLaw_id_eq_zero
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_int (hBE.mean_eq 0) hBE.sigma_pos.ne'
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => (X 0 ω - m) / σ)) = 1 :=
    integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂(P.map (fun ω => (X 0 ω - m) / σ)) =
        berryEsseenRho X P m σ := by
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  have hSmall' :
      ∀ t ∈ Set.Icc (-L) L,
        (∫ x, |x| ^ 3 ∂(P.map (fun ω => (X 0 ω - m) / σ))) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3 := by
    intro t ht
    simpa [hM] using hSmall t ht
  have hrate :=
    fourierDistanceIntegral_normalizedSum_standardNormal_le_durrett_rate
      (P := P) (X := X) (m := m) (σ := σ)
      hBE.aemeasurable hBE.independent hBE.identDistrib
      h3 hmean hsecond hn hWindow hSmall'
  simpa [hM] using hrate

/-- Integrability of the original Fourier-distance integrand for the
normalized-sum law, specialized to the Berry-Esseen hypotheses and a valid
central/small-frequency window. -/
lemma integrableOn_fourierDistanceIntegrand_normalizedSum_standardNormal_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (_hn : 1 ≤ n) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    IntegrableOn
      (fun t : ℝ =>
        ‖charFun (P.map (normalizedSum X m σ (n + 1))) t -
          charFun standardNormalMeasure t‖ / |t|)
      (Set.Icc (-L) L) := by
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hstd_meas
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3) ν := by
    dsimp [ν]
    exact integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hmean :
      ∫ x : ℝ, x ∂ν = 0 := by
    dsimp [ν]
    exact integral_standardizedLaw_id_eq_zero
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_int (hBE.mean_eq 0) hBE.sigma_pos.ne'
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂ν = 1 := by
    dsimp [ν]
    exact integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂ν = berryEsseenRho X P m σ := by
    dsimp [ν]
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  have hSmall' :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * (∫ x, |x| ^ 3 ∂ν) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1 := by
    intro t ht
    simpa [hM] using hSmall t ht
  have hInt :=
    integrableOn_fourierDistanceIntegrand_scaled_pow_succ_standardNormal
      (μ := ν) h3 hmean hsecond n hWindow hSmall'
  have hcf :
      (fun t : ℝ =>
        charFun (P.map (normalizedSum X m σ (n + 1))) t) =
      fun t : ℝ =>
        charFun ν (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
    funext t
    simpa [ν] using
      charFun_normalizedSum_eq_standardized_pow
        (μ := P) hBE.aemeasurable hBE.independent hBE.identDistrib (n + 1) t
  simpa [hcf] using hInt

/-- Integrability of the original Fourier-distance integrand under Durrett's
larger-window hypotheses. -/
lemma integrableOn_fourierDistanceIntegrand_normalizedSum_standardNormal_of_hypotheses_durrett
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    IntegrableOn
      (fun t : ℝ =>
        ‖charFun (P.map (normalizedSum X m σ (n + 1))) t -
          charFun standardNormalMeasure t‖ / |t|)
      (Set.Icc (-L) L) := by
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hstd_meas
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3) ν := by
    dsimp [ν]
    exact integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hmean :
      ∫ x : ℝ, x ∂ν = 0 := by
    dsimp [ν]
    exact integral_standardizedLaw_id_eq_zero
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_int (hBE.mean_eq 0) hBE.sigma_pos.ne'
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂ν = 1 := by
    dsimp [ν]
    exact integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂ν = berryEsseenRho X P m σ := by
    dsimp [ν]
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  have hSmall' :
      ∀ t ∈ Set.Icc (-L) L,
        (∫ x, |x| ^ 3 ∂ν) *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3 := by
    intro t ht
    simpa [hM] using hSmall t ht
  have hInt :=
    integrableOn_fourierDistanceIntegrand_scaled_pow_succ_standardNormal_durrett
      (μ := ν) h3 hmean hsecond hn hWindow hSmall'
  have hcf :
      (fun t : ℝ =>
        charFun (P.map (normalizedSum X m σ (n + 1))) t) =
      fun t : ℝ =>
        charFun ν (t / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
    funext t
    simpa [ν] using
      charFun_normalizedSum_eq_standardized_pow
        (μ := P) hBE.aemeasurable hBE.independent hBE.identDistrib (n + 1) t
  simpa [hcf] using hInt

/-- Esseen/Fourier smoothing for normalized sums under the book-facing
Berry-Esseen hypotheses, conditional only on the smoothed inversion identity
for the Polya-smoothed laws and the chosen Fourier window. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_inversion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1)
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth (P.map (normalizedSum X m σ (n + 1)))
          (polyaKernelMeasure L))
        (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))
        (charFun
          (polyaSmooth (P.map (normalizedSum X m σ (n + 1)))
            (polyaKernelMeasure L)))
        (charFun
          (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))) L) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      (esseenFourierBudget
        (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure 1 L) := by
  have hZ :
      AEMeasurable (normalizedSum X m σ (n + 1)) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable (n + 1)
  letI : IsProbabilityMeasure (P.map (normalizedSum X m σ (n + 1))) :=
    Measure.isProbabilityMeasure_map hZ
  have hOrigInt :
      IntegrableOn
        (fun t : ℝ =>
          ‖charFun (P.map (normalizedSum X m σ (n + 1))) t -
            charFun standardNormalMeasure t‖ / |t|)
        (Set.Icc (-L) L) :=
    integrableOn_fourierDistanceIntegrand_normalizedSum_standardNormal_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE hn hWindow hSmall
  exact
    esseenFourierSmoothing_standardNormal_polyaKernelMeasure_from_inversion_sup
      (μ := P.map (normalizedSum X m σ (n + 1)))
      (L := L) hL hInv hOrigInt

/-- Esseen/Fourier smoothing for normalized sums under the book-facing
Berry-Esseen hypotheses, using any available CDF Lipschitz constant for the
standard-normal target.  The Polya-smoothed inversion identity is discharged
locally from the finite first moments implied by the third-moment hypothesis. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_lipschitz
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    {lam : ℝ} (hlam : 0 < lam)
    (hLip : measureCDFLipschitz standardNormalMeasure lam)
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      (esseenFourierBudget
        (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure lam L) := by
  have hZ :
      AEMeasurable (normalizedSum X m σ (n + 1)) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable (n + 1)
  letI : IsProbabilityMeasure (P.map (normalizedSum X m σ (n + 1))) :=
    Measure.isProbabilityMeasure_map hZ
  have hOrigInt :
      IntegrableOn
        (fun t : ℝ =>
          ‖charFun (P.map (normalizedSum X m σ (n + 1))) t -
            charFun standardNormalMeasure t‖ / |t|)
        (Set.Icc (-L) L) :=
    integrableOn_fourierDistanceIntegrand_normalizedSum_standardNormal_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE hn hWindow hSmall
  have hμ1 :
      Integrable (fun x : ℝ => x)
        (P.map (normalizedSum X m σ (n + 1))) :=
    integrable_id_normalizedSumLaw_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE (n + 1)
  exact
    esseenFourierSmoothing_standardNormal_polyaKernelMeasure_from_integrable_sup_lipschitz
      (μ := P.map (normalizedSum X m σ (n + 1)))
      (lam := lam) (L := L) hL hlam hLip hμ1 hOrigInt

/-- Esseen/Fourier smoothing for normalized sums under the book-facing
Berry-Esseen hypotheses.  The Polya-smoothed inversion identity is discharged
locally from the finite first moments implied by the third-moment hypothesis. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      (esseenFourierBudget
        (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure 1 L) := by
  exact
    measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_lipschitz
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn hL (lam := 1) (by norm_num)
      standardNormal_measureCDFLipschitz hWindow hSmall

/-- Esseen/Fourier smoothing for normalized sums with the standard-normal
Lipschitz constant `2 / 5`. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_two_fifths
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      (esseenFourierBudget
        (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure (2 / 5) L) := by
  exact
    measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_lipschitz
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn hL (lam := 2 / 5) (by norm_num)
      standardNormal_measureCDFLipschitz_two_fifths hWindow hSmall

/-- A square cutoff bound implies the central-window condition used in the
pointwise Berry-Esseen Fourier estimate. -/
lemma berryEsseenWindow_of_cutoff_sq {n : ℕ} {L : ℝ}
    (hLsq : L ^ 2 ≤ ((n + 1 : ℕ) : ℝ)) :
    ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ) := by
  intro t ht
  have ht_abs : |t| ≤ L := abs_le.mpr ht
  have hsq_abs : |t| ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg t) ht_abs 2
  calc
    t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    _ ≤ L ^ 2 := hsq_abs
    _ ≤ ((n + 1 : ℕ) : ℝ) := hLsq

/-- A cutoff bound `(2 / 3) ρ L ≤ √N` implies the small-frequency Taylor
condition on the whole window `[-L,L]`. -/
lemma berryEsseenSmall_of_cutoff_bound {n : ℕ} {rho L : ℝ}
    (hrho : 0 ≤ rho)
    (hCut : (2 / 3 : ℝ) * rho * L ≤ Real.sqrt ((n + 1 : ℕ) : ℝ)) :
    ∀ t ∈ Set.Icc (-L) L,
      (2 / 3 : ℝ) * rho *
        |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1 := by
  have hNpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr hNpos
  intro t ht
  have ht_abs : |t| ≤ L := abs_le.mpr ht
  have hcoef0 : 0 ≤ (2 / 3 : ℝ) * rho := by positivity
  have hnum :
      (2 / 3 : ℝ) * rho * |t| ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    (mul_le_mul_of_nonneg_left ht_abs hcoef0).trans hCut
  have hdiv :
      ((2 / 3 : ℝ) * rho * |t|) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hsqrt_pos]
    simpa using hnum
  rw [abs_div, abs_of_pos hsqrt_pos]
  have hrewrite :
      (2 / 3 : ℝ) * rho *
          (|t| / Real.sqrt ((n + 1 : ℕ) : ℝ)) =
        ((2 / 3 : ℝ) * rho * |t|) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    ring
  rw [hrewrite]
  exact hdiv

/-- A square cutoff bound implies Durrett's larger central-window condition. -/
lemma berryEsseenDurrettWindow_of_cutoff_sq {n : ℕ} {L : ℝ}
    (hLsq : L ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ)) :
    ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
  intro t ht
  have ht_abs : |t| ≤ L := abs_le.mpr ht
  have hsq_abs : |t| ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg t) ht_abs 2
  calc
    t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    _ ≤ L ^ 2 := hsq_abs
    _ ≤ 2 * ((n + 1 : ℕ) : ℝ) := hLsq

/-- A cutoff bound `ρL ≤ (4/3)√N` implies Durrett's small-frequency
condition on the whole window `[-L,L]`. -/
lemma berryEsseenDurrettSmall_of_cutoff_bound {n : ℕ} {rho L : ℝ}
    (hrho : 0 ≤ rho)
    (hCut : rho * L ≤ (4 / 3 : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)) :
    ∀ t ∈ Set.Icc (-L) L,
      rho * |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3 := by
  have hNpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr hNpos
  intro t ht
  have ht_abs : |t| ≤ L := abs_le.mpr ht
  have hnum :
      rho * |t| ≤ (4 / 3 : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    (mul_le_mul_of_nonneg_left ht_abs hrho).trans hCut
  have hdiv :
      (rho * |t|) / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ 4 / 3 := by
    rw [div_le_iff₀ hsqrt_pos]
    simpa [mul_assoc] using hnum
  rw [abs_div, abs_of_pos hsqrt_pos]
  have hrewrite :
      rho * (|t| / Real.sqrt ((n + 1 : ℕ) : ℝ)) =
        (rho * |t|) / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    ring
  rw [hrewrite]
  exact hdiv

/-- The explicit Esseen budget bound obtained from the integrated
Durrett/Feller Fourier estimate plus the Polya smoothing tail. -/
lemma esseenFourierBudget_normalizedSum_standardNormal_le_rate_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {lam L : ℝ}
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    esseenFourierBudget
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure lam L ≤
      (1 / Real.pi) *
        ((18 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ)) +
        polyaTailBudget lam L := by
  have hFourier :
      fourierDistanceIntegral
        (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure L ≤
        (18 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ) :=
    fourierDistanceIntegral_normalizedSum_standardNormal_le_rate_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE hn hWindow hSmall
  unfold esseenFourierBudget
  have hcoef : 0 ≤ (1 / Real.pi : ℝ) :=
    div_nonneg zero_le_one Real.pi_pos.le
  simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right
    (mul_le_mul_of_nonneg_left hFourier hcoef)
    (polyaTailBudget lam L)

/-- Conditional end-of-chain CDF estimate with all rate constants except the
choice of Fourier cutoff exposed explicitly.  The only remaining analytic
input is the smoothed inversion identity for the concrete Polya-smoothed
laws. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_inversion_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1)
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth (P.map (normalizedSum X m σ (n + 1)))
          (polyaKernelMeasure L))
        (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))
        (charFun
          (polyaSmooth (P.map (normalizedSum X m σ (n + 1)))
            (polyaKernelMeasure L)))
        (charFun
          (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))) L) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      ((1 / Real.pi) *
        ((18 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ)) +
        polyaTailBudget 1 L) := by
  exact measureCDFErrorLE_mono
    (measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_inversion
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn hL hWindow hSmall hInv)
    (esseenFourierBudget_normalizedSum_standardNormal_le_rate_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn hWindow hSmall)

/-- End-of-chain CDF estimate with the Polya-smoothed inversion identity
discharged locally, parameterized by the CDF Lipschitz constant used for the
standard-normal smoothing tail.  All rate constants except the choice of
Fourier cutoff are exposed explicitly. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_rate_lipschitz
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    {lam : ℝ} (hlam : 0 < lam)
    (hLip : measureCDFLipschitz standardNormalMeasure lam)
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      ((1 / Real.pi) *
        ((18 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ)) +
        polyaTailBudget lam L) := by
  exact measureCDFErrorLE_mono
    (measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_lipschitz
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn hL (lam := lam) hlam hLip hWindow hSmall)
    (esseenFourierBudget_normalizedSum_standardNormal_le_rate_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) (lam := lam)
      hBE hn hWindow hSmall)

/-- End-of-chain CDF estimate with the Polya-smoothed inversion identity
discharged locally.  All rate constants except the choice of Fourier cutoff
are exposed explicitly. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      ((1 / Real.pi) *
        ((18 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ)) +
        polyaTailBudget 1 L) := by
  exact
    measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_rate_lipschitz
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn hL (lam := 1) (by norm_num)
      standardNormal_measureCDFLipschitz hWindow hSmall

/-- End-of-chain CDF estimate using the Gaussian Lipschitz constant `2 / 5`. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_rate_two_fifths
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      ((1 / Real.pi) *
        ((18 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ)) +
        polyaTailBudget (2 / 5) L) := by
  exact
    measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_rate_lipschitz
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn hL (lam := 2 / 5) (by norm_num)
      standardNormal_measureCDFLipschitz_two_fifths hWindow hSmall

/-- Durrett/Feller CDF estimate with all constants exposed, using the larger
Fourier window and Gaussian Lipschitz constant `2 / 5`. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_durrett_rate_two_fifths
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {L : ℝ} (hL : 0 < L)
    (hWindow :
      ∀ t ∈ Set.Icc (-L) L, t ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (-L) L,
        berryEsseenRho X P m σ *
          |t / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      ((1 / Real.pi) *
        ((6 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ)) +
        polyaTailBudget (2 / 5) L) := by
  have hZ :
      AEMeasurable (normalizedSum X m σ (n + 1)) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable (n + 1)
  letI : IsProbabilityMeasure (P.map (normalizedSum X m σ (n + 1))) :=
    Measure.isProbabilityMeasure_map hZ
  have hμ1 :
      Integrable (fun x : ℝ => x)
        (P.map (normalizedSum X m σ (n + 1))) :=
    integrable_id_normalizedSumLaw_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE (n + 1)
  have hOrigInt :
      IntegrableOn
        (fun θ : ℝ =>
          ‖charFun (P.map (normalizedSum X m σ (n + 1))) θ -
            charFun standardNormalMeasure θ‖ / |θ|)
        (Set.Icc (-L) L) :=
    integrableOn_fourierDistanceIntegrand_normalizedSum_standardNormal_of_hypotheses_durrett
      (P := P) (X := X) (m := m) (σ := σ) hBE hn hWindow hSmall
  have hSmooth :
      measureCDFErrorLE
        (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
        (esseenFourierBudget
          (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
          (2 / 5) L) :=
    esseenFourierSmoothing_standardNormal_polyaKernelMeasure_from_integrable_sup_two_fifths
      (μ := P.map (normalizedSum X m σ (n + 1)))
      (L := L) hL hμ1 hOrigInt
  have hFourier :
      fourierDistanceIntegral
        (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure L ≤
        (6 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ) :=
    fourierDistanceIntegral_normalizedSum_standardNormal_le_durrett_rate_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE hn hWindow hSmall
  refine measureCDFErrorLE_mono hSmooth ?_
  unfold esseenFourierBudget
  have hcoef : 0 ≤ (1 / Real.pi : ℝ) :=
    div_nonneg zero_le_one Real.pi_pos.le
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right
      (mul_le_mul_of_nonneg_left hFourier hcoef)
      (polyaTailBudget (2 / 5) L)

/-- Conditional CDF estimate using cutoff-side assumptions instead of the
pointwise window hypotheses.  This is the form intended for the eventual
choice of `L` in terms of `n` and `ρ`. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_inversion_rate_of_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    (hrho : 0 ≤ berryEsseenRho X P m σ)
    (hLsq : L ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hCut :
      (2 / 3 : ℝ) * berryEsseenRho X P m σ * L ≤
        Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hInv :
      inversionCDFFormulaFor
        (polyaSmooth (P.map (normalizedSum X m σ (n + 1)))
          (polyaKernelMeasure L))
        (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))
        (charFun
          (polyaSmooth (P.map (normalizedSum X m σ (n + 1)))
            (polyaKernelMeasure L)))
        (charFun
          (polyaSmooth standardNormalMeasure (polyaKernelMeasure L))) L) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      ((1 / Real.pi) *
        ((18 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ)) +
        polyaTailBudget 1 L) := by
  exact
    measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_inversion_rate
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn hL
      (berryEsseenWindow_of_cutoff_sq (n := n) (L := L) hLsq)
      (berryEsseenSmall_of_cutoff_bound
        (n := n) (rho := berryEsseenRho X P m σ) (L := L) hrho hCut)
      hInv

/-- CDF estimate using cutoff-side assumptions, with the Polya-smoothed
inversion identity discharged locally from the moment hypotheses, and with
the standard-normal Lipschitz constant left explicit. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_rate_of_cutoff_lipschitz
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    {lam : ℝ} (hlam : 0 < lam)
    (hLip : measureCDFLipschitz standardNormalMeasure lam)
    (hrho : 0 ≤ berryEsseenRho X P m σ)
    (hLsq : L ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hCut :
      (2 / 3 : ℝ) * berryEsseenRho X P m σ * L ≤
        Real.sqrt ((n + 1 : ℕ) : ℝ)) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      ((1 / Real.pi) *
        ((18 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ)) +
        polyaTailBudget lam L) := by
  exact
    measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_rate_lipschitz
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn hL (lam := lam) hlam hLip
      (berryEsseenWindow_of_cutoff_sq (n := n) (L := L) hLsq)
      (berryEsseenSmall_of_cutoff_bound
        (n := n) (rho := berryEsseenRho X P m σ) (L := L) hrho hCut)

/-- CDF estimate using cutoff-side assumptions, with the Polya-smoothed
inversion identity discharged locally from the moment hypotheses. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_rate_of_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    (hrho : 0 ≤ berryEsseenRho X P m σ)
    (hLsq : L ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hCut :
      (2 / 3 : ℝ) * berryEsseenRho X P m σ * L ≤
        Real.sqrt ((n + 1 : ℕ) : ℝ)) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      ((1 / Real.pi) *
        ((18 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ)) +
        polyaTailBudget 1 L) := by
  exact
    measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_rate_of_cutoff_lipschitz
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn hL (lam := 1) (by norm_num)
      standardNormal_measureCDFLipschitz hrho hLsq hCut

/-- CDF estimate using cutoff-side assumptions and the Gaussian Lipschitz
constant `2 / 5`. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_rate_of_cutoff_two_fifths
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 < L)
    (hrho : 0 ≤ berryEsseenRho X P m σ)
    (hLsq : L ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hCut :
      (2 / 3 : ℝ) * berryEsseenRho X P m σ * L ≤
        Real.sqrt ((n + 1 : ℕ) : ℝ)) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ (n + 1))) standardNormalMeasure
      ((1 / Real.pi) *
        ((18 / 5) * berryEsseenRho X P m σ /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 / ((n + 1 : ℕ) : ℝ)) +
        polyaTailBudget (2 / 5) L) := by
  exact
    measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_rate_of_cutoff_lipschitz
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn hL (lam := 2 / 5) (by norm_num)
      standardNormal_measureCDFLipschitz_two_fifths hrho hLsq hCut

lemma one_div_pi_le_one : (1 / Real.pi : ℝ) ≤ 1 := by
  rw [div_le_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_three]

lemma one_div_pi_le_one_div_three : (1 / Real.pi : ℝ) ≤ 1 / 3 := by
  rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ) < 3)]
  nlinarith [Real.pi_gt_three]

lemma one_div_pi_le_fifty_div_one_fifty_seven :
    (1 / Real.pi : ℝ) ≤ 50 / 157 := by
  rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ) < 157)]
  nlinarith [Real.pi_gt_d2]

/-- Leading coefficient of the present Durrett/Polya constant budget:
`(6 / 5 + 36 / 5) / π`.  The finite-size `2 / N` term is not included. -/
def berryEsseenDurrettPolyaLeadingConstant : ℝ :=
  42 / (5 * Real.pi)

/-- The present Durrett/Polya budget cannot yield the displayed HDP constant
`1` by arithmetic cleanup alone: its asymptotic leading coefficient is already
strictly larger than `1`. -/
lemma one_lt_berryEsseenDurrettPolyaLeadingConstant :
    1 < berryEsseenDurrettPolyaLeadingConstant := by
  unfold berryEsseenDurrettPolyaLeadingConstant
  have hden : 0 < (5 : ℝ) * Real.pi := by positivity
  rw [lt_div_iff₀ hden]
  nlinarith [Real.pi_lt_four]

/-- The same leading coefficient is below `3`, matching the public constant
proved by the local Durrett/Feller smoothing chain after the small-`N` split. -/
lemma berryEsseenDurrettPolyaLeadingConstant_lt_three :
    berryEsseenDurrettPolyaLeadingConstant < 3 := by
  unfold berryEsseenDurrettPolyaLeadingConstant
  have hden : 0 < (5 : ℝ) * Real.pi := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith [Real.pi_gt_three]

/-! ### Shevtsova-rate bridge for the eventual sharp HDP constant -/

/-- The scalar equation used by Prawitz/Shevtsova to define `θ₀`:
`θ² + 2 θ sin θ + 6 (cos θ - 1) = 0`. -/
def shevtsovaThetaEquationValue (θ : ℝ) : ℝ :=
  θ ^ 2 + 2 * θ * Real.sin θ + 6 * (Real.cos θ - 1)

/-- The Prawitz/Shevtsova root condition for `θ₀`, including the interval
where the quoted root lies. -/
def shevtsovaThetaEquation (θ : ℝ) : Prop :=
  θ ∈ Set.Icc Real.pi (2 * Real.pi) ∧
    shevtsovaThetaEquationValue θ = 0

lemma continuous_shevtsovaThetaEquationValue :
    Continuous shevtsovaThetaEquationValue := by
  unfold shevtsovaThetaEquationValue
  continuity

lemma shevtsovaThetaEquationValue_pi_eq :
    shevtsovaThetaEquationValue Real.pi = Real.pi ^ 2 - 12 := by
  unfold shevtsovaThetaEquationValue
  rw [Real.sin_pi, Real.cos_pi]
  ring

lemma shevtsovaThetaEquationValue_pi_nonpos :
    shevtsovaThetaEquationValue Real.pi ≤ 0 := by
  rw [shevtsovaThetaEquationValue_pi_eq]
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

lemma shevtsovaThetaEquationValue_two_pi_eq :
    shevtsovaThetaEquationValue (2 * Real.pi) = (2 * Real.pi) ^ 2 := by
  unfold shevtsovaThetaEquationValue
  rw [Real.sin_two_pi, Real.cos_two_pi]
  ring

lemma shevtsovaThetaEquationValue_two_pi_nonneg :
    0 ≤ shevtsovaThetaEquationValue (2 * Real.pi) := by
  rw [shevtsovaThetaEquationValue_two_pi_eq]
  positivity

/-- Existence of Prawitz/Shevtsova's `θ₀` in `[π, 2π]`.  This discharges the
first purely analytic root-existence target in the Shevtsova proof spine. -/
theorem shevtsovaTheta0_exists :
    ∃ θ : ℝ, shevtsovaThetaEquation θ := by
  have hπ_le : Real.pi ≤ 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hcont :
      ContinuousOn shevtsovaThetaEquationValue
        (Set.Icc Real.pi (2 * Real.pi)) :=
    continuous_shevtsovaThetaEquationValue.continuousOn
  have hzero_mem :
      0 ∈ Set.Icc
        (shevtsovaThetaEquationValue Real.pi)
        (shevtsovaThetaEquationValue (2 * Real.pi)) :=
    ⟨shevtsovaThetaEquationValue_pi_nonpos,
      shevtsovaThetaEquationValue_two_pi_nonneg⟩
  rcases intermediate_value_Icc hπ_le hcont hzero_mem with
    ⟨θ, hθmem, hθzero⟩
  exact ⟨θ, hθmem, hθzero⟩

/-- The Prawitz/Shevtsova root `θ₀`, chosen from the IVT existence theorem. -/
def shevtsovaTheta0 : ℝ :=
  Classical.choose shevtsovaTheta0_exists

lemma shevtsovaTheta0_spec :
    shevtsovaThetaEquation shevtsovaTheta0 :=
  Classical.choose_spec shevtsovaTheta0_exists

lemma shevtsovaTheta0_mem_Icc :
    shevtsovaTheta0 ∈ Set.Icc Real.pi (2 * Real.pi) :=
  shevtsovaTheta0_spec.1

lemma shevtsovaTheta0_equation :
    shevtsovaThetaEquationValue shevtsovaTheta0 = 0 :=
  shevtsovaTheta0_spec.2

lemma shevtsovaTheta0_pos :
    0 < shevtsovaTheta0 := by
  exact Real.pi_pos.trans_le shevtsovaTheta0_mem_Icc.1

/-- Prawitz's `κ` constant attached to the chosen root `θ₀`. -/
def shevtsovaKappa : ℝ :=
  (Real.cos shevtsovaTheta0 - 1 + shevtsovaTheta0 ^ 2 / 2) /
    shevtsovaTheta0 ^ 3

lemma shevtsovaKappa_denominator_pos :
    0 < shevtsovaTheta0 ^ 3 := by
  exact pow_pos shevtsovaTheta0_pos 3

lemma shevtsovaKappa_numerator_pos :
    0 < Real.cos shevtsovaTheta0 - 1 + shevtsovaTheta0 ^ 2 / 2 := by
  have hcos : -1 ≤ Real.cos shevtsovaTheta0 :=
    Real.neg_one_le_cos shevtsovaTheta0
  have htheta_gt_three : 3 < shevtsovaTheta0 :=
    Real.pi_gt_three.trans_le shevtsovaTheta0_mem_Icc.1
  nlinarith

lemma shevtsovaKappa_pos :
    0 < shevtsovaKappa := by
  unfold shevtsovaKappa
  exact div_pos shevtsovaKappa_numerator_pos shevtsovaKappa_denominator_pos

/-- A crude upper bound on Prawitz's `κ`, enough for later positivity and
branch estimates. -/
lemma shevtsovaKappa_lt_one :
    shevtsovaKappa < 1 := by
  unfold shevtsovaKappa
  rw [div_lt_iff₀ shevtsovaKappa_denominator_pos]
  have hnum_le :
      Real.cos shevtsovaTheta0 - 1 + shevtsovaTheta0 ^ 2 / 2 ≤
        shevtsovaTheta0 ^ 2 / 2 := by
    nlinarith [Real.cos_le_one shevtsovaTheta0]
  have htheta_gt_one : 1 < shevtsovaTheta0 := by
    nlinarith [Real.pi_gt_three, shevtsovaTheta0_mem_Icc.1]
  have hsq_pos : 0 < shevtsovaTheta0 ^ 2 :=
    sq_pos_of_pos shevtsovaTheta0_pos
  have hpow : shevtsovaTheta0 ^ 2 / 2 < shevtsovaTheta0 ^ 3 := by
    nlinarith
  simpa [one_mul] using hnum_le.trans_lt hpow

lemma shevtsovaKappa_mul_theta0_eq :
    shevtsovaKappa * shevtsovaTheta0 =
      (Real.cos shevtsovaTheta0 - 1 + shevtsovaTheta0 ^ 2 / 2) /
        shevtsovaTheta0 ^ 2 := by
  unfold shevtsovaKappa
  field_simp [shevtsovaTheta0_pos.ne']

lemma shevtsovaKappa_mul_theta0_le_half :
    shevtsovaKappa * shevtsovaTheta0 ≤ 1 / 2 := by
  rw [shevtsovaKappa_mul_theta0_eq]
  have hden : 0 < shevtsovaTheta0 ^ 2 := sq_pos_of_pos shevtsovaTheta0_pos
  rw [div_le_iff₀ hden]
  nlinarith [Real.cos_le_one shevtsovaTheta0]

/-- Cosine Taylor-remainder ratio whose maximum is encoded by Prawitz's
constant `κ`.  The removable value at zero is irrelevant for the derivative
and supremum statements used later. -/
def shevtsovaCosRemainderRatio (x : ℝ) : ℝ :=
  (Real.cos x - 1 + x ^ 2 / 2) / x ^ 3

lemma shevtsovaCosRemainderRatio_theta0_eq_kappa :
    shevtsovaCosRemainderRatio shevtsovaTheta0 = shevtsovaKappa := rfl

lemma hasDerivAt_shevtsovaCosRemainderRatio {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt shevtsovaCosRemainderRatio
      (-(shevtsovaThetaEquationValue x) / (2 * x ^ 4)) x := by
  have hnum :
      HasDerivAt
        (fun y : ℝ => Real.cos y - 1 + y ^ 2 / 2)
        (-Real.sin x + x) x := by
    have hcos :
        HasDerivAt (fun y : ℝ => Real.cos y - 1)
          (-Real.sin x) x := by
      exact (Real.hasDerivAt_cos x).sub_const 1
    have hsq :
        HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      convert (hasDerivAt_pow (n := 2) (x := x)).div_const 2 using 1
      ring
    simpa [add_comm, add_left_comm, add_assoc] using hcos.add hsq
  have hden : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_pow (n := 3) (x := x))
  have hden_ne : x ^ 3 ≠ 0 := pow_ne_zero 3 hx
  have hquot := hnum.div hden hden_ne
  unfold shevtsovaCosRemainderRatio
  convert hquot using 1
  unfold shevtsovaThetaEquationValue
  field_simp [hx]
  ring_nf

lemma deriv_shevtsovaCosRemainderRatio_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    deriv shevtsovaCosRemainderRatio x =
      -(shevtsovaThetaEquationValue x) / (2 * x ^ 4) :=
  (hasDerivAt_shevtsovaCosRemainderRatio hx).deriv

lemma deriv_shevtsovaCosRemainderRatio_theta0 :
    deriv shevtsovaCosRemainderRatio shevtsovaTheta0 = 0 := by
  rw [deriv_shevtsovaCosRemainderRatio_of_ne_zero shevtsovaTheta0_pos.ne',
    shevtsovaTheta0_equation]
  simp

lemma sin_nonpos_of_mem_Icc_pi_two_pi {u : ℝ}
    (hu : u ∈ Set.Icc Real.pi (2 * Real.pi)) :
    Real.sin u ≤ 0 := by
  have hsub_mem : 2 * Real.pi - u ∈ Set.Icc 0 Real.pi := by
    constructor <;> linarith [hu.1, hu.2]
  have hsin_nonneg :
      0 ≤ Real.sin (2 * Real.pi - u) :=
    Real.sin_nonneg_of_mem_Icc hsub_mem
  rw [Real.sin_two_pi_sub] at hsin_nonneg
  linarith

lemma hasDerivAt_shevtsovaThetaEquationValue (θ : ℝ) :
    HasDerivAt shevtsovaThetaEquationValue
      (2 * θ * (1 + Real.cos θ) - 4 * Real.sin θ) θ := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * θ) θ := by
    simpa using (hasDerivAt_pow (n := 2) (x := θ))
  have hysin :
      HasDerivAt (fun y : ℝ => y * Real.sin y)
        (Real.sin θ + θ * Real.cos θ) θ :=
    by
      simpa using (hasDerivAt_id θ).mul (Real.hasDerivAt_sin θ)
  have htwoysin :
      HasDerivAt (fun y : ℝ => 2 * y * Real.sin y)
        (2 * Real.sin θ + 2 * θ * Real.cos θ) θ := by
    convert hysin.const_mul 2 using 1 <;> ring_nf
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos y - 1)
        (-Real.sin θ) θ :=
    (Real.hasDerivAt_cos θ).sub_const 1
  have hsixcos :
      HasDerivAt (fun y : ℝ => 6 * (Real.cos y - 1))
        (6 * (-Real.sin θ)) θ :=
    hcos.const_mul 6
  have h :=
    (hsq.add htwoysin).add hsixcos
  unfold shevtsovaThetaEquationValue
  convert h using 1
  ring

lemma deriv_shevtsovaThetaEquationValue (θ : ℝ) :
    deriv shevtsovaThetaEquationValue θ =
      2 * θ * (1 + Real.cos θ) - 4 * Real.sin θ :=
  (hasDerivAt_shevtsovaThetaEquationValue θ).deriv

lemma shevtsovaThetaEquationValue_zero_eq :
    shevtsovaThetaEquationValue 0 = 0 := by
  unfold shevtsovaThetaEquationValue
  rw [Real.sin_zero, Real.cos_zero]
  norm_num

lemma shevtsovaThetaEquationValue_deriv_nonpos_of_mem_Icc_zero_pi
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    deriv shevtsovaThetaEquationValue θ ≤ 0 := by
  rw [deriv_shevtsovaThetaEquationValue]
  by_cases hπ : θ = Real.pi
  · subst θ
    rw [Real.sin_pi, Real.cos_pi]
    norm_num
  · have hθ_lt_pi : θ < Real.pi := lt_of_le_of_ne hθ.2 hπ
    have hy_nonneg : 0 ≤ θ / 2 := by nlinarith [hθ.1]
    have hy_lt : θ / 2 < Real.pi / 2 := by linarith
    have htan : θ / 2 ≤ Real.tan (θ / 2) :=
      Real.le_tan hy_nonneg hy_lt
    have hy_cos_pos : 0 < Real.cos (θ / 2) := by
      exact Real.cos_pos_of_mem_Ioo
        ⟨by nlinarith [hθ.1, Real.pi_pos], by linarith⟩
    have hycos : (θ / 2) * Real.cos (θ / 2) ≤ Real.sin (θ / 2) := by
      rw [Real.tan_eq_sin_div_cos] at htan
      rw [le_div_iff₀ hy_cos_pos] at htan
      simpa [mul_comm, mul_left_comm, mul_assoc] using htan
    have hmul :
        (θ / 2 * Real.cos (θ / 2)) *
            (4 * Real.cos (θ / 2)) ≤
          Real.sin (θ / 2) * (4 * Real.cos (θ / 2)) :=
      mul_le_mul_of_nonneg_right hycos (by positivity)
    have hmain : θ * (1 + Real.cos θ) ≤ 2 * Real.sin θ := by
      convert hmul using 1
      · rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
        ring_nf
      · rw [show θ = 2 * (θ / 2) by ring, Real.sin_two_mul]
        ring_nf
    nlinarith

lemma differentiableOn_shevtsovaThetaEquationValue_interior_Icc_zero_pi :
    DifferentiableOn ℝ shevtsovaThetaEquationValue
      (interior (Set.Icc 0 Real.pi)) := by
  intro θ _hθ
  exact (hasDerivAt_shevtsovaThetaEquationValue θ).differentiableAt.differentiableWithinAt

lemma antitoneOn_shevtsovaThetaEquationValue_Icc_zero_pi :
    AntitoneOn shevtsovaThetaEquationValue
      (Set.Icc 0 Real.pi) := by
  exact antitoneOn_of_deriv_nonpos
    (convex_Icc 0 Real.pi)
    continuous_shevtsovaThetaEquationValue.continuousOn
    differentiableOn_shevtsovaThetaEquationValue_interior_Icc_zero_pi
    (fun θ hθ =>
      shevtsovaThetaEquationValue_deriv_nonpos_of_mem_Icc_zero_pi
        (interior_subset hθ))

lemma shevtsovaThetaEquationValue_nonpos_of_mem_Icc_zero_pi
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    shevtsovaThetaEquationValue θ ≤ 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 Real.pi :=
    ⟨le_rfl, Real.pi_pos.le⟩
  have hanti :=
    antitoneOn_shevtsovaThetaEquationValue_Icc_zero_pi
      hzero hθ hθ.1
  rwa [shevtsovaThetaEquationValue_zero_eq] at hanti

lemma shevtsovaThetaEquationValue_deriv_nonneg_of_mem_Icc_pi_two_pi
    {θ : ℝ} (hθ : θ ∈ Set.Icc Real.pi (2 * Real.pi)) :
    0 ≤ deriv shevtsovaThetaEquationValue θ := by
  rw [deriv_shevtsovaThetaEquationValue]
  have hθ_nonneg : 0 ≤ θ := (Real.pi_pos.trans_le hθ.1).le
  have hsin : Real.sin θ ≤ 0 :=
    sin_nonpos_of_mem_Icc_pi_two_pi hθ
  have hcos : 0 ≤ 1 + Real.cos θ := by
    nlinarith [Real.neg_one_le_cos θ]
  have hleft : 0 ≤ 2 * θ * (1 + Real.cos θ) := by
    positivity
  nlinarith

lemma differentiableOn_shevtsovaThetaEquationValue_interior_Icc_pi_two_pi :
    DifferentiableOn ℝ shevtsovaThetaEquationValue
      (interior (Set.Icc Real.pi (2 * Real.pi))) := by
  intro θ hθ
  exact (hasDerivAt_shevtsovaThetaEquationValue θ).differentiableAt.differentiableWithinAt

lemma monotoneOn_shevtsovaThetaEquationValue_Icc_pi_two_pi :
    MonotoneOn shevtsovaThetaEquationValue
      (Set.Icc Real.pi (2 * Real.pi)) := by
  exact monotoneOn_of_deriv_nonneg
    (convex_Icc Real.pi (2 * Real.pi))
    continuous_shevtsovaThetaEquationValue.continuousOn
    differentiableOn_shevtsovaThetaEquationValue_interior_Icc_pi_two_pi
    (fun θ hθ =>
      shevtsovaThetaEquationValue_deriv_nonneg_of_mem_Icc_pi_two_pi
        (interior_subset hθ))

lemma shevtsovaThetaEquationValue_nonpos_of_mem_Icc_pi_theta0
    {θ : ℝ} (hθ : θ ∈ Set.Icc Real.pi shevtsovaTheta0) :
    shevtsovaThetaEquationValue θ ≤ 0 := by
  have hθ_full : θ ∈ Set.Icc Real.pi (2 * Real.pi) :=
    ⟨hθ.1, hθ.2.trans shevtsovaTheta0_mem_Icc.2⟩
  have hmono :=
    monotoneOn_shevtsovaThetaEquationValue_Icc_pi_two_pi
      hθ_full shevtsovaTheta0_mem_Icc hθ.2
  rwa [shevtsovaTheta0_equation] at hmono

lemma shevtsovaThetaEquationValue_nonneg_of_mem_Icc_theta0_two_pi
    {θ : ℝ} (hθ : θ ∈ Set.Icc shevtsovaTheta0 (2 * Real.pi)) :
    0 ≤ shevtsovaThetaEquationValue θ := by
  have hθ_full : θ ∈ Set.Icc Real.pi (2 * Real.pi) :=
    ⟨shevtsovaTheta0_mem_Icc.1.trans hθ.1, hθ.2⟩
  have hmono :=
    monotoneOn_shevtsovaThetaEquationValue_Icc_pi_two_pi
      shevtsovaTheta0_mem_Icc hθ_full hθ.1
  rwa [shevtsovaTheta0_equation] at hmono

lemma shevtsovaCosRemainderRatio_deriv_nonneg_of_mem_Icc_pi_theta0
    {θ : ℝ} (hθ : θ ∈ Set.Icc Real.pi shevtsovaTheta0) :
    0 ≤ deriv shevtsovaCosRemainderRatio θ := by
  have hθ_pos : 0 < θ := Real.pi_pos.trans_le hθ.1
  rw [deriv_shevtsovaCosRemainderRatio_of_ne_zero hθ_pos.ne']
  have hE : shevtsovaThetaEquationValue θ ≤ 0 :=
    shevtsovaThetaEquationValue_nonpos_of_mem_Icc_pi_theta0 hθ
  exact div_nonneg (neg_nonneg.mpr hE) (by positivity)

lemma shevtsovaCosRemainderRatio_deriv_nonneg_of_mem_Ioc_zero_pi
    {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 Real.pi) :
    0 ≤ deriv shevtsovaCosRemainderRatio θ := by
  rw [deriv_shevtsovaCosRemainderRatio_of_ne_zero hθ.1.ne']
  have hE : shevtsovaThetaEquationValue θ ≤ 0 :=
    shevtsovaThetaEquationValue_nonpos_of_mem_Icc_zero_pi
      ⟨hθ.1.le, hθ.2⟩
  exact div_nonneg (neg_nonneg.mpr hE) (by positivity)

lemma continuousOn_shevtsovaCosRemainderRatio_Icc_of_pos_left
    {a b : ℝ} (ha : 0 < a) :
    ContinuousOn shevtsovaCosRemainderRatio (Set.Icc a b) := by
  intro θ hθ
  have hθ_pos : 0 < θ := ha.trans_le hθ.1
  unfold shevtsovaCosRemainderRatio
  exact
    (((Real.continuous_cos.continuousAt.sub continuous_const.continuousAt).add
      (((continuous_id.pow 2).continuousAt).div_const 2)).div
      ((continuous_id.pow 3).continuousAt)
      (pow_ne_zero 3 hθ_pos.ne')).continuousWithinAt

lemma differentiableOn_shevtsovaCosRemainderRatio_interior_Icc_of_pos_left
    {a b : ℝ} (ha : 0 < a) :
    DifferentiableOn ℝ shevtsovaCosRemainderRatio
      (interior (Set.Icc a b)) := by
  intro θ hθ
  have hθ_mem : θ ∈ Set.Icc a b :=
    interior_subset hθ
  have hθ_pos : 0 < θ := ha.trans_le hθ_mem.1
  exact (hasDerivAt_shevtsovaCosRemainderRatio hθ_pos.ne').differentiableAt.differentiableWithinAt

lemma monotoneOn_shevtsovaCosRemainderRatio_Icc_of_pos_left_le_pi
    {a b : ℝ} (ha : 0 < a) (hb : b ≤ Real.pi) :
    MonotoneOn shevtsovaCosRemainderRatio (Set.Icc a b) := by
  exact monotoneOn_of_deriv_nonneg
    (convex_Icc a b)
    (continuousOn_shevtsovaCosRemainderRatio_Icc_of_pos_left ha)
    (differentiableOn_shevtsovaCosRemainderRatio_interior_Icc_of_pos_left ha)
    (fun θ hθ =>
      let hθ_mem : θ ∈ Set.Icc a b := interior_subset hθ
      shevtsovaCosRemainderRatio_deriv_nonneg_of_mem_Ioc_zero_pi
        ⟨ha.trans_le hθ_mem.1, hθ_mem.2.trans hb⟩)

lemma shevtsovaCosRemainderRatio_deriv_nonpos_of_mem_Icc_theta0_two_pi
    {θ : ℝ} (hθ : θ ∈ Set.Icc shevtsovaTheta0 (2 * Real.pi)) :
    deriv shevtsovaCosRemainderRatio θ ≤ 0 := by
  rw [deriv_shevtsovaCosRemainderRatio_of_ne_zero
    (shevtsovaTheta0_pos.trans_le hθ.1).ne']
  have hE : 0 ≤ shevtsovaThetaEquationValue θ :=
    shevtsovaThetaEquationValue_nonneg_of_mem_Icc_theta0_two_pi hθ
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hE) (by positivity)

lemma continuousOn_shevtsovaCosRemainderRatio_Icc_pi_theta0 :
    ContinuousOn shevtsovaCosRemainderRatio
      (Set.Icc Real.pi shevtsovaTheta0) := by
  intro θ hθ
  have hθ_pos : 0 < θ := Real.pi_pos.trans_le hθ.1
  unfold shevtsovaCosRemainderRatio
  exact
    (((Real.continuous_cos.continuousAt.sub continuous_const.continuousAt).add
      (((continuous_id.pow 2).continuousAt).div_const 2)).div
      ((continuous_id.pow 3).continuousAt)
      (pow_ne_zero 3 hθ_pos.ne')).continuousWithinAt

lemma differentiableOn_shevtsovaCosRemainderRatio_interior_Icc_pi_theta0 :
    DifferentiableOn ℝ shevtsovaCosRemainderRatio
      (interior (Set.Icc Real.pi shevtsovaTheta0)) := by
  intro θ hθ
  have hθ_mem : θ ∈ Set.Icc Real.pi shevtsovaTheta0 :=
    interior_subset hθ
  have hθ_pos : 0 < θ := Real.pi_pos.trans_le hθ_mem.1
  exact (hasDerivAt_shevtsovaCosRemainderRatio hθ_pos.ne').differentiableAt.differentiableWithinAt

lemma monotoneOn_shevtsovaCosRemainderRatio_Icc_pi_theta0 :
    MonotoneOn shevtsovaCosRemainderRatio
      (Set.Icc Real.pi shevtsovaTheta0) := by
  exact monotoneOn_of_deriv_nonneg
    (convex_Icc Real.pi shevtsovaTheta0)
    continuousOn_shevtsovaCosRemainderRatio_Icc_pi_theta0
    differentiableOn_shevtsovaCosRemainderRatio_interior_Icc_pi_theta0
    (fun θ hθ =>
      shevtsovaCosRemainderRatio_deriv_nonneg_of_mem_Icc_pi_theta0
        (interior_subset hθ))

lemma continuousOn_shevtsovaCosRemainderRatio_Icc_theta0_two_pi :
    ContinuousOn shevtsovaCosRemainderRatio
      (Set.Icc shevtsovaTheta0 (2 * Real.pi)) := by
  intro θ hθ
  have hθ_pos : 0 < θ := shevtsovaTheta0_pos.trans_le hθ.1
  unfold shevtsovaCosRemainderRatio
  exact
    (((Real.continuous_cos.continuousAt.sub continuous_const.continuousAt).add
      (((continuous_id.pow 2).continuousAt).div_const 2)).div
      ((continuous_id.pow 3).continuousAt)
      (pow_ne_zero 3 hθ_pos.ne')).continuousWithinAt

lemma differentiableOn_shevtsovaCosRemainderRatio_interior_Icc_theta0_two_pi :
    DifferentiableOn ℝ shevtsovaCosRemainderRatio
      (interior (Set.Icc shevtsovaTheta0 (2 * Real.pi))) := by
  intro θ hθ
  have hθ_mem : θ ∈ Set.Icc shevtsovaTheta0 (2 * Real.pi) :=
    interior_subset hθ
  have hθ_pos : 0 < θ := shevtsovaTheta0_pos.trans_le hθ_mem.1
  exact (hasDerivAt_shevtsovaCosRemainderRatio hθ_pos.ne').differentiableAt.differentiableWithinAt

lemma antitoneOn_shevtsovaCosRemainderRatio_Icc_theta0_two_pi :
    AntitoneOn shevtsovaCosRemainderRatio
      (Set.Icc shevtsovaTheta0 (2 * Real.pi)) := by
  exact antitoneOn_of_deriv_nonpos
    (convex_Icc shevtsovaTheta0 (2 * Real.pi))
    continuousOn_shevtsovaCosRemainderRatio_Icc_theta0_two_pi
    differentiableOn_shevtsovaCosRemainderRatio_interior_Icc_theta0_two_pi
    (fun θ hθ =>
      shevtsovaCosRemainderRatio_deriv_nonpos_of_mem_Icc_theta0_two_pi
        (interior_subset hθ))

lemma shevtsovaCosRemainderRatio_le_kappa_of_mem_Icc_pi_two_pi
    {θ : ℝ} (hθ : θ ∈ Set.Icc Real.pi (2 * Real.pi)) :
    shevtsovaCosRemainderRatio θ ≤ shevtsovaKappa := by
  by_cases hle : θ ≤ shevtsovaTheta0
  · have hθ_left : θ ∈ Set.Icc Real.pi shevtsovaTheta0 :=
      ⟨hθ.1, hle⟩
    have hθ0_left : shevtsovaTheta0 ∈ Set.Icc Real.pi shevtsovaTheta0 :=
      ⟨shevtsovaTheta0_mem_Icc.1, le_rfl⟩
    have hmono :=
      monotoneOn_shevtsovaCosRemainderRatio_Icc_pi_theta0
        hθ_left hθ0_left hle
    simpa [shevtsovaCosRemainderRatio_theta0_eq_kappa] using hmono
  · have hθ0_le : shevtsovaTheta0 ≤ θ := le_of_not_ge hle
    have hθ_right : θ ∈ Set.Icc shevtsovaTheta0 (2 * Real.pi) :=
      ⟨hθ0_le, hθ.2⟩
    have hθ0_right :
        shevtsovaTheta0 ∈ Set.Icc shevtsovaTheta0 (2 * Real.pi) :=
      ⟨le_rfl, shevtsovaTheta0_mem_Icc.2⟩
    have hanti :=
      antitoneOn_shevtsovaCosRemainderRatio_Icc_theta0_two_pi
        hθ0_right hθ_right hθ0_le
    simpa [shevtsovaCosRemainderRatio_theta0_eq_kappa] using hanti

lemma shevtsovaCosRemainderRatio_le_kappa_of_mem_Ioc_zero_pi
    {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 Real.pi) :
    shevtsovaCosRemainderRatio θ ≤ shevtsovaKappa := by
  have hmono :=
    monotoneOn_shevtsovaCosRemainderRatio_Icc_of_pos_left_le_pi
      (a := θ) (b := Real.pi) hθ.1 le_rfl
  have hθ_mem : θ ∈ Set.Icc θ Real.pi :=
    ⟨le_rfl, hθ.2⟩
  have hπ_mem : Real.pi ∈ Set.Icc θ Real.pi :=
    ⟨hθ.2, le_rfl⟩
  have hle_pi :
      shevtsovaCosRemainderRatio θ ≤
        shevtsovaCosRemainderRatio Real.pi :=
    hmono hθ_mem hπ_mem hθ.2
  exact hle_pi.trans
    (shevtsovaCosRemainderRatio_le_kappa_of_mem_Icc_pi_two_pi
      ⟨le_rfl, by nlinarith [Real.pi_pos]⟩)

lemma shevtsovaCosRemainderRatio_le_kappa_of_mem_Ioc_zero_two_pi
    {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (2 * Real.pi)) :
    shevtsovaCosRemainderRatio θ ≤ shevtsovaKappa := by
  by_cases hle : θ ≤ Real.pi
  · exact shevtsovaCosRemainderRatio_le_kappa_of_mem_Ioc_zero_pi
      ⟨hθ.1, hle⟩
  · exact shevtsovaCosRemainderRatio_le_kappa_of_mem_Icc_pi_two_pi
      ⟨le_of_not_ge hle, hθ.2⟩

lemma real_cos_remainder_le_shevtsovaKappa_mul_abs_cube_of_abs_le_two_pi
    {x : ℝ} (hx : |x| ≤ 2 * Real.pi) :
    Real.cos x - 1 + x ^ 2 / 2 ≤ shevtsovaKappa * |x| ^ 3 := by
  by_cases hx0 : x = 0
  · subst x
    norm_num
  · have habs_pos : 0 < |x| := abs_pos.mpr hx0
    have hratio :
        shevtsovaCosRemainderRatio |x| ≤ shevtsovaKappa :=
      shevtsovaCosRemainderRatio_le_kappa_of_mem_Ioc_zero_two_pi
        ⟨habs_pos, hx⟩
    unfold shevtsovaCosRemainderRatio at hratio
    have hden_pos : 0 < |x| ^ 3 := pow_pos habs_pos 3
    have hnum_le :
        Real.cos |x| - 1 + |x| ^ 2 / 2 ≤
          shevtsovaKappa * |x| ^ 3 :=
      (div_le_iff₀ hden_pos).mp hratio
    simpa [Real.cos_abs, sq_abs] using hnum_le

lemma one_div_four_pi_le_shevtsovaKappa :
    1 / (4 * Real.pi) ≤ shevtsovaKappa := by
  have hratio :
      shevtsovaCosRemainderRatio (2 * Real.pi) =
        1 / (4 * Real.pi) := by
    unfold shevtsovaCosRemainderRatio
    rw [Real.cos_two_pi]
    field_simp [Real.pi_ne_zero]
    ring
  have hle :=
    shevtsovaCosRemainderRatio_le_kappa_of_mem_Icc_pi_two_pi
      (θ := 2 * Real.pi) ⟨by nlinarith [Real.pi_pos], le_rfl⟩
  rwa [hratio] at hle

lemma one_half_le_shevtsovaKappa_mul_two_pi :
    1 / 2 ≤ shevtsovaKappa * (2 * Real.pi) := by
  calc
    (1 / 2 : ℝ) = (1 / (4 * Real.pi)) * (2 * Real.pi) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ shevtsovaKappa * (2 * Real.pi) := by
      exact mul_le_mul_of_nonneg_right
        one_div_four_pi_le_shevtsovaKappa (by positivity)

lemma real_cos_remainder_le_shevtsovaKappa_mul_abs_cube (x : ℝ) :
    Real.cos x - 1 + x ^ 2 / 2 ≤ shevtsovaKappa * |x| ^ 3 := by
  by_cases hx : |x| ≤ 2 * Real.pi
  · exact real_cos_remainder_le_shevtsovaKappa_mul_abs_cube_of_abs_le_two_pi hx
  · have hlarge : 2 * Real.pi ≤ |x| := le_of_not_ge hx
    have hhalf : (1 / 2 : ℝ) ≤ shevtsovaKappa * |x| := by
      exact one_half_le_shevtsovaKappa_mul_two_pi.trans
        (mul_le_mul_of_nonneg_left hlarge shevtsovaKappa_pos.le)
    have hquad : x ^ 2 / 2 ≤ shevtsovaKappa * |x| ^ 3 := by
      calc
        x ^ 2 / 2 = |x| ^ 2 * (1 / 2) := by
          rw [sq_abs]
          ring
        _ ≤ |x| ^ 2 * (shevtsovaKappa * |x|) :=
          mul_le_mul_of_nonneg_left hhalf (sq_nonneg |x|)
        _ = shevtsovaKappa * |x| ^ 3 := by ring
    have hcos : Real.cos x - 1 ≤ 0 := by
      nlinarith [Real.cos_le_one x]
    nlinarith

lemma real_cos_le_one_sub_sq_div_two_add_shevtsovaKappa_abs_cube (x : ℝ) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + shevtsovaKappa * |x| ^ 3 := by
  have h := real_cos_remainder_le_shevtsovaKappa_mul_abs_cube x
  linarith

/-- The middle-branch ratio in Shevtsova's auxiliary function:
`(1 - cos u) / u²`. -/
def shevtsovaCosRatio (u : ℝ) : ℝ :=
  (1 - Real.cos u) / u ^ 2

lemma hasDerivAt_shevtsovaCosRatio {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt shevtsovaCosRatio
      ((u * Real.sin u - 2 * (1 - Real.cos u)) / u ^ 3) u := by
  have hnum :
      HasDerivAt (fun y : ℝ => 1 - Real.cos y) (Real.sin u) u := by
    simpa using
      ((hasDerivAt_const (x := u) (c := (1 : ℝ))).sub
        (Real.hasDerivAt_cos u))
  have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow (n := 2) (x := u))
  have hden_ne : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hquot :=
    (hnum.div hden hden_ne)
  unfold shevtsovaCosRatio
  convert hquot using 1
  field_simp [hu]

lemma deriv_shevtsovaCosRatio_of_ne_zero {u : ℝ} (hu : u ≠ 0) :
    deriv shevtsovaCosRatio u =
      (u * Real.sin u - 2 * (1 - Real.cos u)) / u ^ 3 :=
  (hasDerivAt_shevtsovaCosRatio hu).deriv

lemma shevtsovaCosRatio_deriv_nonpos_of_mem_Icc_pi_two_pi {u : ℝ}
    (hu : u ∈ Set.Icc Real.pi (2 * Real.pi)) :
    deriv shevtsovaCosRatio u ≤ 0 := by
  have hu_pos : 0 < u := Real.pi_pos.trans_le hu.1
  rw [deriv_shevtsovaCosRatio_of_ne_zero hu_pos.ne']
  have hsin : Real.sin u ≤ 0 :=
    sin_nonpos_of_mem_Icc_pi_two_pi hu
  have hmul_sin : u * Real.sin u ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hu_pos.le hsin
  have hcos_nonneg : 0 ≤ 1 - Real.cos u :=
    one_sub_cos_nonneg u
  have hnum_nonpos :
      u * Real.sin u - 2 * (1 - Real.cos u) ≤ 0 := by
    nlinarith
  exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos
    (pow_nonneg hu_pos.le 3)

lemma continuousOn_shevtsovaCosRatio_Icc_pi_two_pi :
    ContinuousOn shevtsovaCosRatio (Set.Icc Real.pi (2 * Real.pi)) := by
  intro u hu
  have hu_pos : 0 < u := Real.pi_pos.trans_le hu.1
  unfold shevtsovaCosRatio
  exact
    ((continuous_const.sub Real.continuous_cos).continuousAt.div
      ((continuous_id.pow 2).continuousAt)
      (pow_ne_zero 2 hu_pos.ne')).continuousWithinAt

lemma differentiableOn_shevtsovaCosRatio_interior_Icc_pi_two_pi :
    DifferentiableOn ℝ shevtsovaCosRatio
      (interior (Set.Icc Real.pi (2 * Real.pi))) := by
  intro u hu
  have hu_mem : u ∈ Set.Icc Real.pi (2 * Real.pi) :=
    interior_subset hu
  have hu_pos : 0 < u := Real.pi_pos.trans_le hu_mem.1
  exact (hasDerivAt_shevtsovaCosRatio hu_pos.ne').differentiableAt.differentiableWithinAt

lemma antitoneOn_shevtsovaCosRatio_Icc_pi_two_pi :
    AntitoneOn shevtsovaCosRatio (Set.Icc Real.pi (2 * Real.pi)) := by
  exact antitoneOn_of_deriv_nonpos
    (convex_Icc Real.pi (2 * Real.pi))
    continuousOn_shevtsovaCosRatio_Icc_pi_two_pi
    differentiableOn_shevtsovaCosRatio_interior_Icc_pi_two_pi
    (fun u hu =>
      shevtsovaCosRatio_deriv_nonpos_of_mem_Icc_pi_two_pi
        (interior_subset hu))

/-! #### Prawitz kernel and auxiliary `ψ` function -/

/-- Real sign function used in Prawitz's smoothing kernel. -/
def shevtsovaRealSign (x : ℝ) : ℝ :=
  if x < 0 then -1 else if x = 0 then 0 else 1

lemma shevtsovaRealSign_of_neg {x : ℝ} (hx : x < 0) :
    shevtsovaRealSign x = -1 := by
  simp [shevtsovaRealSign, hx]

lemma shevtsovaRealSign_zero :
    shevtsovaRealSign 0 = 0 := by
  simp [shevtsovaRealSign]

lemma shevtsovaRealSign_of_pos {x : ℝ} (hx : 0 < x) :
    shevtsovaRealSign x = 1 := by
  simp [shevtsovaRealSign, not_lt.mpr hx.le, hx.ne']

lemma abs_shevtsovaRealSign_le_one (x : ℝ) :
    |shevtsovaRealSign x| ≤ 1 := by
  by_cases hneg : x < 0
  · simp [shevtsovaRealSign, hneg]
  · by_cases hzero : x = 0
    · simp [shevtsovaRealSign, hzero]
    · simp [shevtsovaRealSign, hneg, hzero]

/-- Cotangent written as `cos / sin`, matching Prawitz's kernel formula while
avoiding a dependency on any specialized cotangent API. -/
def shevtsovaRealCot (x : ℝ) : ℝ :=
  Real.cos x / Real.sin x

/-- Prawitz's smoothing kernel.  The formula is extended outside `[-1, 1]`;
the later integral statements restrict the relevant range and ignore the
removable singularities. -/
def shevtsovaPrawitzKernel (t : ℝ) : ℂ :=
  (((1 - |t|) / 2 : ℝ) : ℂ) +
    ((((1 - |t|) * shevtsovaRealCot (Real.pi * t) +
        shevtsovaRealSign t / Real.pi) / 2 : ℝ) : ℂ) * Complex.I

lemma shevtsovaPrawitzKernel_re (t : ℝ) :
    (shevtsovaPrawitzKernel t).re = (1 - |t|) / 2 := by
  simp [shevtsovaPrawitzKernel]

lemma shevtsovaPrawitzKernel_im (t : ℝ) :
    (shevtsovaPrawitzKernel t).im =
      ((1 - |t|) * shevtsovaRealCot (Real.pi * t) +
        shevtsovaRealSign t / Real.pi) / 2 := by
  simp [shevtsovaPrawitzKernel]

/-- Multiplication by `i`, used for terms such as `i / (2πt)`. -/
def shevtsovaIMul (x : ℝ) : ℂ :=
  (x : ℂ) * Complex.I

lemma shevtsovaIMul_re (x : ℝ) :
    (shevtsovaIMul x).re = 0 := by
  simp [shevtsovaIMul]

lemma shevtsovaIMul_im (x : ℝ) :
    (shevtsovaIMul x).im = x := by
  simp [shevtsovaIMul]

lemma norm_shevtsovaIMul (x : ℝ) :
    ‖shevtsovaIMul x‖ = |x| := by
  simp [shevtsovaIMul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs]

lemma shevtsovaPrawitzKernel_sub_IMul_re (t x : ℝ) :
    (shevtsovaPrawitzKernel t - shevtsovaIMul x).re =
      (1 - |t|) / 2 := by
  simp [Complex.sub_re, shevtsovaPrawitzKernel_re, shevtsovaIMul_re]

lemma shevtsovaPrawitzKernel_sub_IMul_im (t x : ℝ) :
    (shevtsovaPrawitzKernel t - shevtsovaIMul x).im =
      ((1 - |t|) * shevtsovaRealCot (Real.pi * t) +
        shevtsovaRealSign t / Real.pi) / 2 - x := by
  simp [Complex.sub_im, shevtsovaPrawitzKernel_im, shevtsovaIMul_im]

lemma shevtsovaPrawitzKernel_zero :
    shevtsovaPrawitzKernel 0 = (1 / 2 : ℂ) := by
  apply Complex.ext <;> simp [shevtsovaPrawitzKernel_re, shevtsovaPrawitzKernel_im,
    shevtsovaRealSign_zero, shevtsovaRealCot]

lemma complex_norm_sq_eq_re_sq_add_im_sq (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

lemma shevtsovaPrawitzKernel_norm_sq (t : ℝ) :
    ‖shevtsovaPrawitzKernel t‖ ^ 2 =
      ((1 - |t|) / 2) ^ 2 +
        (((1 - |t|) * shevtsovaRealCot (Real.pi * t) +
          shevtsovaRealSign t / Real.pi) / 2) ^ 2 := by
  rw [complex_norm_sq_eq_re_sq_add_im_sq,
    shevtsovaPrawitzKernel_re, shevtsovaPrawitzKernel_im]

lemma shevtsovaPrawitzKernel_sub_IMul_norm_sq (t x : ℝ) :
    ‖shevtsovaPrawitzKernel t - shevtsovaIMul x‖ ^ 2 =
      ((1 - |t|) / 2) ^ 2 +
        (((1 - |t|) * shevtsovaRealCot (Real.pi * t) +
          shevtsovaRealSign t / Real.pi) / 2 - x) ^ 2 := by
  rw [complex_norm_sq_eq_re_sq_add_im_sq,
    shevtsovaPrawitzKernel_sub_IMul_re,
    shevtsovaPrawitzKernel_sub_IMul_im]

lemma shevtsovaPrawitzKernel_re_nonneg_of_mem_Icc_zero_one
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (shevtsovaPrawitzKernel t).re := by
  rw [shevtsovaPrawitzKernel_re, abs_of_nonneg ht.1]
  nlinarith [ht.2]

lemma shevtsovaPrawitzKernel_re_le_half_of_mem_Icc_zero_one
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (shevtsovaPrawitzKernel t).re ≤ 1 / 2 := by
  rw [shevtsovaPrawitzKernel_re, abs_of_nonneg ht.1]
  nlinarith [ht.1]

lemma shevtsovaPrawitzKernel_abs_mul_norm_le_one_of_mem_Icc_zero_half
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :
    |t| * ‖shevtsovaPrawitzKernel t‖ ≤ 1 := by
  by_cases ht0 : t = 0
  · subst t
    simp [shevtsovaPrawitzKernel_zero]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have ht_abs : |t| = t := abs_of_nonneg ht.1
    have harg_nonneg : 0 ≤ Real.pi * t := by positivity
    have harg_le : Real.pi * t ≤ Real.pi / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le]
    have hsin_lower :
        2 * t ≤ Real.sin (Real.pi * t) := by
      have h := Real.mul_le_sin (x := Real.pi * t) harg_nonneg harg_le
      convert h using 1
      field_simp [Real.pi_ne_zero]
    have hsin_pos : 0 < Real.sin (Real.pi * t) := by
      exact (by positivity : 0 < 2 * t).trans_le hsin_lower
    have hcos_nonneg : 0 ≤ Real.cos (Real.pi * t) := by
      exact Real.cos_nonneg_of_mem_Icc
        ⟨by nlinarith [harg_nonneg, Real.pi_pos], harg_le⟩
    have hcot_nonneg : 0 ≤ shevtsovaRealCot (Real.pi * t) := by
      unfold shevtsovaRealCot
      exact div_nonneg hcos_nonneg hsin_pos.le
    have hcot_le :
        shevtsovaRealCot (Real.pi * t) ≤
          1 / Real.sin (Real.pi * t) := by
      unfold shevtsovaRealCot
      exact div_le_div_of_nonneg_right (Real.cos_le_one (Real.pi * t)) hsin_pos.le
    have ht_div_sin_le :
        t / Real.sin (Real.pi * t) ≤ 1 / 2 := by
      rw [div_le_iff₀ hsin_pos]
      nlinarith [hsin_lower]
    have ht_cot_le :
        t * shevtsovaRealCot (Real.pi * t) ≤ 1 / 2 := by
      calc
        t * shevtsovaRealCot (Real.pi * t) ≤
            t * (1 / Real.sin (Real.pi * t)) :=
          mul_le_mul_of_nonneg_left hcot_le ht.1
        _ = t / Real.sin (Real.pi * t) := by ring
        _ ≤ 1 / 2 := ht_div_sin_le
    have hone_sub_nonneg : 0 ≤ 1 - t := by nlinarith [ht.2]
    have hone_sub_le_one : 1 - t ≤ 1 := by nlinarith [ht.1]
    have hscaled_cot_le :
        (1 - t) * shevtsovaRealCot (Real.pi * t) ≤
          shevtsovaRealCot (Real.pi * t) := by
      simpa [one_mul] using
        mul_le_mul_of_nonneg_right hone_sub_le_one hcot_nonneg
    have ht_scaled_cot_le :
        t * ((1 - t) * shevtsovaRealCot (Real.pi * t)) ≤ 1 / 2 := by
      calc
        t * ((1 - t) * shevtsovaRealCot (Real.pi * t)) ≤
            t * shevtsovaRealCot (Real.pi * t) :=
          mul_le_mul_of_nonneg_left hscaled_cot_le ht.1
        _ ≤ 1 / 2 := ht_cot_le
    have ht_div_pi_le : t / Real.pi ≤ 1 / 6 := by
      calc
        t / Real.pi = t * (1 / Real.pi) := by ring
        _ ≤ (1 / 2 : ℝ) * (1 / 3 : ℝ) :=
          mul_le_mul ht.2 one_div_pi_le_one_div_three
            (by positivity) (by norm_num)
        _ = 1 / 6 := by norm_num
    have hre_abs :
        |(shevtsovaPrawitzKernel t).re| = (1 - t) / 2 := by
      rw [shevtsovaPrawitzKernel_re, ht_abs,
        abs_of_nonneg (by nlinarith [ht.2] : 0 ≤ (1 - t) / 2)]
    have ht_re_le :
        t * |(shevtsovaPrawitzKernel t).re| ≤ 1 / 2 := by
      rw [hre_abs]
      nlinarith [ht.1, ht.2]
    have him_nonneg :
        0 ≤ (((1 - t) * shevtsovaRealCot (Real.pi * t) +
          shevtsovaRealSign t / Real.pi) / 2 : ℝ) := by
      have hsign : shevtsovaRealSign t = 1 :=
        shevtsovaRealSign_of_pos ht_pos
      rw [hsign]
      exact div_nonneg
        (add_nonneg (mul_nonneg hone_sub_nonneg hcot_nonneg)
          (div_nonneg zero_le_one Real.pi_pos.le))
        (by norm_num)
    have him_abs :
        |(shevtsovaPrawitzKernel t).im| =
          (((1 - t) * shevtsovaRealCot (Real.pi * t) +
            1 / Real.pi) / 2 : ℝ) := by
      have hsign : shevtsovaRealSign t = 1 :=
        shevtsovaRealSign_of_pos ht_pos
      rw [shevtsovaPrawitzKernel_im, hsign, ht_abs,
        abs_of_nonneg (by simpa [hsign] using him_nonneg)]
    have ht_im_le :
        t * |(shevtsovaPrawitzKernel t).im| ≤ 1 / 2 := by
      rw [him_abs]
      calc
        t * (((1 - t) * shevtsovaRealCot (Real.pi * t) +
            1 / Real.pi) / 2) =
            (t * ((1 - t) * shevtsovaRealCot (Real.pi * t)) +
              t / Real.pi) / 2 := by
          ring
        _ ≤ ((1 / 2 : ℝ) + 1 / 6) / 2 := by
          exact div_le_div_of_nonneg_right
            (add_le_add ht_scaled_cot_le ht_div_pi_le) (by norm_num)
        _ ≤ 1 / 2 := by norm_num
    calc
      |t| * ‖shevtsovaPrawitzKernel t‖ =
          t * ‖shevtsovaPrawitzKernel t‖ := by rw [ht_abs]
      _ ≤ t * (|(shevtsovaPrawitzKernel t).re| +
          |(shevtsovaPrawitzKernel t).im|) :=
        mul_le_mul_of_nonneg_left
          (Complex.norm_le_abs_re_add_abs_im (shevtsovaPrawitzKernel t)) ht.1
      _ = t * |(shevtsovaPrawitzKernel t).re| +
          t * |(shevtsovaPrawitzKernel t).im| := by ring
      _ ≤ 1 / 2 + 1 / 2 := add_le_add ht_re_le ht_im_le
      _ = 1 := by norm_num

lemma abs_one_sub_mul_shevtsovaRealCot_le_pi_mul_sq_div_three
    {x : ℝ} (hx0 : 0 < x) (hxle : x ≤ Real.pi / 2) :
    |1 - x * shevtsovaRealCot x| ≤ Real.pi * x ^ 2 / 3 := by
  have hx_nonneg : 0 ≤ x := hx0.le
  have hx_lt_pi : x < Real.pi := by
    nlinarith [hxle, Real.pi_pos]
  have hsin_pos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0 hx_lt_pi
  have hsin_lower : (2 / Real.pi) * x ≤ Real.sin x :=
    Real.mul_le_sin hx_nonneg hxle
  have hsin_abs : |Real.sin x| = Real.sin x := abs_of_pos hsin_pos
  have hsin_sub : |Real.sin x - x| ≤ x ^ 3 / 6 := by
    simpa [abs_of_nonneg hx_nonneg] using
      abs_sin_sub_id_le_abs_cube_div_six x
  have hcos_nonneg : 0 ≤ 1 - Real.cos x := one_sub_cos_nonneg x
  have hmul_cos_abs :
      |x * (1 - Real.cos x)| = x * (1 - Real.cos x) := by
    exact abs_of_nonneg (mul_nonneg hx_nonneg hcos_nonneg)
  have hmul_cos_le :
      x * (1 - Real.cos x) ≤ x * (x ^ 2 / 2) := by
    exact mul_le_mul_of_nonneg_left (one_sub_cos_le_sq_div_two x) hx_nonneg
  have hnum :
      |Real.sin x - x * Real.cos x| ≤ (2 / 3) * x ^ 3 := by
    calc
      |Real.sin x - x * Real.cos x| =
          |(Real.sin x - x) + x * (1 - Real.cos x)| := by
            congr 1
            ring
      _ ≤ |Real.sin x - x| + |x * (1 - Real.cos x)| :=
        abs_add_le _ _
      _ ≤ x ^ 3 / 6 + x * (x ^ 2 / 2) := by
        exact add_le_add hsin_sub (by simpa [hmul_cos_abs] using hmul_cos_le)
      _ = (2 / 3) * x ^ 3 := by ring
  have hid :
      1 - x * shevtsovaRealCot x =
        (Real.sin x - x * Real.cos x) / Real.sin x := by
    unfold shevtsovaRealCot
    field_simp [hsin_pos.ne']
  rw [hid, abs_div, hsin_abs]
  have hnum_nonneg : 0 ≤ (2 / 3) * x ^ 3 := by positivity
  calc
    |Real.sin x - x * Real.cos x| / Real.sin x ≤
        ((2 / 3) * x ^ 3) / Real.sin x :=
      div_le_div_of_nonneg_right hnum hsin_pos.le
    _ ≤ ((2 / 3) * x ^ 3) / ((2 / Real.pi) * x) := by
      exact div_le_div_of_nonneg_left hnum_nonneg
        (by positivity : 0 < (2 / Real.pi) * x) hsin_lower
    _ = Real.pi * x ^ 2 / 3 := by
      field_simp [Real.pi_ne_zero, hx0.ne']

lemma shevtsovaPrawitzKernel_sub_IMul_im_abs_le_one_of_mem_Ioc_zero_half
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ)) :
    |(shevtsovaPrawitzKernel t -
        shevtsovaIMul ((2 * Real.pi * t)⁻¹)).im| ≤ 1 := by
  have ht_pos : 0 < t := ht.1
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have ht_le : t ≤ (1 / 2 : ℝ) := ht.2
  have hone_sub_nonneg : 0 ≤ 1 - t := by nlinarith [ht_le]
  have harg_pos : 0 < Real.pi * t := by positivity
  have harg_le : Real.pi * t ≤ Real.pi / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left ht_le Real.pi_pos.le]
  have hcot :
      |1 - (Real.pi * t) * shevtsovaRealCot (Real.pi * t)| ≤
        Real.pi * (Real.pi * t) ^ 2 / 3 :=
    abs_one_sub_mul_shevtsovaRealCot_le_pi_mul_sq_div_three
      (x := Real.pi * t) harg_pos harg_le
  have him_eq :
      (shevtsovaPrawitzKernel t -
          shevtsovaIMul ((2 * Real.pi * t)⁻¹)).im =
        - ((1 - t) / (2 * Real.pi * t)) *
          (1 - (Real.pi * t) * shevtsovaRealCot (Real.pi * t)) := by
    rw [shevtsovaPrawitzKernel_sub_IMul_im]
    have hsign : shevtsovaRealSign t = 1 :=
      shevtsovaRealSign_of_pos ht_pos
    have ht_abs : |t| = t := abs_of_pos ht_pos
    rw [hsign, ht_abs]
    field_simp [Real.pi_ne_zero, ht_pos.ne']
    ring
  rw [him_eq, abs_mul, abs_neg]
  have hfactor_nonneg : 0 ≤ (1 - t) / (2 * Real.pi * t) := by
    exact div_nonneg hone_sub_nonneg (by positivity : 0 ≤ 2 * Real.pi * t)
  have hfactor_abs :
      |(1 - t) / (2 * Real.pi * t)| =
        (1 - t) / (2 * Real.pi * t) :=
    abs_of_nonneg hfactor_nonneg
  rw [hfactor_abs]
  calc
    (1 - t) / (2 * Real.pi * t) *
        |1 - Real.pi * t * shevtsovaRealCot (Real.pi * t)| ≤
      (1 - t) / (2 * Real.pi * t) *
        (Real.pi * (Real.pi * t) ^ 2 / 3) :=
      mul_le_mul_of_nonneg_left hcot hfactor_nonneg
    _ = (1 - t) * Real.pi ^ 2 * t / 6 := by
      field_simp [Real.pi_ne_zero, ht_pos.ne']
      ring
    _ ≤ 1 := by
      have hprod_nonneg : 0 ≤ (1 - t) * t :=
        mul_nonneg hone_sub_nonneg ht_nonneg
      have hprod_le : (1 - t) * t ≤ 1 / 2 := by
        nlinarith [ht_nonneg, ht_le]
      have hpi_sq_le : Real.pi ^ 2 ≤ 12 := by
        nlinarith [Real.pi_pos, Real.pi_lt_d2]
      have hmul :
          Real.pi ^ 2 * ((1 - t) * t) ≤ 12 * (1 / 2 : ℝ) := by
        exact mul_le_mul hpi_sq_le hprod_le hprod_nonneg (by norm_num)
      nlinarith

lemma shevtsovaPrawitzKernel_sub_IMul_norm_le_three_halves_of_mem_Ioc_zero_half
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ)) :
    ‖shevtsovaPrawitzKernel t -
        shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ ≤ 3 / 2 := by
  have ht_pos : 0 < t := ht.1
  have ht_le : t ≤ (1 / 2 : ℝ) := ht.2
  have ht_abs : |t| = t := abs_of_pos ht_pos
  have hre_nonneg : 0 ≤ ((1 - t) / 2 : ℝ) := by
    nlinarith [ht_le]
  have hre_abs :
      |(shevtsovaPrawitzKernel t -
        shevtsovaIMul ((2 * Real.pi * t)⁻¹)).re| = (1 - t) / 2 := by
    rw [shevtsovaPrawitzKernel_sub_IMul_re, ht_abs,
      abs_of_nonneg hre_nonneg]
  have hre_le :
      |(shevtsovaPrawitzKernel t -
        shevtsovaIMul ((2 * Real.pi * t)⁻¹)).re| ≤ (1 / 2 : ℝ) := by
    rw [hre_abs]
    nlinarith [ht_pos.le]
  have him_le :
      |(shevtsovaPrawitzKernel t -
        shevtsovaIMul ((2 * Real.pi * t)⁻¹)).im| ≤ 1 :=
    shevtsovaPrawitzKernel_sub_IMul_im_abs_le_one_of_mem_Ioc_zero_half ht
  calc
    ‖shevtsovaPrawitzKernel t -
        shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ ≤
        |(shevtsovaPrawitzKernel t -
          shevtsovaIMul ((2 * Real.pi * t)⁻¹)).re| +
        |(shevtsovaPrawitzKernel t -
          shevtsovaIMul ((2 * Real.pi * t)⁻¹)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (1 / 2 : ℝ) + 1 := add_le_add hre_le him_le
    _ = 3 / 2 := by norm_num

lemma shevtsovaPrawitzKernel_sub_IMul_norm_le_three_halves_of_mem_Icc_zero_half
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :
    ‖shevtsovaPrawitzKernel t -
        shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ ≤ 3 / 2 := by
  by_cases ht0 : t = 0
  · subst t
    rw [shevtsovaPrawitzKernel_zero]
    norm_num [shevtsovaIMul]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    exact
      shevtsovaPrawitzKernel_sub_IMul_norm_le_three_halves_of_mem_Ioc_zero_half
        (t := t) ⟨ht_pos, ht.2⟩

lemma shevtsovaPrawitzKernel_one :
    shevtsovaPrawitzKernel 1 = shevtsovaIMul ((2 * Real.pi)⁻¹) := by
  apply Complex.ext
  · simp [shevtsovaPrawitzKernel_re, shevtsovaIMul_re]
  · rw [shevtsovaPrawitzKernel_im, shevtsovaIMul_im]
    have hsign : shevtsovaRealSign (1 : ℝ) = 1 :=
      shevtsovaRealSign_of_pos zero_lt_one
    rw [hsign]
    simp [shevtsovaRealCot]
    field_simp [Real.pi_ne_zero]

lemma shevtsovaPrawitzKernel_sub_IMul_one :
    shevtsovaPrawitzKernel 1 - shevtsovaIMul ((2 * Real.pi)⁻¹) = 0 := by
  rw [shevtsovaPrawitzKernel_one]
  simp

lemma one_sub_mul_abs_shevtsovaRealCot_le_half_of_mem_Ioo_half_one
    {t : ℝ} (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    (1 - t) * |shevtsovaRealCot (Real.pi * t)| ≤ 1 / 2 := by
  let s : ℝ := 1 - t
  have ht_lt : t < (1 : ℝ) := ht.2
  have ht_gt_half : (1 / 2 : ℝ) < t := ht.1
  have hs_pos : 0 < s := by
    dsimp [s]
    nlinarith [ht_lt]
  have hs_nonneg : 0 ≤ s := hs_pos.le
  have hs_le : s ≤ (1 / 2 : ℝ) := by
    dsimp [s]
    nlinarith [ht_gt_half]
  have harg_nonneg : 0 ≤ Real.pi * s := by positivity
  have harg_le : Real.pi * s ≤ Real.pi / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs_le Real.pi_pos.le]
  have hsin_lower : 2 * s ≤ Real.sin (Real.pi * s) := by
    have h := Real.mul_le_sin (x := Real.pi * s) harg_nonneg harg_le
    convert h using 1
    field_simp [Real.pi_ne_zero]
  have hsin_pos : 0 < Real.sin (Real.pi * s) := by
    exact (by positivity : 0 < 2 * s).trans_le hsin_lower
  have hsin_t : Real.sin (Real.pi * t) = Real.sin (Real.pi * s) := by
    have harg : Real.pi * t = Real.pi - Real.pi * s := by
      dsimp [s]
      ring
    rw [harg, Real.sin_pi_sub]
  have hcos_t : Real.cos (Real.pi * t) = -Real.cos (Real.pi * s) := by
    have harg : Real.pi * t = Real.pi - Real.pi * s := by
      dsimp [s]
      ring
    rw [harg, Real.cos_pi_sub]
  have hcot_abs_le :
      |shevtsovaRealCot (Real.pi * t)| ≤
        1 / Real.sin (Real.pi * s) := by
    unfold shevtsovaRealCot
    rw [hcos_t, hsin_t, abs_div, abs_neg, abs_of_pos hsin_pos]
    exact div_le_div_of_nonneg_right
      (Real.abs_cos_le_one (Real.pi * s)) hsin_pos.le
  have hs_div_sin_le : s / Real.sin (Real.pi * s) ≤ 1 / 2 := by
    rw [div_le_iff₀ hsin_pos]
    nlinarith [hsin_lower]
  calc
    (1 - t) * |shevtsovaRealCot (Real.pi * t)| =
        s * |shevtsovaRealCot (Real.pi * t)| := by rfl
    _ ≤ s * (1 / Real.sin (Real.pi * s)) :=
      mul_le_mul_of_nonneg_left hcot_abs_le hs_nonneg
    _ = s / Real.sin (Real.pi * s) := by ring
    _ ≤ 1 / 2 := hs_div_sin_le

lemma shevtsovaPrawitzKernel_norm_le_one_of_mem_Ioo_half_one
    {t : ℝ} (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ‖shevtsovaPrawitzKernel t‖ ≤ 1 := by
  have ht_pos : 0 < t := by nlinarith [ht.1]
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have ht_le_one : t ≤ (1 : ℝ) := ht.2.le
  have ht_abs : |t| = t := abs_of_pos ht_pos
  have hone_sub_nonneg : 0 ≤ 1 - t := by nlinarith [ht.2]
  have hre_abs :
      |(shevtsovaPrawitzKernel t).re| = (1 - t) / 2 := by
    rw [shevtsovaPrawitzKernel_re, ht_abs,
      abs_of_nonneg (by nlinarith [ht_le_one] : 0 ≤ (1 - t) / 2)]
  have hre_le :
      |(shevtsovaPrawitzKernel t).re| ≤ (1 / 2 : ℝ) := by
    rw [hre_abs]
    nlinarith [ht_nonneg]
  have hscaled_abs :
      |(1 - t) * shevtsovaRealCot (Real.pi * t)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hone_sub_nonneg]
    exact one_sub_mul_abs_shevtsovaRealCot_le_half_of_mem_Ioo_half_one ht
  have hpi_abs : |(1 / Real.pi : ℝ)| = 1 / Real.pi :=
    abs_of_pos (by positivity : 0 < (1 / Real.pi : ℝ))
  have hnum_abs :
      |(1 - t) * shevtsovaRealCot (Real.pi * t) +
        1 / Real.pi| ≤ 1 := by
    calc
      |(1 - t) * shevtsovaRealCot (Real.pi * t) + 1 / Real.pi| ≤
          |(1 - t) * shevtsovaRealCot (Real.pi * t)| +
            |(1 / Real.pi : ℝ)| :=
        abs_add_le _ _
      _ ≤ 1 / 2 + 1 / Real.pi := by
        exact add_le_add hscaled_abs (by rw [hpi_abs])
      _ ≤ 1 := by
        nlinarith [one_div_pi_le_one_div_three]
  have him_abs : |(shevtsovaPrawitzKernel t).im| ≤ (1 / 2 : ℝ) := by
    rw [shevtsovaPrawitzKernel_im]
    have hsign : shevtsovaRealSign t = 1 :=
      shevtsovaRealSign_of_pos ht_pos
    rw [hsign, ht_abs]
    calc
      |(((1 - t) * shevtsovaRealCot (Real.pi * t) +
          1 / Real.pi) / 2 : ℝ)| =
          |(1 - t) * shevtsovaRealCot (Real.pi * t) +
            1 / Real.pi| / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 1 / 2 := div_le_div_of_nonneg_right hnum_abs (by norm_num)
  calc
    ‖shevtsovaPrawitzKernel t‖ ≤
        |(shevtsovaPrawitzKernel t).re| +
          |(shevtsovaPrawitzKernel t).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (1 / 2 : ℝ) + 1 / 2 := add_le_add hre_le him_abs
    _ = 1 := by norm_num

lemma shevtsovaPrawitzKernel_norm_le_one_of_mem_Icc_half_one
    {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ‖shevtsovaPrawitzKernel t‖ ≤ 1 := by
  by_cases hhalf : t = 1 / 2
  · subst t
    have hsign : shevtsovaRealSign (1 / 2 : ℝ) = 1 :=
      shevtsovaRealSign_of_pos (by norm_num)
    have harg : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by ring
    have hre_abs :
        |(shevtsovaPrawitzKernel (1 / 2 : ℝ)).re| = (1 / 4 : ℝ) := by
      rw [shevtsovaPrawitzKernel_re]
      norm_num
    have hpi_inv_le_one : Real.pi⁻¹ ≤ (1 : ℝ) := by
      rw [inv_eq_one_div, div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    have him_abs :
        |(shevtsovaPrawitzKernel (1 / 2 : ℝ)).im| ≤ (1 / 2 : ℝ) := by
      rw [shevtsovaPrawitzKernel_im, hsign]
      norm_num [shevtsovaRealCot, harg, Real.sin_pi_div_two,
        Real.cos_pi_div_two]
      have hpos : 0 ≤ (Real.pi⁻¹ / 2 : ℝ) := by positivity
      rw [abs_of_nonneg hpos]
      nlinarith
    calc
      ‖shevtsovaPrawitzKernel (1 / 2 : ℝ)‖ ≤
          |(shevtsovaPrawitzKernel (1 / 2 : ℝ)).re| +
            |(shevtsovaPrawitzKernel (1 / 2 : ℝ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ (1 / 4 : ℝ) + 1 / 2 := add_le_add (by rw [hre_abs]) him_abs
      _ ≤ 1 := by norm_num
  · by_cases hone : t = 1
    · subst t
      rw [shevtsovaPrawitzKernel_one, norm_shevtsovaIMul]
      have hpos : 0 < (2 * Real.pi : ℝ) := by positivity
      rw [abs_of_pos (inv_pos.mpr hpos), inv_eq_one_div]
      rw [div_le_iff₀ hpos]
      nlinarith [Real.pi_gt_three]
    · have ht_gt : (1 / 2 : ℝ) < t :=
        lt_of_le_of_ne ht.1 (Ne.symm hhalf)
      have ht_lt : t < (1 : ℝ) :=
        lt_of_le_of_ne ht.2 hone
      exact
        shevtsovaPrawitzKernel_norm_le_one_of_mem_Ioo_half_one
          (t := t) ⟨ht_gt, ht_lt⟩

lemma measurable_shevtsovaRealSign :
    Measurable shevtsovaRealSign := by
  unfold shevtsovaRealSign
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_lt measurable_id measurable_const
  · refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_eq

lemma measurable_shevtsovaRealCot :
    Measurable shevtsovaRealCot := by
  unfold shevtsovaRealCot
  fun_prop

lemma measurable_shevtsovaPrawitzKernel :
    Measurable shevtsovaPrawitzKernel := by
  have hsign : Measurable shevtsovaRealSign := measurable_shevtsovaRealSign
  have hcot : Measurable shevtsovaRealCot := measurable_shevtsovaRealCot
  unfold shevtsovaPrawitzKernel
  fun_prop

lemma measurable_shevtsovaPrawitzKernel_norm :
    Measurable (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖) :=
  measurable_shevtsovaPrawitzKernel.norm

lemma integrableOn_shevtsovaPrawitzKernel_norm_Icc_half_one :
    IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc (1 / 2 : ℝ) 1) := by
  have hIcc_ne_top : volume (Set.Icc (1 / 2 : ℝ) 1) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hConst :
      IntegrableOn (fun _ : ℝ => (1 : ℝ))
        (Set.Icc (1 / 2 : ℝ) 1) :=
    integrableOn_const hIcc_ne_top
  refine hConst.mono' measurable_shevtsovaPrawitzKernel_norm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact shevtsovaPrawitzKernel_norm_le_one_of_mem_Icc_half_one ht

lemma integral_Icc_half_one_shevtsovaPrawitzKernel_norm_le :
    (∫ t in Set.Icc (1 / 2 : ℝ) 1,
      ‖shevtsovaPrawitzKernel t‖ ∂volume) ≤ 1 / 2 := by
  have hInt :
      IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
        (Set.Icc (1 / 2 : ℝ) 1) :=
    integrableOn_shevtsovaPrawitzKernel_norm_Icc_half_one
  have hIcc_ne_top : volume (Set.Icc (1 / 2 : ℝ) 1) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hConst :
      IntegrableOn (fun _ : ℝ => (1 : ℝ))
        (Set.Icc (1 / 2 : ℝ) 1) :=
    integrableOn_const hIcc_ne_top
  have hMono :
      (∫ t in Set.Icc (1 / 2 : ℝ) 1,
        ‖shevtsovaPrawitzKernel t‖ ∂volume) ≤
        ∫ t in Set.Icc (1 / 2 : ℝ) 1, (1 : ℝ) ∂volume := by
    refine setIntegral_mono_on hInt hConst measurableSet_Icc ?_
    intro t ht
    exact shevtsovaPrawitzKernel_norm_le_one_of_mem_Icc_half_one ht
  have hEval :
      (∫ t in Set.Icc (1 / 2 : ℝ) 1, (1 : ℝ) ∂volume) = 1 / 2 := by
    rw [setIntegral_const]
    rw [Real.volume_real_Icc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    norm_num
  exact hMono.trans_eq hEval

lemma integrableOn_shevtsovaPrawitzKernel_norm_Icc_of_half_le
    {t0 : ℝ} (hhalf : 1 / 2 ≤ t0) :
    IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 1) := by
  have hIcc_ne_top : volume (Set.Icc t0 1) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hConst :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc t0 1) :=
    integrableOn_const hIcc_ne_top
  refine hConst.mono' measurable_shevtsovaPrawitzKernel_norm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact
    shevtsovaPrawitzKernel_norm_le_one_of_mem_Icc_half_one
      ⟨hhalf.trans ht.1, ht.2⟩

lemma integral_Icc_shevtsovaPrawitzKernel_norm_le_one_sub_of_half_le
    {t0 : ℝ} (hhalf : 1 / 2 ≤ t0) (ht0_le_one : t0 ≤ 1) :
    (∫ t in Set.Icc t0 1,
      ‖shevtsovaPrawitzKernel t‖ ∂volume) ≤ 1 - t0 := by
  have hInt :
      IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
        (Set.Icc t0 1) :=
    integrableOn_shevtsovaPrawitzKernel_norm_Icc_of_half_le hhalf
  have hIcc_ne_top : volume (Set.Icc t0 1) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hConst :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc t0 1) :=
    integrableOn_const hIcc_ne_top
  have hMono :
      (∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ ∂volume) ≤
        ∫ t in Set.Icc t0 1, (1 : ℝ) ∂volume := by
    refine setIntegral_mono_on hInt hConst measurableSet_Icc ?_
    intro t ht
    exact
      shevtsovaPrawitzKernel_norm_le_one_of_mem_Icc_half_one
        ⟨hhalf.trans ht.1, ht.2⟩
  have hEval :
      (∫ t in Set.Icc t0 1, (1 : ℝ) ∂volume) = 1 - t0 := by
    rw [setIntegral_const]
    rw [Real.volume_real_Icc_of_le ht0_le_one]
    norm_num
  exact hMono.trans_eq hEval

lemma shevtsovaPrawitzKernel_norm_le_inv_t0_of_mem_Icc
    {t0 t : ℝ} (ht0 : 0 < t0)
    (ht : t ∈ Set.Icc t0 (1 / 2 : ℝ)) :
    ‖shevtsovaPrawitzKernel t‖ ≤ 1 / t0 := by
  have ht_pos : 0 < t := ht0.trans_le ht.1
  have ht_abs : |t| = t := abs_of_pos ht_pos
  have hkernel :=
    shevtsovaPrawitzKernel_abs_mul_norm_le_one_of_mem_Icc_zero_half
      (t := t) ⟨ht_pos.le, ht.2⟩
  have hnorm_le_inv_t : ‖shevtsovaPrawitzKernel t‖ ≤ 1 / t := by
    rw [ht_abs] at hkernel
    rw [le_div_iff₀ ht_pos]
    simpa [mul_comm] using hkernel
  exact hnorm_le_inv_t.trans (one_div_le_one_div_of_le ht0 ht.1)

lemma integrableOn_shevtsovaPrawitzKernel_norm_Icc_t0_half
    {t0 : ℝ} (ht0 : 0 < t0) :
    IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 (1 / 2 : ℝ)) := by
  have hIcc_ne_top : volume (Set.Icc t0 (1 / 2 : ℝ)) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hConst :
      IntegrableOn (fun _ : ℝ => 1 / t0)
        (Set.Icc t0 (1 / 2 : ℝ)) :=
    integrableOn_const hIcc_ne_top
  refine hConst.mono' measurable_shevtsovaPrawitzKernel_norm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact shevtsovaPrawitzKernel_norm_le_inv_t0_of_mem_Icc ht0 ht

lemma integral_Icc_t0_half_shevtsovaPrawitzKernel_norm_le
    {t0 : ℝ} (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) :
    (∫ t in Set.Icc t0 (1 / 2 : ℝ),
      ‖shevtsovaPrawitzKernel t‖ ∂volume) ≤
      (1 / t0) * (1 / 2 - t0) := by
  have hInt :
      IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
        (Set.Icc t0 (1 / 2 : ℝ)) :=
    integrableOn_shevtsovaPrawitzKernel_norm_Icc_t0_half ht0
  have hIcc_ne_top : volume (Set.Icc t0 (1 / 2 : ℝ)) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hConst :
      IntegrableOn (fun _ : ℝ => 1 / t0)
        (Set.Icc t0 (1 / 2 : ℝ)) :=
    integrableOn_const hIcc_ne_top
  have hMono :
      (∫ t in Set.Icc t0 (1 / 2 : ℝ),
        ‖shevtsovaPrawitzKernel t‖ ∂volume) ≤
        ∫ t in Set.Icc t0 (1 / 2 : ℝ), (1 / t0) ∂volume := by
    refine setIntegral_mono_on hInt hConst measurableSet_Icc ?_
    intro t ht
    exact shevtsovaPrawitzKernel_norm_le_inv_t0_of_mem_Icc ht0 ht
  have hEval :
      (∫ t in Set.Icc t0 (1 / 2 : ℝ), (1 / t0) ∂volume) =
        (1 / t0) * (1 / 2 - t0) := by
    rw [setIntegral_const]
    rw [Real.volume_real_Icc_of_le ht0le]
    simp [smul_eq_mul]
    ring
  exact hMono.trans_eq hEval

lemma shevtsovaPrawitzKernel_norm_le_inv_t0_of_mem_Icc_t0_one
    {t0 t : ℝ} (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2)
    (ht : t ∈ Set.Icc t0 (1 : ℝ)) :
    ‖shevtsovaPrawitzKernel t‖ ≤ 1 / t0 := by
  by_cases hle : t ≤ (1 / 2 : ℝ)
  · exact shevtsovaPrawitzKernel_norm_le_inv_t0_of_mem_Icc
      ht0 ⟨ht.1, hle⟩
  · have hhalf_le : (1 / 2 : ℝ) ≤ t := le_of_not_ge hle
    have hupper : ‖shevtsovaPrawitzKernel t‖ ≤ 1 :=
      shevtsovaPrawitzKernel_norm_le_one_of_mem_Icc_half_one
        ⟨hhalf_le, ht.2⟩
    have hinv_ge_one : (1 : ℝ) ≤ 1 / t0 := by
      rw [le_div_iff₀ ht0]
      nlinarith [ht0le]
    exact hupper.trans hinv_ge_one

lemma integrableOn_shevtsovaPrawitzKernel_norm_Icc_t0_one
    {t0 : ℝ} (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) :
    IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 (1 : ℝ)) := by
  have hIcc_ne_top : volume (Set.Icc t0 (1 : ℝ)) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hConst :
      IntegrableOn (fun _ : ℝ => 1 / t0) (Set.Icc t0 (1 : ℝ)) :=
    integrableOn_const hIcc_ne_top
  refine hConst.mono' measurable_shevtsovaPrawitzKernel_norm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact
    shevtsovaPrawitzKernel_norm_le_inv_t0_of_mem_Icc_t0_one
      ht0 ht0le ht

lemma integral_Icc_t0_one_shevtsovaPrawitzKernel_norm_le
    {t0 : ℝ} (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) :
    (∫ t in Set.Icc t0 (1 : ℝ),
      ‖shevtsovaPrawitzKernel t‖ ∂volume) ≤
      (1 / t0) * (1 - t0) := by
  have hInt :
      IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
        (Set.Icc t0 (1 : ℝ)) :=
    integrableOn_shevtsovaPrawitzKernel_norm_Icc_t0_one ht0 ht0le
  have hIcc_ne_top : volume (Set.Icc t0 (1 : ℝ)) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hConst :
      IntegrableOn (fun _ : ℝ => 1 / t0) (Set.Icc t0 (1 : ℝ)) :=
    integrableOn_const hIcc_ne_top
  have hMono :
      (∫ t in Set.Icc t0 (1 : ℝ),
        ‖shevtsovaPrawitzKernel t‖ ∂volume) ≤
        ∫ t in Set.Icc t0 (1 : ℝ), (1 / t0) ∂volume := by
    refine setIntegral_mono_on hInt hConst measurableSet_Icc ?_
    intro t ht
    exact
      shevtsovaPrawitzKernel_norm_le_inv_t0_of_mem_Icc_t0_one
        ht0 ht0le ht
  have ht0le1 : t0 ≤ (1 : ℝ) := by nlinarith [ht0le]
  have hEval :
      (∫ t in Set.Icc t0 (1 : ℝ), (1 / t0) ∂volume) =
        (1 / t0) * (1 - t0) := by
    rw [setIntegral_const]
    rw [Real.volume_real_Icc_of_le ht0le1]
    simp [smul_eq_mul]
    ring
  exact hMono.trans_eq hEval

lemma integral_Icc_t0_one_shevtsovaPrawitzKernel_norm_le_inv
    {t0 : ℝ} (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) :
    (∫ t in Set.Icc t0 (1 : ℝ),
      ‖shevtsovaPrawitzKernel t‖ ∂volume) ≤ 1 / t0 := by
  have h :=
    integral_Icc_t0_one_shevtsovaPrawitzKernel_norm_le
      (t0 := t0) ht0 ht0le
  have hnonneg : 0 ≤ 1 / t0 := by positivity
  have hlen : 1 - t0 ≤ 1 := by linarith [ht0.le]
  have hmul :
      (1 / t0) * (1 - t0) ≤ (1 / t0) * 1 :=
    mul_le_mul_of_nonneg_left hlen hnonneg
  nlinarith

/-- Auxiliary function `ψ(t, ε)` from the Prawitz/Shevtsova proof. -/
def shevtsovaPsi (t ε : ℝ) : ℝ :=
  if |t| ≤ shevtsovaTheta0 / ε then
    t ^ 2 / 2 - shevtsovaKappa * ε * |t| ^ 3
  else if shevtsovaTheta0 < ε * |t| ∧ ε * |t| ≤ 2 * Real.pi then
    (1 - Real.cos (ε * t)) / ε ^ 2
  else
    0

lemma shevtsovaPsi_eq_first_of_abs_le {t ε : ℝ}
    (h : |t| ≤ shevtsovaTheta0 / ε) :
    shevtsovaPsi t ε =
      t ^ 2 / 2 - shevtsovaKappa * ε * |t| ^ 3 := by
  simp [shevtsovaPsi, h]

lemma measurable_shevtsovaPsi_const_epsilon (ε : ℝ) :
    Measurable (fun t : ℝ => shevtsovaPsi t ε) := by
  unfold shevtsovaPsi
  have hfirst :
      MeasurableSet {t : ℝ | |t| ≤ shevtsovaTheta0 / ε} :=
    measurableSet_le measurable_abs measurable_const
  have hmulAbs : Measurable (fun t : ℝ => ε * |t|) :=
    measurable_const.mul measurable_abs
  have hsecond :
      MeasurableSet
        {t : ℝ | shevtsovaTheta0 < ε * |t| ∧
          ε * |t| ≤ 2 * Real.pi} :=
    (measurableSet_lt measurable_const hmulAbs).inter
      (measurableSet_le hmulAbs measurable_const)
  refine Measurable.ite hfirst ?_ ?_
  · fun_prop
  · refine Measurable.ite hsecond ?_ measurable_const
    fun_prop

lemma integrable_real_cos_mul (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ => Real.cos (t * x)) μ := by
  refine Integrable.of_bound
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Real.cos (t * x)) μ)
    1 ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact Real.abs_cos_le_one (t * x)

lemma integrable_real_sin_mul (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ => Real.sin (t * x)) μ := by
  refine Integrable.of_bound
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Real.sin (t * x)) μ)
    1 ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact Real.abs_sin_le_one (t * x)

lemma integrable_prawitzCosFirstMajorant
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) (t : ℝ) :
    Integrable
      (fun x : ℝ =>
        1 - (t * x) ^ 2 / 2 + shevtsovaKappa * |t * x| ^ 3) μ := by
  have h2 : Integrable (fun x : ℝ => x ^ 2) μ :=
    integrable_sq_of_integrable_abs_cube μ h3
  have hquad :
      Integrable (fun x : ℝ => (t * x) ^ 2 / 2) μ := by
    have hfun :
        (fun x : ℝ => (t * x) ^ 2 / 2) =
          fun x : ℝ => (t ^ 2 / 2) * x ^ 2 := by
      funext x
      ring_nf
    rw [hfun]
    exact h2.const_mul (t ^ 2 / 2)
  have hcube :
      Integrable (fun x : ℝ => shevtsovaKappa * |t * x| ^ 3) μ := by
    have hfun :
        (fun x : ℝ => shevtsovaKappa * |t * x| ^ 3) =
          fun x : ℝ => (shevtsovaKappa * |t| ^ 3) * |x| ^ 3 := by
      funext x
      rw [abs_mul, mul_pow]
      ring
    rw [hfun]
    exact h3.const_mul (shevtsovaKappa * |t| ^ 3)
  exact ((integrable_const (c := (1 : ℝ))).sub hquad).add hcube

lemma integral_cos_mul_le_one_sub_sq_div_two_add_shevtsovaKappa_abs_cube
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (t : ℝ) :
    ∫ x : ℝ, Real.cos (t * x) ∂μ ≤
      1 - t ^ 2 / 2 +
        shevtsovaKappa * |t| ^ 3 * ∫ x : ℝ, |x| ^ 3 ∂μ := by
  have hcos : Integrable (fun x : ℝ => Real.cos (t * x)) μ :=
    integrable_real_cos_mul μ t
  have hmajor :
      Integrable
        (fun x : ℝ =>
          1 - (t * x) ^ 2 / 2 + shevtsovaKappa * |t * x| ^ 3) μ :=
    integrable_prawitzCosFirstMajorant μ h3 t
  have hmono :
      ∫ x : ℝ, Real.cos (t * x) ∂μ ≤
        ∫ x : ℝ,
          1 - (t * x) ^ 2 / 2 + shevtsovaKappa * |t * x| ^ 3 ∂μ := by
    exact integral_mono hcos hmajor fun x =>
      real_cos_le_one_sub_sq_div_two_add_shevtsovaKappa_abs_cube (t * x)
  have h2 : Integrable (fun x : ℝ => x ^ 2) μ :=
    integrable_sq_of_integrable_abs_cube μ h3
  have hquad :
      Integrable (fun x : ℝ => (t * x) ^ 2 / 2) μ := by
    have hfun :
        (fun x : ℝ => (t * x) ^ 2 / 2) =
          fun x : ℝ => (t ^ 2 / 2) * x ^ 2 := by
      funext x
      ring_nf
    rw [hfun]
    exact h2.const_mul (t ^ 2 / 2)
  have hcube :
      Integrable (fun x : ℝ => shevtsovaKappa * |t * x| ^ 3) μ := by
    have hfun :
        (fun x : ℝ => shevtsovaKappa * |t * x| ^ 3) =
          fun x : ℝ => (shevtsovaKappa * |t| ^ 3) * |x| ^ 3 := by
      funext x
      rw [abs_mul, mul_pow]
      ring
    rw [hfun]
    exact h3.const_mul (shevtsovaKappa * |t| ^ 3)
  have hquad_int :
      (∫ x : ℝ, (t * x) ^ 2 / 2 ∂μ) = t ^ 2 / 2 := by
    calc
      (∫ x : ℝ, (t * x) ^ 2 / 2 ∂μ)
          = ∫ x : ℝ, (t ^ 2 / 2) * x ^ 2 ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards with x
              ring
      _ = (t ^ 2 / 2) * ∫ x : ℝ, x ^ 2 ∂μ := by
            rw [integral_const_mul]
      _ = t ^ 2 / 2 := by
            rw [hsecond]
            ring
  have hcube_int :
      (∫ x : ℝ, shevtsovaKappa * |t * x| ^ 3 ∂μ) =
        shevtsovaKappa * |t| ^ 3 * ∫ x : ℝ, |x| ^ 3 ∂μ := by
    calc
      (∫ x : ℝ, shevtsovaKappa * |t * x| ^ 3 ∂μ)
          = ∫ x : ℝ, (shevtsovaKappa * |t| ^ 3) * |x| ^ 3 ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards with x
              rw [abs_mul, mul_pow]
              ring
      _ = shevtsovaKappa * |t| ^ 3 * ∫ x : ℝ, |x| ^ 3 ∂μ := by
            rw [integral_const_mul]
  have hμreal_univ : μ.real Set.univ = 1 := by
    rw [measureReal_def, measure_univ]
    norm_num
  have hmajor_eval :
      (∫ x : ℝ,
          1 - (t * x) ^ 2 / 2 + shevtsovaKappa * |t * x| ^ 3 ∂μ) =
        1 - t ^ 2 / 2 +
          shevtsovaKappa * |t| ^ 3 * ∫ x : ℝ, |x| ^ 3 ∂μ := by
    calc
      (∫ x : ℝ,
          1 - (t * x) ^ 2 / 2 + shevtsovaKappa * |t * x| ^ 3 ∂μ)
          = (∫ x : ℝ, 1 - (t * x) ^ 2 / 2 ∂μ) +
              ∫ x : ℝ, shevtsovaKappa * |t * x| ^ 3 ∂μ := by
              simpa using
                integral_add ((integrable_const (c := (1 : ℝ))).sub hquad) hcube
      _ = ((∫ x : ℝ, (1 : ℝ) ∂μ) -
              ∫ x : ℝ, (t * x) ^ 2 / 2 ∂μ) +
            ∫ x : ℝ, shevtsovaKappa * |t * x| ^ 3 ∂μ := by
              rw [integral_sub (integrable_const (c := (1 : ℝ))) hquad]
      _ = 1 - t ^ 2 / 2 +
            shevtsovaKappa * |t| ^ 3 * ∫ x : ℝ, |x| ^ 3 ∂μ := by
              rw [integral_const, hμreal_univ, hquad_int, hcube_int]
              simp
  exact hmono.trans_eq hmajor_eval

lemma integral_cos_mul_le_one_sub_shevtsovaPsi_of_first_branch
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {t : ℝ}
    (hfirst :
      |t| ≤ shevtsovaTheta0 / (∫ x : ℝ, |x| ^ 3 ∂μ)) :
    ∫ x : ℝ, Real.cos (t * x) ∂μ ≤
      1 - shevtsovaPsi t (∫ x : ℝ, |x| ^ 3 ∂μ) := by
  calc
    ∫ x : ℝ, Real.cos (t * x) ∂μ
        ≤ 1 - t ^ 2 / 2 +
            shevtsovaKappa * |t| ^ 3 *
              ∫ x : ℝ, |x| ^ 3 ∂μ :=
          integral_cos_mul_le_one_sub_sq_div_two_add_shevtsovaKappa_abs_cube
            μ h3 hsecond t
    _ = 1 - shevtsovaPsi t (∫ x : ℝ, |x| ^ 3 ∂μ) := by
          rw [shevtsovaPsi_eq_first_of_abs_le hfirst]
          ring

/-- Random-variable form of the first branch of the Prawitz/Shevtsova cosine
majorant.  The proof maps the random variable to its law, so the law-level
integral estimate remains the canonical API. -/
lemma integral_cos_comp_le_one_sub_shevtsovaPsi_of_first_branch
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ}
    (hY : AEMeasurable Y P)
    (h3 : Integrable (fun ω => |Y ω| ^ 3) P)
    (hsecond : ∫ ω, Y ω ^ 2 ∂P = 1)
    {t : ℝ}
    (hfirst :
      |t| ≤ shevtsovaTheta0 / (∫ ω, |Y ω| ^ 3 ∂P)) :
    ∫ ω, Real.cos (t * Y ω) ∂P ≤
      1 - shevtsovaPsi t (∫ ω, |Y ω| ^ 3 ∂P) := by
  letI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY
  have h3map :
      Integrable (fun x : ℝ => |x| ^ 3) (P.map Y) := by
    have hgm :
        AEStronglyMeasurable (fun x : ℝ => |x| ^ 3) (P.map Y) :=
      (by fun_prop : Measurable (fun x : ℝ => |x| ^ 3)).aestronglyMeasurable
    rw [integrable_map_measure hgm hY]
    exact h3
  have hthird_map :
      (∫ x : ℝ, |x| ^ 3 ∂(P.map Y)) =
        ∫ ω, |Y ω| ^ 3 ∂P := by
    rw [integral_map hY]
    exact (by fun_prop :
      AEStronglyMeasurable (fun x : ℝ => |x| ^ 3) (P.map Y))
  have hsecond_map :
      (∫ x : ℝ, x ^ 2 ∂(P.map Y)) = 1 := by
    rw [integral_map hY]
    · exact hsecond
    · exact (by fun_prop :
        AEStronglyMeasurable (fun x : ℝ => x ^ 2) (P.map Y))
  have hcos_map :
      (∫ x : ℝ, Real.cos (t * x) ∂(P.map Y)) =
        ∫ ω, Real.cos (t * Y ω) ∂P := by
    rw [integral_map hY]
    exact (by fun_prop :
      AEStronglyMeasurable (fun x : ℝ => Real.cos (t * x)) (P.map Y))
  have hlaw :
      ∫ x : ℝ, Real.cos (t * x) ∂(P.map Y) ≤
        1 - shevtsovaPsi t (∫ x : ℝ, |x| ^ 3 ∂(P.map Y)) :=
    integral_cos_mul_le_one_sub_shevtsovaPsi_of_first_branch
      (P.map Y) h3map hsecond_map (by rwa [hthird_map])
  rwa [hcos_map, hthird_map] at hlaw

lemma charFun_re_eq_integral_cos
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    (charFun μ t).re = ∫ x : ℝ, Real.cos (t * x) ∂μ := by
  have hExp := integrable_exp_I_mul μ t
  have hExpEq :
      (∫ x, Complex.exp (↑t * ↑x * Complex.I) ∂μ) =
        ∫ x, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    congr 2
    norm_num
  calc
    (charFun μ t).re =
        (∫ x, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μ).re := by
          rw [charFun_apply_real, hExpEq]
    _ = ∫ x, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)).re ∂μ := by
          simpa using (integral_re hExp).symm
    _ = ∫ x : ℝ, Real.cos (t * x) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [Complex.exp_ofReal_mul_I_re]

lemma charFun_im_eq_integral_sin
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    (charFun μ t).im = ∫ x : ℝ, Real.sin (t * x) ∂μ := by
  have hExp := integrable_exp_I_mul μ t
  have hExpEq :
      (∫ x, Complex.exp (↑t * ↑x * Complex.I) ∂μ) =
        ∫ x, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    congr 2
    norm_num
  calc
    (charFun μ t).im =
        (∫ x, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂μ).im := by
          rw [charFun_apply_real, hExpEq]
    _ = ∫ x, (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)).im ∂μ := by
          simpa using (integral_im hExp).symm
    _ = ∫ x : ℝ, Real.sin (t * x) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [Complex.exp_ofReal_mul_I_im]

lemma abs_charFun_im_le_cubic_of_mean_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0) (t : ℝ) :
    |(charFun μ t).im| ≤
      (|t| ^ 3 / 6) * ∫ x : ℝ, |x| ^ 3 ∂μ := by
  have hsin : Integrable (fun x : ℝ => Real.sin (t * x)) μ :=
    integrable_real_sin_mul μ t
  have hlin : Integrable (fun x : ℝ => t * x) μ :=
    (integrable_id_of_integrable_abs_cube μ h3).const_mul t
  have hdiff :
      Integrable (fun x : ℝ => Real.sin (t * x) - t * x) μ :=
    hsin.sub hlin
  have hlin_int : (∫ x : ℝ, t * x ∂μ) = 0 := by
    rw [integral_const_mul, hmean, mul_zero]
  have hsin_eq :
      (∫ x : ℝ, Real.sin (t * x) ∂μ) =
        ∫ x : ℝ, Real.sin (t * x) - t * x ∂μ := by
    calc
      (∫ x : ℝ, Real.sin (t * x) ∂μ)
          = (∫ x : ℝ, Real.sin (t * x) ∂μ) -
              ∫ x : ℝ, t * x ∂μ := by
            rw [hlin_int, sub_zero]
      _ = ∫ x : ℝ, Real.sin (t * x) - t * x ∂μ := by
            rw [integral_sub hsin hlin]
  have hBoundInt :
      Integrable (fun x : ℝ => (|t| ^ 3 / 6) * |x| ^ 3) μ := by
    convert h3.const_mul (|t| ^ 3 / 6) using 1
  have hpoint :
      ∀ x : ℝ,
        ‖Real.sin (t * x) - t * x‖ ≤
          (|t| ^ 3 / 6) * |x| ^ 3 := by
    intro x
    rw [Real.norm_eq_abs]
    calc
      |Real.sin (t * x) - t * x| ≤ |t * x| ^ 3 / 6 :=
        abs_sin_sub_id_le_abs_cube_div_six (t * x)
      _ = (|t| ^ 3 / 6) * |x| ^ 3 := by
        rw [abs_mul, mul_pow]
        ring
  rw [charFun_im_eq_integral_sin μ t, hsin_eq]
  calc
    |∫ x : ℝ, Real.sin (t * x) - t * x ∂μ|
        = ‖∫ x : ℝ, Real.sin (t * x) - t * x ∂μ‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ x : ℝ, ‖Real.sin (t * x) - t * x‖ ∂μ :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, (|t| ^ 3 / 6) * |x| ^ 3 ∂μ := by
          exact integral_mono hdiff.norm hBoundInt hpoint
    _ = (|t| ^ 3 / 6) * ∫ x : ℝ, |x| ^ 3 ∂μ := by
          rw [integral_const_mul]

lemma charFun_im_sq_le_cubic_sq_of_mean_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0) (t : ℝ) :
    (charFun μ t).im ^ 2 ≤
      ((|t| ^ 3 / 6) * ∫ x : ℝ, |x| ^ 3 ∂μ) ^ 2 := by
  have h := abs_charFun_im_le_cubic_of_mean_zero
    (μ := μ) h3 hmean t
  rw [← sq_abs ((charFun μ t).im)]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

lemma charFun_re_le_one_sub_shevtsovaPsi_of_first_branch
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {t : ℝ}
    (hfirst :
      |t| ≤ shevtsovaTheta0 / (∫ x : ℝ, |x| ^ 3 ∂μ)) :
    (charFun μ t).re ≤
      1 - shevtsovaPsi t (∫ x : ℝ, |x| ^ 3 ∂μ) := by
  rw [charFun_re_eq_integral_cos μ t]
  exact integral_cos_mul_le_one_sub_shevtsovaPsi_of_first_branch
    μ h3 hsecond hfirst

/-- Random-variable form of the first-branch real-part characteristic-function
bound. -/
lemma charFun_map_re_le_one_sub_shevtsovaPsi_of_first_branch
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ}
    (hY : AEMeasurable Y P)
    (h3 : Integrable (fun ω => |Y ω| ^ 3) P)
    (hsecond : ∫ ω, Y ω ^ 2 ∂P = 1)
    {t : ℝ}
    (hfirst :
      |t| ≤ shevtsovaTheta0 / (∫ ω, |Y ω| ^ 3 ∂P)) :
    (charFun (P.map Y) t).re ≤
      1 - shevtsovaPsi t (∫ ω, |Y ω| ^ 3 ∂P) := by
  letI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY
  rw [charFun_re_eq_integral_cos (P.map Y) t]
  have hcos_map :
      (∫ x : ℝ, Real.cos (t * x) ∂(P.map Y)) =
        ∫ ω, Real.cos (t * Y ω) ∂P := by
    rw [integral_map hY]
    exact (by fun_prop :
      AEStronglyMeasurable (fun x : ℝ => Real.cos (t * x)) (P.map Y))
  rw [hcos_map]
  exact integral_cos_comp_le_one_sub_shevtsovaPsi_of_first_branch
    hY h3 hsecond hfirst

lemma standardizedCharFun_im_abs_le_cubic_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ t : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    |(charFun (P.map (fun ω => (X 0 ω - m) / σ)) t).im| ≤
      (|t| ^ 3 / 6) * berryEsseenRho X P m σ := by
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hstd_meas
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3) ν := by
    dsimp [ν]
    exact integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hmean :
      ∫ x : ℝ, x ∂ν = 0 := by
    dsimp [ν]
    exact integral_standardizedLaw_id_eq_zero
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_int (hBE.mean_eq 0)
      hBE.sigma_pos.ne'
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂ν = berryEsseenRho X P m σ := by
    dsimp [ν]
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  have h :=
    abs_charFun_im_le_cubic_of_mean_zero
      (μ := ν) h3 hmean t
  simpa [ν, hM] using h

lemma standardizedCharFun_im_sq_le_cubic_sq_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ t : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    (charFun (P.map (fun ω => (X 0 ω - m) / σ)) t).im ^ 2 ≤
      ((|t| ^ 3 / 6) * berryEsseenRho X P m σ) ^ 2 := by
  have h := standardizedCharFun_im_abs_le_cubic_of_hypotheses
    (P := P) (X := X) (m := m) (σ := σ) (t := t) hBE
  rw [← sq_abs ((charFun (P.map (fun ω => (X 0 ω - m) / σ)) t).im)]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

lemma add_cube_le_four_mul_cube_add_cube {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  have hnonneg : 0 ≤ 3 * (a + b) * (a - b) ^ 2 := by positivity
  have hidentity :
      4 * (a ^ 3 + b ^ 3) - (a + b) ^ 3 =
        3 * (a + b) * (a - b) ^ 2 := by
    ring
  nlinarith

lemma abs_sub_cube_le_four_mul_abs_cube_add_abs_cube (x y : ℝ) :
    |x - y| ^ 3 ≤ 4 * (|x| ^ 3 + |y| ^ 3) := by
  have htri : |x - y| ≤ |x| + |y| := by
    simpa [sub_eq_add_neg] using abs_add_le x (-y)
  calc
    |x - y| ^ 3 ≤ (|x| + |y|) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) htri 3
    _ ≤ 4 * (|x| ^ 3 + |y| ^ 3) :=
      add_cube_le_four_mul_cube_add_cube (abs_nonneg x) (abs_nonneg y)

lemma integrable_abs_fst_cube_prod
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Integrable (fun p : ℝ × ℝ => |p.1| ^ 3) (μ.prod μ) :=
  h3.comp_fst μ

lemma integrable_abs_snd_cube_prod
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Integrable (fun p : ℝ × ℝ => |p.2| ^ 3) (μ.prod μ) :=
  h3.comp_snd μ

lemma integrable_abs_symmDiff_cube_prod
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 3) (μ.prod μ) := by
  have hfst : Integrable (fun p : ℝ × ℝ => |p.1| ^ 3) (μ.prod μ) :=
    integrable_abs_fst_cube_prod μ h3
  have hsnd : Integrable (fun p : ℝ × ℝ => |p.2| ^ 3) (μ.prod μ) :=
    integrable_abs_snd_cube_prod μ h3
  have hbound :
      Integrable (fun p : ℝ × ℝ => 4 * (|p.1| ^ 3 + |p.2| ^ 3))
        (μ.prod μ) :=
    (hfst.add hsnd).const_mul 4
  refine hbound.mono' ?_ ?_
  · exact (by fun_prop :
      AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 3) (μ.prod μ))
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg (p.1 - p.2)) 3)]
    exact abs_sub_cube_le_four_mul_abs_cube_add_abs_cube p.1 p.2

lemma integrable_abs_symmDiff_div_sqrt_two_cube_prod
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Integrable
      (fun p : ℝ × ℝ => |(p.1 - p.2) / Real.sqrt 2| ^ 3)
      (μ.prod μ) := by
  have hdiff : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 3) (μ.prod μ) :=
    integrable_abs_symmDiff_cube_prod μ h3
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  convert hdiff.const_mul ((Real.sqrt (2 : ℝ)) ^ 3)⁻¹ using 1
  ext p
  rw [abs_div, abs_of_pos hsqrt_pos, div_eq_mul_inv, mul_pow]
  ring

lemma integral_abs_symmDiff_div_sqrt_two_cube_prod_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    ∫ p : ℝ × ℝ, |(p.1 - p.2) / Real.sqrt 2| ^ 3 ∂(μ.prod μ) ≤
      2 * Real.sqrt 2 * ∫ x : ℝ, |x| ^ 3 ∂μ := by
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_ne : Real.sqrt (2 : ℝ) ≠ 0 := hsqrt_pos.ne'
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt_cube_pos : 0 < Real.sqrt (2 : ℝ) ^ 3 :=
    pow_pos hsqrt_pos 3
  have hconst : 4 / Real.sqrt (2 : ℝ) ^ 3 = Real.sqrt 2 := by
    have hcube_ne : Real.sqrt (2 : ℝ) ^ 3 ≠ 0 :=
      pow_ne_zero 3 hsqrt_ne
    rw [div_eq_iff hcube_ne]
    calc
      (4 : ℝ) = (Real.sqrt 2 ^ 2) ^ 2 := by
        rw [hsqrt_sq]
        norm_num
      _ = Real.sqrt 2 * Real.sqrt 2 ^ 3 := by
        ring
  have hleft :
      Integrable
        (fun p : ℝ × ℝ => |(p.1 - p.2) / Real.sqrt 2| ^ 3) (μ.prod μ) :=
    integrable_abs_symmDiff_div_sqrt_two_cube_prod μ h3
  have hfst : Integrable (fun p : ℝ × ℝ => |p.1| ^ 3) (μ.prod μ) :=
    integrable_abs_fst_cube_prod μ h3
  have hsnd : Integrable (fun p : ℝ × ℝ => |p.2| ^ 3) (μ.prod μ) :=
    integrable_abs_snd_cube_prod μ h3
  have hmajor :
      Integrable
        (fun p : ℝ × ℝ => Real.sqrt 2 * (|p.1| ^ 3 + |p.2| ^ 3)) (μ.prod μ) :=
    (hfst.add hsnd).const_mul (Real.sqrt 2)
  have hmono :
      ∫ p : ℝ × ℝ, |(p.1 - p.2) / Real.sqrt 2| ^ 3 ∂(μ.prod μ) ≤
        ∫ p : ℝ × ℝ,
          Real.sqrt 2 * (|p.1| ^ 3 + |p.2| ^ 3) ∂(μ.prod μ) := by
    exact integral_mono hleft hmajor fun p => by
      have hdiff :
          |p.1 - p.2| ^ 3 ≤ 4 * (|p.1| ^ 3 + |p.2| ^ 3) :=
        abs_sub_cube_le_four_mul_abs_cube_add_abs_cube p.1 p.2
      calc
        |(p.1 - p.2) / Real.sqrt 2| ^ 3
            = |p.1 - p.2| ^ 3 / Real.sqrt 2 ^ 3 := by
                rw [abs_div, div_pow, abs_of_pos hsqrt_pos]
        _ ≤ (4 * (|p.1| ^ 3 + |p.2| ^ 3)) / Real.sqrt 2 ^ 3 := by
                exact div_le_div_of_nonneg_right hdiff hsqrt_cube_pos.le
        _ = (4 / Real.sqrt 2 ^ 3) * (|p.1| ^ 3 + |p.2| ^ 3) := by
                ring
        _ = Real.sqrt 2 * (|p.1| ^ 3 + |p.2| ^ 3) := by
                rw [hconst]
  have hfst_int :
      (∫ p : ℝ × ℝ, |p.1| ^ 3 ∂(μ.prod μ)) =
        ∫ x : ℝ, |x| ^ 3 ∂μ := by
    have h :=
      (integral_fun_fst (μ := μ) (ν := μ) (f := fun x : ℝ => |x| ^ 3))
    rw [h]
    simp [measureReal_def]
  have hsnd_int :
      (∫ p : ℝ × ℝ, |p.2| ^ 3 ∂(μ.prod μ)) =
        ∫ x : ℝ, |x| ^ 3 ∂μ := by
    have h :=
      (integral_fun_snd (μ := μ) (ν := μ) (f := fun x : ℝ => |x| ^ 3))
    rw [h]
    simp [measureReal_def]
  have hmajor_eval :
      (∫ p : ℝ × ℝ,
        Real.sqrt 2 * (|p.1| ^ 3 + |p.2| ^ 3) ∂(μ.prod μ)) =
        2 * Real.sqrt 2 * ∫ x : ℝ, |x| ^ 3 ∂μ := by
    calc
      (∫ p : ℝ × ℝ,
        Real.sqrt 2 * (|p.1| ^ 3 + |p.2| ^ 3) ∂(μ.prod μ))
          = Real.sqrt 2 *
              ∫ p : ℝ × ℝ, |p.1| ^ 3 + |p.2| ^ 3 ∂(μ.prod μ) := by
              rw [integral_const_mul]
      _ = Real.sqrt 2 *
            ((∫ p : ℝ × ℝ, |p.1| ^ 3 ∂(μ.prod μ)) +
              ∫ p : ℝ × ℝ, |p.2| ^ 3 ∂(μ.prod μ)) := by
              rw [integral_add hfst hsnd]
      _ = 2 * Real.sqrt 2 * ∫ x : ℝ, |x| ^ 3 ∂μ := by
              rw [hfst_int, hsnd_int]
              ring
  exact hmono.trans_eq hmajor_eval

lemma integrable_symmDiff_sq_prod
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (μ.prod μ) := by
  have h1 : Integrable (fun x : ℝ => x) μ :=
    integrable_id_of_integrable_abs_cube μ h3
  have h2 : Integrable (fun x : ℝ => x ^ 2) μ :=
    integrable_sq_of_integrable_abs_cube μ h3
  have hfst2 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (μ.prod μ) :=
    h2.comp_fst μ
  have hsnd2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (μ.prod μ) :=
    h2.comp_snd μ
  have hcross : Integrable (fun p : ℝ × ℝ => p.1 * p.2) (μ.prod μ) :=
    h1.mul_prod h1
  have h2cross : Integrable (fun p : ℝ × ℝ => 2 * (p.1 * p.2)) (μ.prod μ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross.const_mul 2
  refine ((hfst2.sub h2cross).add hsnd2).congr ?_
  filter_upwards with p
  simp only [Pi.add_apply, Pi.sub_apply]
  ring_nf

lemma integral_symmDiff_sq_prod_eq_two
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1) :
    ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(μ.prod μ) = 2 := by
  have h1 : Integrable (fun x : ℝ => x) μ :=
    integrable_id_of_integrable_abs_cube μ h3
  have h2 : Integrable (fun x : ℝ => x ^ 2) μ :=
    integrable_sq_of_integrable_abs_cube μ h3
  have hfst2 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (μ.prod μ) :=
    h2.comp_fst μ
  have hsnd2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (μ.prod μ) :=
    h2.comp_snd μ
  have hcross : Integrable (fun p : ℝ × ℝ => p.1 * p.2) (μ.prod μ) :=
    h1.mul_prod h1
  have h2cross : Integrable (fun p : ℝ × ℝ => 2 * (p.1 * p.2)) (μ.prod μ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross.const_mul 2
  have hrewrite :
      (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(μ.prod μ)) =
        ∫ p : ℝ × ℝ, p.1 ^ 2 - 2 * (p.1 * p.2) + p.2 ^ 2 ∂(μ.prod μ) := by
    refine integral_congr_ae ?_
    filter_upwards with p
    ring
  have hfst_int :
      (∫ p : ℝ × ℝ, p.1 ^ 2 ∂(μ.prod μ)) = 1 := by
    have h :=
      (integral_fun_fst (μ := μ) (ν := μ) (f := fun x : ℝ => x ^ 2))
    rw [h]
    rw [hsecond]
    simp [measureReal_def]
  have hsnd_int :
      (∫ p : ℝ × ℝ, p.2 ^ 2 ∂(μ.prod μ)) = 1 := by
    have h :=
      (integral_fun_snd (μ := μ) (ν := μ) (f := fun x : ℝ => x ^ 2))
    rw [h]
    rw [hsecond]
    simp [measureReal_def]
  have hcross_int :
      (∫ p : ℝ × ℝ, p.1 * p.2 ∂(μ.prod μ)) = 0 := by
    simpa [hmean] using
      (integral_prod_mul (μ := μ) (ν := μ)
        (f := fun x : ℝ => x) (g := fun x : ℝ => x))
  have hsub_int :
      (∫ p : ℝ × ℝ, p.1 ^ 2 - 2 * (p.1 * p.2) ∂(μ.prod μ)) =
        (∫ p : ℝ × ℝ, p.1 ^ 2 ∂(μ.prod μ)) -
          ∫ p : ℝ × ℝ, 2 * (p.1 * p.2) ∂(μ.prod μ) := by
    simpa [Pi.sub_apply] using integral_sub hfst2 h2cross
  have hexpanded_int :
      (∫ p : ℝ × ℝ,
        p.1 ^ 2 - 2 * (p.1 * p.2) + p.2 ^ 2 ∂(μ.prod μ)) =
        (∫ p : ℝ × ℝ, p.1 ^ 2 - 2 * (p.1 * p.2) ∂(μ.prod μ)) +
          ∫ p : ℝ × ℝ, p.2 ^ 2 ∂(μ.prod μ) := by
    simpa [Pi.add_apply] using integral_add (hfst2.sub h2cross) hsnd2
  have hcross2_int :
      (∫ p : ℝ × ℝ, 2 * (p.1 * p.2) ∂(μ.prod μ)) = 0 := by
    rw [integral_const_mul, hcross_int]
    ring
  rw [hrewrite, hexpanded_int, hsub_int, hfst_int, hsnd_int, hcross2_int]
  ring

lemma integral_symmDiff_div_sqrt_two_sq_prod_eq_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1) :
    ∫ p : ℝ × ℝ, ((p.1 - p.2) / Real.sqrt 2) ^ 2 ∂(μ.prod μ) = 1 := by
  have hdiff : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (μ.prod μ) :=
    integrable_symmDiff_sq_prod μ h3
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  calc
    ∫ p : ℝ × ℝ, ((p.1 - p.2) / Real.sqrt 2) ^ 2 ∂(μ.prod μ)
        = ∫ p : ℝ × ℝ, (1 / 2 : ℝ) * (p.1 - p.2) ^ 2 ∂(μ.prod μ) := by
            refine integral_congr_ae ?_
            filter_upwards with p
            field_simp [hsqrt_pos.ne']
            rw [hsqrt_sq]
    _ = (1 / 2 : ℝ) *
          ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(μ.prod μ) := by
            rw [integral_const_mul]
    _ = 1 := by
            rw [integral_symmDiff_sq_prod_eq_two μ h3 hmean hsecond]
            ring

/-- Symmetrization identity for characteristic functions: if `X` and `X'`
are independent with law `μ`, then the real part of the characteristic
function of `X - X'` is `|f(t)|²`. -/
lemma charFun_symmetrizedDiff_re_eq_norm_sq
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (charFun ((μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)) t).re =
      ‖charFun μ t‖ ^ 2 := by
  let neg : ℝ → ℝ := fun x => -x
  let addPair : ℝ × ℝ → ℝ := fun p => p.1 + p.2
  let diffPair : ℝ × ℝ → ℝ := fun p => p.1 - p.2
  have hneg_meas : Measurable neg := by
    dsimp [neg]
    fun_prop
  letI : IsProbabilityMeasure (μ.map neg) :=
    Measure.isProbabilityMeasure_map hneg_meas.aemeasurable
  have hmap :
      (μ.prod (μ.map neg)).map addPair =
        (μ.prod μ).map diffPair := by
    have hprod :
        μ.prod (μ.map neg) =
          (μ.prod μ).map (Prod.map id neg) := by
      simpa [neg] using
        (Measure.map_prod_map μ μ measurable_id
          hneg_meas)
    rw [hprod]
    rw [Measure.map_map]
    · congr 1
    · exact (by fun_prop : Measurable addPair)
    · exact measurable_id.prodMap hneg_meas
  have hneg :
      charFun (μ.map neg) t = charFun μ (-t) := by
    simpa [neg] using (charFun_map_mul (μ := μ) (-1 : ℝ) t)
  have hcf :
      charFun ((μ.prod μ).map diffPair) t =
        charFun μ t * (starRingEnd ℂ) (charFun μ t) := by
    have hprod :=
      congrFun
        (charFun_map_add_prod_eq_mul (μ := μ) (ν := μ.map neg)) t
    rw [← hmap]
    calc
      charFun ((μ.prod (μ.map neg)).map addPair) t
          = charFun μ t * charFun (μ.map neg) t := by
              simpa [addPair, Pi.mul_apply] using hprod
      _ = charFun μ t * (starRingEnd ℂ) (charFun μ t) := by
              rw [hneg, charFun_neg]
  rw [hcf]
  rw [Complex.mul_conj]
  simp [Complex.sq_norm]

/-- Variance-normalized symmetrization identity.  The real part of the
characteristic function of `(X - X') / sqrt 2` is the squared modulus of the
original characteristic function at the scaled frequency. -/
lemma charFun_symmetrizedDiff_div_sqrt_two_re_eq_norm_sq
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (charFun ((μ.prod μ).map
        (fun p : ℝ × ℝ => (p.1 - p.2) / Real.sqrt 2)) t).re =
      ‖charFun μ (t / Real.sqrt 2)‖ ^ 2 := by
  let diffPair : ℝ × ℝ → ℝ := fun p => p.1 - p.2
  have hscale :
      charFun ((μ.prod μ).map
          (fun p : ℝ × ℝ => (p.1 - p.2) / Real.sqrt 2)) t =
        charFun ((μ.prod μ).map diffPair) (t / Real.sqrt 2) := by
    have h :=
      charFun_map_mul_comp
        (μ := μ.prod μ) (f := diffPair)
        (by fun_prop : AEMeasurable diffPair (μ.prod μ))
        ((Real.sqrt 2)⁻¹) t
    have harg : (Real.sqrt 2)⁻¹ * t = t / Real.sqrt 2 := by
      rw [div_eq_mul_inv, mul_comm]
    simpa [diffPair, div_eq_mul_inv, mul_comm, harg] using h
  rw [hscale]
  exact charFun_symmetrizedDiff_re_eq_norm_sq μ (t / Real.sqrt 2)

/-- First-branch Prawitz/Shevtsova square-modulus estimate obtained by
applying the cosine majorant to the symmetrized law `(X - X') / sqrt 2`. -/
lemma norm_charFun_div_sqrt_two_sq_le_one_sub_shevtsovaPsi_symmDiff_of_first_branch
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {t : ℝ}
    (hfirst :
      |t| ≤ shevtsovaTheta0 /
        (∫ p : ℝ × ℝ, |(p.1 - p.2) / Real.sqrt 2| ^ 3 ∂(μ.prod μ))) :
    ‖charFun μ (t / Real.sqrt 2)‖ ^ 2 ≤
      1 - shevtsovaPsi t
        (∫ p : ℝ × ℝ, |(p.1 - p.2) / Real.sqrt 2| ^ 3 ∂(μ.prod μ)) := by
  let Y : ℝ × ℝ → ℝ := fun p => (p.1 - p.2) / Real.sqrt 2
  have hY : AEMeasurable Y (μ.prod μ) := by
    dsimp [Y]
    fun_prop
  have h3Y : Integrable (fun p : ℝ × ℝ => |Y p| ^ 3) (μ.prod μ) := by
    dsimp [Y]
    exact integrable_abs_symmDiff_div_sqrt_two_cube_prod μ h3
  have hsecondY : ∫ p : ℝ × ℝ, Y p ^ 2 ∂(μ.prod μ) = 1 := by
    dsimp [Y]
    exact integral_symmDiff_div_sqrt_two_sq_prod_eq_one μ h3 hmean hsecond
  have hbound :
      (charFun ((μ.prod μ).map Y) t).re ≤
        1 - shevtsovaPsi t (∫ p : ℝ × ℝ, |Y p| ^ 3 ∂(μ.prod μ)) :=
    charFun_map_re_le_one_sub_shevtsovaPsi_of_first_branch
      (P := μ.prod μ) (Y := Y) hY h3Y hsecondY hfirst
  have hid := charFun_symmetrizedDiff_div_sqrt_two_re_eq_norm_sq μ t
  simpa [Y, hid] using hbound

/-- Frequency-rescaled version of
`norm_charFun_div_sqrt_two_sq_le_one_sub_shevtsovaPsi_symmDiff_of_first_branch`,
with the original characteristic function evaluated at `t`. -/
lemma norm_charFun_sq_le_one_sub_shevtsovaPsi_symmDiff_scaled_of_first_branch
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {t : ℝ}
    (hfirst :
      |Real.sqrt 2 * t| ≤ shevtsovaTheta0 /
        (∫ p : ℝ × ℝ, |(p.1 - p.2) / Real.sqrt 2| ^ 3 ∂(μ.prod μ))) :
    ‖charFun μ t‖ ^ 2 ≤
      1 - shevtsovaPsi (Real.sqrt 2 * t)
        (∫ p : ℝ × ℝ, |(p.1 - p.2) / Real.sqrt 2| ^ 3 ∂(μ.prod μ)) := by
  have hsqrt_ne : Real.sqrt (2 : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h :=
    norm_charFun_div_sqrt_two_sq_le_one_sub_shevtsovaPsi_symmDiff_of_first_branch
      μ h3 hmean hsecond (t := Real.sqrt 2 * t) hfirst
  have harg : Real.sqrt 2 * t / Real.sqrt 2 = t := by
    field_simp [hsqrt_ne]
  simpa [harg] using h

lemma standardizedCharFun_re_le_one_sub_shevtsovaPsi_of_first_branch_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ t : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (hfirst : |t| ≤ shevtsovaTheta0 / berryEsseenRho X P m σ) :
    (charFun (P.map (fun ω => (X 0 ω - m) / σ)) t).re ≤
      1 - shevtsovaPsi t (berryEsseenRho X P m σ) := by
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hstd_meas
  have h3 :
      Integrable (fun x : ℝ => |x| ^ 3) ν := by
    dsimp [ν]
    exact integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hsecond :
      ∫ x : ℝ, x ^ 2 ∂ν = 1 := by
    dsimp [ν]
    exact integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂ν = berryEsseenRho X P m σ := by
    dsimp [ν]
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  have hfirstν :
      |t| ≤ shevtsovaTheta0 / (∫ x : ℝ, |x| ^ 3 ∂ν) := by
    simpa [hM] using hfirst
  have h :=
    charFun_re_le_one_sub_shevtsovaPsi_of_first_branch
      (μ := ν) h3 hsecond hfirstν
  simpa [ν, hM] using h

lemma shevtsovaPsi_eq_second_of_first_not_and_window {t ε : ℝ}
    (hfirst : ¬ |t| ≤ shevtsovaTheta0 / ε)
    (hwindow : shevtsovaTheta0 < ε * |t| ∧ ε * |t| ≤ 2 * Real.pi) :
    shevtsovaPsi t ε = (1 - Real.cos (ε * t)) / ε ^ 2 := by
  simp [shevtsovaPsi, hfirst, hwindow]

lemma shevtsovaPsi_eq_zero_of_not_first_not_second {t ε : ℝ}
    (hfirst : ¬ |t| ≤ shevtsovaTheta0 / ε)
    (hsecond :
      ¬ (shevtsovaTheta0 < ε * |t| ∧ ε * |t| ≤ 2 * Real.pi)) :
    shevtsovaPsi t ε = 0 := by
  simp [shevtsovaPsi, hfirst, hsecond]

lemma shevtsovaPsi_zero_of_pos {ε : ℝ} (hε : 0 < ε) :
    shevtsovaPsi 0 ε = 0 := by
  have hfirst : |(0 : ℝ)| ≤ shevtsovaTheta0 / ε := by
    simpa using (div_pos shevtsovaTheta0_pos hε).le
  rw [shevtsovaPsi_eq_first_of_abs_le hfirst]
  simp

lemma shevtsovaPsi_div_sqrt_eq_div
    {N : ℕ} (hN : 0 < N) {t ε : ℝ} (hε : 0 < ε) :
    shevtsovaPsi (t / Real.sqrt (N : ℝ)) ε =
      shevtsovaPsi t (ε / Real.sqrt (N : ℝ)) / (N : ℝ) := by
  let s : ℝ := Real.sqrt (N : ℝ)
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr hN_pos
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hs_sq : s ^ 2 = (N : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt hN_pos.le
  have hεs_pos : 0 < ε / s := div_pos hε hs_pos
  have hfirst_iff :
      |t / s| ≤ shevtsovaTheta0 / ε ↔
        |t| ≤ shevtsovaTheta0 / (ε / s) := by
    rw [abs_div, abs_of_pos hs_pos]
    constructor
    · intro h
      rw [le_div_iff₀ hεs_pos]
      have hmul := mul_le_mul_of_nonneg_left h hs_pos.le
      field_simp [hs_ne] at hmul ⊢
      linarith
    · intro h
      rw [le_div_iff₀ hε]
      have hmul := mul_le_mul_of_nonneg_left h hεs_pos.le
      field_simp [hs_ne] at hmul ⊢
      linarith
  have hwindow_iff :
      (shevtsovaTheta0 < ε * |t / s| ∧
        ε * |t / s| ≤ 2 * Real.pi) ↔
      (shevtsovaTheta0 < (ε / s) * |t| ∧
        (ε / s) * |t| ≤ 2 * Real.pi) := by
    have hscale : ε * |t / s| = (ε / s) * |t| := by
      rw [abs_div, abs_of_pos hs_pos]
      field_simp [hs_ne]
    rw [hscale]
  by_cases hfirst :
      |t| ≤ shevtsovaTheta0 / (ε / s)
  · have hfirst_left : |t / s| ≤ shevtsovaTheta0 / ε :=
      hfirst_iff.mpr hfirst
    rw [shevtsovaPsi_eq_first_of_abs_le hfirst_left,
      shevtsovaPsi_eq_first_of_abs_le hfirst]
    rw [abs_div, abs_of_pos hs_pos]
    field_simp [hs_ne, hε.ne', hεs_pos.ne', hs_sq]
    rw [← hs_sq]
    ring
  · have hfirst_left : ¬ |t / s| ≤ shevtsovaTheta0 / ε := by
      intro hleft
      exact hfirst (hfirst_iff.mp hleft)
    by_cases hwindow :
        shevtsovaTheta0 < (ε / s) * |t| ∧
          (ε / s) * |t| ≤ 2 * Real.pi
    · have hwindow_left :
        shevtsovaTheta0 < ε * |t / s| ∧
          ε * |t / s| ≤ 2 * Real.pi :=
          hwindow_iff.mpr hwindow
      rw [shevtsovaPsi_eq_second_of_first_not_and_window
          hfirst_left hwindow_left,
        shevtsovaPsi_eq_second_of_first_not_and_window
          hfirst hwindow]
      have harg : ε * (t / s) = (ε / s) * t := by
        field_simp [hs_ne]
      rw [harg]
      field_simp [hs_ne, hε.ne', hεs_pos.ne', hs_sq]
      rw [← hs_sq]
      ring
    · have hwindow_left :
        ¬ (shevtsovaTheta0 < ε * |t / s| ∧
          ε * |t / s| ≤ 2 * Real.pi) := by
          intro hleft
          exact hwindow (hwindow_iff.mp hleft)
      rw [shevtsovaPsi_eq_zero_of_not_first_not_second
          hfirst_left hwindow_left,
        shevtsovaPsi_eq_zero_of_not_first_not_second
          hfirst hwindow]
      simp

lemma shevtsovaPsi_div_sqrt_eq_div_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ t : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) :
    shevtsovaPsi (t / Real.sqrt (N : ℝ))
        (berryEsseenRho X P m σ) =
      shevtsovaPsi t
        (shevtsovaLyapunovFraction (berryEsseenRho X P m σ) N) /
          (N : ℝ) := by
  have hrho_pos : 0 < berryEsseenRho X P m σ := by
    exact lt_of_lt_of_le zero_lt_one
      (one_le_berryEsseenRho_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE)
  simpa [shevtsovaLyapunovFraction] using
    shevtsovaPsi_div_sqrt_eq_div
      (N := N) hN (t := t)
      (ε := berryEsseenRho X P m σ) hrho_pos

lemma shevtsovaPsi_two_sqrt_two_scale_eq_div
    {N : ℕ} (hN : 0 < N) {t ρ : ℝ} (hρ : 0 < ρ) :
    shevtsovaPsi
        (Real.sqrt 2 * (t / Real.sqrt (N : ℝ)))
        (2 * Real.sqrt 2 * ρ) =
      shevtsovaPsi (Real.sqrt 2 * t)
        (2 * Real.sqrt 2 * shevtsovaLyapunovFraction ρ N) /
          (N : ℝ) := by
  have hsqrt_two_pos : 0 < Real.sqrt (2 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hε_pos : 0 < 2 * Real.sqrt 2 * ρ :=
    mul_pos (mul_pos (by norm_num) hsqrt_two_pos) hρ
  have h :=
    shevtsovaPsi_div_sqrt_eq_div
      (N := N) hN (t := Real.sqrt 2 * t)
      (ε := 2 * Real.sqrt 2 * ρ) hε_pos
  have harg :
      (Real.sqrt 2 * t) / Real.sqrt (N : ℝ) =
        Real.sqrt 2 * (t / Real.sqrt (N : ℝ)) := by
    ring
  have hε :
      (2 * Real.sqrt 2 * ρ) / Real.sqrt (N : ℝ) =
        2 * Real.sqrt 2 * shevtsovaLyapunovFraction ρ N := by
    simp [shevtsovaLyapunovFraction]
    ring
  simpa [harg, hε] using h

lemma shevtsovaPsi_two_sqrt_two_scale_eq_div_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ t : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) :
    shevtsovaPsi
        (Real.sqrt 2 * (t / Real.sqrt (N : ℝ)))
        (2 * Real.sqrt 2 * berryEsseenRho X P m σ) =
      shevtsovaPsi (Real.sqrt 2 * t)
        (2 * Real.sqrt 2 *
          shevtsovaLyapunovFraction (berryEsseenRho X P m σ) N) /
          (N : ℝ) := by
  have hrho_pos : 0 < berryEsseenRho X P m σ := by
    exact lt_of_lt_of_le zero_lt_one
      (one_le_berryEsseenRho_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE)
  exact
    shevtsovaPsi_two_sqrt_two_scale_eq_div
      (N := N) hN (t := t)
      (ρ := berryEsseenRho X P m σ) hrho_pos

lemma shevtsovaPsi_second_nonneg {t ε : ℝ}
    (hfirst : ¬ |t| ≤ shevtsovaTheta0 / ε)
    (hwindow : shevtsovaTheta0 < ε * |t| ∧ ε * |t| ≤ 2 * Real.pi) :
    0 ≤ shevtsovaPsi t ε := by
  rw [shevtsovaPsi_eq_second_of_first_not_and_window hfirst hwindow]
  exact div_nonneg (one_sub_cos_nonneg (ε * t)) (sq_nonneg ε)

lemma shevtsovaPsi_eq_second_of_pos_and_window {t ε : ℝ}
    (hε : 0 < ε)
    (hwindow : shevtsovaTheta0 < ε * |t| ∧ ε * |t| ≤ 2 * Real.pi) :
    shevtsovaPsi t ε = (1 - Real.cos (ε * t)) / ε ^ 2 := by
  have hfirst : ¬ |t| ≤ shevtsovaTheta0 / ε := by
    intro hle
    have hmul :
        ε * |t| ≤ ε * (shevtsovaTheta0 / ε) :=
      mul_le_mul_of_nonneg_left hle hε.le
    have hle_theta : ε * |t| ≤ shevtsovaTheta0 := by
      simpa [mul_div_cancel₀ shevtsovaTheta0 hε.ne'] using hmul
    linarith
  exact shevtsovaPsi_eq_second_of_first_not_and_window hfirst hwindow

lemma abs_le_shevtsovaTheta0_div_of_mul_abs_le
    {t ε : ℝ} (hε : 0 < ε)
    (h : ε * |t| ≤ shevtsovaTheta0) :
    |t| ≤ shevtsovaTheta0 / ε := by
  rw [le_div_iff₀ hε]
  simpa [mul_comm] using h

lemma shevtsovaTheta0_lt_mul_abs_of_not_first
    {t ε : ℝ} (hε : 0 < ε)
    (hfirst : ¬ |t| ≤ shevtsovaTheta0 / ε) :
    shevtsovaTheta0 < ε * |t| := by
  by_contra hnot
  exact hfirst
    (abs_le_shevtsovaTheta0_div_of_mul_abs_le hε (not_lt.mp hnot))

lemma shevtsovaCosRatio_theta0_eq_half_sub_kappa_mul_theta0 :
    shevtsovaCosRatio shevtsovaTheta0 =
      1 / 2 - shevtsovaKappa * shevtsovaTheta0 := by
  rw [shevtsovaKappa_mul_theta0_eq]
  unfold shevtsovaCosRatio
  field_simp [shevtsovaTheta0_pos.ne']
  ring

lemma shevtsovaPsi_first_branch_eq_abs_sq_mul_linear {t ε : ℝ}
    (hfirst : |t| ≤ shevtsovaTheta0 / ε) :
    shevtsovaPsi t ε =
      |t| ^ 2 * (1 / 2 - shevtsovaKappa * ε * |t|) := by
  rw [shevtsovaPsi_eq_first_of_abs_le hfirst]
  have ht_sq : |t| ^ 2 = t ^ 2 := by
    rw [sq_abs]
  have ht_cube : |t| ^ 3 = t ^ 2 * |t| := by
    calc
      |t| ^ 3 = |t| ^ 2 * |t| := by ring
      _ = t ^ 2 * |t| := by rw [sq_abs]
  rw [ht_sq, ht_cube]
  ring

lemma shevtsovaPsi_first_branch_ge_sq_div_four {t ε : ℝ}
    (hfirst : |t| ≤ shevtsovaTheta0 / ε)
    (hsmall : shevtsovaKappa * ε * |t| ≤ 1 / 4) :
    t ^ 2 / 4 ≤ shevtsovaPsi t ε := by
  rw [shevtsovaPsi_first_branch_eq_abs_sq_mul_linear hfirst]
  have hlinear :
      (1 / 4 : ℝ) ≤ 1 / 2 - shevtsovaKappa * ε * |t| := by
    linarith
  have hscaled :
      |t| ^ 2 * (1 / 4 : ℝ) ≤
        |t| ^ 2 * (1 / 2 - shevtsovaKappa * ε * |t|) :=
    mul_le_mul_of_nonneg_left hlinear (sq_nonneg |t|)
  have hrewrite : |t| ^ 2 * (1 / 4 : ℝ) = t ^ 2 / 4 := by
    rw [sq_abs]
    ring
  rwa [hrewrite] at hscaled

lemma sqrt_one_sub_shevtsovaPsi_pow_le_exp_neg_sq_div_eight_of_first_branch
    {t ε : ℝ} {N : ℕ}
    (hfirst : |t| ≤ shevtsovaTheta0 / ε)
    (hsmall : shevtsovaKappa * ε * |t| ≤ 1 / 4) :
    (Real.sqrt (1 - shevtsovaPsi t ε)) ^ N ≤
      Real.exp (-((N : ℝ) * t ^ 2) / 8) := by
  have hlower :
      t ^ 2 / 4 ≤ shevtsovaPsi t ε :=
    shevtsovaPsi_first_branch_ge_sq_div_four
      (t := t) (ε := ε) hfirst hsmall
  have h :=
    real_sqrt_one_sub_pow_le_exp_neg_mul_of_ge
      (a := shevtsovaPsi t ε) (b := t ^ 2 / 4)
      hlower N
  convert h using 2
  ring

lemma sqrt_one_sub_shevtsovaPsi_pow_le_exp_neg_quarter_of_first_branch_scaled
    {N : ℕ} (hN : 0 < N) {t ε : ℝ}
    (hfirst :
      |Real.sqrt 2 * (t / Real.sqrt (N : ℝ))| ≤
        shevtsovaTheta0 / ε)
    (hsmall :
      shevtsovaKappa * ε *
        |Real.sqrt 2 * (t / Real.sqrt (N : ℝ))| ≤ 1 / 4) :
    (Real.sqrt
      (1 - shevtsovaPsi
        (Real.sqrt 2 * (t / Real.sqrt (N : ℝ))) ε)) ^ N ≤
      Real.exp (-(t ^ 2) / 4) := by
  have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hbase :=
    sqrt_one_sub_shevtsovaPsi_pow_le_exp_neg_sq_div_eight_of_first_branch
      (t := Real.sqrt 2 * (t / Real.sqrt (N : ℝ)))
      (ε := ε) (N := N) hfirst hsmall
  have harg :
      -((N : ℝ) *
          (Real.sqrt 2 * (t / Real.sqrt (N : ℝ))) ^ 2) / 8 =
        -(t ^ 2) / 4 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt hN_real.le]
    field_simp [hN_real.ne']
    ring
  simpa [harg] using hbase

lemma shevtsovaPsi_first_branch_antitone {t ε₁ ε₂ : ℝ}
    (hε : ε₁ ≤ ε₂)
    (hfirst₁ : |t| ≤ shevtsovaTheta0 / ε₁)
    (hfirst₂ : |t| ≤ shevtsovaTheta0 / ε₂) :
    shevtsovaPsi t ε₂ ≤ shevtsovaPsi t ε₁ := by
  have hψ₁ :=
    shevtsovaPsi_first_branch_eq_abs_sq_mul_linear
      (t := t) (ε := ε₁) hfirst₁
  have hψ₂ :=
    shevtsovaPsi_first_branch_eq_abs_sq_mul_linear
      (t := t) (ε := ε₂) hfirst₂
  have hmul :
      shevtsovaKappa * ε₁ * |t| ≤ shevtsovaKappa * ε₂ * |t| := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hε shevtsovaKappa_pos.le)
      (abs_nonneg t)
  have hlinear :
      1 / 2 - shevtsovaKappa * ε₂ * |t| ≤
        1 / 2 - shevtsovaKappa * ε₁ * |t| := by
    linarith
  have hscaled :
      |t| ^ 2 *
          (1 / 2 - shevtsovaKappa * ε₂ * |t|) ≤
        |t| ^ 2 *
          (1 / 2 - shevtsovaKappa * ε₁ * |t|) :=
    mul_le_mul_of_nonneg_left hlinear (sq_nonneg |t|)
  rwa [hψ₂, hψ₁]

lemma shevtsovaPsi_second_branch_eq_abs_sq_mul_cosRatio {t ε : ℝ}
    (hε : 0 < ε)
    (hwindow : shevtsovaTheta0 < ε * |t| ∧ ε * |t| ≤ 2 * Real.pi) :
    shevtsovaPsi t ε =
      |t| ^ 2 * shevtsovaCosRatio (ε * |t|) := by
  rw [shevtsovaPsi_eq_second_of_pos_and_window hε hwindow]
  unfold shevtsovaCosRatio
  have ht_abs_pos : 0 < |t| := by
    by_contra hnot
    have ht_abs_zero : |t| = 0 := le_antisymm (not_lt.mp hnot) (abs_nonneg t)
    nlinarith [hwindow.1, shevtsovaTheta0_pos]
  have hcos : Real.cos (ε * t) = Real.cos (ε * |t|) := by
    calc
      Real.cos (ε * t) = Real.cos |ε * t| := by
        rw [Real.cos_abs]
      _ = Real.cos (ε * |t|) := by
        rw [abs_mul, abs_of_pos hε]
  rw [hcos]
  field_simp [hε.ne', ht_abs_pos.ne']

lemma shevtsovaPsi_second_branch_antitone {t ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hε : ε₁ ≤ ε₂)
    (hwindow₁ :
      shevtsovaTheta0 < ε₁ * |t| ∧ ε₁ * |t| ≤ 2 * Real.pi)
    (hwindow₂ :
      shevtsovaTheta0 < ε₂ * |t| ∧ ε₂ * |t| ≤ 2 * Real.pi) :
    shevtsovaPsi t ε₂ ≤ shevtsovaPsi t ε₁ := by
  have hψ₁ :=
    shevtsovaPsi_second_branch_eq_abs_sq_mul_cosRatio
      (t := t) (ε := ε₁) hε₁ hwindow₁
  have hψ₂ :=
    shevtsovaPsi_second_branch_eq_abs_sq_mul_cosRatio
      (t := t) (ε := ε₂) hε₂ hwindow₂
  have hu₁_mem : ε₁ * |t| ∈ Set.Icc Real.pi (2 * Real.pi) := by
    exact ⟨shevtsovaTheta0_mem_Icc.1.trans hwindow₁.1.le,
      hwindow₁.2⟩
  have hu₂_mem : ε₂ * |t| ∈ Set.Icc Real.pi (2 * Real.pi) := by
    exact ⟨shevtsovaTheta0_mem_Icc.1.trans hwindow₂.1.le,
      hwindow₂.2⟩
  have hu_le : ε₁ * |t| ≤ ε₂ * |t| :=
    mul_le_mul_of_nonneg_right hε (abs_nonneg t)
  have hratio :
      shevtsovaCosRatio (ε₂ * |t|) ≤
        shevtsovaCosRatio (ε₁ * |t|) :=
    antitoneOn_shevtsovaCosRatio_Icc_pi_two_pi
      hu₁_mem hu₂_mem hu_le
  have hmul :
      |t| ^ 2 * shevtsovaCosRatio (ε₂ * |t|) ≤
        |t| ^ 2 * shevtsovaCosRatio (ε₁ * |t|) :=
    mul_le_mul_of_nonneg_left hratio (sq_nonneg |t|)
  rwa [hψ₂, hψ₁]

lemma shevtsovaPsi_second_branch_le_first_branch {t ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hfirst₁ : |t| ≤ shevtsovaTheta0 / ε₁)
    (hwindow₂ :
      shevtsovaTheta0 < ε₂ * |t| ∧ ε₂ * |t| ≤ 2 * Real.pi) :
    shevtsovaPsi t ε₂ ≤ shevtsovaPsi t ε₁ := by
  have hψ₁ :=
    shevtsovaPsi_first_branch_eq_abs_sq_mul_linear
      (t := t) (ε := ε₁) hfirst₁
  have hψ₂ :=
    shevtsovaPsi_second_branch_eq_abs_sq_mul_cosRatio
      (t := t) (ε := ε₂) hε₂ hwindow₂
  have hu₁_le :
      ε₁ * |t| ≤ shevtsovaTheta0 := by
    have hmul :
        ε₁ * |t| ≤ ε₁ * (shevtsovaTheta0 / ε₁) :=
      mul_le_mul_of_nonneg_left hfirst₁ hε₁.le
    simpa [mul_div_cancel₀ shevtsovaTheta0 hε₁.ne'] using hmul
  have hu₂_mem : ε₂ * |t| ∈ Set.Icc Real.pi (2 * Real.pi) := by
    exact ⟨shevtsovaTheta0_mem_Icc.1.trans hwindow₂.1.le,
      hwindow₂.2⟩
  have hratio :
      shevtsovaCosRatio (ε₂ * |t|) ≤
        shevtsovaCosRatio shevtsovaTheta0 := by
    exact antitoneOn_shevtsovaCosRatio_Icc_pi_two_pi
      shevtsovaTheta0_mem_Icc hu₂_mem hwindow₂.1.le
  have htheta_linear :
      1 / 2 - shevtsovaKappa * shevtsovaTheta0 ≤
        1 / 2 - shevtsovaKappa * ε₁ * |t| := by
    have hmul :
        shevtsovaKappa * (ε₁ * |t|) ≤
          shevtsovaKappa * shevtsovaTheta0 :=
      mul_le_mul_of_nonneg_left hu₁_le shevtsovaKappa_pos.le
    linarith
  have hlinear :
      shevtsovaCosRatio (ε₂ * |t|) ≤
        1 / 2 - shevtsovaKappa * ε₁ * |t| := by
    rw [shevtsovaCosRatio_theta0_eq_half_sub_kappa_mul_theta0] at hratio
    exact hratio.trans htheta_linear
  have hscaled :
      |t| ^ 2 * shevtsovaCosRatio (ε₂ * |t|) ≤
        |t| ^ 2 *
          (1 / 2 - shevtsovaKappa * ε₁ * |t|) :=
    mul_le_mul_of_nonneg_left hlinear (sq_nonneg |t|)
  rwa [hψ₂, hψ₁]

lemma shevtsovaPsi_first_nonneg {t ε : ℝ}
    (hε : 0 < ε) (hfirst : |t| ≤ shevtsovaTheta0 / ε) :
    0 ≤ shevtsovaPsi t ε := by
  rw [shevtsovaPsi_eq_first_of_abs_le hfirst]
  have hmul :
      ε * |t| ≤ ε * (shevtsovaTheta0 / ε) :=
    mul_le_mul_of_nonneg_left hfirst hε.le
  have hε_abs : ε * |t| ≤ shevtsovaTheta0 := by
    simpa [mul_div_cancel₀ shevtsovaTheta0 hε.ne'] using hmul
  have hκ_nonneg : 0 ≤ shevtsovaKappa := shevtsovaKappa_pos.le
  have hκmul :
      shevtsovaKappa * (ε * |t|) ≤
        shevtsovaKappa * shevtsovaTheta0 :=
    mul_le_mul_of_nonneg_left hε_abs hκ_nonneg
  have hbracket :
      0 ≤ (1 / 2 : ℝ) - shevtsovaKappa * ε * |t| := by
    nlinarith [hκmul, shevtsovaKappa_mul_theta0_le_half]
  have hsq : 0 ≤ |t| ^ 2 := sq_nonneg |t|
  have hprod :
      0 ≤ |t| ^ 2 *
        ((1 / 2 : ℝ) - shevtsovaKappa * ε * |t|) :=
    mul_nonneg hsq hbracket
  have hform :
      |t| ^ 2 * ((1 / 2 : ℝ) - shevtsovaKappa * ε * |t|) =
        t ^ 2 / 2 - shevtsovaKappa * ε * |t| ^ 3 := by
    have ht_sq : t ^ 2 = |t| ^ 2 := by
      rw [sq_abs]
    rw [ht_sq]
    ring_nf
  exact hform ▸ hprod

lemma shevtsovaPsi_nonneg_of_pos {t ε : ℝ} (hε : 0 < ε) :
    0 ≤ shevtsovaPsi t ε := by
  by_cases hfirst : |t| ≤ shevtsovaTheta0 / ε
  · exact shevtsovaPsi_first_nonneg hε hfirst
  · by_cases hsecond :
        shevtsovaTheta0 < ε * |t| ∧ ε * |t| ≤ 2 * Real.pi
    · exact shevtsovaPsi_second_nonneg hfirst hsecond
    · rw [shevtsovaPsi_eq_zero_of_not_first_not_second hfirst hsecond]

lemma shevtsovaPsi_antitone_epsilon {t ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hε : ε₁ ≤ ε₂) :
    shevtsovaPsi t ε₂ ≤ shevtsovaPsi t ε₁ := by
  by_cases hfirst₂ : |t| ≤ shevtsovaTheta0 / ε₂
  · have hdiv :
      shevtsovaTheta0 / ε₂ ≤ shevtsovaTheta0 / ε₁ := by
      have hrecip : 1 / ε₂ ≤ 1 / ε₁ :=
        one_div_le_one_div_of_le hε₁ hε
      calc
        shevtsovaTheta0 / ε₂ =
            shevtsovaTheta0 * (1 / ε₂) := by ring
        _ ≤ shevtsovaTheta0 * (1 / ε₁) :=
            mul_le_mul_of_nonneg_left hrecip shevtsovaTheta0_pos.le
        _ = shevtsovaTheta0 / ε₁ := by ring
    have hfirst₁ : |t| ≤ shevtsovaTheta0 / ε₁ :=
      hfirst₂.trans hdiv
    exact shevtsovaPsi_first_branch_antitone
      (t := t) (ε₁ := ε₁) (ε₂ := ε₂) hε hfirst₁ hfirst₂
  · by_cases hsecond₂ :
        shevtsovaTheta0 < ε₂ * |t| ∧ ε₂ * |t| ≤ 2 * Real.pi
    · by_cases hfirst₁ : |t| ≤ shevtsovaTheta0 / ε₁
      · exact shevtsovaPsi_second_branch_le_first_branch
          (t := t) (ε₁ := ε₁) (ε₂ := ε₂) hε₁ hε₂ hfirst₁ hsecond₂
      · have hsecond₁ :
          shevtsovaTheta0 < ε₁ * |t| ∧
            ε₁ * |t| ≤ 2 * Real.pi := by
          have hlt :
              shevtsovaTheta0 < ε₁ * |t| :=
            shevtsovaTheta0_lt_mul_abs_of_not_first hε₁ hfirst₁
          have hmul_le :
              ε₁ * |t| ≤ ε₂ * |t| :=
            mul_le_mul_of_nonneg_right hε (abs_nonneg t)
          exact ⟨hlt, hmul_le.trans hsecond₂.2⟩
        exact shevtsovaPsi_second_branch_antitone
          (t := t) (ε₁ := ε₁) (ε₂ := ε₂)
          hε₁ hε₂ hε hsecond₁ hsecond₂
    · rw [shevtsovaPsi_eq_zero_of_not_first_not_second hfirst₂ hsecond₂]
      exact shevtsovaPsi_nonneg_of_pos hε₁

/-- First-branch square-modulus estimate with the symmetrized third moment
replaced by the standard `2 sqrt 2 * β₃` bound. -/
lemma norm_charFun_sq_le_one_sub_shevtsovaPsi_two_sqrt_two_beta_of_first_branch
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hsecond : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    {t : ℝ}
    (hfirst :
      |Real.sqrt 2 * t| ≤ shevtsovaTheta0 /
        (2 * Real.sqrt 2 * ∫ x : ℝ, |x| ^ 3 ∂μ)) :
    ‖charFun μ t‖ ^ 2 ≤
      1 - shevtsovaPsi (Real.sqrt 2 * t)
        (2 * Real.sqrt 2 * ∫ x : ℝ, |x| ^ 3 ∂μ) := by
  let Y : ℝ × ℝ → ℝ := fun p => (p.1 - p.2) / Real.sqrt 2
  let βs : ℝ := ∫ p : ℝ × ℝ, |Y p| ^ 3 ∂(μ.prod μ)
  let β : ℝ := ∫ x : ℝ, |x| ^ 3 ∂μ
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hβ_ge_one : 1 ≤ β := by
    dsimp [β]
    exact one_le_integral_abs_cube_of_integral_sq_eq_one μ h3 hsecond
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ_ge_one
  have hE_pos : 0 < 2 * Real.sqrt 2 * β := by
    exact mul_pos (mul_pos (by norm_num) hsqrt_pos) hβ_pos
  have hY : AEMeasurable Y (μ.prod μ) := by
    dsimp [Y]
    fun_prop
  let ν : Measure ℝ := (μ.prod μ).map Y
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hY
  have h3Y : Integrable (fun p : ℝ × ℝ => |Y p| ^ 3) (μ.prod μ) := by
    dsimp [Y]
    exact integrable_abs_symmDiff_div_sqrt_two_cube_prod μ h3
  have h3ν : Integrable (fun x : ℝ => |x| ^ 3) ν := by
    have hgm :
        AEStronglyMeasurable (fun x : ℝ => |x| ^ 3) ν :=
      (by fun_prop : Measurable (fun x : ℝ => |x| ^ 3)).aestronglyMeasurable
    rw [integrable_map_measure hgm hY]
    exact h3Y
  have hsecondν : ∫ x : ℝ, x ^ 2 ∂ν = 1 := by
    dsimp [ν, Y]
    rw [integral_map hY]
    · exact integral_symmDiff_div_sqrt_two_sq_prod_eq_one μ h3 hmean hsecond
    · exact (by fun_prop :
        AEStronglyMeasurable (fun x : ℝ => x ^ 2) ((μ.prod μ).map Y))
  have hβs_eq :
      (∫ x : ℝ, |x| ^ 3 ∂ν) = βs := by
    dsimp [ν, βs]
    rw [integral_map hY]
    exact (by fun_prop :
      AEStronglyMeasurable (fun x : ℝ => |x| ^ 3) ((μ.prod μ).map Y))
  have hβs_ge_one : 1 ≤ βs := by
    have h :=
      one_le_integral_abs_cube_of_integral_sq_eq_one ν h3ν hsecondν
    rwa [hβs_eq] at h
  have hβs_pos : 0 < βs := lt_of_lt_of_le zero_lt_one hβs_ge_one
  have hβs_le : βs ≤ 2 * Real.sqrt 2 * β := by
    dsimp [βs, β, Y]
    exact integral_abs_symmDiff_div_sqrt_two_cube_prod_le μ h3
  have hdiv :
      shevtsovaTheta0 / (2 * Real.sqrt 2 * β) ≤
        shevtsovaTheta0 / βs := by
    have hrecip : 1 / (2 * Real.sqrt 2 * β) ≤ 1 / βs :=
      one_div_le_one_div_of_le hβs_pos hβs_le
    calc
      shevtsovaTheta0 / (2 * Real.sqrt 2 * β) =
          shevtsovaTheta0 * (1 / (2 * Real.sqrt 2 * β)) := by ring
      _ ≤ shevtsovaTheta0 * (1 / βs) :=
          mul_le_mul_of_nonneg_left hrecip shevtsovaTheta0_pos.le
      _ = shevtsovaTheta0 / βs := by ring
  have hfirstβs :
      |Real.sqrt 2 * t| ≤ shevtsovaTheta0 / βs :=
    hfirst.trans hdiv
  have hsymm :
      ‖charFun μ t‖ ^ 2 ≤
        1 - shevtsovaPsi (Real.sqrt 2 * t) βs := by
    dsimp [βs, Y] at hfirstβs ⊢
    exact
      norm_charFun_sq_le_one_sub_shevtsovaPsi_symmDiff_scaled_of_first_branch
        μ h3 hmean hsecond hfirstβs
  have hψ :
      shevtsovaPsi (Real.sqrt 2 * t) (2 * Real.sqrt 2 * β) ≤
        shevtsovaPsi (Real.sqrt 2 * t) βs :=
    shevtsovaPsi_antitone_epsilon hβs_pos hE_pos hβs_le
  have hrhs :
      1 - shevtsovaPsi (Real.sqrt 2 * t) βs ≤
        1 - shevtsovaPsi (Real.sqrt 2 * t) (2 * Real.sqrt 2 * β) := by
    linarith
  exact hsymm.trans hrhs

/-- HDP-hypotheses form of the first-branch Prawitz square-modulus estimate
for the standardized one-summand characteristic function. -/
lemma standardizedCharFun_norm_sq_le_one_sub_shevtsovaPsi_two_sqrt_two_beta_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ t : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (hfirst :
      |Real.sqrt 2 * t| ≤ shevtsovaTheta0 /
        (2 * Real.sqrt 2 * berryEsseenRho X P m σ)) :
    ‖charFun (P.map (fun ω => (X 0 ω - m) / σ)) t‖ ^ 2 ≤
      1 - shevtsovaPsi (Real.sqrt 2 * t)
        (2 * Real.sqrt 2 * berryEsseenRho X P m σ) := by
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hstd_meas :
      AEMeasurable (fun ω => (X 0 ω - m) / σ) P :=
    ((hBE.aemeasurable 0).sub aemeasurable_const).div_const σ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hstd_meas
  have hX0_int : Integrable (X 0) P :=
    integrable_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hX0_mlp : MemLp (X 0) 2 P :=
    memLp_two_of_integrable_centered_abs_cube
      (P := P) (Y := X 0) (m := m)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have h3ν :
      Integrable (fun x : ℝ => |x| ^ 3) ν := by
    dsimp [ν]
    exact integrable_standardizedLaw_abs_cube
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.third_abs_integrable
  have hmeanν : ∫ x : ℝ, x ∂ν = 0 := by
    dsimp [ν]
    exact integral_standardizedLaw_id_eq_zero
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_int (hBE.mean_eq 0)
      hBE.sigma_pos.ne'
  have hsecondν : ∫ x : ℝ, x ^ 2 ∂ν = 1 := by
    dsimp [ν]
    exact integral_standardizedLaw_sq_eq_one
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hX0_mlp (hBE.mean_eq 0)
      (hBE.variance_eq 0) hBE.sigma_pos.ne'
  have hβν :
      (∫ x : ℝ, |x| ^ 3 ∂ν) = berryEsseenRho X P m σ := by
    dsimp [ν]
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  have hfirstν :
      |Real.sqrt 2 * t| ≤ shevtsovaTheta0 /
        (2 * Real.sqrt 2 * ∫ x : ℝ, |x| ^ 3 ∂ν) := by
    simpa [hβν] using hfirst
  have h :=
    norm_charFun_sq_le_one_sub_shevtsovaPsi_two_sqrt_two_beta_of_first_branch
      ν h3ν hmeanν hsecondν hfirstν
  simpa [ν, hβν] using h

lemma complex_norm_le_sqrt_of_norm_sq_le {z : ℂ} {a : ℝ}
    (h : ‖z‖ ^ 2 ≤ a) :
    ‖z‖ ≤ Real.sqrt a :=
  Real.le_sqrt_of_sq_le h

/-- Square-root form of the first-branch Prawitz estimate for the
standardized one-summand characteristic function. -/
lemma standardizedCharFun_norm_le_sqrt_one_sub_shevtsovaPsi_two_sqrt_two_beta_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ t : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (hfirst :
      |Real.sqrt 2 * t| ≤ shevtsovaTheta0 /
        (2 * Real.sqrt 2 * berryEsseenRho X P m σ)) :
    ‖charFun (P.map (fun ω => (X 0 ω - m) / σ)) t‖ ≤
      Real.sqrt
        (1 - shevtsovaPsi (Real.sqrt 2 * t)
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ)) := by
  exact complex_norm_le_sqrt_of_norm_sq_le
    (standardizedCharFun_norm_sq_le_one_sub_shevtsovaPsi_two_sqrt_two_beta_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE hfirst)

/-- Pointwise first-branch Prawitz decay for Shevtsova's normalized-sum
characteristic function.  This keeps the exact `ψ` expression instead of
collapsing it to the older Durrett Gaussian envelope. -/
lemma shevtsovaFnAbs_le_sqrt_one_sub_shevtsovaPsi_pow_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) {t : ℝ}
    (hfirst :
      |Real.sqrt 2 * (t / Real.sqrt (N : ℝ))| ≤
        shevtsovaTheta0 /
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ)) :
    shevtsovaFnAbs P X m σ N t ≤
      (Real.sqrt
        (1 - shevtsovaPsi
          (Real.sqrt 2 * (t / Real.sqrt (N : ℝ)))
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N := by
  have hbase :=
    standardizedCharFun_norm_le_sqrt_one_sub_shevtsovaPsi_two_sqrt_two_beta_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE
      (t := t / Real.sqrt (N : ℝ)) hfirst
  have hpow :
      ‖charFun (P.map (fun ω => (X 0 ω - m) / σ))
          (t / Real.sqrt (N : ℝ))‖ ^ N ≤
        (Real.sqrt
          (1 - shevtsovaPsi
            (Real.sqrt 2 * (t / Real.sqrt (N : ℝ)))
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N :=
    pow_le_pow_left₀ (norm_nonneg _) hbase N
  calc
    shevtsovaFnAbs P X m σ N t
        = ‖charFun (P.map (fun ω => (X 0 ω - m) / σ))
            (t / Real.sqrt (N : ℝ))‖ ^ N := by
          exact shevtsovaFnAbs_eq_norm_power_of_hypotheses
            (P := P) (X := X) (m := m) (σ := σ) hBE N t
    _ ≤
        (Real.sqrt
          (1 - shevtsovaPsi
            (Real.sqrt 2 * (t / Real.sqrt (N : ℝ)))
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N := hpow

/-- The same pointwise `f_n` estimate as
`shevtsovaFnAbs_le_sqrt_one_sub_shevtsovaPsi_pow_of_hypotheses`, rewritten in
Shevtsova's normalized notation with the Lyapunov fraction. -/
lemma shevtsovaFnAbs_le_sqrt_one_sub_shevtsovaPsi_lyapunov_pow_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) {t : ℝ}
    (hfirst :
      |Real.sqrt 2 * (t / Real.sqrt (N : ℝ))| ≤
        shevtsovaTheta0 /
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ)) :
    shevtsovaFnAbs P X m σ N t ≤
      (Real.sqrt
        (1 - shevtsovaPsi (Real.sqrt 2 * t)
          (2 * Real.sqrt 2 *
            shevtsovaLyapunovFraction (berryEsseenRho X P m σ) N) /
            (N : ℝ))) ^ N := by
  have hbase :=
    shevtsovaFnAbs_le_sqrt_one_sub_shevtsovaPsi_pow_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N
      (t := t) hfirst
  have hψ :=
    shevtsovaPsi_two_sqrt_two_scale_eq_div_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE (N := N) hN (t := t)
  simpa [hψ] using hbase

/-- Pointwise exponential decay for the normalized-sum characteristic function
under the first-branch Prawitz condition and the small-`ψ` cutoff. -/
lemma shevtsovaFnAbs_le_exp_neg_quarter_from_sqrtPsi_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) {t : ℝ}
    (hfirst :
      |Real.sqrt 2 * (t / Real.sqrt (N : ℝ))| ≤
        shevtsovaTheta0 /
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ))
    (hsmall :
      shevtsovaKappa * (2 * Real.sqrt 2 * berryEsseenRho X P m σ) *
        |Real.sqrt 2 * (t / Real.sqrt (N : ℝ))| ≤ 1 / 4) :
    shevtsovaFnAbs P X m σ N t ≤ Real.exp (-(t ^ 2) / 4) := by
  have hFnSqrt :=
    shevtsovaFnAbs_le_sqrt_one_sub_shevtsovaPsi_pow_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N
      (t := t) hfirst
  have hSqrtExp :
      (Real.sqrt
        (1 - shevtsovaPsi
          (Real.sqrt 2 * (t / Real.sqrt (N : ℝ)))
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N ≤
        Real.exp (-(t ^ 2) / 4) :=
    sqrt_one_sub_shevtsovaPsi_pow_le_exp_neg_quarter_of_first_branch_scaled
      (N := N) hN (t := t)
      (ε := 2 * Real.sqrt 2 * berryEsseenRho X P m σ)
      hfirst hsmall
  exact hFnSqrt.trans hSqrtExp

lemma shevtsovaPsi_le_one_sub_cos_div_sq_of_pos
    {t ε : ℝ} (hε : 0 < ε) :
    shevtsovaPsi t ε ≤ (1 - Real.cos (ε * t)) / ε ^ 2 := by
  by_cases hfirst : |t| ≤ shevtsovaTheta0 / ε
  · rw [shevtsovaPsi_eq_first_of_abs_le hfirst]
    have hmul :
        ε * |t| ≤ shevtsovaTheta0 := by
      have hscaled :
          ε * |t| ≤ ε * (shevtsovaTheta0 / ε) :=
        mul_le_mul_of_nonneg_left hfirst hε.le
      simpa [mul_div_cancel₀ shevtsovaTheta0 hε.ne'] using hscaled
    have habs_le_two_pi : |ε * t| ≤ 2 * Real.pi := by
      rw [abs_mul, abs_of_pos hε]
      exact hmul.trans shevtsovaTheta0_mem_Icc.2
    have hcos :=
      real_cos_remainder_le_shevtsovaKappa_mul_abs_cube_of_abs_le_two_pi
        (x := ε * t) habs_le_two_pi
    have hgap :
        (ε * t) ^ 2 / 2 - shevtsovaKappa * |ε * t| ^ 3 ≤
          1 - Real.cos (ε * t) := by
      nlinarith
    have hrewrite :
        (ε * t) ^ 2 / 2 - shevtsovaKappa * |ε * t| ^ 3 =
          ε ^ 2 *
            (t ^ 2 / 2 - shevtsovaKappa * ε * |t| ^ 3) := by
      rw [abs_mul, abs_of_pos hε]
      ring
    rw [hrewrite] at hgap
    rw [le_div_iff₀ (sq_pos_of_pos hε)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hgap
  · by_cases hsecond :
        shevtsovaTheta0 < ε * |t| ∧
          ε * |t| ≤ 2 * Real.pi
    · rw [shevtsovaPsi_eq_second_of_first_not_and_window
        hfirst hsecond]
    · rw [shevtsovaPsi_eq_zero_of_not_first_not_second
        hfirst hsecond]
      exact div_nonneg (one_sub_cos_nonneg (ε * t)) (sq_nonneg ε)

lemma shevtsovaPsi_le_sq_div_two_of_pos {t ε : ℝ} (hε : 0 < ε) :
    shevtsovaPsi t ε ≤ t ^ 2 / 2 := by
  by_cases hfirst : |t| ≤ shevtsovaTheta0 / ε
  · rw [shevtsovaPsi_eq_first_of_abs_le hfirst]
    have hterm :
        0 ≤ shevtsovaKappa * ε * |t| ^ 3 :=
      mul_nonneg (mul_nonneg shevtsovaKappa_pos.le hε.le)
        (pow_nonneg (abs_nonneg t) 3)
    nlinarith
  · by_cases hsecond :
        shevtsovaTheta0 < ε * |t| ∧ ε * |t| ≤ 2 * Real.pi
    · rw [shevtsovaPsi_eq_second_of_first_not_and_window hfirst hsecond]
      have hcos := one_sub_cos_le_sq_div_two (ε * t)
      have hden : 0 ≤ ε ^ 2 := sq_nonneg ε
      calc
        (1 - Real.cos (ε * t)) / ε ^ 2
            ≤ ((ε * t) ^ 2 / 2) / ε ^ 2 :=
              div_le_div_of_nonneg_right hcos hden
        _ = t ^ 2 / 2 := by
              field_simp [hε.ne']
    · rw [shevtsovaPsi_eq_zero_of_not_first_not_second hfirst hsecond]
      positivity

/-- Prawitz's smoothing bound functional, in the notation used by
Shevtsova.  The main Durrett/Feller chain in this file uses the Polya/Esseen
functional above; this definition gives the sharper Prawitz route a checked
local target over the same normalized-sum law. -/
def shevtsovaPrawitzSmoothingBound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T : ℝ) : ℝ :=
  2 * (∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t‖ *
          shevtsovaRn P X m σ N (T * t) ∂volume) +
  2 * (∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ *
          shevtsovaFnAbs P X m σ N (T * t) ∂volume) +
  2 * (∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t -
            shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ *
          Real.exp (-(T ^ 2 * t ^ 2) / 2) ∂volume) +
  (1 / Real.pi) *
    (∫ t in Set.Ioi t0,
      Real.exp (-(T ^ 2 * t ^ 2) / 2) / t ∂volume)

def shevtsovaPrawitzRnTerm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T : ℝ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) t0,
    ‖shevtsovaPrawitzKernel t‖ *
      shevtsovaRn P X m σ N (T * t) ∂volume

def shevtsovaPrawitzFnTerm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T : ℝ) : ℝ :=
  ∫ t in Set.Icc t0 1,
    ‖shevtsovaPrawitzKernel t‖ *
      shevtsovaFnAbs P X m σ N (T * t) ∂volume

def shevtsovaPrawitzGaussianKernelTerm (t0 T : ℝ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) t0,
    ‖shevtsovaPrawitzKernel t -
        shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ *
      Real.exp (-(T ^ 2 * t ^ 2) / 2) ∂volume

def shevtsovaPrawitzGaussianTailTerm (t0 T : ℝ) : ℝ :=
  ∫ t in Set.Ioi t0,
    Real.exp (-(T ^ 2 * t ^ 2) / 2) / t ∂volume

lemma shevtsovaPrawitzSmoothingBound_eq_terms
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T : ℝ) :
    shevtsovaPrawitzSmoothingBound P X m σ N t0 T =
      2 * shevtsovaPrawitzRnTerm P X m σ N t0 T +
      2 * shevtsovaPrawitzFnTerm P X m σ N t0 T +
      2 * shevtsovaPrawitzGaussianKernelTerm t0 T +
      (1 / Real.pi) * shevtsovaPrawitzGaussianTailTerm t0 T := by
  rfl

/-- The harmless unit-modulus oscillation appearing in the positive-frequency
Prawitz inversion integrals. -/
def shevtsovaPrawitzOscillation (x T t : ℝ) : ℂ :=
  Complex.exp (((-(T * t * x)) : ℝ) * Complex.I)

lemma norm_shevtsovaPrawitzOscillation (x T t : ℝ) :
    ‖shevtsovaPrawitzOscillation x T t‖ = 1 := by
  simpa [shevtsovaPrawitzOscillation] using
    Complex.norm_exp_ofReal_mul_I (-(T * t * x))

lemma norm_charFun_standardNormalMeasure (u : ℝ) :
    ‖charFun standardNormalMeasure u‖ = Real.exp (-(u ^ 2) / 2) := by
  rw [shevtsovaNormalCharFun_eq, Complex.norm_exp_ofReal]
  congr 1
  ring

/-- Oscillatory Prawitz integral over the low-frequency `r_n` part. -/
def shevtsovaPrawitzRnOscillatoryIntegral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T x : ℝ) : ℂ :=
  ∫ t in Set.Icc (0 : ℝ) t0,
    shevtsovaPrawitzKernel t *
      shevtsovaPrawitzOscillation x T t *
      (shevtsovaFn P X m σ N (T * t) -
        charFun standardNormalMeasure (T * t)) ∂volume

/-- Oscillatory Prawitz integral over the upper-frequency `f_n` part. -/
def shevtsovaPrawitzFnOscillatoryIntegral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T x : ℝ) : ℂ :=
  ∫ t in Set.Icc t0 1,
    shevtsovaPrawitzKernel t *
      shevtsovaPrawitzOscillation x T t *
      shevtsovaFn P X m σ N (T * t) ∂volume

/-- Oscillatory normal correction on `[0,t0]`, where Prawitz's kernel is
compared to the CDF inversion kernel `i/(2πt)`. -/
def shevtsovaPrawitzGaussianKernelOscillatoryIntegral
    (t0 T x : ℝ) : ℂ :=
  ∫ t in Set.Icc (0 : ℝ) t0,
    (shevtsovaPrawitzKernel t -
        shevtsovaIMul ((2 * Real.pi * t)⁻¹)) *
      shevtsovaPrawitzOscillation x T t *
      charFun standardNormalMeasure (T * t) ∂volume

/-- Oscillatory normal tail from the ideal CDF inversion kernel. -/
def shevtsovaPrawitzGaussianTailOscillatoryIntegral
    (t0 T x : ℝ) : ℂ :=
  ∫ t in Set.Ioi t0,
    shevtsovaIMul ((2 * Real.pi * t)⁻¹) *
      shevtsovaPrawitzOscillation x T t *
      charFun standardNormalMeasure (T * t) ∂volume

/-- The complex oscillatory error controlled by Prawitz's four scalar terms.
The later CDF-inversion step should identify CDF errors with the real part of
this expression; this definition isolates the purely analytic decomposition. -/
def shevtsovaPrawitzOscillatoryErrorIntegral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T x : ℝ) : ℂ :=
  (2 : ℝ) • shevtsovaPrawitzRnOscillatoryIntegral P X m σ N t0 T x +
  (2 : ℝ) • shevtsovaPrawitzFnOscillatoryIntegral P X m σ N t0 T x +
  (2 : ℝ) • shevtsovaPrawitzGaussianKernelOscillatoryIntegral t0 T x -
  (2 : ℝ) • shevtsovaPrawitzGaussianTailOscillatoryIntegral t0 T x

lemma norm_shevtsovaPrawitzRnOscillatoryIntegral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T x : ℝ) :
    ‖shevtsovaPrawitzRnOscillatoryIntegral P X m σ N t0 T x‖ ≤
      shevtsovaPrawitzRnTerm P X m σ N t0 T := by
  unfold shevtsovaPrawitzRnOscillatoryIntegral
    shevtsovaPrawitzRnTerm
  calc
    ‖∫ t in Set.Icc (0 : ℝ) t0,
        shevtsovaPrawitzKernel t *
          shevtsovaPrawitzOscillation x T t *
          (shevtsovaFn P X m σ N (T * t) -
            charFun standardNormalMeasure (T * t)) ∂volume‖
        ≤ ∫ t in Set.Icc (0 : ℝ) t0,
            ‖shevtsovaPrawitzKernel t *
              shevtsovaPrawitzOscillation x T t *
              (shevtsovaFn P X m σ N (T * t) -
                charFun standardNormalMeasure (T * t))‖ ∂volume :=
          norm_integral_le_integral_norm _
    _ = ∫ t in Set.Icc (0 : ℝ) t0,
          ‖shevtsovaPrawitzKernel t‖ *
            shevtsovaRn P X m σ N (T * t) ∂volume := by
          refine integral_congr_ae ?_
          exact Eventually.of_forall fun t => by
            change ‖shevtsovaPrawitzKernel t *
                shevtsovaPrawitzOscillation x T t *
                (shevtsovaFn P X m σ N (T * t) -
                  charFun standardNormalMeasure (T * t))‖ =
              ‖shevtsovaPrawitzKernel t‖ *
                shevtsovaRn P X m σ N (T * t)
            rw [norm_mul, norm_mul,
              norm_shevtsovaPrawitzOscillation]
            simp [shevtsovaRn, mul_comm]

lemma norm_shevtsovaPrawitzFnOscillatoryIntegral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T x : ℝ) :
    ‖shevtsovaPrawitzFnOscillatoryIntegral P X m σ N t0 T x‖ ≤
      shevtsovaPrawitzFnTerm P X m σ N t0 T := by
  unfold shevtsovaPrawitzFnOscillatoryIntegral
    shevtsovaPrawitzFnTerm
  calc
    ‖∫ t in Set.Icc t0 1,
        shevtsovaPrawitzKernel t *
          shevtsovaPrawitzOscillation x T t *
          shevtsovaFn P X m σ N (T * t) ∂volume‖
        ≤ ∫ t in Set.Icc t0 1,
            ‖shevtsovaPrawitzKernel t *
              shevtsovaPrawitzOscillation x T t *
              shevtsovaFn P X m σ N (T * t)‖ ∂volume :=
          norm_integral_le_integral_norm _
    _ = ∫ t in Set.Icc t0 1,
          ‖shevtsovaPrawitzKernel t‖ *
            shevtsovaFnAbs P X m σ N (T * t) ∂volume := by
          refine integral_congr_ae ?_
          exact Eventually.of_forall fun t => by
            change ‖shevtsovaPrawitzKernel t *
                shevtsovaPrawitzOscillation x T t *
                shevtsovaFn P X m σ N (T * t)‖ =
              ‖shevtsovaPrawitzKernel t‖ *
                shevtsovaFnAbs P X m σ N (T * t)
            rw [norm_mul, norm_mul,
              norm_shevtsovaPrawitzOscillation]
            simp [shevtsovaFnAbs, mul_comm]

lemma norm_shevtsovaPrawitzGaussianKernelOscillatoryIntegral_le
    (t0 T x : ℝ) :
    ‖shevtsovaPrawitzGaussianKernelOscillatoryIntegral t0 T x‖ ≤
      shevtsovaPrawitzGaussianKernelTerm t0 T := by
  unfold shevtsovaPrawitzGaussianKernelOscillatoryIntegral
    shevtsovaPrawitzGaussianKernelTerm
  calc
    ‖∫ t in Set.Icc (0 : ℝ) t0,
        (shevtsovaPrawitzKernel t -
            shevtsovaIMul ((2 * Real.pi * t)⁻¹)) *
          shevtsovaPrawitzOscillation x T t *
          charFun standardNormalMeasure (T * t) ∂volume‖
        ≤ ∫ t in Set.Icc (0 : ℝ) t0,
            ‖(shevtsovaPrawitzKernel t -
                shevtsovaIMul ((2 * Real.pi * t)⁻¹)) *
              shevtsovaPrawitzOscillation x T t *
              charFun standardNormalMeasure (T * t)‖ ∂volume :=
          norm_integral_le_integral_norm _
    _ = ∫ t in Set.Icc (0 : ℝ) t0,
          ‖shevtsovaPrawitzKernel t -
              shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ *
            Real.exp (-(T ^ 2 * t ^ 2) / 2) ∂volume := by
          refine integral_congr_ae ?_
          exact Eventually.of_forall fun t => by
            change ‖(shevtsovaPrawitzKernel t -
                  shevtsovaIMul ((2 * Real.pi * t)⁻¹)) *
                shevtsovaPrawitzOscillation x T t *
                charFun standardNormalMeasure (T * t)‖ =
              ‖shevtsovaPrawitzKernel t -
                  shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ *
                Real.exp (-(T ^ 2 * t ^ 2) / 2)
            rw [norm_mul, norm_mul,
              norm_shevtsovaPrawitzOscillation,
              norm_charFun_standardNormalMeasure]
            ring_nf

lemma norm_shevtsovaPrawitzGaussianTailOscillatoryIntegral_le
    {t0 T x : ℝ} (ht0 : 0 < t0) :
    ‖shevtsovaPrawitzGaussianTailOscillatoryIntegral t0 T x‖ ≤
      (1 / (2 * Real.pi)) * shevtsovaPrawitzGaussianTailTerm t0 T := by
  unfold shevtsovaPrawitzGaussianTailOscillatoryIntegral
    shevtsovaPrawitzGaussianTailTerm
  calc
    ‖∫ t in Set.Ioi t0,
        shevtsovaIMul ((2 * Real.pi * t)⁻¹) *
          shevtsovaPrawitzOscillation x T t *
          charFun standardNormalMeasure (T * t) ∂volume‖
        ≤ ∫ t in Set.Ioi t0,
            ‖shevtsovaIMul ((2 * Real.pi * t)⁻¹) *
              shevtsovaPrawitzOscillation x T t *
              charFun standardNormalMeasure (T * t)‖ ∂volume :=
          norm_integral_le_integral_norm _
    _ = ∫ t in Set.Ioi t0,
          (1 / (2 * Real.pi)) *
            (Real.exp (-(T ^ 2 * t ^ 2) / 2) / t) ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht_pos : 0 < t := ht0.trans ht
          have hden_pos : 0 < 2 * Real.pi * t := by positivity
          rw [norm_mul, norm_mul, norm_shevtsovaPrawitzOscillation,
            norm_charFun_standardNormalMeasure, norm_shevtsovaIMul,
            abs_of_pos (inv_pos.mpr hden_pos)]
          field_simp [hden_pos.ne', ht_pos.ne', Real.pi_ne_zero]
    _ = (1 / (2 * Real.pi)) *
          (∫ t in Set.Ioi t0,
            Real.exp (-(T ^ 2 * t ^ 2) / 2) / t ∂volume) := by
          rw [integral_const_mul]

lemma norm_shevtsovaPrawitzOscillatoryErrorIntegral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) {t0 T x : ℝ}
    (ht0 : 0 < t0) :
    ‖shevtsovaPrawitzOscillatoryErrorIntegral P X m σ N t0 T x‖ ≤
      shevtsovaPrawitzSmoothingBound P X m σ N t0 T := by
  let I₁ :=
    shevtsovaPrawitzRnOscillatoryIntegral P X m σ N t0 T x
  let I₂ :=
    shevtsovaPrawitzFnOscillatoryIntegral P X m σ N t0 T x
  let I₃ :=
    shevtsovaPrawitzGaussianKernelOscillatoryIntegral t0 T x
  let I₄ :=
    shevtsovaPrawitzGaussianTailOscillatoryIntegral t0 T x
  have htri :
      ‖(2 : ℝ) • I₁ + (2 : ℝ) • I₂ + (2 : ℝ) • I₃ -
          (2 : ℝ) • I₄‖ ≤
        ‖(2 : ℝ) • I₁‖ + ‖(2 : ℝ) • I₂‖ +
          ‖(2 : ℝ) • I₃‖ + ‖(2 : ℝ) • I₄‖ := by
    calc
      ‖(2 : ℝ) • I₁ + (2 : ℝ) • I₂ + (2 : ℝ) • I₃ -
          (2 : ℝ) • I₄‖
          ≤ ‖(2 : ℝ) • I₁ + (2 : ℝ) • I₂ +
              (2 : ℝ) • I₃‖ + ‖(2 : ℝ) • I₄‖ :=
            norm_sub_le _ _
      _ ≤ (‖(2 : ℝ) • I₁ + (2 : ℝ) • I₂‖ +
              ‖(2 : ℝ) • I₃‖) + ‖(2 : ℝ) • I₄‖ :=
            by
              have habc :
                  ‖(2 : ℝ) • I₁ + (2 : ℝ) • I₂ + (2 : ℝ) • I₃‖ ≤
                    ‖(2 : ℝ) • I₁ + (2 : ℝ) • I₂‖ +
                      ‖(2 : ℝ) • I₃‖ :=
                norm_add_le _ _
              linarith
      _ ≤ ((‖(2 : ℝ) • I₁‖ + ‖(2 : ℝ) • I₂‖) +
              ‖(2 : ℝ) • I₃‖) + ‖(2 : ℝ) • I₄‖ :=
            by
              have hab :
                  ‖(2 : ℝ) • I₁ + (2 : ℝ) • I₂‖ ≤
                    ‖(2 : ℝ) • I₁‖ + ‖(2 : ℝ) • I₂‖ :=
                norm_add_le _ _
              linarith
      _ = ‖(2 : ℝ) • I₁‖ + ‖(2 : ℝ) • I₂‖ +
          ‖(2 : ℝ) • I₃‖ + ‖(2 : ℝ) • I₄‖ := by ring
  have h₁ :
      ‖(2 : ℝ) • I₁‖ ≤
        2 * shevtsovaPrawitzRnTerm P X m σ N t0 T := by
    calc
      ‖(2 : ℝ) • I₁‖ = 2 * ‖I₁‖ := by
        simp
      _ ≤ 2 * shevtsovaPrawitzRnTerm P X m σ N t0 T :=
        mul_le_mul_of_nonneg_left
          (norm_shevtsovaPrawitzRnOscillatoryIntegral_le
            (P := P) (X := X) (m := m) (σ := σ) N t0 T x)
          (by norm_num)
  have h₂ :
      ‖(2 : ℝ) • I₂‖ ≤
        2 * shevtsovaPrawitzFnTerm P X m σ N t0 T := by
    calc
      ‖(2 : ℝ) • I₂‖ = 2 * ‖I₂‖ := by
        simp
      _ ≤ 2 * shevtsovaPrawitzFnTerm P X m σ N t0 T :=
        mul_le_mul_of_nonneg_left
          (norm_shevtsovaPrawitzFnOscillatoryIntegral_le
            (P := P) (X := X) (m := m) (σ := σ) N t0 T x)
          (by norm_num)
  have h₃ :
      ‖(2 : ℝ) • I₃‖ ≤
        2 * shevtsovaPrawitzGaussianKernelTerm t0 T := by
    calc
      ‖(2 : ℝ) • I₃‖ = 2 * ‖I₃‖ := by
        simp
      _ ≤ 2 * shevtsovaPrawitzGaussianKernelTerm t0 T :=
        mul_le_mul_of_nonneg_left
          (norm_shevtsovaPrawitzGaussianKernelOscillatoryIntegral_le
            t0 T x)
          (by norm_num)
  have h₄ :
      ‖(2 : ℝ) • I₄‖ ≤
        (1 / Real.pi) * shevtsovaPrawitzGaussianTailTerm t0 T := by
    calc
      ‖(2 : ℝ) • I₄‖ = 2 * ‖I₄‖ := by
        simp
      _ ≤ 2 * ((1 / (2 * Real.pi)) *
          shevtsovaPrawitzGaussianTailTerm t0 T) :=
        mul_le_mul_of_nonneg_left
          (norm_shevtsovaPrawitzGaussianTailOscillatoryIntegral_le
            (t0 := t0) (T := T) (x := x) ht0)
          (by norm_num)
      _ = (1 / Real.pi) * shevtsovaPrawitzGaussianTailTerm t0 T := by
        field_simp [Real.pi_ne_zero]
  calc
    ‖shevtsovaPrawitzOscillatoryErrorIntegral P X m σ N t0 T x‖
        = ‖(2 : ℝ) • I₁ + (2 : ℝ) • I₂ + (2 : ℝ) • I₃ -
            (2 : ℝ) • I₄‖ := by
          rfl
    _ ≤ ‖(2 : ℝ) • I₁‖ + ‖(2 : ℝ) • I₂‖ +
          ‖(2 : ℝ) • I₃‖ + ‖(2 : ℝ) • I₄‖ := htri
    _ ≤ 2 * shevtsovaPrawitzRnTerm P X m σ N t0 T +
          2 * shevtsovaPrawitzFnTerm P X m σ N t0 T +
          2 * shevtsovaPrawitzGaussianKernelTerm t0 T +
          (1 / Real.pi) * shevtsovaPrawitzGaussianTailTerm t0 T := by
          nlinarith [h₁, h₂, h₃, h₄]
    _ = shevtsovaPrawitzSmoothingBound P X m σ N t0 T := by
          rw [shevtsovaPrawitzSmoothingBound_eq_terms]

/-- The real part of the oscillatory Prawitz error is controlled by the same
four scalar certificate terms. -/
lemma abs_re_shevtsovaPrawitzOscillatoryErrorIntegral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) {t0 T x : ℝ}
    (ht0 : 0 < t0) :
    |(shevtsovaPrawitzOscillatoryErrorIntegral P X m σ N t0 T x).re| ≤
      shevtsovaPrawitzSmoothingBound P X m σ N t0 T :=
  (Complex.abs_re_le_norm _).trans
    (norm_shevtsovaPrawitzOscillatoryErrorIntegral_le
      (P := P) (X := X) (m := m) (σ := σ) N ht0)

/-- A sufficient pointwise Prawitz inversion target: identify each CDF
difference with the real part of the oscillatory error integral.  Prawitz's
Lemma 1 is an inequality, not necessarily this exact pointwise representation;
the lemmas below record that this stronger formula would immediately imply
`Δ_n ≤ shevtsovaPrawitzSmoothingBound`. -/
def shevtsovaPrawitzPointwiseInversionFormula
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T : ℝ) : Prop :=
  ∀ x : ℝ,
    measureCDFDiff (shevtsovaNormalizedSumLaw P X m σ N)
        standardNormalMeasure x =
      (shevtsovaPrawitzOscillatoryErrorIntegral P X m σ N t0 T x).re

lemma measureCDFErrorLE_of_shevtsovaPrawitzPointwiseInversionFormula
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) {t0 T : ℝ}
    (ht0 : 0 < t0)
    (hInv :
      shevtsovaPrawitzPointwiseInversionFormula P X m σ N t0 T) :
    measureCDFErrorLE (shevtsovaNormalizedSumLaw P X m σ N)
      standardNormalMeasure
      (shevtsovaPrawitzSmoothingBound P X m σ N t0 T) := by
  intro x
  change
    |measureCDFDiff (shevtsovaNormalizedSumLaw P X m σ N)
        standardNormalMeasure x| ≤
      shevtsovaPrawitzSmoothingBound P X m σ N t0 T
  rw [hInv x]
  exact
    abs_re_shevtsovaPrawitzOscillatoryErrorIntegral_le
      (P := P) (X := X) (m := m) (σ := σ) N
      (t0 := t0) (T := T) (x := x) ht0

lemma shevtsovaDelta_le_of_shevtsovaPrawitzPointwiseInversionFormula
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) {N : ℕ}
    {t0 T : ℝ} (ht0 : 0 < t0)
    (hInv :
      shevtsovaPrawitzPointwiseInversionFormula P X m σ N t0 T) :
    shevtsovaDelta P X m σ N ≤
      shevtsovaPrawitzSmoothingBound P X m σ N t0 T :=
  shevtsovaDelta_le_of_measureCDFErrorLE
    (P := P) (X := X) (m := m) (σ := σ) hBE
    (measureCDFErrorLE_of_shevtsovaPrawitzPointwiseInversionFormula
      (P := P) (X := X) (m := m) (σ := σ) N ht0 hInv)

lemma shevtsovaPrawitzRnTerm_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T : ℝ) :
    0 ≤ shevtsovaPrawitzRnTerm P X m σ N t0 T := by
  unfold shevtsovaPrawitzRnTerm
  exact integral_nonneg fun t =>
    mul_nonneg (norm_nonneg _)
      (shevtsovaRn_nonneg P X m σ N (T * t))

lemma shevtsovaPrawitzFnTerm_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) (t0 T : ℝ) :
    0 ≤ shevtsovaPrawitzFnTerm P X m σ N t0 T := by
  unfold shevtsovaPrawitzFnTerm
  exact integral_nonneg fun t =>
    mul_nonneg (norm_nonneg _)
      (shevtsovaFnAbs_nonneg P X m σ N (T * t))

lemma shevtsovaPrawitzGaussianKernelTerm_nonneg (t0 T : ℝ) :
    0 ≤ shevtsovaPrawitzGaussianKernelTerm t0 T := by
  unfold shevtsovaPrawitzGaussianKernelTerm
  exact integral_nonneg fun t =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

lemma shevtsovaPrawitzGaussianTailTerm_nonneg
    {t0 T : ℝ} (ht0 : 0 < t0) :
    0 ≤ shevtsovaPrawitzGaussianTailTerm t0 T := by
  unfold shevtsovaPrawitzGaussianTailTerm
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact div_nonneg (Real.exp_pos _).le (ht0.trans ht).le

lemma integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    (∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2)) =
      (2 * b)⁻¹ := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (1 : ℝ)) (b := b)
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (-1 : ℝ) < 1) hb
  convert h using 1
  · refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    simp [Real.rpow_one]
  · norm_num
    rw [Real.rpow_neg_one]

lemma integral_Ioi_mul_exp_neg_T_sq_div_two {T : ℝ} (hT : T ≠ 0) :
    (∫ x in Set.Ioi (0 : ℝ),
      x * Real.exp (-(T ^ 2 * x ^ 2) / 2)) = (T ^ 2)⁻¹ := by
  have hb : 0 < T ^ 2 / 2 := by positivity
  have h := integral_Ioi_mul_exp_neg_mul_sq (b := T ^ 2 / 2) hb
  convert h using 1
  · refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    ring_nf
  · ring_nf

lemma shevtsovaPrawitzGaussianTail_pointwise_le_quadratic_majorant
    {t0 T t : ℝ} (ht0 : 0 < t0) (ht : t ∈ Set.Ioi t0) :
    Real.exp (-(T ^ 2 * t ^ 2) / 2) / t ≤
      (1 / t0 ^ 2) *
        (t * Real.exp (-(T ^ 2 * t ^ 2) / 2)) := by
  have htt0 : t0 < t := ht
  have ht_pos : 0 < t := ht0.trans htt0
  have ht0sq_pos : 0 < t0 ^ 2 := sq_pos_of_pos ht0
  have hrecip : 1 / t ≤ t / t0 ^ 2 := by
    field_simp [ht_pos.ne', ht0sq_pos.ne']
    nlinarith [ht0.le, htt0.le, sq_nonneg (t - t0)]
  have hexp_nonneg : 0 ≤ Real.exp (-(T ^ 2 * t ^ 2) / 2) :=
    (Real.exp_pos _).le
  calc
    Real.exp (-(T ^ 2 * t ^ 2) / 2) / t =
        (1 / t) * Real.exp (-(T ^ 2 * t ^ 2) / 2) := by ring
    _ ≤ (t / t0 ^ 2) * Real.exp (-(T ^ 2 * t ^ 2) / 2) :=
      mul_le_mul_of_nonneg_right hrecip hexp_nonneg
    _ = (1 / t0 ^ 2) *
        (t * Real.exp (-(T ^ 2 * t ^ 2) / 2)) := by ring

lemma integrableOn_shevtsovaPrawitzGaussianTailMajorant
    {t0 T : ℝ} (hT : T ≠ 0) :
    IntegrableOn
      (fun t : ℝ => (1 / t0 ^ 2) *
        (t * Real.exp (-(T ^ 2 * t ^ 2) / 2)))
      (Set.Ioi t0) := by
  have hb : 0 < T ^ 2 / 2 := by positivity
  have hglobal : Integrable
      (fun t : ℝ => t * Real.exp (-(T ^ 2 * t ^ 2) / 2)) := by
    have h := integrable_mul_exp_neg_mul_sq (b := T ^ 2 / 2) hb
    convert h using 1
    ext t
    ring_nf
  exact hglobal.integrableOn.const_mul (1 / t0 ^ 2)

lemma integrableOn_shevtsovaPrawitzGaussianTailTerm_of_pos
    {t0 T : ℝ} (ht0 : 0 < t0) (hT : T ≠ 0) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(T ^ 2 * t ^ 2) / 2) / t)
      (Set.Ioi t0) := by
  have hBoundInt :
      IntegrableOn
        (fun t : ℝ => (1 / t0 ^ 2) *
          (t * Real.exp (-(T ^ 2 * t ^ 2) / 2)))
        (Set.Ioi t0) :=
    integrableOn_shevtsovaPrawitzGaussianTailMajorant
      (t0 := t0) (T := T) hT
  refine hBoundInt.mono' ?_ ?_
  · have hmeas :
        Measurable
          (fun t : ℝ => Real.exp (-((T ^ 2) * t ^ 2 / 2)) / t) := by
      exact (((((measurable_const :
          Measurable (fun _ : ℝ => T ^ 2)).mul
        (measurable_id.pow_const 2)).div_const 2).neg).exp).div
        measurable_id
    convert hmeas.aestronglyMeasurable using 1
    ext t
    ring_nf
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htt0 : t0 < t := ht
    have ht_pos : 0 < t := ht0.trans htt0
    have hf_nonneg : 0 ≤ Real.exp (-(T ^ 2 * t ^ 2) / 2) / t :=
      div_nonneg (Real.exp_pos _).le ht_pos.le
    rw [Real.norm_eq_abs, abs_of_nonneg hf_nonneg]
    exact
      shevtsovaPrawitzGaussianTail_pointwise_le_quadratic_majorant
        (T := T) ht0 ht

lemma shevtsovaPrawitzGaussianTailTerm_le_inv_sq_mul_inv_sq
    {t0 T : ℝ} (ht0 : 0 < t0) (hT : T ≠ 0) :
    shevtsovaPrawitzGaussianTailTerm t0 T ≤
      (1 / t0 ^ 2) * (T ^ 2)⁻¹ := by
  have hTailInt :
      IntegrableOn
        (fun t : ℝ => Real.exp (-(T ^ 2 * t ^ 2) / 2) / t)
        (Set.Ioi t0) :=
    integrableOn_shevtsovaPrawitzGaussianTailTerm_of_pos
      (t0 := t0) (T := T) ht0 hT
  have hMajorantInt_t0 :
      IntegrableOn
        (fun t : ℝ => (1 / t0 ^ 2) *
          (t * Real.exp (-(T ^ 2 * t ^ 2) / 2)))
        (Set.Ioi t0) :=
    integrableOn_shevtsovaPrawitzGaussianTailMajorant
      (t0 := t0) (T := T) hT
  have hCompare :
      shevtsovaPrawitzGaussianTailTerm t0 T ≤
        ∫ t in Set.Ioi t0,
          (1 / t0 ^ 2) *
            (t * Real.exp (-(T ^ 2 * t ^ 2) / 2)) ∂volume := by
    unfold shevtsovaPrawitzGaussianTailTerm
    refine setIntegral_mono_on hTailInt hMajorantInt_t0 measurableSet_Ioi ?_
    intro t ht
    exact
      shevtsovaPrawitzGaussianTail_pointwise_le_quadratic_majorant
        (T := T) ht0 ht
  have hMajorantInt_0 :
      IntegrableOn
        (fun t : ℝ => (1 / t0 ^ 2) *
          (t * Real.exp (-(T ^ 2 * t ^ 2) / 2)))
        (Set.Ioi (0 : ℝ)) :=
    by
      have hb : 0 < T ^ 2 / 2 := by positivity
      have hglobal : Integrable
          (fun t : ℝ => t * Real.exp (-(T ^ 2 * t ^ 2) / 2)) := by
        have h := integrable_mul_exp_neg_mul_sq (b := T ^ 2 / 2) hb
        convert h using 1
        ext t
        ring_nf
      exact hglobal.integrableOn.const_mul (1 / t0 ^ 2)
  have hSet :
      (∫ t in Set.Ioi t0,
        (1 / t0 ^ 2) *
          (t * Real.exp (-(T ^ 2 * t ^ 2) / 2)) ∂volume) ≤
        ∫ t in Set.Ioi (0 : ℝ),
          (1 / t0 ^ 2) *
            (t * Real.exp (-(T ^ 2 * t ^ 2) / 2)) ∂volume := by
    refine setIntegral_mono_set hMajorantInt_0 ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := ht
      positivity
    · exact Eventually.of_forall fun t ht => (ht0.trans ht : 0 < t)
  have hEval :
      (∫ t in Set.Ioi (0 : ℝ),
        (1 / t0 ^ 2) *
          (t * Real.exp (-(T ^ 2 * t ^ 2) / 2)) ∂volume) =
        (1 / t0 ^ 2) * (T ^ 2)⁻¹ := by
    rw [integral_const_mul, integral_Ioi_mul_exp_neg_T_sq_div_two hT]
  exact hCompare.trans (hSet.trans_eq hEval)

lemma one_div_pi_mul_shevtsovaPrawitzGaussianTailTerm_le
    {t0 T : ℝ} (ht0 : 0 < t0) (hT : T ≠ 0) :
    (1 / Real.pi) * shevtsovaPrawitzGaussianTailTerm t0 T ≤
      (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzGaussianTailTerm_le_inv_sq_mul_inv_sq
      (t0 := t0) (T := T) ht0 hT)
    (by positivity)

lemma measurable_shevtsovaPrawitzGaussianKernelIntegrand (T : ℝ) :
    Measurable
      (fun t : ℝ =>
        ‖shevtsovaPrawitzKernel t -
            shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ *
          Real.exp (-(T ^ 2 * t ^ 2) / 2)) := by
  have hIMul :
      Measurable
        (fun t : ℝ => shevtsovaIMul ((2 * Real.pi * t)⁻¹)) := by
    unfold shevtsovaIMul
    exact (((measurable_const.mul measurable_id).inv).complex_ofReal.mul_const
      Complex.I)
  have hnorm :
      Measurable
        (fun t : ℝ =>
          ‖shevtsovaPrawitzKernel t -
              shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖) :=
    (measurable_shevtsovaPrawitzKernel.sub hIMul).norm
  have hexp :
      Measurable
        (fun t : ℝ => Real.exp (-((T ^ 2) * t ^ 2 / 2))) := by
    exact ((((measurable_const : Measurable (fun _ : ℝ => T ^ 2)).mul
      (measurable_id.pow_const 2)).div_const 2).neg).exp
  have h :
      Measurable
        (fun t : ℝ =>
          ‖shevtsovaPrawitzKernel t -
              shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ *
            Real.exp (-((T ^ 2) * t ^ 2 / 2))) :=
    hnorm.mul hexp
  convert h using 1
  ext t
  ring_nf

lemma integrableOn_shevtsovaPrawitzGaussianKernelIntegrand_of_bound
    {t0 T C : ℝ} (hC : 0 ≤ C)
    (hBound :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t -
            shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ ≤ C) :
    IntegrableOn
      (fun t : ℝ =>
        ‖shevtsovaPrawitzKernel t -
            shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ *
          Real.exp (-(T ^ 2 * t ^ 2) / 2))
      (Set.Icc (0 : ℝ) t0) := by
  have hIcc_ne_top : volume (Set.Icc (0 : ℝ) t0) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hConst : IntegrableOn (fun _ : ℝ => C) (Set.Icc (0 : ℝ) t0) :=
    integrableOn_const hIcc_ne_top
  refine hConst.mono' ?_ ?_
  · exact (measurable_shevtsovaPrawitzGaussianKernelIntegrand T).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs]
    have hnonneg :
        0 ≤
          ‖shevtsovaPrawitzKernel t -
              shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ *
            Real.exp (-(T ^ 2 * t ^ 2) / 2) := by
      positivity
    rw [abs_of_nonneg hnonneg]
    exact
      (mul_le_mul_of_nonneg_right (hBound t ht)
        (Real.exp_pos _).le).trans
        (by
          simpa using
            mul_le_of_le_one_right hC
              (Real.exp_le_one_iff.mpr
                (by nlinarith [sq_nonneg T, sq_nonneg t])))

lemma shevtsovaPrawitzGaussianKernelTerm_le_const_mul
    {t0 T C : ℝ} (h0t : 0 ≤ t0) (hC : 0 ≤ C)
    (hBound :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t -
            shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ ≤ C) :
    shevtsovaPrawitzGaussianKernelTerm t0 T ≤ C * t0 := by
  have hConst : IntegrableOn (fun _ : ℝ => C) (Set.Icc (0 : ℝ) t0) := by
    have hIcc_ne_top : volume (Set.Icc (0 : ℝ) t0) ≠ ∞ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    exact integrableOn_const hIcc_ne_top
  have hInt :
      IntegrableOn
        (fun t : ℝ =>
          ‖shevtsovaPrawitzKernel t -
              shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ *
            Real.exp (-(T ^ 2 * t ^ 2) / 2))
        (Set.Icc (0 : ℝ) t0) :=
    integrableOn_shevtsovaPrawitzGaussianKernelIntegrand_of_bound
      (t0 := t0) (T := T) (C := C) hC hBound
  unfold shevtsovaPrawitzGaussianKernelTerm
  have hMono :
      (∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t -
            shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ *
          Real.exp (-(T ^ 2 * t ^ 2) / 2) ∂volume) ≤
        ∫ t in Set.Icc (0 : ℝ) t0, C ∂volume := by
    refine setIntegral_mono_on hInt hConst measurableSet_Icc ?_
    intro t ht
    exact
      (mul_le_mul_of_nonneg_right (hBound t ht)
        (Real.exp_pos _).le).trans
        (by
          simpa using
            mul_le_of_le_one_right hC
              (Real.exp_le_one_iff.mpr
                (by nlinarith [sq_nonneg T, sq_nonneg t])))
  have hEval :
      (∫ t in Set.Icc (0 : ℝ) t0, C ∂volume) = C * t0 := by
    rw [integral_const]
    simp [Real.volume_real_Icc_of_le h0t, smul_eq_mul]
    ring
  exact hMono.trans_eq hEval

lemma two_mul_shevtsovaPrawitzGaussianKernelTerm_le_two_mul_const_mul
    {t0 T C : ℝ} (h0t : 0 ≤ t0) (hC : 0 ≤ C)
    (hBound :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t -
            shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ ≤ C) :
    2 * shevtsovaPrawitzGaussianKernelTerm t0 T ≤
      2 * (C * t0) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzGaussianKernelTerm_le_const_mul
      (t0 := t0) (T := T) (C := C) h0t hC hBound)
    (by norm_num)

lemma shevtsovaPrawitzGaussianKernelTerm_le_three_halves_mul
    {t0 T : ℝ} (h0t : 0 ≤ t0) (ht0_le : t0 ≤ 1 / 2) :
    shevtsovaPrawitzGaussianKernelTerm t0 T ≤ (3 / 2) * t0 := by
  refine shevtsovaPrawitzGaussianKernelTerm_le_const_mul
    (t0 := t0) (T := T) (C := 3 / 2) h0t (by norm_num) ?_
  intro t ht
  exact
    shevtsovaPrawitzKernel_sub_IMul_norm_le_three_halves_of_mem_Icc_zero_half
      (t := t) ⟨ht.1, ht.2.trans ht0_le⟩

lemma two_mul_shevtsovaPrawitzGaussianKernelTerm_le_three_mul
    {t0 T : ℝ} (h0t : 0 ≤ t0) (ht0_le : t0 ≤ 1 / 2) :
    2 * shevtsovaPrawitzGaussianKernelTerm t0 T ≤ 3 * t0 := by
  have h :=
    shevtsovaPrawitzGaussianKernelTerm_le_three_halves_mul
      (t0 := t0) (T := T) h0t ht0_le
  nlinarith

lemma integrableOn_shevtsovaPrawitzDurrettMajorant_of_kernel_abs_mul_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (n : ℕ) (t0 T C : ℝ)
    (hKernel :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        |t| * ‖shevtsovaPrawitzKernel t‖ ≤ C) :
    IntegrableOn
      (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
        (|T * t| *
          berryEsseenDurrettFourierBound
            (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)))
      (Set.Icc (0 : ℝ) t0) := by
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hBoundInt :
      IntegrableOn
        (fun t : ℝ => (|T| * C) *
          berryEsseenDurrettFourierBound ν n (T * t))
        (Set.Icc (0 : ℝ) t0) := by
    exact
      ((continuous_const.mul
        ((continuous_berryEsseenDurrettFourierBound ν n).comp
          (continuous_const.mul continuous_id))).integrableOn_Icc)
  change Integrable
    (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
      (|T * t| * berryEsseenDurrettFourierBound ν n (T * t)))
    (volume.restrict (Set.Icc (0 : ℝ) t0))
  change Integrable
    (fun t : ℝ => (|T| * C) *
      berryEsseenDurrettFourierBound ν n (T * t))
    (volume.restrict (Set.Icc (0 : ℝ) t0)) at hBoundInt
  refine hBoundInt.mono' ?_ ?_
  · have hAbs : Measurable (fun t : ℝ => |T * t|) := by fun_prop
    have hB :
        Measurable (fun t : ℝ =>
          berryEsseenDurrettFourierBound ν n (T * t)) :=
      ((continuous_berryEsseenDurrettFourierBound ν n).comp
        (continuous_const.mul continuous_id)).measurable
    exact (measurable_shevtsovaPrawitzKernel_norm.mul
      (hAbs.mul hB)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hB_nonneg :
        0 ≤ berryEsseenDurrettFourierBound ν n (T * t) :=
      berryEsseenDurrettFourierBound_nonneg ν n (T * t)
    have hmajor_nonneg :
        0 ≤ ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| * berryEsseenDurrettFourierBound ν n (T * t)) := by
      exact mul_nonneg (norm_nonneg _)
        (mul_nonneg (abs_nonneg _) hB_nonneg)
    rw [Real.norm_eq_abs, abs_of_nonneg hmajor_nonneg]
    calc
      ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| * berryEsseenDurrettFourierBound ν n (T * t))
          = |T| * (|t| * ‖shevtsovaPrawitzKernel t‖) *
              berryEsseenDurrettFourierBound ν n (T * t) := by
        rw [abs_mul]
        ring
      _ ≤ |T| * C * berryEsseenDurrettFourierBound ν n (T * t) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hKernel t ht) (abs_nonneg T))
          hB_nonneg
      _ = (|T| * C) *
            berryEsseenDurrettFourierBound ν n (T * t) := by
        ring

lemma integrableOn_shevtsovaPrawitzDurrettMajorant_of_t0_le_half
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (n : ℕ) (t0 T : ℝ)
    (ht0 : t0 ≤ 1 / 2) :
    IntegrableOn
      (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
        (|T * t| *
          berryEsseenDurrettFourierBound
            (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)))
      (Set.Icc (0 : ℝ) t0) := by
  exact
    integrableOn_shevtsovaPrawitzDurrettMajorant_of_kernel_abs_mul_le
      (P := P) (X := X) (m := m) (σ := σ) n t0 T 1
      (fun t ht =>
        shevtsovaPrawitzKernel_abs_mul_norm_le_one_of_mem_Icc_zero_half
          ⟨ht.1, ht.2.trans ht0⟩)

lemma integrableOn_shevtsovaPrawitzRn_durrettMajorant_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) (t0 T : ℝ)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3)
    (hMajorant :
      IntegrableOn
        (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| *
            berryEsseenDurrettFourierBound
              (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)))
        (Set.Icc (0 : ℝ) t0)) :
    IntegrableOn
      (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
        shevtsovaRn P X m σ (n + 1) (T * t))
      (Set.Icc (0 : ℝ) t0) := by
  change Integrable
    (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
      shevtsovaRn P X m σ (n + 1) (T * t))
    (volume.restrict (Set.Icc (0 : ℝ) t0))
  change Integrable
    (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
      (|T * t| *
        berryEsseenDurrettFourierBound
          (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)))
    (volume.restrict (Set.Icc (0 : ℝ) t0)) at hMajorant
  refine hMajorant.mono' ?_ ?_
  · exact (measurable_shevtsovaPrawitzKernel_norm.mul
      (((continuous_shevtsovaRn_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE (n + 1)).comp
          (continuous_const.mul continuous_id)).measurable)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (norm_nonneg (shevtsovaPrawitzKernel t))
        (shevtsovaRn_nonneg P X m σ (n + 1) (T * t)))]
    exact mul_le_mul_of_nonneg_left
      (shevtsovaRn_le_abs_mul_durrett_bound_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE hn
        (t := T * t) (hWindow t ht) (hSmall t ht))
      (norm_nonneg (shevtsovaPrawitzKernel t))

lemma shevtsovaPrawitzRnTerm_le_durrettIntegral_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) (t0 T : ℝ)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3)
    (hMajorant :
      IntegrableOn
        (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| *
            berryEsseenDurrettFourierBound
              (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)))
        (Set.Icc (0 : ℝ) t0)) :
    shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      ∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| *
            berryEsseenDurrettFourierBound
              (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)) ∂volume := by
  have hLeft :=
    integrableOn_shevtsovaPrawitzRn_durrettMajorant_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T hWindow hSmall hMajorant
  unfold shevtsovaPrawitzRnTerm
  refine setIntegral_mono_on hLeft hMajorant measurableSet_Icc ?_
  intro t ht
  exact mul_le_mul_of_nonneg_left
    (shevtsovaRn_le_abs_mul_durrett_bound_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE hn
      (t := T * t) (hWindow t ht) (hSmall t ht))
    (norm_nonneg (shevtsovaPrawitzKernel t))

lemma two_mul_shevtsovaPrawitzRnTerm_le_two_mul_durrettIntegral_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) (t0 T : ℝ)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3)
    (hMajorant :
      IntegrableOn
        (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| *
            berryEsseenDurrettFourierBound
              (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)))
        (Set.Icc (0 : ℝ) t0)) :
    2 * shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      2 * (∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| *
            berryEsseenDurrettFourierBound
              (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)) ∂volume) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzRnTerm_le_durrettIntegral_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T hWindow hSmall hMajorant)
    (by norm_num)

lemma shevtsovaPrawitzRnTerm_le_durrettIntegral_of_kernel_abs_mul_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) (t0 T C : ℝ)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3)
    (hKernel :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        |t| * ‖shevtsovaPrawitzKernel t‖ ≤ C) :
    shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      ∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| *
            berryEsseenDurrettFourierBound
              (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)) ∂volume := by
  have hMajorant :=
    integrableOn_shevtsovaPrawitzDurrettMajorant_of_kernel_abs_mul_le
      (P := P) (X := X) (m := m) (σ := σ) n t0 T C hKernel
  exact
    shevtsovaPrawitzRnTerm_le_durrettIntegral_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T hWindow hSmall hMajorant

lemma two_mul_shevtsovaPrawitzRnTerm_le_two_mul_durrettIntegral_of_kernel_abs_mul_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) (t0 T C : ℝ)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3)
    (hKernel :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        |t| * ‖shevtsovaPrawitzKernel t‖ ≤ C) :
    2 * shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      2 * (∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| *
            berryEsseenDurrettFourierBound
              (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)) ∂volume) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzRnTerm_le_durrettIntegral_of_kernel_abs_mul_le
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T C hWindow hSmall hKernel)
    (by norm_num)

lemma shevtsovaPrawitzRnTerm_le_durrettIntegral_of_t0_le_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) (t0 T : ℝ)
    (ht0 : t0 ≤ 1 / 2)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      ∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| *
            berryEsseenDurrettFourierBound
              (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)) ∂volume := by
  have hMajorant :=
    integrableOn_shevtsovaPrawitzDurrettMajorant_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ) n t0 T ht0
  exact
    shevtsovaPrawitzRnTerm_le_durrettIntegral_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T hWindow hSmall hMajorant

lemma two_mul_shevtsovaPrawitzRnTerm_le_two_mul_durrettIntegral_of_t0_le_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) (t0 T : ℝ)
    (ht0 : t0 ≤ 1 / 2)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    2 * shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      2 * (∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| *
            berryEsseenDurrettFourierBound
              (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)) ∂volume) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzRnTerm_le_durrettIntegral_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T ht0 hWindow hSmall)
    (by norm_num)

lemma integral_univ_abs_mul_berryEsseenDurrettFourierBound_comp_eq
    (μ : Measure ℝ) (n : ℕ) {T : ℝ} (hT : T ≠ 0) :
    (∫ t : ℝ,
        |T| * berryEsseenDurrettFourierBound μ n (T * t)) =
      ∫ u : ℝ, berryEsseenDurrettFourierBound μ n u := by
  have hcomp :
      (∫ t : ℝ, berryEsseenDurrettFourierBound μ n (T * t)) =
        |T⁻¹| * ∫ u : ℝ, berryEsseenDurrettFourierBound μ n u := by
    simpa [smul_eq_mul] using
      (Measure.integral_comp_mul_left
        (g := fun u : ℝ => berryEsseenDurrettFourierBound μ n u) T)
  rw [integral_const_mul, hcomp, abs_inv]
  have hT_abs : |T| ≠ 0 := abs_ne_zero.mpr hT
  rw [← mul_assoc, mul_inv_cancel₀ hT_abs, one_mul]

lemma integral_Icc_abs_mul_berryEsseenDurrettFourierBound_comp_le_integral_univ
    (μ : Measure ℝ) (n : ℕ) (t0 T : ℝ) :
    (∫ t in Set.Icc (0 : ℝ) t0,
        |T| * berryEsseenDurrettFourierBound μ n (T * t) ∂volume) ≤
      ∫ u : ℝ, berryEsseenDurrettFourierBound μ n u := by
  by_cases hT : T = 0
  · subst T
    have hnonneg :
        0 ≤ ∫ u : ℝ, berryEsseenDurrettFourierBound μ n u :=
      integral_nonneg fun u => berryEsseenDurrettFourierBound_nonneg μ n u
    simpa using hnonneg
  · have hScaledInt :
        Integrable
          (fun t : ℝ =>
            |T| * berryEsseenDurrettFourierBound μ n (T * t)) :=
      ((integrable_berryEsseenDurrettFourierBound μ n).comp_mul_left' hT).const_mul |T|
    have hSet :
        (∫ t in Set.Icc (0 : ℝ) t0,
            |T| * berryEsseenDurrettFourierBound μ n (T * t) ∂volume) ≤
          ∫ t : ℝ,
            |T| * berryEsseenDurrettFourierBound μ n (T * t) := by
      conv_rhs => rw [← setIntegral_univ]
      exact setIntegral_mono_set hScaledInt.integrableOn
        (Eventually.of_forall fun t =>
          mul_nonneg (abs_nonneg T)
            (berryEsseenDurrettFourierBound_nonneg μ n (T * t)))
        (Eventually.of_forall fun t _ht => Set.mem_univ t)
    exact hSet.trans_eq
      (integral_univ_abs_mul_berryEsseenDurrettFourierBound_comp_eq
        μ n hT)

lemma shevtsovaPrawitzDurrettIntegral_le_scaledDurrettIntegral_of_t0_le_half
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (n : ℕ) (t0 T : ℝ)
    (ht0 : t0 ≤ 1 / 2) :
    (∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| *
            berryEsseenDurrettFourierBound
              (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t)) ∂volume) ≤
      ∫ t in Set.Icc (0 : ℝ) t0,
        |T| *
          berryEsseenDurrettFourierBound
            (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t) ∂volume := by
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hLeft :
      IntegrableOn
        (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| *
            berryEsseenDurrettFourierBound ν n (T * t)))
        (Set.Icc (0 : ℝ) t0) := by
    exact
      integrableOn_shevtsovaPrawitzDurrettMajorant_of_t0_le_half
        (P := P) (X := X) (m := m) (σ := σ) n t0 T ht0
  have hRight :
      IntegrableOn
        (fun t : ℝ => |T| *
          berryEsseenDurrettFourierBound ν n (T * t))
        (Set.Icc (0 : ℝ) t0) := by
    exact
      (continuous_const.mul
        ((continuous_berryEsseenDurrettFourierBound ν n).comp
          (continuous_const.mul continuous_id))).integrableOn_Icc
  change
    (∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t‖ *
          (|T * t| * berryEsseenDurrettFourierBound ν n (T * t))
          ∂volume) ≤
      ∫ t in Set.Icc (0 : ℝ) t0,
        |T| * berryEsseenDurrettFourierBound ν n (T * t) ∂volume
  refine setIntegral_mono_on hLeft hRight measurableSet_Icc ?_
  intro t ht
  have hB_nonneg :
      0 ≤ berryEsseenDurrettFourierBound ν n (T * t) :=
    berryEsseenDurrettFourierBound_nonneg ν n (T * t)
  calc
    ‖shevtsovaPrawitzKernel t‖ *
        (|T * t| * berryEsseenDurrettFourierBound ν n (T * t))
        = |T| * (|t| * ‖shevtsovaPrawitzKernel t‖) *
            berryEsseenDurrettFourierBound ν n (T * t) := by
      rw [abs_mul]
      ring
    _ ≤ |T| * 1 * berryEsseenDurrettFourierBound ν n (T * t) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (shevtsovaPrawitzKernel_abs_mul_norm_le_one_of_mem_Icc_zero_half
            ⟨ht.1, ht.2.trans ht0⟩)
          (abs_nonneg T))
        hB_nonneg
    _ = |T| * berryEsseenDurrettFourierBound ν n (T * t) := by ring

lemma shevtsovaPrawitzRnTerm_le_scaledDurrettIntegral_of_t0_le_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) (t0 T : ℝ)
    (ht0 : t0 ≤ 1 / 2)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      ∫ t in Set.Icc (0 : ℝ) t0,
        |T| *
          berryEsseenDurrettFourierBound
            (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t) ∂volume := by
  exact
    (shevtsovaPrawitzRnTerm_le_durrettIntegral_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T ht0 hWindow hSmall).trans
      (shevtsovaPrawitzDurrettIntegral_le_scaledDurrettIntegral_of_t0_le_half
        (P := P) (X := X) (m := m) (σ := σ) n t0 T ht0)

lemma two_mul_shevtsovaPrawitzRnTerm_le_two_mul_scaledDurrettIntegral_of_t0_le_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) (t0 T : ℝ)
    (ht0 : t0 ≤ 1 / 2)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    2 * shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      2 * (∫ t in Set.Icc (0 : ℝ) t0,
        |T| *
          berryEsseenDurrettFourierBound
            (P.map (fun ω => (X 0 ω - m) / σ)) n (T * t) ∂volume) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzRnTerm_le_scaledDurrettIntegral_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T ht0 hWindow hSmall)
    (by norm_num)

lemma shevtsovaPrawitzRnTerm_le_durrettRate_of_t0_le_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) (t0 T : ℝ)
    (ht0 : t0 ≤ 1 / 2)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      (6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hFirst :
      shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
        ∫ t in Set.Icc (0 : ℝ) t0,
          |T| * berryEsseenDurrettFourierBound ν n (T * t) ∂volume :=
    shevtsovaPrawitzRnTerm_le_scaledDurrettIntegral_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T ht0 hWindow hSmall
  have hScaled :
      (∫ t in Set.Icc (0 : ℝ) t0,
          |T| * berryEsseenDurrettFourierBound ν n (T * t) ∂volume) ≤
        ∫ u : ℝ, berryEsseenDurrettFourierBound ν n u :=
    integral_Icc_abs_mul_berryEsseenDurrettFourierBound_comp_le_integral_univ
      ν n t0 T
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂ν = berryEsseenRho X P m σ := by
    dsimp [ν]
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  calc
    shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T
        ≤ ∫ t in Set.Icc (0 : ℝ) t0,
          |T| * berryEsseenDurrettFourierBound ν n (T * t) ∂volume := hFirst
    _ ≤ ∫ u : ℝ, berryEsseenDurrettFourierBound ν n u := hScaled
    _ ≤ (6 / 5) * (∫ x : ℝ, |x| ^ 3 ∂ν) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) :=
      integral_berryEsseenDurrettFourierBound_le ν n
    _ = (6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ) := by
      rw [hM]

lemma two_mul_shevtsovaPrawitzRnTerm_le_two_mul_durrettRate_of_t0_le_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) (t0 T : ℝ)
    (ht0 : t0 ≤ 1 / 2)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    2 * shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      2 * ((6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ)) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzRnTerm_le_durrettRate_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T ht0 hWindow hSmall)
    (by norm_num)

lemma berryEsseenDurrettFourierBound_le_polynomial
    (μ : Measure ℝ) (n : ℕ) (t : ℝ) :
    berryEsseenDurrettFourierBound μ n t ≤
      (1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ)) := by
  have hM : 0 ≤ ∫ x, |x| ^ 3 ∂μ := integral_abs_cube_nonneg μ
  have hN_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr hN_pos
  have hbase_nonneg :
      0 ≤
        (1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |t| ^ 2 /
            Real.sqrt ((n + 1 : ℕ) : ℝ) +
          |t| ^ 3 / (8 * ((n + 1 : ℕ) : ℝ)) := by
    positivity
  unfold berryEsseenDurrettFourierBound
  exact mul_le_of_le_one_right hbase_nonneg
    (Real.exp_le_one_iff.mpr
      (show -(1 / 4 : ℝ) * t ^ 2 ≤ 0 by
        nlinarith [sq_nonneg t]))

lemma integral_Icc_zero_sq_eq {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in Set.Icc (0 : ℝ) a, t ^ 2 ∂volume) = a ^ 3 / 3 := by
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (μ := volume)
    (f := fun t : ℝ => t ^ 2) ha]
  rw [integral_pow]
  norm_num

lemma integral_Icc_zero_cube_eq {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in Set.Icc (0 : ℝ) a, t ^ 3 ∂volume) = a ^ 4 / 4 := by
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (μ := volume)
    (f := fun t : ℝ => t ^ 3) ha]
  rw [integral_pow]
  norm_num

lemma integral_Icc_abs_mul_berryEsseenDurrettFourierBound_comp_le_localPolynomial
    (μ : Measure ℝ) (n : ℕ) {t0 T : ℝ} (ht0 : 0 ≤ t0) :
    (∫ t in Set.Icc (0 : ℝ) t0,
        |T| * berryEsseenDurrettFourierBound μ n (T * t) ∂volume) ≤
      ((1 / 6 : ℝ) * (∫ x, |x| ^ 3 ∂μ) * |T| ^ 3 /
          Real.sqrt ((n + 1 : ℕ) : ℝ)) * (t0 ^ 3 / 3) +
        (|T| ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) * (t0 ^ 4 / 4) := by
  let M : ℝ := ∫ x, |x| ^ 3 ∂μ
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let A : ℝ := (1 / 6 : ℝ) * M * |T| ^ 3 / Real.sqrt N
  let B : ℝ := |T| ^ 4 / (8 * N)
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact integral_abs_cube_nonneg μ
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, M, N]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, N]
    positivity
  have hLeft :
      IntegrableOn
        (fun t : ℝ => |T| * berryEsseenDurrettFourierBound μ n (T * t))
        (Set.Icc (0 : ℝ) t0) := by
    exact (continuous_const.mul
      ((continuous_berryEsseenDurrettFourierBound μ n).comp
        (continuous_const.mul continuous_id))).integrableOn_Icc
  have hRight :
      IntegrableOn (fun t : ℝ => A * t ^ 2 + B * t ^ 3)
        (Set.Icc (0 : ℝ) t0) := by
    exact (by fun_prop :
      Continuous fun t : ℝ => A * t ^ 2 + B * t ^ 3).integrableOn_Icc
  have hMono :
      (∫ t in Set.Icc (0 : ℝ) t0,
          |T| * berryEsseenDurrettFourierBound μ n (T * t) ∂volume) ≤
        ∫ t in Set.Icc (0 : ℝ) t0, A * t ^ 2 + B * t ^ 3 ∂volume := by
    refine setIntegral_mono_on hLeft hRight measurableSet_Icc ?_
    intro t ht
    have ht_nonneg : 0 ≤ t := ht.1
    have hpoly :=
      berryEsseenDurrettFourierBound_le_polynomial μ n (T * t)
    have hscaled := mul_le_mul_of_nonneg_left hpoly (abs_nonneg T)
    calc
      |T| * berryEsseenDurrettFourierBound μ n (T * t)
          ≤ |T| *
              ((1 / 6 : ℝ) * M * |T * t| ^ 2 / Real.sqrt N +
                |T * t| ^ 3 / (8 * N)) := by
            simpa [M, N] using hscaled
      _ = A * t ^ 2 + B * t ^ 3 := by
            rw [abs_mul, abs_of_nonneg ht_nonneg]
            dsimp [A, B, M, N]
            ring
  have hEval :
      (∫ t in Set.Icc (0 : ℝ) t0, A * t ^ 2 + B * t ^ 3 ∂volume) =
        A * (t0 ^ 3 / 3) + B * (t0 ^ 4 / 4) := by
    have hIntSq :
        IntegrableOn (fun t : ℝ => A * t ^ 2) (Set.Icc (0 : ℝ) t0) := by
      exact (by fun_prop : Continuous fun t : ℝ => A * t ^ 2).integrableOn_Icc
    have hIntCube :
        IntegrableOn (fun t : ℝ => B * t ^ 3) (Set.Icc (0 : ℝ) t0) := by
      exact (by fun_prop : Continuous fun t : ℝ => B * t ^ 3).integrableOn_Icc
    rw [integral_add hIntSq hIntCube, integral_const_mul,
      integral_const_mul, integral_Icc_zero_sq_eq ht0,
      integral_Icc_zero_cube_eq ht0]
  exact hMono.trans_eq (by simpa [A, B, M, N] using hEval)

lemma shevtsovaPrawitzRnTerm_le_localPolynomial_of_t0_le_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 T : ℝ}
    (h0t : 0 ≤ t0) (ht0 : t0 ≤ 1 / 2)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      ((1 / 6 : ℝ) * berryEsseenRho X P m σ * |T| ^ 3 /
          Real.sqrt ((n + 1 : ℕ) : ℝ)) * (t0 ^ 3 / 3) +
        (|T| ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) * (t0 ^ 4 / 4) := by
  let ν : Measure ℝ := P.map (fun ω => (X 0 ω - m) / σ)
  have hFirst :
      shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
        ∫ t in Set.Icc (0 : ℝ) t0,
          |T| * berryEsseenDurrettFourierBound ν n (T * t) ∂volume :=
    shevtsovaPrawitzRnTerm_le_scaledDurrettIntegral_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T ht0 hWindow hSmall
  have hLocal :=
    integral_Icc_abs_mul_berryEsseenDurrettFourierBound_comp_le_localPolynomial
      (μ := ν) (n := n) (t0 := t0) (T := T) h0t
  have hM :
      ∫ x : ℝ, |x| ^ 3 ∂ν = berryEsseenRho X P m σ := by
    dsimp [ν]
    rw [integral_standardizedLaw_abs_cube_eq
      (P := P) (Y := X 0) (m := m) (σ := σ)
      (hBE.aemeasurable 0) hBE.sigma_pos]
    rfl
  exact hFirst.trans (by simpa [ν, hM] using hLocal)

lemma two_mul_shevtsovaPrawitzRnTerm_le_two_mul_localPolynomial_of_t0_le_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 T : ℝ}
    (h0t : 0 ≤ t0) (ht0 : t0 ≤ 1 / 2)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    2 * shevtsovaPrawitzRnTerm P X m σ (n + 1) t0 T ≤
      2 *
        (((1 / 6 : ℝ) * berryEsseenRho X P m σ * |T| ^ 3 /
            Real.sqrt ((n + 1 : ℕ) : ℝ)) * (t0 ^ 3 / 3) +
          (|T| ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) * (t0 ^ 4 / 4)) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzRnTerm_le_localPolynomial_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn h0t ht0 hWindow hSmall)
    (by norm_num)

lemma integrableOn_shevtsovaPrawitzFn_integrand_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ)
    (hK : IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 1)) :
    IntegrableOn
      (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
        shevtsovaFnAbs P X m σ N (T * t))
      (Set.Icc t0 1) := by
  change Integrable
    (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖ *
      shevtsovaFnAbs P X m σ N (T * t))
    (volume.restrict (Set.Icc t0 1))
  change Integrable (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
    (volume.restrict (Set.Icc t0 1)) at hK
  refine hK.mono' ?_ ?_
  · exact (measurable_shevtsovaPrawitzKernel_norm.mul
      (((continuous_shevtsovaFnAbs_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE N).comp
          (continuous_const.mul continuous_id)).measurable)).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (norm_nonneg (shevtsovaPrawitzKernel t))
        (shevtsovaFnAbs_nonneg P X m σ N (T * t)))]
    exact mul_le_of_le_one_right (norm_nonneg (shevtsovaPrawitzKernel t))
      (shevtsovaFnAbs_le_one_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE N (T * t))

lemma shevtsovaPrawitzFnTerm_le_kernelIntegral_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ)
    (hK : IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 1)) :
    shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      ∫ t in Set.Icc t0 1, ‖shevtsovaPrawitzKernel t‖ ∂volume := by
  have hLeft :=
    integrableOn_shevtsovaPrawitzFn_integrand_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N t0 T hK
  unfold shevtsovaPrawitzFnTerm
  refine setIntegral_mono_on hLeft hK measurableSet_Icc ?_
  intro t _ht
  exact mul_le_of_le_one_right (norm_nonneg (shevtsovaPrawitzKernel t))
    (shevtsovaFnAbs_le_one_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N (T * t))

lemma two_mul_shevtsovaPrawitzFnTerm_le_two_mul_kernelIntegral_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ)
    (hK : IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 1)) :
    2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      2 * (∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ ∂volume) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzFnTerm_le_kernelIntegral_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N t0 T hK)
    (by norm_num)

/-- Prawitz second-term bound using the newly proved first-branch
Shevtsova `ψ` decay.  The right-hand integrability is explicit here; later
certificate lemmas can discharge it for concrete windows. -/
lemma shevtsovaPrawitzFnTerm_le_sqrtPsiIntegral_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ)
    (hK : IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 1))
    (hMajorant :
      IntegrableOn
        (fun t : ℝ =>
          ‖shevtsovaPrawitzKernel t‖ *
            (Real.sqrt
              (1 - shevtsovaPsi
                (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
                (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N)
        (Set.Icc t0 1))
    (hfirst :
      ∀ t ∈ Set.Icc t0 1,
        |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| ≤
          shevtsovaTheta0 /
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ)) :
    shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      ∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ *
          (Real.sqrt
            (1 - shevtsovaPsi
              (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
              (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N ∂volume := by
  have hLeft :=
    integrableOn_shevtsovaPrawitzFn_integrand_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N t0 T hK
  unfold shevtsovaPrawitzFnTerm
  refine setIntegral_mono_on hLeft hMajorant measurableSet_Icc ?_
  intro t ht
  exact mul_le_mul_of_nonneg_left
    (shevtsovaFnAbs_le_sqrt_one_sub_shevtsovaPsi_pow_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N
      (t := T * t) (hfirst t ht))
    (norm_nonneg (shevtsovaPrawitzKernel t))

lemma two_mul_shevtsovaPrawitzFnTerm_le_two_mul_sqrtPsiIntegral_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ)
    (hK : IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 1))
    (hMajorant :
      IntegrableOn
        (fun t : ℝ =>
          ‖shevtsovaPrawitzKernel t‖ *
            (Real.sqrt
              (1 - shevtsovaPsi
                (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
                (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N)
        (Set.Icc t0 1))
    (hfirst :
      ∀ t ∈ Set.Icc t0 1,
        |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| ≤
          shevtsovaTheta0 /
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ)) :
    2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      2 * (∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ *
          (Real.sqrt
            (1 - shevtsovaPsi
              (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
              (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N ∂volume) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzFnTerm_le_sqrtPsiIntegral_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE N t0 T hK hMajorant hfirst)
    (by norm_num)

lemma two_sqrt_two_mul_berryEsseenRho_pos_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    0 < 2 * Real.sqrt 2 * berryEsseenRho X P m σ := by
  have hrho_pos : 0 < berryEsseenRho X P m σ := by
    exact zero_lt_one.trans_le
      (one_le_berryEsseenRho_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE)
  positivity

lemma sqrt_one_sub_shevtsovaPsi_pow_le_one_of_first_branch_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ t : ℝ} {N : ℕ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    (Real.sqrt
      (1 - shevtsovaPsi
        (Real.sqrt 2 * (t / Real.sqrt (N : ℝ)))
        (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N ≤ 1 := by
  have hε_pos :
      0 < 2 * Real.sqrt 2 * berryEsseenRho X P m σ :=
    two_sqrt_two_mul_berryEsseenRho_pos_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE
  have hbase_le :
      1 - shevtsovaPsi
        (Real.sqrt 2 * (t / Real.sqrt (N : ℝ)))
        (2 * Real.sqrt 2 * berryEsseenRho X P m σ) ≤ 1 := by
    have hpsi_nonneg :
        0 ≤ shevtsovaPsi
          (Real.sqrt 2 * (t / Real.sqrt (N : ℝ)))
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ) :=
      shevtsovaPsi_nonneg_of_pos hε_pos
    linarith
  have hsqrt_le :
      Real.sqrt
        (1 - shevtsovaPsi
          (Real.sqrt 2 * (t / Real.sqrt (N : ℝ)))
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ)) ≤ 1 := by
    rwa [Real.sqrt_le_one]
  exact pow_le_one₀ (Real.sqrt_nonneg _) hsqrt_le

lemma measurable_shevtsovaSqrtPsiMajorant_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (N : ℕ) (T : ℝ) :
    Measurable
      (fun t : ℝ =>
        (Real.sqrt
          (1 - shevtsovaPsi
            (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N) := by
  have harg :
      Measurable
        (fun t : ℝ => Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))) := by
    exact ((continuous_const.mul
      ((continuous_const.mul continuous_id).div_const
        (Real.sqrt (N : ℝ)))).measurable)
  have hpsi :
      Measurable
        (fun t : ℝ =>
          shevtsovaPsi
            (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ)) :=
    (measurable_shevtsovaPsi_const_epsilon
      (2 * Real.sqrt 2 * berryEsseenRho X P m σ)).comp harg
  exact (Real.continuous_sqrt.measurable.comp
    (measurable_const.sub hpsi)).pow_const N

lemma integrableOn_shevtsovaPrawitzSqrtPsiMajorant_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ)
    (hK : IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 1)) :
    IntegrableOn
      (fun t : ℝ =>
        ‖shevtsovaPrawitzKernel t‖ *
          (Real.sqrt
            (1 - shevtsovaPsi
              (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
              (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N)
      (Set.Icc t0 1) := by
  change Integrable
    (fun t : ℝ =>
      ‖shevtsovaPrawitzKernel t‖ *
        (Real.sqrt
          (1 - shevtsovaPsi
            (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N)
    (volume.restrict (Set.Icc t0 1))
  change Integrable (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
    (volume.restrict (Set.Icc t0 1)) at hK
  refine hK.mono' ?_ ?_
  · exact (measurable_shevtsovaPrawitzKernel_norm.mul
      (measurable_shevtsovaSqrtPsiMajorant_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) N T)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg (norm_nonneg (shevtsovaPrawitzKernel t))
          (pow_nonneg (Real.sqrt_nonneg _) N))]
    exact mul_le_of_le_one_right
      (norm_nonneg (shevtsovaPrawitzKernel t))
      (sqrt_one_sub_shevtsovaPsi_pow_le_one_of_first_branch_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE
        (N := N) (t := T * t))

lemma shevtsovaPrawitzFnTerm_le_sqrtPsiIntegral_of_first_branch_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ)
    (hK : IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 1))
    (hfirst :
      ∀ t ∈ Set.Icc t0 1,
        |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| ≤
          shevtsovaTheta0 /
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ)) :
    shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      ∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ *
          (Real.sqrt
            (1 - shevtsovaPsi
              (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
              (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N ∂volume := by
  exact shevtsovaPrawitzFnTerm_le_sqrtPsiIntegral_of_hypotheses
    (P := P) (X := X) (m := m) (σ := σ)
    hBE N t0 T hK
    (integrableOn_shevtsovaPrawitzSqrtPsiMajorant_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N t0 T hK)
    hfirst

lemma two_mul_shevtsovaPrawitzFnTerm_le_two_mul_sqrtPsiIntegral_of_first_branch_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ)
    (hK : IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 1))
    (hfirst :
      ∀ t ∈ Set.Icc t0 1,
        |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| ≤
          shevtsovaTheta0 /
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ)) :
    2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      2 * (∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ *
          (Real.sqrt
            (1 - shevtsovaPsi
              (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
              (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N ∂volume) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzFnTerm_le_sqrtPsiIntegral_of_first_branch_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE N t0 T hK hfirst)
    (by norm_num)

lemma shevtsovaPrawitzFnFirstBranch_of_cutoff_bound
    {N : ℕ} (hN : 0 < N) {rho t0 T : ℝ}
    (hrho : 0 < rho) (ht0 : 0 ≤ t0)
    (hCut : 4 * rho * |T| ≤ shevtsovaTheta0 * Real.sqrt (N : ℝ)) :
    ∀ t ∈ Set.Icc t0 1,
      |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| ≤
        shevtsovaTheta0 / (2 * Real.sqrt 2 * rho) := by
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr hN_pos_real
  have hsqrt2_pos : 0 < Real.sqrt (2 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_mul : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := by
    rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hmain : 4 * rho * |T| / Real.sqrt (N : ℝ) ≤ shevtsovaTheta0 := by
    rw [div_le_iff₀ hsqrtN_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hCut
  intro t ht
  have ht_nonneg : 0 ≤ t := ht0.trans ht.1
  have ht_abs_le_one : |t| ≤ 1 := by
    rw [abs_of_nonneg ht_nonneg]
    exact ht.2
  have hleft :
      |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| =
        Real.sqrt 2 * (|T| * |t| / Real.sqrt (N : ℝ)) := by
    rw [abs_mul, abs_of_pos hsqrt2_pos, abs_div,
      abs_of_pos hsqrtN_pos, abs_mul]
  have hscale :
      Real.sqrt 2 * (|T| * |t| / Real.sqrt (N : ℝ)) ≤
        Real.sqrt 2 * (|T| / Real.sqrt (N : ℝ)) := by
    have hmul_abs_le : |T| * |t| ≤ |T| := by
      simpa [mul_one] using
        mul_le_mul_of_nonneg_left ht_abs_le_one (abs_nonneg T)
    have hdiv_le :
        |T| * |t| / Real.sqrt (N : ℝ) ≤
          |T| / Real.sqrt (N : ℝ) :=
      div_le_div_of_nonneg_right hmul_abs_le hsqrtN_pos.le
    exact mul_le_mul_of_nonneg_left hdiv_le hsqrt2_pos.le
  rw [hleft]
  calc
    Real.sqrt 2 * (|T| * |t| / Real.sqrt (N : ℝ))
        ≤ Real.sqrt 2 * (|T| / Real.sqrt (N : ℝ)) := hscale
    _ ≤ shevtsovaTheta0 / (2 * Real.sqrt 2 * rho) := by
          have hden_pos : 0 < 2 * Real.sqrt 2 * rho := by positivity
          rw [le_div_iff₀ hden_pos]
          calc
            Real.sqrt 2 * (|T| / Real.sqrt (N : ℝ)) *
                (2 * Real.sqrt 2 * rho)
                = 4 * rho * |T| / Real.sqrt (N : ℝ) := by
                  rw [show Real.sqrt 2 * (|T| / Real.sqrt (N : ℝ)) *
                      (2 * Real.sqrt 2 * rho) =
                        (Real.sqrt 2 * Real.sqrt 2) *
                          (2 * rho * |T| / Real.sqrt (N : ℝ)) by ring]
                  rw [hsqrt2_mul]
                  ring
            _ ≤ shevtsovaTheta0 := hmain

lemma shevtsovaPrawitzFnTerm_le_sqrtPsiIntegral_of_cutoff_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ) (ht0 : 0 ≤ t0)
    (hK : IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 1))
    (hCut :
      4 * berryEsseenRho X P m σ * |T| ≤
        shevtsovaTheta0 * Real.sqrt (N : ℝ)) :
    shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      ∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ *
          (Real.sqrt
            (1 - shevtsovaPsi
              (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
              (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N ∂volume := by
  have hrho_pos : 0 < berryEsseenRho X P m σ := by
    exact zero_lt_one.trans_le
      (one_le_berryEsseenRho_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE)
  exact
    shevtsovaPrawitzFnTerm_le_sqrtPsiIntegral_of_first_branch_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE N t0 T hK
      (shevtsovaPrawitzFnFirstBranch_of_cutoff_bound
        (N := N) hN (rho := berryEsseenRho X P m σ)
        (t0 := t0) (T := T) hrho_pos ht0 hCut)

lemma two_mul_shevtsovaPrawitzFnTerm_le_two_mul_sqrtPsiIntegral_of_cutoff_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ) (ht0 : 0 ≤ t0)
    (hK : IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
      (Set.Icc t0 1))
    (hCut :
      4 * berryEsseenRho X P m σ * |T| ≤
        shevtsovaTheta0 * Real.sqrt (N : ℝ)) :
    2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      2 * (∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ *
          (Real.sqrt
            (1 - shevtsovaPsi
              (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
              (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N ∂volume) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzFnTerm_le_sqrtPsiIntegral_of_cutoff_bound
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hN t0 T ht0 hK hCut)
    (by norm_num)

lemma shevtsovaPrawitzFnTerm_le_sqrtPsiIntegral_of_pos_le_half_cutoff_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ)
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2)
    (hCut :
      4 * berryEsseenRho X P m σ * |T| ≤
        shevtsovaTheta0 * Real.sqrt (N : ℝ)) :
    shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      ∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ *
          (Real.sqrt
            (1 - shevtsovaPsi
              (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
              (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N ∂volume := by
  have hK :
      IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
        (Set.Icc t0 1) :=
    integrableOn_shevtsovaPrawitzKernel_norm_Icc_t0_one ht0 ht0le
  exact
    shevtsovaPrawitzFnTerm_le_sqrtPsiIntegral_of_cutoff_bound
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hN t0 T ht0.le hK hCut

lemma two_mul_shevtsovaPrawitzFnTerm_le_two_mul_sqrtPsiIntegral_of_pos_le_half_cutoff_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ)
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2)
    (hCut :
      4 * berryEsseenRho X P m σ * |T| ≤
        shevtsovaTheta0 * Real.sqrt (N : ℝ)) :
    2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      2 * (∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ *
          (Real.sqrt
            (1 - shevtsovaPsi
              (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
              (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N ∂volume) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzFnTerm_le_sqrtPsiIntegral_of_pos_le_half_cutoff_bound
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hN t0 T ht0 ht0le hCut)
    (by norm_num)

lemma shevtsovaPrawitzFnSqrtPsiSmall_of_cutoff_bound
    {N : ℕ} (hN : 0 < N) {rho t0 T : ℝ}
    (hrho : 0 ≤ rho) (ht0 : 0 ≤ t0)
    (hCut :
      16 * shevtsovaKappa * rho * |T| ≤
        Real.sqrt (N : ℝ)) :
    ∀ t ∈ Set.Icc t0 1,
      shevtsovaKappa * (2 * Real.sqrt 2 * rho) *
        |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| ≤ 1 / 4 := by
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr hN_pos_real
  have hsqrt2_pos : 0 < Real.sqrt (2 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_mul : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := by
    rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hmain :
      4 * shevtsovaKappa * rho * |T| /
          Real.sqrt (N : ℝ) ≤ 1 / 4 := by
    rw [div_le_iff₀ hsqrtN_pos]
    nlinarith [hCut]
  intro t ht
  have ht_nonneg : 0 ≤ t := ht0.trans ht.1
  have ht_abs_le_one : |t| ≤ 1 := by
    rw [abs_of_nonneg ht_nonneg]
    exact ht.2
  have hscaled_abs : |T| * |t| ≤ |T| := by
    simpa [mul_one] using
      mul_le_mul_of_nonneg_left ht_abs_le_one (abs_nonneg T)
  have hcoef_nonneg : 0 ≤ 4 * shevtsovaKappa * rho := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) shevtsovaKappa_pos.le) hrho
  have hscaled :
      4 * shevtsovaKappa * rho * (|T| * |t|) /
          Real.sqrt (N : ℝ) ≤
        4 * shevtsovaKappa * rho * |T| / Real.sqrt (N : ℝ) := by
    have hmul :
        4 * shevtsovaKappa * rho * (|T| * |t|) ≤
          4 * shevtsovaKappa * rho * |T| :=
      mul_le_mul_of_nonneg_left hscaled_abs hcoef_nonneg
    exact div_le_div_of_nonneg_right hmul hsqrtN_pos.le
  have hleft :
      shevtsovaKappa * (2 * Real.sqrt 2 * rho) *
          |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| =
        4 * shevtsovaKappa * rho * (|T| * |t|) /
          Real.sqrt (N : ℝ) := by
    rw [abs_mul, abs_of_pos hsqrt2_pos, abs_div,
      abs_of_pos hsqrtN_pos, abs_mul]
    calc
      shevtsovaKappa * (2 * Real.sqrt 2 * rho) *
          (Real.sqrt 2 * (|T| * |t| / Real.sqrt (N : ℝ)))
          = (Real.sqrt 2 * Real.sqrt 2) *
              (2 * shevtsovaKappa * rho *
                (|T| * |t| / Real.sqrt (N : ℝ))) := by
            ring
      _ = 4 * shevtsovaKappa * rho * (|T| * |t|) /
          Real.sqrt (N : ℝ) := by
            rw [hsqrt2_mul]
            ring
  rw [hleft]
  exact hscaled.trans hmain

lemma one_div_four_mul_shevtsovaKappa_le_theta0 :
    1 / (4 * shevtsovaKappa) ≤ shevtsovaTheta0 := by
  have hκ_pos : 0 < shevtsovaKappa := shevtsovaKappa_pos
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hκ_lower : 1 / (4 * Real.pi) ≤ shevtsovaKappa :=
    one_div_four_pi_le_shevtsovaKappa
  have hle_pi : 1 / (4 * shevtsovaKappa) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity : 0 < 4 * shevtsovaKappa)]
    have hmul :
        (1 / (4 * Real.pi)) * (4 * Real.pi) ≤
          shevtsovaKappa * (4 * Real.pi) :=
      mul_le_mul_of_nonneg_right hκ_lower (by positivity)
    have hleft :
        (1 / (4 * Real.pi)) * (4 * Real.pi) = 1 := by
      field_simp [Real.pi_pos.ne']
    have hright :
        shevtsovaKappa * (4 * Real.pi) =
          (4 * shevtsovaKappa) * Real.pi := by
      ring
    have hmul' : 1 ≤ (4 * shevtsovaKappa) * Real.pi := by
      calc
        1 = (1 / (4 * Real.pi)) * (4 * Real.pi) := hleft.symm
        _ ≤ shevtsovaKappa * (4 * Real.pi) := hmul
        _ = (4 * shevtsovaKappa) * Real.pi := hright
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
  exact hle_pi.trans shevtsovaTheta0_mem_Icc.1

/-- A convenient rational lower bound for the Prawitz constant `κ`.  This is
weaker than the local `1 / (4π)` lower bound, but it is algebraically handy for
standard-cutoff side conditions. -/
lemma three_div_128_le_shevtsovaKappa :
    (3 / 128 : ℝ) ≤ shevtsovaKappa := by
  have hpi_bound : (3 / 128 : ℝ) ≤ 1 / (4 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : 0 < 4 * Real.pi)]
    nlinarith [Real.pi_lt_four]
  exact hpi_bound.trans one_div_four_pi_le_shevtsovaKappa

/-- The standard cutoff used by the first-branch `sqrt(1 - ψ)^N` Prawitz
route. -/
def shevtsovaSqrtPsiCutoffT (rho : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho)

lemma shevtsovaSqrtPsiCutoffT_pos
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho) :
    0 < shevtsovaSqrtPsiCutoffT rho N := by
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
  unfold shevtsovaSqrtPsiCutoffT
  exact div_pos (Real.sqrt_pos.mpr hN_pos_real)
    (mul_pos (mul_pos (by norm_num) shevtsovaKappa_pos) hrho)

lemma abs_shevtsovaSqrtPsiCutoffT
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho) :
    |shevtsovaSqrtPsiCutoffT rho N| =
      shevtsovaSqrtPsiCutoffT rho N := by
  exact abs_of_pos (shevtsovaSqrtPsiCutoffT_pos (N := N) hN hrho)

lemma shevtsovaPrawitzFnFirstCut_of_sqrtPsiCutoff
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho) :
    4 * rho * |shevtsovaSqrtPsiCutoffT rho N| ≤
      shevtsovaTheta0 * Real.sqrt (N : ℝ) := by
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrtN_nonneg : 0 ≤ Real.sqrt (N : ℝ) :=
    (Real.sqrt_pos.mpr hN_pos_real).le
  rw [abs_shevtsovaSqrtPsiCutoffT (N := N) hN hrho]
  unfold shevtsovaSqrtPsiCutoffT
  have hden_pos : 0 < 16 * shevtsovaKappa * rho := by
    exact mul_pos (mul_pos (by norm_num) shevtsovaKappa_pos) hrho
  calc
    4 * rho *
        (Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho))
        = (1 / (4 * shevtsovaKappa)) * Real.sqrt (N : ℝ) := by
          field_simp [hden_pos.ne', hrho.ne', shevtsovaKappa_pos.ne']
          ring
    _ ≤ shevtsovaTheta0 * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_right
            one_div_four_mul_shevtsovaKappa_le_theta0
            hsqrtN_nonneg

lemma shevtsovaPrawitzFnSmallPsiCut_of_sqrtPsiCutoff
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho) :
    16 * shevtsovaKappa * rho *
        |shevtsovaSqrtPsiCutoffT rho N| ≤
      Real.sqrt (N : ℝ) := by
  rw [abs_shevtsovaSqrtPsiCutoffT (N := N) hN hrho]
  unfold shevtsovaSqrtPsiCutoffT
  have hden_pos : 0 < 16 * shevtsovaKappa * rho := by
    exact mul_pos (mul_pos (by norm_num) shevtsovaKappa_pos) hrho
  calc
    16 * shevtsovaKappa * rho *
        (Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho))
        = Real.sqrt (N : ℝ) := by
          field_simp [hden_pos.ne', hrho.ne', shevtsovaKappa_pos.ne']
    _ ≤ Real.sqrt (N : ℝ) := le_rfl

lemma shevtsovaPrawitzRnSmallCut_of_sqrtPsiCutoff
    {N : ℕ} (hN : 0 < N) {rho t0 : ℝ}
    (hrho : 1 ≤ rho) (ht0_nonneg : 0 ≤ t0) (ht0le : t0 ≤ 1 / 2) :
    rho * |shevtsovaSqrtPsiCutoffT rho N * t0| ≤
      (4 / 3 : ℝ) * Real.sqrt (N : ℝ) := by
  have hrho_pos : 0 < rho := by nlinarith
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrtN_nonneg : 0 ≤ Real.sqrt (N : ℝ) :=
    (Real.sqrt_pos.mpr hN_pos_real).le
  have hκ_t0 : t0 ≤ (64 / 3 : ℝ) * shevtsovaKappa := by
    calc
      t0 ≤ 1 / 2 := ht0le
      _ ≤ (64 / 3 : ℝ) * shevtsovaKappa := by
            nlinarith [three_div_128_le_shevtsovaKappa]
  have hfactor : t0 / (16 * shevtsovaKappa) ≤ (4 / 3 : ℝ) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) shevtsovaKappa_pos)]
    nlinarith [hκ_t0]
  have hleft :
      rho * |shevtsovaSqrtPsiCutoffT rho N * t0| =
        Real.sqrt (N : ℝ) * (t0 / (16 * shevtsovaKappa)) := by
    rw [abs_mul, abs_shevtsovaSqrtPsiCutoffT (N := N) hN hrho_pos,
      abs_of_nonneg ht0_nonneg]
    unfold shevtsovaSqrtPsiCutoffT
    field_simp [hrho_pos.ne', shevtsovaKappa_pos.ne']
  rw [hleft]
  calc
    Real.sqrt (N : ℝ) * (t0 / (16 * shevtsovaKappa))
        ≤ Real.sqrt (N : ℝ) * (4 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left hfactor hsqrtN_nonneg
    _ = (4 / 3 : ℝ) * Real.sqrt (N : ℝ) := by ring

lemma shevtsovaPrawitzRnWindowCut_of_sqrtPsiCutoff
    {N : ℕ} (hN : 0 < N) {rho t0 : ℝ}
    (hrho : 1 ≤ rho) (ht0_nonneg : 0 ≤ t0) (ht0le : t0 ≤ 1 / 2) :
    (shevtsovaSqrtPsiCutoffT rho N * t0) ^ 2 ≤ 2 * (N : ℝ) := by
  have hsmall :=
    shevtsovaPrawitzRnSmallCut_of_sqrtPsiCutoff
      (N := N) hN (rho := rho) (t0 := t0)
      hrho ht0_nonneg ht0le
  have hrho_nonneg : 0 ≤ rho := by nlinarith
  have hsqrtN_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have habs_le :
      |shevtsovaSqrtPsiCutoffT rho N * t0| ≤
        (4 / 3 : ℝ) * Real.sqrt (N : ℝ) := by
    have hscale :
        |shevtsovaSqrtPsiCutoffT rho N * t0| ≤
          rho * |shevtsovaSqrtPsiCutoffT rho N * t0| := by
      simpa [one_mul] using
        mul_le_mul_of_nonneg_right hrho
          (abs_nonneg (shevtsovaSqrtPsiCutoffT rho N * t0))
    exact hscale.trans hsmall
  have hsq_le :
      |shevtsovaSqrtPsiCutoffT rho N * t0| ^ 2 ≤
        ((4 / 3 : ℝ) * Real.sqrt (N : ℝ)) ^ 2 := by
    exact
      (sq_le_sq₀
        (abs_nonneg (shevtsovaSqrtPsiCutoffT rho N * t0))
        (mul_nonneg (by norm_num) hsqrtN_nonneg)).mpr habs_le
  have htarget :
      ((4 / 3 : ℝ) * Real.sqrt (N : ℝ)) ^ 2 ≤
        2 * (N : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith
  rw [← sq_abs]
  exact hsq_le.trans htarget

lemma shevtsovaPrawitzFnFirstBranch_of_sqrtPsi_cutoff
    {N : ℕ} (hN : 0 < N) {rho t0 : ℝ}
    (hrho : 0 < rho) (ht0 : 0 ≤ t0) :
    ∀ t ∈ Set.Icc t0 1,
      |Real.sqrt 2 *
          (((Real.sqrt (N : ℝ) /
              (16 * shevtsovaKappa * rho)) * t) /
            Real.sqrt (N : ℝ))| ≤
        shevtsovaTheta0 / (2 * Real.sqrt 2 * rho) := by
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr hN_pos_real
  have hT_abs :
      |Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho)| =
        Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho) := by
    rw [abs_of_nonneg]
    exact div_nonneg hsqrtN_pos.le
      (mul_nonneg
        (mul_nonneg (by norm_num) shevtsovaKappa_pos.le) hrho.le)
  have hCut :
      4 * rho *
          |Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho)| ≤
        shevtsovaTheta0 * Real.sqrt (N : ℝ) := by
    rw [hT_abs]
    have hden_pos : 0 < 16 * shevtsovaKappa * rho := by
      exact mul_pos
        (mul_pos (by norm_num) shevtsovaKappa_pos) hrho
    calc
      4 * rho *
          (Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho))
          = (1 / (4 * shevtsovaKappa)) *
              Real.sqrt (N : ℝ) := by
            field_simp [hden_pos.ne', hrho.ne', shevtsovaKappa_pos.ne']
            ring
      _ ≤ shevtsovaTheta0 * Real.sqrt (N : ℝ) :=
            mul_le_mul_of_nonneg_right
              one_div_four_mul_shevtsovaKappa_le_theta0
              hsqrtN_pos.le
  exact
    shevtsovaPrawitzFnFirstBranch_of_cutoff_bound
      (N := N) hN (rho := rho) (t0 := t0)
      (T := Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho))
      hrho ht0 hCut

lemma shevtsovaPrawitzFnSqrtPsiSmall_of_sqrtPsi_cutoff
    {N : ℕ} (hN : 0 < N) {rho t0 : ℝ}
    (hrho : 0 < rho) (ht0 : 0 ≤ t0) :
    ∀ t ∈ Set.Icc t0 1,
      shevtsovaKappa * (2 * Real.sqrt 2 * rho) *
        |Real.sqrt 2 *
          (((Real.sqrt (N : ℝ) /
              (16 * shevtsovaKappa * rho)) * t) /
            Real.sqrt (N : ℝ))| ≤ 1 / 4 := by
  have hT_abs :
      |Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho)| =
        Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho) := by
    rw [abs_of_nonneg]
    exact div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg
        (mul_nonneg (by norm_num) shevtsovaKappa_pos.le) hrho.le)
  have hCut :
      16 * shevtsovaKappa * rho *
          |Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho)| ≤
        Real.sqrt (N : ℝ) := by
    rw [hT_abs]
    have hden_pos : 0 < 16 * shevtsovaKappa * rho := by
      exact mul_pos
        (mul_pos (by norm_num) shevtsovaKappa_pos) hrho
    calc
      16 * shevtsovaKappa * rho *
          (Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho))
          = Real.sqrt (N : ℝ) := by
            field_simp [hden_pos.ne', hrho.ne', shevtsovaKappa_pos.ne']
      _ ≤ Real.sqrt (N : ℝ) := le_rfl
  exact
    shevtsovaPrawitzFnSqrtPsiSmall_of_cutoff_bound
      (N := N) hN (rho := rho) (t0 := t0)
      (T := Real.sqrt (N : ℝ) / (16 * shevtsovaKappa * rho))
      hrho.le ht0 hCut

lemma integral_Ioi_mul_exp_neg_T_sq_div_four {T : ℝ} (hT : T ≠ 0) :
    (∫ x in Set.Ioi (0 : ℝ),
      x * Real.exp (-(T ^ 2 * x ^ 2) / 4)) =
      2 * (T ^ 2)⁻¹ := by
  have hb : 0 < T ^ 2 / 4 := by positivity
  have h := integral_Ioi_mul_exp_neg_mul_sq (b := T ^ 2 / 4) hb
  convert h using 1
  · refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    ring_nf
  · field_simp [pow_ne_zero 2 hT]
    ring

lemma integral_Icc_inv_t0_mul_exp_neg_T_sq_div_four_le
    {t0 T : ℝ} (ht0 : 0 < t0) (hT : T ≠ 0) :
    (∫ t in Set.Icc t0 1,
      (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4) ∂volume) ≤
      (1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹)) := by
  let f : ℝ → ℝ := fun t =>
    (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4)
  let g : ℝ → ℝ := fun t =>
    (1 / t0) * ((1 / t0) *
      (t * Real.exp (-(T ^ 2 * t ^ 2) / 4)))
  have hfInt : IntegrableOn f (Set.Icc t0 1) := by
    dsimp [f]
    exact (by fun_prop :
      Continuous fun t : ℝ =>
        (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4)).integrableOn_Icc
  have hgIntIcc : IntegrableOn g (Set.Icc t0 1) := by
    dsimp [g]
    exact (by fun_prop :
      Continuous fun t : ℝ =>
        (1 / t0) * ((1 / t0) *
          (t * Real.exp (-(T ^ 2 * t ^ 2) / 4)))).integrableOn_Icc
  have hb : 0 < T ^ 2 / 4 := by positivity
  have hglobal :
      Integrable (fun t : ℝ =>
        t * Real.exp (-(T ^ 2 * t ^ 2) / 4)) := by
    have h := integrable_mul_exp_neg_mul_sq (b := T ^ 2 / 4) hb
    convert h using 1
    ext t
    ring_nf
  have hgIntIoi :
      IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    dsimp [g]
    exact (hglobal.const_mul (1 / t0)).const_mul (1 / t0) |>.integrableOn
  have hCompare :
      (∫ t in Set.Icc t0 1, f t ∂volume) ≤
        ∫ t in Set.Icc t0 1, g t ∂volume := by
    refine setIntegral_mono_on hfInt hgIntIcc measurableSet_Icc ?_
    intro t ht
    have ht_pos : 0 < t := ht0.trans_le ht.1
    have hexp_nonneg : 0 ≤ Real.exp (-(T ^ 2 * t ^ 2) / 4) :=
      (Real.exp_pos _).le
    have ht0_inv_nonneg : 0 ≤ 1 / t0 := by positivity
    have hscale : 1 ≤ t / t0 := by
      rw [le_div_iff₀ ht0]
      simpa using ht.1
    dsimp [f, g]
    calc
      (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4)
          ≤ (1 / t0) *
              ((t / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4)) := by
            exact mul_le_mul_of_nonneg_left
              (by
                calc
                  Real.exp (-(T ^ 2 * t ^ 2) / 4)
                      = 1 * Real.exp (-(T ^ 2 * t ^ 2) / 4) := by ring
                  _ ≤ (t / t0) *
                        Real.exp (-(T ^ 2 * t ^ 2) / 4) :=
                    mul_le_mul_of_nonneg_right hscale hexp_nonneg)
              ht0_inv_nonneg
      _ = (1 / t0) *
              ((1 / t0) *
                (t * Real.exp (-(T ^ 2 * t ^ 2) / 4))) := by ring
  have hSet :
      (∫ t in Set.Icc t0 1, g t ∂volume) ≤
        ∫ t in Set.Ioi (0 : ℝ), g t ∂volume := by
    refine setIntegral_mono_set hgIntIoi ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := ht
      dsimp [g]
      positivity
    · exact Eventually.of_forall fun t ht => ht0.trans_le ht.1
  have hEval :
      (∫ t in Set.Ioi (0 : ℝ), g t ∂volume) =
        (1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹)) := by
    dsimp [g]
    rw [integral_const_mul, integral_const_mul,
      integral_Ioi_mul_exp_neg_T_sq_div_four hT]
  exact hCompare.trans (hSet.trans_eq hEval)

lemma shevtsovaPrawitzFnTerm_le_exp_decay_from_sqrtPsi_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ)
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hfirst :
      ∀ t ∈ Set.Icc t0 1,
        |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| ≤
          shevtsovaTheta0 /
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ))
    (hsmallPsi :
      ∀ t ∈ Set.Icc t0 1,
        shevtsovaKappa *
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ) *
          |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| ≤ 1 / 4) :
    shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      (1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹)) := by
  have hK :
      IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
        (Set.Icc t0 1) :=
    integrableOn_shevtsovaPrawitzKernel_norm_Icc_t0_one ht0 ht0le
  have hLeft :=
    integrableOn_shevtsovaPrawitzFn_integrand_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N t0 T hK
  have hRight :
      IntegrableOn
        (fun t : ℝ => (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4))
        (Set.Icc t0 1) := by
    exact (by fun_prop :
      Continuous fun t : ℝ =>
        (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4)).integrableOn_Icc
  have hCompare :
      shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
        ∫ t in Set.Icc t0 1,
          (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4) ∂volume := by
    unfold shevtsovaPrawitzFnTerm
    refine setIntegral_mono_on hLeft hRight measurableSet_Icc ?_
    intro t ht
    have hKernel :
        ‖shevtsovaPrawitzKernel t‖ ≤ 1 / t0 :=
      shevtsovaPrawitzKernel_norm_le_inv_t0_of_mem_Icc_t0_one
        ht0 ht0le ht
    have hFnSqrt :
        shevtsovaFnAbs P X m σ N (T * t) ≤
          (Real.sqrt
            (1 - shevtsovaPsi
              (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
              (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N :=
      shevtsovaFnAbs_le_sqrt_one_sub_shevtsovaPsi_pow_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE N
        (t := T * t) (hfirst t ht)
    have hSqrtExp :
        (Real.sqrt
          (1 - shevtsovaPsi
            (Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ)))
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ))) ^ N ≤
          Real.exp (-((T * t) ^ 2) / 4) :=
      sqrt_one_sub_shevtsovaPsi_pow_le_exp_neg_quarter_of_first_branch_scaled
        (N := N) hN (t := T * t)
        (ε := 2 * Real.sqrt 2 * berryEsseenRho X P m σ)
        (hfirst t ht) (hsmallPsi t ht)
    have hFn :
        shevtsovaFnAbs P X m σ N (T * t) ≤
          Real.exp (-((T * t) ^ 2) / 4) :=
      hFnSqrt.trans hSqrtExp
    have hInv_nonneg : 0 ≤ 1 / t0 := by positivity
    calc
      ‖shevtsovaPrawitzKernel t‖ * shevtsovaFnAbs P X m σ N (T * t)
          ≤ (1 / t0) * shevtsovaFnAbs P X m σ N (T * t) :=
            mul_le_mul_of_nonneg_right hKernel
              (shevtsovaFnAbs_nonneg P X m σ N (T * t))
      _ ≤ (1 / t0) * Real.exp (-((T * t) ^ 2) / 4) :=
            mul_le_mul_of_nonneg_left hFn hInv_nonneg
      _ = (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4) := by
            ring_nf
  exact hCompare.trans
    (integral_Icc_inv_t0_mul_exp_neg_T_sq_div_four_le
      (t0 := t0) (T := T) ht0 hT)

lemma two_mul_shevtsovaPrawitzFnTerm_le_exp_decay_from_sqrtPsi_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ)
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hfirst :
      ∀ t ∈ Set.Icc t0 1,
        |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| ≤
          shevtsovaTheta0 /
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ))
    (hsmallPsi :
      ∀ t ∈ Set.Icc t0 1,
        shevtsovaKappa *
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ) *
          |Real.sqrt 2 * ((T * t) / Real.sqrt (N : ℝ))| ≤ 1 / 4) :
    2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzFnTerm_le_exp_decay_from_sqrtPsi_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hN t0 T ht0 ht0le hT hfirst hsmallPsi)
    (by norm_num)

lemma shevtsovaPrawitzFnTerm_le_exp_decay_from_sqrtPsi_of_cutoff_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ)
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hFirstCut :
      4 * berryEsseenRho X P m σ * |T| ≤
        shevtsovaTheta0 * Real.sqrt (N : ℝ))
    (hSmallPsiCut :
      16 * shevtsovaKappa * berryEsseenRho X P m σ * |T| ≤
        Real.sqrt (N : ℝ)) :
    shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      (1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹)) := by
  have hrho_pos : 0 < berryEsseenRho X P m σ := by
    exact zero_lt_one.trans_le
      (one_le_berryEsseenRho_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE)
  exact
    shevtsovaPrawitzFnTerm_le_exp_decay_from_sqrtPsi_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hN t0 T ht0 ht0le hT
      (shevtsovaPrawitzFnFirstBranch_of_cutoff_bound
        (N := N) hN (rho := berryEsseenRho X P m σ)
        (t0 := t0) (T := T) hrho_pos ht0.le hFirstCut)
      (shevtsovaPrawitzFnSqrtPsiSmall_of_cutoff_bound
        (N := N) hN (rho := berryEsseenRho X P m σ)
        (t0 := t0) (T := T) hrho_pos.le ht0.le hSmallPsiCut)

lemma two_mul_shevtsovaPrawitzFnTerm_le_exp_decay_from_sqrtPsi_of_cutoff_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ)
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hFirstCut :
      4 * berryEsseenRho X P m σ * |T| ≤
        shevtsovaTheta0 * Real.sqrt (N : ℝ))
    (hSmallPsiCut :
      16 * shevtsovaKappa * berryEsseenRho X P m σ * |T| ≤
        Real.sqrt (N : ℝ)) :
    2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzFnTerm_le_exp_decay_from_sqrtPsi_of_cutoff_bound
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hN t0 T ht0 ht0le hT hFirstCut hSmallPsiCut)
    (by norm_num)

lemma shevtsovaPrawitzFnTerm_le_exp_decay_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ)
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hWindow :
      ∀ t ∈ Set.Icc t0 1,
        ((T * t) / Real.sqrt (N : ℝ)) ^ 2 ≤ 1)
    (hSmall :
      ∀ t ∈ Set.Icc t0 1,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt (N : ℝ)| ≤ 1) :
    shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      (1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹)) := by
  have hK :
      IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
        (Set.Icc t0 1) :=
    integrableOn_shevtsovaPrawitzKernel_norm_Icc_t0_one ht0 ht0le
  have hLeft :=
    integrableOn_shevtsovaPrawitzFn_integrand_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N t0 T hK
  have hRight :
      IntegrableOn
        (fun t : ℝ => (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4))
        (Set.Icc t0 1) := by
    exact (by fun_prop :
      Continuous fun t : ℝ =>
        (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4)).integrableOn_Icc
  have hCompare :
      shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
        ∫ t in Set.Icc t0 1,
          (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4) ∂volume := by
    unfold shevtsovaPrawitzFnTerm
    refine setIntegral_mono_on hLeft hRight measurableSet_Icc ?_
    intro t ht
    have hKernel :
        ‖shevtsovaPrawitzKernel t‖ ≤ 1 / t0 :=
      shevtsovaPrawitzKernel_norm_le_inv_t0_of_mem_Icc_t0_one
        ht0 ht0le ht
    have hFn :
        shevtsovaFnAbs P X m σ N (T * t) ≤
          Real.exp (-((T * t) ^ 2) / 4) :=
      shevtsovaFnAbs_le_exp_neg_quarter_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE hN
        (t := T * t) (hWindow t ht) (hSmall t ht)
    have hInv_nonneg : 0 ≤ 1 / t0 := by positivity
    calc
      ‖shevtsovaPrawitzKernel t‖ * shevtsovaFnAbs P X m σ N (T * t)
          ≤ (1 / t0) * shevtsovaFnAbs P X m σ N (T * t) :=
            mul_le_mul_of_nonneg_right hKernel
              (shevtsovaFnAbs_nonneg P X m σ N (T * t))
      _ ≤ (1 / t0) * Real.exp (-((T * t) ^ 2) / 4) :=
            mul_le_mul_of_nonneg_left hFn hInv_nonneg
      _ = (1 / t0) * Real.exp (-(T ^ 2 * t ^ 2) / 4) := by
            ring_nf
  exact hCompare.trans
    (integral_Icc_inv_t0_mul_exp_neg_T_sq_div_four_le
      (t0 := t0) (T := T) ht0 hT)

lemma two_mul_shevtsovaPrawitzFnTerm_le_exp_decay_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ)
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hWindow :
      ∀ t ∈ Set.Icc t0 1,
        ((T * t) / Real.sqrt (N : ℝ)) ^ 2 ≤ 1)
    (hSmall :
      ∀ t ∈ Set.Icc t0 1,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt (N : ℝ)| ≤ 1) :
    2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzFnTerm_le_exp_decay_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hN t0 T ht0 ht0le hT hWindow hSmall)
    (by norm_num)

lemma shevtsovaPrawitzRnWindow_of_cutoff_bound
    {n : ℕ} {t0 T : ℝ} (ht0 : 0 ≤ t0)
    (hCut : (T * t0) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ)) :
    ∀ t ∈ Set.Icc (0 : ℝ) t0,
      (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
  intro t ht
  have habs : |T * t| ≤ |T * t0| := by
    rw [abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left ht.2 (abs_nonneg T)
  exact (sq_le_sq.mpr habs).trans hCut

lemma shevtsovaPrawitzRnSmall_of_cutoff_bound
    {n : ℕ} {rho t0 T : ℝ} (hrho : 0 ≤ rho) (ht0 : 0 ≤ t0)
    (hCut :
      rho * |T * t0| ≤
        (4 / 3 : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)) :
    ∀ t ∈ Set.Icc (0 : ℝ) t0,
      rho * |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3 := by
  have hN_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt_pos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr hN_pos
  intro t ht
  have habs : |T * t| ≤ |T * t0| := by
    rw [abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left ht.2 (abs_nonneg T)
  have hscaled : rho * |T * t| ≤ rho * |T * t0| :=
    mul_le_mul_of_nonneg_left habs hrho
  calc
    rho * |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)|
        = rho * |T * t| / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
          rw [abs_div, abs_of_pos hsqrt_pos]
          ring
    _ ≤ ((4 / 3 : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)) /
          Real.sqrt ((n + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (hscaled.trans hCut) hsqrt_pos.le
    _ = 4 / 3 := by
          field_simp [hsqrt_pos.ne']

lemma shevtsovaPrawitzFnWindow_of_cutoff_bound
    {N : ℕ} (hN : 0 < N) {t0 T : ℝ} (ht0 : 0 ≤ t0)
    (hCut : T ^ 2 ≤ (N : ℝ)) :
    ∀ t ∈ Set.Icc t0 1,
      ((T * t) / Real.sqrt (N : ℝ)) ^ 2 ≤ 1 := by
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt_sq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hN_pos.le
  intro t ht
  have ht_nonneg : 0 ≤ t := ht0.trans ht.1
  have ht_abs_le_one : |t| ≤ 1 := by
    rw [abs_of_nonneg ht_nonneg]
    exact ht.2
  have hscaled : |T * t| ≤ |T| := by
    rw [abs_mul]
    simpa using
      mul_le_mul_of_nonneg_left ht_abs_le_one (abs_nonneg T)
  have hsquare : (T * t) ^ 2 ≤ T ^ 2 :=
    sq_le_sq.mpr hscaled
  calc
    ((T * t) / Real.sqrt (N : ℝ)) ^ 2
        = (T * t) ^ 2 / (N : ℝ) := by
          rw [div_pow, hsqrt_sq]
    _ ≤ T ^ 2 / (N : ℝ) :=
          div_le_div_of_nonneg_right hsquare hN_pos.le
    _ ≤ 1 := by
          rw [div_le_iff₀ hN_pos]
          simpa using hCut

lemma shevtsovaPrawitzFnSmall_of_cutoff_bound
    {N : ℕ} (hN : 0 < N) {rho t0 T : ℝ}
    (hrho : 0 ≤ rho) (ht0 : 0 ≤ t0)
    (hCut :
      (2 / 3 : ℝ) * rho * |T| ≤ Real.sqrt (N : ℝ)) :
    ∀ t ∈ Set.Icc t0 1,
      (2 / 3 : ℝ) * rho *
        |(T * t) / Real.sqrt (N : ℝ)| ≤ 1 := by
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr hN_pos
  have hcoef_nonneg : 0 ≤ (2 / 3 : ℝ) * rho := by positivity
  intro t ht
  have ht_nonneg : 0 ≤ t := ht0.trans ht.1
  have ht_abs_le_one : |t| ≤ 1 := by
    rw [abs_of_nonneg ht_nonneg]
    exact ht.2
  have hscaled_abs : |T * t| ≤ |T| := by
    rw [abs_mul]
    simpa using
      mul_le_mul_of_nonneg_left ht_abs_le_one (abs_nonneg T)
  have hscaled :
      (2 / 3 : ℝ) * rho * |T * t| ≤
        (2 / 3 : ℝ) * rho * |T| :=
    mul_le_mul_of_nonneg_left hscaled_abs hcoef_nonneg
  calc
    (2 / 3 : ℝ) * rho *
        |(T * t) / Real.sqrt (N : ℝ)|
        = ((2 / 3 : ℝ) * rho * |T * t|) /
            Real.sqrt (N : ℝ) := by
          rw [abs_div, abs_of_pos hsqrt_pos]
          ring
    _ ≤ Real.sqrt (N : ℝ) / Real.sqrt (N : ℝ) :=
          div_le_div_of_nonneg_right (hscaled.trans hCut) hsqrt_pos.le
    _ = 1 := by
          field_simp [hsqrt_pos.ne']

lemma shevtsovaPrawitzFnTerm_le_exp_decay_of_cutoff_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ)
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hWindowCut : T ^ 2 ≤ (N : ℝ))
    (hSmallCut :
      (2 / 3 : ℝ) * berryEsseenRho X P m σ * |T| ≤
        Real.sqrt (N : ℝ)) :
    shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      (1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹)) := by
  have hrho_nonneg : 0 ≤ berryEsseenRho X P m σ := by
    have hrho_one : 1 ≤ berryEsseenRho X P m σ :=
      one_le_berryEsseenRho_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE
    nlinarith
  exact
    shevtsovaPrawitzFnTerm_le_exp_decay_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hN t0 T ht0 ht0le hT
      (shevtsovaPrawitzFnWindow_of_cutoff_bound
        (N := N) hN ht0.le hWindowCut)
      (shevtsovaPrawitzFnSmall_of_cutoff_bound
        (N := N) hN hrho_nonneg ht0.le hSmallCut)

lemma two_mul_shevtsovaPrawitzFnTerm_le_exp_decay_of_cutoff_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} (hN : 0 < N) (t0 T : ℝ)
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hWindowCut : T ^ 2 ≤ (N : ℝ))
    (hSmallCut :
      (2 / 3 : ℝ) * berryEsseenRho X P m σ * |T| ≤
        Real.sqrt (N : ℝ)) :
    2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzFnTerm_le_exp_decay_of_cutoff_bound
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hN t0 T ht0 ht0le hT hWindowCut hSmallCut)
    (by norm_num)

lemma shevtsovaPrawitzFnTerm_le_inv_t0_of_pos_le_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ) (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) :
    shevtsovaPrawitzFnTerm P X m σ N t0 T ≤ 1 / t0 := by
  have hK :
      IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
        (Set.Icc t0 1) :=
    integrableOn_shevtsovaPrawitzKernel_norm_Icc_t0_one ht0 ht0le
  exact
    (shevtsovaPrawitzFnTerm_le_kernelIntegral_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N t0 T hK).trans
      (integral_Icc_t0_one_shevtsovaPrawitzKernel_norm_le_inv
        (t0 := t0) ht0 ht0le)

lemma two_mul_shevtsovaPrawitzFnTerm_le_two_div_t0_of_pos_le_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ) (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) :
    2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤ 2 * (1 / t0) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzFnTerm_le_inv_t0_of_pos_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE N t0 T ht0 ht0le)
    (by norm_num)

lemma shevtsovaPrawitzFnTerm_le_one_sub_of_half_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ) (hhalf : 1 / 2 ≤ t0) (ht0_le_one : t0 ≤ 1) :
    shevtsovaPrawitzFnTerm P X m σ N t0 T ≤ 1 - t0 := by
  have hK :
      IntegrableOn (fun t : ℝ => ‖shevtsovaPrawitzKernel t‖)
        (Set.Icc t0 1) :=
    integrableOn_shevtsovaPrawitzKernel_norm_Icc_of_half_le hhalf
  exact
    (shevtsovaPrawitzFnTerm_le_kernelIntegral_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE N t0 T hK).trans
      (integral_Icc_shevtsovaPrawitzKernel_norm_le_one_sub_of_half_le
        hhalf ht0_le_one)

lemma two_mul_shevtsovaPrawitzFnTerm_le_two_mul_one_sub_of_half_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) (N : ℕ)
    (t0 T : ℝ) (hhalf : 1 / 2 ≤ t0) (ht0_le_one : t0 ≤ 1) :
    2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤
      2 * (1 - t0) := by
  exact mul_le_mul_of_nonneg_left
    (shevtsovaPrawitzFnTerm_le_one_sub_of_half_le
      (P := P) (X := X) (m := m) (σ := σ)
      hBE N t0 T hhalf ht0_le_one)
    (by norm_num)

lemma shevtsovaPrawitzSmoothingBound_le_of_term_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {m σ : ℝ} {N : ℕ} {t0 T B₁ B₂ B₃ B₄ : ℝ}
    (h₁ : 2 * shevtsovaPrawitzRnTerm P X m σ N t0 T ≤ B₁)
    (h₂ : 2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤ B₂)
    (h₃ : 2 * shevtsovaPrawitzGaussianKernelTerm t0 T ≤ B₃)
    (h₄ : (1 / Real.pi) * shevtsovaPrawitzGaussianTailTerm t0 T ≤ B₄) :
    shevtsovaPrawitzSmoothingBound P X m σ N t0 T ≤
      B₁ + B₂ + B₃ + B₄ := by
  rw [shevtsovaPrawitzSmoothingBound_eq_terms]
  linarith

lemma shevtsovaPrawitzSmoothingBound_le_of_term_bounds_trans
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {m σ : ℝ} {N : ℕ} {t0 T B₁ B₂ B₃ B₄ B : ℝ}
    (h₁ : 2 * shevtsovaPrawitzRnTerm P X m σ N t0 T ≤ B₁)
    (h₂ : 2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤ B₂)
    (h₃ : 2 * shevtsovaPrawitzGaussianKernelTerm t0 T ≤ B₃)
    (h₄ : (1 / Real.pi) * shevtsovaPrawitzGaussianTailTerm t0 T ≤ B₄)
    (hB : B₁ + B₂ + B₃ + B₄ ≤ B) :
    shevtsovaPrawitzSmoothingBound P X m σ N t0 T ≤ B :=
  (shevtsovaPrawitzSmoothingBound_le_of_term_bounds
    (P := P) (X := X) (m := m) (σ := σ) (N := N)
    (t0 := t0) (T := T) h₁ h₂ h₃ h₄).trans hB

lemma shevtsovaPrawitzSmoothingBound_le_current_explicit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 T : ℝ}
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3) :
    shevtsovaPrawitzSmoothingBound P X m σ (n + 1) t0 T ≤
      2 * ((6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ)) +
      2 * (1 / t0) +
      3 * t0 +
      (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹) := by
  exact shevtsovaPrawitzSmoothingBound_le_of_term_bounds
    (P := P) (X := X) (m := m) (σ := σ) (N := n + 1)
    (t0 := t0) (T := T)
    (B₁ := 2 * ((6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ)))
    (B₂ := 2 * (1 / t0))
    (B₃ := 3 * t0)
    (B₄ := (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹))
    (two_mul_shevtsovaPrawitzRnTerm_le_two_mul_durrettRate_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T ht0le hWindow hSmall)
    (two_mul_shevtsovaPrawitzFnTerm_le_two_div_t0_of_pos_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE (n + 1) t0 T ht0 ht0le)
    (two_mul_shevtsovaPrawitzGaussianKernelTerm_le_three_mul
      (t0 := t0) (T := T) ht0.le ht0le)
    (one_div_pi_mul_shevtsovaPrawitzGaussianTailTerm_le
      (t0 := t0) (T := T) ht0 hT)

lemma shevtsovaPrawitzSmoothingBound_le_exp_decay_explicit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 T : ℝ}
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hRnWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hRnSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3)
    (hFnWindow :
      ∀ t ∈ Set.Icc t0 1,
        ((T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 1)
    (hFnSmall :
      ∀ t ∈ Set.Icc t0 1,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    shevtsovaPrawitzSmoothingBound P X m σ (n + 1) t0 T ≤
      2 * ((6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ)) +
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) +
      3 * t0 +
      (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹) := by
  exact shevtsovaPrawitzSmoothingBound_le_of_term_bounds
    (P := P) (X := X) (m := m) (σ := σ) (N := n + 1)
    (t0 := t0) (T := T)
    (B₁ := 2 * ((6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ)))
    (B₂ := 2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))))
    (B₃ := 3 * t0)
    (B₄ := (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹))
    (two_mul_shevtsovaPrawitzRnTerm_le_two_mul_durrettRate_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T ht0le hRnWindow hRnSmall)
    (two_mul_shevtsovaPrawitzFnTerm_le_exp_decay_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE (Nat.succ_pos n) t0 T ht0 ht0le hT hFnWindow hFnSmall)
    (two_mul_shevtsovaPrawitzGaussianKernelTerm_le_three_mul
      (t0 := t0) (T := T) ht0.le ht0le)
    (one_div_pi_mul_shevtsovaPrawitzGaussianTailTerm_le
      (t0 := t0) (T := T) ht0 hT)

lemma shevtsovaPrawitzSmoothingBound_le_localRn_exp_decay_explicit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 T : ℝ}
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hRnWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hRnSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3)
    (hFnWindow :
      ∀ t ∈ Set.Icc t0 1,
        ((T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 1)
    (hFnSmall :
      ∀ t ∈ Set.Icc t0 1,
        (2 / 3 : ℝ) * berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1) :
    shevtsovaPrawitzSmoothingBound P X m σ (n + 1) t0 T ≤
      2 *
        (((1 / 6 : ℝ) * berryEsseenRho X P m σ * |T| ^ 3 /
            Real.sqrt ((n + 1 : ℕ) : ℝ)) * (t0 ^ 3 / 3) +
          (|T| ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) * (t0 ^ 4 / 4)) +
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) +
      3 * t0 +
      (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹) := by
  exact shevtsovaPrawitzSmoothingBound_le_of_term_bounds
    (P := P) (X := X) (m := m) (σ := σ) (N := n + 1)
    (t0 := t0) (T := T)
    (B₁ := 2 *
        (((1 / 6 : ℝ) * berryEsseenRho X P m σ * |T| ^ 3 /
            Real.sqrt ((n + 1 : ℕ) : ℝ)) * (t0 ^ 3 / 3) +
          (|T| ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) * (t0 ^ 4 / 4)))
    (B₂ := 2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))))
    (B₃ := 3 * t0)
    (B₄ := (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹))
    (two_mul_shevtsovaPrawitzRnTerm_le_two_mul_localPolynomial_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn ht0.le ht0le hRnWindow hRnSmall)
    (two_mul_shevtsovaPrawitzFnTerm_le_exp_decay_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE (Nat.succ_pos n) t0 T ht0 ht0le hT hFnWindow hFnSmall)
    (two_mul_shevtsovaPrawitzGaussianKernelTerm_le_three_mul
      (t0 := t0) (T := T) ht0.le ht0le)
    (one_div_pi_mul_shevtsovaPrawitzGaussianTailTerm_le
      (t0 := t0) (T := T) ht0 hT)

lemma shevtsovaPrawitzSmoothingBound_le_exp_decay_from_sqrtPsi_explicit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 T : ℝ}
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hRnWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hRnSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3)
    (hFnFirst :
      ∀ t ∈ Set.Icc t0 1,
        |Real.sqrt 2 * ((T * t) /
          Real.sqrt ((n + 1 : ℕ) : ℝ))| ≤
          shevtsovaTheta0 /
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ))
    (hFnSmallPsi :
      ∀ t ∈ Set.Icc t0 1,
        shevtsovaKappa *
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ) *
          |Real.sqrt 2 * ((T * t) /
            Real.sqrt ((n + 1 : ℕ) : ℝ))| ≤ 1 / 4) :
    shevtsovaPrawitzSmoothingBound P X m σ (n + 1) t0 T ≤
      2 * ((6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ)) +
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) +
      3 * t0 +
      (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹) := by
  exact shevtsovaPrawitzSmoothingBound_le_of_term_bounds
    (P := P) (X := X) (m := m) (σ := σ) (N := n + 1)
    (t0 := t0) (T := T)
    (B₁ := 2 * ((6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ)))
    (B₂ := 2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))))
    (B₃ := 3 * t0)
    (B₄ := (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹))
    (two_mul_shevtsovaPrawitzRnTerm_le_two_mul_durrettRate_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn t0 T ht0le hRnWindow hRnSmall)
    (two_mul_shevtsovaPrawitzFnTerm_le_exp_decay_from_sqrtPsi_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE (Nat.succ_pos n) t0 T ht0 ht0le hT hFnFirst hFnSmallPsi)
    (two_mul_shevtsovaPrawitzGaussianKernelTerm_le_three_mul
      (t0 := t0) (T := T) ht0.le ht0le)
    (one_div_pi_mul_shevtsovaPrawitzGaussianTailTerm_le
      (t0 := t0) (T := T) ht0 hT)

lemma shevtsovaPrawitzSmoothingBound_le_localRn_exp_decay_from_sqrtPsi_explicit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 T : ℝ}
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hRnWindow :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        (T * t) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hRnSmall :
      ∀ t ∈ Set.Icc (0 : ℝ) t0,
        berryEsseenRho X P m σ *
          |(T * t) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 4 / 3)
    (hFnFirst :
      ∀ t ∈ Set.Icc t0 1,
        |Real.sqrt 2 * ((T * t) /
          Real.sqrt ((n + 1 : ℕ) : ℝ))| ≤
          shevtsovaTheta0 /
            (2 * Real.sqrt 2 * berryEsseenRho X P m σ))
    (hFnSmallPsi :
      ∀ t ∈ Set.Icc t0 1,
        shevtsovaKappa *
          (2 * Real.sqrt 2 * berryEsseenRho X P m σ) *
          |Real.sqrt 2 * ((T * t) /
            Real.sqrt ((n + 1 : ℕ) : ℝ))| ≤ 1 / 4) :
    shevtsovaPrawitzSmoothingBound P X m σ (n + 1) t0 T ≤
      2 *
        (((1 / 6 : ℝ) * berryEsseenRho X P m σ * |T| ^ 3 /
            Real.sqrt ((n + 1 : ℕ) : ℝ)) * (t0 ^ 3 / 3) +
          (|T| ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) * (t0 ^ 4 / 4)) +
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) +
      3 * t0 +
      (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹) := by
  exact shevtsovaPrawitzSmoothingBound_le_of_term_bounds
    (P := P) (X := X) (m := m) (σ := σ) (N := n + 1)
    (t0 := t0) (T := T)
    (B₁ := 2 *
        (((1 / 6 : ℝ) * berryEsseenRho X P m σ * |T| ^ 3 /
            Real.sqrt ((n + 1 : ℕ) : ℝ)) * (t0 ^ 3 / 3) +
          (|T| ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) * (t0 ^ 4 / 4)))
    (B₂ := 2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))))
    (B₃ := 3 * t0)
    (B₄ := (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹))
    (two_mul_shevtsovaPrawitzRnTerm_le_two_mul_localPolynomial_of_t0_le_half
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn ht0.le ht0le hRnWindow hRnSmall)
    (two_mul_shevtsovaPrawitzFnTerm_le_exp_decay_from_sqrtPsi_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ)
      hBE (Nat.succ_pos n) t0 T ht0 ht0le hT hFnFirst hFnSmallPsi)
    (two_mul_shevtsovaPrawitzGaussianKernelTerm_le_three_mul
      (t0 := t0) (T := T) ht0.le ht0le)
    (one_div_pi_mul_shevtsovaPrawitzGaussianTailTerm_le
      (t0 := t0) (T := T) ht0 hT)

lemma shevtsovaPrawitzSmoothingBound_le_exp_decay_of_cutoff_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 T : ℝ}
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hRnWindowCut :
      (T * t0) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hRnSmallCut :
      berryEsseenRho X P m σ * |T * t0| ≤
        (4 / 3 : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hFnWindowCut :
      T ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hFnSmallCut :
      (2 / 3 : ℝ) * berryEsseenRho X P m σ * |T| ≤
        Real.sqrt ((n + 1 : ℕ) : ℝ)) :
    shevtsovaPrawitzSmoothingBound P X m σ (n + 1) t0 T ≤
      2 * ((6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ)) +
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) +
      3 * t0 +
      (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹) := by
  have hrho_nonneg : 0 ≤ berryEsseenRho X P m σ := by
    have hrho_one : 1 ≤ berryEsseenRho X P m σ :=
      one_le_berryEsseenRho_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE
    nlinarith
  exact
    shevtsovaPrawitzSmoothingBound_le_exp_decay_explicit
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn ht0 ht0le hT
      (shevtsovaPrawitzRnWindow_of_cutoff_bound
        (n := n) ht0.le hRnWindowCut)
      (shevtsovaPrawitzRnSmall_of_cutoff_bound
        (n := n) hrho_nonneg ht0.le hRnSmallCut)
      (shevtsovaPrawitzFnWindow_of_cutoff_bound
        (N := n + 1) (Nat.succ_pos n) ht0.le hFnWindowCut)
      (shevtsovaPrawitzFnSmall_of_cutoff_bound
        (N := n + 1) (Nat.succ_pos n) hrho_nonneg ht0.le
        hFnSmallCut)

lemma shevtsovaPrawitzSmoothingBound_le_localRn_exp_decay_of_cutoff_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 T : ℝ}
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hRnWindowCut :
      (T * t0) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hRnSmallCut :
      berryEsseenRho X P m σ * |T * t0| ≤
        (4 / 3 : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hFnWindowCut :
      T ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hFnSmallCut :
      (2 / 3 : ℝ) * berryEsseenRho X P m σ * |T| ≤
        Real.sqrt ((n + 1 : ℕ) : ℝ)) :
    shevtsovaPrawitzSmoothingBound P X m σ (n + 1) t0 T ≤
      2 *
        (((1 / 6 : ℝ) * berryEsseenRho X P m σ * |T| ^ 3 /
            Real.sqrt ((n + 1 : ℕ) : ℝ)) * (t0 ^ 3 / 3) +
          (|T| ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) * (t0 ^ 4 / 4)) +
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) +
      3 * t0 +
      (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹) := by
  have hrho_nonneg : 0 ≤ berryEsseenRho X P m σ := by
    have hrho_one : 1 ≤ berryEsseenRho X P m σ :=
      one_le_berryEsseenRho_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE
    nlinarith
  exact
    shevtsovaPrawitzSmoothingBound_le_localRn_exp_decay_explicit
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn ht0 ht0le hT
      (shevtsovaPrawitzRnWindow_of_cutoff_bound
        (n := n) ht0.le hRnWindowCut)
      (shevtsovaPrawitzRnSmall_of_cutoff_bound
        (n := n) hrho_nonneg ht0.le hRnSmallCut)
      (shevtsovaPrawitzFnWindow_of_cutoff_bound
        (N := n + 1) (Nat.succ_pos n) ht0.le hFnWindowCut)
      (shevtsovaPrawitzFnSmall_of_cutoff_bound
        (N := n + 1) (Nat.succ_pos n) hrho_nonneg ht0.le
        hFnSmallCut)

lemma shevtsovaPrawitzSmoothingBound_le_exp_decay_from_sqrtPsi_of_cutoff_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 T : ℝ}
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hRnWindowCut :
      (T * t0) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hRnSmallCut :
      berryEsseenRho X P m σ * |T * t0| ≤
        (4 / 3 : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hFnFirstCut :
      4 * berryEsseenRho X P m σ * |T| ≤
        shevtsovaTheta0 * Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hFnSmallPsiCut :
      16 * shevtsovaKappa * berryEsseenRho X P m σ * |T| ≤
        Real.sqrt ((n + 1 : ℕ) : ℝ)) :
    shevtsovaPrawitzSmoothingBound P X m σ (n + 1) t0 T ≤
      2 * ((6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ)) +
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) +
      3 * t0 +
      (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹) := by
  have hrho_pos : 0 < berryEsseenRho X P m σ := by
    exact zero_lt_one.trans_le
      (one_le_berryEsseenRho_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE)
  exact
    shevtsovaPrawitzSmoothingBound_le_exp_decay_from_sqrtPsi_explicit
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn ht0 ht0le hT
      (shevtsovaPrawitzRnWindow_of_cutoff_bound
        (n := n) ht0.le hRnWindowCut)
      (shevtsovaPrawitzRnSmall_of_cutoff_bound
        (n := n) hrho_pos.le ht0.le hRnSmallCut)
      (shevtsovaPrawitzFnFirstBranch_of_cutoff_bound
        (N := n + 1) (Nat.succ_pos n)
        (rho := berryEsseenRho X P m σ)
        (t0 := t0) (T := T) hrho_pos ht0.le hFnFirstCut)
      (shevtsovaPrawitzFnSqrtPsiSmall_of_cutoff_bound
        (N := n + 1) (Nat.succ_pos n)
        (rho := berryEsseenRho X P m σ)
        (t0 := t0) (T := T) hrho_pos.le ht0.le hFnSmallPsiCut)

lemma shevtsovaPrawitzSmoothingBound_le_localRn_exp_decay_from_sqrtPsi_of_cutoff_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 T : ℝ}
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) (hT : T ≠ 0)
    (hRnWindowCut :
      (T * t0) ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ))
    (hRnSmallCut :
      berryEsseenRho X P m σ * |T * t0| ≤
        (4 / 3 : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hFnFirstCut :
      4 * berryEsseenRho X P m σ * |T| ≤
        shevtsovaTheta0 * Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hFnSmallPsiCut :
      16 * shevtsovaKappa * berryEsseenRho X P m σ * |T| ≤
        Real.sqrt ((n + 1 : ℕ) : ℝ)) :
    shevtsovaPrawitzSmoothingBound P X m σ (n + 1) t0 T ≤
      2 *
        (((1 / 6 : ℝ) * berryEsseenRho X P m σ * |T| ^ 3 /
            Real.sqrt ((n + 1 : ℕ) : ℝ)) * (t0 ^ 3 / 3) +
          (|T| ^ 4 / (8 * ((n + 1 : ℕ) : ℝ))) * (t0 ^ 4 / 4)) +
      2 * ((1 / t0) * ((1 / t0) * (2 * (T ^ 2)⁻¹))) +
      3 * t0 +
      (1 / Real.pi) * ((1 / t0 ^ 2) * (T ^ 2)⁻¹) := by
  have hrho_pos : 0 < berryEsseenRho X P m σ := by
    exact zero_lt_one.trans_le
      (one_le_berryEsseenRho_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE)
  exact
    shevtsovaPrawitzSmoothingBound_le_localRn_exp_decay_from_sqrtPsi_explicit
      (P := P) (X := X) (m := m) (σ := σ)
      hBE hn ht0 ht0le hT
      (shevtsovaPrawitzRnWindow_of_cutoff_bound
        (n := n) ht0.le hRnWindowCut)
      (shevtsovaPrawitzRnSmall_of_cutoff_bound
        (n := n) hrho_pos.le ht0.le hRnSmallCut)
      (shevtsovaPrawitzFnFirstBranch_of_cutoff_bound
        (N := n + 1) (Nat.succ_pos n)
        (rho := berryEsseenRho X P m σ)
        (t0 := t0) (T := T) hrho_pos ht0.le hFnFirstCut)
      (shevtsovaPrawitzFnSqrtPsiSmall_of_cutoff_bound
        (N := n + 1) (Nat.succ_pos n)
        (rho := berryEsseenRho X P m σ)
        (t0 := t0) (T := T) hrho_pos.le ht0.le hFnSmallPsiCut)

/-- Four-term Prawitz functional bound at the standard first-branch cutoff
`T = sqrt (n + 1) / (16κρ)`.  This packages all scalar side conditions needed
by the `sqrt(1 - ψ)^N` exponential-decay route. -/
lemma shevtsovaPrawitzSmoothingBound_le_exp_decay_from_sqrtPsi_standard_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 : ℝ}
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) :
    shevtsovaPrawitzSmoothingBound P X m σ (n + 1) t0
        (shevtsovaSqrtPsiCutoffT
          (berryEsseenRho X P m σ) (n + 1)) ≤
      2 * ((6 / 5) * berryEsseenRho X P m σ /
          Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 / ((n + 1 : ℕ) : ℝ)) +
      2 * ((1 / t0) * ((1 / t0) *
        (2 * ((shevtsovaSqrtPsiCutoffT
          (berryEsseenRho X P m σ) (n + 1)) ^ 2)⁻¹))) +
      3 * t0 +
      (1 / Real.pi) * ((1 / t0 ^ 2) *
        ((shevtsovaSqrtPsiCutoffT
          (berryEsseenRho X P m σ) (n + 1)) ^ 2)⁻¹) := by
  have hN : 0 < n + 1 := Nat.succ_pos n
  have hrho_lower : 1 ≤ berryEsseenRho X P m σ :=
    one_le_berryEsseenRho_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE
  have hrho_pos : 0 < berryEsseenRho X P m σ := by
    exact zero_lt_one.trans_le hrho_lower
  have hT :
      shevtsovaSqrtPsiCutoffT
        (berryEsseenRho X P m σ) (n + 1) ≠ 0 :=
    (shevtsovaSqrtPsiCutoffT_pos
      (N := n + 1) hN (rho := berryEsseenRho X P m σ) hrho_pos).ne'
  exact
    shevtsovaPrawitzSmoothingBound_le_exp_decay_from_sqrtPsi_of_cutoff_bounds
      (P := P) (X := X) (m := m) (σ := σ)
      (n := n) (t0 := t0)
      (T := shevtsovaSqrtPsiCutoffT
        (berryEsseenRho X P m σ) (n + 1))
      hBE hn ht0 ht0le hT
      (shevtsovaPrawitzRnWindowCut_of_sqrtPsiCutoff
        (N := n + 1) hN
        (rho := berryEsseenRho X P m σ) (t0 := t0)
        hrho_lower ht0.le ht0le)
      (shevtsovaPrawitzRnSmallCut_of_sqrtPsiCutoff
        (N := n + 1) hN
        (rho := berryEsseenRho X P m σ) (t0 := t0)
        hrho_lower ht0.le ht0le)
      (shevtsovaPrawitzFnFirstCut_of_sqrtPsiCutoff
        (N := n + 1) hN
        (rho := berryEsseenRho X P m σ) hrho_pos)
      (shevtsovaPrawitzFnSmallPsiCut_of_sqrtPsiCutoff
        (N := n + 1) hN
        (rho := berryEsseenRho X P m σ) hrho_pos)

/-- Variant of the standard-cutoff Prawitz functional bound that keeps the
finite-window polynomial bound for the near-zero `r_n` component. -/
lemma shevtsovaPrawitzSmoothingBound_le_localRn_exp_decay_from_sqrtPsi_standard_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {n : ℕ} (hn : 9 ≤ n) {t0 : ℝ}
    (ht0 : 0 < t0) (ht0le : t0 ≤ 1 / 2) :
    shevtsovaPrawitzSmoothingBound P X m σ (n + 1) t0
        (shevtsovaSqrtPsiCutoffT
          (berryEsseenRho X P m σ) (n + 1)) ≤
      2 *
        (((1 / 6 : ℝ) * berryEsseenRho X P m σ *
            |shevtsovaSqrtPsiCutoffT
              (berryEsseenRho X P m σ) (n + 1)| ^ 3 /
            Real.sqrt ((n + 1 : ℕ) : ℝ)) * (t0 ^ 3 / 3) +
          (|shevtsovaSqrtPsiCutoffT
              (berryEsseenRho X P m σ) (n + 1)| ^ 4 /
              (8 * ((n + 1 : ℕ) : ℝ))) * (t0 ^ 4 / 4)) +
      2 * ((1 / t0) * ((1 / t0) *
        (2 * ((shevtsovaSqrtPsiCutoffT
          (berryEsseenRho X P m σ) (n + 1)) ^ 2)⁻¹))) +
      3 * t0 +
      (1 / Real.pi) * ((1 / t0 ^ 2) *
        ((shevtsovaSqrtPsiCutoffT
          (berryEsseenRho X P m σ) (n + 1)) ^ 2)⁻¹) := by
  have hN : 0 < n + 1 := Nat.succ_pos n
  have hrho_lower : 1 ≤ berryEsseenRho X P m σ :=
    one_le_berryEsseenRho_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE
  have hrho_pos : 0 < berryEsseenRho X P m σ := by
    exact zero_lt_one.trans_le hrho_lower
  have hT :
      shevtsovaSqrtPsiCutoffT
        (berryEsseenRho X P m σ) (n + 1) ≠ 0 :=
    (shevtsovaSqrtPsiCutoffT_pos
      (N := n + 1) hN (rho := berryEsseenRho X P m σ) hrho_pos).ne'
  exact
    shevtsovaPrawitzSmoothingBound_le_localRn_exp_decay_from_sqrtPsi_of_cutoff_bounds
      (P := P) (X := X) (m := m) (σ := σ)
      (n := n) (t0 := t0)
      (T := shevtsovaSqrtPsiCutoffT
        (berryEsseenRho X P m σ) (n + 1))
      hBE hn ht0 ht0le hT
      (shevtsovaPrawitzRnWindowCut_of_sqrtPsiCutoff
        (N := n + 1) hN
        (rho := berryEsseenRho X P m σ) (t0 := t0)
        hrho_lower ht0.le ht0le)
      (shevtsovaPrawitzRnSmallCut_of_sqrtPsiCutoff
        (N := n + 1) hN
        (rho := berryEsseenRho X P m σ) (t0 := t0)
        hrho_lower ht0.le ht0le)
      (shevtsovaPrawitzFnFirstCut_of_sqrtPsiCutoff
        (N := n + 1) hN
        (rho := berryEsseenRho X P m σ) hrho_pos)
      (shevtsovaPrawitzFnSmallPsiCut_of_sqrtPsiCutoff
        (N := n + 1) hN
        (rho := berryEsseenRho X P m σ) hrho_pos)

lemma shevtsovaPrawitzSmoothingBound_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m σ : ℝ) (N : ℕ) {t0 T : ℝ}
    (ht0 : 0 < t0) :
    0 ≤ shevtsovaPrawitzSmoothingBound P X m σ N t0 T := by
  unfold shevtsovaPrawitzSmoothingBound
  have hI₁ :
      0 ≤ ∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t‖ *
          shevtsovaRn P X m σ N (T * t) ∂volume := by
    exact integral_nonneg fun t =>
      mul_nonneg (norm_nonneg _)
        (shevtsovaRn_nonneg P X m σ N (T * t))
  have hI₂ :
      0 ≤ ∫ t in Set.Icc t0 1,
        ‖shevtsovaPrawitzKernel t‖ *
          shevtsovaFnAbs P X m σ N (T * t) ∂volume := by
    exact integral_nonneg fun t =>
      mul_nonneg (norm_nonneg _)
        (shevtsovaFnAbs_nonneg P X m σ N (T * t))
  have hI₃ :
      0 ≤ ∫ t in Set.Icc (0 : ℝ) t0,
        ‖shevtsovaPrawitzKernel t -
            shevtsovaIMul ((2 * Real.pi * t)⁻¹)‖ *
          Real.exp (-(T ^ 2 * t ^ 2) / 2) ∂volume := by
    exact integral_nonneg fun t =>
      mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hI₄ :
      0 ≤ ∫ t in Set.Ioi t0,
        Real.exp (-(T ^ 2 * t ^ 2) / 2) / t ∂volume := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (Real.exp_pos _).le (ht0.trans ht).le
  have htail :
      0 ≤ (1 / Real.pi : ℝ) *
        (∫ t in Set.Ioi t0,
          Real.exp (-(T ^ 2 * t ^ 2) / 2) / t ∂volume) := by
    exact mul_nonneg (by positivity) hI₄
  nlinarith

/-- Shevtsova's structural Berry-Esseen coefficient `0.33554`, recorded as an
exact rational.  The analytic theorem using this constant is not assumed here;
these constants only support proved arithmetic and interface bridges. -/
def shevtsovaStructuralCoefficient : ℝ :=
  (33554 : ℝ) / 100000

/-- Shevtsova's additive structural constant `0.415`, recorded as an exact
rational. -/
def shevtsovaStructuralShift : ℝ :=
  (83 : ℝ) / 200

/-- Shevtsova's optimization parameter
`ε = (ρ + 0.415) / sqrt N`. -/
def shevtsovaOptimizationEpsilon (rho : ℝ) (N : ℕ) : ℝ :=
  (rho + shevtsovaStructuralShift) / Real.sqrt (N : ℝ)

/-- The classical absolute constant `0.4748` obtained from Shevtsova's
structural estimate and the moment lower bound `ρ ≥ 1`. -/
def shevtsovaAbsoluteConstant : ℝ :=
  (1187 : ℝ) / 2500

/-- Shevtsova's structural rate
`0.33554 * (ρ + 0.415) / sqrt N`. -/
def shevtsovaStructuralRate (rho : ℝ) (N : ℕ) : ℝ :=
  shevtsovaStructuralCoefficient * (rho + shevtsovaStructuralShift) /
    Real.sqrt (N : ℝ)

lemma shevtsovaStructuralCoefficient_pos :
    0 < shevtsovaStructuralCoefficient := by
  unfold shevtsovaStructuralCoefficient
  norm_num

lemma shevtsovaStructuralShift_pos :
    0 < shevtsovaStructuralShift := by
  unfold shevtsovaStructuralShift
  norm_num

lemma shevtsovaOptimizationEpsilon_nonneg {rho : ℝ} {N : ℕ}
    (hrho : 0 ≤ rho) :
    0 ≤ shevtsovaOptimizationEpsilon rho N := by
  unfold shevtsovaOptimizationEpsilon
  exact div_nonneg
    (add_nonneg hrho shevtsovaStructuralShift_pos.le)
    (Real.sqrt_nonneg _)

lemma shevtsovaStructuralRate_eq_coeff_mul_optimizationEpsilon
    (rho : ℝ) (N : ℕ) :
    shevtsovaStructuralRate rho N =
      shevtsovaStructuralCoefficient *
        shevtsovaOptimizationEpsilon rho N := by
  unfold shevtsovaStructuralRate shevtsovaOptimizationEpsilon
  ring

lemma shevtsovaAbsoluteConstant_lt_one :
    shevtsovaAbsoluteConstant < 1 := by
  unfold shevtsovaAbsoluteConstant
  norm_num

/-- Exact arithmetic behind Shevtsova's advertised `0.4748` absolute
constant. -/
lemma shevtsovaStructuralCoefficient_mul_shift_le_absolute
    {rho : ℝ} (hrho : 1 ≤ rho) :
    shevtsovaStructuralCoefficient *
        (rho + shevtsovaStructuralShift) ≤
      shevtsovaAbsoluteConstant * rho := by
  unfold shevtsovaStructuralCoefficient shevtsovaStructuralShift
    shevtsovaAbsoluteConstant
  nlinarith [hrho]

/-- Shevtsova's structural rate is bounded by the classical `0.4748` rate
whenever the standardized third absolute moment satisfies `ρ ≥ 1`. -/
lemma shevtsovaStructuralRate_le_berryEsseenRate_absolute
    {rho : ℝ} (hrho : 1 ≤ rho) (N : ℕ) :
    shevtsovaStructuralRate rho N ≤
      berryEsseenRate shevtsovaAbsoluteConstant rho N := by
  exact div_le_div_of_nonneg_right
    (shevtsovaStructuralCoefficient_mul_shift_le_absolute hrho)
    (Real.sqrt_nonneg _)

/-- Since `0.4748 < 1`, Shevtsova's structural rate would immediately imply
the displayed HDP `C = 1` rate. -/
lemma shevtsovaStructuralRate_le_berryEsseenRate_one
    {rho : ℝ} (hrho : 1 ≤ rho) (N : ℕ) :
    shevtsovaStructuralRate rho N ≤ berryEsseenRate 1 rho N := by
  have hrho_nonneg : 0 ≤ rho := by nlinarith [hrho]
  exact (shevtsovaStructuralRate_le_berryEsseenRate_absolute
    (rho := rho) hrho N).trans
      (berryEsseenRate_mono_constant
        shevtsovaAbsoluteConstant_lt_one.le hrho_nonneg N)

/-- Law-level bridge from a future fully formalized Shevtsova structural CDF
estimate to the displayed HDP `C = 1` CDF estimate. -/
theorem measureCDFErrorLE_of_shevtsovaStructuralRate
    {ν : Measure ℝ} {rho : ℝ} (hrho : 1 ≤ rho) (N : ℕ)
    (hCDF : measureCDFErrorLE ν standardNormalMeasure
      (shevtsovaStructuralRate rho N)) :
    measureCDFErrorLE ν standardNormalMeasure
      (berryEsseenRate 1 rho N) :=
  measureCDFErrorLE_mono hCDF
    (shevtsovaStructuralRate_le_berryEsseenRate_one hrho N)

/-- Book-facing bridge: a future Shevtsova structural law-level estimate for
the normalized sum gives the exact displayed closed-tail event bound. -/
theorem berryEsseenClosedUpperTail_event_of_shevtsovaStructuralRate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (_hN : 0 < N) (t : ℝ)
    (hCDF :
      measureCDFErrorLE
        (P.map (normalizedSum X m σ N)) standardNormalMeasure
        (shevtsovaStructuralRate (berryEsseenRho X P m σ) N)) :
    |P.real {ω | t ≤ normalizedSum X m σ N ω} -
        standardNormalMeasure.real (Set.Ici t)| ≤
      berryEsseenRate 1 (berryEsseenRho X P m σ) N := by
  have hZ : AEMeasurable (normalizedSum X m σ N) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable N
  letI : IsProbabilityMeasure (P.map (normalizedSum X m σ N)) :=
    Measure.isProbabilityMeasure_map hZ
  have hrho : 1 ≤ berryEsseenRho X P m σ :=
    one_le_berryEsseenRho_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE
  have hCDF_one :
      measureCDFErrorLE
        (P.map (normalizedSum X m σ N)) standardNormalMeasure
        (berryEsseenRate 1 (berryEsseenRho X P m σ) N) :=
    measureCDFErrorLE_of_shevtsovaStructuralRate
      (ν := P.map (normalizedSum X m σ N))
      (rho := berryEsseenRho X P m σ) hrho N hCDF
  have hClosed :
      measureClosedUpperTailErrorLE
        (P.map (normalizedSum X m σ N)) standardNormalMeasure
        (berryEsseenRate 1 (berryEsseenRho X P m σ) N) :=
    measureClosedUpperTailErrorLE_of_measureCDFErrorLE hCDF_one
  have hmap :
      (P.map (normalizedSum X m σ N)).real (Set.Ici t) =
        P.real {ω | t ≤ normalizedSum X m σ N ω} := by
    rw [measureReal_def,
      Measure.map_apply_of_aemeasurable hZ measurableSet_Ici]
    rfl
  simpa [measureClosedUpperTailErrorLE, hmap] using hClosed t

/-- A bound on Shevtsova's `Δ_n` by the structural rate is already the
measure-level structural CDF estimate needed by the exact-constant bridge. -/
theorem measureCDFErrorLE_of_shevtsovaDelta_le_structuralRate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ}
    (hDelta :
      shevtsovaDelta P X m σ N ≤
        shevtsovaStructuralRate (berryEsseenRho X P m σ) N) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ N)) standardNormalMeasure
      (shevtsovaStructuralRate (berryEsseenRho X P m σ) N) := by
  simpa [shevtsovaNormalizedSumLaw] using
    measureCDFErrorLE_of_shevtsovaDelta_le
      (P := P) (X := X) (m := m) (σ := σ) hBE hDelta

/-- Book-facing endpoint for a future fully formalized proof of
`Δ_n ≤ 0.33554 * (ρ + 0.415) / sqrt N`. -/
theorem berryEsseenClosedUpperTail_event_of_shevtsovaDelta_le_structuralRate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (hN : 0 < N) (t : ℝ)
    (hDelta :
      shevtsovaDelta P X m σ N ≤
        shevtsovaStructuralRate (berryEsseenRho X P m σ) N) :
    |P.real {ω | t ≤ normalizedSum X m σ N ω} -
        standardNormalMeasure.real (Set.Ici t)| ≤
      berryEsseenRate 1 (berryEsseenRho X P m σ) N :=
  berryEsseenClosedUpperTail_event_of_shevtsovaStructuralRate
    (P := P) (X := X) (m := m) (σ := σ) hBE N hN t
    (measureCDFErrorLE_of_shevtsovaDelta_le_structuralRate
      (P := P) (X := X) (m := m) (σ := σ) hBE hDelta)

/-- If Prawitz's smoothing inequality bounds `Δ_n` by the checked Prawitz
functional and the later numerical/analytic estimate bounds that functional by
Shevtsova's structural rate, then the structural CDF estimate follows. -/
theorem measureCDFErrorLE_of_shevtsovaPrawitzSmoothingBound_le_structuralRate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} {t0 T : ℝ}
    (hPrawitz :
      shevtsovaDelta P X m σ N ≤
        shevtsovaPrawitzSmoothingBound P X m σ N t0 T)
    (hBound :
      shevtsovaPrawitzSmoothingBound P X m σ N t0 T ≤
        shevtsovaStructuralRate (berryEsseenRho X P m σ) N) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ N)) standardNormalMeasure
      (shevtsovaStructuralRate (berryEsseenRho X P m σ) N) :=
  measureCDFErrorLE_of_shevtsovaDelta_le_structuralRate
    (P := P) (X := X) (m := m) (σ := σ) hBE
    (hPrawitz.trans hBound)

/-- Certificate-facing Prawitz bridge: if each of the four named Prawitz
terms has a checked bound and those bounds sum to Shevtsova's structural rate,
then the structural CDF estimate follows. -/
theorem measureCDFErrorLE_of_shevtsovaPrawitzTermBounds_le_structuralRate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    {N : ℕ} {t0 T B₁ B₂ B₃ B₄ : ℝ}
    (hPrawitz :
      shevtsovaDelta P X m σ N ≤
        shevtsovaPrawitzSmoothingBound P X m σ N t0 T)
    (h₁ : 2 * shevtsovaPrawitzRnTerm P X m σ N t0 T ≤ B₁)
    (h₂ : 2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤ B₂)
    (h₃ : 2 * shevtsovaPrawitzGaussianKernelTerm t0 T ≤ B₃)
    (h₄ : (1 / Real.pi) * shevtsovaPrawitzGaussianTailTerm t0 T ≤ B₄)
    (hSum :
      B₁ + B₂ + B₃ + B₄ ≤
        shevtsovaStructuralRate (berryEsseenRho X P m σ) N) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ N)) standardNormalMeasure
      (shevtsovaStructuralRate (berryEsseenRho X P m σ) N) :=
  measureCDFErrorLE_of_shevtsovaPrawitzSmoothingBound_le_structuralRate
    (P := P) (X := X) (m := m) (σ := σ) hBE hPrawitz
    (shevtsovaPrawitzSmoothingBound_le_of_term_bounds_trans
      (P := P) (X := X) (m := m) (σ := σ) (N := N)
      (t0 := t0) (T := T) h₁ h₂ h₃ h₄ hSum)

/-- Exact displayed closed-tail endpoint for the Prawitz route: once the
Prawitz smoothing inequality and its Shevtsova structural numerical bound are
formalized, no additional probability plumbing remains. -/
theorem berryEsseenClosedUpperTail_event_of_shevtsovaPrawitzSmoothingBound_le_structuralRate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (hN : 0 < N) (t : ℝ) {t0 T : ℝ}
    (hPrawitz :
      shevtsovaDelta P X m σ N ≤
        shevtsovaPrawitzSmoothingBound P X m σ N t0 T)
    (hBound :
      shevtsovaPrawitzSmoothingBound P X m σ N t0 T ≤
        shevtsovaStructuralRate (berryEsseenRho X P m σ) N) :
    |P.real {ω | t ≤ normalizedSum X m σ N ω} -
        standardNormalMeasure.real (Set.Ici t)| ≤
      berryEsseenRate 1 (berryEsseenRho X P m σ) N :=
  berryEsseenClosedUpperTail_event_of_shevtsovaStructuralRate
    (P := P) (X := X) (m := m) (σ := σ) hBE N hN t
    (measureCDFErrorLE_of_shevtsovaPrawitzSmoothingBound_le_structuralRate
      (P := P) (X := X) (m := m) (σ := σ) hBE hPrawitz hBound)

/-- Exact displayed closed-tail endpoint fed by four separate Prawitz
certificate-term bounds. -/
theorem berryEsseenClosedUpperTail_event_of_shevtsovaPrawitzTermBounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (hN : 0 < N) (t : ℝ) {t0 T B₁ B₂ B₃ B₄ : ℝ}
    (hPrawitz :
      shevtsovaDelta P X m σ N ≤
        shevtsovaPrawitzSmoothingBound P X m σ N t0 T)
    (h₁ : 2 * shevtsovaPrawitzRnTerm P X m σ N t0 T ≤ B₁)
    (h₂ : 2 * shevtsovaPrawitzFnTerm P X m σ N t0 T ≤ B₂)
    (h₃ : 2 * shevtsovaPrawitzGaussianKernelTerm t0 T ≤ B₃)
    (h₄ : (1 / Real.pi) * shevtsovaPrawitzGaussianTailTerm t0 T ≤ B₄)
    (hSum :
      B₁ + B₂ + B₃ + B₄ ≤
        shevtsovaStructuralRate (berryEsseenRho X P m σ) N) :
    |P.real {ω | t ≤ normalizedSum X m σ N ω} -
        standardNormalMeasure.real (Set.Ici t)| ≤
      berryEsseenRate 1 (berryEsseenRho X P m σ) N :=
  berryEsseenClosedUpperTail_event_of_shevtsovaStructuralRate
    (P := P) (X := X) (m := m) (σ := σ) hBE N hN t
    (measureCDFErrorLE_of_shevtsovaPrawitzTermBounds_le_structuralRate
      (P := P) (X := X) (m := m) (σ := σ) hBE
      hPrawitz h₁ h₂ h₃ h₄ hSum)

lemma polyaTailBudget_one_standard_cutoff_eq
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho) :
    polyaTailBudget 1 (Real.sqrt (N : ℝ) / (16 * rho)) =
      384 * rho / (Real.pi * Real.sqrt (N : ℝ)) := by
  have hsqrt_ne :
      Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN : 0 < (N : ℝ))).ne'
  have hden_ne : (16 : ℝ) * rho ≠ 0 :=
    mul_ne_zero (by norm_num) hrho.ne'
  unfold polyaTailBudget
  field_simp [Real.pi_pos.ne', hsqrt_ne, hden_ne, hrho.ne']
  ring

lemma polyaTailBudget_two_fifths_standard_cutoff_eq
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho) :
    polyaTailBudget (2 / 5) (Real.sqrt (N : ℝ) / (16 * rho)) =
      (768 / 5) * rho / (Real.pi * Real.sqrt (N : ℝ)) := by
  have hsqrt_ne :
      Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN : 0 < (N : ℝ))).ne'
  have hden_ne : (16 : ℝ) * rho ≠ 0 :=
    mul_ne_zero (by norm_num) hrho.ne'
  unfold polyaTailBudget
  field_simp [Real.pi_pos.ne', hsqrt_ne, hden_ne, hrho.ne']
  ring

lemma berryEsseen_standard_cutoff_sq_le
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 1 ≤ rho) :
    (Real.sqrt (N : ℝ) / (16 * rho)) ^ 2 ≤ (N : ℝ) := by
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  have hden_pos : 0 < (16 : ℝ) * rho := by positivity
  have hden_sq_ge_one : 1 ≤ ((16 : ℝ) * rho) ^ 2 := by
    nlinarith [hrho]
  calc
    (Real.sqrt (N : ℝ) / (16 * rho)) ^ 2
        = (N : ℝ) / ((16 : ℝ) * rho) ^ 2 := by
          rw [div_pow, Real.sq_sqrt hN_nonneg]
    _ ≤ (N : ℝ) := by
          rw [div_le_iff₀ (sq_pos_of_pos hden_pos)]
          nlinarith

lemma berryEsseen_standard_cutoff_bound
    {N : ℕ} {rho : ℝ} (hrho : 1 ≤ rho) :
    16 * rho * (Real.sqrt (N : ℝ) / (16 * rho)) ≤
      Real.sqrt (N : ℝ) := by
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  calc
    16 * rho * (Real.sqrt (N : ℝ) / (16 * rho))
        = Real.sqrt (N : ℝ) := by
          field_simp [hrho_pos.ne']
    _ ≤ Real.sqrt (N : ℝ) := le_rfl

lemma berryEsseenBudget_standard_cutoff_le_rate
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 1 ≤ rho) :
    (1 / Real.pi) *
        (256 * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ)) +
      polyaTailBudget 1 (Real.sqrt (N : ℝ) / (16 * rho)) ≤
        berryEsseenRate 216 rho N := by
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN_ge_one_real : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr hN_pos_real
  have hsqrt_ge_one : 1 ≤ Real.sqrt (N : ℝ) := by
    simpa using Real.sqrt_le_sqrt hN_ge_one_real
  have hsqrt_sq :
      Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hN_pos_real.le
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  have htermN :
      4 / (N : ℝ) ≤ 4 * rho / Real.sqrt (N : ℝ) := by
    have hprod : 4 ≤ 4 * rho * Real.sqrt (N : ℝ) := by
      nlinarith [hrho, hsqrt_ge_one]
    calc
      4 / (N : ℝ)
          = 4 / Real.sqrt (N : ℝ) ^ 2 := by rw [hsqrt_sq]
      _ ≤ (4 * rho * Real.sqrt (N : ℝ)) /
            Real.sqrt (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hprod (sq_nonneg _)
      _ = 4 * rho / Real.sqrt (N : ℝ) := by
          field_simp [hsqrt_pos.ne']
  have hfourier_arg :
      256 * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ) ≤
        260 * rho / Real.sqrt (N : ℝ) := by
    calc
      256 * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ)
          ≤ 256 * rho / Real.sqrt (N : ℝ) +
              4 * rho / Real.sqrt (N : ℝ) :=
            add_le_add (le_refl _) htermN
      _ = 260 * rho / Real.sqrt (N : ℝ) := by ring
  have hcoef_nonneg : 0 ≤ (1 / Real.pi : ℝ) :=
    div_nonneg zero_le_one Real.pi_pos.le
  have hfourier_nonneg :
      0 ≤ 260 * rho / Real.sqrt (N : ℝ) := by positivity
  have hfourier :
      (1 / Real.pi) *
          (256 * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ)) ≤
        (1 / 3) * (260 * rho / Real.sqrt (N : ℝ)) := by
    calc
      (1 / Real.pi) *
          (256 * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ))
          ≤ (1 / Real.pi) *
              (260 * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hfourier_arg hcoef_nonneg
      _ ≤ (1 / 3) * (260 * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_right one_div_pi_le_one_div_three hfourier_nonneg
  have htail_eq :=
    polyaTailBudget_one_standard_cutoff_eq (N := N) hN hrho_pos
  have htail_nonneg :
      0 ≤ 384 * rho / Real.sqrt (N : ℝ) := by positivity
  have htail :
      polyaTailBudget 1 (Real.sqrt (N : ℝ) / (16 * rho)) ≤
        (1 / 3) * (384 * rho / Real.sqrt (N : ℝ)) := by
    rw [htail_eq]
    calc
      384 * rho / (Real.pi * Real.sqrt (N : ℝ))
          = (1 / Real.pi) *
              (384 * rho / Real.sqrt (N : ℝ)) := by
            field_simp [Real.pi_pos.ne', hsqrt_pos.ne']
      _ ≤ (1 / 3) * (384 * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_right one_div_pi_le_one_div_three htail_nonneg
  calc
    (1 / Real.pi) *
        (256 * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ)) +
      polyaTailBudget 1 (Real.sqrt (N : ℝ) / (16 * rho))
        ≤ (1 / 3) * (260 * rho / Real.sqrt (N : ℝ)) +
            (1 / 3) * (384 * rho / Real.sqrt (N : ℝ)) :=
          add_le_add hfourier htail
    _ = (644 / 3) * rho / Real.sqrt (N : ℝ) := by ring
    _ ≤ 216 * rho / Real.sqrt (N : ℝ) := by
          gcongr
          norm_num
    _ = berryEsseenRate 216 rho N := by
          rw [berryEsseenRate]

lemma berryEsseenBudget_standard_cutoff_le_rate_two_fifths
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 1 ≤ rho) :
    (1 / Real.pi) *
        ((432 / 5) * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ)) +
      polyaTailBudget (2 / 5) (Real.sqrt (N : ℝ) / (16 * rho)) ≤
        berryEsseenRate 78 rho N := by
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN_ge_one_real : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr hN_pos_real
  have hsqrt_ge_one : 1 ≤ Real.sqrt (N : ℝ) := by
    simpa using Real.sqrt_le_sqrt hN_ge_one_real
  have hsqrt_sq :
      Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hN_pos_real.le
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  have htermN :
      4 / (N : ℝ) ≤ 4 * rho / Real.sqrt (N : ℝ) := by
    have hprod : 4 ≤ 4 * rho * Real.sqrt (N : ℝ) := by
      nlinarith [hrho, hsqrt_ge_one]
    calc
      4 / (N : ℝ)
          = 4 / Real.sqrt (N : ℝ) ^ 2 := by rw [hsqrt_sq]
      _ ≤ (4 * rho * Real.sqrt (N : ℝ)) /
            Real.sqrt (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hprod (sq_nonneg _)
      _ = 4 * rho / Real.sqrt (N : ℝ) := by
          field_simp [hsqrt_pos.ne']
  have hfourier_arg :
      (432 / 5) * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ) ≤
        (452 / 5) * rho / Real.sqrt (N : ℝ) := by
    calc
      (432 / 5) * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ)
          ≤ (432 / 5) * rho / Real.sqrt (N : ℝ) +
              4 * rho / Real.sqrt (N : ℝ) :=
            add_le_add (le_refl _) htermN
      _ = (452 / 5) * rho / Real.sqrt (N : ℝ) := by ring
  have hcoef_nonneg : 0 ≤ (1 / Real.pi : ℝ) :=
    div_nonneg zero_le_one Real.pi_pos.le
  have hfourier_nonneg :
      0 ≤ (452 / 5) * rho / Real.sqrt (N : ℝ) := by positivity
  have hfourier :
      (1 / Real.pi) *
          ((432 / 5) * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ)) ≤
        (50 / 157) * ((452 / 5) * rho / Real.sqrt (N : ℝ)) := by
    calc
      (1 / Real.pi) *
          ((432 / 5) * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ))
          ≤ (1 / Real.pi) *
              ((452 / 5) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hfourier_arg hcoef_nonneg
      _ ≤ (50 / 157) * ((452 / 5) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_right one_div_pi_le_fifty_div_one_fifty_seven
              hfourier_nonneg
  have htail_eq :=
    polyaTailBudget_two_fifths_standard_cutoff_eq (N := N) hN hrho_pos
  have htail_nonneg :
      0 ≤ (768 / 5) * rho / Real.sqrt (N : ℝ) := by positivity
  have htail :
      polyaTailBudget (2 / 5) (Real.sqrt (N : ℝ) / (16 * rho)) ≤
        (50 / 157) * ((768 / 5) * rho / Real.sqrt (N : ℝ)) := by
    rw [htail_eq]
    calc
      (768 / 5) * rho / (Real.pi * Real.sqrt (N : ℝ))
          = (1 / Real.pi) *
              ((768 / 5) * rho / Real.sqrt (N : ℝ)) := by
            field_simp [Real.pi_pos.ne', hsqrt_pos.ne']
      _ ≤ (50 / 157) * ((768 / 5) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_right one_div_pi_le_fifty_div_one_fifty_seven
              htail_nonneg
  calc
    (1 / Real.pi) *
        ((432 / 5) * rho / Real.sqrt (N : ℝ) + 4 / (N : ℝ)) +
      polyaTailBudget (2 / 5) (Real.sqrt (N : ℝ) / (16 * rho))
        ≤ (50 / 157) * ((452 / 5) * rho / Real.sqrt (N : ℝ)) +
            (50 / 157) * ((768 / 5) * rho / Real.sqrt (N : ℝ)) :=
          add_le_add hfourier htail
    _ = (12200 / 157) * rho / Real.sqrt (N : ℝ) := by ring
    _ ≤ 78 * rho / Real.sqrt (N : ℝ) := by
          gcongr
          norm_num
    _ = berryEsseenRate 78 rho N := by
          rw [berryEsseenRate]

/-- Polya smoothing tail at the enlarged cutoff allowed by the cubic Taylor
remainder. -/
lemma polyaTailBudget_two_fifths_cubic_cutoff_eq
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho) :
    polyaTailBudget (2 / 5) (3 * Real.sqrt (N : ℝ) / (4 * rho)) =
      (64 / 5) * rho / (Real.pi * Real.sqrt (N : ℝ)) := by
  have hsqrt_ne :
      Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN : 0 < (N : ℝ))).ne'
  have hden_ne : (4 : ℝ) * rho ≠ 0 :=
    mul_ne_zero (by norm_num) hrho.ne'
  unfold polyaTailBudget
  field_simp [Real.pi_pos.ne', hsqrt_ne, hden_ne, hrho.ne']
  ring

lemma berryEsseen_cubic_cutoff_sq_le
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 1 ≤ rho) :
    (3 * Real.sqrt (N : ℝ) / (4 * rho)) ^ 2 ≤ (N : ℝ) := by
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  have hden_pos : 0 < (4 : ℝ) * rho := by positivity
  calc
    (3 * Real.sqrt (N : ℝ) / (4 * rho)) ^ 2
        = 9 * (N : ℝ) / ((4 : ℝ) * rho) ^ 2 := by
          rw [div_pow, mul_pow, Real.sq_sqrt hN_nonneg]
          ring
    _ ≤ (N : ℝ) := by
          rw [div_le_iff₀ (sq_pos_of_pos hden_pos)]
          have hsq : (9 : ℝ) ≤ ((4 : ℝ) * rho) ^ 2 := by
            nlinarith [hrho]
          have hmul :=
            mul_le_mul_of_nonneg_left hsq hN_nonneg
          nlinarith

lemma berryEsseen_cubic_cutoff_bound
    {N : ℕ} {rho : ℝ} (hrho : 1 ≤ rho) :
    (2 / 3 : ℝ) * rho *
        (3 * Real.sqrt (N : ℝ) / (4 * rho)) ≤
      Real.sqrt (N : ℝ) := by
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_nonneg _
  calc
    (2 / 3 : ℝ) * rho *
        (3 * Real.sqrt (N : ℝ) / (4 * rho))
        = Real.sqrt (N : ℝ) / 2 := by
          field_simp [hrho_pos.ne']
          ring
    _ ≤ Real.sqrt (N : ℝ) := by
          nlinarith

lemma berryEsseenBudget_cubic_cutoff_le_rate_two_fifths
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 1 ≤ rho) :
    (1 / Real.pi) *
        ((18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)) +
      polyaTailBudget (2 / 5)
        (3 * Real.sqrt (N : ℝ) / (4 * rho)) ≤
        berryEsseenRate 7 rho N := by
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN_ge_one_real : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr hN_pos_real
  have hsqrt_ge_one : 1 ≤ Real.sqrt (N : ℝ) := by
    simpa using Real.sqrt_le_sqrt hN_ge_one_real
  have hsqrt_sq :
      Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hN_pos_real.le
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  have htermN :
      2 / (N : ℝ) ≤ 2 * rho / Real.sqrt (N : ℝ) := by
    have hprod : 2 ≤ 2 * rho * Real.sqrt (N : ℝ) := by
      nlinarith [hrho, hsqrt_ge_one]
    calc
      2 / (N : ℝ)
          = 2 / Real.sqrt (N : ℝ) ^ 2 := by rw [hsqrt_sq]
      _ ≤ (2 * rho * Real.sqrt (N : ℝ)) /
            Real.sqrt (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hprod (sq_nonneg _)
      _ = 2 * rho / Real.sqrt (N : ℝ) := by
          field_simp [hsqrt_pos.ne']
  have hfourier_arg :
      (18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ) ≤
        (28 / 5) * rho / Real.sqrt (N : ℝ) := by
    calc
      (18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)
          ≤ (18 / 5) * rho / Real.sqrt (N : ℝ) +
              2 * rho / Real.sqrt (N : ℝ) :=
            add_le_add (le_refl _) htermN
      _ = (28 / 5) * rho / Real.sqrt (N : ℝ) := by ring
  have hcoef_nonneg : 0 ≤ (1 / Real.pi : ℝ) :=
    div_nonneg zero_le_one Real.pi_pos.le
  have hfourier_nonneg :
      0 ≤ (28 / 5) * rho / Real.sqrt (N : ℝ) := by positivity
  have hfourier :
      (1 / Real.pi) *
          ((18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)) ≤
        (50 / 157) * ((28 / 5) * rho / Real.sqrt (N : ℝ)) := by
    calc
      (1 / Real.pi) *
          ((18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ))
          ≤ (1 / Real.pi) *
              ((28 / 5) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hfourier_arg hcoef_nonneg
      _ ≤ (50 / 157) * ((28 / 5) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_right one_div_pi_le_fifty_div_one_fifty_seven
              hfourier_nonneg
  have htail_eq :=
    polyaTailBudget_two_fifths_cubic_cutoff_eq (N := N) hN hrho_pos
  have htail_nonneg :
      0 ≤ (64 / 5) * rho / Real.sqrt (N : ℝ) := by positivity
  have htail :
      polyaTailBudget (2 / 5) (3 * Real.sqrt (N : ℝ) / (4 * rho)) ≤
        (50 / 157) * ((64 / 5) * rho / Real.sqrt (N : ℝ)) := by
    rw [htail_eq]
    calc
      (64 / 5) * rho / (Real.pi * Real.sqrt (N : ℝ))
          = (1 / Real.pi) *
              ((64 / 5) * rho / Real.sqrt (N : ℝ)) := by
            field_simp [Real.pi_pos.ne', hsqrt_pos.ne']
      _ ≤ (50 / 157) * ((64 / 5) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_right one_div_pi_le_fifty_div_one_fifty_seven
              htail_nonneg
  calc
    (1 / Real.pi) *
        ((18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)) +
      polyaTailBudget (2 / 5) (3 * Real.sqrt (N : ℝ) / (4 * rho))
        ≤ (50 / 157) * ((28 / 5) * rho / Real.sqrt (N : ℝ)) +
            (50 / 157) * ((64 / 5) * rho / Real.sqrt (N : ℝ)) :=
          add_le_add hfourier htail
    _ = (920 / 157) * rho / Real.sqrt (N : ℝ) := by ring
    _ ≤ 7 * rho / Real.sqrt (N : ℝ) := by
          gcongr
          norm_num
    _ = berryEsseenRate 7 rho N := by
          rw [berryEsseenRate]

/-- Polya smoothing tail at the full cutoff allowed by the exact cubic Taylor
remainder. -/
lemma polyaTailBudget_two_fifths_unit_cutoff_eq
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho) :
    polyaTailBudget (2 / 5) (Real.sqrt (N : ℝ) / rho) =
      (48 / 5) * rho / (Real.pi * Real.sqrt (N : ℝ)) := by
  have hsqrt_ne :
      Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN : 0 < (N : ℝ))).ne'
  unfold polyaTailBudget
  field_simp [Real.pi_pos.ne', hsqrt_ne, hrho.ne']
  ring

lemma berryEsseen_unit_cutoff_sq_le
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 1 ≤ rho) :
    (Real.sqrt (N : ℝ) / rho) ^ 2 ≤ (N : ℝ) := by
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  have hrho_sq_ge_one : 1 ≤ rho ^ 2 := by
    nlinarith [hrho]
  calc
    (Real.sqrt (N : ℝ) / rho) ^ 2
        = (N : ℝ) / rho ^ 2 := by
          rw [div_pow, Real.sq_sqrt hN_nonneg]
    _ ≤ (N : ℝ) := by
          rw [div_le_iff₀ (sq_pos_of_pos hrho_pos)]
          have hmul :=
            mul_le_mul_of_nonneg_left hrho_sq_ge_one hN_nonneg
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

lemma berryEsseen_unit_cutoff_bound
    {N : ℕ} {rho : ℝ} (hrho : 1 ≤ rho) :
    (2 / 3 : ℝ) * rho * (Real.sqrt (N : ℝ) / rho) ≤
      Real.sqrt (N : ℝ) := by
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_nonneg _
  calc
    (2 / 3 : ℝ) * rho * (Real.sqrt (N : ℝ) / rho)
        = (2 / 3 : ℝ) * Real.sqrt (N : ℝ) := by
          field_simp [hrho_pos.ne']
    _ ≤ Real.sqrt (N : ℝ) := by
          nlinarith

/-- Polya smoothing tail at Durrett's cutoff `4√N/(3ρ)`. -/
lemma polyaTailBudget_two_fifths_durrett_cutoff_eq
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho) :
    polyaTailBudget (2 / 5) (4 * Real.sqrt (N : ℝ) / (3 * rho)) =
      (36 / 5) * rho / (Real.pi * Real.sqrt (N : ℝ)) := by
  have hsqrt_ne :
      Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN : 0 < (N : ℝ))).ne'
  have hden_ne : (3 : ℝ) * rho ≠ 0 :=
    mul_ne_zero (by norm_num) hrho.ne'
  unfold polyaTailBudget
  field_simp [Real.pi_pos.ne', hsqrt_ne, hden_ne, hrho.ne']
  ring

lemma berryEsseen_durrett_cutoff_sq_le
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 1 ≤ rho) :
    (4 * Real.sqrt (N : ℝ) / (3 * rho)) ^ 2 ≤ 2 * (N : ℝ) := by
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  have hden_pos : 0 < (3 : ℝ) * rho := by positivity
  calc
    (4 * Real.sqrt (N : ℝ) / (3 * rho)) ^ 2
        = 16 * (N : ℝ) / ((3 : ℝ) * rho) ^ 2 := by
          rw [div_pow, mul_pow, Real.sq_sqrt hN_nonneg]
          ring
    _ ≤ 2 * (N : ℝ) := by
          rw [div_le_iff₀ (sq_pos_of_pos hden_pos)]
          have hsq : (16 : ℝ) ≤ 2 * ((3 : ℝ) * rho) ^ 2 := by
            nlinarith [hrho]
          have hmul :=
            mul_le_mul_of_nonneg_left hsq hN_nonneg
          nlinarith

lemma berryEsseen_durrett_cutoff_bound
    {N : ℕ} {rho : ℝ} (hrho : 1 ≤ rho) :
    rho * (4 * Real.sqrt (N : ℝ) / (3 * rho)) ≤
      (4 / 3 : ℝ) * Real.sqrt (N : ℝ) := by
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  calc
    rho * (4 * Real.sqrt (N : ℝ) / (3 * rho))
        = (4 / 3 : ℝ) * Real.sqrt (N : ℝ) := by
          field_simp [hrho_pos.ne']
    _ ≤ (4 / 3 : ℝ) * Real.sqrt (N : ℝ) := le_rfl

lemma berryEsseenBudget_durrett_cutoff_le_rate_two_fifths
    {N : ℕ} (hN : 0 < N) (hNlarge : 10 ≤ N)
    {rho : ℝ} (hrho : 1 ≤ rho) :
    (1 / Real.pi) *
        ((6 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)) +
      polyaTailBudget (2 / 5)
        (4 * Real.sqrt (N : ℝ) / (3 * rho)) ≤
        berryEsseenRate 3 rho N := by
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr hN_pos_real
  have hsqrt_sq :
      Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hN_pos_real.le
  have hN_ge_nine : (9 : ℕ) ≤ N := by omega
  have hN_ge_nine_real : (9 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_nine
  have hsqrt_ge_three : (3 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have h := Real.sqrt_le_sqrt hN_ge_nine_real
    norm_num at h
    exact h
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  have htermN :
      2 / (N : ℝ) ≤ (2 / 3 : ℝ) * rho / Real.sqrt (N : ℝ) := by
    have hprod :
        2 * Real.sqrt (N : ℝ) ≤
          ((2 / 3 : ℝ) * rho) * (N : ℝ) := by
      have hbase : (3 : ℝ) ≤ rho * Real.sqrt (N : ℝ) := by
        nlinarith [hrho, hsqrt_ge_three]
      have hbase' : (2 : ℝ) ≤ (2 / 3 : ℝ) * rho * Real.sqrt (N : ℝ) := by
        nlinarith
      calc
        2 * Real.sqrt (N : ℝ)
            ≤ ((2 / 3 : ℝ) * rho * Real.sqrt (N : ℝ)) *
                Real.sqrt (N : ℝ) :=
              mul_le_mul_of_nonneg_right hbase' hsqrt_pos.le
        _ = ((2 / 3 : ℝ) * rho) *
              (Real.sqrt (N : ℝ) ^ 2) := by
              ring
        _ = ((2 / 3 : ℝ) * rho) * (N : ℝ) := by
              rw [hsqrt_sq]
    rw [div_le_div_iff₀ hN_pos_real hsqrt_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
  have hfourier_arg :
      (6 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ) ≤
        (28 / 15) * rho / Real.sqrt (N : ℝ) := by
    calc
      (6 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)
          ≤ (6 / 5) * rho / Real.sqrt (N : ℝ) +
              (2 / 3 : ℝ) * rho / Real.sqrt (N : ℝ) :=
            add_le_add (le_refl _) htermN
      _ = (28 / 15) * rho / Real.sqrt (N : ℝ) := by ring
  have hcoef_nonneg : 0 ≤ (1 / Real.pi : ℝ) :=
    div_nonneg zero_le_one Real.pi_pos.le
  have hfourier_nonneg :
      0 ≤ (28 / 15) * rho / Real.sqrt (N : ℝ) := by positivity
  have hfourier :
      (1 / Real.pi) *
          ((6 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)) ≤
        (50 / 157) * ((28 / 15) * rho / Real.sqrt (N : ℝ)) := by
    calc
      (1 / Real.pi) *
          ((6 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ))
          ≤ (1 / Real.pi) *
              ((28 / 15) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hfourier_arg hcoef_nonneg
      _ ≤ (50 / 157) * ((28 / 15) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_right one_div_pi_le_fifty_div_one_fifty_seven
              hfourier_nonneg
  have htail_eq :=
    polyaTailBudget_two_fifths_durrett_cutoff_eq (N := N) hN hrho_pos
  have htail_nonneg :
      0 ≤ (36 / 5) * rho / Real.sqrt (N : ℝ) := by positivity
  have htail :
      polyaTailBudget (2 / 5) (4 * Real.sqrt (N : ℝ) / (3 * rho)) ≤
        (50 / 157) * ((36 / 5) * rho / Real.sqrt (N : ℝ)) := by
    rw [htail_eq]
    calc
      (36 / 5) * rho / (Real.pi * Real.sqrt (N : ℝ))
          = (1 / Real.pi) *
              ((36 / 5) * rho / Real.sqrt (N : ℝ)) := by
            field_simp [Real.pi_pos.ne', hsqrt_pos.ne']
      _ ≤ (50 / 157) * ((36 / 5) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_right one_div_pi_le_fifty_div_one_fifty_seven
              htail_nonneg
  calc
    (1 / Real.pi) *
        ((6 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)) +
      polyaTailBudget (2 / 5)
        (4 * Real.sqrt (N : ℝ) / (3 * rho))
        ≤ (50 / 157) * ((28 / 15) * rho / Real.sqrt (N : ℝ)) +
            (50 / 157) * ((36 / 5) * rho / Real.sqrt (N : ℝ)) :=
          add_le_add hfourier htail
    _ = (6800 / 2355) * rho / Real.sqrt (N : ℝ) := by ring
    _ ≤ 3 * rho / Real.sqrt (N : ℝ) := by
          gcongr
          norm_num
    _ = berryEsseenRate 3 rho N := by
          rw [berryEsseenRate]

/-- Durrett/Feller final integral-constant calculation at the cutoff
`L = 4√N/(3ρ)`: the locally integrated Fourier majorant, the normal
`2 / 5` Lipschitz constant, the Polya tail term, and the `π` rational bound
combine to the public `C = 3` Berry-Esseen rate. -/
lemma durrettFeller_finalIntegralConstants_durrettCutoff
    {N : ℕ} (hN : 0 < N) (hNlarge : 10 ≤ N)
    {rho : ℝ} (hrho : 1 ≤ rho) :
    (1 / Real.pi) *
        ((6 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)) +
      polyaTailBudget (2 / 5)
        (4 * Real.sqrt (N : ℝ) / (3 * rho)) ≤
        berryEsseenRate 3 rho N :=
  berryEsseenBudget_durrett_cutoff_le_rate_two_fifths hN hNlarge hrho

lemma berryEsseenBudget_unit_cutoff_le_rate_two_fifths
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 1 ≤ rho) :
    (1 / Real.pi) *
        ((18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)) +
      polyaTailBudget (2 / 5) (Real.sqrt (N : ℝ) / rho) ≤
        berryEsseenRate 5 rho N := by
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN_ge_one_real : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr hN_pos_real
  have hsqrt_ge_one : 1 ≤ Real.sqrt (N : ℝ) := by
    simpa using Real.sqrt_le_sqrt hN_ge_one_real
  have hsqrt_sq :
      Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hN_pos_real.le
  have hrho_pos : 0 < rho := by nlinarith [hrho]
  have htermN :
      2 / (N : ℝ) ≤ 2 * rho / Real.sqrt (N : ℝ) := by
    have hprod : 2 ≤ 2 * rho * Real.sqrt (N : ℝ) := by
      nlinarith [hrho, hsqrt_ge_one]
    calc
      2 / (N : ℝ)
          = 2 / Real.sqrt (N : ℝ) ^ 2 := by rw [hsqrt_sq]
      _ ≤ (2 * rho * Real.sqrt (N : ℝ)) /
            Real.sqrt (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hprod (sq_nonneg _)
      _ = 2 * rho / Real.sqrt (N : ℝ) := by
          field_simp [hsqrt_pos.ne']
  have hfourier_arg :
      (18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ) ≤
        (28 / 5) * rho / Real.sqrt (N : ℝ) := by
    calc
      (18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)
          ≤ (18 / 5) * rho / Real.sqrt (N : ℝ) +
              2 * rho / Real.sqrt (N : ℝ) :=
            add_le_add (le_refl _) htermN
      _ = (28 / 5) * rho / Real.sqrt (N : ℝ) := by ring
  have hcoef_nonneg : 0 ≤ (1 / Real.pi : ℝ) :=
    div_nonneg zero_le_one Real.pi_pos.le
  have hfourier_nonneg :
      0 ≤ (28 / 5) * rho / Real.sqrt (N : ℝ) := by positivity
  have hfourier :
      (1 / Real.pi) *
          ((18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)) ≤
        (50 / 157) * ((28 / 5) * rho / Real.sqrt (N : ℝ)) := by
    calc
      (1 / Real.pi) *
          ((18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ))
          ≤ (1 / Real.pi) *
              ((28 / 5) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hfourier_arg hcoef_nonneg
      _ ≤ (50 / 157) * ((28 / 5) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_right one_div_pi_le_fifty_div_one_fifty_seven
              hfourier_nonneg
  have htail_eq :=
    polyaTailBudget_two_fifths_unit_cutoff_eq (N := N) hN hrho_pos
  have htail_nonneg :
      0 ≤ (48 / 5) * rho / Real.sqrt (N : ℝ) := by positivity
  have htail :
      polyaTailBudget (2 / 5) (Real.sqrt (N : ℝ) / rho) ≤
        (50 / 157) * ((48 / 5) * rho / Real.sqrt (N : ℝ)) := by
    rw [htail_eq]
    calc
      (48 / 5) * rho / (Real.pi * Real.sqrt (N : ℝ))
          = (1 / Real.pi) *
              ((48 / 5) * rho / Real.sqrt (N : ℝ)) := by
            field_simp [Real.pi_pos.ne', hsqrt_pos.ne']
      _ ≤ (50 / 157) * ((48 / 5) * rho / Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_right one_div_pi_le_fifty_div_one_fifty_seven
              htail_nonneg
  calc
    (1 / Real.pi) *
        ((18 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)) +
      polyaTailBudget (2 / 5) (Real.sqrt (N : ℝ) / rho)
        ≤ (50 / 157) * ((28 / 5) * rho / Real.sqrt (N : ℝ)) +
            (50 / 157) * ((48 / 5) * rho / Real.sqrt (N : ℝ)) :=
          add_le_add hfourier htail
    _ = (760 / 157) * rho / Real.sqrt (N : ℝ) := by ring
    _ ≤ 5 * rho / Real.sqrt (N : ℝ) := by
          gcongr
          norm_num
    _ = berryEsseenRate 5 rho N := by
          rw [berryEsseenRate]

/-- Measure-level Berry-Esseen theorem obtained from the local Durrett/Feller
Fourier smoothing proof, with an explicit absolute constant. -/
theorem measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_berryEsseenRate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (hN : 0 < N) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ N)) standardNormalMeasure
      (berryEsseenRate 3 (berryEsseenRho X P m σ) N) := by
  let rho := berryEsseenRho X P m σ
  have hrho_lower : 1 ≤ rho := by
    simpa [rho] using one_le_berryEsseenRho_of_hypotheses
      (P := P) (X := X) (m := m) (σ := σ) hBE
  have hrho_nonneg : 0 ≤ rho := by nlinarith [hrho_lower]
  by_cases hNsmall : N < 10
  · have hN_le_nine : N ≤ 9 := by omega
    have hZ : AEMeasurable (normalizedSum X m σ N) P :=
      normalizedSum_aemeasurable (μ := P) hBE.aemeasurable N
    letI : IsProbabilityMeasure (P.map (normalizedSum X m σ N)) :=
      Measure.isProbabilityMeasure_map hZ
    have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
    have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
      Real.sqrt_pos.mpr hN_pos_real
    have hN_le_nine_real : (N : ℝ) ≤ (9 : ℝ) := by exact_mod_cast hN_le_nine
    have hsqrt_le_three : Real.sqrt (N : ℝ) ≤ 3 := by
      have h := Real.sqrt_le_sqrt hN_le_nine_real
      norm_num at h
      exact h
    exact measureCDFErrorLE_mono
      (measureCDFErrorLE_one
        (P.map (normalizedSum X m σ N)) standardNormalMeasure)
      (by
        rw [berryEsseenRate]
        change 1 ≤ (3 * rho) / Real.sqrt (N : ℝ)
        rw [le_div_iff₀ hsqrt_pos]
        have hthree_le : (3 : ℝ) ≤ 3 * rho := by nlinarith
        nlinarith)
  · have hNlarge : 10 ≤ N := by omega
    let n : ℕ := N - 1
    have hn : 9 ≤ n := by omega
    have hsucc : n + 1 = N := by omega
    let L : ℝ := 4 * Real.sqrt (N : ℝ) / (3 * rho)
    have hLpos : 0 < L := by
      have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN
      have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
        Real.sqrt_pos.mpr hN_pos_real
      have hrho_pos : 0 < rho := by nlinarith [hrho_lower]
      exact div_pos (mul_pos (by norm_num) hsqrt_pos)
        (mul_pos (by norm_num) hrho_pos)
    have hLsqN :
        L ^ 2 ≤ 2 * (N : ℝ) := by
      simpa [L] using
        berryEsseen_durrett_cutoff_sq_le (N := N) hN hrho_lower
    have hLsq :
        L ^ 2 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
      simpa [hsucc] using hLsqN
    have hCutN :
        rho * L ≤ (4 / 3 : ℝ) * Real.sqrt (N : ℝ) := by
      simpa [L] using
        berryEsseen_durrett_cutoff_bound (N := N) (rho := rho) hrho_lower
    have hCut :
        berryEsseenRho X P m σ * L ≤
          (4 / 3 : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      simpa [rho, hsucc] using hCutN
    have hmeasure :=
      measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_durrett_rate_two_fifths
        (P := P) (X := X) (m := m) (σ := σ)
        hBE hn hLpos
        (berryEsseenDurrettWindow_of_cutoff_sq (n := n) (L := L) hLsq)
        (berryEsseenDurrettSmall_of_cutoff_bound
          (n := n) (rho := berryEsseenRho X P m σ) (L := L)
          (by simpa [rho] using hrho_nonneg) hCut)
    have hmeasureN :
        measureCDFErrorLE
          (P.map (normalizedSum X m σ N)) standardNormalMeasure
          ((1 / Real.pi) *
            ((6 / 5) * rho / Real.sqrt (N : ℝ) + 2 / (N : ℝ)) +
            polyaTailBudget (2 / 5) L) := by
      simpa [rho, L, hsucc] using hmeasure
    exact measureCDFErrorLE_mono hmeasureN
      (by
        simpa [rho, L] using
          berryEsseenBudget_durrett_cutoff_le_rate_two_fifths
            (N := N) hN hNlarge hrho_lower)

/-- Book-facing Berry-Esseen CDF conclusion with the local smoothing proof
discharged end-to-end. -/
theorem berryEsseenConclusion_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    BerryEsseenConclusion X P m σ 3 := by
  intro N hN
  have hZ : AEMeasurable (normalizedSum X m σ N) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable N
  exact cdfErrorBound_of_measureCDFErrorLE hZ
    (measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_berryEsseenRate
      (P := P) (X := X) (m := m) (σ := σ) hBE N hN)

/-- Strict-upper-tail Berry-Esseen conclusion from the same measure-level
Fourier smoothing theorem. -/
theorem berryEsseenTailConclusion_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    BerryEsseenTailConclusion X P m σ 3 := by
  intro N hN
  have hZ : AEMeasurable (normalizedSum X m σ N) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable N
  letI : IsProbabilityMeasure (P.map (normalizedSum X m σ N)) :=
    Measure.isProbabilityMeasure_map hZ
  exact upperTailErrorBound_of_measureUpperTailErrorLE hZ
    (measureUpperTailErrorLE_of_measureCDFErrorLE
      (measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_berryEsseenRate
        (P := P) (X := X) (m := m) (σ := σ) hBE N hN))

/-- Closed-upper-tail Berry-Esseen conclusion, matching the displayed HDP
event form `{Z_N ≥ t}`. -/
theorem berryEsseenClosedTailConclusion_of_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    BerryEsseenClosedTailConclusion X P m σ 3 := by
  intro N hN
  have hZ : AEMeasurable (normalizedSum X m σ N) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable N
  letI : IsProbabilityMeasure (P.map (normalizedSum X m σ N)) :=
    Measure.isProbabilityMeasure_map hZ
  exact closedUpperTailErrorBound_of_measureClosedUpperTailErrorLE hZ
    (measureClosedUpperTailErrorLE_of_measureCDFErrorLE
      (measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_berryEsseenRate
        (P := P) (X := X) (m := m) (σ := σ) hBE N hN))

/-- Named measure-level Berry-Esseen theorem from the Durrett/Feller
formalization.  This is the direct law-level Kolmogorov-distance statement. -/
theorem berryEsseenMeasureCDF
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (hN : 0 < N) :
    measureCDFErrorLE
      (P.map (normalizedSum X m σ N)) standardNormalMeasure
      (berryEsseenRate 3 (berryEsseenRho X P m σ) N) :=
  measureCDFErrorLE_normalizedSum_standardNormal_of_hypotheses_berryEsseenRate
    (P := P) (X := X) (m := m) (σ := σ) hBE N hN

/-- Named book-facing Berry-Esseen theorem.  It proves the bundled CDF
conclusion from the bundled i.i.d. hypotheses with the explicit formalized
constant `3`. -/
theorem berryEsseen
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    BerryEsseenConclusion X P m σ 3 :=
  berryEsseenConclusion_of_hypotheses (P := P) (X := X) (m := m) (σ := σ) hBE

/-- Named strict-upper-tail Berry-Esseen theorem. -/
theorem berryEsseenUpperTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    BerryEsseenTailConclusion X P m σ 3 :=
  berryEsseenTailConclusion_of_hypotheses
    (P := P) (X := X) (m := m) (σ := σ) hBE

/-- Named closed-upper-tail Berry-Esseen theorem, matching the displayed
HDP event form `{Z_N ≥ t}`. -/
theorem berryEsseenClosedUpperTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ) :
    BerryEsseenClosedTailConclusion X P m σ 3 :=
  berryEsseenClosedTailConclusion_of_hypotheses
    (P := P) (X := X) (m := m) (σ := σ) hBE

/-- Named measure-level closed-upper-tail Berry-Esseen theorem. -/
theorem berryEsseenMeasureClosedUpperTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (hN : 0 < N) :
    measureClosedUpperTailErrorLE
      (P.map (normalizedSum X m σ N)) standardNormalMeasure
      (berryEsseenRate 3 (berryEsseenRho X P m σ) N) := by
  have hZ : AEMeasurable (normalizedSum X m σ N) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable N
  letI : IsProbabilityMeasure (P.map (normalizedSum X m σ N)) :=
    Measure.isProbabilityMeasure_map hZ
  exact measureClosedUpperTailErrorLE_of_measureCDFErrorLE
    (berryEsseenMeasureCDF (P := P) (X := X) (m := m) (σ := σ) hBE N hN)

/-- Promotion lemma for the exact displayed HDP constant.

If a future sharper Berry-Esseen proof gives the measure-level CDF estimate
with some constant `C ≤ 1`, then the pointwise closed-tail event statement
follows with the displayed constant `1`.  This theorem contains no analytic
gap: the only remaining mathematical input is the sharper measure-level CDF
estimate supplied as `hCDF`. -/
theorem berryEsseenClosedUpperTail_event_of_measureCDFErrorLE_le_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ C : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (hC : C ≤ 1)
    (N : ℕ) (_hN : 0 < N) (t : ℝ)
    (hCDF :
      measureCDFErrorLE
        (P.map (normalizedSum X m σ N)) standardNormalMeasure
        (berryEsseenRate C (berryEsseenRho X P m σ) N)) :
    |P.real {ω | t ≤ normalizedSum X m σ N ω} -
        standardNormalMeasure.real (Set.Ici t)| ≤
      berryEsseenRate 1 (berryEsseenRho X P m σ) N := by
  have hZ : AEMeasurable (normalizedSum X m σ N) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable N
  letI : IsProbabilityMeasure (P.map (normalizedSum X m σ N)) :=
    Measure.isProbabilityMeasure_map hZ
  have hrho_nonneg : 0 ≤ berryEsseenRho X P m σ := by
    have hrho_one : 1 ≤ berryEsseenRho X P m σ :=
      one_le_berryEsseenRho_of_hypotheses
        (P := P) (X := X) (m := m) (σ := σ) hBE
    nlinarith
  have hCDF_one :
      measureCDFErrorLE
        (P.map (normalizedSum X m σ N)) standardNormalMeasure
        (berryEsseenRate 1 (berryEsseenRho X P m σ) N) :=
    measureCDFErrorLE_mono hCDF
      (berryEsseenRate_mono_constant hC hrho_nonneg N)
  have hClosed :
      measureClosedUpperTailErrorLE
        (P.map (normalizedSum X m σ N)) standardNormalMeasure
        (berryEsseenRate 1 (berryEsseenRho X P m σ) N) :=
    measureClosedUpperTailErrorLE_of_measureCDFErrorLE hCDF_one
  have hmap :
      (P.map (normalizedSum X m σ N)).real (Set.Ici t) =
        P.real {ω | t ≤ normalizedSum X m σ N ω} := by
    rw [measureReal_def,
      Measure.map_apply_of_aemeasurable hZ measurableSet_Ici]
    rfl
  simpa [measureClosedUpperTailErrorLE, hmap] using hClosed t

/-- Sequence-level version of
`berryEsseenClosedUpperTail_event_of_measureCDFErrorLE_le_one`: a proved CDF
Berry-Esseen theorem with any constant `C ≤ 1` immediately gives the exact
displayed HDP closed-tail event statement. -/
theorem berryEsseenClosedUpperTail_event_of_measureCDFErrorLE_all_le_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ C : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (hC : C ≤ 1)
    (hCDF :
      ∀ N : ℕ, 0 < N →
        measureCDFErrorLE
          (P.map (normalizedSum X m σ N)) standardNormalMeasure
          (berryEsseenRate C (berryEsseenRho X P m σ) N))
    (N : ℕ) (hN : 0 < N) (t : ℝ) :
    |P.real {ω | t ≤ normalizedSum X m σ N ω} -
        standardNormalMeasure.real (Set.Ici t)| ≤
      berryEsseenRate 1 (berryEsseenRho X P m σ) N :=
  berryEsseenClosedUpperTail_event_of_measureCDFErrorLE_le_one
    (P := P) (X := X) (m := m) (σ := σ) hBE hC N hN t (hCDF N hN)

/-- Pointwise closed-upper-tail Berry-Esseen theorem in the displayed HDP event
form `|P{Z_N ≥ t} - P{g ≥ t}| ≤ C ρ / √N`, with the local Durrett/Feller
constant `C = 3`. -/
theorem berryEsseenClosedUpperTail_event
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {m σ : ℝ}
    (hBE : BerryEsseenHypotheses (μ := P) X m σ)
    (N : ℕ) (hN : 0 < N) (t : ℝ) :
    |P.real {ω | t ≤ normalizedSum X m σ N ω} -
        standardNormalMeasure.real (Set.Ici t)| ≤
      berryEsseenRate 3 (berryEsseenRho X P m σ) N := by
  have hZ : AEMeasurable (normalizedSum X m σ N) P :=
    normalizedSum_aemeasurable (μ := P) hBE.aemeasurable N
  have hmap :
      (P.map (normalizedSum X m σ N)).real (Set.Ici t) =
        P.real {ω | t ≤ normalizedSum X m σ N ω} := by
    rw [measureReal_def,
      Measure.map_apply_of_aemeasurable hZ measurableSet_Ici]
    rfl
  have htail :=
    berryEsseenMeasureClosedUpperTail
      (P := P) (X := X) (m := m) (σ := σ) hBE N hN t
  simpa [measureClosedUpperTailErrorLE, hmap] using htail

end DurrettConstants

end LeanFpAnalysis.HDP
