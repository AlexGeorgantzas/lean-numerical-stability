import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.UniformRowComposition
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Gram
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.Core
import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.FloatingPoint

W11 canonical reusable randomized linear algebra destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.UniformRowSamplingFP`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/UniformRowSamplingFP.lean
--
-- Floating-point transfer for Algorithm 3 uniform row sampling after
-- signed-Hadamard preprocessing.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602







namespace NumStability

open scoped BigOperators

/-!
## Floating-point uniform row sketches

The exact Algorithm 3 uniform row sketch samples row `i` and rescales it by
`1 / sqrt(s / m)`, so its Gram matrix is the uniform sample-average matrix
already analyzed in `UniformRowSamplingMGF`.  This file adds the corresponding
rounded row-scaling and rounded Gram-dot-product layer, reusing the repository's
division, row-sketch Gram, and dot-product perturbation lemmas.
-/

-- ============================================================
-- Uniform row-scaling kernels
-- ============================================================

/-- Uniform row-scaling denominator `sqrt(s / m)` for an `s`-row sketch sampled
from `m` rows. -/
noncomputable def uniformRowSampleScaleDen {m : ℕ} (s : ℕ) : ℝ :=
  Real.sqrt ((s : ℝ) * (m : ℝ)⁻¹)

/-- The uniform row-scaling denominator is nonzero when both `m` and `s` are
positive. -/
theorem uniformRowSampleScaleDen_ne_zero {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    uniformRowSampleScaleDen (m := m) s ≠ 0 := by
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmul : 0 < (s : ℝ) * (m : ℝ)⁻¹ :=
    mul_pos hs (inv_pos.mpr hmRpos)
  exact ne_of_gt (by
    unfold uniformRowSampleScaleDen
    exact Real.sqrt_pos.2 hmul)

/-- A floating-point computation of the uniform row-rescaling denominator
    `sqrt(s / m)` used after Algorithm 3 preprocessing. -/
structure ComputedUniformRowScaleDen (fp : FPModel) (m s : ℕ) where
  den : ℝ
  den_abs_error : ℝ
  den_abs_error_nonneg : 0 ≤ den_abs_error
  den_abs_error_bound :
    |den - uniformRowSampleScaleDen (m := m) s| ≤ den_abs_error
  den_ne_zero : den ≠ 0

namespace ComputedUniformRowScaleDen

variable {fp : FPModel} {m s : ℕ}

theorem abs_error_bound (dhat : ComputedUniformRowScaleDen fp m s) :
    |dhat.den - uniformRowSampleScaleDen (m := m) s| ≤ dhat.den_abs_error :=
  dhat.den_abs_error_bound

/-- Scalar square-root perturbation used by concrete denominator routines:
if `1 + delta` is nonnegative, then replacing `sqrt 1` by
`sqrt (1 + delta)` costs at most `|delta|`. -/
theorem abs_sqrt_one_add_sub_one_le_abs (delta : ℝ)
    (hpos : 0 ≤ 1 + delta) :
    |Real.sqrt (1 + delta) - 1| ≤ |delta| := by
  have hden_pos : 0 < Real.sqrt (1 + delta) + 1 := by
    nlinarith [Real.sqrt_nonneg (1 + delta)]
  have hden_ge_one : 1 ≤ Real.sqrt (1 + delta) + 1 := by
    nlinarith [Real.sqrt_nonneg (1 + delta)]
  have hden_ne : Real.sqrt (1 + delta) + 1 ≠ 0 := ne_of_gt hden_pos
  have hsqrt_sq : Real.sqrt (1 + delta) ^ 2 = 1 + delta :=
    Real.sq_sqrt hpos
  have hidentity :
      Real.sqrt (1 + delta) - 1 =
        delta / (Real.sqrt (1 + delta) + 1) := by
    field_simp [hden_ne]
    nlinarith
  rw [hidentity, abs_div]
  have hden_abs_ge_one : 1 ≤ |Real.sqrt (1 + delta) + 1| := by
    simp [abs_of_pos hden_pos, hden_ge_one]
  have hden_abs_pos : 0 < |Real.sqrt (1 + delta) + 1| :=
    lt_of_lt_of_le zero_lt_one hden_abs_ge_one
  have hmul :
      |delta| ≤ |delta| * |Real.sqrt (1 + delta) + 1| := by
    simpa using
      (mul_le_mul_of_nonneg_left hden_abs_ge_one (abs_nonneg delta))
  exact (div_le_iff₀ hden_abs_pos).2 hmul

/-- Exact uniform row-scale denominator certificate.  This is the
zero-denominator-error specialization used when the implementation supplies
`sqrt(s / m)` exactly and only the subsequent row scaling divisions are
rounded. -/
noncomputable def exact (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    ComputedUniformRowScaleDen fp m s where
  den := uniformRowSampleScaleDen (m := m) s
  den_abs_error := 0
  den_abs_error_nonneg := le_rfl
  den_abs_error_bound := by simp
  den_ne_zero := uniformRowSampleScaleDen_ne_zero hm hs

@[simp] theorem exact_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    (exact fp hm hs).den = uniformRowSampleScaleDen (m := m) s := rfl

@[simp] theorem exact_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    (exact fp hm hs).den_abs_error = 0 := rfl

/-- Concrete denominator certificate for the routine
`fl_sqrt ((s : ℝ) * (m : ℝ)⁻¹)` when the input ratio is supplied exactly.

This charges the rounded square-root primitive itself.  If an implementation
also forms `(s : ℝ) * (m : ℝ)⁻¹` in floating point, that earlier scalar
computation must instantiate a separate certificate before this constructor is
used. -/
noncomputable def flSqrtExactInput (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    ComputedUniformRowScaleDen fp m s where
  den := fp.fl_sqrt ((s : ℝ) * (m : ℝ)⁻¹)
  den_abs_error := uniformRowSampleScaleDen (m := m) s * fp.u
  den_abs_error_nonneg := by
    exact mul_nonneg (Real.sqrt_nonneg _) fp.u_nonneg
  den_abs_error_bound := by
    let x : ℝ := (s : ℝ) * (m : ℝ)⁻¹
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      exact mul_nonneg (le_of_lt hs) (inv_nonneg.mpr (le_of_lt hmRpos))
    obtain ⟨δ, hδ, hfl⟩ := fp.model_sqrt x hx_nonneg
    have hd_nonneg : 0 ≤ uniformRowSampleScaleDen (m := m) s :=
      Real.sqrt_nonneg _
    calc
      |fp.fl_sqrt x - uniformRowSampleScaleDen (m := m) s|
          = |uniformRowSampleScaleDen (m := m) s * δ| := by
              unfold uniformRowSampleScaleDen
              rw [hfl]
              dsimp [x]
              ring_nf
      _ = uniformRowSampleScaleDen (m := m) s * |δ| := by
              rw [abs_mul, abs_of_nonneg hd_nonneg]
      _ ≤ uniformRowSampleScaleDen (m := m) s * fp.u :=
              mul_le_mul_of_nonneg_left hδ hd_nonneg
  den_ne_zero := by
    let x : ℝ := (s : ℝ) * (m : ℝ)⁻¹
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      exact mul_nonneg (le_of_lt hs) (inv_nonneg.mpr (le_of_lt hmRpos))
    obtain ⟨δ, hδ, hfl⟩ := fp.model_sqrt x hx_nonneg
    have hd_ne : Real.sqrt x ≠ 0 := by
      simpa [uniformRowSampleScaleDen, x] using
        uniformRowSampleScaleDen_ne_zero hm hs
    have hδ_lower : -fp.u ≤ δ := (abs_le.mp hδ).1
    have hfactor_pos : 0 < 1 + δ := by linarith
    rw [hfl]
    exact mul_ne_zero hd_ne (ne_of_gt hfactor_pos)

@[simp] theorem flSqrtExactInput_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtExactInput fp hm hs hu).den =
      fp.fl_sqrt ((s : ℝ) * (m : ℝ)⁻¹) := rfl

@[simp] theorem flSqrtExactInput_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtExactInput fp hm hs hu).den_abs_error =
      uniformRowSampleScaleDen (m := m) s * fp.u := rfl

/-- Concrete denominator certificate for the routine
`fl_sqrt (fl_div (s : R) (m : R))`.

The sampling law is still the exact uniform law.  This constructor charges the
rounded scalar ratio `s/m` and the rounded square-root primitive used to form
the non-probability scale denominator. -/
noncomputable def flDivThenSqrt (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    ComputedUniformRowScaleDen fp m s where
  den := fp.fl_sqrt (fp.fl_div (s : ℝ) (m : ℝ))
  den_abs_error :=
    uniformRowSampleScaleDen (m := m) s *
      (Real.sqrt (1 + fp.u) * fp.u + fp.u)
  den_abs_error_nonneg := by
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (1 + fp.u) * fp.u + fp.u := by
      exact add_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) fp.u_nonneg) fp.u_nonneg
    exact mul_nonneg (Real.sqrt_nonneg _) hsqrt_nonneg
  den_abs_error_bound := by
    let x : ℝ := (s : ℝ) / (m : ℝ)
    let xhat : ℝ := fp.fl_div (s : ℝ) (m : ℝ)
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmR_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
    have hx_pos : 0 < x := by
      dsimp [x]
      exact div_pos hs hmRpos
    obtain ⟨δr, hδr, hdiv⟩ := fp.model_div (s : ℝ) (m : ℝ) hmR_ne
    have hxhat_eq : xhat = x * (1 + δr) := by
      dsimp [xhat, x]
      simpa using hdiv
    have hδr_lower : -fp.u ≤ δr := (abs_le.mp hδr).1
    have hδr_upper : δr ≤ fp.u := (abs_le.mp hδr).2
    have hfactor_pos : 0 < 1 + δr := by linarith
    have hfactor_nonneg : 0 ≤ 1 + δr := le_of_lt hfactor_pos
    have hxhat_pos : 0 < xhat := by
      rw [hxhat_eq]
      exact mul_pos hx_pos hfactor_pos
    obtain ⟨δs, hδs, hsqrt⟩ :=
      fp.model_sqrt xhat (le_of_lt hxhat_pos)
    let d : ℝ := Real.sqrt x
    let a : ℝ := Real.sqrt (1 + δr)
    have hd_nonneg : 0 ≤ d := Real.sqrt_nonneg _
    have ha_nonneg : 0 ≤ a := Real.sqrt_nonneg _
    have h1u_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have ha_le : a ≤ Real.sqrt (1 + fp.u) := by
      dsimp [a]
      exact Real.sqrt_le_sqrt (by linarith)
    have hsqrt_ratio : |a - 1| ≤ fp.u := by
      exact
        (abs_sqrt_one_add_sub_one_le_abs δr hfactor_nonneg).trans hδr
    have hscalar :
        |a * (1 + δs) - 1| ≤
          Real.sqrt (1 + fp.u) * fp.u + fp.u := by
      have hsplit : a * (1 + δs) - 1 = a * δs + (a - 1) := by ring
      calc
        |a * (1 + δs) - 1|
            = |a * δs + (a - 1)| := by rw [hsplit]
        _ ≤ |a * δs| + |a - 1| := abs_add_le _ _
        _ = a * |δs| + |a - 1| := by
              rw [abs_mul, abs_of_nonneg ha_nonneg]
        _ ≤ a * fp.u + fp.u := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hδs ha_nonneg)
                hsqrt_ratio
        _ ≤ Real.sqrt (1 + fp.u) * fp.u + fp.u := by
              have h :=
                add_le_add_right
                  (mul_le_mul_of_nonneg_right ha_le fp.u_nonneg) fp.u
              linarith
    have hsqrt_xhat :
        Real.sqrt xhat = d * a := by
      rw [hxhat_eq]
      dsimp [d, a]
      rw [Real.sqrt_mul (le_of_lt hx_pos) (1 + δr)]
    have hmain :
        |Real.sqrt xhat * (1 + δs) - d| ≤
          d * (Real.sqrt (1 + fp.u) * fp.u + fp.u) := by
      rw [hsqrt_xhat]
      have hsplit : d * a * (1 + δs) - d =
          d * (a * (1 + δs) - 1) := by ring
      calc
        |d * a * (1 + δs) - d|
            = |d * (a * (1 + δs) - 1)| := by rw [hsplit]
        _ = d * |a * (1 + δs) - 1| := by
              rw [abs_mul, abs_of_nonneg hd_nonneg]
        _ ≤ d * (Real.sqrt (1 + fp.u) * fp.u + fp.u) :=
              mul_le_mul_of_nonneg_left hscalar hd_nonneg
    have htarget :
        |fp.fl_sqrt xhat - d| ≤
          d * (Real.sqrt (1 + fp.u) * fp.u + fp.u) := by
      rw [hsqrt]
      exact hmain
    simpa [xhat, x, d, uniformRowSampleScaleDen, div_eq_mul_inv]
      using htarget
  den_ne_zero := by
    let x : ℝ := (s : ℝ) / (m : ℝ)
    let xhat : ℝ := fp.fl_div (s : ℝ) (m : ℝ)
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmR_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
    have hx_pos : 0 < x := by
      dsimp [x]
      exact div_pos hs hmRpos
    obtain ⟨δr, hδr, hdiv⟩ := fp.model_div (s : ℝ) (m : ℝ) hmR_ne
    have hxhat_eq : xhat = x * (1 + δr) := by
      dsimp [xhat, x]
      simpa using hdiv
    have hδr_lower : -fp.u ≤ δr := (abs_le.mp hδr).1
    have hfactor_pos : 0 < 1 + δr := by linarith
    have hxhat_pos : 0 < xhat := by
      rw [hxhat_eq]
      exact mul_pos hx_pos hfactor_pos
    obtain ⟨δs, hδs, hsqrt⟩ :=
      fp.model_sqrt xhat (le_of_lt hxhat_pos)
    have hsqrt_ne : Real.sqrt xhat ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hxhat_pos)
    have hδs_lower : -fp.u ≤ δs := (abs_le.mp hδs).1
    have hfactor_s_pos : 0 < 1 + δs := by linarith
    rw [hsqrt]
    exact mul_ne_zero hsqrt_ne (ne_of_gt hfactor_s_pos)

@[simp] theorem flDivThenSqrt_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flDivThenSqrt fp hm hs hu).den =
      fp.fl_sqrt (fp.fl_div (s : ℝ) (m : ℝ)) := rfl

@[simp] theorem flDivThenSqrt_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flDivThenSqrt fp hm hs hu).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        (Real.sqrt (1 + fp.u) * fp.u + fp.u) := rfl

/-- Concrete denominator certificate for the routine
`fl_sqrt (fl_mul (s : R) (fl_div 1 (m : R)))`.

This is a second non-probability scale-denominator implementation for the
Algorithm 3 uniform row sketch: it forms a rounded reciprocal of `m`, multiplies
by `s`, and finally takes a rounded square root.  The uniform sampling law is
still exact; this constructor only charges the scalar arithmetic used to build
the row-rescaling denominator. -/
noncomputable def flInvMulThenSqrt (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    ComputedUniformRowScaleDen fp m s where
  den := fp.fl_sqrt (fp.fl_mul (s : ℝ) (fp.fl_div 1 (m : ℝ)))
  den_abs_error :=
    uniformRowSampleScaleDen (m := m) s *
      (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
        (2 * fp.u + fp.u ^ 2))
  den_abs_error_nonneg := by
    have htail : 0 ≤
        Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
          (2 * fp.u + fp.u ^ 2) := by
      exact add_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) fp.u_nonneg)
        (by nlinarith [fp.u_nonneg])
    exact mul_nonneg (Real.sqrt_nonneg _) htail
  den_abs_error_bound := by
    let x : ℝ := (s : ℝ) * (m : ℝ)⁻¹
    let invhat : ℝ := fp.fl_div 1 (m : ℝ)
    let xhat : ℝ := fp.fl_mul (s : ℝ) invhat
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmR_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
    have hx_pos : 0 < x := by
      dsimp [x]
      exact mul_pos hs (inv_pos.mpr hmRpos)
    obtain ⟨δi, hδi, hdiv⟩ := fp.model_div 1 (m : ℝ) hmR_ne
    have hinvhat_eq : invhat = ((m : ℝ)⁻¹) * (1 + δi) := by
      dsimp [invhat]
      simpa [one_div] using hdiv
    obtain ⟨δm, hδm, hmul⟩ := fp.model_mul (s : ℝ) invhat
    let f : ℝ := (1 + δi) * (1 + δm)
    have hxhat_eq : xhat = x * f := by
      dsimp [xhat]
      rw [hmul, hinvhat_eq]
      dsimp [x, f]
      ring
    have hδi_lower : -fp.u ≤ δi := (abs_le.mp hδi).1
    have hδi_upper : δi ≤ fp.u := (abs_le.mp hδi).2
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hδm_upper : δm ≤ fp.u := (abs_le.mp hδm).2
    have hi_pos : 0 < 1 + δi := by linarith
    have hm_pos : 0 < 1 + δm := by linarith
    have hf_pos : 0 < f := by
      dsimp [f]
      exact mul_pos hi_pos hm_pos
    have hf_nonneg : 0 ≤ f := le_of_lt hf_pos
    have hxhat_pos : 0 < xhat := by
      rw [hxhat_eq]
      exact mul_pos hx_pos hf_pos
    obtain ⟨δs, hδs, hsqrt⟩ :=
      fp.model_sqrt xhat (le_of_lt hxhat_pos)
    let d : ℝ := Real.sqrt x
    let a : ℝ := Real.sqrt f
    have hd_nonneg : 0 ≤ d := Real.sqrt_nonneg _
    have ha_nonneg : 0 ≤ a := Real.sqrt_nonneg _
    have h1u_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have hf_upper : f ≤ (1 + fp.u) * (1 + fp.u) := by
      dsimp [f]
      have hi_le : 1 + δi ≤ 1 + fp.u := by linarith
      have hm_le : 1 + δm ≤ 1 + fp.u := by linarith
      exact mul_le_mul hi_le hm_le (le_of_lt hm_pos) h1u_nonneg
    have ha_le : a ≤ Real.sqrt ((1 + fp.u) * (1 + fp.u)) := by
      dsimp [a]
      exact Real.sqrt_le_sqrt hf_upper
    have hf_abs :
        |f - 1| ≤ 2 * fp.u + fp.u ^ 2 := by
      have hf_expand : f - 1 = δi + δm + δi * δm := by
        dsimp [f]
        ring
      calc
        |f - 1| = |δi + δm + δi * δm| := by rw [hf_expand]
        _ ≤ |δi + δm| + |δi * δm| := abs_add_le _ _
        _ ≤ (|δi| + |δm|) + |δi * δm| := by
              simpa [add_assoc, add_comm, add_left_comm] using
                add_le_add_right (abs_add_le δi δm) |δi * δm|
        _ = |δi| + |δm| + |δi| * |δm| := by
              rw [abs_mul]
        _ ≤ fp.u + fp.u + fp.u * fp.u := by
              have hprod : |δi| * |δm| ≤ fp.u * fp.u :=
                mul_le_mul hδi hδm (abs_nonneg δm) fp.u_nonneg
              nlinarith
        _ = 2 * fp.u + fp.u ^ 2 := by ring
    have hsqrt_ratio : |a - 1| ≤ 2 * fp.u + fp.u ^ 2 := by
      have hone : 1 + (f - 1) = f := by ring
      have hpos : 0 ≤ 1 + (f - 1) := by
        simpa [hone] using hf_nonneg
      have h :=
        abs_sqrt_one_add_sub_one_le_abs (f - 1) hpos
      simpa [a, hone] using h.trans hf_abs
    have hscalar :
        |a * (1 + δs) - 1| ≤
          Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
            (2 * fp.u + fp.u ^ 2) := by
      have hsplit : a * (1 + δs) - 1 = a * δs + (a - 1) := by ring
      calc
        |a * (1 + δs) - 1|
            = |a * δs + (a - 1)| := by rw [hsplit]
        _ ≤ |a * δs| + |a - 1| := abs_add_le _ _
        _ = a * |δs| + |a - 1| := by
              rw [abs_mul, abs_of_nonneg ha_nonneg]
        _ ≤ a * fp.u + (2 * fp.u + fp.u ^ 2) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hδs ha_nonneg)
                hsqrt_ratio
        _ ≤ Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
              (2 * fp.u + fp.u ^ 2) := by
              simpa [add_assoc, add_comm, add_left_comm] using
                add_le_add_right
                (mul_le_mul_of_nonneg_right ha_le fp.u_nonneg)
                (2 * fp.u + fp.u ^ 2)
    have hsqrt_xhat : Real.sqrt xhat = d * a := by
      rw [hxhat_eq]
      dsimp [d, a]
      rw [Real.sqrt_mul (le_of_lt hx_pos) f]
    have hmain :
        |Real.sqrt xhat * (1 + δs) - d| ≤
          d * (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
            (2 * fp.u + fp.u ^ 2)) := by
      rw [hsqrt_xhat]
      have hsplit : d * a * (1 + δs) - d =
          d * (a * (1 + δs) - 1) := by ring
      calc
        |d * a * (1 + δs) - d|
            = |d * (a * (1 + δs) - 1)| := by rw [hsplit]
        _ = d * |a * (1 + δs) - 1| := by
              rw [abs_mul, abs_of_nonneg hd_nonneg]
        _ ≤ d * (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
            (2 * fp.u + fp.u ^ 2)) :=
              mul_le_mul_of_nonneg_left hscalar hd_nonneg
    have htarget :
        |fp.fl_sqrt xhat - d| ≤
          d * (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
            (2 * fp.u + fp.u ^ 2)) := by
      rw [hsqrt]
      exact hmain
    simpa [xhat, x, d, uniformRowSampleScaleDen]
      using htarget
  den_ne_zero := by
    let x : ℝ := (s : ℝ) * (m : ℝ)⁻¹
    let invhat : ℝ := fp.fl_div 1 (m : ℝ)
    let xhat : ℝ := fp.fl_mul (s : ℝ) invhat
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmR_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
    have hx_pos : 0 < x := by
      dsimp [x]
      exact mul_pos hs (inv_pos.mpr hmRpos)
    obtain ⟨δi, hδi, hdiv⟩ := fp.model_div 1 (m : ℝ) hmR_ne
    have hinvhat_eq : invhat = ((m : ℝ)⁻¹) * (1 + δi) := by
      dsimp [invhat]
      simpa [one_div] using hdiv
    obtain ⟨δm, hδm, hmul⟩ := fp.model_mul (s : ℝ) invhat
    let f : ℝ := (1 + δi) * (1 + δm)
    have hxhat_eq : xhat = x * f := by
      dsimp [xhat]
      rw [hmul, hinvhat_eq]
      dsimp [x, f]
      ring
    have hδi_lower : -fp.u ≤ δi := (abs_le.mp hδi).1
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hi_pos : 0 < 1 + δi := by linarith
    have hm_pos : 0 < 1 + δm := by linarith
    have hf_pos : 0 < f := by
      dsimp [f]
      exact mul_pos hi_pos hm_pos
    have hxhat_pos : 0 < xhat := by
      rw [hxhat_eq]
      exact mul_pos hx_pos hf_pos
    obtain ⟨δs, hδs, hsqrt⟩ :=
      fp.model_sqrt xhat (le_of_lt hxhat_pos)
    have hsqrt_ne : Real.sqrt xhat ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hxhat_pos)
    have hδs_lower : -fp.u ≤ δs := (abs_le.mp hδs).1
    have hfactor_s_pos : 0 < 1 + δs := by linarith
    rw [hsqrt]
    exact mul_ne_zero hsqrt_ne (ne_of_gt hfactor_s_pos)

@[simp] theorem flInvMulThenSqrt_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flInvMulThenSqrt fp hm hs hu).den =
      fp.fl_sqrt (fp.fl_mul (s : ℝ) (fp.fl_div 1 (m : ℝ))) := rfl

@[simp] theorem flInvMulThenSqrt_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flInvMulThenSqrt fp hm hs hu).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
          (2 * fp.u + fp.u ^ 2)) := rfl

/-- Concrete denominator certificate for the routine
`fl_div (fl_sqrt (s : R)) (fl_sqrt (m : R))`.

This covers an implementation that forms the two square roots separately and
then divides them.  The uniform sampling law remains exact; the only charged
operations are the two rounded square roots and the rounded scalar division
used to compute the non-probability row-rescaling denominator. -/
noncomputable def flSqrtDivSqrt (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    ComputedUniformRowScaleDen fp m s where
  den := fp.fl_div (fp.fl_sqrt (s : ℝ)) (fp.fl_sqrt (m : ℝ))
  den_abs_error :=
    uniformRowSampleScaleDen (m := m) s *
      ((3 * fp.u + fp.u ^ 2) / (1 - fp.u))
  den_abs_error_nonneg := by
    have hnum : 0 ≤ 3 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg]
    have hden : 0 ≤ 1 - fp.u := le_of_lt (sub_pos.mpr hu)
    exact mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hnum hden)
  den_abs_error_bound := by
    let sR : ℝ := (s : ℝ)
    let mR : ℝ := (m : ℝ)
    let shat : ℝ := fp.fl_sqrt sR
    let mhat : ℝ := fp.fl_sqrt mR
    let sqrtS : ℝ := Real.sqrt sR
    let sqrtM : ℝ := Real.sqrt mR
    let d : ℝ := uniformRowSampleScaleDen (m := m) s
    have hmRpos : 0 < mR := by
      dsimp [mR]
      exact_mod_cast hm
    have hsRpos : 0 < sR := by
      dsimp [sR]
      exact hs
    have hsR_nonneg : 0 ≤ sR := le_of_lt hsRpos
    have hmR_nonneg : 0 ≤ mR := le_of_lt hmRpos
    obtain ⟨δs, hδs, hsqrt_s⟩ := fp.model_sqrt sR hsR_nonneg
    obtain ⟨δm, hδm, hsqrt_m⟩ := fp.model_sqrt mR hmR_nonneg
    have hsqrtM_ne : sqrtM ≠ 0 := by
      dsimp [sqrtM]
      exact ne_of_gt (Real.sqrt_pos.2 hmRpos)
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hδm_upper : δm ≤ fp.u := (abs_le.mp hδm).2
    have hfactor_m_pos : 0 < 1 + δm := by linarith
    have hfactor_m_ne : 1 + δm ≠ 0 := ne_of_gt hfactor_m_pos
    have hmhat_ne : mhat ≠ 0 := by
      dsimp [mhat]
      rw [hsqrt_m]
      exact mul_ne_zero hsqrtM_ne (ne_of_gt hfactor_m_pos)
    obtain ⟨δd, hδd, hdiv⟩ := fp.model_div shat mhat hmhat_ne
    let g : ℝ := ((1 + δs) / (1 + δm)) * (1 + δd)
    have hd_eq : d = sqrtS / sqrtM := by
      dsimp [d, uniformRowSampleScaleDen, sqrtS, sqrtM, sR, mR]
      rw [show (s : ℝ) * (m : ℝ)⁻¹ = (s : ℝ) / (m : ℝ) by ring]
      rw [Real.sqrt_div (le_of_lt hs) (m : ℝ)]
    have hden_eq :
        fp.fl_div shat mhat = d * g := by
      rw [hdiv]
      dsimp [shat, mhat]
      rw [hsqrt_s, hsqrt_m, hd_eq]
      dsimp [sqrtS, sqrtM, g]
      field_simp [hsqrtM_ne, hfactor_m_ne]
    have hδs_upper : δs ≤ fp.u := (abs_le.mp hδs).2
    have hδd_upper : δd ≤ fp.u := (abs_le.mp hδd).2
    have hnum_bound :
        |(1 + δs) * (1 + δd) - (1 + δm)| ≤
          3 * fp.u + fp.u ^ 2 := by
      have hexpand :
          (1 + δs) * (1 + δd) - (1 + δm) =
            δs + δd + δs * δd - δm := by ring
      have htri :
          |δs + δd + δs * δd - δm| ≤
            |δs| + |δd| + |δs * δd| + |δm| := by
        have htri₁ :
            |δs + δd + δs * δd| ≤
              |δs + δd| + |δs * δd| :=
          abs_add_le (δs + δd) (δs * δd)
        have htri₂ : |δs + δd| ≤ |δs| + |δd| :=
          abs_add_le δs δd
        calc
          |δs + δd + δs * δd - δm|
              = |(δs + δd + δs * δd) + (-δm)| := by ring_nf
          _ ≤ |δs + δd + δs * δd| + |-δm| :=
              abs_add_le _ _
          _ ≤ (|δs + δd| + |δs * δd|) + |-δm| :=
              by linarith
          _ ≤ ((|δs| + |δd|) + |δs * δd|) + |-δm| :=
              by linarith
          _ = |δs| + |δd| + |δs * δd| + |δm| := by
              simp [abs_neg, add_assoc]
      have hprod : |δs * δd| ≤ fp.u * fp.u := by
        rw [abs_mul]
        exact mul_le_mul hδs hδd (abs_nonneg δd) fp.u_nonneg
      calc
        |(1 + δs) * (1 + δd) - (1 + δm)|
            = |δs + δd + δs * δd - δm| := by rw [hexpand]
        _ ≤ |δs| + |δd| + |δs * δd| + |δm| := htri
        _ ≤ fp.u + fp.u + fp.u * fp.u + fp.u := by
              nlinarith [hδs, hδd, hδm, hprod]
        _ = 3 * fp.u + fp.u ^ 2 := by ring
    have hnum_nonneg : 0 ≤ 3 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg]
    have hden_pos : 0 < 1 - fp.u := sub_pos.mpr hu
    have hden_abs_lower : 1 - fp.u ≤ |1 + δm| := by
      rw [abs_of_pos hfactor_m_pos]
      linarith
    have hg_bound :
        |g - 1| ≤ (3 * fp.u + fp.u ^ 2) / (1 - fp.u) := by
      have hg_identity :
          g - 1 =
            ((1 + δs) * (1 + δd) - (1 + δm)) / (1 + δm) := by
        dsimp [g]
        field_simp [hfactor_m_ne]
      calc
        |g - 1|
            = |((1 + δs) * (1 + δd) - (1 + δm)) / (1 + δm)| := by
                rw [hg_identity]
        _ = |(1 + δs) * (1 + δd) - (1 + δm)| / |1 + δm| :=
            abs_div _ _
        _ ≤ (3 * fp.u + fp.u ^ 2) / |1 + δm| :=
            div_le_div_of_nonneg_right hnum_bound (abs_nonneg _)
        _ ≤ (3 * fp.u + fp.u ^ 2) / (1 - fp.u) :=
            div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_abs_lower
    have hd_nonneg : 0 ≤ d := by
      dsimp [d, uniformRowSampleScaleDen]
      exact Real.sqrt_nonneg _
    have htarget :
        |fp.fl_div shat mhat - d| ≤
          d * ((3 * fp.u + fp.u ^ 2) / (1 - fp.u)) := by
      rw [hden_eq]
      have hsplit : d * g - d = d * (g - 1) := by ring
      calc
        |d * g - d|
            = |d * (g - 1)| := by rw [hsplit]
        _ = d * |g - 1| := by
              rw [abs_mul, abs_of_nonneg hd_nonneg]
        _ ≤ d * ((3 * fp.u + fp.u ^ 2) / (1 - fp.u)) :=
              mul_le_mul_of_nonneg_left hg_bound hd_nonneg
    simpa [shat, mhat, d]
      using htarget
  den_ne_zero := by
    let sR : ℝ := (s : ℝ)
    let mR : ℝ := (m : ℝ)
    let shat : ℝ := fp.fl_sqrt sR
    let mhat : ℝ := fp.fl_sqrt mR
    have hmRpos : 0 < mR := by
      dsimp [mR]
      exact_mod_cast hm
    have hsRpos : 0 < sR := by
      dsimp [sR]
      exact hs
    obtain ⟨δs, hδs, hsqrt_s⟩ := fp.model_sqrt sR (le_of_lt hsRpos)
    obtain ⟨δm, hδm, hsqrt_m⟩ := fp.model_sqrt mR (le_of_lt hmRpos)
    have hsqrtS_ne : Real.sqrt sR ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hsRpos)
    have hsqrtM_ne : Real.sqrt mR ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hmRpos)
    have hδs_lower : -fp.u ≤ δs := (abs_le.mp hδs).1
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hfactor_s_pos : 0 < 1 + δs := by linarith
    have hfactor_m_pos : 0 < 1 + δm := by linarith
    have hshat_ne : shat ≠ 0 := by
      dsimp [shat]
      rw [hsqrt_s]
      exact mul_ne_zero hsqrtS_ne (ne_of_gt hfactor_s_pos)
    have hmhat_ne : mhat ≠ 0 := by
      dsimp [mhat]
      rw [hsqrt_m]
      exact mul_ne_zero hsqrtM_ne (ne_of_gt hfactor_m_pos)
    obtain ⟨δd, hδd, hdiv⟩ := fp.model_div shat mhat hmhat_ne
    have hratio_ne : shat / mhat ≠ 0 := div_ne_zero hshat_ne hmhat_ne
    have hδd_lower : -fp.u ≤ δd := (abs_le.mp hδd).1
    have hfactor_d_pos : 0 < 1 + δd := by linarith
    rw [hdiv]
    exact mul_ne_zero hratio_ne (ne_of_gt hfactor_d_pos)

@[simp] theorem flSqrtDivSqrt_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtDivSqrt fp hm hs hu).den =
      fp.fl_div (fp.fl_sqrt (s : ℝ)) (fp.fl_sqrt (m : ℝ)) := rfl

@[simp] theorem flSqrtDivSqrt_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtDivSqrt fp hm hs hu).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        ((3 * fp.u + fp.u ^ 2) / (1 - fp.u)) := rfl

/-- Concrete denominator certificate for the routine
`fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (m : R)))`.

This covers the common implementation pattern "form `sqrt(s)`, form
`sqrt(m)`, compute a rounded reciprocal of the latter, and multiply."  The
uniform sampling law remains exact; this constructor charges only the scalar
arithmetic used to compute the non-probability row-rescaling denominator. -/
noncomputable def flSqrtMulInvSqrt (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    ComputedUniformRowScaleDen fp m s where
  den :=
    fp.fl_mul (fp.fl_sqrt (s : ℝ))
      (fp.fl_div 1 (fp.fl_sqrt (m : ℝ)))
  den_abs_error :=
    uniformRowSampleScaleDen (m := m) s *
      ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u))
  den_abs_error_nonneg := by
    have hnum : 0 ≤ 4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3 := by
      nlinarith [fp.u_nonneg]
    have hden : 0 ≤ 1 - fp.u := le_of_lt (sub_pos.mpr hu)
    exact mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hnum hden)
  den_abs_error_bound := by
    let sR : ℝ := (s : ℝ)
    let mR : ℝ := (m : ℝ)
    let shat : ℝ := fp.fl_sqrt sR
    let mhat : ℝ := fp.fl_sqrt mR
    let invMhat : ℝ := fp.fl_div 1 mhat
    let sqrtS : ℝ := Real.sqrt sR
    let sqrtM : ℝ := Real.sqrt mR
    let d : ℝ := uniformRowSampleScaleDen (m := m) s
    have hmRpos : 0 < mR := by
      dsimp [mR]
      exact_mod_cast hm
    have hsRpos : 0 < sR := by
      dsimp [sR]
      exact hs
    have hsR_nonneg : 0 ≤ sR := le_of_lt hsRpos
    have hmR_nonneg : 0 ≤ mR := le_of_lt hmRpos
    obtain ⟨δs, hδs, hsqrt_s⟩ := fp.model_sqrt sR hsR_nonneg
    obtain ⟨δm, hδm, hsqrt_m⟩ := fp.model_sqrt mR hmR_nonneg
    have hsqrtM_ne : sqrtM ≠ 0 := by
      dsimp [sqrtM]
      exact ne_of_gt (Real.sqrt_pos.2 hmRpos)
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hδm_upper : δm ≤ fp.u := (abs_le.mp hδm).2
    have hfactor_m_pos : 0 < 1 + δm := by linarith
    have hfactor_m_ne : 1 + δm ≠ 0 := ne_of_gt hfactor_m_pos
    have hmhat_ne : mhat ≠ 0 := by
      dsimp [mhat]
      rw [hsqrt_m]
      exact mul_ne_zero hsqrtM_ne (ne_of_gt hfactor_m_pos)
    obtain ⟨δi, hδi, hdiv⟩ := fp.model_div 1 mhat hmhat_ne
    obtain ⟨δp, hδp, hmul⟩ := fp.model_mul shat invMhat
    let g : ℝ := ((1 + δs) * (1 + δi) * (1 + δp)) / (1 + δm)
    have hd_eq : d = sqrtS / sqrtM := by
      dsimp [d, uniformRowSampleScaleDen, sqrtS, sqrtM, sR, mR]
      rw [show (s : ℝ) * (m : ℝ)⁻¹ = (s : ℝ) / (m : ℝ) by ring]
      rw [Real.sqrt_div (le_of_lt hs) (m : ℝ)]
    have hden_eq :
        fp.fl_mul shat invMhat = d * g := by
      rw [hmul]
      dsimp [shat, invMhat]
      rw [hdiv, hsqrt_s]
      dsimp [mhat]
      rw [hsqrt_m, hd_eq]
      dsimp [sqrtS, sqrtM, g]
      field_simp [hsqrtM_ne, hfactor_m_ne]
    have hprod_abs :
        |δs * δi| ≤ fp.u * fp.u := by
      rw [abs_mul]
      exact mul_le_mul hδs hδi (abs_nonneg _) fp.u_nonneg
    have hprod_sp_abs :
        |δs * δp| ≤ fp.u * fp.u := by
      rw [abs_mul]
      exact mul_le_mul hδs hδp (abs_nonneg _) fp.u_nonneg
    have hprod_ip_abs :
        |δi * δp| ≤ fp.u * fp.u := by
      rw [abs_mul]
      exact mul_le_mul hδi hδp (abs_nonneg _) fp.u_nonneg
    have hprod3_abs :
        |δs * δi * δp| ≤ fp.u * fp.u * fp.u := by
      rw [abs_mul, abs_mul]
      have hprod_si : |δs| * |δi| ≤ fp.u * fp.u :=
        mul_le_mul hδs hδi (abs_nonneg _) fp.u_nonneg
      exact mul_le_mul hprod_si hδp (abs_nonneg _)
        (mul_nonneg fp.u_nonneg fp.u_nonneg)
    have htri :
        |δs + δi + δp + δs * δi + δs * δp + δi * δp +
            δs * δi * δp - δm| ≤
          |δs| + |δi| + |δp| + |δs * δi| + |δs * δp| +
            |δi * δp| + |δs * δi * δp| + |δm| := by
      have h0 :
          |δs + δi + δp + δs * δi + δs * δp + δi * δp +
              δs * δi * δp - δm| ≤
            |δs + δi + δp + δs * δi + δs * δp + δi * δp +
                δs * δi * δp| + |δm| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le
            (δs + δi + δp + δs * δi + δs * δp + δi * δp +
              δs * δi * δp) (-δm)
      have h1 :
          |δs + δi + δp + δs * δi + δs * δp + δi * δp +
              δs * δi * δp| ≤
            |δs + δi + δp + δs * δi + δs * δp + δi * δp| +
              |δs * δi * δp| := by
        simpa [add_assoc] using
          abs_add_le
            (δs + δi + δp + δs * δi + δs * δp + δi * δp)
            (δs * δi * δp)
      have h2 :
          |δs + δi + δp + δs * δi + δs * δp + δi * δp| ≤
            |δs + δi + δp + δs * δi + δs * δp| + |δi * δp| := by
        simpa [add_assoc] using
          abs_add_le
            (δs + δi + δp + δs * δi + δs * δp) (δi * δp)
      have h3 :
          |δs + δi + δp + δs * δi + δs * δp| ≤
            |δs + δi + δp + δs * δi| + |δs * δp| := by
        simpa [add_assoc] using
          abs_add_le (δs + δi + δp + δs * δi) (δs * δp)
      have h4 :
          |δs + δi + δp + δs * δi| ≤
            |δs + δi + δp| + |δs * δi| := by
        simpa [add_assoc] using abs_add_le (δs + δi + δp) (δs * δi)
      have h5 : |δs + δi + δp| ≤ |δs + δi| + |δp| := by
        simpa [add_assoc] using abs_add_le (δs + δi) δp
      have h6 : |δs + δi| ≤ |δs| + |δi| :=
        abs_add_le δs δi
      linarith
    have hnum_bound :
        |(1 + δs) * (1 + δi) * (1 + δp) - (1 + δm)| ≤
          4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3 := by
      have hexpand :
          (1 + δs) * (1 + δi) * (1 + δp) - (1 + δm) =
            δs + δi + δp + δs * δi + δs * δp + δi * δp +
              δs * δi * δp - δm := by
        ring
      calc
        |(1 + δs) * (1 + δi) * (1 + δp) - (1 + δm)|
            =
          |δs + δi + δp + δs * δi + δs * δp + δi * δp +
              δs * δi * δp - δm| := by rw [hexpand]
        _ ≤ |δs| + |δi| + |δp| + |δs * δi| + |δs * δp| +
              |δi * δp| + |δs * δi * δp| + |δm| := htri
        _ ≤ 4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3 := by
              nlinarith [hδs, hδi, hδp, hδm, hprod_abs,
                hprod_sp_abs, hprod_ip_abs, hprod3_abs]
    have hnum_nonneg : 0 ≤ 4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3 := by
      nlinarith [fp.u_nonneg]
    have hden_pos : 0 < 1 - fp.u := sub_pos.mpr hu
    have hden_abs_lower : 1 - fp.u ≤ |1 + δm| := by
      rw [abs_of_pos hfactor_m_pos]
      linarith
    have hg_bound :
        |g - 1| ≤
          (4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u) := by
      have hg_identity :
          g - 1 =
            ((1 + δs) * (1 + δi) * (1 + δp) - (1 + δm)) /
              (1 + δm) := by
        dsimp [g]
        field_simp [hfactor_m_ne]
      calc
        |g - 1|
            = |((1 + δs) * (1 + δi) * (1 + δp) - (1 + δm)) /
                (1 + δm)| := by rw [hg_identity]
        _ =
            |(1 + δs) * (1 + δi) * (1 + δp) - (1 + δm)| /
              |1 + δm| := abs_div _ _
        _ ≤ (4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / |1 + δm| :=
            div_le_div_of_nonneg_right hnum_bound (abs_nonneg _)
        _ ≤ (4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u) :=
            div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_abs_lower
    have hd_nonneg : 0 ≤ d := by
      dsimp [d, uniformRowSampleScaleDen]
      exact Real.sqrt_nonneg _
    have htarget :
        |fp.fl_mul shat invMhat - d| ≤
          d * ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u)) := by
      rw [hden_eq]
      have hsplit : d * g - d = d * (g - 1) := by ring
      calc
        |d * g - d|
            = |d * (g - 1)| := by rw [hsplit]
        _ = d * |g - 1| := by
              rw [abs_mul, abs_of_nonneg hd_nonneg]
        _ ≤ d * ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) /
              (1 - fp.u)) :=
              mul_le_mul_of_nonneg_left hg_bound hd_nonneg
    simpa [shat, invMhat, d]
      using htarget
  den_ne_zero := by
    let sR : ℝ := (s : ℝ)
    let mR : ℝ := (m : ℝ)
    let shat : ℝ := fp.fl_sqrt sR
    let mhat : ℝ := fp.fl_sqrt mR
    let invMhat : ℝ := fp.fl_div 1 mhat
    have hmRpos : 0 < mR := by
      dsimp [mR]
      exact_mod_cast hm
    have hsRpos : 0 < sR := by
      dsimp [sR]
      exact hs
    obtain ⟨δs, hδs, hsqrt_s⟩ := fp.model_sqrt sR (le_of_lt hsRpos)
    obtain ⟨δm, hδm, hsqrt_m⟩ := fp.model_sqrt mR (le_of_lt hmRpos)
    have hsqrtS_ne : Real.sqrt sR ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hsRpos)
    have hsqrtM_ne : Real.sqrt mR ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hmRpos)
    have hδs_lower : -fp.u ≤ δs := (abs_le.mp hδs).1
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hfactor_s_pos : 0 < 1 + δs := by linarith
    have hfactor_m_pos : 0 < 1 + δm := by linarith
    have hshat_ne : shat ≠ 0 := by
      dsimp [shat]
      rw [hsqrt_s]
      exact mul_ne_zero hsqrtS_ne (ne_of_gt hfactor_s_pos)
    have hmhat_ne : mhat ≠ 0 := by
      dsimp [mhat]
      rw [hsqrt_m]
      exact mul_ne_zero hsqrtM_ne (ne_of_gt hfactor_m_pos)
    obtain ⟨δi, hδi, hdiv⟩ := fp.model_div 1 mhat hmhat_ne
    have hinv_ne : invMhat ≠ 0 := by
      dsimp [invMhat]
      rw [hdiv]
      have hone_div_ne : (1 : ℝ) / mhat ≠ 0 :=
        div_ne_zero one_ne_zero hmhat_ne
      have hδi_lower : -fp.u ≤ δi := (abs_le.mp hδi).1
      have hfactor_i_pos : 0 < 1 + δi := by linarith
      exact mul_ne_zero hone_div_ne (ne_of_gt hfactor_i_pos)
    obtain ⟨δp, hδp, hmul⟩ := fp.model_mul shat invMhat
    have hδp_lower : -fp.u ≤ δp := (abs_le.mp hδp).1
    have hfactor_p_pos : 0 < 1 + δp := by linarith
    rw [hmul]
    exact mul_ne_zero (mul_ne_zero hshat_ne hinv_ne)
      (ne_of_gt hfactor_p_pos)

@[simp] theorem flSqrtMulInvSqrt_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtMulInvSqrt fp hm hs hu).den =
      fp.fl_mul (fp.fl_sqrt (s : ℝ))
        (fp.fl_div 1 (fp.fl_sqrt (m : ℝ))) := rfl

@[simp] theorem flSqrtMulInvSqrt_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtMulInvSqrt fp hm hs hu).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u)) := rfl

end ComputedUniformRowScaleDen

/- ============================================================
   Concrete denominator routine used by the final SRHT endpoints
   ============================================================ -/

/-- Positive `gammaValid` horizons imply the unit roundoff is below one.

This adapter lets concrete denominator routines use the same sample-count
roundoff guard as the downstream Gram-dot-product analysis. -/
theorem uniformRowUnitRoundoff_lt_one_of_pos_gammaValid
    (fp : FPModel) {s : ℕ} (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) :
    fp.u < 1 := by
  have hsNat : 0 < s := by exact_mod_cast hs
  have hone_le_s_nat : 1 ≤ s := Nat.succ_le_iff.mpr hsNat
  have hone_le_s : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hone_le_s_nat
  have hu_le_su : fp.u ≤ (s : ℝ) * fp.u := by
    simpa using mul_le_mul_of_nonneg_right hone_le_s fp.u_nonneg
  have hsu_lt_one : (s : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hγ
  exact lt_of_le_of_lt hu_le_su hsu_lt_one

/-- Concrete uniform-row denominator routine for Algorithm 3.

The row-sampling law remains the exact uniform law.  The non-probability
denominator used by the implementation is the rounded routine
`fl_sqrt ((s : R) * (m : R)^{-1})`, where the scalar input ratio is supplied
exactly, and the constructor below carries the proved absolute
denominator-error bound for that routine. -/
noncomputable def uniformRowFlSqrtExactInputScaleDen
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    ComputedUniformRowScaleDen fp m s :=
  ComputedUniformRowScaleDen.flSqrtExactInput fp hm hs
    (uniformRowUnitRoundoff_lt_one_of_pos_gammaValid fp hs hγs)

@[simp] theorem uniformRowFlSqrtExactInputScaleDen_den
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtExactInputScaleDen fp hm hs hγs).den =
      fp.fl_sqrt ((s : ℝ) * (m : ℝ)⁻¹) := rfl

@[simp] theorem uniformRowFlSqrtExactInputScaleDen_den_abs_error
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtExactInputScaleDen fp hm hs hγs).den_abs_error =
      uniformRowSampleScaleDen (m := m) s * fp.u := rfl

/-- Concrete uniform-row denominator routine for Algorithm 3.

The row-sampling law remains the exact uniform law.  The non-probability
denominator used by the implementation is the rounded routine
`fl_sqrt (fl_div (s : R) (m : R))`, and the constructor below carries the
proved absolute denominator-error bound for that routine. -/
noncomputable def uniformRowFlDivThenSqrtScaleDen
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    ComputedUniformRowScaleDen fp m s :=
  ComputedUniformRowScaleDen.flDivThenSqrt fp hm hs
    (uniformRowUnitRoundoff_lt_one_of_pos_gammaValid fp hs hγs)

@[simp] theorem uniformRowFlDivThenSqrtScaleDen_den
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlDivThenSqrtScaleDen fp hm hs hγs).den =
      fp.fl_sqrt (fp.fl_div (s : ℝ) (m : ℝ)) := rfl

@[simp] theorem uniformRowFlDivThenSqrtScaleDen_den_abs_error
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlDivThenSqrtScaleDen fp hm hs hγs).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        (Real.sqrt (1 + fp.u) * fp.u + fp.u) := rfl

/-- Concrete uniform-row denominator routine for Algorithm 3.

The row-sampling law remains the exact uniform law.  The non-probability
denominator used by the implementation is the rounded routine
`fl_sqrt (fl_mul (s : R) (fl_div 1 (m : R)))`, and the constructor below
carries the proved absolute denominator-error bound for that routine. -/
noncomputable def uniformRowFlInvMulThenSqrtScaleDen
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    ComputedUniformRowScaleDen fp m s :=
  ComputedUniformRowScaleDen.flInvMulThenSqrt fp hm hs
    (uniformRowUnitRoundoff_lt_one_of_pos_gammaValid fp hs hγs)

@[simp] theorem uniformRowFlInvMulThenSqrtScaleDen_den
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlInvMulThenSqrtScaleDen fp hm hs hγs).den =
      fp.fl_sqrt (fp.fl_mul (s : ℝ) (fp.fl_div 1 (m : ℝ))) := rfl

@[simp] theorem uniformRowFlInvMulThenSqrtScaleDen_den_abs_error
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlInvMulThenSqrtScaleDen fp hm hs hγs).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
          (2 * fp.u + fp.u ^ 2)) := rfl

/-- Concrete uniform-row denominator routine for Algorithm 3.

The row-sampling law remains the exact uniform law.  The non-probability
denominator used by the implementation is the rounded routine
`fl_div (fl_sqrt (s : R)) (fl_sqrt (m : R))`, and the constructor below
carries the proved absolute denominator-error bound for that routine. -/
noncomputable def uniformRowFlSqrtDivSqrtScaleDen
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    ComputedUniformRowScaleDen fp m s :=
  ComputedUniformRowScaleDen.flSqrtDivSqrt fp hm hs
    (uniformRowUnitRoundoff_lt_one_of_pos_gammaValid fp hs hγs)

@[simp] theorem uniformRowFlSqrtDivSqrtScaleDen_den
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtDivSqrtScaleDen fp hm hs hγs).den =
      fp.fl_div (fp.fl_sqrt (s : ℝ)) (fp.fl_sqrt (m : ℝ)) := rfl

@[simp] theorem uniformRowFlSqrtDivSqrtScaleDen_den_abs_error
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtDivSqrtScaleDen fp hm hs hγs).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        ((3 * fp.u + fp.u ^ 2) / (1 - fp.u)) := rfl

/-- Concrete uniform-row denominator routine for Algorithm 3.

The row-sampling law remains the exact uniform law.  The non-probability
denominator used by the implementation is the rounded routine
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt m))`, and the constructor below carries
the proved absolute denominator-error bound for that routine. -/
noncomputable def uniformRowFlSqrtMulInvSqrtScaleDen
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    ComputedUniformRowScaleDen fp m s :=
  ComputedUniformRowScaleDen.flSqrtMulInvSqrt fp hm hs
    (uniformRowUnitRoundoff_lt_one_of_pos_gammaValid fp hs hγs)

@[simp] theorem uniformRowFlSqrtMulInvSqrtScaleDen_den
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs).den =
      fp.fl_mul (fp.fl_sqrt (s : ℝ))
        (fp.fl_div 1 (fp.fl_sqrt (m : ℝ))) := rfl

@[simp] theorem uniformRowFlSqrtMulInvSqrtScaleDen_den_abs_error
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u)) := rfl

/-- Exact uniform row-sampling sketch entry. -/
noncomputable def uniformRowSampleIncrement {m n : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  U i j / uniformRowSampleScaleDen (m := m) s

/-- Floating-point uniform row-sampling sketch entry, using the repository's
rounded division primitive. -/
noncomputable def fl_uniformRowSampleIncrement (fp : FPModel)
    {m n : ℕ} (s : ℕ) (U : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  fp.fl_div (U i j) (uniformRowSampleScaleDen (m := m) s)

/-- Exact uniform row-sampling sketch entry using a computed scale
    denominator. -/
noncomputable def uniformRowSampleIncrementWithComputedDen {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (den : ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  U i j / den

/-- Floating-point uniform row-sampling sketch entry using a computed scale
    denominator. -/
noncomputable def fl_uniformRowSampleIncrementWithComputedDen (fp : FPModel)
    {m n : ℕ} (U : Fin m → Fin n → ℝ) (den : ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  fp.fl_div (U i j) den

/-- Forward-error bound for one floating-point uniform row-scaling division. -/
theorem fl_uniformRowSampleIncrement_error_bound (fp : FPModel)
    {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n)
    (hdenom : uniformRowSampleScaleDen (m := m) s ≠ 0) :
    |fl_uniformRowSampleIncrement fp s U i j -
      uniformRowSampleIncrement s U i j| ≤
      |uniformRowSampleIncrement s U i j| * fp.u := by
  unfold fl_uniformRowSampleIncrement uniformRowSampleIncrement
  exact fl_div_error_bound fp (U i j)
    (uniformRowSampleScaleDen (m := m) s) hdenom

/-- Forward-error bound for one floating-point uniform row-scaling division
    with a computed denominator. -/
theorem fl_uniformRowSampleIncrementWithComputedDen_error_bound
    (fp : FPModel) {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (den : ℝ) (i : Fin m) (j : Fin n) (hdenom : den ≠ 0) :
    |fl_uniformRowSampleIncrementWithComputedDen fp U den i j -
      uniformRowSampleIncrementWithComputedDen U den i j| ≤
      |uniformRowSampleIncrementWithComputedDen U den i j| * fp.u := by
  unfold fl_uniformRowSampleIncrementWithComputedDen
    uniformRowSampleIncrementWithComputedDen
  exact fl_div_error_bound fp (U i j) den hdenom

/-- Exact uniform row sketch for a trace of sampled rows. -/
noncomputable def uniformRowSampleSketch {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin steps → Fin n → ℝ :=
  fun t j => uniformRowSampleIncrement s U (samples t) j

/-- Floating-point uniform row sketch for a trace of sampled rows. -/
noncomputable def fl_uniformRowSampleSketch (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin steps → Fin n → ℝ :=
  fun t j => fl_uniformRowSampleIncrement fp s U (samples t) j

/-- Exact uniform row sketch using a computed scale denominator. -/
noncomputable def uniformRowSampleSketchWithComputedDen {m n steps : ℕ}
    (U : Fin m → Fin n → ℝ) (den : ℝ) (samples : RowTrace m steps) :
    Fin steps → Fin n → ℝ :=
  fun t j => uniformRowSampleIncrementWithComputedDen U den (samples t) j

/-- Floating-point uniform row sketch using a computed scale denominator. -/
noncomputable def fl_uniformRowSampleSketchWithComputedDen (fp : FPModel)
    {m n steps : ℕ} (U : Fin m → Fin n → ℝ) (den : ℝ)
    (samples : RowTrace m steps) : Fin steps → Fin n → ℝ :=
  fun t j => fl_uniformRowSampleIncrementWithComputedDen fp U den (samples t) j

/-- Entrywise forward-error bound for the floating-point uniform row sketch. -/
theorem fl_uniformRowSampleSketch_error_bound (fp : FPModel)
    {m n steps s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hdenom : uniformRowSampleScaleDen (m := m) s ≠ 0) :
    |fl_uniformRowSampleSketch fp s U samples t j -
      uniformRowSampleSketch s U samples t j| ≤
      |uniformRowSampleSketch s U samples t j| * fp.u := by
  exact fl_uniformRowSampleIncrement_error_bound fp U (samples t) j hdenom

/-- Entrywise forward-error bound for the floating-point uniform row sketch
    with a computed scale denominator. -/
theorem fl_uniformRowSampleSketchWithComputedDen_error_bound (fp : FPModel)
    {m n steps : ℕ} (U : Fin m → Fin n → ℝ) (den : ℝ)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hdenom : den ≠ 0) :
    |fl_uniformRowSampleSketchWithComputedDen fp U den samples t j -
      uniformRowSampleSketchWithComputedDen U den samples t j| ≤
      |uniformRowSampleSketchWithComputedDen U den samples t j| * fp.u := by
  exact fl_uniformRowSampleIncrementWithComputedDen_error_bound fp U den
    (samples t) j hdenom

/-- Uniform row-scaling bound packaged for a computed denominator
    certificate. -/
theorem fl_uniformRowSampleSketch_computedDen_error_bound (fp : FPModel)
    {m n steps s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s) (samples : RowTrace m steps)
    (t : Fin steps) (j : Fin n) :
    |fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples t j -
      uniformRowSampleSketchWithComputedDen U dhat.den samples t j| ≤
      |uniformRowSampleSketchWithComputedDen U dhat.den samples t j| * fp.u :=
  fl_uniformRowSampleSketchWithComputedDen_error_bound fp U dhat.den
    samples t j dhat.den_ne_zero

/-- Perturbation from using a computed row-scale denominator instead of the
ideal `sqrt(s / m)` denominator.  The sampling law is still exact; this theorem
charges only the non-probability scalar used by the row scaling step. -/
theorem uniformRowSampleIncrementWithComputedDen_ideal_error_bound
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (i : Fin m) (j : Fin n)
    (hdenom : uniformRowSampleScaleDen (m := m) s ≠ 0) :
    |uniformRowSampleIncrementWithComputedDen U dhat.den i j -
      uniformRowSampleIncrement s U i j| ≤
      |U i j| * dhat.den_abs_error /
        (|dhat.den| * |uniformRowSampleScaleDen (m := m) s|) := by
  let d : ℝ := uniformRowSampleScaleDen (m := m) s
  have hdelta : |d - dhat.den| ≤ dhat.den_abs_error := by
    simpa [d, abs_sub_comm] using dhat.den_abs_error_bound
  have hd : d ≠ 0 := by
    simpa [d] using hdenom
  have hdenprod_nonneg : 0 ≤ |dhat.den| * |d| :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsplit :
      U i j / dhat.den - U i j / d =
        U i j * (d - dhat.den) / (dhat.den * d) := by
    field_simp [dhat.den_ne_zero, hd]
  unfold uniformRowSampleIncrementWithComputedDen uniformRowSampleIncrement
  calc
    |U i j / dhat.den - U i j / d|
        = |U i j * (d - dhat.den) / (dhat.den * d)| := by
            rw [hsplit]
    _ = |U i j| * |d - dhat.den| / (|dhat.den| * |d|) := by
            rw [abs_div, abs_mul, abs_mul]
    _ ≤ |U i j| * dhat.den_abs_error / (|dhat.den| * |d|) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdelta (abs_nonneg _))
              hdenprod_nonneg

/-- Total entrywise row-scaling error when the uniform-row denominator is
computed approximately and the division itself is rounded. -/
theorem fl_uniformRowSampleSketch_computedDen_total_error_bound
    (fp : FPModel) {m n steps s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s) (samples : RowTrace m steps)
    (t : Fin steps) (j : Fin n) (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    |fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples t j -
      uniformRowSampleSketch s U samples t j| ≤
      |uniformRowSampleSketchWithComputedDen U dhat.den samples t j| * fp.u +
        |U (samples t) j| * dhat.den_abs_error /
          (|dhat.den| * |uniformRowSampleScaleDen (m := m) s|) := by
  let Comp : ℝ :=
    uniformRowSampleSketchWithComputedDen U dhat.den samples t j
  let Exact : ℝ := uniformRowSampleSketch s U samples t j
  let Fl : ℝ :=
    fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples t j
  have hround :
      |Fl - Comp| ≤ |Comp| * fp.u := by
    simpa [Fl, Comp] using
      fl_uniformRowSampleSketch_computedDen_error_bound
        fp U dhat samples t j
  have hdenom : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  have hden :
      |Comp - Exact| ≤
        |U (samples t) j| * dhat.den_abs_error /
          (|dhat.den| * |uniformRowSampleScaleDen (m := m) s|) := by
    simpa [Comp, Exact, uniformRowSampleSketch,
      uniformRowSampleSketchWithComputedDen] using
      uniformRowSampleIncrementWithComputedDen_ideal_error_bound
        fp U dhat (samples t) j hdenom
  have hsplit : Fl - Exact = (Fl - Comp) + (Comp - Exact) := by ring
  calc
    |Fl - Exact|
        = |(Fl - Comp) + (Comp - Exact)| := by rw [hsplit]
    _ ≤ |Fl - Comp| + |Comp - Exact| := abs_add_le _ _
    _ ≤ |Comp| * fp.u +
        |U (samples t) j| * dhat.den_abs_error /
          (|dhat.den| * |uniformRowSampleScaleDen (m := m) s|) :=
        add_le_add hround hden

/-- Exact-denominator specialization of the computed-denominator row-scaling
bound.  With zero denominator error, the result reduces to the ordinary rounded
division bound for the ideal uniform row sketch. -/
theorem fl_uniformRowSampleSketch_computedDen_total_error_bound_exact
    (fp : FPModel) {m n steps s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    |fl_uniformRowSampleSketchWithComputedDen fp U
        (ComputedUniformRowScaleDen.exact fp hm hs).den samples t j -
      uniformRowSampleSketch s U samples t j| ≤
      |uniformRowSampleSketch s U samples t j| * fp.u := by
  have hdenom : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  simpa [fl_uniformRowSampleSketchWithComputedDen, fl_uniformRowSampleSketch,
    uniformRowSampleSketchWithComputedDen] using
    fl_uniformRowSampleSketch_error_bound fp U samples t j hdenom

/-- The exact row-sketch Gram of the uniformly rescaled sampled rows is the
uniform sample-average Gram matrix used by the exact concentration theorem. -/
theorem rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
    {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    rowSketchGram (uniformRowSampleSketch s U samples) =
      uniformRowSampleGram U samples := by
  classical
  funext j k
  have hden_ne : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
  have hden_sq :
      uniformRowSampleScaleDen (m := m) s ^ 2 =
        (s : ℝ) * (m : ℝ)⁻¹ := by
    unfold uniformRowSampleScaleDen
    rw [Real.sq_sqrt]
    exact mul_nonneg (le_of_lt hs) (inv_nonneg.mpr (le_of_lt hmRpos))
  unfold rowSketchGram uniformRowSampleSketch uniformRowSampleIncrement
    uniformRowSampleGram uniformRowOuterGramSample
  calc
    (∑ t : Fin s,
      U (samples t) j / uniformRowSampleScaleDen (m := m) s *
        (U (samples t) k / uniformRowSampleScaleDen (m := m) s))
        =
      ∑ t : Fin s,
        ((m : ℝ) * U (samples t) j * U (samples t) k) / (s : ℝ) := by
          apply Finset.sum_congr rfl
          intro t _
          calc
            U (samples t) j / uniformRowSampleScaleDen (m := m) s *
                (U (samples t) k / uniformRowSampleScaleDen (m := m) s)
                =
              (U (samples t) j * U (samples t) k) /
                (uniformRowSampleScaleDen (m := m) s ^ 2) := by
                  field_simp [hden_ne]
            _ =
              (U (samples t) j * U (samples t) k) /
                ((s : ℝ) * (m : ℝ)⁻¹) := by
                  rw [hden_sq]
            _ =
              ((m : ℝ) * U (samples t) j * U (samples t) k) / (s : ℝ) := by
                  field_simp [hs_ne, hm_ne]
    _ =
      (∑ t : Fin s, (m : ℝ) * U (samples t) j * U (samples t) k) /
        (s : ℝ) := by
          rw [Finset.sum_div]

/-- Sample-dependent exact sampled-Gram perturbation budget induced by an
entrywise absolute error certificate for a computed preconditioned basis
`Vhat`.  This budget charges only the computed basis entries; it does not charge
the uniform row law, which is exact and implementation-independent. -/
noncomputable def uniformRowSampleGramBasisPerturbBudget {m n s : ℕ}
    (V Vhat : Fin m → Fin n → ℝ) (E : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) : ℝ :=
  frobNorm
    (fun j k : Fin n =>
      ∑ t : Fin s,
        ((E (samples t) j / uniformRowSampleScaleDen (m := m) s) *
            |uniformRowSampleSketch s Vhat samples t k| +
          |uniformRowSampleSketch s V samples t j| *
            (E (samples t) k / uniformRowSampleScaleDen (m := m) s)))

/-- A computed preconditioned basis with entrywise absolute error `E` induces
the displayed sampled-Gram perturbation budget. -/
theorem uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
    {m n s : ℕ} (V Vhat : Fin m → Fin n → ℝ)
    (E : Fin m → Fin n → ℝ) (samples : RowTrace m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hE_nonneg : ∀ i j, 0 ≤ E i j)
    (hentry : ∀ i j, |Vhat i j - V i j| ≤ E i j) :
    frobNorm
      (fun j k =>
        uniformRowSampleGram Vhat samples j k -
          uniformRowSampleGram V samples j k) ≤
      uniformRowSampleGramBasisPerturbBudget V Vhat E samples := by
  classical
  let B : Fin s → Fin n → ℝ := uniformRowSampleSketch s V samples
  let Bhat : Fin s → Fin n → ℝ := uniformRowSampleSketch s Vhat samples
  let Escaled : Fin s → Fin n → ℝ :=
    fun t j => E (samples t) j / uniformRowSampleScaleDen (m := m) s
  have hden_pos : 0 < uniformRowSampleScaleDen (m := m) s := by
    unfold uniformRowSampleScaleDen
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    exact Real.sqrt_pos.2 (mul_pos hs (inv_pos.mpr hmRpos))
  have hEscaled_nonneg : ∀ t j, 0 ≤ Escaled t j := by
    intro t j
    exact div_nonneg (hE_nonneg (samples t) j) (le_of_lt hden_pos)
  have hBentry : ∀ t j, |Bhat t j - B t j| ≤ Escaled t j := by
    intro t j
    dsimp [B, Bhat, Escaled, uniformRowSampleSketch,
      uniformRowSampleIncrement]
    rw [← sub_div, abs_div, abs_of_pos hden_pos]
    exact div_le_div_of_nonneg_right
      (hentry (samples t) j) (le_of_lt hden_pos)
  have hgram :=
    rowSketchGram_frob_abs_error_bound_of_entrywise
      B Bhat Escaled hEscaled_nonneg hBentry
  have hB :
      rowSketchGram B = uniformRowSampleGram V samples := by
    simpa [B] using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        V samples hm hs
  have hBhat :
      rowSketchGram Bhat = uniformRowSampleGram Vhat samples := by
    simpa [Bhat] using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        Vhat samples hm hs
  simpa [uniformRowSampleGramBasisPerturbBudget, B, Bhat, Escaled, hB, hBhat]
    using hgram

-- ============================================================
-- Fully floating-point uniform sample Gram
-- ============================================================

/-- Fully floating-point uniform sampled Gram: form the rounded uniform row
sketch and compute each Gram entry using the repository dot-product algorithm. -/
noncomputable def fl_uniformRowSampleGramDot (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k =>
    fl_dotProduct fp steps
      (fun t => fl_uniformRowSampleSketch fp s U samples t j)
      (fun t => fl_uniformRowSampleSketch fp s U samples t k)

/-- Fully floating-point uniform sampled Gram with a computed denominator:
form each sampled row using `den` instead of the exact mathematical
`sqrt(s/m)`, round that division, and compute each Gram entry using the
repository dot-product algorithm. -/
noncomputable def fl_uniformRowSampleGramDotWithComputedDen (fp : FPModel)
    {m n steps : ℕ} (_s : ℕ)
    (U : Fin m → Fin n → ℝ) (den : ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k =>
    fl_dotProduct fp steps
      (fun t => fl_uniformRowSampleSketchWithComputedDen fp U den samples t j)
      (fun t => fl_uniformRowSampleSketchWithComputedDen fp U den samples t k)

/-- Sample-dependent row-scaling perturbation budget for a uniform row sketch.
It is expressed in terms of the exact uniformly rescaled sketch entries. -/
noncomputable def uniformRowSampleGramFpPerturbBudget (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) : ℝ :=
  frobNorm
    (fun j k : Fin n =>
      (2 * fp.u + fp.u ^ 2) *
        ∑ t : Fin steps,
          |uniformRowSampleSketch s U samples t j| *
            |uniformRowSampleSketch s U samples t k|)

/-- Sample-dependent dot-product perturbation budget for the fully
floating-point uniform sampled Gram. -/
noncomputable def uniformRowSampleGramDotProductBudget (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) : ℝ :=
  frobNorm
    (fun j k : Fin n =>
      gamma fp steps * (1 + fp.u) ^ 2 *
        ∑ t : Fin steps,
          |uniformRowSampleSketch s U samples t j| *
            |uniformRowSampleSketch s U samples t k|)

/-- Total sample-dependent perturbation budget for the fully floating-point
uniform sampled Gram. -/
noncomputable def uniformRowSampleGramFullFpPerturbBudget (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) : ℝ :=
  uniformRowSampleGramFpPerturbBudget fp s U samples +
    uniformRowSampleGramDotProductBudget fp s U samples

/-- Entrywise absolute error budget for a rounded uniform-row sketch built
with a computed denominator.  The first term is the rounded sampled-row
division, and the second term is the denominator-computation error measured
against the exact denominator `sqrt(s/m)`. -/
noncomputable def uniformRowSampleSketchComputedDenEntryAbsBudget
    (fp : FPModel) {m n steps s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n) : ℝ :=
  |uniformRowSampleSketchWithComputedDen U dhat.den samples t j| * fp.u +
    |U (samples t) j| * dhat.den_abs_error /
      (|dhat.den| * |uniformRowSampleScaleDen (m := m) s|)

/-- Sample-dependent exact-Gram perturbation budget for a uniform-row sketch
whose row denominator has been computed before the rounded row divisions. -/
noncomputable def uniformRowSampleGramComputedDenScalePerturbBudget
    (fp : FPModel) {m n steps s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (samples : RowTrace m steps) : ℝ :=
  let B : Fin steps → Fin n → ℝ := uniformRowSampleSketch s U samples
  let Bhat : Fin steps → Fin n → ℝ :=
    fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples
  let E : Fin steps → Fin n → ℝ :=
    uniformRowSampleSketchComputedDenEntryAbsBudget fp U dhat samples
  frobNorm
    (fun j k : Fin n =>
      ∑ t : Fin steps, (E t j * |Bhat t k| + |B t j| * E t k))

/-- Sample-dependent dot-product budget for a uniform sampled Gram whose row
sketch was formed with a computed denominator.  It is written directly in
terms of the actually rounded sketch inputs to the dot products. -/
noncomputable def uniformRowSampleGramComputedDenDotProductBudget
    (fp : FPModel) {m n steps s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (samples : RowTrace m steps) : ℝ :=
  let Bhat : Fin steps → Fin n → ℝ :=
    fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples
  frobNorm
    (fun j k : Fin n =>
      gamma fp steps *
        ∑ t : Fin steps, |Bhat t j| * |Bhat t k|)

/-- Total sample-dependent perturbation budget for the fully floating-point
uniform sampled Gram with computed denominator. -/
noncomputable def uniformRowSampleGramComputedDenFullFpPerturbBudget
    (fp : FPModel) {m n steps s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (samples : RowTrace m steps) : ℝ :=
  uniformRowSampleGramComputedDenScalePerturbBudget fp U dhat samples +
    uniformRowSampleGramComputedDenDotProductBudget fp U dhat samples

/-- The sample-dependent uniform FP Gram perturbation budget is nonnegative. -/
theorem uniformRowSampleGramFullFpPerturbBudget_nonneg (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    0 ≤ uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
  unfold uniformRowSampleGramFullFpPerturbBudget
    uniformRowSampleGramFpPerturbBudget
    uniformRowSampleGramDotProductBudget
  exact add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

/-- The sample-dependent computed-denominator uniform FP Gram perturbation
budget is nonnegative. -/
theorem uniformRowSampleGramComputedDenFullFpPerturbBudget_nonneg
    (fp : FPModel) {m n steps s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (samples : RowTrace m steps) :
    0 ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
  unfold uniformRowSampleGramComputedDenFullFpPerturbBudget
  exact add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

/-- Deterministic constant budget for the row-scaling part of the uniform
sampled-Gram perturbation.  The scalar `C` bounds every sampled absolute-product
sum `∑ₜ |B_tj| |B_tk|`. -/
noncomputable def uniformRowSampleGramFpPerturbConstBudget (fp : FPModel)
    {n : ℕ} (C : ℝ) : ℝ :=
  frobNorm (fun _j _k : Fin n => (2 * fp.u + fp.u ^ 2) * C)

/-- Deterministic constant budget for the dot-product part of the uniform
sampled-Gram perturbation. -/
noncomputable def uniformRowSampleGramDotProductConstBudget (fp : FPModel)
    {n : ℕ} (steps : ℕ) (C : ℝ) : ℝ :=
  frobNorm
    (fun _j _k : Fin n => gamma fp steps * (1 + fp.u) ^ 2 * C)

/-- Total deterministic constant budget for the fully floating-point uniform
sampled Gram. -/
noncomputable def uniformRowSampleGramFullFpConstBudget (fp : FPModel)
    {n : ℕ} (steps : ℕ) (C : ℝ) : ℝ :=
  uniformRowSampleGramFpPerturbConstBudget fp (n := n) C +
    uniformRowSampleGramDotProductConstBudget fp (n := n) steps C

/-- Closed form of the row-scaling constant budget, exposing the dimension of
the Gram matrix. -/
theorem uniformRowSampleGramFpPerturbConstBudget_eq_nat_mul
    (fp : FPModel) {n : ℕ} {C : ℝ} (hC : 0 ≤ C) :
    uniformRowSampleGramFpPerturbConstBudget fp (n := n) C =
      (n : ℝ) * ((2 * fp.u + fp.u ^ 2) * C) := by
  have hscale : 0 ≤ (2 * fp.u + fp.u ^ 2) * C := by
    have hu : 0 ≤ 2 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg, sq_nonneg fp.u]
    exact mul_nonneg hu hC
  unfold uniformRowSampleGramFpPerturbConstBudget
  exact frobNorm_const hscale

/-- Closed form of the dot-product constant budget, exposing the dimension of
the Gram matrix. -/
theorem uniformRowSampleGramDotProductConstBudget_eq_nat_mul
    (fp : FPModel) {n steps : ℕ} {C : ℝ}
    (hγ : gammaValid fp steps) (hC : 0 ≤ C) :
    uniformRowSampleGramDotProductConstBudget fp (n := n) steps C =
      (n : ℝ) * (gamma fp steps * (1 + fp.u) ^ 2 * C) := by
  have hscale : 0 ≤ gamma fp steps * (1 + fp.u) ^ 2 * C := by
    have hleft : 0 ≤ gamma fp steps * (1 + fp.u) ^ 2 :=
      mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + fp.u))
    exact mul_nonneg hleft hC
  unfold uniformRowSampleGramDotProductConstBudget
  exact frobNorm_const hscale

/-- A row-norm bound controls one unscaled row product. -/
theorem abs_mul_entry_le_rowNormSq {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) (j k : Fin n) :
    |U i j| * |U i k| ≤ rowNormSq U i := by
  let x : Fin n → ℝ := fun l => U i l
  have hj : |U i j| ≤ vecNorm2 x := by
    simpa [x] using abs_coord_le_vecNorm2 x j
  have hk : |U i k| ≤ vecNorm2 x := by
    simpa [x] using abs_coord_le_vecNorm2 x k
  calc
    |U i j| * |U i k|
        ≤ vecNorm2 x * vecNorm2 x :=
          mul_le_mul hj hk (abs_nonneg _) (vecNorm2_nonneg x)
    _ = rowNormSq U i := by
          rw [← sq, vecNorm2_sq]
          rfl

/-- If every sampled row has squared norm at most `R`, then every
absolute-product sum in the uniformly rescaled sketch is at most `m R`. -/
theorem uniformRowSampleSketch_abs_mul_sum_le_of_rowNormSq_le
    {m n s : ℕ} (U : Fin m → Fin n → ℝ) (samples : RowTrace m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    {R : ℝ} (hrow : ∀ t : Fin s, rowNormSq U (samples t) ≤ R)
    (j k : Fin n) :
    (∑ t : Fin s,
        |uniformRowSampleSketch s U samples t j| *
          |uniformRowSampleSketch s U samples t k|) ≤
      (m : ℝ) * R := by
  classical
  have hden_ne : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  have hden_pos : 0 < uniformRowSampleScaleDen (m := m) s := by
    unfold uniformRowSampleScaleDen
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    exact Real.sqrt_pos.2 (mul_pos hs (inv_pos.mpr hmRpos))
  have hden_sq :
      uniformRowSampleScaleDen (m := m) s ^ 2 =
        (s : ℝ) * (m : ℝ)⁻¹ := by
    unfold uniformRowSampleScaleDen
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    rw [Real.sq_sqrt]
    exact mul_nonneg (le_of_lt hs) (inv_nonneg.mpr (le_of_lt hmRpos))
  have hden_sq_pos : 0 < uniformRowSampleScaleDen (m := m) s ^ 2 := by
    exact sq_pos_of_ne_zero hden_ne
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
  calc
    (∑ t : Fin s,
        |uniformRowSampleSketch s U samples t j| *
          |uniformRowSampleSketch s U samples t k|)
        ≤ ∑ _t : Fin s, ((m : ℝ) * R) / (s : ℝ) := by
            apply Finset.sum_le_sum
            intro t _
            have hprodU :
                |U (samples t) j| * |U (samples t) k| ≤ R :=
              (abs_mul_entry_le_rowNormSq U (samples t) j k).trans (hrow t)
            unfold uniformRowSampleSketch uniformRowSampleIncrement
            calc
              |U (samples t) j / uniformRowSampleScaleDen (m := m) s| *
                  |U (samples t) k / uniformRowSampleScaleDen (m := m) s|
                  =
                (|U (samples t) j| * |U (samples t) k|) /
                  (uniformRowSampleScaleDen (m := m) s ^ 2) := by
                    rw [abs_div, abs_div, abs_of_pos hden_pos]
                    field_simp [hden_ne]
              _ ≤ R / (uniformRowSampleScaleDen (m := m) s ^ 2) :=
                    div_le_div_of_nonneg_right hprodU (le_of_lt hden_sq_pos)
              _ = ((m : ℝ) * R) / (s : ℝ) := by
                    rw [hden_sq]
                    field_simp [hs_ne, hm_ne]
    _ = (m : ℝ) * R := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
          field_simp [hs_ne]

/-- The sample-dependent uniform row-scaling FP budget is bounded by the
constant budget whenever all sampled absolute-product sums are bounded by `C`.
-/
theorem uniformRowSampleGramFpPerturbBudget_le_const_of_abs_mul_sum_le
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) {C : ℝ} (hC : 0 ≤ C)
    (hprod :
      ∀ j k : Fin n,
        (∑ t : Fin s,
          |uniformRowSampleSketch s U samples t j| *
            |uniformRowSampleSketch s U samples t k|) ≤ C) :
    uniformRowSampleGramFpPerturbBudget fp s U samples ≤
      uniformRowSampleGramFpPerturbConstBudget fp (n := n) C := by
  classical
  let c : ℝ := 2 * fp.u + fp.u ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  unfold uniformRowSampleGramFpPerturbBudget
    uniformRowSampleGramFpPerturbConstBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hc hC
  · intro j k
    let S : ℝ :=
      ∑ t : Fin s,
        |uniformRowSampleSketch s U samples t j| *
          |uniformRowSampleSketch s U samples t k|
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      |(2 * fp.u + fp.u ^ 2) * S|
          = c * S := by
              simp [c, S, abs_of_nonneg (mul_nonneg hc hS_nonneg)]
      _ ≤ c * C := mul_le_mul_of_nonneg_left (by simpa [S] using hprod j k) hc
      _ = (2 * fp.u + fp.u ^ 2) * C := by simp [c]

/-- The sample-dependent uniform dot-product FP budget is bounded by the
constant budget whenever all sampled absolute-product sums are bounded by `C`.
-/
theorem uniformRowSampleGramDotProductBudget_le_const_of_abs_mul_sum_le
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) {C : ℝ} (hγ : gammaValid fp s) (hC : 0 ≤ C)
    (hprod :
      ∀ j k : Fin n,
        (∑ t : Fin s,
          |uniformRowSampleSketch s U samples t j| *
            |uniformRowSampleSketch s U samples t k|) ≤ C) :
    uniformRowSampleGramDotProductBudget fp s U samples ≤
      uniformRowSampleGramDotProductConstBudget fp (n := n) s C := by
  classical
  let c : ℝ := gamma fp s * (1 + fp.u) ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + fp.u))
  unfold uniformRowSampleGramDotProductBudget
    uniformRowSampleGramDotProductConstBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hc hC
  · intro j k
    let S : ℝ :=
      ∑ t : Fin s,
        |uniformRowSampleSketch s U samples t j| *
          |uniformRowSampleSketch s U samples t k|
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      |gamma fp s * (1 + fp.u) ^ 2 * S|
          = c * S := by
              simp [c, S, abs_of_nonneg (mul_nonneg hc hS_nonneg)]
      _ ≤ c * C := mul_le_mul_of_nonneg_left (by simpa [S] using hprod j k) hc
      _ = gamma fp s * (1 + fp.u) ^ 2 * C := by simp [c]

/-- The sample-dependent total FP budget is bounded by a deterministic constant
budget under the same absolute-product-sum bound. -/
theorem uniformRowSampleGramFullFpPerturbBudget_le_const_of_abs_mul_sum_le
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) {C : ℝ} (hγ : gammaValid fp s) (hC : 0 ≤ C)
    (hprod :
      ∀ j k : Fin n,
        (∑ t : Fin s,
          |uniformRowSampleSketch s U samples t j| *
            |uniformRowSampleSketch s U samples t k|) ≤ C) :
    uniformRowSampleGramFullFpPerturbBudget fp s U samples ≤
      uniformRowSampleGramFullFpConstBudget fp (n := n) s C := by
  unfold uniformRowSampleGramFullFpPerturbBudget
    uniformRowSampleGramFullFpConstBudget
  exact add_le_add
    (uniformRowSampleGramFpPerturbBudget_le_const_of_abs_mul_sum_le
      fp U samples hC hprod)
    (uniformRowSampleGramDotProductBudget_le_const_of_abs_mul_sum_le
      fp U samples hγ hC hprod)

/-- Row-norm version of the deterministic constant FP-budget cap: if every
sampled row of `U` has squared norm at most `R`, then the full sampled-Gram FP
budget is bounded by the constant-budget expression with `C = m R`. -/
theorem uniformRowSampleGramFullFpPerturbBudget_le_const_of_sample_rowNormSq_le
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ t : Fin s, rowNormSq U (samples t) ≤ R) :
    uniformRowSampleGramFullFpPerturbBudget fp s U samples ≤
      uniformRowSampleGramFullFpConstBudget fp (n := n) s ((m : ℝ) * R) := by
  have hC : 0 ≤ (m : ℝ) * R := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le m) hR
  exact
    uniformRowSampleGramFullFpPerturbBudget_le_const_of_abs_mul_sum_le
      fp U samples hγ hC
      (uniformRowSampleSketch_abs_mul_sum_le_of_rowNormSq_le
        U samples hm hs hrow)

/-- Deterministic fully-floating-point perturbation bound for uniform row
sampling, reusing the repository division and dot-product stability results. -/
theorem fl_uniformRowSampleGramDot_perturb_bound
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (samples : RowTrace m s) :
    frobNorm
      (fun j k =>
        fl_uniformRowSampleGramDot fp s U samples j k -
          uniformRowSampleGram U samples j k) ≤
      uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
  classical
  let B : Fin s → Fin n → ℝ := uniformRowSampleSketch s U samples
  let Bhat : Fin s → Fin n → ℝ := fl_uniformRowSampleSketch fp s U samples
  have hden_ne : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  have hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * fp.u := by
    intro t j
    simpa [B, Bhat] using
      fl_uniformRowSampleSketch_error_bound fp U samples t j hden_ne
  have hdot :
      frobNorm
        (fun j k =>
          fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) ≤
        uniformRowSampleGramDotProductBudget fp s U samples := by
    have hlocal :=
      rowSketchGram_dot_frob_error_bound_of_entrywise
        fp B Bhat fp.u fp.u_nonneg hγ hentry
    simpa [uniformRowSampleGramDotProductBudget, B] using hlocal
  have hBgram :
      rowSketchGram B = uniformRowSampleGram U samples := by
    simpa [B] using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        U samples hm hs
  have hscale :
      frobNorm
        (fun j k =>
          rowSketchGram Bhat j k - uniformRowSampleGram U samples j k) ≤
        uniformRowSampleGramFpPerturbBudget fp s U samples := by
    have hpoint :=
      rowSketchGram_frob_error_bound_of_entrywise
        B Bhat fp.u fp.u_nonneg hentry
    simpa [uniformRowSampleGramFpPerturbBudget, B, hBgram] using hpoint
  have hsplit :
      (fun j k =>
        fl_uniformRowSampleGramDot fp s U samples j k -
          uniformRowSampleGram U samples j k) =
      (fun j k =>
        (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k) +
        (rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)) := by
    funext j k
    simp [fl_uniformRowSampleGramDot, Bhat]
  have htri :=
    frobNorm_add_le
      (fun j k =>
        fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k)
      (fun j k => rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)
  calc
    frobNorm
      (fun j k =>
        fl_uniformRowSampleGramDot fp s U samples j k -
          uniformRowSampleGram U samples j k)
        =
      frobNorm
        (fun j k =>
          (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) +
          (rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)) := by
          rw [hsplit]
    _ ≤
        frobNorm
          (fun j k =>
            fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
        frobNorm
          (fun j k =>
            rowSketchGram Bhat j k - uniformRowSampleGram U samples j k) :=
          htri
    _ ≤ uniformRowSampleGramDotProductBudget fp s U samples +
        uniformRowSampleGramFpPerturbBudget fp s U samples :=
          add_le_add hdot hscale
    _ = uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
          unfold uniformRowSampleGramFullFpPerturbBudget
          ring

/-- Deterministic fully-floating-point perturbation bound for uniform row
sampling when the non-probability denominator `sqrt(s/m)` is itself computed.

The exact row law is still the uniform law.  The budget charges the computed
denominator certificate, rounded row divisions, and rounded Gram dot products.
-/
theorem fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (samples : RowTrace m s) :
    frobNorm
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s U dhat.den samples j k -
          uniformRowSampleGram U samples j k) ≤
      uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
  classical
  let B : Fin s → Fin n → ℝ := uniformRowSampleSketch s U samples
  let Bhat : Fin s → Fin n → ℝ :=
    fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples
  let E : Fin s → Fin n → ℝ :=
    uniformRowSampleSketchComputedDenEntryAbsBudget fp U dhat samples
  have hden_ne : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  have hE_nonneg : ∀ t j, 0 ≤ E t j := by
    intro t j
    dsimp [E, uniformRowSampleSketchComputedDenEntryAbsBudget]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _) fp.u_nonneg)
      (div_nonneg
        (mul_nonneg (abs_nonneg _) dhat.den_abs_error_nonneg)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have hentry : ∀ t j, |Bhat t j - B t j| ≤ E t j := by
    intro t j
    simpa [B, Bhat, E, uniformRowSampleSketchComputedDenEntryAbsBudget] using
      fl_uniformRowSampleSketch_computedDen_total_error_bound
        fp U dhat samples t j hm hs
  have hscale :
      frobNorm
        (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k) ≤
      uniformRowSampleGramComputedDenScalePerturbBudget fp U dhat samples := by
    simpa [uniformRowSampleGramComputedDenScalePerturbBudget, B, Bhat, E] using
      rowSketchGram_frob_abs_error_bound_of_entrywise
        B Bhat E hE_nonneg hentry
  have hdot :
      frobNorm
        (fun j k =>
          fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) ≤
      uniformRowSampleGramComputedDenDotProductBudget fp U dhat samples := by
    apply frobNorm_le_of_entry_abs_le
    · intro j k
      apply mul_nonneg (gamma_nonneg fp hγ)
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    · intro j k
      simpa [uniformRowSampleGramComputedDenDotProductBudget, Bhat] using
        dotProduct_error_bound fp s
          (fun t => Bhat t j) (fun t => Bhat t k) hγ
  have hBgram :
      rowSketchGram B = uniformRowSampleGram U samples := by
    simpa [B] using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        U samples hm hs
  have hscale' :
      frobNorm
        (fun j k => rowSketchGram Bhat j k - uniformRowSampleGram U samples j k) ≤
      uniformRowSampleGramComputedDenScalePerturbBudget fp U dhat samples := by
    simpa [hBgram] using hscale
  have hsplit :
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s U dhat.den samples j k -
          uniformRowSampleGram U samples j k) =
      (fun j k =>
        (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k) +
        (rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)) := by
    funext j k
    simp [fl_uniformRowSampleGramDotWithComputedDen, Bhat]
  have htri :=
    frobNorm_add_le
      (fun j k =>
        fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k)
      (fun j k => rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)
  calc
    frobNorm
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s U dhat.den samples j k -
          uniformRowSampleGram U samples j k)
        =
      frobNorm
        (fun j k =>
          (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) +
          (rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)) := by
          rw [hsplit]
    _ ≤
        frobNorm
          (fun j k =>
            fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
        frobNorm
          (fun j k =>
            rowSketchGram Bhat j k - uniformRowSampleGram U samples j k) :=
          htri
    _ ≤ uniformRowSampleGramComputedDenDotProductBudget fp U dhat samples +
        uniformRowSampleGramComputedDenScalePerturbBudget fp U dhat samples :=
          add_le_add hdot hscale'
    _ = uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
          unfold uniformRowSampleGramComputedDenFullFpPerturbBudget
          ring

-- ============================================================
-- High-probability Frobenius FP transfer for arbitrary uniform-row inputs
-- ============================================================

/-- Exact iid uniform-row Frobenius event around the exact Gram `UᵀU`.

This event is exact arithmetic: the row law is exact and the sampled Gram is
the exact mathematical average. -/
def uniformRowSampleGramRowGramFrobErrorEvent {m n s : ℕ}
    (U : Fin m → Fin n → ℝ) (η : ℝ) :
    Set (RowTrace m s) :=
  {samples |
    frobNorm
      (fun j k : Fin n => uniformRowSampleGram U samples j k - rowGram U j k) ≤
      η}

/-- Floating-point iid uniform-row Frobenius event around the exact Gram
`UᵀU`, using the exact mathematical denominator in the row-scaling division.

The event charges rounded row divisions and rounded Gram dot products through
the concrete sample-dependent budget. -/
def uniformRowFlSampleGramDotRowGramFrobErrorEvent
    (fp : FPModel) {m n s : ℕ}
    (U : Fin m → Fin n → ℝ) (η : ℝ) :
    Set (RowTrace m s) :=
  {samples |
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s U samples j k - rowGram U j k) ≤
      η + uniformRowSampleGramFullFpPerturbBudget fp s U samples}

/-- Floating-point iid uniform-row Frobenius event around the exact Gram
`UᵀU`, with a computed non-probability denominator.  The event charges
denominator computation, rounded row divisions, and rounded Gram dot products
through the concrete sample-dependent budget. -/
def uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent
    (fp : FPModel) {m n s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (η : ℝ) :
    Set (RowTrace m s) :=
  {samples |
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s U dhat.den samples j k -
          rowGram U j k) ≤
      η + uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples}

/-- The exact Frobenius event transfers to the fully floating-point event with
the exact mathematical row-scale denominator. -/
theorem uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDot
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) :
    uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η ⊆
      uniformRowFlSampleGramDotRowGramFrobErrorEvent (s := s) fp U η := by
  classical
  intro samples hsamples
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDot fp s U samples j k -
        uniformRowSampleGram U samples j k
  let DeltaExact : Fin n → Fin n → ℝ :=
    fun j k => uniformRowSampleGram U samples j k - rowGram U j k
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
    simpa [DeltaFp] using
      fl_uniformRowSampleGramDot_perturb_bound fp U hm hs hγ samples
  have hExact : frobNorm DeltaExact ≤ η := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent, DeltaExact]
      using hsamples
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s U samples j k - rowGram U j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaExact j k) := by
    funext j k
    dsimp [DeltaFp, DeltaExact]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaExact
  have hbound :
      frobNorm
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s U samples j k - rowGram U j k) ≤
        η + uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
    calc
      frobNorm
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s U samples j k - rowGram U j k)
          =
        frobNorm (fun j k : Fin n => DeltaFp j k + DeltaExact j k) := by
          rw [hsplit]
      _ ≤ frobNorm DeltaFp + frobNorm DeltaExact := htri
      _ ≤ η + uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
          linarith
  simpa [uniformRowFlSampleGramDotRowGramFrobErrorEvent] using hbound

/-- The exact Frobenius event transfers to the fully floating-point event with
a computed non-probability row-scale denominator. -/
theorem uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDotWithComputedDen
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) :
    uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η ⊆
      uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent
        (s := s) fp U dhat η := by
  classical
  intro samples hsamples
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen
          fp s U dhat.den samples j k -
        uniformRowSampleGram U samples j k
  let DeltaExact : Fin n → Fin n → ℝ :=
    fun j k => uniformRowSampleGram U samples j k - rowGram U j k
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
    simpa [DeltaFp] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp U dhat hm hs hγ samples
  have hExact : frobNorm DeltaExact ≤ η := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent, DeltaExact]
      using hsamples
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s U dhat.den samples j k -
          rowGram U j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaExact j k) := by
    funext j k
    dsimp [DeltaFp, DeltaExact]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaExact
  have hbound :
      frobNorm
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s U dhat.den samples j k -
            rowGram U j k) ≤
        η + uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
    calc
      frobNorm
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s U dhat.den samples j k -
            rowGram U j k)
          =
        frobNorm (fun j k : Fin n => DeltaFp j k + DeltaExact j k) := by
          rw [hsplit]
      _ ≤ frobNorm DeltaFp + frobNorm DeltaExact := htri
      _ ≤
          η + uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
          linarith
  simpa [uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent]
    using hbound
















































































































-- ============================================================
-- High-probability floating-point transfer for Algorithm 3
-- ============================================================

/-- The floating-point two-sided uniform-row sample-Gram event after
signed-Hadamard preprocessing.  The Loewner radius is the exact sampling radius
plus the explicit sample-dependent FP perturbation budget. -/
def signedHadamardFlUniformRowSampleGramTwoSidedEvent (fp : FPModel)
    {m n s : ℕ} (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (ε : ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    let τ : ℝ := uniformRowSampleGramFullFpPerturbBudget fp s V x.2
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k)}

/-- Floating-point two-sided uniform-row sample-Gram event with a deterministic
FP perturbation radius `τ`. -/
def signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent (fp : FPModel)
    {m n s : ℕ} (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (ε τ : ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k)}

/-- Floating-point two-sided uniform-row sample-Gram event for an implemented
preprocessed basis `Vhat`.  The function `τ` is allowed to depend on both the
Rademacher preprocessing outcome and the sampled row trace, so it can charge
computed Hadamard/sign/basis arithmetic, computed row scaling, and rounded Gram
dot products in one visible radius. -/
def signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
    (fp : FPModel) {m n s : ℕ}
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace m s → ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Constant-radius version of the computed-preprocessed floating-point
uniform-row event. -/
def signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent
    (fp : FPModel) {m n s : ℕ}
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (ε τ : ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
    fp Vhat ε (fun _ => τ)

/-- Floating-point two-sided uniform-row sample-Gram event for an implemented
preprocessed basis `Vhat` when the row-scale denominator `sqrt(s/m)` is also a
computed non-probability quantity. -/
def signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {m n s : ℕ}
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace m s → ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Perturbation event connecting the implemented preprocessed basis `Vhat` to
the exact signed-Hadamard basis `H D_ω U`.  This event is intentionally generic:
it is where a concrete FP implementation of `H`, the diagonal signs, a basis
`U`, or any singular-vector routine must pay its error budget. -/
def signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (τ : RademacherTrace m × RowTrace m s → ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

/-- Constant-radius version of the computed-preprocessed perturbation event. -/
def signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (τ : ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
    fp H U Vhat (fun _ => τ)

/-- Perturbation event connecting the implemented preprocessed basis `Vhat`,
computed row denominator, rounded row scaling, and rounded Gram dot products
to the exact signed-Hadamard basis `H D_ω U`. -/
def signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (τ : RademacherTrace m × RowTrace m s → ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

-- ============================================================
-- Exact right-factor congruence for Algorithm 3 input matrices
-- ============================================================

/-- Right-factor congruence `Cᵀ M C` for finite real matrices.

This is the exact analysis bridge from an orthonormal-column basis `U` to an
Algorithm 3 input matrix factored as `A = U C`. -/
noncomputable def rightGramCongruence {r n : ℕ}
    (M : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ a : Fin r, ∑ b : Fin r, C a j * M a b * C b k

/-- Left preprocessing commutes with a deterministic right factor. -/
theorem preconditionRows_preconditionColumns_assoc {m r n : ℕ}
    (P : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) :
    preconditionRows P (preconditionColumns U C) =
      preconditionColumns (preconditionRows P U) C := by
  classical
  ext i j
  unfold preconditionRows preconditionColumns
  conv_lhs => arg 2; ext k; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Rectangular left preprocessing commutes with a deterministic right factor. -/
theorem preconditionRows_preconditionColumns_assoc_rect {r m q n : ℕ}
    (P : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ) :
    preconditionRows P (preconditionColumns U C) =
      preconditionColumns (preconditionRows P U) C := by
  classical
  ext i j
  unfold preconditionRows preconditionColumns
  conv_lhs => arg 2; ext k; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Quadratic forms commute with the right-factor congruence `Cᵀ M C`. -/
theorem finiteQuadraticForm_rightGramCongruence {r n : ℕ}
    (M : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (x : Fin n → ℝ) :
    finiteQuadraticForm (rightGramCongruence M C) x =
      finiteQuadraticForm M (fun a : Fin r => ∑ j : Fin n, C a j * x j) := by
  classical
  let y : Fin r → ℝ := fun a => ∑ j : Fin n, C a j * x j
  have hmat : ∀ j : Fin n,
      finiteMatVec (rightGramCongruence M C) x j =
        ∑ a : Fin r, C a j * finiteMatVec M y a := by
    intro j
    unfold finiteMatVec rightGramCongruence y
    conv_lhs => arg 2; ext k; rw [Finset.sum_mul]
    conv_lhs => arg 2; ext k; arg 2; ext a; rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    finiteQuadraticForm (rightGramCongruence M C) x
        =
      ∑ j : Fin n, x j * (∑ a : Fin r, C a j * finiteMatVec M y a) := by
        unfold finiteQuadraticForm
        apply Finset.sum_congr rfl
        intro j _
        rw [hmat]
    _ =
      ∑ a : Fin r, (∑ j : Fin n, C a j * x j) * finiteMatVec M y a := by
        conv_lhs => arg 2; ext j; rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ =
      finiteQuadraticForm M y := by
        rfl

/-- Loewner order is preserved by right-factor congruence. -/
theorem finiteLoewnerLe_rightGramCongruence {r n : ℕ}
    {M N : Fin r → Fin r → ℝ} (C : Fin r → Fin n → ℝ)
    (hMN : finiteLoewnerLe M N) :
    finiteLoewnerLe (rightGramCongruence M C)
      (rightGramCongruence N C) := by
  intro x
  rw [finiteQuadraticForm_rightGramCongruence,
    finiteQuadraticForm_rightGramCongruence]
  exact hMN (fun a : Fin r => ∑ j : Fin n, C a j * x j)

/-- Congruence of a scalar identity is the scalar Gram of the right factor. -/
theorem rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram {r n : ℕ}
    (C : Fin r → Fin n → ℝ) (ε : ℝ) :
    rightGramCongruence (fun a b : Fin r => ε * finiteIdMatrix a b) C =
      fun j k : Fin n => ε * rowGram C j k := by
  classical
  ext j k
  unfold rightGramCongruence rowGram finiteIdMatrix
  calc
    ∑ a : Fin r, ∑ b : Fin r, C a j * (ε * if a = b then 1 else 0) * C b k
        =
      ∑ a : Fin r, C a j * (ε * 1) * C a k := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb
          have hneq : a ≠ b := Ne.symm hb
          simp [hneq]
        · intro hnot
          exact (hnot (Finset.mem_univ a)).elim
    _ = ε * ∑ a : Fin r, C a j * C a k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring

/-- Congruence of the identity is the Gram of the right factor. -/
theorem rightGramCongruence_finiteIdMatrix_eq_rowGram {r n : ℕ}
    (C : Fin r → Fin n → ℝ) :
    rightGramCongruence (finiteIdMatrix : Fin r → Fin r → ℝ) C =
      rowGram C := by
  have h := rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1
  simpa using h

/-- Right-factor congruence is additive. -/
theorem rightGramCongruence_add {r n : ℕ}
    (M N : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ) :
    rightGramCongruence (fun a b => M a b + N a b) C =
      fun j k => rightGramCongruence M C j k +
        rightGramCongruence N C j k := by
  classical
  ext j k
  unfold rightGramCongruence
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Right-factor congruence commutes with negation. -/
theorem rightGramCongruence_neg {r n : ℕ}
    (M : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ) :
    rightGramCongruence (fun a b => -M a b) C =
      fun j k => -rightGramCongruence M C j k := by
  classical
  ext j k
  unfold rightGramCongruence
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Right-factor congruence commutes with subtraction. -/
theorem rightGramCongruence_sub {r n : ℕ}
    (M N : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ) :
    rightGramCongruence (fun a b => M a b - N a b) C =
      fun j k => rightGramCongruence M C j k -
        rightGramCongruence N C j k := by
  classical
  ext j k
  unfold rightGramCongruence
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A two-sided Loewner bound with an arbitrary exact right-hand side is stable
under an additive perturbation whose Frobenius norm is at most `τ`; the
right-hand side gains `τ I`. -/
theorem finiteLoewnerLe_two_sided_add_general_of_frobNorm_le {n : ℕ}
    (Exact Delta Eps : Fin n → Fin n → ℝ) {τ : ℝ}
    (hExactUpper : finiteLoewnerLe Exact Eps)
    (hExactLower : finiteLoewnerLe (fun j k => -Exact j k) Eps)
    (hpert : frobNorm Delta ≤ τ) :
    finiteLoewnerLe
        (fun j k : Fin n => Exact j k + Delta j k)
        (fun j k : Fin n => Eps j k + τ * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n => -(Exact j k + Delta j k))
        (fun j k : Fin n => Eps j k + τ * finiteIdMatrix j k) := by
  classical
  have hDeltaOp : opNorm2Le Delta τ :=
    opNorm2Le_of_frobNorm_le Delta hpert
  have hDeltaUpper :
      finiteLoewnerLe Delta
        (fun j k : Fin n => τ * finiteIdMatrix j k) := by
    intro x
    rw [finiteQuadraticForm_smul_finiteIdMatrix]
    have habs :=
      abs_vecInnerProduct_matMulVec_le_of_opNorm2Le Delta hDeltaOp x
    have hquad :
        |finiteQuadraticForm Delta x| ≤ τ * finiteVecNorm2Sq x := by
      simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
        finiteVecNorm2Sq, vecNorm2Sq] using habs
    exact (le_abs_self (finiteQuadraticForm Delta x)).trans hquad
  have hDeltaLower :
      finiteLoewnerLe (fun j k : Fin n => -Delta j k)
        (fun j k : Fin n => τ * finiteIdMatrix j k) := by
    intro x
    rw [finiteQuadraticForm_smul_finiteIdMatrix]
    have hDeltaNegOp :
        opNorm2Le (fun j k : Fin n => -Delta j k) τ := by
      have hneg : frobNorm (fun j k : Fin n => -Delta j k) ≤ τ := by
        simpa [frobNorm_neg] using hpert
      exact opNorm2Le_of_frobNorm_le (fun j k : Fin n => -Delta j k) hneg
    have habs :=
      abs_vecInnerProduct_matMulVec_le_of_opNorm2Le
        (fun j k : Fin n => -Delta j k) hDeltaNegOp x
    have hquad :
        |finiteQuadraticForm (fun j k : Fin n => -Delta j k) x| ≤
          τ * finiteVecNorm2Sq x := by
      simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
        finiteVecNorm2Sq, vecNorm2Sq] using habs
    exact (le_abs_self
      (finiteQuadraticForm (fun j k : Fin n => -Delta j k) x)).trans hquad
  have hUpper := finiteLoewnerLe_add hExactUpper hDeltaUpper
  have hLower' := finiteLoewnerLe_add hExactLower hDeltaLower
  have hLower :
      finiteLoewnerLe
        (fun j k : Fin n => -(Exact j k + Delta j k))
        (fun j k : Fin n => Eps j k + τ * finiteIdMatrix j k) := by
    convert hLower' using 1
    ext j k
    ring
  exact ⟨hUpper, hLower⟩

/-- Sampling after a right factor is congruent to sampling the basis first. -/
theorem uniformRowSampleGram_preconditionColumns_eq_rightGramCongruence
    {m r n s : ℕ} (V : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) (samples : RowTrace m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    uniformRowSampleGram (preconditionColumns V C) samples =
      rightGramCongruence (uniformRowSampleGram V samples) C := by
  classical
  have hsketch :
      uniformRowSampleSketch s (preconditionColumns V C) samples =
        preconditionColumns (uniformRowSampleSketch s V samples) C := by
    ext t j
    unfold uniformRowSampleSketch uniformRowSampleIncrement preconditionColumns
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hleft :
      rowSketchGram (uniformRowSampleSketch s (preconditionColumns V C) samples) =
        uniformRowSampleGram (preconditionColumns V C) samples := by
    simpa using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        (preconditionColumns V C) samples hm hs
  have hright :
      rowSketchGram (uniformRowSampleSketch s V samples) =
        uniformRowSampleGram V samples := by
    simpa using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        V samples hm hs
  have hgram :
      rowSketchGram
          (preconditionColumns (uniformRowSampleSketch s V samples) C) =
        rightGramCongruence
          (rowSketchGram (uniformRowSampleSketch s V samples)) C := by
    ext j k
    unfold rowSketchGram preconditionColumns rightGramCongruence
    conv_lhs => arg 2; ext i; rw [Finset.sum_mul]
    conv_lhs => arg 2; ext i; arg 2; ext a; rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    uniformRowSampleGram (preconditionColumns V C) samples
        = rowSketchGram
            (uniformRowSampleSketch s (preconditionColumns V C) samples) := by
            exact hleft.symm
    _ = rowSketchGram
            (preconditionColumns (uniformRowSampleSketch s V samples) C) := by
            rw [hsketch]
    _ = rightGramCongruence
            (rowSketchGram (uniformRowSampleSketch s V samples)) C := hgram
    _ = rightGramCongruence (uniformRowSampleGram V samples) C := by
            rw [hright]

/-- Ordinary Grams after a right factor are right-factor congruences. -/
theorem rowGram_preconditionColumns_eq_rightGramCongruence
    {m r n : ℕ} (V : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) :
    rowGram (preconditionColumns V C) =
      rightGramCongruence (rowGram V) C := by
  classical
  ext j k
  unfold rowGram preconditionColumns rightGramCongruence
  conv_lhs => arg 2; ext i; rw [Finset.sum_mul]
  conv_lhs => arg 2; ext i; arg 2; ext a; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact sampled-Gram error for a factored input `A = U C` is the right-factor
congruence of the orthonormal-basis sampled-Gram error. -/
theorem uniformRowSampleGram_factoredInput_error_eq_rightGramCongruence_error
    {m r n s : ℕ} (P : Fin m → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (samples : RowTrace m s) (hU : HasOrthonormalColumns U)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    (fun j k : Fin n =>
        uniformRowSampleGram
            (preconditionRows P (preconditionColumns U C)) samples j k -
          rowGram (preconditionColumns U C) j k) =
      rightGramCongruence
        (fun a b : Fin r =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C := by
  classical
  let V : Fin m → Fin r → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  have hY :
      preconditionRows P A = preconditionColumns V C := by
    simpa [A, V] using preconditionRows_preconditionColumns_assoc P U C
  have hsample :
      uniformRowSampleGram (preconditionRows P A) samples =
        rightGramCongruence (uniformRowSampleGram V samples) C := by
    rw [hY]
    exact
      uniformRowSampleGram_preconditionColumns_eq_rightGramCongruence
        V C samples hm hs
  have hAgram : rowGram A = rowGram C := by
    change rowGram (preconditionColumns U C) = rowGram C
    rw [rowGram_preconditionColumns_eq_rightGramCongruence]
    have hgram : rowGram U = idMatrix r :=
      rowGram_eq_id_of_orthonormal_columns U hU
    ext j k
    have hcong :
        rightGramCongruence
            (fun a b : Fin r => (1 : ℝ) * finiteIdMatrix a b) C j k =
          (fun j k : Fin n => (1 : ℝ) * rowGram C j k) j k := by
      simpa using
        congrFun (congrFun
          (rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1) j) k
    simpa [hgram, idMatrix] using hcong
  ext j k
  calc
    uniformRowSampleGram (preconditionRows P (preconditionColumns U C)) samples j k -
        rowGram (preconditionColumns U C) j k
        =
      rightGramCongruence (uniformRowSampleGram V samples) C j k -
        rightGramCongruence (finiteIdMatrix : Fin r → Fin r → ℝ) C j k := by
        simp [A, V, hsample, hAgram,
          rightGramCongruence_finiteIdMatrix_eq_rowGram]
    _ =
      rightGramCongruence
        (fun a b : Fin r =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C j k := by
        have hsub :=
          congrFun (congrFun
            (rightGramCongruence_sub
              (uniformRowSampleGram V samples)
              (finiteIdMatrix : Fin r → Fin r → ℝ) C) j) k
        simpa [V] using hsub.symm

/-- The right-factor congruence of `ε I` is `ε AᵀA` for a factored input
`A = U C` with exact orthonormal analysis basis. -/
theorem rightGramCongruence_smul_finiteIdMatrix_eq_smul_factoredInputGram
    {m r n : ℕ} (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (ε : ℝ) :
    rightGramCongruence (fun a b : Fin r => ε * finiteIdMatrix a b) C =
      fun j k : Fin n => ε * rowGram (preconditionColumns U C) j k := by
  have hAgram : rowGram (preconditionColumns U C) = rowGram C := by
    rw [rowGram_preconditionColumns_eq_rightGramCongruence]
    have hgram : rowGram U = idMatrix r :=
      rowGram_eq_id_of_orthonormal_columns U hU
    ext j k
    have hcong :
        rightGramCongruence
            (fun a b : Fin r => (1 : ℝ) * finiteIdMatrix a b) C j k =
          (fun j k : Fin n => (1 : ℝ) * rowGram C j k) j k := by
      simpa using
        congrFun (congrFun
          (rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1) j) k
    simpa [hgram, idMatrix] using hcong
  rw [rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram]
  rw [hAgram]

/-- Exact two-sided sampled-Gram event for an Algorithm 3 input matrix factored
as `A = U C`, where `U` is the exact orthonormal analysis basis. -/
def signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
    {m r n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) (ε : ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let P : Fin m → Fin m → ℝ :=
      matMul m H (diagMatrix (rademacherSignVector x.1))
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Y : Fin m → Fin n → ℝ := preconditionRows P A
    finiteLoewnerLe
      (fun j k : Fin n => uniformRowSampleGram Y x.2 j k - rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n => -(uniformRowSampleGram Y x.2 j k - rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k)}

/-- The orthonormal-basis SRHT sample-Gram event implies the corresponding
factored-input event for `A = U C`. -/
theorem signedHadamardUniformRowSampleGramTwoSidedEvent_subset_factoredInput
    {m r n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) (ε : ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    signedHadamardUniformRowSampleGramTwoSidedEvent
        (m := m) (n := r) (s := s) H U ε ⊆
      signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
        (m := m) (r := r) (n := n) (s := s) H U C ε := by
  classical
  intro x hx
  let P : Fin m → Fin m → ℝ :=
    matMul m H (diagMatrix (rademacherSignVector x.1))
  let V : Fin m → Fin r → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  let Y : Fin m → Fin n → ℝ := preconditionRows P A
  let ExactU : Fin r → Fin r → ℝ :=
    fun a b => uniformRowSampleGram V x.2 a b - finiteIdMatrix a b
  let ExactA : Fin n → Fin n → ℝ :=
    fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
  let EpsU : Fin r → Fin r → ℝ :=
    fun a b => ε * finiteIdMatrix a b
  let EpsA : Fin n → Fin n → ℝ :=
    fun j k => ε * rowGram A j k
  have hxU :
      finiteLoewnerLe ExactU EpsU ∧
      finiteLoewnerLe (fun a b : Fin r => -ExactU a b) EpsU := by
    simpa [signedHadamardUniformRowSampleGramTwoSidedEvent, P, V, ExactU, EpsU]
      using hx
  have hErr :
      ExactA = rightGramCongruence ExactU C := by
    simpa [P, V, A, Y, ExactU, ExactA] using
      uniformRowSampleGram_factoredInput_error_eq_rightGramCongruence_error
        P U C x.2 hU hm hs
  have hEps :
      rightGramCongruence EpsU C = EpsA := by
    simpa [A, EpsU, EpsA] using
      rightGramCongruence_smul_finiteIdMatrix_eq_smul_factoredInputGram
        U C hU ε
  have hUpperBase :
      finiteLoewnerLe (rightGramCongruence ExactU C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.1
  have hLowerBase :
      finiteLoewnerLe
        (rightGramCongruence (fun a b : Fin r => -ExactU a b) C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.2
  have hUpper : finiteLoewnerLe ExactA EpsA := by
    rw [hErr, ← hEps]
    exact hUpperBase
  have hNegErr :
      (fun j k : Fin n => -ExactA j k) =
        rightGramCongruence (fun a b : Fin r => -ExactU a b) C := by
    rw [hErr]
    rw [rightGramCongruence_neg]
  have hLower : finiteLoewnerLe (fun j k : Fin n => -ExactA j k) EpsA := by
    rw [hNegErr, ← hEps]
    exact hLowerBase
  simpa [signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent,
    P, A, Y, ExactA, EpsA] using And.intro hUpper hLower













































/-- Fully floating-point computed-input event for Algorithm 3 on a factored
input `A = U C`, using a computed uniform row-scale denominator. -/
def signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {m r n s : ℕ}
    (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace m s → ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k)}












































































































/-- If `U` has orthonormal columns, the Gram of `U C` is the Gram of `C`. -/
theorem rowGram_preconditionColumns_eq_rowGram_of_orthonormal
    {m r n : ℕ} (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) (hU : HasOrthonormalColumns U) :
    rowGram (preconditionColumns U C) = rowGram C := by
  rw [rowGram_preconditionColumns_eq_rightGramCongruence]
  have hgram : rowGram U = idMatrix r :=
    rowGram_eq_id_of_orthonormal_columns U hU
  ext j k
  have hcong :
      rightGramCongruence (fun a b : Fin r => (1 : ℝ) * finiteIdMatrix a b) C
        j k =
      (fun j k : Fin n => (1 : ℝ) * rowGram C j k) j k := by
    simpa using
      congrFun (congrFun
        (rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1) j) k
  simpa [hgram, idMatrix] using hcong

/-- Implemented signed-Hadamard preconditioned basis formed by a computed or
stored left preconditioner certificate and one rounded matrix product. -/
noncomputable def signedHadamardComputedLeftPreconditionedBasis
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (ω : RademacherTrace m) : Fin m → Fin n → ℝ :=
  fl_preconditionRowsWithComputedLeft fp (Pihat ω) U

/-- Entrywise basis-error budget for
`signedHadamardComputedLeftPreconditionedBasis`.  It charges both the
generated/stored preconditioner-entry errors in `Pihat` and the rounded matrix
product used to form `Vhat = fl(Pihat * U)`. -/
noncomputable def signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
        (matMul m H (diagMatrix (rademacherSignVector ω))))
    (ω : RademacherTrace m) (i : Fin m) (j : Fin n) : ℝ :=
  flPreconditionRowsWithComputedLeftEntryErrorBudget fp (Pihat ω) U i j

/-- Implemented signed-Hadamard preconditioned basis formed from both a
computed/stored left preconditioner and a computed/stored input basis.  This
is the Algorithm 3 surface for singular vectors or bases that are computed
before preprocessing. -/
noncomputable def signedHadamardComputedLeftInputPreconditionedBasis
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (ω : RademacherTrace m) : Fin m → Fin n → ℝ :=
  fl_preconditionRowsWithComputedLeftAndInput fp (Pihat ω) Uhat

/-- Entrywise basis-error budget for
`signedHadamardComputedLeftInputPreconditionedBasis`.  It charges
generated/stored preconditioner-entry errors, computed input-basis errors, and
the rounded matrix product used to form `Vhat = fl(Pihat * Uhat)`. -/
noncomputable def signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
        (matMul m H (diagMatrix (rademacherSignVector ω))))
    (ω : RademacherTrace m) (i : Fin m) (j : Fin n) : ℝ :=
  flPreconditionRowsWithComputedLeftInputEntryErrorBudget
    fp (Pihat ω) Uhat i j

/-- Exact/stored signed-Hadamard preconditioner certificate.  This instantiates
the computed-preconditioner surface when the realized `H D_omega` matrix is
available exactly; the subsequent `Vhat = fl((H D_omega) U)` product is still
charged by floating-point matrix multiplication. -/
noncomputable def signedHadamardExactStoredPreconditioner
    (fp : FPModel) {m : ℕ} (H : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) :
    ComputedPreconditioner fp
      (matMul m H (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.exact fp
    (matMul m H (diagMatrix (rademacherSignVector ω)))

/-- Exact supplied signed-Hadamard factors with rounded preconditioner
formation.  The Hadamard/FHT table `H` and realized Rademacher sign vector are
treated as exact mathematical inputs, while the realized preconditioner
`H * diag(sign)` is produced by a rounded matrix product. -/
noncomputable def signedHadamardExactFactorPreconditioner
    (fp : FPModel) {m : ℕ} (H : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (matMul m H (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardExactFactors
    fp H (rademacherSignVector ω) hγm

/-- Signed-Hadamard preconditioner from a supplied sign-pattern table with
rounded `sqrt (1 / m)` scaling.  The Rademacher sign law is exact, while the
scaled table and the realized `H D_omega` product are represented by computed
certificates. -/
noncomputable def signedHadamardScaledPatternPreconditioner
    (fp : FPModel) {m : ℕ} (S : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (matMul m (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardScaledPattern
    fp S (rademacherSignVector ω) hγm

/-- Signed-Hadamard preconditioner from a supplied sign-pattern table with
rounded `sqrt (1 / m)` scaling and rounded storage of the realized
Rademacher signs.  The Rademacher law itself is exact; this certificate only
charges the non-probability sign-storage/copy arithmetic before the diagonal is
formed and multiplied into the scaled table. -/
noncomputable def signedHadamardScaledPatternStoredSignPreconditioner
    (fp : FPModel) {m : ℕ} (S : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (matMul m (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardScaledPatternStoredSign
    fp S (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- Signed-Hadamard preconditioner from a supplied sign-pattern table with
rounded `sqrt (1 / m)` scaling and rounded add-zero storage of the realized
Rademacher signs.  The Rademacher law itself is exact; this certificate only
charges the non-probability sign-storage/copy arithmetic `fl_add sign_i 0`
before the diagonal is formed and multiplied into the scaled table. -/
noncomputable def signedHadamardScaledPatternStoredSignAddZeroRightPreconditioner
    (fp : FPModel) {m : ℕ} (S : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (matMul m (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardScaledPatternStoredSignAddZeroRight
    fp S (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- Signed-Hadamard preconditioner from a supplied sign-pattern table with
rounded `sqrt (1 / m)` scaling and rounded subtract-zero storage of the
realized Rademacher signs.  The Rademacher law itself is exact; this
certificate only charges the non-probability sign-storage/copy arithmetic
`fl_sub sign_i 0` before the diagonal is formed and multiplied into the scaled
table. -/
noncomputable def signedHadamardScaledPatternStoredSignSubZeroRightPreconditioner
    (fp : FPModel) {m : ℕ} (S : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (matMul m (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardScaledPatternStoredSignSubZeroRight
    fp S (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- Signed-Hadamard preconditioner from the concrete generated
Sylvester/Walsh sign-pattern table with rounded `sqrt (1 / 2^p)` scaling.
The bit-parity table is generated exactly; the FP budget starts with scale
formation and the rounded `H D_omega` product. -/
noncomputable def signedHadamardSylvesterPatternPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p))
    (hγm : gammaValid fp (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterPattern
    fp p (rademacherSignVector ω) hγm

/-- Signed-Hadamard preconditioner computed by applying the rounded generated
Sylvester/Walsh FHT schedule to the diagonal Rademacher sign matrix.

This is the fast-schedule implementation path for `H D_ω`: the Rademacher law
is exact, while the generated FHT butterfly arithmetic and rounded
`sqrt(1/2^p)` scale are charged by the `ComputedPreconditioner` certificate. -/
noncomputable def signedHadamardSylvesterFhtSchedulePreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtSchedule
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with explicit rounded
`fl_add y_i 0` storage/copy after every FHT pair update.  The Rademacher law
itself remains exact; this charges only non-probability FHT writeback
arithmetic in addition to butterfly arithmetic and rounded normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredAddZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredAddZeroRight
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with explicit rounded
`fl_mul y_i 1` storage/copy after every FHT pair update.  The Rademacher law
itself remains exact; this charges only non-probability FHT writeback
arithmetic in addition to butterfly arithmetic and rounded normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredMulOnePreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredMulOne
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with explicit rounded
`fl_sub y_i 0` storage/copy after every FHT pair update.  The Rademacher law
itself remains exact; this charges only non-probability FHT writeback
arithmetic in addition to butterfly arithmetic and rounded normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSubZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredSubZeroRight
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_add y_i 0`
storage/copy only on the two outputs modified by each FHT pair update.  The
Rademacher law itself remains exact; this charges only non-probability FHT
writeback arithmetic in addition to butterfly arithmetic and rounded
normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRight
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul y_i 1`
storage/copy only on the two outputs modified by each FHT pair update.  The
Rademacher law itself remains exact; this charges only non-probability FHT
writeback arithmetic in addition to butterfly arithmetic and rounded
normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleModifiedStoredMulOnePreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredMulOne
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_sub y_i 0`
storage/copy only on the two outputs modified by each FHT pair update.  The
Rademacher law itself remains exact; this charges only non-probability FHT
writeback arithmetic in addition to butterfly arithmetic and rounded
normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRight
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs before the FHT stages are applied to
the diagonal input.  The Rademacher law itself remains exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtSchedule
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and explicit rounded `fl_add y_i 0`
storage/copy after every FHT pair update.  Probability laws remain exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredAddZeroRight
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and explicit rounded `fl_mul y_i 1`
storage/copy after every FHT pair update.  Probability laws remain exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignStoredMulOnePreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredMulOne
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and explicit rounded `fl_sub y_i 0`
storage/copy after every FHT pair update.  Probability laws remain exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignStoredSubZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredSubZeroRight
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and rounded `fl_add y_i 0`
storage/copy only on modified FHT pair outputs.  Probability laws remain
exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRight
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and rounded `fl_mul y_i 1`
storage/copy only on modified FHT pair outputs.  Probability laws remain
exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredMulOnePreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredMulOne
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and rounded `fl_sub y_i 0`
storage/copy only on modified FHT pair outputs.  Probability laws remain
exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRight
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Generated Sylvester/Walsh sign-pattern preconditioner with rounded
`fl_mul sign_i 1` storage of the realized Rademacher signs. -/
noncomputable def signedHadamardSylvesterPatternStoredSignPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p))
    (hγm : gammaValid fp (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSign
    fp p (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- Generated Sylvester/Walsh sign-pattern preconditioner with rounded
`fl_add sign_i 0` storage of the realized Rademacher signs. -/
noncomputable def signedHadamardSylvesterPatternStoredSignAddZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p))
    (hγm : gammaValid fp (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSignAddZeroRight
    fp p (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- Generated Sylvester/Walsh sign-pattern preconditioner with rounded
`fl_sub sign_i 0` storage of the realized Rademacher signs. -/
noncomputable def signedHadamardSylvesterPatternStoredSignSubZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p))
    (hγm : gammaValid fp (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSignSubZeroRight
    fp p (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- With an exact/stored signed-Hadamard preconditioner certificate, the
computed-left basis-entry budget contains no transform-storage term. -/
@[simp] theorem signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget_exactStored
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (ω : RademacherTrace m) (i : Fin m) (j : Fin n) :
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget fp H U
        (signedHadamardExactStoredPreconditioner fp H) ω i j =
      gamma fp m *
        ∑ k : Fin m,
          |(matMul m H (diagMatrix (rademacherSignVector ω))) i k| *
            |U k j| := by
  simp [signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget,
    signedHadamardExactStoredPreconditioner]

/-- With an exact input basis certificate, the computed-left/input budget
reduces to the existing computed-left basis-entry budget. -/
@[simp] theorem signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget_exactInput
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (ω : RademacherTrace m) (i : Fin m) (j : Fin n) :
    signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
        fp H (ComputedMatrix.exact fp U) Pihat ω i j =
      signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
        fp H U Pihat ω i j := by
  simp [signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget,
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget]

/-- Sample-dependent perturbation budget for the concrete computed-left
preconditioned Algorithm 3 path.  The first term charges rounded row scaling
and sampled-Gram dot products after `Vhat` has been formed.  The second term
charges the difference between the exact sampled Gram of `Vhat` and that of the
ideal signed-Hadamard basis `H D_ω U`. -/
noncomputable def signedHadamardComputedLeftUniformRowPerturbBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (x : RademacherTrace m × RowTrace m s) : ℝ :=
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
      fp H U Pihat x.1
  uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for the concrete computed-left
preconditioned Algorithm 3 path when the uniform row-scale denominator is
computed.  It charges the computed denominator, rounded row divisions, rounded
Gram dot products, and the basis drift from `Vhat` back to the exact
`H D_ω U`. -/
noncomputable def signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (dhat : ComputedUniformRowScaleDen fp m s)
    (x : RademacherTrace m × RowTrace m s) : ℝ :=
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
      fp H U Pihat x.1
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2





































































































































































































/-- Floating-point two-sided sample-Gram event for an implemented finite
signed-mixing preprocessed basis.  Here the sign law and the uniform row trace
are exact probability laws; the matrix entries in `Vhat`, row scaling, and Gram
dot products are the computed non-probability quantities. -/
def signedMixingComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
    (fp : FPModel) {r m n s : ℕ}
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace r s → ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Floating-point two-sided sample-Gram event for an implemented finite
signed-mixing preprocessed basis when the uniform row-scale denominator
`sqrt(s/r)` is also computed. -/
def signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {r m n s : ℕ}
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace r s → ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Perturbation event connecting an implemented finite signed-mixing
preprocessed basis `Vhat` to the exact analysis basis
`(G diag(ω)) U`. -/
def signedMixingComputedPreconditionedFlUniformRowPerturbEvent
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (τ : RademacherTrace m × RowTrace r s → ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (signedMixingRows G (rademacherSignVector x.1)) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

/-- Perturbation event for finite signed mixing with a computed uniform
row-scale denominator. -/
def signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (τ : RademacherTrace m × RowTrace r s → ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (signedMixingRows G (rademacherSignVector x.1)) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

/-- Implemented finite signed-mixing preconditioned basis formed by a computed
or stored left preconditioner certificate and one rounded matrix product. -/
noncomputable def signedMixingComputedLeftPreconditionedBasis
    (fp : FPModel) {r m n : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (ω : RademacherTrace m) : Fin r → Fin n → ℝ :=
  fl_preconditionRowsWithComputedLeft fp (Pihat ω) U

/-- Entrywise basis-error budget for
`signedMixingComputedLeftPreconditionedBasis`.  It charges both the computed
preconditioner-entry errors in `Pihat` and the rounded matrix product used to
form `Vhat = fl(Pihat * U)`. -/
noncomputable def signedMixingComputedLeftPreconditionedBasisEntryErrorBudget
    (fp : FPModel) {r m n : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (ω : RademacherTrace m) (i : Fin r) (j : Fin n) : ℝ :=
  flPreconditionRowsWithComputedLeftEntryErrorBudget fp (Pihat ω) U i j

/-- Exact/stored signed-mixing preconditioner certificate.  The subsequent
`Vhat = fl(Pihat * U)` product is still charged. -/
noncomputable def signedMixingExactStoredPreconditioner
    (fp : FPModel) {r m : ℕ} (G : Fin r → Fin m → ℝ)
    (ω : RademacherTrace m) :
    ComputedPreconditioner fp
      (signedMixingRows G (rademacherSignVector ω)) :=
  ComputedPreconditioner.exact fp
    (signedMixingRows G (rademacherSignVector ω))

/-- Exact supplied finite signed-mixing factors with rounded preconditioner
formation.  The deterministic table `G` and exact Rademacher sign vector are
mathematical inputs; forming `G * diag(sign)` is a rounded matrix product. -/
noncomputable def signedMixingExactFactorPreconditioner
    (fp : FPModel) {r m : ℕ} (G : Fin r → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (signedMixingRows G (rademacherSignVector ω)) :=
  ComputedPreconditioner.flSignedMixingExactFactors
    fp G (rademacherSignVector ω) hγm

/-- With an exact/stored signed-mixing preconditioner certificate, the
computed-left basis-entry budget contains no preconditioner-storage term. -/
@[simp] theorem signedMixingComputedLeftPreconditionedBasisEntryErrorBudget_exactStored
    (fp : FPModel) {r m n : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (ω : RademacherTrace m) (i : Fin r) (j : Fin n) :
    signedMixingComputedLeftPreconditionedBasisEntryErrorBudget fp G U
        (signedMixingExactStoredPreconditioner fp G) ω i j =
      gamma fp m *
        ∑ k : Fin m,
          |signedMixingRows G (rademacherSignVector ω) i k| *
            |U k j| := by
  simp [signedMixingComputedLeftPreconditionedBasisEntryErrorBudget,
    signedMixingExactStoredPreconditioner]

/-- Sample-dependent perturbation budget for the concrete computed-left finite
signed-mixing path.  It charges rounded row scaling and Gram dot products after
`Vhat` has been formed, plus the sampled-Gram drift from `Vhat` back to the
exact basis `(G diag(ω)) U`. -/
noncomputable def signedMixingComputedLeftUniformRowPerturbBudget
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (x : RademacherTrace m × RowTrace r s) : ℝ :=
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (signedMixingRows G (rademacherSignVector x.1)) U
  let Vhat : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1
  let E : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasisEntryErrorBudget
      fp G U Pihat x.1
  uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for the concrete computed-left finite
signed-mixing path when the uniform row-scale denominator `sqrt(s/r)` is
computed. -/
noncomputable def signedMixingComputedLeftUniformRowComputedDenPerturbBudget
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (x : RademacherTrace m × RowTrace r s) : ℝ :=
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (signedMixingRows G (rademacherSignVector x.1)) U
  let Vhat : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1
  let E : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasisEntryErrorBudget
      fp G U Pihat x.1
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2















































































































































































































































































































































































































/- ============================================================
-- CountSketch computed preprocessing plus uniform-row FP transfer
-- ============================================================ -/

/-- Floating-point two-sided sample-Gram event for an implemented CountSketch
preprocessed basis.  The exact hash/sign and uniform row laws are probability
objects; `Vhat`, row scaling, and Gram dot products are computed
non-probability quantities charged by `τ`. -/
def countSketchComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
    (fp : FPModel) {r m n s : ℕ}
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (ε : ℝ)
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Floating-point two-sided sample-Gram event for an implemented CountSketch
preprocessed basis when the uniform row-scale denominator `sqrt(s/r)` is also
computed. -/
def countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {r m n s : ℕ}
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ε : ℝ)
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Perturbation event connecting an implemented CountSketch-preconditioned
basis `Vhat` to the exact analysis basis `S_{h,\omega} U`. -/
def countSketchComputedPreconditionedFlUniformRowPerturbEvent
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

/-- Perturbation event for CountSketch preprocessing with a computed uniform
row-scale denominator. -/
def countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

/-- Implemented sparse CountSketch-preconditioned basis: exact hash/sign
selection, rounded signed products, and rounded bucket accumulation. -/
noncomputable def countSketchSparseComputedPreconditionedBasis
    (fp : FPModel) {r m n : ℕ} (U : Fin m → Fin n → ℝ)
    (x : CountSketchHash r m × RademacherTrace m) : Fin r → Fin n → ℝ :=
  fl_countSketchSparseApply fp x.1 (rademacherSignVector x.2) U

/-- Implemented sparse CountSketch-preconditioned basis when the realized
Rademacher signs are first stored or copied in floating point before the
sparse bucket accumulation.  The hash/sign probability law is exact; only the
stored sign table and subsequent arithmetic are computed quantities. -/
noncomputable def countSketchSparseComputedPreconditionedBasisWithStoredSign
    (fp : FPModel) {r m n : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (x : CountSketchHash r m × RademacherTrace m) : Fin r → Fin n → ℝ :=
  fl_countSketchSparseApplyWithStoredSign
    fp x.1 (rademacherSignVector x.2) (storedSignOf x.2) U

/-- Implemented sparse CountSketch-preconditioned basis when realized
Rademacher signs are stored or copied in floating point and each realized
hash bucket is traversed in an exact fixed order.  The order is a discrete
memory-layout choice, not a floating-point computation. -/
noncomputable def countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
    (fp : FPModel) {r m n : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (x : CountSketchHash r m × RademacherTrace m) : Fin r → Fin n → ℝ :=
  fl_countSketchSparseApplyWithStoredSignPermuted
    fp x.1 (rademacherSignVector x.2) (storedSignOf x.2) U (orderOf x.1)

/-- Implemented sparse CountSketch-preconditioned basis when realized
Rademacher signs are stored or copied in floating point and each realized
hash bucket is accumulated by an exact supplied binary summation tree.  The
tree shape is a discrete implementation choice, not a floating-point real
quantity. -/
noncomputable def countSketchSparseComputedPreconditionedBasisWithStoredSignTree
    (fp : FPModel) {r m n : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (x : CountSketchHash r m × RademacherTrace m) : Fin r → Fin n → ℝ :=
  fl_countSketchSparseApplyWithStoredSignTree
    fp x.1 (rademacherSignVector x.2) (storedSignOf x.2) U (treeOf x.1)

/-- Sample-dependent perturbation budget for sparse computed CountSketch
preprocessing followed by exact-denominator rounded uniform row sampling. -/
noncomputable def countSketchSparseUniformRowPerturbBudget
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s) : ℝ :=
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasis fp U x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyFpAbsBudget
      fp x.1.1 (rademacherSignVector x.1.2) U
  uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for sparse computed CountSketch
preprocessing followed by computed-denominator rounded uniform row sampling. -/
noncomputable def countSketchSparseUniformRowComputedDenPerturbBudget
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s) : ℝ :=
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasis fp U x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyFpAbsBudget
      fp x.1.1 (rademacherSignVector x.1.2) U
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for stored-sign sparse computed
CountSketch preprocessing followed by computed-denominator rounded uniform row
sampling.  This budget explicitly includes sign storage/copying, rounded signed
products, bucket accumulation, the computed denominator, sampled-row divisions,
and sampled-Gram dot products. -/
noncomputable def countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s) : ℝ :=
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows x.1.1 sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSign
      fp U storedSignOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignFpAbsBudget
      fp x.1.1 sign signhat U
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for stored-sign sparse computed
CountSketch preprocessing with exact per-bucket traversal orders, followed by
computed-denominator rounded uniform row sampling.  This budget charges sign
storage/copying, rounded signed products, bucket accumulation in the selected
order, the computed denominator, sampled-row divisions, and sampled-Gram dot
products. -/
noncomputable def countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s) : ℝ :=
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows x.1.1 sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
      fp U storedSignOf orderOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignPermutedFpAbsBudget
      fp x.1.1 sign signhat U (orderOf x.1.1)
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for stored-sign sparse computed
CountSketch preprocessing with tree-reduced bucket accumulations, followed by
computed-denominator rounded uniform row sampling.  This budget charges sign
storage/copying, rounded signed products, tree-depth bucket accumulation, the
computed denominator, sampled-row divisions, and sampled-Gram dot products. -/
noncomputable def countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s) : ℝ :=
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows x.1.1 sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSignTree
      fp U storedSignOf treeOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignTreeFpAbsBudget
      fp x.1.1 sign signhat U (treeOf x.1.1)
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2











































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Exact sampled-Gram error for a rectangularly preconditioned factored input
`A = U C`, specialized for the CountSketch section before the later generic
factored-input block. -/
theorem uniformRowSampleGram_countSketchRectFactoredInput_error_eq_rightGramCongruence_error
    {r m q n s : ℕ} (P : Fin r → Fin m → ℝ)
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (samples : RowTrace r s) (hU : HasOrthonormalColumns U)
    (hr : 0 < r) (hs : 0 < (s : ℝ)) :
    (fun j k : Fin n =>
        uniformRowSampleGram
            (preconditionRows P (preconditionColumns U C)) samples j k -
          rowGram (preconditionColumns U C) j k) =
      rightGramCongruence
        (fun a b : Fin q =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C := by
  classical
  let V : Fin r → Fin q → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  have hY :
      preconditionRows P A = preconditionColumns V C := by
    simpa [A, V] using preconditionRows_preconditionColumns_assoc_rect P U C
  have hsample :
      uniformRowSampleGram (preconditionRows P A) samples =
        rightGramCongruence (uniformRowSampleGram V samples) C := by
    rw [hY]
    exact
      uniformRowSampleGram_preconditionColumns_eq_rightGramCongruence
        V C samples hr hs
  have hAgram : rowGram A = rowGram C := by
    change rowGram (preconditionColumns U C) = rowGram C
    rw [rowGram_preconditionColumns_eq_rightGramCongruence]
    have hgram : rowGram U = idMatrix q :=
      rowGram_eq_id_of_orthonormal_columns U hU
    ext j k
    have hcong :
        rightGramCongruence
            (fun a b : Fin q => (1 : ℝ) * finiteIdMatrix a b) C j k =
          (fun j k : Fin n => (1 : ℝ) * rowGram C j k) j k := by
      simpa using
        congrFun (congrFun
          (rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1) j) k
    simpa [hgram, idMatrix] using hcong
  ext j k
  calc
    uniformRowSampleGram (preconditionRows P (preconditionColumns U C)) samples j k -
        rowGram (preconditionColumns U C) j k
        =
      rightGramCongruence (uniformRowSampleGram V samples) C j k -
        rightGramCongruence (finiteIdMatrix : Fin q → Fin q → ℝ) C j k := by
        simp [A, V, hsample, hAgram,
          rightGramCongruence_finiteIdMatrix_eq_rowGram]
    _ =
      rightGramCongruence
        (fun a b : Fin q =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C j k := by
        have hsub :=
          congrFun (congrFun
            (rightGramCongruence_sub
              (uniformRowSampleGram V samples)
              (finiteIdMatrix : Fin q → Fin q → ℝ) C) j) k
        simpa [V] using hsub.symm

/-- Exact two-sided sampled-Gram event for CountSketch followed by uniform row
sampling on an actual input matrix factored as `A = U C`, where `U` is the
exact orthonormal analysis basis and `C` is an exact right factor used only in
the analysis. -/
def countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
    {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ) (ε : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let P : Fin r → Fin m → ℝ :=
      countSketchRows x.1.1 (rademacherSignVector x.1.2)
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Y : Fin r → Fin n → ℝ := preconditionRows P A
    finiteLoewnerLe
      (fun j k : Fin n => uniformRowSampleGram Y x.2 j k - rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n => -(uniformRowSampleGram Y x.2 j k - rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k)}

/-- The exact orthonormal-basis CountSketch sample-Gram event implies the
corresponding actual-input event for `A = U C`. -/
theorem countSketchUniformRowSampleGramTwoSidedEvent_subset_factoredInput
    {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ) (ε : ℝ)
    (hU : HasOrthonormalColumns U) (hr : 0 < r) (hs : 0 < (s : ℝ)) :
    countSketchUniformRowSampleGramTwoSidedEvent
        (r := r) (m := m) (n := q) (s := s) U ε ⊆
      countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
        (r := r) (m := m) (q := q) (n := n) (s := s) U C ε := by
  classical
  intro x hx
  let P : Fin r → Fin m → ℝ :=
    countSketchRows x.1.1 (rademacherSignVector x.1.2)
  let V : Fin r → Fin q → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  let Y : Fin r → Fin n → ℝ := preconditionRows P A
  let ExactU : Fin q → Fin q → ℝ :=
    fun a b => uniformRowSampleGram V x.2 a b - finiteIdMatrix a b
  let ExactA : Fin n → Fin n → ℝ :=
    fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
  let EpsU : Fin q → Fin q → ℝ :=
    fun a b => ε * finiteIdMatrix a b
  let EpsA : Fin n → Fin n → ℝ :=
    fun j k => ε * rowGram A j k
  have hxU :
      finiteLoewnerLe ExactU EpsU ∧
      finiteLoewnerLe (fun a b : Fin q => -ExactU a b) EpsU := by
    simpa [countSketchUniformRowSampleGramTwoSidedEvent, P, V, ExactU, EpsU]
      using hx
  have hErr :
      ExactA = rightGramCongruence ExactU C := by
    simpa [P, V, A, Y, ExactU, ExactA] using
      uniformRowSampleGram_countSketchRectFactoredInput_error_eq_rightGramCongruence_error
        P U C x.2 hU hr hs
  have hEps :
      rightGramCongruence EpsU C = EpsA := by
    simpa [A, EpsU, EpsA] using
      rightGramCongruence_smul_finiteIdMatrix_eq_smul_factoredInputGram
        U C hU ε
  have hUpperBase :
      finiteLoewnerLe (rightGramCongruence ExactU C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.1
  have hLowerBase :
      finiteLoewnerLe
        (rightGramCongruence (fun a b : Fin q => -ExactU a b) C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.2
  have hUpper : finiteLoewnerLe ExactA EpsA := by
    rw [hErr, ← hEps]
    exact hUpperBase
  have hNegErr :
      (fun j k : Fin n => -ExactA j k) =
        rightGramCongruence (fun a b : Fin q => -ExactU a b) C := by
    rw [hErr]
    rw [rightGramCongruence_neg]
  have hLower : finiteLoewnerLe (fun j k : Fin n => -ExactA j k) EpsA := by
    rw [hNegErr, ← hEps]
    exact hLowerBase
  simpa [countSketchUniformRowFactoredInputSampleGramTwoSidedEvent,
    P, A, Y, ExactA, EpsA] using And.intro hUpper hLower






































/-- Fully floating-point computed event for CountSketch on an actual input
matrix `A = U C`, using a computed uniform row-scale denominator.  The computed
matrix is `Vhat`, normally the sparse rounded CountSketch apply to `A`. -/
def countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ε : ℝ)
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k)}
































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Exact Frobenius event for non-injective CountSketch followed by iid
uniform-row sampling.  The first conjunct controls the exact CountSketch Gram
error around `AᵀA`; the second controls exact row sampling around the exact
preconditioned Gram `(S A)ᵀ(S A)`. -/
def countSketchUniformRowSampleGramRowGramFrobEvent {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ) (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let V : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    frobNorm (fun j k : Fin n => rowGram V j k - rowGram A j k) ≤ ηCS ∧
      frobNorm
        (fun j k : Fin n => uniformRowSampleGram V x.2 j k - rowGram V j k) ≤
        ηRow}

/-- Computed Frobenius event for non-injective CountSketch followed by iid
uniform-row sampling with a computed row-scale denominator.  The event charges
the sparse CountSketch apply, denominator computation, rounded row divisions,
and rounded sampled-Gram dot products through the realized budget. -/
def countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasis fp A x.1
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s Vhat dhat.den x.2 j k -
          rowGram A j k) ≤
      ηCS + ηRow +
        countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat x}































































































































































































































































































/-- Computed non-injective CountSketch plus downstream uniform-row sample-Gram
two-sided finite-Loewner event centered at the exact input Gram.

The radius is exactly the S9z Frobenius radius:
`ηCS + ηRow` for the two exact Markov events plus the concrete realized
floating-point radius for sparse CountSketch apply, computed denominator,
sampled-row divisions, and sampled-Gram dot products. -/
def countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasis fp A x.1
    let τ : ℝ :=
      ηCS + ηRow +
        countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat x
    finiteLoewnerLe
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k)
      (fun j k => τ * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k =>
        -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k))
      (fun j k => τ * finiteIdMatrix j k)}

/-- Stored-sign computed non-injective CountSketch plus downstream uniform-row
sample-Gram two-sided finite-Loewner event centered at the exact input Gram.

The event radius charges the exact CountSketch cover radius `ηCS`, the exact
downstream row-sampling radius `ηRow`, and the concrete stored-sign
floating-point radius for sign storage/copying, sparse bucket accumulation,
computed denominator, sampled-row divisions, and sampled-Gram dot products. -/
def countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSign
        fp A storedSignOf x.1
    let τ : ℝ :=
      ηCS + ηRow +
        countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
          fp A storedSignOf dhat x
    finiteLoewnerLe
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k)
      (fun j k => τ * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k =>
        -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k))
      (fun j k => τ * finiteIdMatrix j k)}

/-- Stored-sign computed non-injective CountSketch with exact per-bucket
traversal orders, followed by downstream uniform-row sample-Gram, centered at
the exact input Gram.

The event radius charges the exact CountSketch cover radius `ηCS`, the exact
downstream row-sampling radius `ηRow`, and the concrete floating-point radius
for sign storage/copying, bucket accumulation in the selected order, computed
denominator, sampled-row divisions, and sampled-Gram dot products. -/
def countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
        fp A storedSignOf orderOf x.1
    let τ : ℝ :=
      ηCS + ηRow +
        countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
          fp A storedSignOf orderOf dhat x
    finiteLoewnerLe
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k)
      (fun j k => τ * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k =>
        -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k))
      (fun j k => τ * finiteIdMatrix j k)}

/-- Stored-sign computed non-injective CountSketch with tree-reduced bucket
accumulations, followed by downstream uniform-row sample-Gram, centered at
the exact input Gram.

The event radius charges the exact CountSketch cover radius `ηCS`, the exact
downstream row-sampling radius `ηRow`, and the concrete floating-point radius
for sign storage/copying, tree-reduced bucket accumulation, computed
denominator, sampled-row divisions, and sampled-Gram dot products. -/
def countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSignTree
        fp A storedSignOf treeOf x.1
    let τ : ℝ :=
      ηCS + ηRow +
        countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
          fp A storedSignOf treeOf dhat x
    finiteLoewnerLe
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k)
      (fun j k => τ * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k =>
        -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k))
      (fun j k => τ * finiteIdMatrix j k)}

/-- The S9z computed Frobenius event implies the corresponding two-sided
finite-Loewner event.  This is a deterministic Frobenius-to-operator bridge
applied after all computed non-probability quantities have already been
charged. -/
theorem countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent_subset_twoSidedLoewnerEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
      fp A dhat ηCS ηRow ⊆
      countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
        fp A dhat ηCS ηRow := by
  classical
  intro x hx
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasis fp A x.1
  let τ : ℝ :=
    ηCS + ηRow +
      countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat x
  let Delta : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        rowGram A j k
  have hpert : frobNorm Delta ≤ τ := by
    simpa [
      countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent,
      Delta, Vhat, τ] using hx
  have hzeroUpper :
      finiteLoewnerLe (fun _j _k : Fin n => 0)
        (fun j k : Fin n => (0 : ℝ) * finiteIdMatrix j k) := by
    intro z
    simp
  have hzeroLower :
      finiteLoewnerLe (fun j k : Fin n => -(fun _j _k : Fin n => 0) j k)
        (fun j k : Fin n => (0 : ℝ) * finiteIdMatrix j k) := by
    intro z
    simp
  have h :=
    finiteLoewnerLe_two_sided_add_of_frobNorm_le
      (Exact := fun _j _k : Fin n => 0)
      (Delta := Delta) (ε := 0) (τ := τ)
      hzeroUpper hzeroLower hpert
  simpa [
    countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent,
    Delta, Vhat, τ] using h














































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Deterministic budget adapter for orthonormal product-grid CountSketch plus
downstream uniform-row sampling.

The exact coefficient/Frobenius product-grid loss for an orthonormal-column
input is bounded by the readable loss involving only the product-grid vector
norms and `n`; the downstream row term uses `||U||_F^2 = n`. -/
theorem countSketchUniformRow_productGrid_orthonormal_coeff_add_frob_add_row_budget
    {r m n s : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (grid : α → ℝ) {η L ηRow δ : ℝ}
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let δCS : ℝ :=
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
    δCS + δRow ≤ δ := by
  classical
  let δCoeff : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
  let δCoeffReadable : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
  let δRowExact : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
  let δRowReadable : ℝ :=
    (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
  have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
  have hvecTerm :
      ∀ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2 ≤
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
            η ^ 2 := by
    intro a
    have hpair :
        (∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) ≤
          vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 := by
      calc
        (∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2)
            ≤
          vecNorm2Sq (rectMatMulVec U (fun j : Fin n => grid (a j))) ^ 2 :=
            countSketchDistinctPair_vecCoeffSq_sum_le_vecNorm2Sq_sq
              (rectMatMulVec U (fun j : Fin n => grid (a j)))
        _ = vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 := by
            rw [hasOrthonormalColumns_vecNorm2Sq_rectMatMulVec_eq U hU]
    have hmul :
        2 * (r : ℝ)⁻¹ *
            (∑ p : CountSketchDistinctPair m,
              (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) ≤
          2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 :=
      mul_le_mul_of_nonneg_left hpair hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg η)
  have hvecSum :
      (∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) ≤
        ∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2 :=
    Finset.sum_le_sum (fun a _ => hvecTerm a)
  have hgram :
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2 ≤
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2 := by
    have hcoeff :
        (∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2) ≤
          (n : ℝ) ^ 2 := by
      calc
        (∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2)
            ≤ frobNormSqRect U ^ 2 :=
              countSketchDistinctPair_gramCoeffSq_sum_le_frobNormSqRect_sq U
        _ = (n : ℝ) ^ 2 := by
              rw [frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU]
    have hmul :
        2 * (r : ℝ)⁻¹ *
            (∑ j : Fin n, ∑ k : Fin n,
              ∑ p : CountSketchDistinctPair m,
                (U p.1.1 j * U p.1.2 k) ^ 2) ≤
          2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg L)
  have hcoeffReadable : δCoeff ≤ δCoeffReadable := by
    dsimp [δCoeff, δCoeffReadable]
    linarith
  have hrowEq : δRowExact = δRowReadable := by
    dsimp [δRowExact, δRowReadable]
    rw [frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU]
  dsimp
  have hreadable : δCoeffReadable + δRowReadable ≤ δ := by
    simpa [δCoeffReadable, δRowReadable] using hbudget
  have hmono : δCoeff + δRowExact ≤ δCoeffReadable + δRowReadable := by
    rw [hrowEq]
    linarith
  exact hmono.trans hreadable


































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Exact sampled-Gram error for a rectangularly preconditioned factored input
`A = U C` is the right-factor congruence of the orthonormal-basis sampled-Gram
error. -/
theorem uniformRowSampleGram_rectFactoredInput_error_eq_rightGramCongruence_error
    {r m q n s : ℕ} (P : Fin r → Fin m → ℝ)
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (samples : RowTrace r s) (hU : HasOrthonormalColumns U)
    (hr : 0 < r) (hs : 0 < (s : ℝ)) :
    (fun j k : Fin n =>
        uniformRowSampleGram
            (preconditionRows P (preconditionColumns U C)) samples j k -
          rowGram (preconditionColumns U C) j k) =
      rightGramCongruence
        (fun a b : Fin q =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C := by
  classical
  let V : Fin r → Fin q → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  have hY :
      preconditionRows P A = preconditionColumns V C := by
    simpa [A, V] using preconditionRows_preconditionColumns_assoc_rect P U C
  have hsample :
      uniformRowSampleGram (preconditionRows P A) samples =
        rightGramCongruence (uniformRowSampleGram V samples) C := by
    rw [hY]
    exact
      uniformRowSampleGram_preconditionColumns_eq_rightGramCongruence
        V C samples hr hs
  have hAgram : rowGram A = rowGram C := by
    change rowGram (preconditionColumns U C) = rowGram C
    rw [rowGram_preconditionColumns_eq_rightGramCongruence]
    have hgram : rowGram U = idMatrix q :=
      rowGram_eq_id_of_orthonormal_columns U hU
    ext j k
    have hcong :
        rightGramCongruence
            (fun a b : Fin q => (1 : ℝ) * finiteIdMatrix a b) C j k =
          (fun j k : Fin n => (1 : ℝ) * rowGram C j k) j k := by
      simpa using
        congrFun (congrFun
          (rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1) j) k
    simpa [hgram, idMatrix] using hcong
  ext j k
  calc
    uniformRowSampleGram (preconditionRows P (preconditionColumns U C)) samples j k -
        rowGram (preconditionColumns U C) j k
        =
      rightGramCongruence (uniformRowSampleGram V samples) C j k -
        rightGramCongruence (finiteIdMatrix : Fin q → Fin q → ℝ) C j k := by
        simp [A, V, hsample, hAgram,
          rightGramCongruence_finiteIdMatrix_eq_rowGram]
    _ =
      rightGramCongruence
        (fun a b : Fin q =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C j k := by
        have hsub :=
          congrFun (congrFun
            (rightGramCongruence_sub
              (uniformRowSampleGram V samples)
              (finiteIdMatrix : Fin q → Fin q → ℝ) C) j) k
        simpa [V] using hsub.symm

/-- Exact two-sided sampled-Gram event for a finite signed-mixing Algorithm 3
input matrix factored as `A = U C`, where `U` is the exact orthonormal analysis
basis. -/
def signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent
    {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ) (ε : ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    let P : Fin r → Fin m → ℝ :=
      signedMixingRows G (rademacherSignVector x.1)
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Y : Fin r → Fin n → ℝ := preconditionRows P A
    finiteLoewnerLe
      (fun j k : Fin n => uniformRowSampleGram Y x.2 j k - rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n => -(uniformRowSampleGram Y x.2 j k - rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k)}

/-- The orthonormal-basis signed-mixing sample-Gram event implies the
corresponding factored-input event for `A = U C`. -/
theorem signedMixingUniformRowSampleGramTwoSidedEvent_subset_factoredInput
    {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ) (ε : ℝ)
    (hU : HasOrthonormalColumns U) (hr : 0 < r) (hs : 0 < (s : ℝ)) :
    signedMixingUniformRowSampleGramTwoSidedEvent
        (r := r) (m := m) (n := q) (s := s) G U ε ⊆
      signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent
        (r := r) (m := m) (q := q) (n := n) (s := s) G U C ε := by
  classical
  intro x hx
  let P : Fin r → Fin m → ℝ :=
    signedMixingRows G (rademacherSignVector x.1)
  let V : Fin r → Fin q → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  let Y : Fin r → Fin n → ℝ := preconditionRows P A
  let ExactU : Fin q → Fin q → ℝ :=
    fun a b => uniformRowSampleGram V x.2 a b - finiteIdMatrix a b
  let ExactA : Fin n → Fin n → ℝ :=
    fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
  let EpsU : Fin q → Fin q → ℝ :=
    fun a b => ε * finiteIdMatrix a b
  let EpsA : Fin n → Fin n → ℝ :=
    fun j k => ε * rowGram A j k
  have hxU :
      finiteLoewnerLe ExactU EpsU ∧
      finiteLoewnerLe (fun a b : Fin q => -ExactU a b) EpsU := by
    simpa [signedMixingUniformRowSampleGramTwoSidedEvent, P, V, ExactU, EpsU]
      using hx
  have hErr :
      ExactA = rightGramCongruence ExactU C := by
    simpa [P, V, A, Y, ExactU, ExactA] using
      uniformRowSampleGram_rectFactoredInput_error_eq_rightGramCongruence_error
        P U C x.2 hU hr hs
  have hEps :
      rightGramCongruence EpsU C = EpsA := by
    simpa [A, EpsU, EpsA] using
      rightGramCongruence_smul_finiteIdMatrix_eq_smul_factoredInputGram
        U C hU ε
  have hUpperBase :
      finiteLoewnerLe (rightGramCongruence ExactU C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.1
  have hLowerBase :
      finiteLoewnerLe
        (rightGramCongruence (fun a b : Fin q => -ExactU a b) C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.2
  have hUpper : finiteLoewnerLe ExactA EpsA := by
    rw [hErr, ← hEps]
    exact hUpperBase
  have hNegErr :
      (fun j k : Fin n => -ExactA j k) =
        rightGramCongruence (fun a b : Fin q => -ExactU a b) C := by
    rw [hErr]
    rw [rightGramCongruence_neg]
  have hLower : finiteLoewnerLe (fun j k : Fin n => -ExactA j k) EpsA := by
    rw [hNegErr, ← hEps]
    exact hLowerBase
  simpa [signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent,
    P, A, Y, ExactA, EpsA] using And.intro hUpper hLower
















































/-- Fully floating-point computed-input event for finite signed mixing on a
factored input `A = U C`, using a computed uniform row-scale denominator. -/
def signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace r s → ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k)}























































































































































































































































































































































































/-- Sample-dependent perturbation budget for the concrete computed-left and
computed-input Algorithm 3 path.  The first term charges rounded row scaling
and sampled-Gram dot products after `Vhat` has been formed.  The second term
charges the difference between the exact sampled Gram of
`Vhat = fl(Pihat * Uhat)` and that of the ideal signed-Hadamard basis
`H D_ω U`. -/
noncomputable def signedHadamardComputedLeftInputUniformRowPerturbBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (x : RademacherTrace m × RowTrace m s) : ℝ :=
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
      fp H Uhat Pihat x.1
  uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2








































































































/-- Sample-dependent perturbation budget for the concrete computed-left and
computed-input Algorithm 3 path when the uniform row-scale denominator is
computed.  It charges the computed denominator, rounded row divisions, rounded
Gram dot products, the computed left preconditioner, and the computed/stored
input matrix before comparing back to the exact signed-Hadamard product
`H D_ω U`. -/
noncomputable def signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (dhat : ComputedUniformRowScaleDen fp m s)
    (x : RademacherTrace m × RowTrace m s) : ℝ :=
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
      fp H Uhat Pihat x.1
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
