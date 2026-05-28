-- Algorithms/Norm2.lean
--
-- Floating-point Euclidean norm kernels.
--
-- This file provides the low-level operation needed by Householder reflector
-- construction: compute a sum of squares using the existing floating-point dot
-- product, then apply the rounded square-root primitive from `FPModel`.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import LeanFpAnalysis.FP.Algorithms.DotProduct

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- Exact Mathlib facts and floating-point vector 2-norm kernels
-- ============================================================

/-- Mathlib's finite-product L2 norm is the square root of the dot product. -/
theorem norm_toLp_two_eq_sqrt_dotProduct (n : ℕ) (x : Fin n → ℝ) :
    ‖WithLp.toLp 2 x‖ = Real.sqrt (x ⬝ᵥ x) := by
  rw [PiLp.norm_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
  unfold dotProduct
  simp [pow_two]

/-- Floating-point squared 2-norm computed as the dot product `xᵀx`. -/
noncomputable def fl_norm2Sq (fp : FPModel) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  fl_dotProduct fp n x x

/-- Floating-point 2-norm: rounded square root of the computed sum of squares.

    The domain side condition for the square-root error model is carried by
    theorems that reason about this definition. -/
noncomputable def fl_norm2 (fp : FPModel) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  fp.fl_sqrt (fl_norm2Sq fp n x)

theorem dotProduct_self_nonneg_real (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ x := by
  unfold dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- The squared 2-norm is zero exactly for the zero vector. -/
theorem dotProduct_self_eq_zero_iff_real (n : ℕ) (x : Fin n → ℝ) :
    x ⬝ᵥ x = 0 ↔ x = 0 := by
  exact dotProduct_self_eq_zero

/-- The squared 2-norm is nonzero exactly for a nonzero vector. -/
theorem dotProduct_self_ne_zero_iff_real (n : ℕ) (x : Fin n → ℝ) :
    x ⬝ᵥ x ≠ 0 ↔ x ≠ 0 := by
  exact not_congr (dotProduct_self_eq_zero_iff_real n x)

/-- The squared 2-norm is positive exactly for a nonzero vector. -/
theorem dotProduct_self_pos_iff_real (n : ℕ) (x : Fin n → ℝ) :
    0 < x ⬝ᵥ x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    rw [hx] at h
    simp [dotProduct] at h
  · intro hx
    have hne : x ⬝ᵥ x ≠ 0 :=
      (dotProduct_self_ne_zero_iff_real n x).2 hx
    exact lt_of_le_of_ne (dotProduct_self_nonneg_real n x) (Ne.symm hne)

theorem norm_toLp_two_nonneg (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ ‖WithLp.toLp 2 x‖ := by
  exact norm_nonneg _

/-- Backward-error form for the computed sum of squares. -/
theorem fl_norm2Sq_backward_error (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp n) :
    ∃ η : Fin n → ℝ,
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      fl_norm2Sq fp n x = ∑ i : Fin n, x i * x i * (1 + η i) := by
  simpa [fl_norm2Sq] using dotProduct_backward_error fp n x x hn

/-- The computed sum of squares is nonnegative when the dot-product error
    factors remain nonnegative.  The `2*n` validity condition is the standard
    way to obtain `gamma fp n < 1`. -/
theorem fl_norm2Sq_nonneg_of_gammaValid_two_mul (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp (2 * n)) :
    0 ≤ fl_norm2Sq fp n x := by
  have hn_small : gammaValid fp n := gammaValid_mono fp (by omega) hn
  obtain ⟨η, hη, hsum⟩ := fl_norm2Sq_backward_error fp n x hn_small
  rw [hsum]
  exact Finset.sum_nonneg fun i _ => by
    have hγ_lt : gamma fp n < 1 := gamma_lt_one fp n hn
    have hfactor : 0 ≤ 1 + η i := by
      linarith [neg_abs_le (η i), hη i, hγ_lt]
    exact mul_nonneg (mul_self_nonneg (x i)) hfactor

/-- Unrolled form for the floating-point 2-norm.

    This exposes both layers of rounding:

    * `η` comes from the dot-product/sum-of-squares computation;
    * `δ` comes from the rounded square root.

    The hypothesis `0 ≤ fl_norm2Sq fp n x` is the domain condition needed to
    apply the square-root model.  Proving it from small-error assumptions is a
    later positivity lemma, not an extra QR-specific assumption. -/
theorem fl_norm2_unroll (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp n)
    (hσ_nonneg : 0 ≤ fl_norm2Sq fp n x) :
    ∃ (η : Fin n → ℝ) (δ : ℝ),
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      |δ| ≤ fp.u ∧
      fl_norm2 fp n x =
        Real.sqrt (∑ i : Fin n, x i * x i * (1 + η i)) * (1 + δ) := by
  obtain ⟨η, hη, hsum⟩ := fl_norm2Sq_backward_error fp n x hn
  obtain ⟨δ, hδ, hsqrt⟩ := fp.model_sqrt (fl_norm2Sq fp n x) hσ_nonneg
  refine ⟨η, δ, hη, hδ, ?_⟩
  unfold fl_norm2
  rw [hsqrt, hsum]

/-- Convenience form of `fl_norm2_unroll` using the standard `2*n`
    `gammaValid` side condition to discharge square-root nonnegativity. -/
theorem fl_norm2_unroll_of_gammaValid_two_mul (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp (2 * n)) :
    ∃ (η : Fin n → ℝ) (δ : ℝ),
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      |δ| ≤ fp.u ∧
      fl_norm2 fp n x =
        Real.sqrt (∑ i : Fin n, x i * x i * (1 + η i)) * (1 + δ) := by
  exact fl_norm2_unroll fp n x (gammaValid_mono fp (by omega) hn)
    (fl_norm2Sq_nonneg_of_gammaValid_two_mul fp n x hn)

end LeanFpAnalysis.FP
