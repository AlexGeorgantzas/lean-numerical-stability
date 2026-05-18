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
import LeanFpAnalysis.FP.Algorithms.DotProduct

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- Exact and floating-point vector 2-norm kernels
-- ============================================================

/-- Exact squared Euclidean norm, `∑ᵢ xᵢ²`. -/
noncomputable def exactNorm2Sq (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, x i * x i

/-- Exact Euclidean norm, `sqrt (∑ᵢ xᵢ²)`. -/
noncomputable def exactNorm2 (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (exactNorm2Sq n x)

/-- Floating-point squared 2-norm computed as the dot product `xᵀx`. -/
noncomputable def fl_norm2Sq (fp : FPModel) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  fl_dotProduct fp n x x

/-- Floating-point 2-norm: rounded square root of the computed sum of squares.

    The domain side condition for the square-root error model is carried by
    theorems that reason about this definition. -/
noncomputable def fl_norm2 (fp : FPModel) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  fp.fl_sqrt (fl_norm2Sq fp n x)

theorem exactNorm2Sq_nonneg (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ exactNorm2Sq n x := by
  unfold exactNorm2Sq
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem exactNorm2_nonneg (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ exactNorm2 n x := by
  unfold exactNorm2
  exact Real.sqrt_nonneg _

/-- Backward-error form for the computed sum of squares. -/
theorem fl_norm2Sq_backward_error (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp n) :
    ∃ η : Fin n → ℝ,
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      fl_norm2Sq fp n x = ∑ i : Fin n, x i * x i * (1 + η i) := by
  simpa [fl_norm2Sq] using dotProduct_backward_error fp n x x hn

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

end LeanFpAnalysis.FP
