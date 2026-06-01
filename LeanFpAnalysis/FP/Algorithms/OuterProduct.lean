-- Algorithms/OuterProduct.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import LeanFpAnalysis.FP.Model

namespace LeanFpAnalysis.FP

/-- Floating-point outer product Â = fl(xyᵀ).

    Computed entrywise: each entry (i, j) of Â is the floating-point
    multiplication of xᵢ by yⱼ (Higham §3.1):
      Âᵢⱼ = fl(xᵢ * yⱼ) -/
noncomputable def fl_outerProduct (fp : FPModel) (m n : ℕ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => fp.fl_mul (x i) (y j)

/-- **Outer product forward error bound** (Higham §3.1, equation 3.6).

    The computed outer product satisfies, componentwise:
      |Â - xyᵀ| ≤ u|xyᵀ|

    Formally: for each entry (i, j),
      |fl_outerProduct fp x y i j - x i * y j| ≤ fp.u * |x i * y j|

    Proof: by definition Âᵢⱼ = fl(xᵢ * yⱼ) = xᵢ * yⱼ * (1 + δᵢⱼ)
    with |δᵢⱼ| ≤ u, so Âᵢⱼ − xᵢyⱼ = xᵢyⱼ · δᵢⱼ,
    and |Âᵢⱼ − xᵢyⱼ| = |xᵢyⱼ| · |δᵢⱼ| ≤ u|xᵢyⱼ|. -/
theorem outerProduct_error_bound (fp : FPModel) (m n : ℕ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    ∀ i : Fin m, ∀ j : Fin n,
      |fl_outerProduct fp m n x y i j - x i * y j| ≤ fp.u * |x i * y j| := by
  intro i j
  unfold fl_outerProduct
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul (x i) (y j)
  rw [hfl]
  -- (x i * y j) * (1 + δ) - x i * y j = x i * y j * δ
  have h_eq : (x i * y j) * (1 + δ) - x i * y j = x i * y j * δ := by ring
  rw [h_eq, abs_mul, mul_comm (|x i * y j|)]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

/-- **Row-wise outer product perturbation representation** (Higham §3.1).

    The computed outer product is the exact outer product of x with a
    row-dependent perturbed ỹ: for each fixed row `i`, there exists Δy such that
      ∀ j, |Δy j| ≤ fp.u * |y j|
      ∀ i j, fl_outerProduct fp x y i j = x i * (y j + Δy j)

    This is deliberately not advertised as full backward stability of the
    outer-product algorithm.  Higham notes after equation (3.6) that the
    computed outer product generally cannot be written as
    `(x + Δx)(y + Δy)ᵀ`, because the computed matrix need not remain rank one.

    Proof: for each fixed row `i` and column `j`, take
    `Δy j = y j * δᵢⱼ`.  Since δᵢⱼ may vary with `i`, a single global Δy
    independent of the row does not exist in general. -/
theorem outerProduct_backward_error (fp : FPModel) (m n : ℕ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    ∀ i : Fin m, ∃ Δy : Fin n → ℝ,
      (∀ j, |Δy j| ≤ fp.u * |y j|) ∧
      ∀ j, fl_outerProduct fp m n x y i j = x i * (y j + Δy j) := by
  intro i
  let δ : Fin n → ℝ := fun j => Classical.choose (fp.model_mul (x i) (y j))
  have hδ : ∀ j, |δ j| ≤ fp.u ∧ fp.fl_mul (x i) (y j) = x i * y j * (1 + δ j) :=
    fun j => Classical.choose_spec (fp.model_mul (x i) (y j))
  refine ⟨fun j => y j * δ j, fun j => ?_, fun j => ?_⟩
  · -- bound: |y j * δ j| ≤ u * |y j|
    rw [abs_mul, mul_comm (|y j|)]
    exact mul_le_mul_of_nonneg_right (hδ j).1 (abs_nonneg _)
  · -- equality: fl_mul (x i) (y j) = x i * (y j + y j * δ j)
    unfold fl_outerProduct
    rw [(hδ j).2]; ring

end LeanFpAnalysis.FP
