-- Model.lean

import Mathlib.Data.Real.Basic

namespace LeanFpAnalysis.FP

/--
A Higham-style axiomatic floating-point model.

We assume each arithmetic operation satisfies:
fl(x op y) = (x op y)(1 + δ), with |δ| ≤ u.
-/

structure FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u

  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ

  /-- Adding 0 is exact: fl(0 + x) = x.  This holds in IEEE 754 because
      0 + x = x exactly, so no rounding error arises. -/
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x

  model_add :
    ∀ x y, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)

  model_sub :
    ∀ x y, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_sub x y = (x - y) * (1 + δ)

  model_mul :
    ∀ x y, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_mul x y = (x * y) * (1 + δ)

  model_div :
    ∀ x y, y ≠ 0 →
      ∃ δ : ℝ,
        |δ| ≤ u ∧
        fl_div x y = (x / y) * (1 + δ)

end LeanFpAnalysis.FP
