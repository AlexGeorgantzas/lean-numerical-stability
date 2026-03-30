-- Condition B: Axioms only (FPModel + gamma provided, no library lemmas)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open scoped BigOperators

/-! ## Provided: Floating-point model and gamma calculus axioms -/

structure FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y, ∃ δ : ℝ, |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_sub : ∀ x y, ∃ δ : ℝ, |δ| ≤ u ∧ fl_sub x y = (x - y) * (1 + δ)
  model_mul : ∀ x y, ∃ δ : ℝ, |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)
  model_div : ∀ x y, y ≠ 0 → ∃ δ : ℝ, |δ| ≤ u ∧ fl_div x y = (x / y) * (1 + δ)

noncomputable def gamma (fp : FPModel) (n : ℕ) : ℝ :=
  (n * fp.u) / (1 - n * fp.u)

def gammaValid (fp : FPModel) (n : ℕ) : Prop :=
  (n : ℝ) * fp.u < 1

/-! ## Task 10: Stationary iteration with inexact triangular solve

Show that when a stationary iteration (A = M − N) uses forward substitution
for the M-solve, the perturbation ξ_k = ΔM·x̂_{k+1} satisfies:
  ‖ξ_k‖_∞ ≤ γ(n)·‖M‖_∞·‖x̂_{k+1}‖_∞

You must define forward substitution, its backward error, infinity norms,
the stationary iteration framework, and prove the bound.
-/

-- YOUR DEFINITIONS AND PROOF HERE:

sorry
