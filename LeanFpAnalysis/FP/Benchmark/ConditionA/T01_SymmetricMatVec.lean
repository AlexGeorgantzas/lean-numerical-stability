-- Condition A: Bare (no library, no axioms provided)
-- The LLM must invent its own FP model and prove the result from scratch.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Task 1: Symmetric matrix-vector backward error

Prove the following in Lean 4 using only Mathlib:

**Theorem (Higham §3.5):** Let A be a real n×n symmetric matrix and x ∈ ℝⁿ.
Suppose each floating-point arithmetic operation fl(a op b) satisfies
  fl(a op b) = (a op b)(1 + δ),  |δ| ≤ u
where u is the unit roundoff. Define γ(n) = nu/(1 − nu) assuming nu < 1.

Then the computed matrix-vector product ŷ = fl(Ax) satisfies
  ŷ = (A + ΔA)x
where ΔA is **symmetric** and |ΔA_{ij}| ≤ γ(n)|A_{ij}| componentwise.

You must:
1. Define an appropriate floating-point model
2. Define the matrix-vector product algorithm
3. Define γ(n) and state the validity condition
4. State and prove the theorem
-/

open scoped BigOperators

-- YOUR DEFINITIONS AND PROOF HERE:

sorry
