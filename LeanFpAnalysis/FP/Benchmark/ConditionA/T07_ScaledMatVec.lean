-- Condition A: Bare (no library, no axioms provided)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Task 7: Scaled matrix-vector product error bound

Prove the following in Lean 4 using only Mathlib:

**Theorem (Higham §3.5, extended):** Under the standard FP model, the computed
scaled matrix-vector product ŷ = fl(α · fl(Ax)) satisfies:

  |ŷ_i − α · ∑_j A_{ij} x_j| ≤ γ(n+1) · |α| · ∑_j |A_{ij}| · |x_j|

where γ(n) = nu/(1−nu).

You must:
1. Define an appropriate floating-point model
2. Define the matrix-vector product and scalar multiplication algorithms
3. Define γ(n), the gamma_mul composition lemma, and the validity condition
4. State and prove the theorem
-/

open scoped BigOperators

-- YOUR DEFINITIONS AND PROOF HERE:

sorry
