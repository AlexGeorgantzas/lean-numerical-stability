-- Condition A: Bare (no library, no axioms provided)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Task 3: Normwise matrix-vector forward error bound

Prove the following in Lean 4 using only Mathlib:

**Theorem (Higham §3.5):** Under the standard FP model fl(a op b) = (a op b)(1+δ),
|δ| ≤ u, the computed matrix-vector product ŷ = fl(Ax) satisfies:

  ‖ŷ − Ax‖∞ ≤ γ(n) · ‖|A| · |x|‖∞

where γ(n) = nu/(1−nu), ‖v‖∞ = max_i |v_i|, and (|A|·|x|)_i = ∑_j |A_{ij}|·|x_j|.

You must:
1. Define an appropriate floating-point model
2. Define the matrix-vector product algorithm
3. Define γ(n), the infinity norm, and state the validity condition
4. Prove the componentwise bound, then lift to the normwise bound
-/

open scoped BigOperators

-- YOUR DEFINITIONS AND PROOF HERE:

sorry
