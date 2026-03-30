-- Condition A: Bare (no library, no axioms provided)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Task 4: PLU solve backward error

Prove the following in Lean 4 using only Mathlib:

**Theorem (Higham §9.3–9.4):** Consider solving Ax = b via PA = LU (partial
pivoting). The computed solution x̂ obtained by forward substitution (Ly = Pb)
then back substitution (Ux = y) satisfies:

  (A + ΔA)x̂ = b

where |ΔA_{ij}| ≤ (3γ(n) + γ(n)²) · ∑_k |L̂_{σ⁻¹(i),k}| · |Û_{kj}|

and P is a permutation matrix with σ : Fin n → Fin n.

You must:
1. Define an appropriate floating-point model
2. Define forward substitution, back substitution, and the LU solve
3. Define permutations and the permuted system
4. Define γ(n) and state the validity condition
5. State and prove the theorem
-/

open scoped BigOperators

-- YOUR DEFINITIONS AND PROOF HERE:

sorry
