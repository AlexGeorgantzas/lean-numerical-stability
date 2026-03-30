-- Condition A: Bare (no library, no axioms provided)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Task 8: BLAS GEMV forward error bound

Prove the following in Lean 4 using only Mathlib:

**Theorem (Higham §3.5, BLAS Level 2):** Under the standard FP model, the
BLAS GEMV operation ŷ = fl(α·Ax + β·y₀) satisfies componentwise:

  |ŷ_i − (α·∑_j A_{ij}x_j + β·(y₀)_i)| ≤
    γ(n+2)·|α|·∑_j |A_{ij}|·|x_j| + γ(2)·|β|·|(y₀)_i|

The computation is:
  1. ŝ_i = fl(∑_j A_{ij} x_j)  (inner product, n multiplications + additions)
  2. t̂_i = fl(α · ŝ_i)         (one multiplication)
  3. û_i = fl(β · (y₀)_i)       (one multiplication)
  4. ŷ_i = fl(t̂_i + û_i)       (one addition)

You must:
1. Define an appropriate floating-point model
2. Define the full GEMV algorithm
3. Define γ(n) and all required composition lemmas
4. State and prove the theorem
-/

open scoped BigOperators

-- YOUR DEFINITIONS AND PROOF HERE:

sorry
