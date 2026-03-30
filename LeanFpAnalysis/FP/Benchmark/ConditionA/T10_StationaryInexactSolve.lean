-- Condition A: Bare (no library, no axioms provided)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Task 10: Stationary iteration with inexact triangular solve

Prove the following in Lean 4 using only Mathlib:

**Theorem (Higham §16 + §8.5):** A stationary iterative method splits A = M − N
and iterates x_{k+1} = M⁻¹(Nx_k + b). When M is lower triangular and the
"M⁻¹" application is computed via forward substitution, the backward error
of each solve produces a perturbation ξ_k = ΔM · x̂_{k+1}.

Show that:
  ‖ξ_k‖_∞ ≤ γ(n) · ‖M‖_∞ · ‖x̂_{k+1}‖_∞

where ΔM is the backward error matrix from forward substitution satisfying
|ΔM_{ij}| ≤ γ(n)|M_{ij}|.

You must:
1. Define an appropriate floating-point model
2. Define forward substitution with backward error
3. Define the infinity norm for vectors and matrices
4. Define the stationary iteration framework
5. State and prove the perturbation bound
-/

open scoped BigOperators

-- YOUR DEFINITIONS AND PROOF HERE:

sorry
