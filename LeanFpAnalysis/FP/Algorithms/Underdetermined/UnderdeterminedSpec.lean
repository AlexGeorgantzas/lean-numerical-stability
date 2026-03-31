-- Algorithms/Underdetermined/UnderdeterminedSpec.lean
--
-- Solution methods and perturbation theory for underdetermined systems
-- (Higham §20.1–20.2).
--
-- An underdetermined system Ax = b with A ∈ ℝ^{m×n}, m < n, has
-- infinitely many solutions. The minimum 2-norm solution is
-- x_LS = Aᵀ(AAᵀ)⁻¹b = A⁺b.
--
-- Two solution methods use the QR factorization Aᵀ = Q[R; 0]:
-- - Q method: solve Rᵀy₁ = b, form x = Q[y₁; 0]ᵀ
-- - SNE method: solve RᵀRy = b, form x = Aᵀy
--
-- Theorem 20.1 (Demmel-Higham): Componentwise perturbation bound
-- for the minimum-norm solution.
-- Lemma 20.2 (Kielbasiński-Schwetlick): Asymmetric normal equation
-- perturbations can be symmetrized without increasing the bound.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §20.1  Minimum-norm solution specification
-- ============================================================

/-- **Minimum 2-norm solution of an underdetermined system** (Higham §20.1).

    For Ax = b with A ∈ ℝ^{m×n} (m < n), the minimum-norm solution is
    x_LS = Aᵀ(AAᵀ)⁻¹b. In the QR factorization framework with
    Aᵀ = Q[R; 0], this becomes x_LS = Q[R⁻ᵀb; 0].

    Since A is rectangular, we work with the m×m Gram matrix AAᵀ.
    The structure captures: (AAᵀ)⁻¹ exists (A has full row rank),
    and x solves the normal equations AAᵀy = b with x = Aᵀy. -/
structure MinNormSolution (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ) : Prop where
  /-- AAᵀ is invertible. -/
  gram_inv : IsInverse m AAT AAT_inv
  /-- y solves the normal equations AAᵀy = b. -/
  normal_eq : ∀ i, matMulVec m AAT y i = b i

-- ============================================================
-- §20.2  Theorem 20.1: Demmel-Higham perturbation bound
-- ============================================================

/-- **Theorem 20.1** (Demmel and Higham): Componentwise perturbation
    of the minimum 2-norm solution to an underdetermined system.

    Let A ∈ ℝ^{m×n} (m ≤ n) be of full rank, and let x, y be the
    minimum 2-norm solutions to Ax = b and (A+ΔA)y = b+Δb. Then:

    ‖x−y‖/‖x‖ ≤ (‖|I−A⁺A|·Eᵀ·|A⁺ᵀx|‖ + ‖|A⁺|·(f+E|x|)‖)·ε/‖x‖ + O(ε²)

    where |ΔA| ≤ εE, |Δb| ≤ εf.

    Special cases (eq 20.8–20.9):
    - E = |A|H, f = |b|: bound involves cond₂(A) = ‖|A⁺||A|‖₂
    - Normwise: ‖x−y‖₂/‖x‖₂ ≤ min{3,n−m+2}(mn)^{1/2}κ₂(A)ε + O(ε²)

    Axiomatized since it requires pseudo-inverse and rectangular matrices. -/
structure DemmelHighamPerturbation (m : ℕ)
    (x y : Fin m → ℝ) (kappa eps : ℝ)
    (sol_bound : ℝ) : Prop where
  /-- κ₂(A) > 0. -/
  kappa_pos : 0 < kappa
  /-- ε is nonnegative. -/
  eps_nonneg : 0 ≤ eps
  /-- The perturbation is small enough. -/
  small_pert : kappa * eps < 1
  /-- Forward error bound (normwise form, eq 20.9):
      ‖x−y‖₂ ≤ sol_bound. -/
  bound : ∀ i, |y i - x i| ≤ sol_bound

-- ============================================================
-- §20.2  Lemma 20.2: Kielbasiński-Schwetlick symmetrization
-- ============================================================

/-- **Lemma 20.2** (Kielbasiński and Schwetlick): Perturbation symmetrization
    for underdetermined normal equations.

    If x̄ satisfies (A+ΔA₁)x̄ = b and x̄ = (A+ΔA₂)ᵀȳ, then there
    exists a single ΔA with ΔA = ΔA₁G₁ + ΔA₂G₂ (G₁+G₂=I) such that
    x̄ is the minimum 2-norm solution to (A+ΔA)x = b.

    The normwise bound satisfies: ‖ΔA‖_p ≤ (‖ΔA₁‖²_p + ‖ΔA₂‖²_p)^{1/2}.

    This is the underdetermined analogue of Lemma 19.6.
    Axiomatized since the proof requires rectangular projections. -/
structure KielbasinskiSchwetlickUndet (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin m → ℝ)
    (eps1 eps2 : ℝ) : Prop where
  /-- Perturbation bounds are nonneg. -/
  eps_nonneg : 0 ≤ eps1 ∧ 0 ≤ eps2
  /-- There exists a symmetrized perturbation ΔG to the Gram system
      with ‖ΔG‖ ≤ (eps1² + eps2²)^{1/2} such that x̂ is the
      minimum-norm solution to a nearby system. -/
  symmetrized : ∃ (ΔG : Fin m → Fin m → ℝ),
    frobNorm ΔG ≤ Real.sqrt (eps1 ^ 2 + eps2 ^ 2) ∧
    (∀ i, matMulVec m (fun a b => AAT a b + ΔG a b) x_hat i = b i)

end LeanFpAnalysis.FP
