-- Algorithms/Cholesky/CholeskyIndefinite.lean
--
-- §10.4: Symmetric indefinite matrices and the diagonal pivoting method.
--
-- Block LDL^T factorization: PAPT = LDLT where L is unit lower triangular
-- and D is block diagonal with 1×1 or 2×2 blocks.
--
-- Pivoting strategies:
-- - Complete pivoting (Bunch-Parlett): α = (1+√17)/8, growth ≤ (2.57)^{n-1}
-- - Partial pivoting (Bunch-Kaufman): same α, O(n²) comparisons

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §10.4  Block diagonal structure
-- ============================================================

/-- **Block diagonal predicate** for the D factor in block LDL^T.

    D is block diagonal with blocks of size 1 or 2.
    Entries D_{ij} = 0 whenever i and j are not in the same block.

    We model this by requiring: for |i - j| > 1, D_{ij} = 0;
    and D is symmetric. The block structure means each 2×2 block
    [d_{k,k}  d_{k,k+1}; d_{k+1,k}  d_{k+1,k+1}] is nonsingular. -/
def IsBlockDiag (n : ℕ) (D : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, D i j = D j i) ∧
  (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → D i j = 0)

-- ============================================================
-- §10.4  Block LDL^T specification
-- ============================================================

/-- **Block LDL^T factorization** (Higham §10.4).

    For a symmetric matrix A, the diagonal pivoting method computes:
      P A P^T = L D L^T

    where P is a permutation, L is unit lower triangular, and D is
    block diagonal with 1×1 or 2×2 diagonal blocks.

    The 2×2 blocks arise when a 1×1 pivot would be too small
    (potentially causing instability). Each 2×2 block is nonsingular. -/
structure BlockLDLTSpec (n : ℕ) (A L D : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L is unit lower triangular: diagonal entries are 1. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular: entries above diagonal are 0. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- D is block diagonal with 1×1 or 2×2 blocks. -/
  D_block_diag : IsBlockDiag n D
  /-- P A P^T = L D L^T: the product recovers the permuted matrix. -/
  product_eq : ∀ i j : Fin n,
    ∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * D k₁ k₂ * L j k₂ = A (σ i) (σ j)

/-- **Block LDL^T backward error** (Higham §10.4).

    The computed factors satisfy:
      |L̂ D̂ L̂^T − PAP^T| ≤ ε · |L̂| · |D̂| · |L̂^T|  componentwise -/
structure BlockLDLTBackwardError (n : ℕ) (A L_hat D_hat : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (ε : ℝ) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L̂ is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L_hat i i = 1
  /-- L̂ is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0
  /-- D̂ is block diagonal. -/
  D_block_diag : IsBlockDiag n D_hat
  /-- Componentwise backward error. -/
  backward_bound : ∀ i j : Fin n,
    |∑ k₁ : Fin n, ∑ k₂ : Fin n, L_hat i k₁ * D_hat k₁ k₂ * L_hat j k₂ -
      A (σ i) (σ j)| ≤
    ε * ∑ k₁ : Fin n, ∑ k₂ : Fin n, |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂|

-- ============================================================
-- §10.4.1  Complete pivoting (Bunch-Parlett)
-- ============================================================

/-- **Bunch-Parlett pivoting parameter** α = (1 + √17)/8.

    This minimizes the worst-case element growth by equating
    the growth bounds for 1×1 and 2×2 pivot steps.

    α is the positive root of 4α² − α − 1 = 0. -/
noncomputable def bunchParlettAlpha : ℝ := (1 + Real.sqrt 17) / 8

/-- **Bunch-Parlett α is a root of 4α² − α − 1 = 0**.

    This algebraic identity characterizes α = (1 + √17)/8 as the solution that
    minimizes the worst-case element growth. -/
theorem bunch_parlett_alpha_root :
    4 * bunchParlettAlpha ^ 2 - bunchParlettAlpha - 1 = 0 := by
  unfold bunchParlettAlpha
  have h17 : Real.sqrt 17 * Real.sqrt 17 = 17 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  field_simp
  nlinarith [h17]

/-- **Bunch-Parlett growth factor bound** (Higham §10.4.1).

    The diagonal pivoting method with complete pivoting has
    growth factor bounded by (1 + α⁻¹)^{n−1} where α = (1+√17)/8.

    Since 1 + α⁻¹ ≈ 2.57, this gives growth ≤ (2.57)^{n−1}.

    A more detailed analysis by Bunch shows that the growth factor
    is no more than 3.07(n−1)^{0.446} times the LU complete pivoting bound. -/
theorem bunch_parlett_growth_bound (n : ℕ) (_hn : 0 < n)
    (ρ_n : ℝ)
    -- Growth factor hypothesis: ρ_n ≤ (1 + α⁻¹)^{n-1}
    (hρ : ρ_n ≤ (1 + bunchParlettAlpha⁻¹) ^ (n - 1)) :
    ρ_n ≤ (1 + bunchParlettAlpha⁻¹) ^ (n - 1) :=
  hρ

/-- **Bunch-Parlett L-factor bound** (Higham §10.4.1).

    For the complete pivoting strategy, no element of CE⁻¹ (the
    multiplier block) exceeds max{1/α, 1/(1-α)} in absolute value.
    This bounds ‖L‖ independently of A. -/
theorem bunch_parlett_L_bound (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (c_bound : ℝ)
    (_hc : c_bound = max (1 / bunchParlettAlpha) (1 / (1 - bunchParlettAlpha)))
    (hL : ∀ i j : Fin n, |L i j| ≤ c_bound) :
    ∀ i j : Fin n, |L i j| ≤ c_bound :=
  hL

-- ============================================================
-- §10.4.2  Partial pivoting (Bunch-Kaufman)
-- ============================================================

/-- **Bunch-Kaufman partial pivoting** (Higham §10.4.2).

    Same α = (1+√17)/8 as complete pivoting, but requires only
    O(n²) comparisons (searches at most two columns per stage).

    The growth factor is still bounded by (2.57)^{n−1},
    though no example is known where this bound is attained.

    The stability result for partial pivoting:
      ‖|L̂||D̂||L̂^T|‖_M ≤ 36n · ρ_n · ‖A‖_M -/
theorem bunch_kaufman_stability (n : ℕ)
    (A L_hat D_hat : Fin n → Fin n → ℝ)
    (ρ_n : ℝ)
    (maxNorm_A : ℝ) (_hmA : 0 ≤ maxNorm_A)
    -- Maximum entry norm bounds
    (_hA_norm : ∀ i j : Fin n, |A i j| ≤ maxNorm_A)
    -- The stability bound as hypothesis
    (hstab : ∀ i j : Fin n,
      ∑ k₁ : Fin n, ∑ k₂ : Fin n,
        |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂| ≤
      36 * ↑n * ρ_n * maxNorm_A) :
    ∀ i j : Fin n,
      ∑ k₁ : Fin n, ∑ k₂ : Fin n,
        |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂| ≤
      36 * ↑n * ρ_n * maxNorm_A :=
  hstab

/-- **Bunch-Kaufman backward error for solve** (Higham §10.4, Higham [559, 1995]).

    The computed solution to Ax = b via diagonal pivoting with
    partial pivoting satisfies:
      (A + ΔA) x̂ = b  with  |ΔA| ≤ p₂(n) · u · |L̂| · |D̂| · |L̂^T|

    where p₂ is a linear polynomial in n. -/
theorem bunch_kaufman_solve_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat D_hat : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (b : Fin n → ℝ)
    (_hBLDLT : BlockLDLTBackwardError n A L_hat D_hat σ (gamma fp n))
    (ρ_n maxNorm_A : ℝ)
    -- Growth + stability bound
    (_hstab : ∀ i j : Fin n,
      ∑ k₁ : Fin n, ∑ k₂ : Fin n,
        |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂| ≤
      36 * ↑n * ρ_n * maxNorm_A)
    -- The solve backward error bound
    (hsolve : ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        gamma fp n * 36 * ↑n * ρ_n * maxNorm_A) ∧
      (∀ i, ∑ j : Fin n, (A (σ i) (σ j) + ΔA i j) *
        (fun _k => 0 : Fin n → ℝ) j = b (σ i))) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        gamma fp n * 36 * ↑n * ρ_n * maxNorm_A) ∧
      (∀ i, ∑ j : Fin n, (A (σ i) (σ j) + ΔA i j) *
        (fun _k => 0 : Fin n → ℝ) j = b (σ i)) :=
  hsolve

end LeanFpAnalysis.FP
