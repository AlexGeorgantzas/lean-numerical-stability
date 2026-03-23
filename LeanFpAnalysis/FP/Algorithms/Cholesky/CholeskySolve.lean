-- Algorithms/Cholesky/CholeskySolve.lean
--
-- Theorem 10.4: Overall backward error for solving Ax = b via Cholesky.
--
-- Combining the Cholesky factorization backward error (Theorem 10.3)
-- with two triangular solves (R̂^T y = b, R̂x = y) gives:
--   (A + ΔA)x̂ = b  with  |ΔA| ≤ γ(3(n+1)) · |R̂^T||R̂|

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.TriangularSolve
import LeanFpAnalysis.FP.Algorithms.ForwardSub
import LeanFpAnalysis.FP.Algorithms.LU.LUSolve
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §10.1  Theorem 10.4: Cholesky solve backward error
-- ============================================================

/-- **Cholesky solve backward error** (Higham §10.1, Theorem 10.4).

    Computing x̂ via Cholesky factorization + triangular solves gives:
      (A + ΔA)x̂ = b  with  |ΔA| ≤ (3γ(n+1) + γ(n+1)²) · |R̂^T||R̂|

    The three error sources are:
    1. Factorization: R̂^T R̂ = A + ΔA₁ with |ΔA₁| ≤ γ(n+1)|R̂^T||R̂|
    2. Forward sub: (R̂^T + ΔR^T)ŷ = b with |ΔR^T| ≤ γ(n)|R̂^T|
    3. Back sub: (R̂ + ΔR)x̂ = ŷ with |ΔR| ≤ γ(n)|R̂|

    Since γ(n) ≤ γ(n+1), all three use ε = γ(n+1), giving
    (3γ(n+1) + γ(n+1)²) which absorbs to γ(3(n+1)).

    This is the exact analogue of Theorem 9.4 for LU. -/
theorem cholesky_solve_backward_error_expanded (fp : FPModel) (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError n A R_hat (gamma fp (n + 1)))
    (hn1 : gammaValid fp (n + 1)) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT b
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        (3 * gamma fp (n + 1) + gamma fp (n + 1) ^ 2) *
          ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let R_hatT := fun i j : Fin n => R_hat j i
  let y_hat := fl_forwardSub fp n R_hatT b
  let x_hat := fl_backSub fp n R_hat y_hat
  -- R̂^T is lower triangular
  have hRT_lower : ∀ i j : Fin n, i.val < j.val → R_hatT i j = 0 :=
    fun i j hij => hChol.R_upper j i hij
  -- R̂ is upper triangular
  have hR_upper : ∀ i j : Fin n, j.val < i.val → R_hat i j = 0 :=
    hChol.R_upper
  -- R̂^T has nonzero diagonal (same as R̂)
  have hRT_diag : ∀ i : Fin n, R_hatT i i ≠ 0 :=
    fun i => hR_diag i
  -- gammaValid fp n (for triangular solve bounds)
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hn1
  -- ε = γ(n+1) for the common bound
  let ε := gamma fp (n + 1)
  have hε : 0 ≤ ε := gamma_nonneg fp hn1
  -- Step 1: Factorization backward error
  obtain ⟨ΔA_fact, hΔA_fact_bound, hΔA_fact_eq⟩ :=
    cholesky_backward_error_perturbation n A R_hat ε hε hChol
  -- Step 2: Forward sub backward error on R̂^T
  obtain ⟨ΔL, hΔL_bound_n, hΔL_eq⟩ :=
    forwardSub_backward_error fp n R_hatT b hRT_diag hRT_lower hn
  -- Step 3: Back sub backward error on R̂
  obtain ⟨ΔU, hΔU_bound_n, hΔU_eq⟩ :=
    backSub_backward_error fp n R_hat y_hat hR_diag hR_upper hn
  -- Promote γ(n) bounds to γ(n+1) bounds
  have hγ_mono : gamma fp n ≤ gamma fp (n + 1) := gamma_mono fp (by omega) hn1
  have hΔL_bound : ∀ i j, |ΔL i j| ≤ ε * |R_hatT i j| := by
    intro i j
    calc |ΔL i j| ≤ gamma fp n * |R_hatT i j| := hΔL_bound_n i j
      _ ≤ ε * |R_hatT i j| := by
          apply mul_le_mul_of_nonneg_right hγ_mono (abs_nonneg _)
  have hΔU_bound : ∀ i j, |ΔU i j| ≤ ε * |R_hat i j| := by
    intro i j
    calc |ΔU i j| ≤ gamma fp n * |R_hat i j| := hΔU_bound_n i j
      _ ≤ ε * |R_hat i j| := by
          apply mul_le_mul_of_nonneg_right hγ_mono (abs_nonneg _)
  -- Apply the generic LU solve backward error theorem
  exact lu_solve_backward_error_bw n A R_hatT R_hat y_hat x_hat
    ε hε ΔA_fact hΔA_fact_bound hΔA_fact_eq b ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq

/-- **Cholesky solve backward error (absorbed form)** (Higham §10.1, Theorem 10.4).

    The absorbed form uses γ(3(n+1)) ≥ 3γ(n+1) + γ(n+1)²:
      (A + ΔA)x̂ = b  with  |ΔA| ≤ γ(3(n+1)) · |R̂^T||R̂| -/
theorem cholesky_solve_backward_error (fp : FPModel) (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError n A R_hat (gamma fp (n + 1)))
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * (n + 1))) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT b
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * (n + 1)) *
        ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let R_hatT := fun i j : Fin n => R_hat j i
  let y_hat := fl_forwardSub fp n R_hatT b
  let x_hat := fl_backSub fp n R_hat y_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_solve_backward_error_expanded fp n A R_hat b hR_diag hChol hn1
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have habsorb := three_gamma_plus_sq_le_gamma fp (n + 1) hn3
  have hS := absRT_R_product_nonneg n R_hat i j
  calc |ΔA i j|
      ≤ (3 * gamma fp (n + 1) + gamma fp (n + 1) ^ 2) *
          ∑ k : Fin n, |R_hat k i| * |R_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * (n + 1)) *
          ∑ k : Fin n, |R_hat k i| * |R_hat k j| := by
        apply mul_le_mul_of_nonneg_right habsorb hS

/-- **Cholesky solve SPD backward stability** (Higham §10.1, combining Theorem 10.4 + growth = 1).

    For SPD with nonneg R̂ and γ(3(n+1)) < 1:
      (A + ΔA)x̂ = b  with  |ΔA| ≤ γ(3(n+1))/(1−γ(n+1)) · |A| -/
theorem cholesky_solve_spd_backward_stable (fp : FPModel) (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError n A R_hat (gamma fp (n + 1)))
    (hn1 : gammaValid fp (n + 1))
    (hn1_lt : gamma fp (n + 1) < 1)
    (hn3 : gammaValid fp (3 * (n + 1)))
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT b
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * (n + 1)) / (1 - gamma fp (n + 1)) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let R_hatT := fun i j : Fin n => R_hat j i
  let y_hat := fl_forwardSub fp n R_hatT b
  let x_hat := fl_backSub fp n R_hat y_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_solve_backward_error fp n A R_hat b hR_diag hChol hn1 hn3
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hε_nn : (0 : ℝ) ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  have hgrowth := cholesky_spd_optimal_growth n A R_hat
    (gamma fp (n + 1)) hn1_lt hε_nn hChol hR_nn i j
  have hγ3_nn : 0 ≤ gamma fp (3 * (n + 1)) := gamma_nonneg fp hn3
  calc |ΔA i j|
      ≤ gamma fp (3 * (n + 1)) *
          ∑ k : Fin n, |R_hat k i| * |R_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * (n + 1)) * (|A i j| / (1 - gamma fp (n + 1))) := by
        apply mul_le_mul_of_nonneg_left hgrowth hγ3_nn
    _ = gamma fp (3 * (n + 1)) / (1 - gamma fp (n + 1)) * |A i j| := by ring

end LeanFpAnalysis.FP
