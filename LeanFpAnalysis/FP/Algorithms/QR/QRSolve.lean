-- Algorithms/QR/QRSolve.lean
--
-- Backward error analysis for QR-based linear system solve (Higham §18.3).
--
-- Theorem 18.5: Solving Ax = b via Householder QR gives
--   (A + ΔA)x̂ = b + Δb with componentwise/normwise bounds.
--
-- The solve proceeds in three stages:
--   1. Compute QR: A + ΔA₁ = Q R̂  (Theorem 18.4)
--   2. Form Qᵀb:  ĉ = Qᵀ(b + Δb)  (Lemma 18.3 applied to b)
--   3. Solve R̂x̂ = ĉ: (R̂ + ΔR)x̂ = ĉ  (backward substitution)
--
-- Combining these yields the overall backward error.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §18.3  Theorem 18.5: QR-based solve backward error
-- ============================================================

/-- **Theorem 18.5**: QR-based solve backward error (normwise).

    Given a system Ax = b solved via Householder QR factorization:
    1. Factor A + ΔA₁ = Q·R̂  (Theorem 18.4)
    2. Compute ĉ = Qᵀ(b + Δb)  (Lemma 18.3 on b as a single column)
    3. Solve (R̂ + ΔR)x̂ = ĉ  (back substitution, Theorem 8.5)

    The combined backward error is (A + ΔA)x̂ = b + Δb where
    the bounds on ΔA, Δb depend on the per-step error constants.

    We axiomatize this structure since the detailed proof requires
    composing three backward error results with careful tracking
    of how perturbations interact through the factorization stages. -/
structure QRSolveBackwardError (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (c_A c_b : ℝ) : Prop where
  /-- There exist perturbations ΔA, Δb such that (A+ΔA)x̂ = b+Δb
      with ‖ΔA‖_F ≤ c_A and ‖Δb‖ ≤ c_b (normwise). -/
  result : ∃ (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
    (∀ i, matMulVec n (fun a b => A a b + ΔA a b) x_hat i = b i + Δb i) ∧
    frobNorm ΔA ≤ c_A ∧
    (∀ i, |Δb i| ≤ c_b)

/-- **Theorem 18.5 composition**: QR solve backward error from components.

    If we have:
    1. QR backward error: A + ΔA₁ = Q·R̂ with ‖ΔA₁‖_F ≤ c₁
    2. Back-substitution backward error: (R̂ + ΔR)x̂ = ĉ with ‖ΔR‖_F ≤ c₂
    3. Qᵀ application backward error on b: ĉ = Qᵀ(b + Δb) with ‖Δb‖ ≤ c₃

    Then (A + ΔA)x̂ = b + Δb where ΔA = ΔA₁ + Q·ΔR, so
    ‖ΔA‖_F ≤ c₁ + c₂ (using orthogonal invariance ‖Q·ΔR‖_F = ‖ΔR‖_F).

    The detailed composition is axiomatized since it requires careful
    algebra to combine the three stages, but the key insight is that
    orthogonal transformations preserve backward error magnitudes. -/
theorem qr_solve_backward_from_components (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (R_hat : Fin n → Fin n → ℝ)
    (ΔA₁ : Fin n → Fin n → ℝ)
    (hQ : IsOrthogonal n Q)
    (hQR : ∀ i j, matMul n Q R_hat i j = A i j + ΔA₁ i j)
    (hΔA₁ : frobNorm ΔA₁ ≤ c₁)
    (x_hat : Fin n → ℝ) (c_hat : Fin n → ℝ)
    (ΔR : Fin n → Fin n → ℝ)
    (hSolve : ∀ i, matMulVec n (fun a b => R_hat a b + ΔR a b) x_hat i = c_hat i)
    (hΔR : frobNorm ΔR ≤ c₂)
    (b : Fin n → ℝ) (Δb : Fin n → ℝ)
    (hQb : ∀ i, c_hat i = matMulVec n (matTranspose Q) (fun k => b k + Δb k) i) :
    ∀ i, matMulVec n (fun a b => A a b + ΔA₁ a b +
      matMul n Q ΔR a b) x_hat i = b i + Δb i := by
  intro i
  -- (A + ΔA₁ + Q·ΔR) x̂ = (Q·R̂ + Q·ΔR) x̂ = Q·(R̂ + ΔR)·x̂ = Q·ĉ
  -- Q·ĉ = Q·Qᵀ(b+Δb) = b + Δb
  -- We prove this pointwise.
  unfold matMulVec
  -- LHS: ∑ j, (A i j + ΔA₁ i j + (Q·ΔR) i j) * x̂_j
  -- We split: ∑ (A + ΔA₁) x̂ + ∑ (Q·ΔR) x̂
  -- = ∑ (Q·R̂) x̂ + ∑ (Q·ΔR) x̂  (by hQR)
  -- = ∑ Q·(R̂ + ΔR) x̂  (distributing Q)
  -- = Q · ((R̂+ΔR)x̂)  (matrix-vector)
  -- = Q · ĉ  (by hSolve)
  -- = Q · Qᵀ(b+Δb)  (by hQb)
  -- = (b + Δb)  (by QQᵀ = I)
  -- We unfold and compute directly.
  have hQRpt : ∀ j, A i j + ΔA₁ i j = matMul n Q R_hat i j := by
    intro j; exact (hQR i j).symm
  simp_rw [show ∀ j : Fin n, (A i j + ΔA₁ i j + matMul n Q ΔR i j) * x_hat j =
    (matMul n Q R_hat i j + matMul n Q ΔR i j) * x_hat j from by
      intro j; rw [hQRpt j]]
  -- Factor: Q·R̂ + Q·ΔR = Q·(R̂ + ΔR)
  simp only [matMul]
  simp_rw [show ∀ j : Fin n,
      ((∑ k, Q i k * R_hat k j) + ∑ k, Q i k * ΔR k j) * x_hat j =
      (∑ k, Q i k * (R_hat k j + ΔR k j)) * x_hat j from by
    intro j; congr 1; rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring]
  -- Now: ∑ j, (∑ k, Q i k * (R̂+ΔR) k j) * x̂_j
  -- = ∑ k, Q i k * ∑ j, (R̂+ΔR) k j * x̂_j
  -- = ∑ k, Q i k * ((R̂+ΔR)·x̂)_k = ∑ k, Q i k * ĉ_k
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [show ∀ k j : Fin n,
      Q i k * (R_hat k j + ΔR k j) * x_hat j =
      Q i k * ((R_hat k j + ΔR k j) * x_hat j) from by
    intros; ring]
  simp_rw [← Finset.mul_sum]
  -- ∑ k, Q i k * ∑ j, (R̂+ΔR)_kj * x̂_j = ∑ k, Q i k * ĉ_k
  have hRx : ∀ k : Fin n,
      ∑ j : Fin n, (R_hat k j + ΔR k j) * x_hat j = c_hat k := by
    intro k; exact hSolve k
  simp_rw [hRx]
  -- ∑ k, Q i k * ĉ_k = ∑ k, Q i k * (Qᵀ(b+Δb))_k
  simp_rw [hQb]
  -- ∑ k, Q i k * ∑ l, Qᵀ k l * (b l + Δb l) = b i + Δb i
  unfold matMulVec matTranspose
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [show ∀ l k : Fin n,
      Q i k * (Q l k * (b l + Δb l)) = Q i k * Q l k * (b l + Δb l) from by
    intros; ring]
  simp_rw [← Finset.sum_mul, IsOrthogonal.row_orthonormal hQ]
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- **Frobenius norm of combined perturbation** for QR solve.

    If ‖ΔA₁‖_F ≤ c₁ and ‖ΔR‖_F ≤ c₂, then
    ‖ΔA₁ + Q·ΔR‖_F ≤ c₁ + c₂
    since ‖Q·ΔR‖_F = ‖ΔR‖_F by orthogonal invariance. -/
theorem qr_solve_perturbation_bound (n : ℕ)
    (Q : Fin n → Fin n → ℝ) (ΔA₁ ΔR : Fin n → Fin n → ℝ)
    (hQ : IsOrthogonal n Q)
    (hΔA₁ : frobNorm ΔA₁ ≤ c₁)
    (hΔR : frobNorm ΔR ≤ c₂)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    frobNorm (fun a b => ΔA₁ a b + matMul n Q ΔR a b) ≤ c₁ + c₂ := by
  calc frobNorm (fun a b => ΔA₁ a b + matMul n Q ΔR a b)
      ≤ frobNorm ΔA₁ +
          frobNorm (matMul n Q ΔR) :=
            frobNorm_add_le ΔA₁ (matMul n Q ΔR)
    _ = frobNorm ΔA₁ +
          frobNorm ΔR := by
        rw [frobNorm_orthogonal_left Q ΔR hQ]
    _ ≤ c₁ + c₂ := by linarith

end LeanFpAnalysis.FP
