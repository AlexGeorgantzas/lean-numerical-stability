-- Algorithms/LeastSquares/LSQRSolve.lean
--
-- Backward error analysis of QR-based least squares solve (Higham §19.2).
--
-- Theorem 19.3: The computed LS solution x̂ via Householder QR satisfies
--   x̂ is the exact LS solution to min‖(b+Δb)−(A+ΔA)x‖₂
--   where ‖ΔA‖_F ≤ nγ_{cm}‖A‖_F and ‖Δb‖₂ ≤ nγ_{cm}‖b‖₂.
--
-- Since the rectangular QR factorization is not representable in the
-- library's square-matrix framework, we axiomatize the backward stability
-- via a structure and derive forward error consequences using the
-- existing perturbation theory infrastructure.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Analysis.PerturbationTheory

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §19.2  Theorem 19.3: QR LS backward stability
-- ============================================================

/-- **Theorem 19.3** (Higham): Householder QR least squares backward stability.

    The computed LS solution x̂ via Householder QR is the exact LS
    minimizer of min_x ‖(b + Δb) − (A + ΔA)x‖₂ where
    ‖ΔA‖_F ≤ c · ‖A‖_F and ‖Δb‖₂ ≤ c · ‖b‖₂ with c = nγ̃_{cm}.

    Since the rectangular A ∈ ℝ^{m×n} is not representable in the
    library's square-matrix framework, we capture the consequence
    for the n×n Gram system: the perturbed normal equations
    (A+ΔA)ᵀ(A+ΔA)x̂ = (A+ΔA)ᵀ(b+Δb) hold, which projects to
    a perturbation of the Gram system AᵀAx = Aᵀb.

    We axiomatize this as a structure, paralleling the library's
    treatment of `HouseholderQRBackwardError` and `QRSolveBackwardError`.

    The proof is described by Higham as "a straightforward
    generalization of the proof of Theorem 18.5." -/
structure LSQRSolveBackwardError (n : ℕ)
    (ATA : Fin n → Fin n → ℝ) (ATb x_hat : Fin n → ℝ)
    (c_G c_g : ℝ) : Prop where
  /-- There exist perturbations ΔG, Δg to the Gram system such that
      (AᵀA + ΔG)x̂ = Aᵀb + Δg with bounded perturbations. -/
  result : ∃ (ΔG : Fin n → Fin n → ℝ) (Δg : Fin n → ℝ),
    (∀ i, matMulVec n (fun a b => ATA a b + ΔG a b) x_hat i = ATb i + Δg i) ∧
    frobNorm ΔG ≤ c_G ∧
    (∀ i, |Δg i| ≤ c_g)

-- ============================================================
-- §19.2  Forward error from QR LS backward stability
-- ============================================================

/-- **Forward error bound for QR-based LS solve**.

    From the backward error (Theorem 19.3), the forward error satisfies
    |x̂ − x| ≤ |(AᵀA)⁻¹| · (|ΔG| · |x̂| + |Δg|)

    Since QR factorization avoids forming AᵀA explicitly, the effective
    conditioning is κ₂(A) (not κ₂(A)²) when the residual is small.
    This is the key advantage of QR over the normal equations method.

    The proof follows the same pattern as `ls_normal_equations_forward_error`
    in LSNormalEquations.lean: extract perturbations from the structure,
    form the residual equation, and apply the inverse bound. -/
theorem ls_qr_forward_error (n : ℕ)
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n ATA ATA_inv)
    (ATb x x_hat : Fin n → ℝ)
    (hExact : ∀ i, matMulVec n ATA x i = ATb i)
    (ΔG : Fin n → Fin n → ℝ) (Δg : Fin n → ℝ)
    (hPerturbed : ∀ i, matMulVec n (fun a b => ATA a b + ΔG a b) x_hat i =
      ATb i + Δg i) :
    ∀ i : Fin n, |x_hat i - x i| ≤
      ∑ j : Fin n, |ATA_inv i j| *
        (∑ k : Fin n, |ΔG j k| * |x_hat k| + |Δg j|) := by
  -- This is a direct application of Theorem 7.2 (normwise_perturbation_bound)
  -- with A := AᵀA, ΔA := ΔG, Δb := Δg.
  have hExact' : ∀ i, ∑ j, ATA i j * x j = ATb i := by
    intro i; exact hExact i
  have hPerturbed' : ∀ i, ∑ j, (ATA i j + ΔG i j) * x_hat j = ATb i + Δg i := by
    intro i; exact hPerturbed i
  intro i
  rw [abs_sub_comm]
  exact normwise_perturbation_bound n ATA ATA_inv x x_hat ATb ΔG Δg
    hInv.1 hExact' hPerturbed' i

-- ============================================================
-- §19.2  QR vs Normal Equations comparison
-- ============================================================

/-- **QR vs Normal Equations: normwise forward error comparison**.

    For the Gram system AᵀAx = Aᵀb, the condition number is
    κ(AᵀA) = κ₂(A)². Hence:
    - Normal equations: forward error ≲ κ₂(A)² · u  (always)
    - QR factorization: forward error ≲ κ₂(A) · u   (when residual small)

    The QR method achieves the lower bound because it works with R
    (condition number κ₂(A)) rather than AᵀA (condition number κ₂(A)²).

    We formalize a normwise version: if |ΔG_{ij}| ≤ ε_G uniformly
    and |Δg_i| ≤ ε_g uniformly, then the forward error is bounded
    by |(AᵀA)⁻¹| · (ε_G · ∑|x̂| + ε_g) componentwise. -/
theorem gram_forward_error_normwise (n : ℕ)
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n ATA ATA_inv)
    (ATb x x_hat : Fin n → ℝ)
    (hExact : ∀ i, matMulVec n ATA x i = ATb i)
    (ΔG : Fin n → Fin n → ℝ) (Δg : Fin n → ℝ)
    (hPerturbed : ∀ i, matMulVec n (fun a b => ATA a b + ΔG a b) x_hat i =
      ATb i + Δg i)
    (hΔG_bound : ∀ i j, |ΔG i j| ≤ ε_G)
    (hΔg_bound : ∀ i, |Δg i| ≤ ε_g)
    (hε_G : 0 ≤ ε_G) (hε_g : 0 ≤ ε_g) :
    ∀ i : Fin n, |x_hat i - x i| ≤
      ∑ j : Fin n, |ATA_inv i j| *
        (ε_G * ∑ k : Fin n, |x_hat k| + ε_g) := by
  have hFwd := ls_qr_forward_error n ATA ATA_inv hInv ATb x x_hat hExact ΔG Δg hPerturbed
  intro i
  calc |x_hat i - x i|
      ≤ ∑ j : Fin n, |ATA_inv i j| *
          (∑ k : Fin n, |ΔG j k| * |x_hat k| + |Δg j|) := hFwd i
    _ ≤ ∑ j : Fin n, |ATA_inv i j| *
          (ε_G * ∑ k : Fin n, |x_hat k| + ε_g) := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hSum : ∑ k : Fin n, |ΔG j k| * |x_hat k| ≤
            ε_G * ∑ k : Fin n, |x_hat k| := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_right (hΔG_bound j k) (abs_nonneg _)
        linarith [hΔg_bound j]

end LeanFpAnalysis.FP
