-- Exact algorithm specifications for Higham, 2nd ed., Chapter 20.

import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Algorithms.LinearSystems.LeastSquares.Refinement
import NumStability.Analysis.Perturbation.LeastSquares.Basic

namespace NumStability

open scoped BigOperators

/-! ## Section 20.5: direct least-squares iterative refinement -/



















/-! ## Section 20.5: augmented-system iterative refinement -/

















/-! ## Section 20.6: seminormal and corrected seminormal equations -/



/-- An exact tall QR relation `A = Q[R;0]` supplies the seminormal identity
`A^T A = R^T R`. -/
theorem higham20_qrFactorization_rectLSGram_eq_seminormalGram {n k : ℕ}
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A : Fin (n + k) → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (hQ : IsOrthogonal (n + k) Q)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R)) :
    ∀ j s : Fin n,
      rectLSGram A j s = ∑ i : Fin n, R i j * R i s := by
  intro j s
  have hpreserve :=
    rectLSGram_matMulRectLeft_orthogonal Q (lsQRTallBlock R) hQ
  calc
    rectLSGram A j s =
        rectLSGram (matMulRectLeft Q (lsQRTallBlock R)) j s := by rw [hA]
    _ = rectLSGram (lsQRTallBlock R) j s :=
      congrFun (congrFun hpreserve j) s
    _ = ∑ i : Fin n, R i j * R i s := by
      unfold rectLSGram lsQRTallBlock
      rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right]







/-- Source-facing SNE endpoint using the exact QR factors from which the
seminormal equations are derived. -/
theorem Higham20SeminormalEquationsSolve.isLeastSquaresMinimizer_of_qr
    {n k : ℕ}
    {Q : Fin (n + k) → Fin (n + k) → ℝ}
    {A : Fin (n + k) → Fin n → ℝ} {b : Fin (n + k) → ℝ}
    {R : Fin n → Fin n → ℝ} {z x : Fin n → ℝ}
    (h : Higham20SeminormalEquationsSolve A b R z x)
    (hQ : IsOrthogonal (n + k) Q)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R)) :
    IsLeastSquaresMinimizer A b x :=
  h.isLeastSquaresMinimizer
    (higham20_qrFactorization_rectLSGram_eq_seminormalGram Q A R hQ hA)







/-- Source-facing CSNE endpoint using the exact QR factors that determine
`R`. -/
theorem Higham20CorrectedSeminormalEquationsStep.updated_isLeastSquaresMinimizer_of_qr
    {n k : ℕ}
    {Q : Fin (n + k) → Fin (n + k) → ℝ}
    {A : Fin (n + k) → Fin n → ℝ} {b : Fin (n + k) → ℝ}
    {R : Fin n → Fin n → ℝ} {z x : Fin n → ℝ}
    {r : Fin (n + k) → ℝ} {t w y : Fin n → ℝ}
    (h : Higham20CorrectedSeminormalEquationsStep A b R z x r t w y)
    (hQ : IsOrthogonal (n + k) Q)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R)) :
    IsLeastSquaresMinimizer A b y :=
  h.updated_isLeastSquaresMinimizer
    (higham20_qrFactorization_rectLSGram_eq_seminormalGram Q A R hQ hA)

end NumStability
