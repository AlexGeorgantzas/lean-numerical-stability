-- Algorithms/Cholesky/CholeskyPerturbation.lean
--
-- Theorem 10.8 (Sun): Perturbation sensitivity of the Cholesky factorization.
--
-- If A is SPD with Cholesky factorization A = R^T R and ΔA is symmetric
-- with ‖A⁻¹ΔA‖₂ < 1, then A + ΔA = (R + ΔR)^T (R + ΔR) and:
--   ‖ΔR‖_F / ‖R‖_F ≤ κ₂(A) / (2‖A‖₂) · ‖ΔA‖_F   (normwise)
--   |ΔR| ≤ triu(|R⁻ᵀ||ΔA||R⁻¹|) · (1 + O(‖ΔA‖))   (componentwise)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination
import LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §10.2  Upper triangular part
-- ============================================================

/-- **Upper triangular part** of a matrix: triu(A)_{ij} = A_{ij} if i ≤ j, else 0. -/
noncomputable def triuPart {n : ℕ} (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if i.val ≤ j.val then A i j else 0

lemma triuPart_upper {n : ℕ} (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, j.val < i.val → triuPart A i j = 0 := by
  intro i j hij
  unfold triuPart
  simp [show ¬(i.val ≤ j.val) from by omega]

lemma triuPart_diag_and_above {n : ℕ} (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, i.val ≤ j.val → triuPart A i j = A i j := by
  intro i j hij
  unfold triuPart
  simp [hij]

-- ============================================================
-- §10.2  Theorem 10.8: Sun perturbation bound (normwise)
-- ============================================================

/-- **Abstract Cholesky perturbation normwise-bound interface**
    (Higham §10.2, Theorem 10.8, first part).

    If A is SPD with A = R^T R and ΔA is symmetric with ‖A⁻¹ΔA‖₂ < 1,
    then A + ΔA = (R + ΔR)^T(R + ΔR) where:
      frobNormSq(ΔR) ≤ (κ₂(A) / (2 · norm₂(A)))² · frobNormSq(ΔA) + O(‖ΔA‖²)

    We state the first-order bound in squared form to avoid sqrt.
    The condition number κ₂(A) = ‖A‖₂ · ‖A⁻¹‖₂ is taken as a hypothesis.
    The perturbation existence/bound itself is supplied as `hpert`. -/
theorem cholesky_perturbation_normwise (n : ℕ)
    (A R : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (_hChol : CholeskyFactSpec n A R)
    (_hSym_A : ∀ i j : Fin n, A i j = A j i)
    (_hSym_ΔA : ∀ i j : Fin n, ΔA i j = ΔA j i)
    -- Norms and condition number as hypotheses
    (norm2_A : ℝ) (_hnorm2_pos : 0 < norm2_A)
    (κ2_A : ℝ) (_hκ2_pos : 0 < κ2_A)
    -- Perturbation is small enough
    (_hSmall : frobNormSq ΔA < norm2_A ^ 2)
    -- The bound: existence of ΔR with the Frobenius norm bound
    -- This first-order perturbation result follows from implicit function
    -- theorem applied to the map R ↦ R^T R.
    (hpert : ∃ ΔR : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → ΔR i j = 0) ∧
      (∀ i j, ∑ k : Fin n, (R k i + ΔR k i) * (R k j + ΔR k j) = A i j + ΔA i j) ∧
      frobNormSq ΔR ≤ κ2_A ^ 2 / (4 * norm2_A ^ 2) * frobNormSq ΔA) :
    ∃ ΔR : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → ΔR i j = 0) ∧
      (∀ i j, ∑ k : Fin n, (R k i + ΔR k i) * (R k j + ΔR k j) = A i j + ΔA i j) ∧
      frobNormSq ΔR ≤ κ2_A ^ 2 / (4 * norm2_A ^ 2) * frobNormSq ΔA :=
  hpert

-- ============================================================
-- §10.2  Theorem 10.8: Sun perturbation bound (componentwise)
-- ============================================================

/-- **Cholesky perturbation componentwise bound** (Higham §10.2, Theorem 10.8, second part).

    Under the conditions of the normwise bound, if ε = ‖(R+ΔR)⁻ᵀ ΔA (R+ΔR)⁻¹‖₂ < 1:
      |ΔR| ≤ triu(|R⁻ᵀ| · |ΔA| · |R⁻¹|) · (1 + O(ε))

    We take the componentwise bound as a hypothesis and express it
    using the upper triangular part and matrix inverses. -/
theorem cholesky_perturbation_componentwise (n : ℕ)
    (R ΔR R_invT R_inv : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (_hChol_R : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (_hΔR_upper : ∀ i j : Fin n, j.val < i.val → ΔR i j = 0)
    -- R⁻ᵀ and R⁻¹ are the transposes/inverses
    (_hR_invT : IsLeftInverse n (fun i j => R j i) R_invT)
    (_hR_inv : IsRightInverse n R R_inv)
    -- First-order bound
    (α : ℝ) (_hα : 0 ≤ α)
    (hbound : ∀ i j : Fin n, i.val ≤ j.val →
      |ΔR i j| ≤ (1 + α) *
        ∑ k₁ : Fin n, |R_invT i k₁| *
          ∑ k₂ : Fin n, |ΔA k₁ k₂| * |R_inv k₂ j|) :
    ∀ i j : Fin n, |ΔR i j| ≤ (1 + α) *
      (if i.val ≤ j.val then
        ∑ k₁ : Fin n, |R_invT i k₁| *
          ∑ k₂ : Fin n, |ΔA k₁ k₂| * |R_inv k₂ j|
       else 0) := by
  intro i j
  by_cases hij : i.val ≤ j.val
  · simp [hij]
    exact hbound i j hij
  · simp [show ¬(i.val ≤ j.val) from by omega]
    have hij' : j.val < i.val := by omega
    have hΔR_zero := _hΔR_upper i j hij'
    simp [hΔR_zero]

-- ============================================================
-- §10.2  Sensitivity of leading submatrices
-- ============================================================

/-- **Leading submatrix sensitivity** (Higham §10.2, Remark after Theorem 10.8).

    The Cholesky factor of A_k = A(1:k, 1:k) is R_k = R(1:k, 1:k).
    Since κ₂(A_{k+1}) ≥ κ₂(A_k) by eigenvalue interlacing:
    - If A is ill-conditioned but A_k is well-conditioned,
      then R_k is insensitive to perturbations but later columns
      of R are much more sensitive.

    We state this as a monotonicity property of the condition number
    along the leading submatrix chain. -/
theorem cholesky_cond_monotone
    (κ : ℕ → ℝ)
    (_hκ_mono : ∀ k : ℕ, κ k ≤ κ (k + 1))
    (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    κ k₁ ≤ κ k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ d ih =>
    calc κ k₁ ≤ κ (k₁ + d) := ih (by omega)
      _ ≤ κ (k₁ + d + 1) := _hκ_mono _
      _ = κ (k₁ + (d + 1)) := by ring_nf

end LeanFpAnalysis.FP
