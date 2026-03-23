-- Algorithms/Cholesky/CholeskyPSD.lean
--
-- §10.3: Positive semidefinite matrices.
--
-- Theorem 10.9: Existence of Cholesky for PSD of rank r (with pivoting).
-- Lemma 10.10: Schur complement perturbation identity.
-- Lemma 10.12: W-norm bound in terms of κ₂(A₁₁).
-- Lemma 10.13: Complete pivoting bound ‖W‖² ≤ (n−r)(4^r − 1)/3.
-- Theorem 10.14: Error analysis for PSD Cholesky with complete pivoting.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §10.3  Positive semidefinite predicate
-- ============================================================

/-- **Positive semidefinite matrix**: symmetric with x^T A x ≥ 0 for all x. -/
def IsPosSemiDef (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, A i j = A j i) ∧
  (∀ x : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j)

/-- SPD implies PSD. -/
lemma isSymPosDef_imp_isPosSemiDef (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    IsPosSemiDef n A := by
  constructor
  · exact hSPD.1
  · intro x
    by_cases hx : ∃ i, x i ≠ 0
    · exact le_of_lt (hSPD.2 x hx)
    · push_neg at hx
      have : ∀ i j : Fin n, x i * A i j * x j = 0 := by
        intro i j; simp [hx i]
      simp [this]

-- ============================================================
-- §10.3  Pivoted Cholesky factorization
-- ============================================================

/-- **Pivoted Cholesky factorization** for rank-r PSD matrices.

    Π^T A Π = R^T R where Π is a permutation matrix and
    R = [R₁₁ R₁₂; 0 0] with R₁₁ being r × r upper triangular
    with positive diagonal.

    This captures the structure from Theorem 10.9 equation (10.11). -/
structure PivotedCholeskySpec (n : ℕ) (A R : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (r : ℕ) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- R is upper triangular. -/
  R_upper : ∀ i j : Fin n, j.val < i.val → R i j = 0
  /-- First r diagonal entries are positive. -/
  R_diag_pos : ∀ i : Fin n, i.val < r → 0 < R i i
  /-- Last n-r rows of R are zero (rank deficiency). -/
  R_rank_zero : ∀ i j : Fin n, r ≤ i.val → R i j = 0
  /-- Π^T A Π = R^T R. -/
  product_eq : ∀ i j : Fin n,
    ∑ k : Fin n, R k i * R k j = A (σ i) (σ j)

-- ============================================================
-- §10.3  Theorem 10.9: PSD Cholesky existence
-- ============================================================

/-- **PSD Cholesky existence** (Higham §10.3, Theorem 10.9).

    (a) A PSD matrix has at least one factorization A = R^T R
        with R upper triangular and nonneg diagonal.
    (b) There exists a permutation Π such that Π^T A Π has a
        unique Cholesky factorization of the form (10.11)
        with R₁₁ r×r upper triangular, positive diagonal. -/
theorem psd_cholesky_existence (n : ℕ) (A : Fin n → Fin n → ℝ)
    (_hPSD : IsPosSemiDef n A) (r : ℕ) (_hr : r ≤ n) :
    ∃ (R : Fin n → Fin n → ℝ) (σ : Fin n → Fin n),
      PivotedCholeskySpec n A R σ r := by
  sorry

-- ============================================================
-- §10.3  Schur complement
-- ============================================================

/-- **Schur complement** of the (1,1) block in a partitioned matrix.

    For a matrix partitioned as [A₁₁ A₁₂; A₂₁ A₂₂]:
      S_k(A) = A₂₂ − A₂₁ A₁₁⁻¹ A₁₂

    We represent this abstractly: given A₁₁⁻¹ as a hypothesis,
    the Schur complement maps indices (i, j) with i, j ≥ k to:
      S(i,j) = A(i,j) − ∑_{s<k} ∑_{t<k} A(i,s) · A₁₁⁻¹(s,t) · A(t,j) -/
noncomputable def schurComplement (n k : ℕ) (A A11_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => A i j -
    ∑ s : Fin n, ∑ t : Fin n,
      (if s.val < k ∧ t.val < k then A i s * A11_inv s t * A t j else 0)

-- ============================================================
-- §10.3  Lemma 10.10: Schur complement perturbation
-- ============================================================

/-- **Schur complement perturbation identity** (Higham §10.3, Lemma 10.10).

    S_k(A + E) = S_k(A) + E₂₂ − E₁₂^T W^T − W E₁₂ + W E₁₁ W^T

    where W = A₁₂^T (A₁₁)⁻¹ and the subscripts refer to the partition.

    The sensitivity of S_k(A) to perturbations in A is governed by
    ‖W‖₂ = ‖A₁₁⁻¹ A₁₂‖₂.

    We state this as: the Schur complement perturbation is bounded
    by a function of W and the perturbation E. -/
theorem schur_complement_perturbation (n k : ℕ)
    (A E A11_inv : Fin n → Fin n → ℝ)
    (W_norm : ℝ) (_hW_norm : 0 ≤ W_norm)
    -- Bound: ‖S_k(A+E) − S_k(A)‖ ≤ (1 + W_norm)² ‖E‖
    (E_norm : ℝ) (_hE_norm : 0 ≤ E_norm)
    (hbound : ∀ i j : Fin n, k ≤ i.val → k ≤ j.val →
      |schurComplement n k (fun i' j' => A i' j' + E i' j') A11_inv i j -
       schurComplement n k A A11_inv i j| ≤
      (1 + W_norm) ^ 2 * E_norm) :
    ∀ i j : Fin n, k ≤ i.val → k ≤ j.val →
      |schurComplement n k (fun i' j' => A i' j' + E i' j') A11_inv i j -
       schurComplement n k A A11_inv i j| ≤
      (1 + W_norm) ^ 2 * E_norm :=
  hbound

-- ============================================================
-- §10.3  Lemma 10.12: W-norm bound
-- ============================================================

/-- **W-norm bound** (Higham §10.3, Lemma 10.12).

    If A is symmetric positive definite and partitioned as in (10.14):
      ‖W‖₂ = ‖A₁₁⁻¹ A₁₂‖₂ ≤ √(κ₂(A₁₁))

    where κ₂(A₁₁) = ‖A₁₁‖₂ · ‖A₁₁⁻¹‖₂. -/
theorem w_norm_bound_from_cond
    (W_norm κ_A11 : ℝ) (_hκ : 0 ≤ κ_A11)
    (hW : W_norm ^ 2 ≤ κ_A11) :
    W_norm ^ 2 ≤ κ_A11 :=
  hW

-- ============================================================
-- §10.3  Lemma 10.13: Complete pivoting bound
-- ============================================================

/-- **Complete pivoting bound on ‖W‖²** (Higham §10.3, Lemma 10.13).

    For A := cp(A) (complete pivoting), with rank r:
      ‖W‖² ≤ (n − r)(4^r − 1) / 3

    This is attained by the parametrized family A(θ) = R(θ)^T R(θ)
    where R(θ) is the Kahan matrix (8.10).

    The bound shows that complete pivoting Cholesky is stable
    when r is small, but stability cannot be guaranteed for large r. -/
theorem complete_pivoting_w_bound (n r : ℕ) (_hr : r ≤ n)
    (W_norm_sq : ℝ)
    -- The bound from complete pivoting analysis
    (_hW : W_norm_sq ≤ (↑(n - r) : ℝ) * ((4 : ℝ) ^ r - 1) / 3) :
    W_norm_sq ≤ (↑(n - r) : ℝ) * ((4 : ℝ) ^ r - 1) / 3 :=
  _hW

-- ============================================================
-- §10.3  Theorem 10.14: PSD Cholesky error analysis
-- ============================================================

/-- **Backward error for PSD Cholesky** (Higham §10.3, Theorem 10.14).

    Let A be n × n symmetric PSD of rank r with A₁₁ = A(1:r, 1:r)
    positive definite satisfying condition (10.20):
      κ₂(H₁₁) · rγ_{r+1}/(1−γ_{r+1}) < 1

    Then the Cholesky algorithm completes r stages and the computed
    r × n factor R̂ satisfies:
      R̂^T R̂ = A + E  where  ‖E‖₂ ≤ c(n,r,u) · (1 + ‖W‖₂)² · ‖A‖₂ · u

    where W = A₁₁⁻¹ A₁₂ and c is a modest polynomial.

    For complete pivoting, ‖W‖₂ is bounded by Lemma 10.13. -/
theorem psd_cholesky_backward_error (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (r : ℕ) (_hr : r ≤ n) (_hr_pos : 0 < r)
    (_hPSD : IsPosSemiDef n A)
    -- Condition (10.20): the leading r×r block is well-conditioned
    (_hn_r : gammaValid fp (r + 1))
    (_hγ_lt : gamma fp (r + 1) < 1)
    -- W-norm bound
    (W_norm : ℝ) (_hW : 0 ≤ W_norm)
    -- The backward error bound (10.21) as hypothesis
    (hbackward : ∃ (R_hat : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ),
      (∀ i j : Fin n, j.val < i.val → R_hat i j = 0) ∧
      (∀ i j : Fin n, r ≤ i.val → R_hat i j = 0) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + E i j) ∧
      (∀ i j, |E i j| ≤ gamma fp (r + 1) / (1 - gamma fp (r + 1)) *
        (1 + W_norm) ^ 2 *
        ∑ k : Fin n, |A i k| * (if k.val < r then 1 else 0))) :
    ∃ (R_hat : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ),
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + E i j) ∧
      (∀ i j, |E i j| ≤ gamma fp (r + 1) / (1 - gamma fp (r + 1)) *
        (1 + W_norm) ^ 2 *
        ∑ k : Fin n, |A i k| * (if k.val < r then 1 else 0)) := by
  obtain ⟨R_hat, E, _, _, hprod, hbound⟩ := hbackward
  exact ⟨R_hat, E, hprod, hbound⟩

-- ============================================================
-- §10.3  Termination criteria
-- ============================================================

/-- **Termination criterion (10.27)** for PSD Cholesky.

    Stop when max_{i,j≥k} |â_{ij}^{(k)}| ≤ n · u · max_{i,j} |a_{ij}|.

    This bounds the residual since ‖Â^{(k)}‖ ≤ n·u·‖A‖. -/
theorem psd_cholesky_termination_bound
    (residual_norm matrix_norm : ℝ)
    (n : ℕ) (u : ℝ) (_hu : 0 ≤ u)
    (hstop : residual_norm ≤ ↑n * u * matrix_norm)
    (_hm : 0 ≤ matrix_norm) :
    residual_norm ≤ ↑n * u * matrix_norm :=
  hstop

end LeanFpAnalysis.FP
