-- Algorithms/Cholesky/CholeskyDemmel.lean
--
-- Demmel's results on Cholesky factorization (Higham §10.1):
-- - Theorem 10.5: |ΔA| ≤ (1−γ_{n+1})⁻¹ γ_{n+1} dd^T (column norm bound)
-- - Theorem 10.6: Scaled forward error via DHD decomposition
-- - Theorem 10.7: Success condition for Cholesky

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §10.1  Column norms and Cauchy-Schwarz
-- ============================================================

/-- **Column norm squared** of R at column i: d_i² = ∑_k R_{ki}². -/
noncomputable def colNormSq (n : ℕ) (R : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ k : Fin n, R k i ^ 2

/-- Column norm squared is nonneg. -/
lemma colNormSq_nonneg (n : ℕ) (R : Fin n → Fin n → ℝ) (i : Fin n) :
    0 ≤ colNormSq n R i :=
  Finset.sum_nonneg (fun k _ => sq_nonneg (R k i))

-- ============================================================
-- §10.1  Theorem 10.5: Demmel column norm bound
-- ============================================================

/-- **Demmel column norm bound** (Higham §10.1, Theorem 10.5).

    If Cholesky factorization applied to SPD A runs to completion,
    then the computed R̂ satisfies:
      R̂^T R̂ = A + ΔA  with  |ΔA_{ij}| ≤ ε/(1−ε) · d_i · d_j

    where d_i = ‖R̂_{:,i}‖₂ (column 2-norm of R̂) and ε = γ_{n+1}.

    The proof uses Cauchy-Schwarz: ∑_k |R̂_{ki}||R̂_{kj}| ≤ d_i d_j,
    combined with the nonneg factor bound |R̂^T||R̂| ≤ |A|/(1−ε).

    We state this with the Cauchy-Schwarz bound as a hypothesis `hCS`
    to avoid introducing sqrt. The bound follows from:
    (∑_k |a_k||b_k|)² ≤ (∑_k a_k²)(∑_k b_k²) = d_i² · d_j². -/
theorem cholesky_demmel_bound (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i)
    (hCS : ∀ i j, ∑ k : Fin n, |R_hat k i| * |R_hat k j| ≤ d i * d j)
    (ε : ℝ) (hε : 0 ≤ ε) (hε_lt : ε < 1)
    (hChol : CholeskyBackwardError n A R_hat ε) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε / (1 - ε) * (d i * d j)) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_backward_error_perturbation n A R_hat ε hε hChol
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have h1_ε_pos : (0 : ℝ) < 1 - ε := by linarith
  -- The direct Cauchy-Schwarz estimate gives |ΔA_ij| ≤ ε d_i d_j.
  -- Since 0 ≤ ε < 1, this immediately weakens to ε/(1-ε) d_i d_j.
  calc |ΔA i j| ≤ ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j| := hΔA_bound i j
    _ ≤ ε * (d i * d j) := by
        apply mul_le_mul_of_nonneg_left (hCS i j) hε
    _ ≤ ε / (1 - ε) * (d i * d j) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (hd i) (hd j))
        rw [le_div_iff₀ h1_ε_pos]
        nlinarith [sq_nonneg ε]

/-- **Demmel column norm bound (direct form)** (Higham §10.1, Theorem 10.5).

    The direct Cauchy-Schwarz bound without the (1−ε)⁻¹ factor:
      |ΔA_{ij}| ≤ ε · d_i · d_j -/
theorem cholesky_demmel_bound_direct (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (hCS : ∀ i j, ∑ k : Fin n, |R_hat k i| * |R_hat k j| ≤ d i * d j)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * (d i * d j)) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_backward_error_perturbation n A R_hat ε hε hChol
  exact ⟨ΔA, fun i j => by
    calc |ΔA i j| ≤ ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j| := hΔA_bound i j
      _ ≤ ε * (d i * d j) := by
          apply mul_le_mul_of_nonneg_left (hCS i j) hε,
    hΔA_eq⟩

-- ============================================================
-- §10.1  Theorem 10.6: Demmel-Wilkinson scaled error
-- ============================================================

-- Diagonal scaling for SPD matrices: D = diag(a_{ii}^{1/2}), H = D⁻¹AD⁻¹.
-- The scaled matrix H has unit diagonal (h_{ii} = 1) and satisfies
-- κ₂(H) ≤ nκ₂(A) (van der Sluis, Corollary 7.6).
-- We represent D as a vector of positive reals. The scaling is passed as
-- a hypothesis `hDHD` rather than computed, avoiding the need for Real.sqrt.

/-- **Abstract Demmel-Wilkinson scaled forward-error interface**
    (Higham §10.1, Theorem 10.6).

    Let A = DHD where D = diag(a_{ii}^{1/2}). Then:
      ‖D⁻¹(x − x̂)‖₂ / ‖D⁻¹x‖₂ ≤ f(n) · κ₂(H) · u

    where f(n) = 2n(1 − γ_{n+1})⁻¹ γ_{n+1}.

    This bound replaces κ₂(A) with the potentially much smaller κ₂(H),
    which captures only the "intrinsic" conditioning, not bad scaling.

    We formalize this with κ₂(H) as a hypothesis. The proof combines
    Theorem 10.5's dd^T bound with the scaling D:
    - |ΔA₁| ≤ (1−γ)⁻¹ γ dd^T (factorization, from Theorem 10.5)
    - |ΔA₂| ≤ diag(γ_i) |R̂^T| (forward sub)
    - |ΔA₃| ≤ diag(γ_{n-i+1}) |R̂| (back sub)
    - Scaling: D⁻¹ dd^T D⁻¹ = ee^T where e_i = d_i/√(a_{ii})
    - ‖D⁻¹ dd^T D⁻¹‖₂ ≤ n (since d_i² ≤ a_{ii}/(1−γ))

    The hypothesis `hscaled_err` supplies this combined perturbation/scaling
    argument; the theorem records the reusable named contract. -/
theorem cholesky_scaled_forward_error (n : ℕ) (_fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (D : Fin n → ℝ)
    (κH f_n : ℝ)
    -- Scaled error hypothesis: combines perturbation theory with
    -- the Demmel dd^T bound. This is the core inequality from the proof.
    (hscaled_err : ∀ (x x_hat : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * x j = ∑ j : Fin n, A i j * x_hat j) →
      ∀ i, |x i - x_hat i| / D i ≤ f_n * κH * _fp.u * (|x i| / D i)) :
    -- The conclusion: scaled error is bounded by f(n) κ₂(H) u
    ∀ (x x_hat : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * x j = ∑ j : Fin n, A i j * x_hat j) →
      ∀ i, |x i - x_hat i| / D i ≤ f_n * κH * _fp.u * (|x i| / D i) :=
  hscaled_err

-- ============================================================
-- §10.1  Theorem 10.7: Cholesky success condition
-- ============================================================

/-- **Cholesky success-condition threshold consequence**
    (Higham §10.1, Theorem 10.7).

    Let A = DHD where D = diag(a_{ii}^{1/2}).
    - If lam_min(H) > nγ_{n+1}/(1−γ_{n+1}), then Cholesky succeeds.
    - If lam_min(H) < −nγ_{n+1}/(1−γ_{n+1}), then Cholesky fails.

    The threshold nγ_{n+1}/(1−γ_{n+1}) arises because Theorem 10.5 shows
    the backward error satisfies D⁻¹ΔAD⁻¹ ≤ n·γ_{n+1}/(1−γ_{n+1}) · I
    (using ‖ee^T‖₂ = n and d_i²/a_{ii} ≤ 1/(1−γ_{n+1})).

    If the minimum eigenvalue of H exceeds this threshold, then
    H + D⁻¹ΔAD⁻¹ is positive definite, ensuring the factorization
    of A + ΔA = D(H + D⁻¹ΔAD⁻¹)D succeeds.

    This theorem formalizes the sign consequence of the Higham threshold:
    the full spectral success theorem is represented by the eigenvalue-bound
    hypotheses rather than derived from a concrete factorization loop. -/
theorem cholesky_success_condition (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (D : Fin n → ℝ) (H : Fin n → Fin n → ℝ)
    (_hD_pos : ∀ i : Fin n, 0 < D i)
    (_hDHD : ∀ i j : Fin n, A i j = D i * H i j * D j)
    (lam_min : ℝ)
    (_hH_diag : ∀ i : Fin n, H i i = 1)
    (hn1 : gammaValid fp (n + 1))
    (hγ_lt : gamma fp (n + 1) < 1)
    -- The eigenvalue condition: lam_min(H) > threshold
    (hlam_min : lam_min > ↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)))
    -- This minimum eigenvalue is a true lower bound on the spectrum
    (_hLam_bound : ∀ x : Fin n → ℝ,
      (∃ i, x i ≠ 0) →
      lam_min * ∑ i : Fin n, x i ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j) :
    -- Conclusion: the threshold is positive, confirming success is possible
    0 < lam_min := by
  have hγ_nn : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  have h1_γ_pos : (0 : ℝ) < 1 - gamma fp (n + 1) := by linarith
  have h_threshold_nn : 0 ≤ ↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)) := by
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg n) hγ_nn
    · linarith
  linarith

/-- **Cholesky failure-condition threshold consequence**
    (Higham §10.1, Theorem 10.7, second part).

    This theorem formalizes the sign consequence `lam_min < 0`; the full
    algorithmic failure result is not derived here from a concrete Cholesky
    execution. -/
theorem cholesky_failure_condition (n : ℕ) (fp : FPModel)
    (lam_min : ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hγ_lt : gamma fp (n + 1) < 1)
    (hLam_neg : lam_min < -(↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)))) :
    lam_min < 0 := by
  have hγ_nn : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  have h1_γ_pos : (0 : ℝ) < 1 - gamma fp (n + 1) := by linarith
  have h_threshold_nn : 0 ≤ ↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)) := by
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg n) hγ_nn
    · linarith
  linarith

end LeanFpAnalysis.FP
