import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Variance Identities

Finite-dimensional algebraic versions of the variance identities highlighted in
HDP Exercise 0.0.3. Probability-specific uses can instantiate these identities
after proving the corresponding expectation and cross-term hypotheses.
-/

open scoped BigOperators

namespace LeanFpAnalysis.HDP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Deterministic orthogonal-sum identity underlying Exercise 0.0.3(a). -/
theorem norm_sum_sq_of_pairwise_inner_zero {k : ℕ} (u : Fin k → E)
    (horth : ∀ i j : Fin k, i ≠ j → inner ℝ (u i) (u j) = 0) :
    ‖∑ j : Fin k, u j‖ ^ 2 = ∑ j : Fin k, ‖u j‖ ^ 2 := by
  classical
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      have hinner : inner ℝ (∑ j : Fin k, u j.castSucc) (u (Fin.last k)) = 0 := by
        rw [sum_inner]
        exact Finset.sum_eq_zero fun j _ => horth j.castSucc (Fin.last k) (by simp)
      have hih :
          ‖∑ j : Fin k, u j.castSucc‖ ^ 2 = ∑ j : Fin k, ‖u j.castSucc‖ ^ 2 := by
        exact ih (fun j : Fin k => u j.castSucc)
          (fun i j hij => horth i.castSucc j.castSucc (by simpa using hij))
      calc
        ‖(∑ j : Fin k, u j.castSucc) + u (Fin.last k)‖ ^ 2
            = ‖∑ j : Fin k, u j.castSucc‖ ^ 2
                + 2 * inner ℝ (∑ j : Fin k, u j.castSucc) (u (Fin.last k))
                + ‖u (Fin.last k)‖ ^ 2 := by
              rw [norm_add_sq_real]
        _ = ∑ j : Fin k, ‖u j.castSucc‖ ^ 2 + ‖u (Fin.last k)‖ ^ 2 := by
              simp [hinner, hih]
        _ = ∑ j : Fin (k + 1), ‖u j‖ ^ 2 := by
              rw [Fin.sum_univ_castSucc]

/-- Weighted finite-distribution form of `E‖Z - EZ‖² = E‖Z‖² - ‖EZ‖²`,
the identity used in Exercise 0.0.3(b). -/
theorem weighted_variance_identity {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → E)
    (hw₁ : ∑ i, w i = 1) :
    (∑ i, w i * ‖z i - (∑ j, w j • z j)‖ ^ 2)
      = (∑ i, w i * ‖z i‖ ^ 2) - ‖∑ i, w i • z i‖ ^ 2 := by
  classical
  let μ : E := ∑ j, w j • z j
  have hinner_sum : ∑ i, w i * inner ℝ (z i) μ = inner ℝ μ μ := by
    calc
      ∑ i, w i * inner ℝ (z i) μ
          = inner ℝ (∑ i, w i • z i) μ := by
              simp [sum_inner, real_inner_smul_left]
      _ = inner ℝ μ μ := by simp [μ]
  have hconst : ∑ i, w i * ‖μ‖ ^ 2 = ‖μ‖ ^ 2 * ∑ i, w i := by
    rw [← Finset.sum_mul]
    ring
  calc
    ∑ i, w i * ‖z i - (∑ j, w j • z j)‖ ^ 2
        = ∑ i, w i * (‖z i‖ ^ 2 - 2 * inner ℝ (z i) μ + ‖μ‖ ^ 2) := by
          simp [μ, norm_sub_sq_real]
    _ = (∑ i, w i * ‖z i‖ ^ 2)
          - 2 * (∑ i, w i * inner ℝ (z i) μ)
          + (∑ i, w i) * ‖μ‖ ^ 2 := by
          simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum]
          rw [hconst]
          ring_nf
    _ = (∑ i, w i * ‖z i‖ ^ 2) - ‖μ‖ ^ 2 := by
          rw [hinner_sum, hw₁]
          rw [← real_inner_self_eq_norm_sq]
          ring
    _ = (∑ i, w i * ‖z i‖ ^ 2) - ‖∑ i, w i • z i‖ ^ 2 := by
          simp [μ]

end LeanFpAnalysis.HDP
