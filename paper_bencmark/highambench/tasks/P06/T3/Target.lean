import HighamBench.P06Definitions

namespace HighamBench

/-- P06-T3: the exact algebra behind the first-order expansion (4.8)--(4.9).
The fully perturbed transformation product splits into its exact part, the
sum of all single-perturbation insertions, and an explicit `t²` remainder. -/
theorem p06_t3_householder_product_first_order_expansion
    {m : ℕ} (t : ℝ)
    (P E : ℕ → Fin m → Fin m → ℝ) (b : Fin m → ℝ) :
    ∀ r i,
      p06PerturbedState t P E b r i =
        p06ExactState P b r i +
          t * p06FirstOrderState P E b r i +
          t ^ 2 * p06HigherOrderState t P E b r i := by
  -- PROOF_START
  sorry

end HighamBench
