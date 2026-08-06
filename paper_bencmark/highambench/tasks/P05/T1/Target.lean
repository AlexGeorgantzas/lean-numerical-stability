import HighamBench.P05Definitions

namespace HighamBench

open scoped BigOperators

/-- P05-T1: the uniform componentwise coefficient form used in Lemma 4.1.
The preceding summation analysis supplies `herror` with `C = (k+1)*u`; this
theorem performs the exact sign-aligned residual distribution. -/
theorem p05_t1_uniform_backward_coefficients
    {k : ℕ} (u computed c : ℝ) (products : Fin k → ℝ)
    (hu : 0 ≤ u)
    (herror :
      |computed - (c - ∑ i : Fin k, products i)| ≤
        ((k + 1 : ℕ) : ℝ) * u *
          ∑ x : Option (Option (Fin k)),
            |p05CoefficientSource computed c products x|) :
    ∃ θ0 θc : ℝ, ∃ θp : Fin k → ℝ,
      |θ0| ≤ ((k + 1 : ℕ) : ℝ) * u ∧
      |θc| ≤ ((k + 1 : ℕ) : ℝ) * u ∧
      (∀ i, |θp i| ≤ ((k + 1 : ℕ) : ℝ) * u) ∧
      computed * (1 + θ0) =
        c * (1 + θc) - ∑ i : Fin k, products i * (1 + θp i) := by
  -- PROOF_START
  sorry

end HighamBench
