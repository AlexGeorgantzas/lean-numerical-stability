import HighamBench.P05Definitions

namespace HighamBench

open scoped BigOperators

/-- P05-T1: Lemma 4.1 for the paper's `k = m + 1`. A certified
round-to-nearest execution of
`(c - sum_i a_i*b_i) / bK` has protected-`c` backward coefficients bounded by
`(m+1)u`; when `bK = 1` and no division is performed, the sharper bound is
`m*u`. -/
theorem p05_t1_uniform_backward_coefficients
    {m : ℕ} (run : P05Lemma41Run m) :
    (∃ θ0 : ℝ, ∃ θ : Fin m → ℝ,
      |θ0| ≤ ((m + 1 : ℕ) : ℝ) * run.format.unitRoundoff ∧
      (∀ i, |θ i| ≤ ((m + 1 : ℕ) : ℝ) * run.format.unitRoundoff) ∧
      run.bK * run.yHat * (1 + θ0) =
        run.c - ∑ i : Fin m, run.a i * run.b i * (1 + θ i)) ∧
    (run.bK = 1 →
      ∃ θ0 : ℝ, ∃ θ : Fin m → ℝ,
        |θ0| ≤ (m : ℝ) * run.format.unitRoundoff ∧
        (∀ i, |θ i| ≤ (m : ℝ) * run.format.unitRoundoff) ∧
        run.yHat * (1 + θ0) =
          run.c - ∑ i : Fin m, run.a i * run.b i * (1 + θ i)) := by
  -- PROOF_START
  sorry

end HighamBench
