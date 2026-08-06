import HighamBench.P16Definitions

namespace HighamBench

/-- P16-T3: exact finite iteration form of Theorem 6.3. If mixed-precision
GMRES contracts by `Lambda` whenever an error remains above its attainable
high-precision floor, then after any number of consecutive such restarts the
error is bounded by `Lambda ^ i` times its initial value. -/
theorem p16_t3_mixed_precision_geometric_convergence {n : ℕ}
    (A Ainv : P16Matrix n) (c uLow uHigh : ℝ)
    (backwardError forwardError : ℕ → ℝ)
    (hc : 0 ≤ c) (huLow : 0 ≤ uLow) (huHigh : 0 ≤ uHigh)
    (hcontract : p16MixedContraction c uLow A Ainv < 1)
    (hbackward : ∀ i : ℕ,
      p16BackwardFloor c uHigh < backwardError i →
        backwardError (i + 1) ≤
          p16MixedContraction c uLow A Ainv * backwardError i)
    (hforward : ∀ i : ℕ,
      p16ForwardFloor c uHigh A Ainv < forwardError i →
        forwardError (i + 1) ≤
          p16MixedContraction c uLow A Ainv * forwardError i) :
    0 ≤ p16BackwardFloor c uHigh ∧
    0 ≤ p16ForwardFloor c uHigh A Ainv ∧
    ∀ i : ℕ,
      p16MixedContraction c uLow A Ainv ^ i ≤ 1 ∧
      ((∀ j < i, p16BackwardFloor c uHigh < backwardError j) →
        backwardError i ≤
          p16MixedContraction c uLow A Ainv ^ i * backwardError 0) ∧
      ((∀ j < i, p16ForwardFloor c uHigh A Ainv < forwardError j) →
        forwardError i ≤
          p16MixedContraction c uLow A Ainv ^ i * forwardError 0) := by
  -- PROOF_START
  sorry

end HighamBench
