import HighamBench.P04Definitions

namespace HighamBench

/-- P04-T2: scalar entrywise form of Theorem 3.2's exact coefficient
assembly, including conversion of both inputs to the low precision. -/
theorem p04_t2_mixed_input_product_bound
    (uLow uFma u : ℝ) (q n : ℕ)
    (a b Δa Δb e computed : ℝ)
    (huLow : 0 ≤ uLow) (huFma : 0 ≤ uFma) (hu : 0 ≤ u)
    (hq : P04GammaValid uFma q) (hn : P04GammaValid u n)
    (hΔa : |Δa| ≤ uLow * |a|)
    (hΔb : |Δb| ≤ uLow * |b|)
    (he : |e| ≤ p04BlockFmaCoeff uFma u q n * |a + Δa| * |b + Δb|)
    (hcomputed : computed = (a + Δa) * (b + Δb) + e) :
    |computed - a * b| ≤
      (2 * uLow + uLow ^ 2 +
          p04BlockFmaCoeff uFma u q n * (1 + uLow) ^ 2) *
        |a| * |b| := by
  -- PROOF_START
  sorry

end HighamBench
