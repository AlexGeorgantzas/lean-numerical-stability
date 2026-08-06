import HighamBench.P08Definitions

namespace HighamBench

/-- P08-T1: the forward-error half of Lemma 4.2, with the printed
`abs(Ainv)*abs(q)` action expanded as a finite sum. -/
theorem p08_t1_lemma_4_2_forward_error_bound
    {n : ℕ} (Ainv : Fin n → Fin n → ℝ)
    (x q h xNext : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u)
    (hUpdate : ∀ i, xNext i = p08MatVec Ainv q i + x i + h i)
    (hRound : ∀ i, |h i| ≤ u * |p08MatVec Ainv q i| + u * |x i|) :
    ∀ i, |xNext i - x i| ≤
      (1 + u) * p08AbsAction Ainv q i + u * |x i| := by
  -- PROOF_START
  sorry

end HighamBench
