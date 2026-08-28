import HighamBench.P08Definitions

namespace HighamBench

/-- P08-T2: the residual-image half of Lemma 4.2. Exact inverse action and
the componentwise update-rounding bound yield Skeel's expanded residual bound. -/
theorem p08_t2_lemma_4_2_residual_bound
    {n : ℕ} (A Ainv : Fin n → Fin n → ℝ)
    (x q h xNext : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u)
    (hInverseAction : ∀ i, p08MatVec A (p08MatVec Ainv q) i = q i)
    (hUpdate : ∀ i, xNext i = p08MatVec Ainv q i + x i + h i)
    (hRound : ∀ i, |h i| ≤ u * |p08MatVec Ainv q i| + u * |x i|) :
    ∀ i, |p08MatVec A (fun j ↦ xNext j - x j) i| ≤
      |q i| + u * p08AbsProductAction A Ainv q i +
        u * p08AbsAction A x i := by
  -- PROOF_START
  sorry

end HighamBench
