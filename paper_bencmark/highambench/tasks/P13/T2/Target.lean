import HighamBench.P13Definitions

namespace HighamBench

/-- P13-T2: Lemma 2.2's componentwise data-perturbation bound. -/
theorem p13_t2_data_perturbation_bound {n : ℕ}
    (ell f deltaF : Fin n → ℝ) (epsilon : ℝ)
    (hdelta : ∀ i, |deltaF i| ≤ epsilon * |f i|)
    (hvalue : p13InterpolationValue ell f ≠ 0) :
    |p13InterpolationValue ell (fun i => f i + deltaF i) -
        p13InterpolationValue ell f| /
        |p13InterpolationValue ell f| ≤
      epsilon * p13Condition ell f := by
  -- PROOF_START
  sorry

end HighamBench
