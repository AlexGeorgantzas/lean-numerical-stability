import HighamBench.P15Definitions

namespace HighamBench

/-- P15-T2: exact finite form of Lemma 3.1, equation (3.2), composing the
low-rank truncation error with the rounded low-rank matrix-vector product. -/
theorem p15_t2_low_rank_matvec_backward_error {n : ℕ}
    (A Atilde truncError roundingError : P15Matrix n)
    (v computed : P15Vector n) (epsilon beta gammaC : ℝ)
    (hepsilon : 0 ≤ epsilon) (hbeta : 0 ≤ beta) (hgammaC : 0 ≤ gammaC)
    (happrox : Atilde = A + truncError)
    (hcomputed : computed = p15MatVec (Atilde + roundingError) v)
    (htrunc : p15FrobNorm truncError ≤ epsilon * beta)
    (hround : p15FrobNorm roundingError ≤ gammaC * p15FrobNorm Atilde) :
    ∃ totalError : P15Matrix n,
      computed = p15MatVec (A + totalError) v ∧
      p15FrobNorm totalError ≤
        gammaC * p15FrobNorm A + epsilon * (1 + gammaC) * beta := by
  -- PROOF_START
  sorry

end HighamBench
