import HighamBench.P16Definitions

namespace HighamBench

/-- P16-T2: exact finite form of the backward-error half of Lemma 4.2. The
computed residual, correction, and update errors yield the next-residual
recurrence before any second-order terms are dropped. -/
theorem p16_t2_restarted_residual_recurrence {n : ℕ}
    (A : P16Matrix n) (b x correction xNext rhat deltaR deltaX : P16Vector n)
    (epsilonR epsilonU w omega : ℝ)
    (hresidual : rhat = p16Residual A b x + deltaR)
    (hupdate : xNext = x + correction + deltaX)
    (hcorrection :
      p16VecNorm (rhat - p16MatVec A correction) ≤
        w * p16VecNorm (p16Residual A b x) +
          omega * (p16VecNorm b + p16FrobNorm A * p16VecNorm xNext))
    (hdeltaR :
      p16VecNorm deltaR ≤
        epsilonR * (p16VecNorm b + p16FrobNorm A * p16VecNorm x))
    (hdeltaX : p16VecNorm deltaX ≤ epsilonU * p16VecNorm xNext)
    (hxmono : p16VecNorm x ≤ p16VecNorm xNext)
    (hepsilonR : 0 ≤ epsilonR) (hepsilonU : 0 ≤ epsilonU) :
    p16VecNorm (p16Residual A b xNext) ≤
      w * p16VecNorm (p16Residual A b x) +
        (epsilonR + epsilonU + omega) *
          (p16VecNorm b + p16FrobNorm A * p16VecNorm xNext) := by
  -- PROOF_START
  sorry

end HighamBench
