import HighamBench.P15Definitions

namespace HighamBench

/-- P15-T2: exact finite forms of Lemma 3.1, equations (3.1) and (3.2),
deriving the rounded low-rank product and composing it with truncation error. -/
theorem p15_t2_low_rank_matvec_backward_error {b r : ℕ}
    (run : P15LowRankMatVecExecution b r) :
    let Atilde := p15LowRankMatrix run.X run.Y
    let deltaAtilde := p15LowRankRoundingError run
    let deltaA := p15LowRankTotalError run
    let gammaC :=
      p15GammaReal (p15LowRankKernelCost b r) run.unitRoundoff
    run.zHat = p15MatVec (Atilde + deltaAtilde) run.v ∧
    p15FrobNorm deltaAtilde ≤ gammaC * p15FrobNorm Atilde ∧
    deltaA = run.truncError + deltaAtilde ∧
    run.zHat = p15MatVec (run.A + deltaA) run.v ∧
    p15FrobNorm deltaA ≤
      gammaC * p15FrobNorm run.A +
        run.epsilon * (1 + gammaC) * run.beta ∧
    gammaC * p15FrobNorm run.A +
        run.epsilon * (1 + gammaC) * run.beta =
      gammaC * p15FrobNorm run.A + run.epsilon * run.beta +
        run.epsilon * gammaC * run.beta := by
  -- PROOF_START
  sorry

end HighamBench
