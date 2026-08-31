import HighamBench.P15Definitions

namespace HighamBench

/-- P15-T3: Lemma 3.3, equations (3.10)--(3.11), for either permitted order of
the three rounded products forming the product of two low-rank matrices. -/
theorem p15_t3_low_rank_matmul_error {b r : ℕ}
    (run : P15LowRankMatMulExecution b r) :
    let Atilde := p15LowRankMatrix run.XA run.YA
    let Btilde := p15LowRankMatrix run.YB run.XB
    let gammaC :=
      p15GammaReal (p15LowRankMatMulCost b r) run.unitRoundoff
    p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) ≤
        gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde ∧
      p15FrobNorm (run.trace.result - p15MatMul run.A run.B) ≤
        gammaC * p15FrobNorm run.A * p15FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p15FrobNorm run.B +
              p15FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB) := by
  -- PROOF_START
  sorry

end HighamBench
