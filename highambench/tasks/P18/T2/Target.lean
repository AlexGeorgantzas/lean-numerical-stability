import HighamBench.P18Definitions

namespace HighamBench

/-- P18-T2: the corrected implicit-midpoint arrays satisfy the exact
second-order consistency and perturbation conditions used after (4.1). -/
theorem p18_t2_corrected_midpoint_order_bound :
    p18CorrectedMidpointATilde =
        p18CoeffMatAdd p18CorrectedMidpointA
          p18CorrectedMidpointAPerturbation ∧
      p18CorrectedMidpointCTilde =
        p18Add p18CorrectedMidpointC
          p18CorrectedMidpointCPerturbation ∧
      p18CorrectedMidpointBTilde =
        p18Add p18CorrectedMidpointB
          p18CorrectedMidpointBPerturbation ∧
      p18CoeffMatVec p18CorrectedMidpointA p18CorrectedMidpointE =
        p18CorrectedMidpointC ∧
      p18CoeffMatVec p18CorrectedMidpointAPerturbation
          p18CorrectedMidpointE = p18CorrectedMidpointCPerturbation ∧
      p18CoeffDot p18CorrectedMidpointBTilde p18CorrectedMidpointE = 1 ∧
      p18CoeffDot p18CorrectedMidpointBTilde
          p18CorrectedMidpointCTilde = 1 / 2 ∧
      p18CoeffDot p18CorrectedMidpointBPerturbation
          p18CorrectedMidpointE = 0 ∧
      p18CoeffDot p18CorrectedMidpointBPerturbation
          p18CorrectedMidpointCTilde = 0 ∧
      p18CoeffDot p18CorrectedMidpointBTilde
          p18CorrectedMidpointCPerturbation = 0 ∧
      p18CoeffDot p18CorrectedMidpointBPerturbation
          p18CorrectedMidpointCPerturbation = 0 ∧
      p18CoeffAbsDot p18CorrectedMidpointBPerturbation
          p18CorrectedMidpointE = 0 ∧
      p18CoeffAbsDot p18CorrectedMidpointBTilde
          p18CorrectedMidpointCPerturbation = 0 := by
  -- PROOF_START
  sorry

end HighamBench
