import HighamBench.P18Definitions

namespace HighamBench

/-- P18-T3: the printed Method 4s3pC coefficients satisfy the third-order
consistency and simplified smooth-perturbation conditions to their print
precision, while failing the corresponding nonsmooth absolute condition. -/
theorem p18_t3_method4s3pc_order_certificate :
    p18Method4s3pCBPerturbation = (fun _ => 0) ∧
      |p18CoeffDot p18Method4s3pCBTilde p18Method4s3pCE - 1| ≤
        p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde p18Method4s3pCCTilde - 1 / 2| ≤
        p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffHadamard p18Method4s3pCCTilde
            p18Method4s3pCCTilde) - 1 / 3| ≤
        p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffMatVec p18Method4s3pCATilde
            p18Method4s3pCCTilde) - 1 / 6| ≤
        p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          p18Method4s3pCCPerturbation| ≤ p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffMatVec p18Method4s3pCAPerturbation
            p18Method4s3pCCTilde)| ≤ p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffMatVec p18Method4s3pCATilde
            p18Method4s3pCCPerturbation)| ≤ p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffHadamard p18Method4s3pCCTilde
            p18Method4s3pCCPerturbation)| ≤ p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffMatVec p18Method4s3pCAPerturbation
            p18Method4s3pCCPerturbation)| ≤ p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffHadamard p18Method4s3pCCPerturbation
            p18Method4s3pCCPerturbation)| ≤ p18PrintedCoeffTolerance ∧
      1 / 100 < p18CoeffAbsDot p18Method4s3pCBTilde
        p18Method4s3pCCPerturbation := by
  -- PROOF_START
  sorry

end HighamBench
