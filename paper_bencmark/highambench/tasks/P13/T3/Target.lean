import HighamBench.P13Definitions

namespace HighamBench

/-- P13-T3: exact finite-certificate form of Theorem 4.1's two cancellation
terms.  The denominator correction is the finite counterpart of the theorem's
first-order `O(u^2)` presentation. -/
theorem p13_t3_barycentric_forward_bound {n : ℕ}
    (coeff f deltaNum deltaDen : Fin n → ℝ)
    (epsilonNum epsilonDen : ℝ)
    (hepsilonNum : 0 ≤ epsilonNum)
    (hepsilonDen : 0 ≤ epsilonDen)
    (hdeltaNum : p13TermPerturbation
      (fun i => coeff i * f i) deltaNum epsilonNum)
    (hdeltaDen : p13TermPerturbation coeff deltaDen epsilonDen)
    (hnumerator : p13InterpolationValue coeff f ≠ 0)
    (hdenominator : p13InterpolationValue coeff (fun _ => 1) ≠ 0)
    (hsmall : epsilonDen * p13Condition coeff (fun _ => 1) < 1) :
    |p13BarycentricComputed coeff f deltaNum deltaDen -
        p13BarycentricValue coeff f| /
        |p13BarycentricValue coeff f| ≤
      (epsilonNum * p13Condition coeff f +
        epsilonDen * p13Condition coeff (fun _ => 1)) /
      (1 - epsilonDen * p13Condition coeff (fun _ => 1)) := by
  -- PROOF_START
  sorry

end HighamBench
