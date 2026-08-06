import HighamBench.P19Definitions

namespace HighamBench

/-- P19-T2: exact finite-vector realization of the four-source modular
aggregate `ξ = αεc + βεb + βug + λεx` in equation (3.8). -/
theorem p19_t2_modular_four_source_error_bound {n : ℕ}
    (alpha beta lambda epsilonC epsilonB ug epsilonX : ℝ)
    (computationError rhsError gmresError solutionError : Fin n → ℝ)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hlambda : 0 ≤ lambda)
    (hcomputation : p19VecNorm2 computationError ≤ epsilonC)
    (hrhs : p19VecNorm2 rhsError ≤ epsilonB)
    (hgmres : p19VecNorm2 gmresError ≤ ug)
    (hsolution : p19VecNorm2 solutionError ≤ epsilonX) :
    p19VecNorm2
        (p19ModularError alpha beta lambda computationError rhsError
          gmresError solutionError) ≤
      p19ModularEnvelope alpha beta lambda epsilonC epsilonB ug epsilonX := by
  -- PROOF_START
  sorry

end HighamBench
