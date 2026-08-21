import HighamBench.P18Definitions

namespace HighamBench

/-- P18-T3: Method 4s3pC has third-order scheme error in both source
regularity regimes. Under the source's exact-tableau interpretation and an
explicit finite-time stability model, the perturbation error is third order
for well-behaved `tau` and second order otherwise. -/
theorem p18_t3_method4s3pc_global_error_regimes
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    {ι : Type*} (method : P18Method4s3pCSourceModel)
    (smooth : P18StableMethod4s3pCBranch State ι method 4)
    (nonsmooth : P18StableMethod4s3pCBranch State ι method 3)
    (hsmooth : smooth.tauRegime = P18TauRegime.wellBehaved)
    (hnonsmooth :
      nonsmooth.tauRegime = P18TauRegime.notWellBehaved) :
    method.tableau.bPerturbation = (fun _ ↦ 0) ∧
      p18ThirdOrderConsistency method.tableau ∧
      p18SmoothPerturbationOrderThree method.tableau ∧
      p18UniformTwoTermGlobalOrder smooth.globalError
        smooth.globalSchemeError smooth.globalPerturbationError
        smooth.step smooth.epsilon 3 3 ∧
      p18UniformTwoTermGlobalOrder nonsmooth.globalError
        nonsmooth.globalSchemeError nonsmooth.globalPerturbationError
        nonsmooth.step nonsmooth.epsilon 3 2 := by
  -- PROOF_START
  sorry

end HighamBench
