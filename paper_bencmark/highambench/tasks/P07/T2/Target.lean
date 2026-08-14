import HighamBench.P07Definitions

namespace HighamBench

/-- P07-T2: the unnumbered backward-error result in the proof of Theorem 3.5.
It retains Algorithm 1.3's computed quantities, the perturbed least-squares
relation, all four terms of `DeltaA`, and the exact page-920 norm bound. -/
theorem p07_t2_backward_error_product_budget
    {m s n : ℕ} {u : ℝ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    (model : P07ScalarArithmeticModel)
    (forwardRun : P07Lemma32ForwardRun pre model)
    (run : P07SAABlendenpikRun pre model forwardRun u) :
    p07Theorem35PerturbedA run =
        p07RectMatMul (p07Theorem35PerturbedY run)
          (p07Theorem35PerturbedR run) ∧
      run.backSubstitution.xHat =
        p07MatVec run.backSubstitution.perturbedRInv
          (p07MatVec run.lsqr.perturbedPseudoinverse
            (p07Theorem35PerturbedB run)) ∧
      p07LeastSquaresNormalEquation (p07Theorem35PerturbedA run)
        (p07Theorem35PerturbedB run) run.backSubstitution.xHat ∧
      p07RectOpNorm2Le (p07Theorem35DeltaA run)
        (run.rSpectrum.upper *
          (((n : ℝ) + Real.sqrt n) * gamma u n * run.ySpectrum.upper +
            (1 + Real.sqrt n * gamma u n) *
              run.lsqrDeltaSpectrum.upper)) := by
  -- PROOF_START
  sorry

end HighamBench
