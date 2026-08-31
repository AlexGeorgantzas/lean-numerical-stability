import HighamBench.P07Definitions

namespace HighamBench

/-- P07-T2: a project-corrected version of the backward-error result in the
proof of Theorem 3.5. The two explicit hypotheses repair the source's missing
perturbed-rank and consistency conditions. -/
theorem p07_t2_backward_error_product_budget
    {m s n : ℕ} {u : ℝ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    (model : P07ScalarArithmeticModel)
    (forwardRun : P07Lemma32ForwardRun pre model)
    (run : P07SAABlendenpikRun pre model forwardRun u)
    (hPerturbedYFullRank :
      Function.Injective (p07MatVec (p07Theorem35PerturbedY run)))
    (hPerturbedBInRange :
      ∃ x, p07MatVec (p07Theorem35PerturbedA run) x =
        p07Theorem35PerturbedB run) :
    p07Theorem35PerturbedA run =
        p07RectMatMul (p07Theorem35PerturbedY run)
          (p07Theorem35PerturbedR run) ∧
      P07MoorePenrosePseudoinverse (p07Theorem35PerturbedA run)
        (p07Theorem35PerturbedPseudoinverse run) ∧
      run.backSubstitution.xHat =
        p07MatVec (p07Theorem35PerturbedPseudoinverse run)
          (p07Theorem35PerturbedB run) ∧
      p07MatVec (p07Theorem35PerturbedA run)
          run.backSubstitution.xHat = p07Theorem35PerturbedB run ∧
      p07RectOpNorm2Le (p07Theorem35DeltaA run)
        (run.rSpectrum.upper *
          (((n : ℝ) + Real.sqrt n) * gamma u n * run.ySpectrum.upper +
            (1 + Real.sqrt n * gamma u n) *
              run.lsqrDeltaSpectrum.upper)) := by
  -- PROOF_START
  sorry

end HighamBench
