import HighamBench.P16Definitions

namespace HighamBench

/-- P16-T2: the backward-error half of Lemma 4.2. Equation (4.18)
holds exactly, while the recurrence (4.15) retains the paper's `≲` semantics
through an explicit second-order remainder. -/
theorem p16_t2_restarted_residual_recurrence
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : P16Matrix n) (b : P16Vector n) (iteration : ℕ)
    (scale : ι → ℝ) (hscale : Filter.Tendsto scale l (nhds 0))
    (hn : 0 < n) (hA : p16IsNonsingular A) (hb : b ≠ 0)
    (step : P16Lemma42BackwardStep l scale A b iteration) :
    (∀ t,
      p16MatVec A (step.xHatNext t) - b =
        step.deltaR t + p16MatVec A (step.correctionHat t) -
          step.residualHat t + p16MatVec A (step.deltaX t)) ∧
      p16FirstOrderLeAt l scale
        (fun t ↦ p16VecNorm (p16Residual A b (step.xHatNext t)))
        (fun t ↦
          step.w t * p16VecNorm (p16Residual A b (step.xHat t)) +
            (step.epsilonR t + step.epsilonU t + step.omega t) *
              (p16VecNorm b +
                p16FrobNorm A * p16VecNorm (step.xHatNext t))) := by
  -- PROOF_START
  sorry

end HighamBench
