import HighamBench.P19Definitions

namespace HighamBench

/-- P19-T2: Theorem 3.1. A modular MGS-GMRES execution has a key dimension
`k ≤ n` with the two `4/3` basis-conditioning bounds, and for every nonsingular
analytical right preconditioner its computed solution satisfies the normalized
first-order forward-error bound (3.8). -/
theorem p19_t2_modular_gmres_forward_error
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (execution : P19Theorem31Execution (n := n) l) :
    ∃ k : ℕ,
      k = execution.run.keyDimension ∧
        0 < k ∧ k ≤ n ∧
          (∀ᶠ t in l,
            1 / (execution.run.vHatSpectrum t).sigmaMin ≤ 4 / 3 ∧
              (execution.run.vHatSpectrum t).sigmaMax ≤ 4 / 3) ∧
          ∀ (MR MRinv : P19Matrix n) (hMR : p19InversePair MR MRinv),
            let analysis := execution.forwardAnalysis MR MRinv hMR
            p19FirstOrderLeAt l (p19PrecisionScale execution.run)
              (fun t ↦ p19ForwardError execution.run.xExact (execution.run.xHat t))
              (fun t ↦
                p19PolynomialFactorValue execution.run.polynomialFactor n k *
                  p19Xi execution.run MR MRinv analysis.quantities t *
                  p19ConditionNumberF
                    (p19SplitOperator execution.run MRinv)
                    (p19SplitInverse execution.run MR)) := by
  -- PROOF_START
  sorry

end HighamBench
