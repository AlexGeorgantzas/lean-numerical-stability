import HighamBench.P16Definitions

namespace HighamBench

/-- P16-T3: Theorem 6.3 for the recorded mixed-precision restarted MGS-GMRES
execution. At every restart, the actual normalized backward error and relative
forward error obey the paper's `Lambda` contraction up to their respective
high-precision first-order floors. -/
theorem p16_t3_mixed_precision_geometric_convergence
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (run : P16MixedPrecisionGMRESRun (n := n) l)
    (hLambda : p16MuchLessThanOneAt l (p16MixedContraction run)) :
    (∀ i : ℕ,
      p16FirstOrderLeAt l (p16MixedScale run)
        (fun t ↦ p16BackwardError run.A run.b (run.xHat (i + 1) t))
        (fun t ↦
          p16MixedContraction run t *
              p16BackwardError run.A run.b (run.xHat i t) +
            p16BackwardFloor run t)) ∧
      ∀ i : ℕ,
        p16FirstOrderLeAt l (p16MixedScale run)
          (fun t ↦ p16ForwardError run.xExact (run.xHat (i + 1) t))
          (fun t ↦
            p16MixedContraction run t *
                p16ForwardError run.xExact (run.xHat i t) +
              p16ForwardFloor run t) := by
  -- PROOF_START
  sorry

end HighamBench
