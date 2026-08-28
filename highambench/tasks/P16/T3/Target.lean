import HighamBench.P16Definitions

namespace HighamBench

/-- P16-T3: Theorem 6.3 for one fixed-precision, fully stored restarted
MGS-GMRES execution. At restart `i`, both actual errors obey the source's
first-order affine contraction with `c(n,k_i)`, low-precision contraction, and
the corresponding high-precision floor. -/
theorem p16_t3_mixed_precision_geometric_convergence
    {n : ℕ} (run : P16FixedMixedPrecisionGMRESRun n)
    (hLambda : ∀ i : ℕ,
      0 ≤ p16FixedMixedContraction run i ∧
        p16FixedMixedContraction run i < 1) :
    (∀ i : ℕ,
      p16BackwardError run.A run.b (run.xHat (i + 1)) ≤
        p16FixedMixedContraction run i *
            p16BackwardError run.A run.b (run.xHat i) +
          p16FixedBackwardFloor run i) ∧
      ∀ i : ℕ,
        p16ForwardError run.xExact (run.xHat (i + 1)) ≤
          p16FixedMixedContraction run i *
              p16ForwardError run.xExact (run.xHat i) +
            p16FixedForwardFloor run i := by
  -- PROOF_START
  sorry

end HighamBench
