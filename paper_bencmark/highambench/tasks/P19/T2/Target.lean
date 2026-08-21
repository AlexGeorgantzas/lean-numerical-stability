import HighamBench.P19Definitions

namespace HighamBench

/-- P19-T2: Theorem 3.1. The MGS case split selects a dimension `k ≤ n`
with both `4/3` basis-conditioning bounds. At that same dimension, every
nonsingular analytical right preconditioner gives the normalized first-order
forward-error estimate (3.8). -/
theorem p19_t2_modular_gmres_forward_error
    {n : ℕ} (semantics : P19FirstOrderSemantics)
    (family : P19Theorem31Family n semantics)
    (mgs : P19MGSSelectionLaw family)
    (appendix : P19StaticAppendixATheory family) :
    ∃ k : P19Theorem31Dimension n,
      p19IterationWellConditioned (family.iteration k) ∧
        (P19Algorithm2Conditions (family.iteration k) →
        ∀ (MR MRinv : P19Matrix n) (hMR : p19InversePair MR MRinv),
          let q := appendix.rightQuantities k MR MRinv hMR
          p19FirstOrderLe semantics
            (p19ForwardError family.system.xExact
              (family.iteration k).xHat)
            ((family.iteration k).dimensionFactor *
              p19StaticXi MR MRinv q *
              p19ConditionNumberF
                (p19StaticSplitOperator family.system MRinv)
                (p19StaticSplitInverse family.system MR))) := by
  -- PROOF_START
  sorry

end HighamBench
