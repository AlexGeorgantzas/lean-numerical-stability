import HighamBench.P19Definitions

namespace HighamBench

/-- P19-T3: equations (3.17), (3.20), and Remark 4. Right- and fixed-
preconditioner flexible MGS-GMRES each attain their conditional first-order
forward-error bound at some iteration no larger than `n`; the right envelope's
additional term is exactly the cost of reapplying `M_R^{-1}` in line 4. -/
theorem p19_t3_right_flexible_attainable_forward_error
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (system : P19FixedRightSystem n)
    (right : P19RightTheorem33Execution system l)
    (flexible : P19FlexibleTheorem34Execution system l) :
    (∃ k : ℕ,
      k = right.run.keyDimension ∧ 0 < k ∧ k ≤ n ∧
        p19FirstOrderLeAt l
          (fun t ↦ p19Condition316Value system
            (right.run.ug t) (right.run.um t) (right.run.ua t)
            (right.run.etaR t) (right.run.rhoAR t))
          (fun t ↦ p19ForwardError system.xExact (right.algorithm.xHat t))
          (fun t ↦
            p19PolynomialFactorValue right.run.polynomialFactor n k *
              p19RightAttainableEnvelope system
                (right.run.ug t) (right.run.um t) (right.run.ua t)
                (right.run.etaR t) (right.run.rhoAR t))) ∧
      (∃ k : ℕ,
        k = flexible.run.keyDimension ∧ 0 < k ∧ k ≤ n ∧
          p19FirstOrderLeAt l
            (fun t ↦ p19Condition316Value system
              (flexible.run.ug t) (flexible.run.um t) (flexible.run.ua t)
              (flexible.run.etaR t) (flexible.run.rhoAR t))
            (fun t ↦
              p19ForwardError system.xExact (flexible.algorithm.xHat t))
            (fun t ↦
              p19PolynomialFactorValue flexible.run.polynomialFactor n k *
                p19FlexibleAttainableEnvelope system
                  (flexible.run.ug t) (flexible.run.ua t)
                  (flexible.run.rhoAR t))) ∧
        ∀ t,
          p19RightAttainableEnvelope system
              (right.run.ug t) (right.run.um t) (right.run.ua t)
              (right.run.etaR t) (right.run.rhoAR t) =
            p19FlexibleAttainableEnvelope system
                (right.run.ug t) (right.run.ua t) (right.run.rhoAR t) +
              right.run.um t * right.run.etaR t *
                p19RightPreconditionerKappa2 system := by
  -- PROOF_START
  sorry

end HighamBench
