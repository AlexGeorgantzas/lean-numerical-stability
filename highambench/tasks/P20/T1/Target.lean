import HighamBench.P20Definitions

namespace HighamBench

/-- P20-T1: equations (3.1), (3.2), and (3.4a). For every nonzero row of
`A`, the selected diagonal entry of `Lambda` is a positive power of two that
satisfies (3.4a), and the maximum coefficient of `Lambda A` lies in
`(theta / 2, theta]`. -/
theorem p20_t1_power_two_row_scaling {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (fmax Fmax : ℝ)
    (hm : 0 < m) (hn : 0 < n)
    (hfmax : 0 < fmax) (hFmax : 0 < Fmax)
    (hrow : ∀ i : Fin m, 0 < p20InfNormVec (A i)) :
    let theta := p20ScalingThreshold n fmax Fmax
    (∀ i : Fin m,
        p20IsPowerOfTwo (p20RowScaleFactor theta (A i)) ∧
          0 < p20RowScaleFactor theta (A i) ∧
          theta / (2 * p20InfNormVec (A i)) <
            p20RowScaleFactor theta (A i) ∧
          p20RowScaleFactor theta (A i) ≤
            theta / p20InfNormVec (A i)) ∧
      (∀ i : Fin m, ∀ j : Fin n,
        |p20LeftScaledMatrix theta A i j| ≤ theta) ∧
      ∀ i : Fin m, ∃ j : Fin n,
        theta / 2 < |p20LeftScaledMatrix theta A i j| := by
  -- PROOF_START
  sorry

end HighamBench
