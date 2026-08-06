import HighamBench.P20Definitions

namespace HighamBench

/-- P20-T3: exact comparison of the narrow-range multiword envelope (4.32)
with the range-unrestricted envelope (4.33), including equality and strictness
certificates for the two added underflow terms. -/
theorem p20_t3_multiword_narrow_range_gap {m n q p : ℕ}
    (u U theta gmin Gmin : ℝ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin q → ℝ)
    (hu : 0 ≤ u) (hgmin : 0 ≤ gmin) (hGmin : 0 ≤ Gmin)
    (htheta : 0 < theta) :
    let rangeFree :=
      p20NormwiseEnvelope (p20MultiRangeFreeCoefficient n p u U) A B
    let inputUnderflow :=
      p20NormwiseEnvelope
        (p20MultiInputUnderflowCoefficient n p u theta gmin) A B
    let accumUnderflow :=
      p20NormwiseEnvelope
        (p20MultiAccumUnderflowCoefficient n p theta Gmin) A B
    let narrowRange :=
      p20NormwiseEnvelope
        (p20MultiNarrowCoefficient n p u U theta gmin Gmin) A B
    rangeFree ≤ narrowRange ∧
      narrowRange = rangeFree + inputUnderflow + accumUnderflow ∧
      (narrowRange = rangeFree ↔
        inputUnderflow = 0 ∧ accumUnderflow = 0) ∧
      ((0 < inputUnderflow ∨ 0 < accumUnderflow) →
        rangeFree < narrowRange) := by
  -- PROOF_START
  sorry

end HighamBench
