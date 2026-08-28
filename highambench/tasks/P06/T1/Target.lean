import HighamBench.P06Definitions

namespace HighamBench

/-- P06-T1: the sentence preceding equation (4.20). The simultaneous
columnwise bounds (4.17), including their second-order terms, imply the
Frobenius-norm bound (4.20) with the same leading coefficient. -/
theorem p06_t1_columnwise_to_frobenius
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (DeltaA : ℝ → Fin m → Fin n → ℝ)
    (columnRemainder : Fin n → ℝ → ℝ)
    (c6 : ℕ) (lambda : ℝ) (_hc6 : 0 < c6) (hlambda : 0 < lambda)
    (hsecondOrder : ∀ j,
      p06SecondOrderAtZeroRight (columnRemainder j))
    (hcolumn :
      ∀ᶠ u in nhdsWithin 0 (Set.Ioo (0 : ℝ) 1),
        ∀ j : Fin n,
          p06VecNorm2 (fun i ↦ DeltaA u i j) ≤
            p06QRLeadingCoefficient c6 lambda m n u *
                p06VecNorm2 (fun i ↦ A i j) +
              |columnRemainder j u|) :
    ∃ normwiseRemainder : ℝ → ℝ,
      p06SecondOrderAtZeroRight normwiseRemainder ∧
        ∀ᶠ u in nhdsWithin 0 (Set.Ioo (0 : ℝ) 1),
          p06FrobNorm (DeltaA u) ≤
            p06QRLeadingCoefficient c6 lambda m n u * p06FrobNorm A +
              |normwiseRemainder u| := by
  -- PROOF_START
  sorry

end HighamBench
