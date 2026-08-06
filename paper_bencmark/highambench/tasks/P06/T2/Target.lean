import HighamBench.P06Definitions

namespace HighamBench

/-- P06-T2: equation (3.4), expressed by equality of all nonnegative norm
thresholds. Rectangular operator control is equivalent to the scalar-identity
Loewner bound for the symmetric dilation. -/
theorem p06_t2_self_adjoint_dilation_norm_bridge
    {m n : ℕ} (M : Fin m → Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    p06RectOpNorm2Le M L ↔
      p06FiniteLoewnerLe (p06SelfAdjointDilation M)
        (fun a b : Fin m ⊕ Fin n ↦ L * p06FiniteId a b) := by
  -- PROOF_START
  sorry

end HighamBench
