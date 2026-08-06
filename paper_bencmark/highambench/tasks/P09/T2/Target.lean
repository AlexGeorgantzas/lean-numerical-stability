import HighamBench.P09Definitions

namespace HighamBench

/-- P09-T2: the backward-error construction on the final page, written for
the normalized real-equivalent Fourier action `Q` and scale `s = sqrt N`. -/
theorem p09_t2_scaled_orthogonal_backward_error
    {n : ℕ} (Q : Fin n → Fin n → ℝ) (e : Fin n → ℝ) (s : ℝ)
    (hs : 0 < s) (hQ : p09Orthogonal Q) :
    ∃ δ : Fin n → ℝ,
      p09MatVec (p09ScaleMatrix s Q) δ = e ∧
      p09VecNorm2 δ = p09VecNorm2 e / s ∧
      p09Max δ ≤ p09VecNorm2 δ := by
  -- PROOF_START
  sorry

end HighamBench
