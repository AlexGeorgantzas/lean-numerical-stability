import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem forwardSub_residual_certificate (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : gammaValid fp n) :
    let xhat := fl_forwardSub fp n L b
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, L i j * xhat j| ≤
        gamma fp n * ∑ j : Fin n, |L i j| * |xhat j| := by
  sorry

end LeanFpAnalysis.FP
