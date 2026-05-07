import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def templatesResidualAllowance (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) (i : Fin n) : ℝ :=
  |fl_residual fp n A x b i| +
    gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x j|)

theorem templates_residual_stop_forward_error
    (fp : FPModel) (n : ℕ) (hnpos : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x xhat b : Fin n → ℝ)
    (residualTol stopTol : ℝ)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hresidualTol_nonneg : 0 ≤ residualTol)
    (hcert : ∀ i : Fin n,
      templatesResidualAllowance fp n A xhat b i ≤ residualTol)
    (hstop :
      infNorm hnpos A_inv * residualTol ≤
        stopTol * infNormVec hnpos xhat) :
    infNormVec hnpos (fun i => x i - xhat i) ≤
      stopTol * infNormVec hnpos xhat := by
  sorry

end LeanFpAnalysis.FP
