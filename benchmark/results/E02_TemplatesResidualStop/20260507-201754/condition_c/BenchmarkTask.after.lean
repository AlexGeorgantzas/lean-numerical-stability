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
  have hcomp := conventional_residual_error fp n A xhat b hn hn1
  have hres_bound : ∀ i : Fin n, |residualVec n A xhat b i| ≤ residualTol := by
    intro i
    have htri :
        |residualVec n A xhat b i| ≤
          |fl_residual fp n A xhat b i| +
            |fl_residual fp n A xhat b i - residualVec n A xhat b i| := by
      have hEq :
          residualVec n A xhat b i =
            fl_residual fp n A xhat b i -
              (fl_residual fp n A xhat b i - residualVec n A xhat b i) := by
        ring
      calc
        |residualVec n A xhat b i|
            = |fl_residual fp n A xhat b i -
                (fl_residual fp n A xhat b i - residualVec n A xhat b i)| :=
                congrArg abs hEq
        _ ≤ |fl_residual fp n A xhat b i| +
              |0 - (fl_residual fp n A xhat b i - residualVec n A xhat b i)| := by
                simpa [sub_zero] using
                  (abs_sub_le (fl_residual fp n A xhat b i) 0
                    (fl_residual fp n A xhat b i - residualVec n A xhat b i))
        _ = |fl_residual fp n A xhat b i| +
              |fl_residual fp n A xhat b i - residualVec n A xhat b i| :=
                by rw [zero_sub, abs_neg]
    have hresidual_eq :
        b i - ∑ j : Fin n, A i j * xhat j = residualVec n A xhat b i := by
      rfl
    have hcomp_i :
        |fl_residual fp n A xhat b i - residualVec n A xhat b i| ≤
          gamma fp (n + 1) *
            (|b i| + ∑ j : Fin n, |A i j| * |xhat j|) := by
      simpa [hresidual_eq] using hcomp i
    calc
      |residualVec n A xhat b i|
          ≤ |fl_residual fp n A xhat b i| +
              |fl_residual fp n A xhat b i - residualVec n A xhat b i| := htri
      _ ≤ |fl_residual fp n A xhat b i| +
            gamma fp (n + 1) *
              (|b i| + ∑ j : Fin n, |A i j| * |xhat j|) := by
            exact add_le_add (le_refl _) hcomp_i
      _ = templatesResidualAllowance fp n A xhat b i := by
            rfl
      _ ≤ residualTol := hcert i
  have hfwd := forward_error_from_residual n A A_inv x xhat b hInv hAx
  have hpoint : ∀ i : Fin n, |x i - xhat i| ≤ infNorm hnpos A_inv * residualTol := by
    intro i
    calc
      |x i - xhat i|
          ≤ ∑ j : Fin n, |A_inv i j| * |residualVec n A xhat b j| := hfwd i
      _ ≤ ∑ j : Fin n, |A_inv i j| * residualTol := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left (hres_bound j) (abs_nonneg _)
      _ = (∑ j : Fin n, |A_inv i j|) * residualTol := by
            rw [Finset.sum_mul]
      _ ≤ infNorm hnpos A_inv * residualTol := by
            exact mul_le_mul_of_nonneg_right (row_sum_le_infNorm hnpos A_inv i)
              hresidualTol_nonneg
  have hnorm : infNormVec hnpos (fun i => x i - xhat i) ≤
      infNorm hnpos A_inv * residualTol := by
    unfold infNormVec
    exact Finset.sup'_le _ _ (fun i _ => hpoint i)
  exact le_trans hnorm hstop

end LeanFpAnalysis.FP
