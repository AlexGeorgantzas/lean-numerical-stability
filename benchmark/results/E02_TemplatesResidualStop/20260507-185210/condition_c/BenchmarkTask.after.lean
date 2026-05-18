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
  have hresBound : ∀ i : Fin n, |residualVec n A xhat b i| ≤ residualTol := by
    intro i
    have hround := conventional_residual_error fp n A xhat b hn hn1 i
    have hcert_i := hcert i
    unfold templatesResidualAllowance at hcert_i
    unfold residualVec
    have htri :
        |b i - ∑ j : Fin n, A i j * xhat j| ≤
          |fl_residual fp n A xhat b i| +
            |fl_residual fp n A xhat b i -
              (b i - ∑ j : Fin n, A i j * xhat j)| := by
      calc
        |b i - ∑ j : Fin n, A i j * xhat j|
            = |fl_residual fp n A xhat b i +
                ((b i - ∑ j : Fin n, A i j * xhat j) -
                  fl_residual fp n A xhat b i)| := by
              congr 1
              ring
        _ ≤ |fl_residual fp n A xhat b i| +
              |fl_residual fp n A xhat b i -
                (b i - ∑ j : Fin n, A i j * xhat j)| := by
            simpa [abs_sub_comm] using
              abs_add_le (fl_residual fp n A xhat b i)
                ((b i - ∑ j : Fin n, A i j * xhat j) -
                  fl_residual fp n A xhat b i)
    calc
      |b i - ∑ j : Fin n, A i j * xhat j|
          ≤ |fl_residual fp n A xhat b i| +
              |fl_residual fp n A xhat b i -
                (b i - ∑ j : Fin n, A i j * xhat j)| := htri
      _ ≤ |fl_residual fp n A xhat b i| +
            gamma fp (n + 1) *
              (|b i| + ∑ j : Fin n, |A i j| * |xhat j|) := by
          exact add_le_add (le_refl _) hround
      _ ≤ residualTol := hcert_i
  have hfwd := forward_error_from_residual n A A_inv x xhat b hInv hAx
  have hcomp :
      ∀ i : Fin n, |x i - xhat i| ≤ infNorm hnpos A_inv * residualTol := by
    intro i
    calc
      |x i - xhat i|
          ≤ ∑ j : Fin n, |A_inv i j| * |residualVec n A xhat b j| := hfwd i
      _ ≤ ∑ j : Fin n, |A_inv i j| * residualTol := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hresBound j) (abs_nonneg _)
      _ = (∑ j : Fin n, |A_inv i j|) * residualTol := by
          rw [Finset.sum_mul]
      _ ≤ infNorm hnpos A_inv * residualTol := by
          exact mul_le_mul_of_nonneg_right
            (row_sum_le_infNorm hnpos A_inv i) hresidualTol_nonneg
  have herrNorm :
      infNormVec hnpos (fun i => x i - xhat i) ≤
        infNorm hnpos A_inv * residualTol := by
    unfold infNormVec
    apply Finset.sup'_le
    intro i _
    exact hcomp i
  exact le_trans herrNorm hstop

end LeanFpAnalysis.FP
