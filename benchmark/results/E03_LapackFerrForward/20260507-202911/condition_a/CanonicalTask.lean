import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def lapackFerrDenom (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) (i : Fin n) : ℝ :=
  |fl_residual fp n A x b i| +
    gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x j|)

noncomputable def lapackFerrNumerator (fp : FPModel) (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j : Fin n, |A_inv i j| * lapackFerrDenom fp n A x b j

noncomputable def lapackFerrBound (fp : FPModel) (n : ℕ) (hnpos : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) : ℝ :=
  infNormVec hnpos (lapackFerrNumerator fp n A A_inv x b) /
    infNormVec hnpos x

theorem lapack_ferr_forward_error_bound
    (fp : FPModel) (n : ℕ) (hnpos : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x xhat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hxhat_norm_pos : 0 < infNormVec hnpos xhat) :
    infNormVec hnpos (fun i => x i - xhat i) /
        infNormVec hnpos xhat ≤
      lapackFerrBound fp n hnpos A A_inv xhat b := by
  sorry

end LeanFpAnalysis.FP
