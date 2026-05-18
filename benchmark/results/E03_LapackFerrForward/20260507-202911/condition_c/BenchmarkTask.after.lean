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
  have hres_comp := conventional_residual_error fp n A xhat b hn hn1
  have hres_bound : ∀ i : Fin n,
      |residualVec n A xhat b i| ≤ lapackFerrDenom fp n A xhat b i := by
    intro i
    unfold lapackFerrDenom residualVec
    have hcomp := hres_comp i
    calc |b i - ∑ j : Fin n, A i j * xhat j|
        = |fl_residual fp n A xhat b i +
            ((b i - ∑ j : Fin n, A i j * xhat j) -
              fl_residual fp n A xhat b i)| := by
            congr 1
            ring
      _ ≤ |fl_residual fp n A xhat b i| +
            |(b i - ∑ j : Fin n, A i j * xhat j) -
              fl_residual fp n A xhat b i| := abs_add_le _ _
      _ = |fl_residual fp n A xhat b i| +
            |fl_residual fp n A xhat b i -
              (b i - ∑ j : Fin n, A i j * xhat j)| := by
            rw [abs_sub_comm]
      _ ≤ |fl_residual fp n A xhat b i| +
            gamma fp (n + 1) *
              (|b i| + ∑ j : Fin n, |A i j| * |xhat j|) := by
            exact add_le_add (le_refl _) hcomp
  have hpoint : ∀ i : Fin n,
      |x i - xhat i| ≤ lapackFerrNumerator fp n A A_inv xhat b i := by
    have hfwd := forward_error_from_residual n A A_inv x xhat b hInv hAx
    intro i
    calc |x i - xhat i|
        ≤ ∑ j : Fin n, |A_inv i j| * |residualVec n A xhat b j| := hfwd i
      _ ≤ ∑ j : Fin n, |A_inv i j| * lapackFerrDenom fp n A xhat b j := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hres_bound j) (abs_nonneg _)
      _ = lapackFerrNumerator fp n A A_inv xhat b i := by
          rfl
  have hnorm : infNormVec hnpos (fun i => x i - xhat i) ≤
      infNormVec hnpos (lapackFerrNumerator fp n A A_inv xhat b) := by
    unfold infNormVec
    apply Finset.sup'_le
    intro i _
    exact le_trans (hpoint i) (le_trans (le_abs_self _)
      (Finset.le_sup'
        (fun i => |lapackFerrNumerator fp n A A_inv xhat b i|)
        (Finset.mem_univ i)))
  unfold lapackFerrBound
  exact div_le_div_of_nonneg_right hnorm (le_of_lt hxhat_norm_pos)

end LeanFpAnalysis.FP
