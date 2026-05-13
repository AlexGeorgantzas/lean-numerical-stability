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
  have hres_bound : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * xhat j| ≤
        lapackFerrDenom fp n A xhat b i := by
    intro i
    have hres :=
      conventional_residual_error fp n A xhat b hn hn1 i
    unfold lapackFerrDenom
    have htri :
        |b i - ∑ j : Fin n, A i j * xhat j| ≤
          |fl_residual fp n A xhat b i| +
            |fl_residual fp n A xhat b i -
              (b i - ∑ j : Fin n, A i j * xhat j)| := by
      calc
        |b i - ∑ j : Fin n, A i j * xhat j|
            = |fl_residual fp n A xhat b i +
                ((b i - ∑ j : Fin n, A i j * xhat j) -
                  fl_residual fp n A xhat b i)| := by ring_nf
        _ ≤ |fl_residual fp n A xhat b i| +
              |(b i - ∑ j : Fin n, A i j * xhat j) -
                fl_residual fp n A xhat b i| := abs_add_le _ _
        _ = |fl_residual fp n A xhat b i| +
              |fl_residual fp n A xhat b i -
                (b i - ∑ j : Fin n, A i j * xhat j)| := by
          rw [abs_sub_comm]
    linarith
  have hsol : ∀ i : Fin n,
      x i - xhat i =
        ∑ j : Fin n, A_inv i j *
          (b j - ∑ k : Fin n, A j k * xhat k) := by
    intro i
    have hdiff : ∀ j : Fin n,
        ∑ k : Fin n, A j k * (x k - xhat k) =
          b j - ∑ k : Fin n, A j k * xhat k := by
      intro j
      calc
        ∑ k : Fin n, A j k * (x k - xhat k)
            = (∑ k : Fin n, A j k * x k) -
                ∑ k : Fin n, A j k * xhat k := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
        _ = b j - ∑ k : Fin n, A j k * xhat k := by
          rw [hAx j]
    have key :
        ∑ j : Fin n, A_inv i j *
            (∑ k : Fin n, A j k * (x k - xhat k)) =
          ∑ j : Fin n, A_inv i j *
            (b j - ∑ k : Fin n, A j k * xhat k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hdiff j]
    have lhs_eq :
        ∑ j : Fin n, A_inv i j *
            (∑ k : Fin n, A j k * (x k - xhat k)) =
          ∑ k : Fin n, (∑ j : Fin n, A_inv i j * A j k) *
            (x k - xhat k) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [lhs_eq] at key
    have inv_eq : ∀ k : Fin n,
        (∑ j : Fin n, A_inv i j * A j k) =
          if i = k then 1 else 0 := fun k => hInv i k
    have lhs_simp :
        ∑ k : Fin n, (∑ j : Fin n, A_inv i j * A j k) *
            (x k - xhat k) =
          x i - xhat i := by
      simp_rw [inv_eq]
      simp
    rw [lhs_simp] at key
    exact key
  have hcomp : ∀ i : Fin n,
      |x i - xhat i| ≤
        lapackFerrNumerator fp n A A_inv xhat b i := by
    intro i
    rw [hsol i]
    unfold lapackFerrNumerator
    calc
      |∑ j : Fin n, A_inv i j *
          (b j - ∑ k : Fin n, A j k * xhat k)|
          ≤ ∑ j : Fin n,
              |A_inv i j *
                (b j - ∑ k : Fin n, A j k * xhat k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |A_inv i j| *
            |b j - ∑ k : Fin n, A j k * xhat k| := by
        apply Finset.sum_congr rfl
        intro j _
        exact abs_mul _ _
      _ ≤ ∑ j : Fin n, |A_inv i j| *
            lapackFerrDenom fp n A xhat b j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hres_bound j) (abs_nonneg _)
  have hdenom_nonneg : ∀ i : Fin n,
      0 ≤ lapackFerrDenom fp n A xhat b i := by
    intro i
    unfold lapackFerrDenom
    have hsum_nonneg :
        0 ≤ ∑ j : Fin n, |A i j| * |xhat j| := by
      exact Finset.sum_nonneg (fun j _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hinside_nonneg :
        0 ≤ |b i| + ∑ j : Fin n, |A i j| * |xhat j| := by
      exact add_nonneg (abs_nonneg _) hsum_nonneg
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg (gamma_nonneg fp hn1) hinside_nonneg)
  have hnum_nonneg : ∀ i : Fin n,
      0 ≤ lapackFerrNumerator fp n A A_inv xhat b i := by
    intro i
    unfold lapackFerrNumerator
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (abs_nonneg _) (hdenom_nonneg j))
  have hnorm :
      infNormVec hnpos (fun i => x i - xhat i) ≤
        infNormVec hnpos (lapackFerrNumerator fp n A A_inv xhat b) := by
    unfold infNormVec
    apply Finset.sup'_le
    intro i _
    calc
      |x i - xhat i| ≤
          lapackFerrNumerator fp n A A_inv xhat b i := hcomp i
      _ = |lapackFerrNumerator fp n A A_inv xhat b i| := by
        rw [abs_of_nonneg (hnum_nonneg i)]
      _ ≤ Finset.sup' Finset.univ
          (Finset.univ_nonempty_iff.mpr ⟨⟨0, hnpos⟩⟩)
          (fun i => |lapackFerrNumerator fp n A A_inv xhat b i|) :=
        Finset.le_sup'
          (fun i => |lapackFerrNumerator fp n A A_inv xhat b i|)
          (Finset.mem_univ i)
  unfold lapackFerrBound
  exact div_le_div_of_nonneg_right hnorm (le_of_lt hxhat_norm_pos)

end LeanFpAnalysis.FP
