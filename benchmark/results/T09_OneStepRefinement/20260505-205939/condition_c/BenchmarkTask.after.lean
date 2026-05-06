import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem one_step_refinement_conventional_residual (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b x0 dhat : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (μ : ℝ)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (hμ_nonneg : 0 ≤ μ)
    (hΔ : ∀ i j, |ΔA i j| ≤ μ * |A i j|)
    (hsolve : ∀ i,
      ∑ j : Fin n, (A i j + ΔA i j) * dhat j =
        fl_residual fp n A x0 b i) :
    let x1 := fun i => x0 i + dhat i
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x1 j| ≤
        μ * ∑ j : Fin n, |A i j| * |dhat j| +
        gamma fp (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x0 j|) := by
  dsimp
  intro i
  let r : Fin n → ℝ := fun i => b i - ∑ j : Fin n, A i j * x0 j
  let rhat : Fin n → ℝ := fl_residual fp n A x0 b
  let ω : Fin n → ℝ :=
    fun i => gamma fp (n + 1) *
      (|b i| + ∑ j : Fin n, |A i j| * |x0 j|)
  have hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x0 j := by
    intro i
    rfl
  have hres : ∀ i, |rhat i - r i| ≤ (0 : ℝ) * |r i| + ω i := by
    intro i
    have h :=
      conventional_residual_error fp n A x0 b hn hn1 i
    dsimp [rhat, r, ω]
    simpa using h
  have hω_nonneg : ∀ i, 0 ≤ ω i := by
    intro i
    dsimp [ω]
    exact mul_nonneg (gamma_nonneg fp hn1)
      (add_nonneg (abs_nonneg _) (Finset.sum_nonneg
        (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  have hx1 : ∀ i : Fin n, (fun i => x0 i + dhat i) i = x0 i + dhat i := by
    intro i
    rfl
  have hbound :=
    one_step_residual_bound n A x0 dhat rhat ΔA μ 0 ω b r
      hr hres hsolve hΔ (fun i => x0 i + dhat i) hx1
      hμ_nonneg (by norm_num) hω_nonneg i
  dsimp [ω] at hbound
  simpa using hbound

end LeanFpAnalysis.FP
