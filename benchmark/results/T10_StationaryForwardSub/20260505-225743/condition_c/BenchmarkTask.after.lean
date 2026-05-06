import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem stationary_forwardSub_residual_bound (fp : FPModel) (n : ℕ) (hnpos : 0 < n)
    (A M N Minv : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (xhat : ℕ → Fin n → ℝ)
    (q μ : ℝ) (m : ℕ)
    (hS : SplittingSpec n A M N Minv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hMdiag : ∀ i, M i i ≠ 0)
    (hMLT : ∀ i j : Fin n, i.val < j.val → M i j = 0)
    (hgamma : gammaValid fp n)
    (hstep : ∀ k,
      xhat (k + 1) =
        fl_forwardSub fp n M
          (fun i => ∑ j : Fin n, N i j * xhat k j + b i))
    (hq_nonneg : 0 ≤ q)
    (hq_lt_one : q < 1)
    (hH : infNorm hnpos (dualIterMatrix n N Minv) ≤ q)
    (hμ_nonneg : 0 ≤ μ)
    (hlocal : ∀ k,
      infNormVec hnpos
        (fun i => gamma fp n * ∑ j : Fin n, |M i j| * |xhat (k + 1) j|)
        ≤ μ) :
    infNormVec hnpos (fun i => b i - ∑ j : Fin n, A i j * xhat (m + 1) j) ≤
      q ^ (m + 1) *
        infNormVec hnpos (fun i => b i - ∑ j : Fin n, A i j * xhat 0 j) +
      μ * infNorm hnpos (matSub_id n (dualIterMatrix n N Minv)) / (1 - q) := by
  let ξ : ℕ → Fin n → ℝ := fun k i =>
    ∑ j : Fin n, M i j * xhat (k + 1) j -
      (∑ j : Fin n, N i j * xhat k j + b i)
  have hIter : ComputedIteration n M N b xhat ξ := by
    refine ⟨?_⟩
    intro k i
    dsimp [ξ]
    ring
  have hξ_bound : ∀ k, infNormVec hnpos (ξ k) ≤ μ := by
    intro k
    have hbwd := forwardSub_backward_error fp n M
      (fun i => ∑ j : Fin n, N i j * xhat k j + b i) hMdiag hMLT hgamma
    obtain ⟨ΔM, hΔM_bound, hΔM_eq⟩ := hbwd
    have hxstep : xhat (k + 1) =
        fl_forwardSub fp n M
          (fun i => ∑ j : Fin n, N i j * xhat k j + b i) := hstep k
    have hξ_abs : ∀ i, |ξ k i| ≤
        gamma fp n * ∑ j : Fin n, |M i j| * |xhat (k + 1) j| := by
      intro i
      have hΔeq :
          ∑ j : Fin n, ΔM i j * xhat (k + 1) j =
            (∑ j : Fin n, N i j * xhat k j + b i) -
              ∑ j : Fin n, M i j * xhat (k + 1) j := by
        have hi := hΔM_eq i
        rw [← hxstep] at hi
        calc
          ∑ j : Fin n, ΔM i j * xhat (k + 1) j
              = ∑ j : Fin n, (M i j + ΔM i j) * xhat (k + 1) j -
                  ∑ j : Fin n, M i j * xhat (k + 1) j := by
                rw [← Finset.sum_sub_distrib]
                congr 1
                ext j
                ring
          _ = (∑ j : Fin n, N i j * xhat k j + b i) -
                ∑ j : Fin n, M i j * xhat (k + 1) j := by
                rw [hi]
      calc
        |ξ k i| ≤ |∑ j : Fin n, ΔM i j * xhat (k + 1) j| := by
          have hξ_eq : ξ k i = -(∑ j : Fin n, ΔM i j * xhat (k + 1) j) := by
            dsimp [ξ]
            rw [hΔeq]
            ring
          rw [hξ_eq, abs_neg]
        _ ≤ ∑ j : Fin n, |ΔM i j * xhat (k + 1) j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |ΔM i j| * |xhat (k + 1) j| := by
          congr 1
          ext j
          exact abs_mul _ _
        _ ≤ ∑ j : Fin n, (gamma fp n * |M i j|) * |xhat (k + 1) j| := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hΔM_bound i j) (abs_nonneg _)
        _ = gamma fp n * ∑ j : Fin n, |M i j| * |xhat (k + 1) j| := by
          rw [Finset.mul_sum]
          congr 1
          ext j
          ring
    calc
      infNormVec hnpos (ξ k)
          ≤ infNormVec hnpos
              (fun i => gamma fp n * ∑ j : Fin n, |M i j| * |xhat (k + 1) j|) := by
            unfold infNormVec
            apply Finset.sup'_le
            intro i _
            calc
              |ξ k i| ≤ gamma fp n * ∑ j : Fin n, |M i j| * |xhat (k + 1) j| :=
                hξ_abs i
              _ = |(gamma fp n * ∑ j : Fin n, |M i j| * |xhat (k + 1) j|)| := by
                rw [abs_of_nonneg]
                exact mul_nonneg (gamma_nonneg fp hgamma)
                  (Finset.sum_nonneg (fun j _ =>
                    mul_nonneg (abs_nonneg _) (abs_nonneg _)))
              _ ≤ Finset.univ.sup'
                  (⟨⟨0, hnpos⟩, Finset.mem_univ _⟩ :
                    (Finset.univ : Finset (Fin n)).Nonempty)
                  (fun i : Fin n =>
                    |(gamma fp n * ∑ j : Fin n, |M i j| * |xhat (k + 1) j|)|) :=
                Finset.le_sup'
                  (fun i : Fin n =>
                    |(gamma fp n * ∑ j : Fin n, |M i j| * |xhat (k + 1) j|)|)
                  (Finset.mem_univ i)
      _ ≤ μ := hlocal k
  exact normwise_residual_bound n hnpos A M N Minv hS b x hAx xhat ξ hIter
    q hq_nonneg hq_lt_one hH μ hμ_nonneg hξ_bound m

end LeanFpAnalysis.FP
