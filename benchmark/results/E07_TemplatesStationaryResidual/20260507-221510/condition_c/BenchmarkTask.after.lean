import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def stationaryLocalError (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (xhat : ℕ → Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, M i j * xhat (k + 1) j -
    (∑ j : Fin n, N i j * xhat k j + b i)

theorem templates_stationary_iteration_residual_bound
    (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ) (b x : Fin n → ℝ)
    (xhat : ℕ → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (q : ℝ) (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1)
    (hH : infNorm hn (dualIterMatrix n N M_inv) ≤ q)
    (mu : ℝ) (hmu_nonneg : 0 ≤ mu)
    (hlocal :
      ∀ k, infNormVec hn (stationaryLocalError n M N b xhat k) ≤ mu) :
    ∀ m : ℕ,
      infNormVec hn (fun i => b i - ∑ j : Fin n, A i j * xhat (m + 1) j) ≤
        q ^ (m + 1) *
            infNormVec hn (fun i => b i - ∑ j : Fin n, A i j * xhat 0 j) +
          mu * infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) / (1 - q) := by
  let ξ : ℕ → Fin n → ℝ := stationaryLocalError n M N b xhat
  have hIter : ComputedIteration n M N b xhat ξ := by
    refine ⟨?_⟩
    intro k i
    dsimp [ξ, stationaryLocalError]
    ring
  exact normwise_residual_bound n hn A M N M_inv hS b x hAx xhat ξ hIter
    q hq_nonneg hq_lt_one hH mu hmu_nonneg hlocal

end LeanFpAnalysis.FP
