import NumStability.Algorithms.Summation.Recursive.Core
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open scoped BigOperators
open NumStability

/-- The shifted, nonmaximal positive exponential sum from Algorithm 4.1. -/
structure ShiftedWeightedRun {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (u : ℝ) where
  fp : FPModel
  unit_eq : fp.u = u
  subtractError : Fin m → ℝ
  subtractError_le : ∀ i, |subtractError i| ≤ u
  expError : Fin m → ℝ
  expError_le : ∀ i, |expError i| ≤ u

noncomputable def maxValue {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) : ℝ := x (π (Fin.last m))

noncomputable def exactTerm {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (i : Fin m) : ℝ :=
  Real.exp (x (π i.castSucc) - maxValue x π)

noncomputable def computedTerm {m : ℕ} {x : Fin (m + 1) → ℝ}
    {π : Equiv.Perm (Fin (m + 1))} {u : ℝ}
    (run : ShiftedWeightedRun x π u) (i : Fin m) : ℝ :=
  Real.exp ((x (π i.castSucc) - maxValue x π) *
      (1 + run.subtractError i)) * (1 + run.expError i)

noncomputable def exactSum {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) : ℝ :=
  ∑ i : Fin m, exactTerm x π i

noncomputable def computedSum {m : ℕ} {x : Fin (m + 1) → ℝ}
    {π : Equiv.Perm (Fin (m + 1))} {u : ℝ}
    (run : ShiftedWeightedRun x π u) : ℝ :=
  fl_recursiveSum run.fp m (computedTerm run)

/-- Equation (4.5) retains each term's input value and its exact position
in the recursive summation, unlike the coarser equation (4.6). -/
theorem target {m : ℕ} (hm : 0 < m) (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1)))
    (hmax : ∀ i, x i ≤ maxValue x π) :
    ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧
      ∀ (u : ℝ), 0 < u → u ≤ u₀ →
        ∀ (run : ShiftedWeightedRun x π u),
          |computedSum run - exactSum x π| ≤
            u * (∑ i : Fin m,
              ((1 + maxValue x π - x (π i.castSucc)) +
                  ((m - i.val : ℕ) : ℝ)) * exactTerm x π i) +
              C * u ^ 2 := by
  sorry

end HighamBenchCandidate
