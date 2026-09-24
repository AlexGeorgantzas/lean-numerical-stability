import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Analysis.MatrixAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open scoped BigOperators
open NumStability

/-- A permutation puts the selected maximum last, exactly as the paper does
for notational convenience. All remaining entries retain the chosen order. -/
structure ShiftedSumRun {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (u : ℝ) where
  fp : FPModel
  unit_eq : fp.u = u
  max_last : ∀ i, x i ≤ x (π (Fin.last m))
  subtractError : Fin m → ℝ
  subtractError_le : ∀ i, |subtractError i| ≤ u
  expError : Fin m → ℝ
  expError_le : ∀ i, |expError i| ≤ u

noncomputable def maxValue {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) : ℝ := x (π (Fin.last m))

noncomputable def exactShiftedTerm {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (i : Fin m) : ℝ :=
  Real.exp (x (π i.castSucc) - maxValue x π)

noncomputable def computedShiftedTerm {m : ℕ} {x : Fin (m + 1) → ℝ}
    {π : Equiv.Perm (Fin (m + 1))} {u : ℝ}
    (run : ShiftedSumRun x π u) (i : Fin m) : ℝ :=
  Real.exp ((x (π i.castSucc) - maxValue x π) *
      (1 + run.subtractError i)) * (1 + run.expError i)

noncomputable def exactShiftedSum {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) : ℝ :=
  ∑ i : Fin m, exactShiftedTerm x π i

noncomputable def computedShiftedSum {m : ℕ} {x : Fin (m + 1) → ℝ}
    {π : Equiv.Perm (Fin (m + 1))} {u : ℝ}
    (run : ShiftedSumRun x π u) : ℝ :=
  fl_recursiveSum run.fp m (computedShiftedTerm run)

/-- Blanchard--Higham--Higham equation (4.6), with `m+1` paper inputs and
one maximal input omitted from the rounded sum. -/
theorem target {m : ℕ} (hm : 0 < m) (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1)))
    (hmax : ∀ i, x i ≤ maxValue x π) :
    ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧
      ∀ (u : ℝ), 0 < u → u ≤ u₀ →
        ∀ (run : ShiftedSumRun x π u),
          0 < exactShiftedSum x π ∧
          |computedShiftedSum run - exactShiftedSum x π| /
              exactShiftedSum x π ≤
            ((m + 1 : ℝ) +
                infNormVec (fun i : Fin (m + 1) => maxValue x π - x i)) * u +
              C * u ^ 2 := by
  sorry

end HighamBenchCandidate
