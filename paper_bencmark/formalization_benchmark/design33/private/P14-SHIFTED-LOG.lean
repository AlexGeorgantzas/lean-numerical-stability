import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Analysis.MatrixAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open scoped BigOperators
open NumStability

/-- The nonmaximal exponential terms of Algorithm 4.1 are evaluated after a
rounded subtraction, then recursively summed. -/
structure ShiftedLogSumRun {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (u : ℝ) where
  fp : FPModel
  unit_eq : fp.u = u
  subtractError : Fin m → ℝ
  subtractError_le : ∀ i, |subtractError i| ≤ u
  expError : Fin m → ℝ
  expError_le : ∀ i, |expError i| ≤ u
  logError : ℝ
  logError_le : |logError| ≤ u

noncomputable def maxValue {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) : ℝ := x (π (Fin.last m))

noncomputable def exactShiftedTerm {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (i : Fin m) : ℝ :=
  Real.exp (x (π i.castSucc) - maxValue x π)

noncomputable def computedShiftedTerm {m : ℕ} {x : Fin (m + 1) → ℝ}
    {π : Equiv.Perm (Fin (m + 1))} {u : ℝ}
    (run : ShiftedLogSumRun x π u) (i : Fin m) : ℝ :=
  Real.exp ((x (π i.castSucc) - maxValue x π) *
      (1 + run.subtractError i)) * (1 + run.expError i)

noncomputable def exactShiftedSum {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) : ℝ :=
  ∑ i : Fin m, exactShiftedTerm x π i

noncomputable def computedShiftedSum {m : ℕ} {x : Fin (m + 1) → ℝ}
    {π : Equiv.Perm (Fin (m + 1))} {u : ℝ}
    (run : ShiftedLogSumRun x π u) : ℝ :=
  fl_recursiveSum run.fp m (computedShiftedTerm run)

noncomputable def exactShiftedLog {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) : ℝ :=
  maxValue x π + Real.log (1 + exactShiftedSum x π)

/-- This is the intermediate computed expression in equation (4.8), before
the paper's final rounded addition, which that equation explicitly ignores. -/
noncomputable def computedShiftedLogIntermediate {m : ℕ}
    {x : Fin (m + 1) → ℝ} {π : Equiv.Perm (Fin (m + 1))} {u : ℝ}
    (run : ShiftedLogSumRun x π u) : ℝ :=
  maxValue x π + Real.log (1 + computedShiftedSum run) * (1 + run.logError)

/-- Blanchard--Higham--Higham, equation (4.8), the absolute first-order
bound for the shifted log-sum-exp intermediate. -/
theorem target {m : ℕ} (hm : 0 < m) (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1)))
    (hmax : ∀ i, x i ≤ maxValue x π) :
    ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧
      ∀ (u : ℝ), 0 < u → u ≤ u₀ →
        ∀ (run : ShiftedLogSumRun x π u),
          0 < 1 + computedShiftedSum run ∧
          |computedShiftedLogIntermediate run - exactShiftedLog x π| ≤
            (Real.log (1 + exactShiftedSum x π) +
              exactShiftedSum x π / (1 + exactShiftedSum x π) *
                ((m + 1 : ℝ) +
                  infNormVec (fun i : Fin (m + 1) => maxValue x π - x i))) * u +
              C * u ^ 2 := by
  sorry

end HighamBenchCandidate
