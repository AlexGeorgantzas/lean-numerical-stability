import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Analysis.MatrixAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open scoped BigOperators
open NumStability

/-- The source's shifted Algorithm 4.1, including all exponential evaluations,
the denominator sum with the chosen maximum omitted, and final divisions. -/
structure ShiftedSoftmaxRun {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (u : ℝ) where
  fp : FPModel
  unit_eq : fp.u = u
  subtractError : Fin (m + 1) → ℝ
  subtractError_le : ∀ i, |subtractError i| ≤ u
  expError : Fin (m + 1) → ℝ
  expError_le : ∀ i, |expError i| ≤ u

noncomputable def maxValue {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) : ℝ := x (π (Fin.last m))

noncomputable def exactShiftedSum {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) : ℝ :=
  ∑ i : Fin m, Real.exp (x (π i.castSucc) - maxValue x π)

noncomputable def computedShiftedTerm {m : ℕ}
    {x : Fin (m + 1) → ℝ} {π : Equiv.Perm (Fin (m + 1))} {u : ℝ}
    (run : ShiftedSoftmaxRun x π u) (j : Fin (m + 1)) : ℝ :=
  Real.exp ((x j - maxValue x π) * (1 + run.subtractError j)) *
    (1 + run.expError j)

noncomputable def computedShiftedSum {m : ℕ}
    {x : Fin (m + 1) → ℝ} {π : Equiv.Perm (Fin (m + 1))} {u : ℝ}
    (run : ShiftedSoftmaxRun x π u) : ℝ :=
  fl_recursiveSum run.fp m (fun i => computedShiftedTerm run (π i.castSucc))

noncomputable def exactSoftmax {m : ℕ} (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) : ℝ :=
  Real.exp (x j - maxValue x π) / (1 + exactShiftedSum x π)

/-- Equation (4.11) treats the denominator 1+computed sum as an exact
real construction; the final division itself is rounded by `FPModel`. -/
noncomputable def computedSoftmax {m : ℕ}
    {x : Fin (m + 1) → ℝ} {π : Equiv.Perm (Fin (m + 1))} {u : ℝ}
    (run : ShiftedSoftmaxRun x π u) (j : Fin (m + 1)) : ℝ :=
  run.fp.fl_div (computedShiftedTerm run j) (1 + computedShiftedSum run)

/-- Blanchard--Higham--Higham Theorem 4.3, equation (4.11). -/
theorem target {m : ℕ} (hm : 0 < m) (x : Fin (m + 1) → ℝ)
    (π : Equiv.Perm (Fin (m + 1)))
    (hmax : ∀ i, x i ≤ maxValue x π) :
    ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧
      ∀ (u : ℝ), 0 < u → u ≤ u₀ →
        ∀ (run : ShiftedSoftmaxRun x π u),
          (∀ j,
            |computedSoftmax run j - exactSoftmax x π j| ≤
              (((m + 1 : ℝ) + 2 +
                  2 * infNormVec (fun i : Fin (m + 1) => maxValue x π - x i)) * u +
                C * u ^ 2) * |exactSoftmax x π j|) ∧
          infNormVec (fun j => computedSoftmax run j - exactSoftmax x π j) /
              infNormVec (exactSoftmax x π) ≤
            ((m + 1 : ℝ) + 2 +
              2 * infNormVec (fun i : Fin (m + 1) => maxValue x π - x i)) * u +
              C * u ^ 2 := by
  sorry

end HighamBenchCandidate
