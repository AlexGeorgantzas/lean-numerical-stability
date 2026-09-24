import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Analysis.MatrixAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open scoped BigOperators
open NumStability

/-- Unshifted Algorithm 3.1 followed by the alternative softmax formula (3.7).
Each transcendental/subtraction operation has its own source-model error. -/
structure AlternativeSoftmaxRun {n : ℕ} (x : Fin n → ℝ) (u : ℝ) where
  fp : FPModel
  unit_eq : fp.u = u
  inputExpError : Fin n → ℝ
  inputExpError_le : ∀ i, |inputExpError i| ≤ u
  logError : ℝ
  logError_le : |logError| ≤ u
  subtractError : Fin n → ℝ
  subtractError_le : ∀ i, |subtractError i| ≤ u
  outputExpError : Fin n → ℝ
  outputExpError_le : ∀ i, |outputExpError i| ≤ u

noncomputable def exactSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, Real.exp (x i)

noncomputable def exactLogSumExp {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.log (exactSum x)

noncomputable def exactSoftmax {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.exp (x j - exactLogSumExp x)

noncomputable def inputExp {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : AlternativeSoftmaxRun x u) (i : Fin n) : ℝ :=
  Real.exp (x i) * (1 + run.inputExpError i)

noncomputable def computedLogSumExp {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : AlternativeSoftmaxRun x u) : ℝ :=
  Real.log (fl_recursiveSum run.fp n (inputExp run)) * (1 + run.logError)

noncomputable def computedSoftmax {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : AlternativeSoftmaxRun x u) (j : Fin n) : ℝ :=
  Real.exp ((x j - computedLogSumExp run) * (1 + run.subtractError j)) *
    (1 + run.outputExpError j)

/-- Blanchard--Higham--Higham Theorem 3.4, equation (3.11), with uniform
quadratic remainder for the unshifted division-free alternative. -/
theorem target {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧
      ∀ (u : ℝ), 0 < u → u ≤ u₀ →
        ∀ (run : AlternativeSoftmaxRun x u),
          infNormVec (fun j => computedSoftmax run j - exactSoftmax x j) /
              infNormVec (exactSoftmax x) ≤
            (|exactLogSumExp x| +
                infNormVec (fun j => x j - exactLogSumExp x) +
                (n + 2 : ℝ)) * u + C * u ^ 2 := by
  sorry

end HighamBenchCandidate
