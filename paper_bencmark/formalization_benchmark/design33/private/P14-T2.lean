import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Analysis.MatrixAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Private admission skeleton only; never a contestant input. -/

namespace HighamBenchCandidate

open scoped BigOperators
open NumStability

/-- The unshifted basic softmax execution from Algorithm 3.1: rounded
exponentials, recursive denominator summation, and rounded divisions. -/
structure BasicSoftmaxRun {n : ℕ} (x : Fin n → ℝ) (u : ℝ) where
  fp : FPModel
  unit_eq : fp.u = u
  expError : Fin n → ℝ
  expError_le : ∀ i, |expError i| ≤ u

noncomputable def exactExpSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, Real.exp (x i)

noncomputable def exactSoftmax {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.exp (x j) / exactExpSum x

noncomputable def computedExp {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : BasicSoftmaxRun x u) (i : Fin n) : ℝ :=
  Real.exp (x i) * (1 + run.expError i)

noncomputable def computedDenominator {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : BasicSoftmaxRun x u) : ℝ :=
  fl_recursiveSum run.fp n (computedExp run)

noncomputable def computedSoftmax {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : BasicSoftmaxRun x u) (j : Fin n) : ℝ :=
  run.fp.fl_div (computedExp run j) (computedDenominator run)

/-- Blanchard--Higham--Higham, Theorem 3.3 and its preceding componentwise
bound. `C` and `u₀` are uniform over admissible runs at fixed `n,x`, which
gives the mathematical content of the printed O(u²). -/
theorem target {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧
      ∀ (u : ℝ), 0 < u → u ≤ u₀ →
        ∀ (run : BasicSoftmaxRun x u),
          (∀ j,
            |computedSoftmax run j - exactSoftmax x j| ≤
              ((n + 3 : ℝ) * u + C * u ^ 2) * |exactSoftmax x j|) ∧
          infNormVec (fun j => computedSoftmax run j - exactSoftmax x j) /
              infNormVec (exactSoftmax x) ≤
                (n + 3 : ℝ) * u + C * u ^ 2 := by
  sorry

end HighamBenchCandidate
