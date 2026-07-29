import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixAlgebra
import NumStability.FloatingPoint.Model

namespace NumStability

open scoped BigOperators

/-!
# NormalEquations

Canonical reusable module extracted without change from LSNormalEquations.
-/

/-- Higham, 2nd ed., Chapter 20, Section 20.4, printed p. 386:
    the 2-by-2 normal-equations cross-product example
    `A = [[1, 1], [epsilon, 0]]`. -/
noncomputable def normalEquationsCrossProductExampleA
    (epsilon : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = 0 then 1 else if j = 0 then epsilon else 0
/-- Higham, 2nd ed., Chapter 20, Section 20.4, printed p. 387:
    exact cross product for the example
    `A^T A = [[1 + epsilon^2, 1], [1, 1]]`. -/
theorem normalEquationsCrossProductExample_gram_eq (epsilon : ℝ) :
    (fun i j : Fin 2 =>
        ∑ k : Fin 2,
          normalEquationsCrossProductExampleA epsilon k i *
          normalEquationsCrossProductExampleA epsilon k j) =
      fun i j =>
        if i = 0 then
          if j = 0 then 1 + epsilon ^ 2 else 1
        else
          if j = 0 then 1 else 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [normalEquationsCrossProductExampleA]
    ring
  · norm_num [normalEquationsCrossProductExampleA]
  · norm_num [normalEquationsCrossProductExampleA]
  · norm_num [normalEquationsCrossProductExampleA]
/-- Higham, 2nd ed., Chapter 20, Section 20.4, printed p. 387:
    source model of the rounded cross product in the example,
    `fl(A^T A) = [[1, 1], [1, 1]]`. -/
noncomputable def normalEquationsCrossProductExampleRoundedGram :
    Fin 2 → Fin 2 → ℝ :=
  fun _ _ => 1
/-- The rounded cross product displayed in Higham's Section 20.4 example is
    singular, witnessed by the nonzero vector `[1, -1]`. -/
theorem normalEquationsCrossProductExampleRoundedGram_singular :
    ∃ x : Fin 2 → ℝ,
      x ≠ 0 ∧
      matMulVec 2 normalEquationsCrossProductExampleRoundedGram x = 0 := by
  refine ⟨fun i => if i = 0 then 1 else -1, ?_, ?_⟩
  · intro hx
    have h0 := congrFun hx (0 : Fin 2)
    norm_num at h0
  · ext i
    fin_cases i <;>
      norm_num [matMulVec, normalEquationsCrossProductExampleRoundedGram]
/-- Computed solution vector produced by the normal-equations Cholesky solve
    used in `ls_normal_equations_backward`. -/
noncomputable def normalEqCholeskyXHat (fp : FPModel) (n : ℕ)
    (c_hat : Fin n → ℝ) (R_hat : Fin n → Fin n → ℝ) : Fin n → ℝ :=
  fl_backSub fp n R_hat
    (fl_forwardSub fp n (fun i j : Fin n => R_hat j i) c_hat)

end NumStability
