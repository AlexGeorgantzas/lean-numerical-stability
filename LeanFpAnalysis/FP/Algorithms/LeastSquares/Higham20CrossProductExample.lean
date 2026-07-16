-- Higham20CrossProductExample.lean
--
-- Executed floating-point form of the normal-equations cross-product example
-- on printed p. 387 of Higham, 2nd ed.

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import LeanFpAnalysis.FP.Algorithms.LeastSquares.LSNormalEquations

namespace LeanFpAnalysis.FP

/-- A concrete standard-model execution for the p. 387 example.  It uses
`epsilon = 1/4`, declares `u = 1/10`, and rounds the sole sensitive addition
`1 + epsilon^2` back to `1`.  Every other primitive operation is exact.

The special rounding has relative error `-1/17`, hence lies inside the declared
unit-roundoff budget.  This is an executable FPModel witness, not a separately
postulated rounded Gram matrix. -/
noncomputable def higham20CrossProductExampleFP : FPModel where
  u := 1 / 10
  u_nonneg := by norm_num
  fl_add := fun x y =>
    if x = 1 ∧ y = (1 / 16 : ℝ) then 1 else x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by
    intro x
    simp
  model_add := by
    intro x y
    by_cases h : x = 1 ∧ y = (1 / 16 : ℝ)
    · refine ⟨-1 / 17, by norm_num, ?_⟩
      change (if x = 1 ∧ y = (1 / 16 : ℝ) then 1 else x + y) =
        (x + y) * (1 + (-1 / 17))
      rw [if_pos h, h.1, h.2]
      norm_num
    · refine ⟨0, by norm_num, ?_⟩
      change (if x = 1 ∧ y = (1 / 16 : ℝ) then 1 else x + y) =
        (x + y) * (1 + 0)
      rw [if_neg h]
      ring
  model_sub := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_mul := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_div := by
    intro x y _hy
    refine ⟨0, by norm_num, by ring⟩
  model_sqrt := by
    intro x _hx
    refine ⟨0, by norm_num, by ring⟩

theorem higham20CrossProductExample_epsilon_pos : (0 : ℝ) < 1 / 4 := by
  norm_num

theorem higham20CrossProductExample_epsilon_lt_sqrt_u :
    (1 / 4 : ℝ) < Real.sqrt higham20CrossProductExampleFP.u := by
  change (1 / 4 : ℝ) < Real.sqrt (1 / 10)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 / 10 : ℝ) := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (1 / 10 : ℝ)) ^ 2 = 1 / 10 :=
    Real.sq_sqrt (by norm_num)
  nlinarith

/-- The actual `fl_matMul` path computes the all-ones Gram matrix in the
source example. -/
theorem higham20CrossProductExample_fl_gram_eq :
    fl_matMul higham20CrossProductExampleFP 2 2 2
        (fun i k => normalEquationsCrossProductExampleA (1 / 4) k i)
        (normalEquationsCrossProductExampleA (1 / 4)) =
      normalEquationsCrossProductExampleRoundedGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fl_matMul, fl_matVec, fl_dotProduct, div_eq_mul_inv,
      normalEquationsCrossProductExampleA,
      normalEquationsCrossProductExampleRoundedGram,
      higham20CrossProductExampleFP, Fin.foldl_succ] <;>
    simp <;> (intro; rfl)

/-- Consequently the matrix produced by the actual rounded product kernel is
singular, witnessed by `[1,-1]`. -/
theorem higham20CrossProductExample_fl_gram_singular :
    ∃ x : Fin 2 → ℝ,
      x ≠ 0 ∧
      matMulVec 2
        (fl_matMul higham20CrossProductExampleFP 2 2 2
          (fun i k => normalEquationsCrossProductExampleA (1 / 4) k i)
          (normalEquationsCrossProductExampleA (1 / 4))) x = 0 := by
  rw [higham20CrossProductExample_fl_gram_eq]
  exact normalEquationsCrossProductExampleRoundedGram_singular

end LeanFpAnalysis.FP
