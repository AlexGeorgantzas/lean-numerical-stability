import NumStability

/-!
# Root import compatibility smoke test

`import NumStability` historically exposes the floating-point model, analysis
definitions, and algorithms.  Keep this test while the curated `Core`,
`Higham`, and `All` entry points are introduced so that migration work does not
silently narrow the existing root import.
-/

namespace NumStabilityTest.Root

open NumStability

noncomputable section

-- Representative declarations from each of the three legacy umbrella imports.
example : Type := FPModel

example : ℝ → ℝ → ℝ := absError

example : (fp : FPModel) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
  fl_recursiveSum

#check higham14_hadamardConditionNumberRaw_negative_one_counterexample
#check fl_noGuardDotProduct
#check higham20_eq20_32_Bplus_residual_eq_crossProjection
#check problem44_outputs_exactly_Icc
#check higham17_problem17_1
#check higham26ADCrudeSweep_nondecreasing

end

end NumStabilityTest.Root
