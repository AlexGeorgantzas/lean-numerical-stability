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

end

end NumStabilityTest.Root
