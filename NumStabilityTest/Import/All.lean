import NumStability.All

/-!
# Complete-tree entry-point smoke test

The explicit `All` entry point must retain reusable algorithms as well as the
source-correspondence corpus.
-/

namespace NumStabilityTest.All

noncomputable section

example :
    (fp : NumStability.FPModel) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
  NumStability.fl_recursiveSum

#check NumStability.higham14_hadamardConditionNumberRaw_negative_one_counterexample

end

end NumStabilityTest.All
