import NumStability.Core

/-!
# Curated-core entry-point smoke test

This test records the foundational model and error-measure declarations that
the deliberately narrow `Core` entry point promises to expose.
-/

namespace NumStabilityTest.Core

noncomputable section

example : Type := NumStability.FPModel

example : ℝ → ℝ → ℝ := NumStability.absError

end

end NumStabilityTest.Core
