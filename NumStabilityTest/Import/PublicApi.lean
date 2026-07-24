import NumStability.Analysis.Error
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.FloatingPoint

/-!
# Public API smoke test

These type ascriptions intentionally record a small, stable cross-section of
the reusable API.  A declaration rename or an incompatible signature change
must therefore be acknowledged by updating this test.
-/

namespace NumStabilityTest.PublicApi

open NumStability

noncomputable section

example : Type := FPModel

example : BasicOp := BasicOp.add

example : IeeeValue → IeeeValue → IeeeValue := ieeeNaiveMax

example : ℝ → ℝ → ℝ := absError

example : ℝ → ℝ → ℝ := relError

example : (fp : FPModel) → (n : ℕ) → (Fin n → ℝ) → ℝ :=
  fl_recursiveSum

example (fp : FPModel) : 0 ≤ fp.u := fp.u_nonneg

example : absError 3 3 = 0 := by
  simp [absError]

end

end NumStabilityTest.PublicApi
