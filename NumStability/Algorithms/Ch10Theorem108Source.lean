import NumStability.Algorithms.HighamChapter10
import NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.LiteralSource

/-!
# Ch10Theorem108Source (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Ch10Theorem108Source`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace NumStability

/-- The displayed perturbed factor is not merely a witness: it is the unique
positive-diagonal Cholesky factor required by the source. -/
theorem higham10_8_counterRhat_unique
    (S : Fin 2 → Fin 2 → ℝ)
    (hS : CholeskyFactSpec 2 higham10_8_counterAplus S) :
    ∀ i j : Fin 2, S i j = higham10_8_counterRhat i j :=
  higham10_1_cholesky_uniqueness 2 higham10_8_counterAplus S
    higham10_8_counterRhat hS higham10_8_counterRhat_cholesky

end NumStability

end
