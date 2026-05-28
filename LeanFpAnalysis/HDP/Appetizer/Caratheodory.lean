import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import LeanFpAnalysis.HDP.Geometry.Convex

/-!
# Caratheodory Theorems in the HDP Appetizer

This file records the exact and approximate Caratheodory statements used at
the start of Vershynin's HDP book.
-/

namespace LeanFpAnalysis.HDP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- HDP Theorem 0.0.1, in finite-dimensional real inner product spaces. -/
theorem caratheodory_finiteDimensional [FiniteDimensional ℝ E]
    {T : Set E} {x : E} (hx : x ∈ convexHull ℝ T) :
    ∃ U : Finset E,
      (U : Set E) ⊆ T ∧
      U.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (U : Set E) := by
  classical
  rw [convexHull_eq_union] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  rcases hx with ⟨U, hU, hAI, hxU⟩
  refine ⟨U, hU, ?_, hxU⟩
  have hcard := hAI.card_le_finrank_succ
  have hv : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : U → E))) ≤ Module.finrank ℝ E :=
    Submodule.finrank_le _
  simpa using hcard.trans (Nat.add_le_add_right hv 1)

/-- HDP Theorem 0.0.2, diameter-normalized form. Repetitions among the selected
points are represented by the function `pts : Fin k → E`. -/
theorem approximate_caratheodory_theorem_0_0_2
    {T : Set E} (hdiam : PairwiseNormBound T 1)
    {x : E} (hx : x ∈ convexHull ℝ T) {k : ℕ} (hk : 0 < k) :
    ∃ pts : Fin k → E,
      (∀ j, pts j ∈ T) ∧
      ‖x - empiricalAverage pts‖ ≤ 1 / Real.sqrt (k : ℝ) :=
  approximate_caratheodory_unit (E := E) hdiam hx hk

/-- HDP Theorem 0.0.2, with the diameter hypothesis stated using mathlib's
`Metric.diam`. The boundedness assumption is the standard side condition
needed for `Metric.diam` to control pairwise distances. -/
theorem approximate_caratheodory_of_diam_le
    {T : Set E} (hbounded : Bornology.IsBounded T) (hdiam : Metric.diam T ≤ 1)
    {x : E} (hx : x ∈ convexHull ℝ T) {k : ℕ} (hk : 0 < k) :
    ∃ pts : Fin k → E,
      (∀ j, pts j ∈ T) ∧
      ‖x - empiricalAverage pts‖ ≤ 1 / Real.sqrt (k : ℝ) := by
  exact approximate_caratheodory_unit (E := E)
    (pairwiseNormBound_of_diam_le hbounded hdiam) hx hk

end LeanFpAnalysis.HDP
