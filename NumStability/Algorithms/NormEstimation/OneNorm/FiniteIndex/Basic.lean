import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Algorithms NormEstimation OneNorm FiniteIndex Basic

Canonical destination for material split out of
`NumStability.Algorithms.CondEstimation` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Standard basis vector e_j. -/
noncomputable def basisVec {n : ℕ} (j : Fin n) : Fin n → ℝ :=
  fun i => if i = j then 1 else 0

/-- Index achieving the maximum of |z_j| over Fin n. -/
noncomputable def argmaxAbs {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) : Fin n :=
  (Finset.exists_max_image Finset.univ (fun j => |z j|)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩).choose

/-- The argmax achieves the maximum. -/
lemma argmaxAbs_spec {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    ∀ j : Fin n, |z j| ≤ |z (argmaxAbs hn z)| := by
  intro j
  exact ((Finset.exists_max_image Finset.univ (fun j => |z j|)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩).choose_spec.2 j (Finset.mem_univ j))

end NumStability
