import NumStability.Algorithms.QR.HouseholderSpecSupport

namespace NumStability

open scoped BigOperators

/-!
# Contract

Canonical reusable module extracted without change from Higham20Theorem20_7.
-/

namespace Theorem20_7

noncomputable def rowScaleCounterA : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, _ => 0
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 1 / 2
theorem rowScaleCounter_pivot0 :
    householderActiveMaxPivotColumn (0 : Fin 2) (0 : Fin 2)
      rowScaleCounterA = 0 := by
  let q := householderActiveMaxPivotColumn (0 : Fin 2) (0 : Fin 2)
    rowScaleCounterA
  have hmax := householderActiveMaxPivotColumn_pivot_max
    (0 : Fin 2) (0 : Fin 2) rowScaleCounterA (0 : Fin 2) (by norm_num)
  change q = 0
  have hqv : q.val = 0 := by
    by_contra hne
    have hq1 : q.val = 1 := by omega
    have hqeq : q = (1 : Fin 2) := Fin.ext hq1
    change householderTrailingColumnNorm2Sq (0 : Fin 2) rowScaleCounterA 0 ≤
      householderTrailingColumnNorm2Sq (0 : Fin 2) rowScaleCounterA q at hmax
    rw [hqeq] at hmax
    norm_num [householderTrailingColumnNorm2Sq,
      householderTrailingNorm2Sq, rowScaleCounterA,
      householderTrailingPart, vecNorm2Sq] at hmax
  exact Fin.ext hqv
/-- Literal source row maximum for the two-column counterexample. -/
noncomputable def rowScaleCounterRowMax (i : Fin 2) : ℝ :=
  max |rowScaleCounterA i (0 : Fin 2)| |rowScaleCounterA i (1 : Fin 2)|
theorem rowScaleCounter_rowMax0 :
    rowScaleCounterRowMax (0 : Fin 2) = 0 := by
  simp [rowScaleCounterRowMax, rowScaleCounterA]

end Theorem20_7

end NumStability
