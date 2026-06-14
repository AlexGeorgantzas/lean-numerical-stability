-- Analysis/Monotonicity.lean
--
-- Local monotonicity foundations for Higham Chapter 2, §2.9.

import Mathlib.Tactic.Linarith
import LeanFpAnalysis.FP.Analysis.FloatingPointArithmetic

namespace LeanFpAnalysis.FP

noncomputable section

namespace FloatingPointFormat

/-!
# Local monotonicity of correctly rounded adjacent rounding

Higham Chapter 2, §2.9 notes monotonicity as a useful property of correctly
rounded arithmetic.  This file proves the local adjacent-bracket foundation for
the source-facing round-to-even selector: on a fixed ordered adjacent bracket,
moving the exact real input to the right cannot move the rounded output to the
left.  This is not full IEEE operation monotonicity; it is the finite-format
rounding-policy lemma that such a theorem can reuse.
-/

theorem nearestAdjacentRoundToEven_eq_left_or_right
    (x a b : ℝ) (leftMantissa : ℕ) :
    nearestAdjacentRoundToEven x a b leftMantissa = a ∨
      nearestAdjacentRoundToEven x a b leftMantissa = b := by
  unfold nearestAdjacentRoundToEven
  by_cases hleft : |x - a| < |x - b|
  · simp [hleft]
  · simp [hleft]
    by_cases hright : |x - b| < |x - a|
    · simp [hright]
    · simp [hright]
      by_cases heven : evenMantissa leftMantissa
      · simp [heven]
      · simp [heven]

theorem left_le_nearestAdjacentRoundToEven
    {x a b : ℝ} {leftMantissa : ℕ}
    (hab : a ≤ b) :
    a ≤ nearestAdjacentRoundToEven x a b leftMantissa := by
  rcases nearestAdjacentRoundToEven_eq_left_or_right x a b leftMantissa with h | h
  · rw [h]
  · rw [h]
    exact hab

theorem nearestAdjacentRoundToEven_le_right
    {x a b : ℝ} {leftMantissa : ℕ}
    (hab : a ≤ b) :
    nearestAdjacentRoundToEven x a b leftMantissa ≤ b := by
  rcases nearestAdjacentRoundToEven_eq_left_or_right x a b leftMantissa with h | h
  · rw [h]
    exact hab
  · rw [h]

/-- On a fixed ordered adjacent bracket, round-to-even is monotone in the exact
input.  The bracket hypotheses are explicit because this is the local selector
used by the source-facing finite rounding policy, not a total IEEE operation. -/
theorem nearestAdjacentRoundToEven_monotone_on_ordered_bracket
    {x y a b : ℝ} {leftMantissa : ℕ}
    (hab : a ≤ b)
    (hx : a ≤ x ∧ x ≤ b)
    (hy : a ≤ y ∧ y ≤ b)
    (hxy : x ≤ y) :
    nearestAdjacentRoundToEven x a b leftMantissa ≤
      nearestAdjacentRoundToEven y a b leftMantissa := by
  have hx_abs_left : |x - a| = x - a := by
    exact abs_of_nonneg (sub_nonneg.mpr hx.1)
  have hx_abs_right : |x - b| = b - x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
    ring
  have hy_abs_left : |y - a| = y - a := by
    exact abs_of_nonneg (sub_nonneg.mpr hy.1)
  have hy_abs_right : |y - b| = b - y := by
    rw [abs_of_nonpos (sub_nonpos.mpr hy.2)]
    ring
  by_cases hx_left : |x - a| < |x - b|
  · have hx_round :
        nearestAdjacentRoundToEven x a b leftMantissa = a :=
      nearestAdjacentRoundToEven_eq_left_of_left_closer hx_left
    rw [hx_round]
    exact left_le_nearestAdjacentRoundToEven hab
  · by_cases hx_right : |x - b| < |x - a|
    · have hx_round :
          nearestAdjacentRoundToEven x a b leftMantissa = b :=
        nearestAdjacentRoundToEven_eq_right_of_right_closer hx_right
      have hy_right : |y - b| < |y - a| := by
        rw [hy_abs_left, hy_abs_right]
        rw [hx_abs_left, hx_abs_right] at hx_right
        linarith
      have hy_round :
          nearestAdjacentRoundToEven y a b leftMantissa = b :=
        nearestAdjacentRoundToEven_eq_right_of_right_closer hy_right
      rw [hx_round, hy_round]
    · have hx_tie : |x - a| = |x - b| := by
        apply le_antisymm
        · exact le_of_not_gt hx_right
        · exact le_of_not_gt hx_left
      by_cases heven : evenMantissa leftMantissa
      · have hx_round :
            nearestAdjacentRoundToEven x a b leftMantissa = a :=
          nearestAdjacentRoundToEven_eq_left_of_tie_even hx_tie heven
        rw [hx_round]
        exact left_le_nearestAdjacentRoundToEven hab
      · have hx_round :
            nearestAdjacentRoundToEven x a b leftMantissa = b :=
          nearestAdjacentRoundToEven_eq_right_of_tie_odd hx_tie heven
        have hy_not_left : ¬ |y - a| < |y - b| := by
          intro hy_left
          rw [hy_abs_left, hy_abs_right] at hy_left
          rw [hx_abs_left, hx_abs_right] at hx_tie
          linarith
        by_cases hy_right : |y - b| < |y - a|
        · have hy_round :
              nearestAdjacentRoundToEven y a b leftMantissa = b :=
            nearestAdjacentRoundToEven_eq_right_of_right_closer hy_right
          rw [hx_round, hy_round]
        · have hy_tie : |y - a| = |y - b| := by
            apply le_antisymm
            · exact le_of_not_gt hy_right
            · exact le_of_not_gt hy_not_left
          have hy_round :
              nearestAdjacentRoundToEven y a b leftMantissa = b :=
            nearestAdjacentRoundToEven_eq_right_of_tie_odd hy_tie heven
          rw [hx_round, hy_round]

end FloatingPointFormat

end

end LeanFpAnalysis.FP
