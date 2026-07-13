-- Algorithms/Ch14ForwardErrorEndpoint.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 14 ("Matrix Inversion"), §14.1, equation (14.3), p. 261.
--
-- Target (14.3):  for Y = (A + ΔA)⁻¹ with |ΔA| ≤ ε|A|,
--     |A⁻¹ − Y| ≤ ε|A⁻¹||A||A⁻¹| + O(ε²).
--
-- This module is IMPORT-ONLY.  It reuses the Codex-owned public declarations in
-- `Algorithms/MatrixInversion.lean` (`ideal_forward_error`,
-- `higham14_eq14_3_forward_error_firstorder_plus_remainder`) and closes the
-- printed (14.3) endpoint by supplying the explicit first-order `|Y|` envelope
-- that the plus-remainder wrapper leaves to the caller.
--
-- The printed derivation is followed exactly:
--   * the EXACT identity  A⁻¹ − Y = A⁻¹ · ΔA · Y  (proved in `ideal_forward_error`);
--   * bound (i)   |A⁻¹ − Y| ≤ ε|A⁻¹||A||Y|;
--   * bound (ii)  |Y| ≤ |A⁻¹| + ε|A⁻¹||A||Y|   (the O(ε) envelope, R := ε·S);
--   * substitution of (ii) into (i), which separates the first-order term
--     ε|A⁻¹||A||A⁻¹| from an explicit remainder that is manifestly ε² · (≥0),
--     i.e. the book's O(ε²).
-- No informal `O(ε²)` hand-waving: the remainder is exhibited as ε² times an
-- explicit nonnegative sum.

import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.MatrixInversion

namespace LeanFpAnalysis.FP.Ch14Ext

open scoped BigOperators
open LeanFpAnalysis.FP

/-- Factor a scalar `ε` out of a nested (double) sum:
    `∑ f · (∑ g · (ε·T)) = ε · ∑ f · (∑ g·T)`. -/
theorem ch14ext_pull_eps_double_sum {n : ℕ} (ε : ℝ)
    (f : Fin n → ℝ) (g : Fin n → Fin n → ℝ) (T : Fin n → ℝ) :
    ∑ k₁ : Fin n, f k₁ * (∑ k₂ : Fin n, g k₁ k₂ * (ε * T k₂))
      = ε * ∑ k₁ : Fin n, f k₁ * (∑ k₂ : Fin n, g k₁ k₂ * T k₂) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k₁ _
  have hin : ∑ k₂ : Fin n, g k₁ k₂ * (ε * T k₂)
      = ε * ∑ k₂ : Fin n, g k₁ k₂ * T k₂ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k₂ _; ring
  rw [hin]; ring

/-- **Higham (14.3), envelope step — bound (ii).**  The O(ε) componentwise
    envelope for the perturbed inverse.

    For `Y = (A + ΔA)⁻¹` (encoded honestly by `(A + ΔA)Y = I`) with `|ΔA| ≤ ε|A|`
    and `A_inv` a two-sided inverse of `A`,
        `|Y| ≤ |A⁻¹| + ε·|A⁻¹||A||Y|`.
    The remainder `R = ε·|A⁻¹||A||Y|` is explicitly ε-scaled — no `O(ε²)`
    hand-waving.  Proof: from the EXACT identity `A⁻¹ − Y = A⁻¹ΔAY`
    (`ideal_forward_error`), `Y = A⁻¹ − (A⁻¹ − Y)`, then the triangle
    inequality. -/
theorem ch14ext_abs_Y_le_abs_Ainv_plus_firstorder_remainder (n : ℕ)
    (A A_inv Y ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (hRInv : IsRightInverse n A A_inv)
    (hY : ∀ i j, ∑ k : Fin n, (A i k + ΔA i k) * Y k j =
      if i = j then 1 else 0) :
    ∀ i j, |Y i j| ≤ |A_inv i j| +
      ε * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ j|) := by
  intro i j
  have hbase := ideal_forward_error n A A_inv Y ΔA ε hε hΔA hInv hRInv hY i j
  have hrw : Y i j = A_inv i j + -(A_inv i j - Y i j) := by ring
  rw [hrw]
  calc |A_inv i j + -(A_inv i j - Y i j)|
      ≤ |A_inv i j| + |-(A_inv i j - Y i j)| := abs_add_le _ _
    _ = |A_inv i j| + |A_inv i j - Y i j| := by rw [abs_neg]
    _ ≤ |A_inv i j| + ε * ∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ j|) := by
        linarith [hbase]

/-- **Higham (14.3) endpoint.**  The printed forward-error bound for a computed
    inverse, at full printed strength.

    For `Y = (A + ΔA)⁻¹` with `|ΔA| ≤ ε|A|` and `A_inv` a two-sided inverse of
    `A`, the componentwise forward error splits as
        `|A⁻¹ − Y| ≤ ε·|A⁻¹||A||A⁻¹|  +  ε²·(explicit ≥ 0 remainder)`.
    The first summand is exactly Higham's first-order term `ε|A⁻¹||A||A⁻¹|`; the
    second is the book's `O(ε²)`, here exhibited as `ε²` times a concrete
    nonnegative sum rather than left informal.

    Proof: substitute the O(ε) envelope
    (`ch14ext_abs_Y_le_abs_Ainv_plus_firstorder_remainder`, bound (ii)) for `|Y|`
    into the Codex plus-remainder wrapper
    `higham14_eq14_3_forward_error_firstorder_plus_remainder`, then factor the
    resulting ε·(remainder involving ε) into ε². -/
theorem ch14ext_eq14_3_forward_error_endpoint (n : ℕ)
    (A A_inv Y ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (hRInv : IsRightInverse n A A_inv)
    (hY : ∀ i j, ∑ k : Fin n, (A i k + ΔA i k) * Y k j =
      if i = j then 1 else 0) :
    ∀ i j, |A_inv i j - Y i j| ≤
      ε * (∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * |A_inv k₂ j|))
      + ε ^ 2 * (∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| *
          (∑ m₁ : Fin n, |A_inv k₂ m₁| *
            (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|)))) := by
  intro i j
  -- Feed the O(ε) envelope (bound (ii)) into the plus-remainder wrapper with
  -- R p q = ε · (∑ |A⁻¹||A||Y|).
  have hpr :=
    higham14_eq14_3_forward_error_firstorder_plus_remainder n A A_inv Y ΔA
      (fun p q => ε * ∑ k₁ : Fin n, |A_inv p k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ q|))
      ε hε hΔA hInv hRInv hY
      (ch14ext_abs_Y_le_abs_Ainv_plus_firstorder_remainder
        n A A_inv Y ΔA ε hε hΔA hInv hRInv hY)
      i j
  -- hpr's remainder is  ε · (∑ |A⁻¹| (∑ |A| · (ε·S))) ; factor the inner ε to ε².
  have hEq :
      ε * (∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| *
          (ε * ∑ m₁ : Fin n, |A_inv k₂ m₁| *
            (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|))))
      = ε ^ 2 * (∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| *
          (∑ m₁ : Fin n, |A_inv k₂ m₁| *
            (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|)))) := by
    rw [pow_two, mul_assoc]
    congr 1
    exact ch14ext_pull_eps_double_sum ε (fun k₁ => |A_inv i k₁|)
      (fun k₁ k₂ => |A k₁ k₂|)
      (fun k₂ => ∑ m₁ : Fin n, |A_inv k₂ m₁| *
        (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|))
  calc |A_inv i j - Y i j|
      ≤ ε * (∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, |A k₁ k₂| * |A_inv k₂ j|))
        + ε * (∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, |A k₁ k₂| *
            (ε * ∑ m₁ : Fin n, |A_inv k₂ m₁| *
              (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|)))) := hpr
    _ = ε * (∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, |A k₁ k₂| * |A_inv k₂ j|))
        + ε ^ 2 * (∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, |A k₁ k₂| *
            (∑ m₁ : Fin n, |A_inv k₂ m₁| *
              (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|)))) := by rw [hEq]

end LeanFpAnalysis.FP.Ch14Ext
