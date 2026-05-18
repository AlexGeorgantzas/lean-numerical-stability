-- Algorithms/QR/HouseholderReflector.lean
--
-- Low-level Householder reflector construction helpers.
--
-- This file starts the reflector-construction layer below full QR.  It keeps
-- the distinction between:
--
--   * rounded construction data, such as a vector built using a rounded norm;
--   * the exact orthogonal Householder matrix associated with a nonzero vector.
--
-- That distinction matters: a rounded scalar β is not automatically the exact
-- scalar that makes I - βvvᵀ orthogonal.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Algorithms.Norm2
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderSpec

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §18.1  Low-level reflector construction helpers
-- ============================================================

/-- Exact sign choice used in Householder reflector construction.

    Comparisons and sign flips are treated as exact control/negation operations,
    not as rounded arithmetic. -/
noncomputable def householderSign (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else -1

theorem abs_householderSign (x : ℝ) : |householderSign x| = 1 := by
  unfold householderSign
  split <;> norm_num

@[simp]
theorem householderSign_zero : householderSign 0 = 1 := by
  simp [householderSign]

/-- Away from zero, the Householder sign choice agrees with Mathlib's
    `Real.sign`.  At zero they intentionally differ: `householderSign 0 = 1`,
    while `Real.sign 0 = 0`. -/
theorem householderSign_eq_realSign_of_ne {x : ℝ} (hx : x ≠ 0) :
    householderSign x = Real.sign x := by
  rcases lt_or_gt_of_ne hx with hxlt | hxgt
  · rw [Real.sign_of_neg hxlt]
    unfold householderSign
    simp [not_le_of_gt hxlt]
  · rw [Real.sign_of_pos hxgt]
    unfold householderSign
    simp [le_of_lt hxgt]

theorem householderSign_mul_eq_abs (x : ℝ) :
    householderSign x * x = |x| := by
  unfold householderSign
  by_cases hx : 0 ≤ x
  · simp [hx, abs_of_nonneg hx]
  · have hxlt : x < 0 := lt_of_not_ge hx
    simp [hx, abs_of_neg hxlt]

/-- Exact scalar `β = 2/(vᵀv)` associated with a Householder vector. -/
noncomputable def exactHouseholderBeta (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  2 / exactNorm2Sq n v

theorem exactHouseholderBeta_mul_norm2Sq (n : ℕ) (v : Fin n → ℝ)
    (hv : exactNorm2Sq n v ≠ 0) :
    exactHouseholderBeta n v * exactNorm2Sq n v = 2 := by
  unfold exactHouseholderBeta
  field_simp [hv]

/-- The exact Householder matrix associated with a nonzero vector is
    orthogonal. -/
theorem exactHouseholder_orthogonal (n : ℕ) (v : Fin n → ℝ)
    (hv : exactNorm2Sq n v ≠ 0) :
    IsOrthogonal n (householder n v (exactHouseholderBeta n v)) := by
  apply householder_orthogonal
  simpa [exactNorm2Sq] using exactHouseholderBeta_mul_norm2Sq n v hv

/-- Floating-point scalar `α = -sign(x₀) * ‖x‖₂`.

    The sign and negation are exact; the norm is the rounded norm from
    `fl_norm2`. -/
noncomputable def fl_householderAlpha (fp : FPModel) (n : ℕ)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  -(householderSign (x 0)) * fl_norm2 fp (n + 1) x

/-- Unrolled form of the rounded norm inside `fl_householderAlpha`. -/
theorem fl_householderAlpha_unroll (fp : FPModel) (n : ℕ)
    (x : Fin (n + 1) → ℝ) (hn : gammaValid fp (2 * (n + 1))) :
    ∃ (η : Fin (n + 1) → ℝ) (δ : ℝ),
      (∀ i : Fin (n + 1), |η i| ≤ gamma fp (n + 1)) ∧
      |δ| ≤ fp.u ∧
      fl_householderAlpha fp n x =
        -(householderSign (x 0)) *
          (Real.sqrt (∑ i : Fin (n + 1), x i * x i * (1 + η i)) * (1 + δ)) := by
  obtain ⟨η, δ, hη, hδ, hnorm⟩ :=
    fl_norm2_unroll_of_gammaValid_two_mul fp (n + 1) x hn
  refine ⟨η, δ, hη, hδ, ?_⟩
  unfold fl_householderAlpha
  rw [hnorm]

/-- Floating-point Householder vector construction from a column segment.

    For a vector `x`, this sets

      `v₀ = fl(x₀ - α)` and `vᵢ = xᵢ` for `i > 0`,

    where `α = -sign(x₀) * fl_norm2(x)`.  This is the first low-level
    construction layer; later theorems must prove the needed nonzero and
    perturbation properties before full QR can use it end-to-end. -/
noncomputable def fl_householderVector (fp : FPModel) (n : ℕ)
    (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i = 0 then fp.fl_sub (x i) (fl_householderAlpha fp n x) else x i

/-- Unrolled form of `fl_householderVector`.

    The first component is computed by one rounded subtraction after the rounded
    norm in `fl_householderAlpha`; every tail component is copied exactly. -/
theorem fl_householderVector_unroll (fp : FPModel) (n : ℕ)
    (x : Fin (n + 1) → ℝ) (hn : gammaValid fp (2 * (n + 1))) :
    ∃ (η : Fin (n + 1) → ℝ) (δnorm δsub : ℝ),
      (∀ i : Fin (n + 1), |η i| ≤ gamma fp (n + 1)) ∧
      |δnorm| ≤ fp.u ∧
      |δsub| ≤ fp.u ∧
      fl_householderVector fp n x 0 =
        (x 0 -
          (-(householderSign (x 0)) *
            (Real.sqrt (∑ i : Fin (n + 1), x i * x i * (1 + η i)) *
              (1 + δnorm)))) * (1 + δsub) ∧
      (∀ i : Fin (n + 1), i ≠ 0 → fl_householderVector fp n x i = x i) := by
  obtain ⟨η, δnorm, hη, hδnorm, halpha⟩ :=
    fl_householderAlpha_unroll fp n x hn
  let α := fl_householderAlpha fp n x
  let δsub : ℝ := Classical.choose (fp.model_sub (x 0) α)
  have hδsub :
      |δsub| ≤ fp.u ∧ fp.fl_sub (x 0) α = (x 0 - α) * (1 + δsub) :=
    Classical.choose_spec (fp.model_sub (x 0) α)
  refine ⟨η, δnorm, δsub, hη, hδnorm, hδsub.1, ?_, ?_⟩
  · unfold fl_householderVector
    simp only [↓reduceIte]
    change fp.fl_sub (x 0) α = _
    rw [hδsub.2]
    rw [show α = fl_householderAlpha fp n x by rfl, halpha]
  · intro i hi
    unfold fl_householderVector
    simp [hi]

/-- Rounded scalar `β` computed from a Householder vector using a rounded
    dot product and rounded division.

    This is useful for modeling executable code, but it should not be assumed
    to make `I - βvvᵀ` exactly orthogonal without an additional proof or an
    exact-β bridge. -/
noncomputable def fl_householderBeta (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  fp.fl_div 2 (fl_norm2Sq fp n v)

/-- Unrolled form of `fl_householderBeta`.

    This exposes the rounded dot product used for `vᵀv` and the final rounded
    division by that computed denominator. -/
theorem fl_householderBeta_unroll (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (hn : gammaValid fp n)
    (hden : fl_norm2Sq fp n v ≠ 0) :
    ∃ (η : Fin n → ℝ) (δdiv : ℝ),
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      |δdiv| ≤ fp.u ∧
      fl_householderBeta fp n v =
        (2 / (∑ i : Fin n, v i * v i * (1 + η i))) * (1 + δdiv) := by
  obtain ⟨η, hη, hsum⟩ := fl_norm2Sq_backward_error fp n v hn
  obtain ⟨δdiv, hδdiv, hdiv⟩ := fp.model_div 2 (fl_norm2Sq fp n v) hden
  refine ⟨η, δdiv, hη, hδdiv, ?_⟩
  unfold fl_householderBeta
  rw [hdiv, hsum]

/-- Exact orthogonal reflector associated with the rounded vector constructed
    from `x`.

    This is not the same object as the reflector formed with the rounded
    `fl_householderBeta`; it is the mathematically exact Householder reflector
    generated by the computed vector. -/
noncomputable def exactHouseholderFromRoundedVector (fp : FPModel) (n : ℕ)
    (x : Fin (n + 1) → ℝ) : Fin (n + 1) → Fin (n + 1) → ℝ :=
  let v := fl_householderVector fp n x
  householder (n + 1) v (exactHouseholderBeta (n + 1) v)

end LeanFpAnalysis.FP
