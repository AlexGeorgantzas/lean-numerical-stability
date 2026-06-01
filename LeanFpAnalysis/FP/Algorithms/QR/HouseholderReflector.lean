-- Algorithms/QR/HouseholderReflector.lean
--
-- Low-level floating-point kernels for constructing a Householder reflector.
--
-- This file is intentionally below the QR-factorization layer.  It defines the
-- rounded operations used to form the scalar alpha, vector v, and scalar beta
-- for P = I - beta * v * v^T, but it does not yet claim the full Higham
-- Lemma 18.1 or Lemma 18.2 stability bounds.

import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Algorithms.Norm2
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderSpec

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §18.1  Householder construction primitives
-- ============================================================

/-- Householder sign convention.

    We choose `1` at zero, as is customary in the stable Householder vector
    construction `alpha = -sign(x_0) * ||x||_2`.  This differs from
    `SignType.sign` only at zero. -/
noncomputable def householderSign (x : ℝ) : ℝ :=
  if x < 0 then -1 else 1

@[simp] theorem householderSign_zero : householderSign 0 = 1 := by
  simp [householderSign]

@[simp] theorem abs_householderSign (x : ℝ) : |householderSign x| = 1 := by
  unfold householderSign
  by_cases hx : x < 0 <;> simp [hx]

/-- Away from zero, `householderSign` agrees with Mathlib's `SignType.sign`
    coerced to `ℝ`. -/
theorem householderSign_eq_sign_of_ne {x : ℝ} (hx : x ≠ 0) :
    householderSign x = (SignType.sign x : ℝ) := by
  by_cases hneg : x < 0
  · simp [householderSign, hneg, sign_neg hneg]
  · have hpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hx)
    simp [householderSign, hneg, sign_pos hpos]

/-- Exact `alpha = -sign(x_0) * ||x||_2` used in Householder construction.

    This is exact algebra, not a floating-point operation.  The rounded
    counterpart is `fl_householderAlpha`. -/
noncomputable def householderAlpha {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  -(householderSign (x ⟨0, hn⟩)) *
    Real.sqrt (∑ i : Fin n, x i * x i)

/-- Exact Householder vector before normalization.

    The first component is `x_0 - alpha`; all tail components are copied from
    `x`.  The rounded counterpart is `fl_householderVector`. -/
noncomputable def householderVector {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if i = ⟨0, hn⟩ then
      x i - householderAlpha hn x
    else
      x i

/-- Exact `beta = 2 / (vᵀv)` for the unnormalized Householder vector. -/
noncomputable def householderBeta {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  let v := householderVector hn x
  2 / (∑ i : Fin n, v i * v i)

@[simp] theorem householderVector_zero {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    householderVector hn x ⟨0, hn⟩ =
      x ⟨0, hn⟩ - householderAlpha hn x := by
  simp [householderVector]

/-- Tail components of the exact Householder vector are copied exactly. -/
theorem householderVector_tail {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (i : Fin n) (hi : i ≠ ⟨0, hn⟩) :
    householderVector hn x i = x i := by
  simp [householderVector, hi]

/-- Exact `beta = 2/(vᵀv)` satisfies the orthogonality side condition for
    `householder_orthogonal` whenever the denominator is nonzero. -/
theorem householderBeta_mul_norm_sq {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ)
    (hden : (∑ i : Fin n,
      householderVector hn x i * householderVector hn x i) ≠ 0) :
    householderBeta hn x *
      (∑ i : Fin n, householderVector hn x i * householderVector hn x i) =
        2 := by
  unfold householderBeta
  have hden' : (∑ i : Fin n, householderVector hn x i ^ 2) ≠ 0 := by
    simpa [pow_two] using hden
  field_simp [hden, hden']

/-- Exact Householder construction produces an orthogonal reflector when
    `vᵀv` is nonzero. -/
theorem householder_exact_orthogonal {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ)
    (hden : (∑ i : Fin n,
      householderVector hn x i * householderVector hn x i) ≠ 0) :
    IsOrthogonal n
      (householder n (householderVector hn x) (householderBeta hn x)) := by
  exact householder_orthogonal n (householderVector hn x) (householderBeta hn x)
    (householderBeta_mul_norm_sq hn x hden)

/-- Rounded `alpha = -sign(x_0) * ||x||_2`.

    The index proof `hn : 0 < n` is explicit because the first component is
    used in the Householder construction. -/
noncomputable def fl_householderAlpha (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  fp.fl_mul (-(householderSign (x ⟨0, hn⟩))) (fl_norm2 fp n x)

/-- Rounded Householder vector.

    Only the first component is formed by a rounded subtraction:
    `v_0 = fl_sub x_0 alpha`.  All tail components are copied exactly. -/
noncomputable def fl_householderVector (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if i = ⟨0, hn⟩ then
      fp.fl_sub (x i) (fl_householderAlpha fp hn x)
    else
      x i

/-- Rounded `beta = fl_div 2 (fl_dotProduct v v)`. -/
noncomputable def fl_householderBeta (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  let v := fl_householderVector fp hn x
  fp.fl_div 2 (fl_dotProduct fp n v v)

-- ============================================================
-- Unroll lemmas
-- ============================================================

/-- Unroll `fl_householderAlpha` through the rounded norm and final
    multiplication. -/
theorem fl_householderAlpha_unroll_of_gammaValid_two_mul (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ)
    (hn : gammaValid fp (2 * n)) :
    ∃ (η : Fin n → ℝ) (δ ε : ℝ),
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      |δ| ≤ fp.u ∧
      |ε| ≤ fp.u ∧
      fl_householderAlpha fp hn0 x =
        (-(householderSign (x ⟨0, hn0⟩)) *
          (Real.sqrt (∑ i : Fin n, x i * x i * (1 + η i)) * (1 + δ))) *
          (1 + ε) := by
  obtain ⟨η, δ, hη, hδ, hnorm⟩ :=
    fl_norm2_unroll_of_gammaValid_two_mul fp n x hn
  obtain ⟨ε, hε, hmul⟩ :=
    fp.model_mul (-(householderSign (x ⟨0, hn0⟩))) (fl_norm2 fp n x)
  refine ⟨η, δ, ε, hη, hδ, hε, ?_⟩
  unfold fl_householderAlpha
  rw [hmul, hnorm]

@[simp] theorem fl_householderVector_zero (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    fl_householderVector fp hn x ⟨0, hn⟩ =
      fp.fl_sub (x ⟨0, hn⟩) (fl_householderAlpha fp hn x) := by
  simp [fl_householderVector]

/-- Tail components of the rounded Householder vector are copied exactly. -/
theorem fl_householderVector_tail (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n)
    (hi : i ≠ ⟨0, hn⟩) :
    fl_householderVector fp hn x i = x i := by
  simp [fl_householderVector, hi]

/-- Tail components of the rounded Householder vector agree with the exact
    Householder vector.  This is the easy, exact-copy part of Higham Lemma
    18.1; the first-component perturbation bound is the hard remaining step. -/
theorem fl_householderVector_tail_eq_householderVector (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n)
    (hi : i ≠ ⟨0, hn⟩) :
    fl_householderVector fp hn x i = householderVector hn x i := by
  rw [fl_householderVector_tail fp hn x i hi,
    householderVector_tail hn x i hi]

/-- The first component of the Householder vector is one rounded subtraction. -/
theorem fl_householderVector_zero_unroll (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∃ δ : ℝ,
      |δ| ≤ fp.u ∧
      fl_householderVector fp hn x ⟨0, hn⟩ =
        (x ⟨0, hn⟩ - fl_householderAlpha fp hn x) * (1 + δ) := by
  obtain ⟨δ, hδ, hsub⟩ :=
    fp.model_sub (x ⟨0, hn⟩) (fl_householderAlpha fp hn x)
  exact ⟨δ, hδ, by simpa [fl_householderVector] using hsub⟩

/-- Unroll `fl_householderBeta` through the rounded dot product and final
    division.  The nonzero denominator hypothesis is exactly the condition
    needed to invoke the `FPModel.model_div` primitive. -/
theorem fl_householderBeta_unroll (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hden : fl_dotProduct fp n (fl_householderVector fp hn0 x)
      (fl_householderVector fp hn0 x) ≠ 0) :
    ∃ (η : Fin n → ℝ) (δ : ℝ),
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      |δ| ≤ fp.u ∧
      fl_householderBeta fp hn0 x =
        ((2 : ℝ) /
          (∑ i : Fin n,
            fl_householderVector fp hn0 x i *
              fl_householderVector fp hn0 x i * (1 + η i))) *
          (1 + δ) := by
  set v := fl_householderVector fp hn0 x
  obtain ⟨η, hη, hdot⟩ := dotProduct_backward_error fp n v v hn
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div 2 (fl_dotProduct fp n v v) hden
  refine ⟨η, δ, hη, hδ, ?_⟩
  unfold fl_householderBeta
  simp only
  rw [hdiv, hdot]

end LeanFpAnalysis.FP
