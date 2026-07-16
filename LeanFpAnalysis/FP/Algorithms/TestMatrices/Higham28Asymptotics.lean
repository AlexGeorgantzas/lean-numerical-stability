/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import LeanFpAnalysis.FP.Algorithms.TestMatrices.Higham28Exact

/-! # Higham Chapter 28: precise asymptotic statement surfaces

This module gives the selected asymptotic prose claims exact filter-based
meanings.  It deliberately supplies no theorem asserting a citation-dependent
limit that has not been derived locally.
-/

namespace LeanFpAnalysis.FP

open Filter Asymptotics

/-- Spectral two-norm condition number using the proved explicit Hilbert
inverse (28.1). -/
noncomputable def hilbertConditionTwo (n : ℕ) : ℝ :=
  opNorm2 (hilbertMatrix n) * opNorm2 (hilbertInverseFormula n)

/-- The shifted Hilbert family `1/(i+j+2)` from p. 514. -/
noncomputable def shiftedHilbertMatrix (n : ℕ) : RSqMat n :=
  fun i j => 1 / (i.val + j.val + 2 : ℕ)

/-- Two-norm condition number of the symmetric Pascal matrix, using its proved
`SᵀS` inverse. -/
noncomputable def pascalConditionTwo (n : ℕ) : ℝ :=
  opNorm2 (pascalMatrix n) *
    opNorm2 ((signedPascal n).transpose * signedPascal n)

/-- Two-norm condition number of the second-difference Toeplitz matrix, using
the proved Green-function inverse. -/
noncomputable def secondDifferenceConditionTwo (n : ℕ) : ℝ :=
  opNorm2 (tridiagonalToeplitz n (-1) 2 (-1)) *
    opNorm2 (secondDifferenceInverse n)

/-- Standard asymptotic-equivalence reading of the determinant display after
(28.2). -/
def HilbertDetAsymptotic : Prop :=
  IsEquivalent atTop
    (fun n : ℕ => Matrix.det (hilbertMatrix n))
    (fun n : ℕ => (2 : ℝ) ^ (-2 * (n : ℝ) ^ 2))

/-- Precise `IsEquivalent` reading of `κ₂(Hₙ) ~ exp(3.5n)`. -/
def HilbertConditionAsymptotic : Prop :=
  IsEquivalent atTop
    hilbertConditionTwo
    (fun n : ℕ => Real.exp (3.5 * n))

/-- Precise Big-O reading of `‖H̃ₙ‖₂ = π + O(1/log n)`. -/
def ShiftedHilbertNormAsymptotic : Prop :=
  (fun n : ℕ => opNorm2 (shiftedHilbertMatrix n) - Real.pi) =O[atTop]
    (fun n : ℕ => 1 / Real.log n)

/-- Precise asymptotic-equivalence reading of the Pascal condition estimate on
p. 520. -/
def PascalConditionAsymptotic : Prop :=
  IsEquivalent atTop
    pascalConditionTwo
    (fun n : ℕ => (16 : ℝ) ^ n / (n * Real.pi))

/-- Precise asymptotic-equivalence reading of the p. 522 second-difference
condition estimate. -/
def SecondDifferenceConditionAsymptotic : Prop :=
  IsEquivalent atTop
    secondDifferenceConditionTwo
    (fun n : ℕ => 4 * (n : ℝ) ^ 2 / Real.pi ^ 2)

/-! ## Explicit-domain asymptotic transfers -/

/-- A relative-error estimate tending to zero produces asymptotic
equivalence.  This is the common analytic transfer used for the three
condition-number rows below. -/
theorem isEquivalent_of_eq_model_mul_one_add
    (f g eps : ℕ → ℝ)
    (heps : Tendsto eps atTop (nhds 0))
    (hformula : ∀ n, f n = g n * (1 + eps n)) :
    IsEquivalent atTop f g := by
  rw [isEquivalent_iff_exists_eq_mul]
  refine ⟨fun n => 1 + eps n, ?_, ?_⟩
  · simpa using tendsto_const_nhds.add heps
  · filter_upwards with n
    simp only [Pi.mul_apply]
    rw [hformula n, mul_comm]

/-- The relative-error transfer has a concrete zero-error producer for every
model sequence, establishing nonvacuity independently of any cited estimate. -/
theorem isEquivalent_self_via_zero_relative_error (g : ℕ → ℝ) :
    IsEquivalent atTop g g := by
  apply isEquivalent_of_eq_model_mul_one_add g g (fun _ => 0)
  · exact tendsto_const_nhds
  · simp

/-- Equation (28.2), explicit-domain form: the exact determinant theorem is
local, while the sole upstream premise is the product/Stirling estimate for
the already-defined closed formula. -/
theorem hilbertDetAsymptotic_of_formula_estimate
    (hestimate : IsEquivalent atTop hilbertDetFormula
      (fun n : ℕ => (2 : ℝ) ^ (-2 * (n : ℝ) ^ 2))) :
    HilbertDetAsymptotic := by
  unfold HilbertDetAsymptotic
  apply hestimate.congr_left
  filter_upwards with n
  exact (hilbert_det_formula n).symm

/-- Section 28.1, explicit-domain transfer from a cited relative spectral
estimate to `kappa_2(H_n) ~ exp(3.5n)`. -/
theorem hilbertConditionAsymptotic_of_relative_estimate
    (eps : ℕ → ℝ)
    (heps : Tendsto eps atTop (nhds 0))
    (hestimate : ∀ n, hilbertConditionTwo n =
      Real.exp (3.5 * n) * (1 + eps n)) :
    HilbertConditionAsymptotic :=
  isEquivalent_of_eq_model_mul_one_add _ _ eps heps hestimate

/-- The shifted-Hilbert norm claim is exactly the cited finite-section
remainder estimate once the remainder is named. -/
theorem shiftedHilbertNormAsymptotic_of_remainder_estimate
    (r : ℕ → ℝ)
    (hdecomp : ∀ n, opNorm2 (shiftedHilbertMatrix n) = Real.pi + r n)
    (hrem : r =O[atTop] (fun n : ℕ => 1 / Real.log n)) :
    ShiftedHilbertNormAsymptotic := by
  unfold ShiftedHilbertNormAsymptotic
  apply hrem.congr'
  · filter_upwards with n
    simp [hdecomp n]
  · exact EventuallyEq.rfl

/-- Section 28.4, explicit-domain transfer from the cited extremal-eigenvalue
and Stirling relative estimate. -/
theorem pascalConditionAsymptotic_of_relative_estimate
    (eps : ℕ → ℝ)
    (heps : Tendsto eps atTop (nhds 0))
    (hestimate : ∀ n, pascalConditionTwo n =
      ((16 : ℝ) ^ n / (n * Real.pi)) * (1 + eps n)) :
    PascalConditionAsymptotic :=
  isEquivalent_of_eq_model_mul_one_add _ _ eps heps hestimate

/-- Section 28.5, explicit-domain transfer from the discrete-sine extremal
eigenvalue estimate. -/
theorem secondDifferenceConditionAsymptotic_of_relative_estimate
    (eps : ℕ → ℝ)
    (heps : Tendsto eps atTop (nhds 0))
    (hestimate : ∀ n, secondDifferenceConditionTwo n =
      (4 * (n : ℝ) ^ 2 / Real.pi ^ 2) * (1 + eps n)) :
    SecondDifferenceConditionAsymptotic :=
  isEquivalent_of_eq_model_mul_one_add _ _ eps heps hestimate

end LeanFpAnalysis.FP
