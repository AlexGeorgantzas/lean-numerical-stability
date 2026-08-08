import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment
import NumStability.Algorithms.TestMatrices.Higham28GinibreDimensionTwo
import NumStability.Algorithms.TestMatrices.Higham28GinibreRecurrence
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedExpectation
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedGaussian
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedKernel
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedConclusion

/-!
# Higham28GinibreSignedConclusion (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreSignedConclusion`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

noncomputable section

namespace NumStability

open Filter

/-- After inserting the scalar signed Gaussian moment, the pair-transfer
coefficient is exactly the two-step increment of the finite closed form. -/
theorem neg_two_mul_corollary31_product_mul_signedMoment_eq_closedForm_shift
    (m : ℕ) (hm : 0 < m) :
    -2 * ((ginibreCorollary31Factor (m + 2) *
        ginibreCorollary31Factor (m + 1)) *
      (-Real.Gamma ((m : ℝ) + 1 / 2) / Real.pi)) =
      realGinibreExpectedCountClosedForm (m + 2) -
        realGinibreExpectedCountClosedForm m := by
  have hcoef := two_mul_ginibreCorollary31Factor_product_div_pi m
  calc
    -2 * ((ginibreCorollary31Factor (m + 2) *
        ginibreCorollary31Factor (m + 1)) *
      (-Real.Gamma ((m : ℝ) + 1 / 2) / Real.pi)) =
        (2 * (ginibreCorollary31Factor (m + 2) *
          ginibreCorollary31Factor (m + 1)) / Real.pi) *
            Real.Gamma ((m : ℝ) + 1 / 2) := by ring
    _ = (Real.sqrt (2 / Real.pi) / Real.Gamma ((m : ℝ) + 1)) *
          Real.Gamma ((m : ℝ) + 1 / 2) := by rw [hcoef]
    _ = Real.sqrt (2 / Real.pi) *
          (Real.Gamma ((m : ℝ) + 1 / 2) /
            Real.Gamma ((m : ℝ) + 1)) := by ring
    _ = realGinibreExpectedCountClosedForm (m + 2) -
          realGinibreExpectedCountClosedForm m :=
      (realGinibreExpectedCountClosedForm_shift_two m hm).symm

/-- A dimensionwise signed-pair kernel transfer implies the exact pair shift
needed by the final recurrence. -/
theorem signedPairShift_of_kernelTransfer
    (htransfer : ∀ n : ℕ, 2 ≤ n →
      expectedGinibreAlternatingPairCount n =
        (ginibreCorollary31Factor n *
          ginibreCorollary31Factor (n - 1)) *
            ginibreOrderedGaussianKernelMoment (n - 2)) :
    ∀ m : ℕ, 0 < m →
      expectedGinibreAlternatingPairCount (m + 2) -
          expectedGinibreAlternatingPairCount m =
        (ginibreCorollary31Factor (m + 2) *
          ginibreCorollary31Factor (m + 1)) *
            ginibreOrderedGaussianSignedMoment m := by
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    have h3 := htransfer 3 (by omega)
    norm_num at h3
    have hk :=
      ginibreOrderedGaussianKernelMoment_eq_sub_two_add_signedMoment 1
    norm_num at hk
    rw [expectedGinibreAlternatingPairCount_one, h3, hk]
    ring
  · have hm2 : 1 < m := by omega
    have hhigh := htransfer (m + 2) (by omega)
    have hlow := htransfer m (by omega)
    rw [show m + 2 - 1 = m + 1 by omega,
      show m + 2 - 2 = m by omega] at hhigh
    have hcoef := ginibreCorollary31Factor_product_shift_two m hm2
    have hkernel :=
      ginibreOrderedGaussianKernelMoment_eq_sub_two_add_signedMoment m
    calc
      expectedGinibreAlternatingPairCount (m + 2) -
          expectedGinibreAlternatingPairCount m =
          (ginibreCorollary31Factor (m + 2) *
              ginibreCorollary31Factor (m + 1)) *
              ginibreOrderedGaussianKernelMoment m -
            (ginibreCorollary31Factor m *
              ginibreCorollary31Factor (m - 1)) *
              ginibreOrderedGaussianKernelMoment (m - 2) := by
        rw [hhigh, hlow]
      _ = (ginibreCorollary31Factor (m + 2) *
            ginibreCorollary31Factor (m + 1)) *
          (ginibreOrderedGaussianKernelMoment m -
            (m : ℝ) * ((m - 1 : ℕ) : ℝ) *
              ginibreOrderedGaussianKernelMoment (m - 2)) := by
        rw [hcoef]
        ring
      _ = (ginibreCorollary31Factor (m + 2) *
            ginibreCorollary31Factor (m + 1)) *
          ginibreOrderedGaussianSignedMoment m := by
        rw [hkernel]
        ring

/-- Any genuine expected-count recurrence matching the closed-form two-step
shift implies the finite real-Ginibre expectation formula in every positive
dimension. -/
theorem realGinibreFiniteExpectationFormula_of_shift
    (hshift : ∀ m : ℕ, 0 < m →
      expectedRealEigenvalueCount (m + 2) -
          expectedRealEigenvalueCount m =
        realGinibreExpectedCountClosedForm (m + 2) -
          realGinibreExpectedCountClosedForm m) :
    RealGinibreFiniteExpectationFormula := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn1 : n = 1
      · subst n
        exact expectedRealEigenvalueCount_eq_closedForm_one
      by_cases hn2 : n = 2
      · subst n
        exact expectedRealEigenvalueCount_eq_closedForm_two
      have hn3 : 3 ≤ n := by omega
      let m := n - 2
      have hmpos : 0 < m := by
        dsimp [m]
        omega
      have hmlt : m < n := by
        dsimp [m]
        omega
      have hmadd : m + 2 = n := by
        dsimp [m]
        omega
      have hprev := ih m hmlt hmpos
      have hstep := hshift m hmpos
      rw [hmadd] at hstep
      linarith

/-- The same genuine two-step shift immediately yields Higham's normalized
real-Ginibre limit. -/
theorem realGinibreExpectedCountLimit_of_shift
    (hshift : ∀ m : ℕ, 0 < m →
      expectedRealEigenvalueCount (m + 2) -
          expectedRealEigenvalueCount m =
        realGinibreExpectedCountClosedForm (m + 2) -
          realGinibreExpectedCountClosedForm m) :
    RealGinibreExpectedCountLimit :=
  realGinibreExpectedCountLimit_of_finiteExpectationFormula
    (realGinibreFiniteExpectationFormula_of_shift hshift)

/-- Recurrence-facing endpoint: once the iterated signed-incidence theorem
identifies the shift of the pair expectation with the ordered scalar moment,
the genuine finite expectation formula follows with no further assumptions. -/
theorem realGinibreFiniteExpectationFormula_of_signedPairShift
    (hpair : ∀ m : ℕ, 0 < m →
      expectedGinibreAlternatingPairCount (m + 2) -
          expectedGinibreAlternatingPairCount m =
        (ginibreCorollary31Factor (m + 2) *
          ginibreCorollary31Factor (m + 1)) *
            ginibreOrderedGaussianSignedMoment m) :
    RealGinibreFiniteExpectationFormula := by
  apply realGinibreFiniteExpectationFormula_of_shift
  intro m hm
  rw [expectedRealEigenvalueCount_shift_eq_neg_two_mul_pair_shift]
  rw [hpair m hm, ginibreOrderedGaussianSignedMoment_eq]
  exact
    neg_two_mul_corollary31_product_mul_signedMoment_eq_closedForm_shift m hm

/-- The identical pair-shift endpoint also yields Higham's normalized limit. -/
theorem realGinibreExpectedCountLimit_of_signedPairShift
    (hpair : ∀ m : ℕ, 0 < m →
      expectedGinibreAlternatingPairCount (m + 2) -
          expectedGinibreAlternatingPairCount m =
        (ginibreCorollary31Factor (m + 2) *
          ginibreCorollary31Factor (m + 1)) *
            ginibreOrderedGaussianSignedMoment m) :
    RealGinibreExpectedCountLimit :=
  realGinibreExpectedCountLimit_of_finiteExpectationFormula
    (realGinibreFiniteExpectationFormula_of_signedPairShift hpair)

end NumStability

end
