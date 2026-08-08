import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import NumStability.Algorithms.TestMatrices.Higham28Asymptotics
import NumStability.Algorithms.TestMatrices.Higham28Probability
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.Ginibre

/-!
# Higham28Ginibre (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28Ginibre`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

open Filter Asymptotics Polynomial MeasureTheory

local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- Once measurability of the root count is supplied, boundedness makes its
integrability under the normalized real-Ginibre law automatic. -/
theorem integrable_realEigenvalueCount_of_aestronglyMeasurable
    (n : ℕ)
    (hmeas : AEStronglyMeasurable
      (fun A : RSqMat n => (realEigenvalueCount n A : ℝ))
      (realGinibreMeasure n)) :
    Integrable
      (fun A : RSqMat n => (realEigenvalueCount n A : ℝ))
      (realGinibreMeasure n) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  apply Integrable.of_bound hmeas n
  filter_upwards with A
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast realEigenvalueCount_le n A

private theorem ginibre_abs_sub_half_le_add (n k : ℕ) (hn : 0 < n) :
    |(k : ℝ) - 1 / 2| ≤ (n : ℝ) + k := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (0 : ℝ) ≤ k := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- For positive dimension, the absolute values of successive terms contract
by at least a factor `1/2`. -/
theorem abs_ginibreHypergeometricTerm_succ_le_half
    (n k : ℕ) (hn : 0 < n) :
    |ginibreHypergeometricTerm n (k + 1)| ≤
      |ginibreHypergeometricTerm n k| * (1 / 2 : ℝ) := by
  rw [ginibreHypergeometricTerm_succ]
  simp only [abs_mul, abs_inv]
  have hden : (0 : ℝ) < (n : ℝ) + k := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hratio :
      |(k : ℝ) - 1 / 2| * |(n : ℝ) + k|⁻¹ ≤ 1 := by
    rw [abs_of_pos hden]
    exact mul_inv_le_one_of_le₀
      (ginibre_abs_sub_half_le_add n k hn) (le_of_lt hden)
  have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [hhalf]
  calc
    |ginibreHypergeometricTerm n k| * |(k : ℝ) - 1 / 2| *
          |(n : ℝ) + k|⁻¹ * (1 / 2) =
        |ginibreHypergeometricTerm n k| *
          (|(k : ℝ) - 1 / 2| * |(n : ℝ) + k|⁻¹) * (1 / 2) := by
            ring
    _ ≤ |ginibreHypergeometricTerm n k| * 1 * (1 / 2) := by
      gcongr
    _ = |ginibreHypergeometricTerm n k| * (1 / 2) := by ring

/-- Explicit geometric majorant for every nonconstant hypergeometric term. -/
theorem abs_ginibreHypergeometricTerm_succ_le
    (n k : ℕ) (hn : 0 < n) :
    |ginibreHypergeometricTerm n (k + 1)| ≤
      (1 / (4 * n : ℝ)) * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero =>
      rw [ginibreHypergeometricTerm_one n hn]
      simp only [abs_neg, pow_zero, mul_one]
      rw [abs_of_nonneg]
      positivity
  | succ k ih =>
      calc
        |ginibreHypergeometricTerm n (k + 1 + 1)| ≤
            |ginibreHypergeometricTerm n (k + 1)| * (1 / 2 : ℝ) :=
          abs_ginibreHypergeometricTerm_succ_le_half n (k + 1) hn
        _ ≤ ((1 / (4 * n : ℝ)) * (1 / 2 : ℝ) ^ k) * (1 / 2) := by
          gcongr
        _ = (1 / (4 * n : ℝ)) * (1 / 2 : ℝ) ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- The entire nonconstant hypergeometric tail is bounded by `1/(2n)`.
This quantitative estimate is stronger than the convergence needed below. -/
theorem abs_realGinibre_hypergeometric_sub_one_le
    (n : ℕ) (hn : 0 < n) :
    |₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ) - 1| ≤
      1 / (2 * n : ℝ) := by
  let c : ℝ := 1 / (4 * n : ℝ)
  have hmajor : Summable (fun k : ℕ => c * (1 / 2 : ℝ) ^ k) :=
    summable_geometric_two.mul_left c
  have hbound : ∀ k : ℕ,
      ‖ginibreHypergeometricTerm n (k + 1)‖ ≤
        c * (1 / 2 : ℝ) ^ k := by
    intro k
    simpa [Real.norm_eq_abs, c] using
      abs_ginibreHypergeometricTerm_succ_le n k hn
  have htail : Summable (fun k : ℕ => ginibreHypergeometricTerm n (k + 1)) :=
    hmajor.of_norm_bounded hbound
  have hfull : Summable (fun k : ℕ => ginibreHypergeometricTerm n k) := by
    apply (summable_nat_add_iff 1).1
    simpa using htail
  have hsplit :
      (∑' k : ℕ, ginibreHypergeometricTerm n k) =
        1 + ∑' k : ℕ, ginibreHypergeometricTerm n (k + 1) := by
    simpa using (hfull.sum_add_tsum_nat_add 1).symm
  rw [realGinibre_hypergeometric_eq_tsum, hsplit]
  have htailBound :
      ‖∑' k : ℕ, ginibreHypergeometricTerm n (k + 1)‖ ≤
        ∑' k : ℕ, c * (1 / 2 : ℝ) ^ k :=
    tsum_of_norm_bounded hmajor.hasSum hbound
  have hsumMajor :
      (∑' k : ℕ, c * (1 / 2 : ℝ) ^ k) = c * 2 := by
    rw [tsum_mul_left, tsum_geometric_two]
  rw [show 1 + (∑' k : ℕ, ginibreHypergeometricTerm n (k + 1)) - 1 =
      ∑' k : ℕ, ginibreHypergeometricTerm n (k + 1) by ring]
  rw [Real.norm_eq_abs, hsumMajor] at htailBound
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp [c] at htailBound
  convert htailBound using 1
  field_simp
  norm_num

/-- The hypergeometric correction in the exact finite-`n` formula tends to
one. -/
theorem realGinibre_hypergeometric_tendsto_one :
    Tendsto
      (fun n : ℕ =>
        ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ))
      atTop (nhds 1) := by
  have hmajor :
      Tendsto (fun n : ℕ => 1 / (2 * n : ℝ)) atTop (nhds 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ) using 1
    funext n
    simp [div_eq_mul_inv, mul_inv_rev]
    ring
  apply tendsto_iff_dist_tendsto_zero.2
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hmajor
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  rw [Real.dist_eq]
  exact abs_realGinibre_hypergeometric_sub_one_le n (by omega)

/-- The exact finite-dimensional closed form has the real-Ginibre
`sqrt(2n/pi)` asymptotic. -/
theorem realGinibreExpectedCountClosedForm_limit :
    Tendsto
      (fun n : ℕ => realGinibreExpectedCountClosedForm n / Real.sqrt n)
      atTop (nhds (Real.sqrt (2 / Real.pi))) := by
  have hsqrtTop :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hconstant :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) / Real.sqrt n)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsqrtTop
  have hproduct :
      Tendsto
        (fun n : ℕ =>
          ((Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma (n : ℝ)) /
              Real.sqrt n) *
            ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ))
        atTop (nhds 1) := by
    simpa using realGinibre_gammaRatio_div_sqrt_tendsto_one.mul
      realGinibre_hypergeometric_tendsto_one
  have hscaled :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (2 / Real.pi) *
            (((Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma (n : ℝ)) /
                Real.sqrt n) *
              ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ)))
        atTop (nhds (Real.sqrt (2 / Real.pi))) := by
    simpa using hproduct.const_mul (Real.sqrt (2 / Real.pi))
  have hadd := hconstant.add hscaled
  convert hadd using 1
  · funext n
    unfold realGinibreExpectedCountClosedForm
    ring
  · simp

/-- The exact remaining random-matrix producer: the matrix integral of the
real-root count equals the Edelman--Kostlan--Shub finite formula in every
positive dimension.  This proposition is kept separate from the analytic
closed-form theorem above because its proof requires the Kac--Rice/coarea
and Jacobian calculation. -/
def RealGinibreFiniteExpectationFormula : Prop :=
  ∀ n : ℕ, 0 < n →
    expectedRealEigenvalueCount n = realGinibreExpectedCountClosedForm n

/-- With the analytic asymptotic now discharged locally, only the precise
finite expectation formula is needed to conclude Higham's Ginibre limit. -/
theorem realGinibreExpectedCountLimit_of_finiteExpectationFormula
    (hfinite : RealGinibreFiniteExpectationFormula) :
    RealGinibreExpectedCountLimit := by
  unfold RealGinibreExpectedCountLimit
  apply realGinibreExpectedCountClosedForm_limit.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  rw [hfinite n (by omega)]

end NumStability
