import NumStability.Algorithms.TestMatrices.Higham28GinibreMeasure
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.GinibreJointDensity

/-!
# Higham28GinibreJointDensity (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreJointDensity`
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

open MeasureTheory ProbabilityTheory

private local instance ginibreJointDensityMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- Convert an integral under the independent real-Ginibre and standard
Gaussian laws into the corresponding density-weighted product-Lebesgue
integral. -/
theorem integral_realGinibre_prod_gaussian_eq_jointDensity
    (n : ℕ) (g : RSqMat n × ℝ → ℝ) :
    (∫ p, g p ∂((realGinibreMeasure n).prod (gaussianReal 0 1))) =
      ∫ p,
        (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2) * g p
        ∂((realGinibreLebesgueMeasure n).prod volume) := by
  rw [realGinibreMeasure_eq_withDensity]
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [prod_withDensity
    (measurable_realGinibreDensityReal n).ennreal_ofReal
    (measurable_gaussianPDF 0 1)]
  have hdensity : Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal (realGinibreDensityReal n p.1) *
        gaussianPDF 0 1 p.2) :=
    (((measurable_realGinibreDensityReal n).ennreal_ofReal.comp
      measurable_fst).mul
        ((measurable_gaussianPDF 0 1).comp measurable_snd))
  rw [integral_withDensity_eq_integral_toReal_smul hdensity]
  · apply integral_congr_ae
    filter_upwards with p
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal
        (le_of_lt (realGinibreDensityReal_pos n p.1)),
      toReal_gaussianPDF]
    simp only [smul_eq_mul]
  · filter_upwards with p
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top gaussianPDF_lt_top

end NumStability

end
