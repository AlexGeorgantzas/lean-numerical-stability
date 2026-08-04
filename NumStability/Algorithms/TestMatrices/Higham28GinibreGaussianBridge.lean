import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantIntegral
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreGaussianBridge

/-!
# Higham28GinibreGaussianBridge (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreGaussianBridge`
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

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal BigOperators

private local instance ginibreGaussianBridgeMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private local instance ginibreGaussianBridgeStandardBorelNuisance (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceNuisance n) :=
  StandardBorelSpace.prod

private local instance ginibreGaussianBridgeStandardBorelCoordinates (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceCoordinates n) :=
  StandardBorelSpace.prod

private instance matrixVolume_isAddHaarMeasure (n : ℕ) :
    (volume : Measure (GinibreRawMatrix n)).IsAddHaarMeasure where
  toIsFiniteMeasureOnCompacts := inferInstance
  toIsAddLeftInvariant := inferInstance
  toIsOpenPosMeasure := inferInstance

local instance ginibreIncidenceLebesgueMeasure_isAddHaarMeasure (n : ℕ) :
    (ginibreIncidenceLebesgueMeasure n).IsAddHaarMeasure := by
  unfold ginibreIncidenceLebesgueMeasure
  exact ContinuousLinearEquiv.isAddHaarMeasure_map
    (ginibreCoordinatesContinuousLinearEquiv n).symm
      (volume : Measure (GinibreRawMatrix (n + 1)))

/-- The affine block assembly map sends incidence Lebesgue measure to the
standard nested product Lebesgue measure on matrices, with no scalar
renormalization. -/
theorem ginibreIncidenceLebesgueMeasure_map (n : ℕ) :
    Measure.map ginibreCoordinatesFinMatrix
        (ginibreIncidenceLebesgueMeasure n) =
      realGinibreLebesgueMeasure (n + 1) := by
  unfold ginibreIncidenceLebesgueMeasure
  rw [Measure.map_map]
  · have hfun : ginibreCoordinatesFinMatrix ∘
        (ginibreCoordinatesContinuousLinearEquiv n).symm = id := by
      funext A
      exact (ginibreCoordinatesLinearEquiv n).apply_symm_apply A
    rw [hfun, Measure.map_id]
    symm
    simp [realGinibreLebesgueMeasure, volume_pi]
  · exact measurable_ginibreCoordinatesFinMatrix
  · exact (ginibreCoordinatesContinuousLinearEquiv n).symm.continuous.measurable

/-- The Gaussian density-weighted root-count `lintegral` in affine block
coordinates is the nonnegative embedding of the real-Ginibre expectation. -/
theorem lintegral_ginibreCoordinate_rootCount_density_eq_expected
    (n : ℕ) :
    (∫⁻ p, (realEigenvalueCount (n + 1)
          (ginibreCoordinatesFinMatrix p) : ℝ≥0∞) *
        ENNReal.ofReal (realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix p))
      ∂ginibreIncidenceLebesgueMeasure n) =
      ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) := by
  let F : GinibreRawMatrix (n + 1) → ℝ≥0∞ := fun A =>
    (realEigenvalueCount (n + 1) A : ℝ≥0∞) *
      ENNReal.ofReal (realGinibreDensityReal (n + 1) A)
  have hmp : MeasurePreserving ginibreCoordinatesFinMatrix
      (ginibreIncidenceLebesgueMeasure n)
      (realGinibreLebesgueMeasure (n + 1)) :=
    ⟨measurable_ginibreCoordinatesFinMatrix,
      ginibreIncidenceLebesgueMeasure_map n⟩
  calc
    (∫⁻ p, (realEigenvalueCount (n + 1)
          (ginibreCoordinatesFinMatrix p) : ℝ≥0∞) *
        ENNReal.ofReal (realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix p))
      ∂ginibreIncidenceLebesgueMeasure n) =
        ∫⁻ A, F A ∂realGinibreLebesgueMeasure (n + 1) := by
      exact hmp.lintegral_comp_emb
        (ginibreCoordinatesContinuousLinearEquiv n).toHomeomorph.measurableEmbedding F
    _ = ∫⁻ A, (realEigenvalueCount (n + 1) A : ℝ≥0∞)
        ∂realGinibreMeasure (n + 1) := by
      rw [realGinibreMeasure_eq_withDensity,
        lintegral_withDensity_eq_lintegral_mul]
      · apply lintegral_congr
        intro A
        simp [F, mul_comm]
      · exact (measurable_realGinibreDensityReal (n + 1)).ennreal_ofReal
      · exact (measurable_of_countable _).comp
          (measurable_realEigenvalueCount (n + 1))
    _ = ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) := by
      unfold expectedRealEigenvalueCount
      symm
      simpa using (ofReal_integral_eq_lintegral_ofReal
        (integrable_realEigenvalueCount (n + 1))
        (ae_of_all _ fun A => Nat.cast_nonneg _))

/-- With the correctly normalized affine Lebesgue measure, the unrestricted
Gaussian incidence determinant integral is exactly the real-Ginibre expected
real-eigenvalue count. -/
theorem lintegral_ginibreIncidence_gaussian_eq_expected (n : ℕ) :
    (∫⁻ q,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))
      ∂ginibreIncidenceLebesgueMeasure n) =
      ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) := by
  rw [lintegral_ginibreIncidence_gaussian_eq_rootCount n
    (ginibreIncidenceLebesgueMeasure n)]
  exact lintegral_ginibreCoordinate_rootCount_density_eq_expected n

end NumStability

end
