import NumStability.Algorithms.TestMatrices.Higham28GinibreIntegral

/-!
# Higham28GinibreDeterminantIntegral (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantIntegral`
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

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal BigOperators

/-- The Gaussian-weighted real-root count in matrix coordinates is exactly
the unrestricted incidence integral of the absolute deflated characteristic
determinant.  This is the fully specialized Kac--Rice/coarea reduction; only
its scalar analytic evaluation remains. -/
theorem lintegral_ginibreIncidence_gaussian_eq_rootCount
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [μ.IsAddHaarMeasure] :
    ∫⁻ q,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q))) ∂μ =
      ∫⁻ p, (realEigenvalueCount (n + 1)
          (ginibreCoordinatesFinMatrix p) : ℝ≥0∞) *
        ENNReal.ofReal (realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix p)) ∂μ := by
  let g : GinibreIncidenceCoordinates n → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (realGinibreDensityReal (n + 1)
      (ginibreCoordinatesFinMatrix p))
  have hg : Measurable g :=
    (measurable_realGinibreDensityReal (n + 1)).ennreal_ofReal.comp
      measurable_ginibreCoordinatesFinMatrix
  rw [← lintegral_ginibreIncidence_regular_eq_rootCount n μ g hg]
  rw [← lintegral_indicator (measurableSet_ginibreIncidenceRegularSet n)]
  apply lintegral_congr
  intro q
  by_cases hq : q ∈ ginibreIncidenceRegularSet n
  · rw [Set.indicator_of_mem hq]
    rw [abs_ginibreIncidenceDerivativeLinearMap_det]
  · rw [Set.indicator_of_notMem hq]
    have hdet : (ginibreIncidenceTangentMatrix q).det = 0 := by
      simpa [ginibreIncidenceRegularSet] using hq
    have hderiv : (ginibreIncidenceDerivativeLinearMap q).det = 0 := by
      rw [ginibreIncidenceDerivativeLinearMap_det, hdet]
    have habs : |(ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| = 0 := by
      rw [← abs_ginibreIncidenceDerivativeLinearMap_det, hderiv]
      simp
    rw [habs]
    simp

end NumStability

end
