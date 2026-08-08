import NumStability.Algorithms.TestMatrices.Higham28GinibreMultiplicity

/-!
# Higham28GinibreIntegral (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreIntegral`
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

open MeasureTheory MeasureTheory.Measure Set

open scoped ENNReal BigOperators

local instance (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceNuisance n) :=
  StandardBorelSpace.prod

local instance (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceCoordinates n) :=
  StandardBorelSpace.prod

theorem measurableSet_ginibreIncidenceRankImage (n : ℕ) (k : Fin (n + 2)) :
    MeasurableSet (ginibreIncidenceChart '' ginibreIncidenceRankPiece n k) :=
  (measurableSet_ginibreIncidenceRankPiece n k).image_of_measurable_injOn
    measurable_ginibreIncidenceChart (injOn_ginibreIncidenceChart_rankPiece n k)

theorem ae_ginibreRegularFiberMultiplicity_eq_realEigenvalueCount
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ p ∂μ, ginibreRegularFiberMultiplicity n p =
      realEigenvalueCount (n + 1) (ginibreCoordinatesFinMatrix p) := by
  have hb : ∀ᵐ p ∂μ, p ∉ ginibreAffineBoundaryEigenpairSet n :=
    (measure_eq_zero_iff_ae_notMem.1
      (measure_ginibreAffineBoundaryEigenpairSet_eq_zero n μ))
  have hc : ∀ᵐ p ∂μ,
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet n)ᶜ :=
    (measure_eq_zero_iff_ae_notMem.1
      (measure_ginibreIncidence_criticalImage_eq_zero n μ))
  filter_upwards [hb, hc] with p hbp hcp
  exact ginibreRegularFiberMultiplicity_eq_realEigenvalueCount p hbp hcp

theorem sum_lintegral_ginibreRankImages_eq_fiberMultiplicity
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    (g : GinibreIncidenceCoordinates n → ℝ≥0∞) (hg : Measurable g) :
    ∑ k : Fin (n + 2),
        ∫⁻ p in ginibreIncidenceChart '' ginibreIncidenceRankPiece n k,
          g p ∂μ =
      ∫⁻ p, (ginibreRegularFiberMultiplicity n p : ℝ≥0∞) * g p ∂μ := by
  symm
  calc
    (∫⁻ p, (ginibreRegularFiberMultiplicity n p : ℝ≥0∞) * g p ∂μ) =
        ∫⁻ p, ∑ k : Fin (n + 2),
          (ginibreIncidenceChart '' ginibreIncidenceRankPiece n k).indicator g p ∂μ := by
      apply lintegral_congr
      intro p
      classical
      unfold ginibreRegularFiberMultiplicity
      rw [Nat.cast_sum]
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      calc
        (∑ k : Fin (n + 2),
              if p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece n k
                then (1 : ℝ≥0∞) else 0) * g p =
            ∑ k : Fin (n + 2),
              (if p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece n k
                then (1 : ℝ≥0∞) else 0) * g p := by
          exact Finset.sum_mul Finset.univ _ _
        _ = ∑ k : Fin (n + 2),
            (ginibreIncidenceChart '' ginibreIncidenceRankPiece n k).indicator g p := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hmem :
              p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece n k
          · simp [hmem]
          · simp [hmem]
    _ = ∑ k : Fin (n + 2), ∫⁻ p,
        (ginibreIncidenceChart '' ginibreIncidenceRankPiece n k).indicator g p ∂μ := by
      rw [MeasureTheory.lintegral_finset_sum Finset.univ]
      intro k hk
      exact hg.indicator (measurableSet_ginibreIncidenceRankImage n k)
    _ = ∑ k : Fin (n + 2),
        ∫⁻ p in ginibreIncidenceChart '' ginibreIncidenceRankPiece n k,
          g p ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact lintegral_indicator
        (measurableSet_ginibreIncidenceRankImage n k) g

theorem lintegral_ginibreIncidence_regular_eq_rootCount
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [μ.IsAddHaarMeasure]
    (g : GinibreIncidenceCoordinates n → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ q in ginibreIncidenceRegularSet n,
        ENNReal.ofReal |(ginibreIncidenceDerivativeLinearMap q).det| *
          g (ginibreIncidenceChart q) ∂μ =
      ∫⁻ p, (realEigenvalueCount (n + 1)
        (ginibreCoordinatesFinMatrix p) : ℝ≥0∞) * g p ∂μ := by
  rw [lintegral_ginibreIncidence_regular_eq_sum_rank_images n μ g]
  rw [sum_lintegral_ginibreRankImages_eq_fiberMultiplicity n μ g hg]
  apply lintegral_congr_ae
  filter_upwards [ae_ginibreRegularFiberMultiplicity_eq_realEigenvalueCount n μ]
    with p hp
  rw [hp]

end NumStability

end
