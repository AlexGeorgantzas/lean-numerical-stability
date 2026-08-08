import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Function.Jacobian
import NumStability.Algorithms.TestMatrices.Higham28GinibreRoots
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibreIncidence

/-!
# Higham28GinibreIncidence (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreIncidence`
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

open scoped BigOperators

open MeasureTheory MeasureTheory.Measure Set

open scoped ENNReal Function

local instance (n : ℕ) : MeasurableSpace (GinibreRawMatrix n) := MeasurableSpace.pi

variable {M Y : Type*}
  [AddCommGroup M] [Module ℝ M]
  [AddCommGroup Y] [Module ℝ Y]

theorem measurable_ginibreIncidenceChart {n : ℕ} :
    Measurable (@ginibreIncidenceChart n) :=
  continuous_ginibreIncidenceChart.measurable

theorem measurable_ginibreCoordinatesFinMatrix {n : ℕ} :
    Measurable (@ginibreCoordinatesFinMatrix n) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  change Measurable (fun p : GinibreIncidenceCoordinates n =>
    ginibreCoordinatesMatrix p
      ((ginibreBlockIndexEquiv n).symm i)
      ((ginibreBlockIndexEquiv n).symm j))
  generalize (ginibreBlockIndexEquiv n).symm i = ii
  generalize (ginibreBlockIndexEquiv n).symm j = jj
  rcases ii with ii | ii <;> rcases jj with jj | jj
  · simp [ginibreCoordinatesMatrix]
    fun_prop
  · rcases ii with ⟨⟩
    simp [ginibreCoordinatesMatrix]
    fun_prop
  · rcases jj with ⟨⟩
    simp [ginibreCoordinatesMatrix]
    fun_prop
  · rcases ii with ⟨⟩
    rcases jj with ⟨⟩
    simp [ginibreCoordinatesMatrix]
    fun_prop

theorem measurable_ginibreIncidenceEigenvalue {n : ℕ} :
    Measurable (@ginibreIncidenceEigenvalue n) :=
  continuous_ginibreIncidenceEigenvalue.measurable

theorem measurable_ginibreIncidenceRootRank (n : ℕ) :
    Measurable (@ginibreIncidenceRootRank n) := by
  apply (measurable_realEigenvalueBelowCount (n + 1)).comp
  exact (measurable_ginibreCoordinatesFinMatrix.comp
    measurable_ginibreIncidenceChart).prodMk
      measurable_ginibreIncidenceEigenvalue

theorem measurableSet_ginibreIncidenceRegularSet (n : ℕ) :
    MeasurableSet (ginibreIncidenceRegularSet n) := by
  exact (measurableSet_eq_fun
    continuous_ginibreIncidenceTangentDet.measurable measurable_const).compl

theorem measurableSet_ginibreIncidenceRankPiece (n : ℕ) (k : Fin (n + 2)) :
    MeasurableSet (ginibreIncidenceRankPiece n k) := by
  exact (measurableSet_ginibreIncidenceRegularSet n).inter
    (measurableSet_eq_fun (measurable_ginibreIncidenceRootRank n) measurable_const)

/-- Along one chart fiber, increasing the distinguished real eigenvalue
strictly increases its root rank. -/
theorem ginibreIncidenceRootRank_lt_of_chart_eq {n : ℕ}
    {q r : GinibreIncidenceCoordinates n}
    (hchart : ginibreIncidenceChart q = ginibreIncidenceChart r)
    (hlt : ginibreIncidenceEigenvalue q < ginibreIncidenceEigenvalue r) :
    ginibreIncidenceRootRank q < ginibreIncidenceRootRank r := by
  unfold ginibreIncidenceRootRank realEigenvalueBelowCount
  rw [hchart]
  let P := Matrix.charpoly (Matrix.of
    (ginibreCoordinatesFinMatrix (ginibreIncidenceChart r)))
  have hP : P ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hmem : ginibreIncidenceEigenvalue q ∈ P.roots := by
    apply (Polynomial.mem_roots hP).2
    simpa [P, hchart] using ginibreIncidenceEigenvalue_isRoot_charpoly q
  exact card_filter_lt_card_filter_of_mem P.roots hmem hlt

theorem injOn_ginibreIncidenceChart_rankPiece (n : ℕ) (k : Fin (n + 2)) :
    Set.InjOn ginibreIncidenceChart (ginibreIncidenceRankPiece n k) := by
  intro q hq r hr hchart
  rcases lt_trichotomy (ginibreIncidenceEigenvalue q)
      (ginibreIncidenceEigenvalue r) with hlt | heq | hgt
  · have hrank := ginibreIncidenceRootRank_lt_of_chart_eq hchart hlt
    rw [hq.2, hr.2] at hrank
    exact (lt_irrefl _ hrank).elim
  · exact ginibreIncidence_eq_of_chart_eq_of_eigenvalue_eq_of_regular
      hchart heq hq.1
  · have hrank := ginibreIncidenceRootRank_lt_of_chart_eq hchart.symm hgt
    rw [hq.2, hr.2] at hrank
    exact (lt_irrefl _ hrank).elim

/-- Finite-to-one area identity for the regular Ginibre incidence chart,
proved by the explicit real-root-rank partition. -/
theorem lintegral_ginibreIncidence_regular_eq_sum_rank_images
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [IsAddHaarMeasure μ]
    (g : GinibreIncidenceCoordinates n → ℝ≥0∞) :
    ∫⁻ q in ginibreIncidenceRegularSet n,
        ENNReal.ofReal |(ginibreIncidenceDerivativeLinearMap q).det| *
          g (ginibreIncidenceChart q) ∂μ =
      ∑ k : Fin (n + 2),
        ∫⁻ p in ginibreIncidenceChart '' ginibreIncidenceRankPiece n k,
          g p ∂μ := by
  rw [← iUnion_ginibreIncidenceRankPiece]
  exact lintegral_finite_partition_image_eq μ
    (ginibreIncidenceRankPiece n)
    (measurableSet_ginibreIncidenceRankPiece n)
    (pairwiseDisjoint_ginibreIncidenceRankPiece n)
    hasFDerivAt_ginibreIncidenceChart
    (injOn_ginibreIncidenceChart_rankPiece n) g

/-- Sard's lemma removes every critical value of the incidence chart.  In
particular, once a real eigenvalue is represented in this affine chart, a
multiple occurrence lies in a Haar-null matrix event by
`mem_ginibreIncidenceRegularSet_iff_root_count_eq_one`. -/
theorem measure_ginibreIncidence_criticalImage_eq_zero
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [IsAddHaarMeasure μ] :
    μ (ginibreIncidenceChart '' (ginibreIncidenceRegularSet n)ᶜ) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (f' := fun q =>
      (ginibreIncidenceDerivativeLinearMap q).toContinuousLinearMap)
  · intro q hq
    exact (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt
  · intro q hq
    change (ginibreIncidenceDerivativeLinearMap q).det = 0
    rw [ginibreIncidenceDerivativeLinearMap_det]
    simpa [ginibreIncidenceRegularSet] using hq

end NumStability

end
