import Mathlib.MeasureTheory.Integral.Pi
import NumStability.Algorithms.TestMatrices.Higham28Ginibre
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.GinibreMeasure

/-!
# Higham28GinibreMeasure (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreMeasure`
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

open MeasureTheory

open scoped ENNReal

namespace NumStability

open ProbabilityTheory

local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- The nested finite product of one-dimensional Lebesgue measures on real
`n × n` matrices. -/
noncomputable def realGinibreLebesgueMeasure (n : ℕ) : Measure (RSqMat n) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => volume))

theorem measurable_realGinibreDensityReal (n : ℕ) :
    Measurable (realGinibreDensityReal n) := by
  unfold realGinibreDensityReal
  fun_prop

theorem integrable_realGinibreDensityReal (n : ℕ) :
    Integrable (realGinibreDensityReal n) (realGinibreLebesgueMeasure n) := by
  unfold realGinibreDensityReal realGinibreLebesgueMeasure
  refine Integrable.fintype_prod
    (f := fun _ : Fin n => fun row : Fin n → ℝ =>
      ∏ j : Fin n, gaussianPDFReal 0 1 (row j))
    (μ := fun _ : Fin n => Measure.pi (fun _ : Fin n => volume)) ?_
  intro i
  refine Integrable.fintype_prod
    (f := fun _ : Fin n => gaussianPDFReal 0 1)
    (μ := fun _ : Fin n => volume) ?_
  intro j
  exact integrable_gaussianPDFReal 0 1

/-- Exact joint-density identity for the standard real-Ginibre matrix law. -/
theorem realGinibreMeasure_eq_withDensity (n : ℕ) :
    realGinibreMeasure n =
      (realGinibreLebesgueMeasure n).withDensity
        (fun A => ENNReal.ofReal (realGinibreDensityReal n A)) := by
  let rowLebesgue : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => volume)
  let rowDensity : (Fin n → ℝ) → ℝ :=
    fun x => ∏ j : Fin n, gaussianPDFReal 0 1 (x j)
  have hrowIntegrable : Integrable rowDensity rowLebesgue := by
    dsimp [rowDensity, rowLebesgue]
    apply Integrable.fintype_prod
    intro j
    exact integrable_gaussianPDFReal 0 1
  have hrowNonneg : ∀ x, 0 ≤ rowDensity x := by
    intro x
    exact Finset.prod_nonneg fun j _ => gaussianPDFReal_nonneg 0 1 (x j)
  have hrow : Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      rowLebesgue.withDensity (fun x => ENNReal.ofReal (rowDensity x)) := by
    have h := Measure.pi_withDensity_ofReal
      (fun _ : Fin n => volume)
      (fun _ : Fin n => gaussianPDFReal 0 1)
      (fun _ => integrable_gaussianPDFReal 0 1)
      (fun _ => gaussianPDFReal_nonneg 0 1)
    simpa [rowLebesgue, rowDensity, gaussianReal_of_var_ne_zero,
      gaussianPDF] using h
  unfold realGinibreMeasure realGinibreLebesgueMeasure realGinibreDensityReal
  rw [show (fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      (fun _ : Fin n => rowLebesgue.withDensity
        (fun x => ENNReal.ofReal (rowDensity x))) by
    funext i
    exact hrow]
  simpa [rowLebesgue, rowDensity] using
    (Measure.pi_withDensity_ofReal
      (fun _ : Fin n => rowLebesgue)
      (fun _ : Fin n => rowDensity)
      (fun _ => hrowIntegrable)
      (fun _ => hrowNonneg))

/-- Every Lebesgue-null matrix event is real-Ginibre-null. -/
theorem realGinibreMeasure_absolutelyContinuous_lebesgue (n : ℕ) :
    realGinibreMeasure n ≪ realGinibreLebesgueMeasure n := by
  rw [realGinibreMeasure_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- The strictly positive Gaussian density also gives the converse null-set
transfer: real-Ginibre and matrix Lebesgue measure are equivalent. -/
theorem realGinibreLebesgueMeasure_absolutelyContinuous (n : ℕ) :
    realGinibreLebesgueMeasure n ≪ realGinibreMeasure n := by
  rw [realGinibreMeasure_eq_withDensity]
  apply withDensity_absolutelyContinuous'
  · exact (measurable_realGinibreDensityReal n).ennreal_ofReal.aemeasurable
  · filter_upwards with A
    exact (ENNReal.ofReal_pos.2 (realGinibreDensityReal_pos n A)).ne'

/-- The expected real-eigenvalue count is exactly its density-weighted
Lebesgue matrix integral.  This is the measure-theoretic starting point for
the missing Kac--Rice/coarea evaluation. -/
theorem expectedRealEigenvalueCount_eq_lebesgue (n : ℕ) :
    expectedRealEigenvalueCount n =
      ∫ A : RSqMat n,
        realGinibreDensityReal n A * (realEigenvalueCount n A : ℝ)
        ∂realGinibreLebesgueMeasure n := by
  unfold expectedRealEigenvalueCount
  rw [realGinibreMeasure_eq_withDensity]
  calc
    (∫ A : RSqMat n, (realEigenvalueCount n A : ℝ)
        ∂(realGinibreLebesgueMeasure n).withDensity
          (fun A => ENNReal.ofReal (realGinibreDensityReal n A))) =
        ∫ A : RSqMat n,
          (ENNReal.ofReal (realGinibreDensityReal n A)).toReal •
            (realEigenvalueCount n A : ℝ)
          ∂realGinibreLebesgueMeasure n :=
      integral_withDensity_eq_integral_toReal_smul
        (measurable_realGinibreDensityReal n).ennreal_ofReal
        (ae_of_all _ fun A => ENNReal.ofReal_lt_top)
        (fun A : RSqMat n => (realEigenvalueCount n A : ℝ))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with A
      rw [ENNReal.toReal_ofReal (le_of_lt (realGinibreDensityReal_pos n A))]
      simp [smul_eq_mul]

end NumStability

end
