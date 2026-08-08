import Mathlib.MeasureTheory.Measure.Prod
import NumStability.Algorithms.TestMatrices.Higham28Probability
import NumStability.Analysis.Probability.Gaussian.AbsoluteMoment
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreDeterminantMoment

/-!
# Higham28GinibreDeterminantMoment (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment`
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

local instance ginibreDeterminantMomentMeasurableSpace (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

local instance ginibreDeterminantMomentSigmaFinite (n : ℕ) :
    SigmaFinite (realGinibreMeasure n) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
  infer_instance

/-- The absolute characteristic determinant averaged over an independent
standard real-Ginibre matrix and standard real Gaussian shift. -/
noncomputable def realGinibreAbsoluteCharacteristicMoment (n : ℕ) : ℝ :=
  ∫ p : RSqMat n × ℝ,
    |(p.1 - p.2 • (1 : RSqMat n)).det|
    ∂(realGinibreMeasure n).prod (gaussianReal 0 1)

/-- The only entry of a standard `1 × 1` real-Ginibre matrix has the
standard real Gaussian law. -/
theorem realGinibreMeasure_one_map_entry :
    (realGinibreMeasure 1).map (fun A : RSqMat 1 => A 0 0) =
      gaussianReal 0 1 := by
  unfold realGinibreMeasure
  rw [show (fun A : RSqMat 1 => A 0 0) =
      (fun r : Fin 1 → ℝ => r 0) ∘ (fun A : RSqMat 1 => A 0) by rfl]
  rw [← Measure.map_map (measurable_pi_apply 0) (measurable_pi_apply 0)]
  change Measure.map (Function.eval 0)
    (Measure.map (Function.eval 0)
      (Measure.pi fun _ : Fin 1 =>
        Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) = _
  have hrow : (Measure.pi fun _ : Fin 1 =>
      Measure.pi fun _ : Fin 1 => gaussianReal 0 1).map
        (Function.eval 0) = Measure.pi fun _ : Fin 1 => gaussianReal 0 1 := by
    rw [Measure.pi_map_eval]
    simp
  rw [hrow]
  change (Measure.pi fun _ : Fin 1 => gaussianReal 0 1).map
    (Function.eval 0) = gaussianReal 0 1
  rw [Measure.pi_map_eval]
  simp

/-- Jointly retaining the sole matrix entry and the independent scalar shift
gives exactly two independent standard real Gaussians. -/
theorem realGinibreMeasure_one_prod_map_entry :
    ((realGinibreMeasure 1).prod (gaussianReal 0 1)).map
        (fun p : RSqMat 1 × ℝ => (p.1 0 0, p.2)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let hA : MeasurePreserving (fun A : RSqMat 1 => A 0 0)
      (realGinibreMeasure 1) (gaussianReal 0 1) :=
    ⟨by fun_prop, realGinibreMeasure_one_map_entry⟩
  have h := hA.prod (MeasurePreserving.id (gaussianReal 0 1))
  simpa [Prod.map] using h.map_eq

/-- The empty determinant has absolute characteristic moment one. -/
theorem realGinibreAbsoluteCharacteristicMoment_zero :
    realGinibreAbsoluteCharacteristicMoment 0 = 1 := by
  unfold realGinibreAbsoluteCharacteristicMoment
  simp only [Matrix.det_isEmpty, abs_one, integral_const, measureReal_def]
  have hprod : ((realGinibreMeasure 0).prod (gaussianReal 0 1)) Set.univ = 1 := by
    rw [Measure.prod_apply MeasurableSet.univ]
    simp [realGinibreMeasure_univ]
  rw [hprod, ENNReal.toReal_one]
  simp

/-- The one-dimensional determinant is the difference of two independent
standard Gaussians, so its absolute moment is `2 / √π`. -/
theorem realGinibreAbsoluteCharacteristicMoment_one :
    realGinibreAbsoluteCharacteristicMoment 1 =
      2 / Real.sqrt Real.pi := by
  unfold realGinibreAbsoluteCharacteristicMoment
  let F : RSqMat 1 × ℝ → ℝ × ℝ := fun p => (p.1 0 0, p.2)
  let μ := (realGinibreMeasure 1).prod (gaussianReal 0 1)
  have hF : AEMeasurable F μ := by fun_prop
  calc
    (∫ p : RSqMat 1 × ℝ, |(p.1 - p.2 • (1 : RSqMat 1)).det| ∂μ) =
        ∫ p : RSqMat 1 × ℝ, |p.1 0 0 - p.2| ∂μ := by
          apply integral_congr_ae
          filter_upwards with p
          simp
    _ = ∫ p : ℝ × ℝ, |p.1 - p.2| ∂μ.map F := by
          exact (integral_map hF
            ((measurable_fst.sub measurable_snd).abs.aestronglyMeasurable)).symm
    _ = ∫ p : ℝ × ℝ, |p.1 - p.2|
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
          rw [show μ.map F =
            (gaussianReal 0 1).prod (gaussianReal 0 1) by
              simpa [μ, F] using realGinibreMeasure_one_prod_map_entry]
    _ = 2 / Real.sqrt Real.pi := integral_abs_standardGaussian_difference

end NumStability

end
