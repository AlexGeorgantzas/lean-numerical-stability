import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment
import NumStability.Algorithms.TestMatrices.Higham28GinibreDimensionTwo
import NumStability.Algorithms.TestMatrices.Higham28GinibreTraceDensity
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreAbsoluteDetRecurrence

/-!
# Higham28GinibreAbsoluteDetRecurrence (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreAbsoluteDetRecurrence`
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

open Filter MeasureTheory ProbabilityTheory Set

open scoped BigOperators ENNReal

set_option maxHeartbeats 800000

private local instance ginibreAbsoluteDetRecurrenceMeasurableSpace (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private local instance ginibreAbsoluteDetRecurrenceSigmaFinite (n : ℕ) :
    SigmaFinite (realGinibreMeasure n) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
  infer_instance

private theorem ginibre_natRawCast_one {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 1 = (1 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_zero {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 0 = (0 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_three {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 3 = (3 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_two {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 2 = (2 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_six {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 6 = (6 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_twelve {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 12 = (12 : R) := by
  simp [Nat.rawCast]

theorem measurable_ginibreAbsDetTwoEntryVector :
    Measurable ginibreAbsDetTwoEntryVector := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp [ginibreAbsDetTwoEntryVector] <;> fun_prop

/-- The flattened matrix entries and scalar shift are exactly five independent
standard real Gaussians. -/
theorem measurePreserving_ginibreAbsDetTwoEntryVector :
    MeasurePreserving ginibreAbsDetTwoEntryVector
      ((realGinibreMeasure 2).prod (gaussianReal 0 1))
      (standardGaussianVectorMeasure 5) := by
  let hA : MeasurePreserving ginibreTwoEntryVector
      (realGinibreMeasure 2) (standardGaussianVectorMeasure 4) :=
    ⟨measurable_ginibreTwoEntryVector,
      realGinibreMeasure_two_map_ginibreTwoEntryVector⟩
  let hscalar : MeasurePreserving (fun x : ℝ => fun _ : Fin 1 => x)
      (gaussianReal 0 1) (standardGaussianVectorMeasure 1) := by
    refine ⟨by fun_prop, ?_⟩
    unfold standardGaussianVectorMeasure
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
    have hpre : (fun x : ℝ => fun _ : Fin 1 => x) ⁻¹' (Set.univ.pi s) = s 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
      constructor
      · intro h
        exact h 0
      · intro hx i
        fin_cases i
        exact hx
    rw [hpre]
    simp
  have hprod := hA.prod hscalar
  have hjoin := (measurePreserving_ginibreGaussianVectorSplit 4 1).symm
    (ginibreGaussianVectorSplitEquiv 4 1)
  have h := hjoin.comp hprod
  convert h using 1
  funext p
  simpa only [Function.comp_apply, Prod.map_apply] using
    ginibreAbsDetTwoEntryVector_eq_splitInverse p

/-- The joint absolute determinant is reduced unconditionally to the standard
five-dimensional Gaussian normal-form integral. -/
theorem realGinibreAbsoluteCharacteristicMoment_two_eq_normalFormIntegral :
    realGinibreAbsoluteCharacteristicMoment 2 =
      ∫ x : Fin 5 → ℝ, ginibreAbsDetTwoNormalForm x
        ∂standardGaussianVectorMeasure 5 := by
  let μ := (realGinibreMeasure 2).prod (gaussianReal 0 1)
  let T : (Fin 5 → ℝ) → (Fin 5 → ℝ) := fun x =>
    Matrix.mulVec ginibreAbsDetTwoRotationMatrix x
  have hT : Measurable T := by fun_prop
  have hflat := measurePreserving_ginibreAbsDetTwoEntryVector
  have hrot : (standardGaussianVectorMeasure 5).map T =
      standardGaussianVectorMeasure 5 :=
    standardGaussianVectorMeasure_map_orthogonalGroup 5
      ginibreAbsDetTwoRotationOrthogonal
  unfold realGinibreAbsoluteCharacteristicMoment
  calc
    (∫ p : RSqMat 2 × ℝ, |(p.1 - p.2 • (1 : RSqMat 2)).det| ∂μ) =
        ∫ p : RSqMat 2 × ℝ,
          ginibreAbsDetTwoNormalForm (T (ginibreAbsDetTwoEntryVector p)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with p
      exact abs_det_two_eq_normalForm_rotation p
    _ = ∫ x : Fin 5 → ℝ, ginibreAbsDetTwoNormalForm (T x)
          ∂standardGaussianVectorMeasure 5 := by
      have hmap := integral_map
        measurable_ginibreAbsDetTwoEntryVector.aemeasurable
        ((measurable_ginibreAbsDetTwoNormalForm.comp hT).aestronglyMeasurable)
        (μ := μ)
      rw [hflat.map_eq] at hmap
      simpa only [Function.comp_apply] using hmap.symm
    _ = ∫ x : Fin 5 → ℝ, ginibreAbsDetTwoNormalForm x
          ∂(standardGaussianVectorMeasure 5).map T := by
      symm
      exact integral_map hT.aemeasurable
        measurable_ginibreAbsDetTwoNormalForm.aestronglyMeasurable
    _ = _ := by rw [hrot]

end NumStability

end
