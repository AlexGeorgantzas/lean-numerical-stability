import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.MeasureTheory.Group.Prod
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment
import NumStability.Algorithms.TestMatrices.Higham28GinibreMeasure
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.GinibreTraceDensity

/-!
# Higham28GinibreTraceDensity (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreTraceDensity`
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

open scoped BigOperators ENNReal

private local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private local instance (n : ℕ) : OpensMeasurableSpace (RSqMat n) :=
  Pi.opensMeasurableSpace

private local instance (n : ℕ) : BorelSpace (RSqMat n) := Pi.borelSpace

theorem measurable_ginibreTraceCorrelatedDensityReal (n : ℕ) :
    Measurable (ginibreTraceCorrelatedDensityReal n) := by
  unfold ginibreTraceCorrelatedDensityReal ginibreTraceQuadratic ginibreMatrixSq
  fun_prop

private local instance ginibreLebesgueSigmaFinite (n : ℕ) :
    SigmaFinite (realGinibreLebesgueMeasure n) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume)))
  infer_instance

private local instance ginibreLebesgueIsAddRightInvariant (n : ℕ) :
    (realGinibreLebesgueMeasure n).IsAddRightInvariant := by
  change Measure.IsAddRightInvariant (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume)))
  infer_instance

theorem measurable_ginibreShiftShear (n : ℕ) : Measurable (ginibreShiftShear n) := by
  apply Measurable.prodMk _ measurable_snd
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hij : Measurable (fun A : RSqMat n => A i j) := by fun_prop
  exact (hij.comp measurable_fst).sub
    (measurable_snd.mul measurable_const)

theorem measurable_ginibreUnshiftShear (n : ℕ) : Measurable (ginibreUnshiftShear n) := by
  apply Measurable.prodMk _ measurable_snd
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hij : Measurable (fun A : RSqMat n => A i j) := by fun_prop
  exact (hij.comp measurable_fst).add
    (measurable_snd.mul measurable_const)

/-- The affine substitution has Jacobian one, expressed intrinsically as
preservation of matrix-by-scalar Lebesgue measure. -/
theorem measurePreserving_ginibreShiftShear (n : ℕ) :
    MeasurePreserving (ginibreShiftShear n)
      ((realGinibreLebesgueMeasure n).prod volume)
      ((realGinibreLebesgueMeasure n).prod volume) := by
  let μ := realGinibreLebesgueMeasure n
  have htranslate : ∀ x : ℝ,
      Measure.map (fun A : RSqMat n => A - x • (1 : RSqMat n)) μ = μ := by
    intro x
    simpa [sub_eq_add_neg] using
      (map_add_right_eq_self μ (-(x • (1 : RSqMat n))))
  have hskewMeas : Measurable
      (Function.uncurry
        (fun x : ℝ => fun A : RSqMat n => A - x • (1 : RSqMat n))) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    have hij : Measurable (fun A : RSqMat n => A i j) := by fun_prop
    exact (hij.comp measurable_snd).sub
      (measurable_fst.mul measurable_const)
  have hskew : MeasurePreserving
      (fun p : ℝ × RSqMat n => (p.1, p.2 - p.1 • (1 : RSqMat n)))
      (volume.prod μ) (volume.prod μ) :=
    (MeasurePreserving.id volume).skew_product hskewMeas
      (ae_of_all _ htranslate)
  have h := (Measure.measurePreserving_swap (μ := volume) (ν := μ)).comp
    (hskew.comp (Measure.measurePreserving_swap (μ := μ) (ν := volume)))
  simpa [μ, ginibreShiftShear, Function.comp_def] using h

/-- Nonnegative-integral version of the absolute characteristic moment. -/
noncomputable def realGinibreAbsoluteCharacteristicMomentLIntegral (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ p : RSqMat n × ℝ,
    ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det|
    ∂(realGinibreMeasure n).prod (gaussianReal 0 1)

theorem measurable_abs_det_ginibreShiftReal (n : ℕ) :
    Measurable (fun p : RSqMat n × ℝ =>
      |(p.1 - p.2 • (1 : RSqMat n)).det|) := by
  apply Measurable.abs
  simp_rw [Matrix.det_apply]
  apply Finset.measurable_sum
  intro σ hσ
  apply Measurable.const_smul
  apply Finset.measurable_prod
  intro i hi
  have hij : Measurable (fun A : RSqMat n => A (σ i) i) := by fun_prop
  exact (hij.comp measurable_fst).sub (measurable_snd.mul measurable_const)

theorem measurable_abs_det_ginibreShift (n : ℕ) :
    Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det|) :=
  (measurable_abs_det_ginibreShiftReal n).ennreal_ofReal

theorem measurable_abs_det_matrixReal (n : ℕ) :
    Measurable (fun A : RSqMat n => |A.det|) :=
  continuous_id.matrix_det.abs.measurable

theorem measurable_abs_det_matrix (n : ℕ) :
    Measurable (fun A : RSqMat n => ENNReal.ofReal |A.det|) := by
  exact (measurable_abs_det_matrixReal n).ennreal_ofReal

/-- The ordinary expectation is the real value of its nonnegative integral.
This is unconditional: Mathlib's conventions agree even in the nonintegrable
case (`integral = 0` and `ENNReal.toReal ∞ = 0`). -/
theorem realGinibreAbsoluteCharacteristicMoment_eq_toReal_lintegral (n : ℕ) :
    realGinibreAbsoluteCharacteristicMoment n =
      (realGinibreAbsoluteCharacteristicMomentLIntegral n).toReal := by
  unfold realGinibreAbsoluteCharacteristicMoment
  unfold realGinibreAbsoluteCharacteristicMomentLIntegral
  exact integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun p => abs_nonneg _)
    (measurable_abs_det_ginibreShiftReal n).aestronglyMeasurable

theorem realGinibreAbsoluteCharacteristicMomentLIntegral_eq_jointDensity
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMomentLIntegral n =
      ∫⁻ p : RSqMat n × ℝ,
        ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
          ENNReal.ofReal
            (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2)
        ∂(realGinibreLebesgueMeasure n).prod volume := by
  unfold realGinibreAbsoluteCharacteristicMomentLIntegral
  rw [realGinibreMeasure_eq_withDensity]
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [prod_withDensity
    (measurable_realGinibreDensityReal n).ennreal_ofReal
    (measurable_gaussianPDF 0 1)]
  have hdensity : Measurable (fun z : RSqMat n × ℝ =>
      ENNReal.ofReal (realGinibreDensityReal n z.1) * gaussianPDF 0 1 z.2) :=
    (((measurable_realGinibreDensityReal n).ennreal_ofReal.comp measurable_fst).mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd))
  rw [lintegral_withDensity_eq_lintegral_mul _ hdensity
    (measurable_abs_det_ginibreShift n)]
  apply lintegral_congr
  intro p
  simp only [Pi.mul_apply, gaussianPDF]
  rw [ENNReal.ofReal_mul (le_of_lt (realGinibreDensityReal_pos n p.1))]
  ring

theorem realGinibreAbsoluteCharacteristicMomentLIntegral_eq_shiftedJointDensity
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMomentLIntegral n =
      ∫⁻ p : RSqMat n × ℝ,
        ENNReal.ofReal |p.1.det| *
          ENNReal.ofReal
            (realGinibreDensityReal n
                (p.1 + p.2 • (1 : RSqMat n)) *
              gaussianPDFReal 0 1 p.2)
        ∂(realGinibreLebesgueMeasure n).prod volume := by
  rw [realGinibreAbsoluteCharacteristicMomentLIntegral_eq_jointDensity]
  let G : RSqMat n × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |p.1.det| *
      ENNReal.ofReal
        (realGinibreDensityReal n (p.1 + p.2 • (1 : RSqMat n)) *
          gaussianPDFReal 0 1 p.2)
  have hdet : Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal |p.1.det|) := by
    exact (measurable_abs_det_matrix n).comp measurable_fst
  have hjoint : Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal
        (realGinibreDensityReal n (p.1 + p.2 • (1 : RSqMat n)) *
          gaussianPDFReal 0 1 p.2)) := by
    apply Measurable.ennreal_ofReal
    exact ((measurable_realGinibreDensityReal n).comp
      (measurable_fst.comp (measurable_ginibreUnshiftShear n))).mul
        ((measurable_gaussianPDFReal 0 1).comp measurable_snd)
  have hG : Measurable G := hdet.mul hjoint
  calc
    (∫⁻ p : RSqMat n × ℝ,
        ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
          ENNReal.ofReal
            (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2)
        ∂(realGinibreLebesgueMeasure n).prod volume) =
      ∫⁻ p, G (ginibreShiftShear n p)
        ∂(realGinibreLebesgueMeasure n).prod volume := by
          apply lintegral_congr
          intro p
          change ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
              ENNReal.ofReal
                (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2) =
            ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
              ENNReal.ofReal
                (realGinibreDensityReal n
                    ((p.1 - p.2 • (1 : RSqMat n)) +
                      p.2 • (1 : RSqMat n)) *
                  gaussianPDFReal 0 1 p.2)
          rw [sub_add_cancel]
    _ = ∫⁻ p, G p ∂(realGinibreLebesgueMeasure n).prod volume :=
      (measurePreserving_ginibreShiftShear n).lintegral_comp hG

/-- The unconditional change-of-variables identity: the absolute
characteristic moment is the determinant integral against the exact
trace-correlated Gaussian density. -/
theorem realGinibreAbsoluteCharacteristicMomentLIntegral_eq_traceDensity
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMomentLIntegral n =
      ∫⁻ B : RSqMat n,
        ENNReal.ofReal |B.det| *
          ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
        ∂realGinibreLebesgueMeasure n := by
  rw [realGinibreAbsoluteCharacteristicMomentLIntegral_eq_shiftedJointDensity]
  let d : RSqMat n → ℝ≥0∞ := fun B => ENNReal.ofReal |B.det|
  let j : RSqMat n × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal
      (realGinibreDensityReal n (p.1 + p.2 • (1 : RSqMat n)) *
        gaussianPDFReal 0 1 p.2)
  have hd : Measurable d := by
    simpa only [d] using measurable_abs_det_matrix n
  have hj : Measurable j := by
    apply Measurable.ennreal_ofReal
    exact ((measurable_realGinibreDensityReal n).comp
      (measurable_fst.comp (measurable_ginibreUnshiftShear n))).mul
        ((measurable_gaussianPDFReal 0 1).comp measurable_snd)
  change (∫⁻ p : RSqMat n × ℝ, d p.1 * j p
      ∂(realGinibreLebesgueMeasure n).prod volume) =
    ∫⁻ B : RSqMat n, d B *
      ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
      ∂realGinibreLebesgueMeasure n
  rw [lintegral_prod (fun p : RSqMat n × ℝ => d p.1 * j p)
    ((hd.comp measurable_fst).mul hj).aemeasurable]
  apply lintegral_congr
  intro B
  have hinner : Measurable (fun x : ℝ => j (B, x)) :=
    hj.comp (measurable_const.prodMk measurable_id)
  change (∫⁻ x : ℝ, d B * j (B, x)) =
    d B * ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
  rw [lintegral_const_mul _ hinner]
  change d B * (∫⁻ x : ℝ, ENNReal.ofReal
      (realGinibreDensityReal n (B + x • (1 : RSqMat n)) *
        gaussianPDFReal 0 1 x)) = _
  rw [lintegral_ginibreShiftJointDensity]

/-- Ordinary-integral form of the same unconditional identity, directly
connected to `realGinibreAbsoluteCharacteristicMoment`. -/
theorem realGinibreAbsoluteCharacteristicMoment_eq_traceDensityIntegral
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMoment n =
      ∫ B : RSqMat n,
        |B.det| * ginibreTraceCorrelatedDensityReal n B
        ∂realGinibreLebesgueMeasure n := by
  calc
    realGinibreAbsoluteCharacteristicMoment n =
        (realGinibreAbsoluteCharacteristicMomentLIntegral n).toReal :=
      realGinibreAbsoluteCharacteristicMoment_eq_toReal_lintegral n
    _ = (∫⁻ B : RSqMat n,
          ENNReal.ofReal |B.det| *
            ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
          ∂realGinibreLebesgueMeasure n).toReal := by
      rw [realGinibreAbsoluteCharacteristicMomentLIntegral_eq_traceDensity]
    _ = (∫⁻ B : RSqMat n,
          ENNReal.ofReal
            (|B.det| * ginibreTraceCorrelatedDensityReal n B)
          ∂realGinibreLebesgueMeasure n).toReal := by
      congr 1
      apply lintegral_congr
      intro B
      rw [ENNReal.ofReal_mul (abs_nonneg B.det)]
    _ = ∫ B : RSqMat n,
          |B.det| * ginibreTraceCorrelatedDensityReal n B
          ∂realGinibreLebesgueMeasure n := by
      symm
      exact integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun B => mul_nonneg (abs_nonneg _)
          (le_of_lt (ginibreTraceCorrelatedDensityReal_pos n B)))
        ((measurable_abs_det_matrixReal n).mul
          (measurable_ginibreTraceCorrelatedDensityReal n)).aestronglyMeasurable

end NumStability

end
