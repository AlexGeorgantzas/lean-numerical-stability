import Mathlib.LinearAlgebra.Matrix.Adjugate
import NumStability.Algorithms.TestMatrices.Higham28GaussianDirection
import NumStability.Algorithms.TestMatrices.Higham28GinibreCorollary31Factor
import NumStability.Algorithms.TestMatrices.Higham28GinibreGaussianBridge
import NumStability.Algorithms.TestMatrices.Higham28GinibreTraceDensity
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes.GinibreOrthogonalFiber

/-!
# Higham28GinibreOrthogonalFiber (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreOrthogonalFiber`
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

open MeasureTheory ProbabilityTheory Set Filter Matrix

open scoped ENNReal BigOperators RealInnerProductSpace Matrix.Norms.Frobenius

private local instance ginibreOrthogonalFiberMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private local instance ginibreOrthogonalFiberMeasureSpaceRSqMat (n : ℕ) :
    MeasureSpace (RSqMat n) := {
  toMeasurableSpace := MeasurableSpace.pi
  volume := realGinibreLebesgueMeasure n }

private local instance ginibreOrthogonalFiberMeasureSpaceNuisanceCore (n : ℕ) :
    MeasureSpace (RSqMat n × (Fin n → ℝ)) := {
  toMeasurableSpace := Prod.instMeasurableSpace
  volume := (volume : Measure (RSqMat n)).prod
    (volume : Measure (Fin n → ℝ)) }

private local instance ginibreOrthogonalFiberMeasureSpaceNuisance (n : ℕ) :
    MeasureSpace (GinibreIncidenceNuisance n) := {
  toMeasurableSpace := Prod.instMeasurableSpace
  volume := (volume : Measure (RSqMat n × (Fin n → ℝ))).prod volume }

private local instance ginibreOrthogonalFiberMeasureSpaceCoordinates (n : ℕ) :
    MeasureSpace (GinibreIncidenceCoordinates n) := {
  toMeasurableSpace := Prod.instMeasurableSpace
  volume := (volume : Measure (GinibreIncidenceNuisance n)).prod volume }

private local instance ginibreOrthogonalFiberStandardBorelNuisance (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceNuisance n) :=
  StandardBorelSpace.prod

private local instance ginibreOrthogonalFiberStandardBorelCoordinates (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceCoordinates n) :=
  StandardBorelSpace.prod

private instance ginibreOrthogonalFiberMatrixMeasurableAdd (n : ℕ) :
    MeasurableAdd (RSqMat n) := {
  measurable_const_add := by
    intro C
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    have hi : Measurable (fun A : RSqMat n => A i) := measurable_pi_apply i
    have hij : Measurable (fun A : RSqMat n => A i j) :=
      (measurable_pi_apply j).comp hi
    exact measurable_const.add hij
  measurable_add_const := by
    intro C
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    have hi : Measurable (fun A : RSqMat n => A i) := measurable_pi_apply i
    have hij : Measurable (fun A : RSqMat n => A i j) :=
      (measurable_pi_apply j).comp hi
    exact hij.add measurable_const }

private instance ginibreOrthogonalFiberMatrixVolumeIsAddHaar (n : ℕ) :
    (volume : Measure (RSqMat n)).IsAddHaarMeasure := {
  toIsFiniteMeasureOnCompacts := by
    change IsFiniteMeasureOnCompacts (Measure.pi (fun _ : Fin n =>
      Measure.pi (fun _ : Fin n => volume)))
    infer_instance
  toIsAddLeftInvariant := by
    change (Measure.pi (fun _ : Fin n =>
      Measure.pi (fun _ : Fin n => volume))).IsAddLeftInvariant
    infer_instance
  toIsOpenPosMeasure := by
    change (Measure.pi (fun _ : Fin n =>
      Measure.pi (fun _ : Fin n => volume))).IsOpenPosMeasure
    infer_instance }

private local instance ginibreOrthogonalFiberMatrixVolumeSigmaFinite (n : ℕ) :
    SigmaFinite (volume : Measure (RSqMat n)) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume)))
  infer_instance

private instance ginibreOrthogonalFiberNuisanceCoreMeasurableAdd (n : ℕ) :
    MeasurableAdd (RSqMat n × (Fin n → ℝ)) := {
  measurable_const_add := by
    intro c
    exact ((measurable_const_add c.1).comp measurable_fst).prodMk
      ((measurable_const_add c.2).comp measurable_snd)
  measurable_add_const := by
    intro c
    exact ((measurable_add_const c.1).comp measurable_fst).prodMk
      ((measurable_add_const c.2).comp measurable_snd) }

private instance ginibreOrthogonalFiberNuisanceCoreVolumeIsAddHaar (n : ℕ) :
    (volume : Measure (RSqMat n × (Fin n → ℝ))).IsAddHaarMeasure := by
  change ((volume : Measure (RSqMat n)).prod
    (volume : Measure (Fin n → ℝ))).IsAddHaarMeasure
  exact Measure.prod.instIsAddHaarMeasure _ _

private local instance ginibreOrthogonalFiberNuisanceCoreVolumeSigmaFinite (n : ℕ) :
    SigmaFinite (volume : Measure (RSqMat n × (Fin n → ℝ))) := by
  change SigmaFinite ((volume : Measure (RSqMat n)).prod
    (volume : Measure (Fin n → ℝ)))
  infer_instance

private instance ginibreOrthogonalFiberNuisanceVolumeIsAddHaar (n : ℕ) :
    (volume : Measure (GinibreIncidenceNuisance n)).IsAddHaarMeasure := by
  change ((volume : Measure (RSqMat n × (Fin n → ℝ))).prod
    (volume : Measure ℝ)).IsAddHaarMeasure
  exact Measure.prod.instIsAddHaarMeasure _ _

variable {M Y : Type*}
  [AddCommGroup M] [Module ℝ M]
  [AddCommGroup Y] [Module ℝ Y]

/-- The finite coordinate permutation
`(((C,z),b),y) ↦ ((b,z),(y,C))` preserves product Lebesgue measure. -/
theorem volume_preserving_ginibreCoordinateReorder (n : ℕ) :
    MeasurePreserving
      (fun q : GinibreIncidenceCoordinates n =>
        ((q.1.2, q.1.1.2), (q.2, q.1.1.1))) := by
  let A := Fin n → Fin n → ℝ
  let B := Fin n → ℝ
  let C := ℝ
  let D := Fin n → ℝ
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((A × B) × C) × D ≃ᵐ
        (A × B) × (C × D)) := volume_preserving_prodAssoc
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (A × B) × (C × D) ≃ᵐ
        A × (B × (C × D))) := volume_preserving_prodAssoc
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodComm : A × (B × (C × D)) ≃ᵐ
        (B × (C × D)) × A) := Measure.measurePreserving_swap
  have h4 : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (B × (C × D)) × A ≃ᵐ
        B × ((C × D) × A)) := volume_preserving_prodAssoc
  have h5 : MeasurePreserving
      (fun p : B × ((C × D) × A) =>
        (p.1, (p.2.1.1, (p.2.1.2, p.2.2)))) :=
    by
      have hp := (MeasurePreserving.id (volume : Measure B)).prod
        (volume_preserving_prodAssoc : MeasurePreserving
          (MeasurableEquiv.prodAssoc : (C × D) × A ≃ᵐ C × (D × A)))
      simpa [Prod.map] using hp
  have h6 : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : B × (C × (D × A)) ≃ᵐ
        (B × C) × (D × A)) := volume_preserving_prodAssoc.symm
  have h7 : MeasurePreserving
      (fun p : (B × C) × (D × A) => ((p.1.2, p.1.1), p.2)) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure B))
      (ν := (volume : Measure C))).prod
        (MeasurePreserving.id (volume : Measure (D × A)))
  have h := h7.comp (h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1)))))
  simpa [A, B, C, D, Function.comp_def] using h

/-- Affine block assembly is a coordinate permutation, hence preserves the
canonical product Lebesgue measure exactly. -/
theorem volume_preserving_ginibreCoordinatesFinMatrix (n : ℕ) :
    MeasurePreserving (@ginibreCoordinatesFinMatrix n) := by
  let Row := Fin (n + 1) → ℝ
  let LeftRow := Fin n → ℝ
  let rowSplit : Row ≃ᵐ ℝ × LeftRow :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  let outerSplit : (Fin (n + 1) → Row) ≃ᵐ Row × (Fin n → Row) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Row) (Fin.last n)
  have hrow : MeasurePreserving rowSplit.symm :=
    (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have hpair : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ LeftRow (Fin n)).symm :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ LeftRow (Fin n)).symm
  have hpi : MeasurePreserving
      (fun f : Fin n → ℝ × LeftRow => fun i => rowSplit.symm (f i)) := by
    simpa [rowSplit] using
      (volume_preserving_pi (fun _ : Fin n => hrow))
  have htop : MeasurePreserving
      (fun p : (Fin n → ℝ) × (Fin n → LeftRow) =>
        fun i => rowSplit.symm (p.1 i, p.2 i)) := by
    have h := hpi.comp hpair
    simpa [Function.comp_def] using h
  have hblocks : MeasurePreserving
      (fun p : (ℝ × LeftRow) × ((Fin n → ℝ) × (Fin n → LeftRow)) =>
        (rowSplit.symm p.1, fun i => rowSplit.symm (p.2.1 i, p.2.2 i))) := by
    have h := hrow.prod htop
    simpa [Prod.map] using h
  have houter : MeasurePreserving outerSplit.symm :=
    (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => Row) (Fin.last n)).symm
  have hjoin : MeasurePreserving
      (fun p : (ℝ × LeftRow) × ((Fin n → ℝ) × (Fin n → LeftRow)) =>
        outerSplit.symm
          (rowSplit.symm p.1, fun i => rowSplit.symm (p.2.1 i, p.2.2 i))) :=
    houter.comp hblocks
  have h := hjoin.comp (volume_preserving_ginibreCoordinateReorder n)
  have hrow_last (p : ℝ × LeftRow) :
      rowSplit.symm p (Fin.last n) = p.1 := by
    have hp := congrArg Prod.fst (rowSplit.apply_symm_apply p)
    exact hp
  have hrow_castSucc (p : ℝ × LeftRow) (j : Fin n) :
      rowSplit.symm p j.castSucc = p.2 j := by
    have hp := congrArg (fun r : ℝ × LeftRow => r.2 j)
      (rowSplit.apply_symm_apply p)
    change rowSplit.symm p ((Fin.last n).succAbove j) = p.2 j at hp
    simpa using hp
  have hfun : (fun q : GinibreIncidenceCoordinates n =>
      outerSplit.symm
        (rowSplit.symm (q.1.2, q.1.1.2),
          fun i => rowSplit.symm (q.2 i, q.1.1.1 i))) =
      @ginibreCoordinatesFinMatrix n := by
    funext q i j
    by_cases hi : i = Fin.last n
    · subst i
      by_cases hj : j = Fin.last n
      · subst j
        simp [outerSplit, rowSplit, ginibreCoordinatesFinMatrix,
          ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
          Matrix.reindex, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv]
        exact hrow_last (q.1.2, q.1.1.2)
      · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
        simp [outerSplit, rowSplit, ginibreCoordinatesFinMatrix,
          ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
          Matrix.reindex, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv]
        exact hrow_castSucc (q.1.2, q.1.1.2) j
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      by_cases hj : j = Fin.last n
      · subst j
        simp [outerSplit, rowSplit, ginibreCoordinatesFinMatrix,
          ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
          Matrix.reindex, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv]
        exact hrow_last (q.2 i, q.1.1.1 i)
      · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
        simp [outerSplit, rowSplit, ginibreCoordinatesFinMatrix,
          ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
          Matrix.reindex, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv]
        exact hrow_castSucc (q.2 i, q.1.1.1 i) j
  rw [← hfun]
  simpa [Function.comp_def] using h

/-- The normalized affine incidence measure is literally the canonical
product Lebesgue measure; there is no residual Haar scalar. -/
theorem ginibreIncidenceLebesgueMeasure_eq_volume (n : ℕ) :
    ginibreIncidenceLebesgueMeasure n =
      (volume : Measure (GinibreIncidenceCoordinates n)) := by
  let e : GinibreIncidenceCoordinates n ≃ᵐ GinibreRawMatrix (n + 1) :=
    (ginibreCoordinatesContinuousLinearEquiv n).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e := by
    simpa [e, ginibreCoordinatesContinuousLinearEquiv,
      ginibreCoordinatesLinearEquiv] using
        (volume_preserving_ginibreCoordinatesFinMatrix n)
  have hesymm := MeasurePreserving.symm e he
  unfold ginibreIncidenceLebesgueMeasure
  exact hesymm.map_eq

/-- Fixed-direction signed transfer with an arbitrary characteristic-polynomial
weight.  It deliberately stops at the nuisance-coordinate integral; later
applications can apply Fubini under the integrability hypothesis natural to
their particular weight. -/
theorem integral_ginibreSignedFixedFiber_of_orthogonal (n : ℕ)
    (y : Fin n → ℝ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (hcol : (fun i => Q i (Fin.last n)) =
      ginibreAffineDirectionScale n y • ginibreAffineFinEigenvector n y)
    (H : Polynomial ℝ → ℝ → ℝ) :
    (∫ u : GinibreIncidenceNuisance n,
      (ginibreIncidenceDeflatedBlock (u, y) -
          ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det *
        H (Matrix.charpoly (Matrix.of (ginibreIncidenceDeflatedBlock (u, y))))
          (ginibreIncidenceEigenvalue (u, y)) *
        realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y)))) =
      (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2)) *
        (gaussianPDFReal 0 1 0) ^ n *
          ∫ v : GinibreIncidenceNuisance n,
            ((show RSqMat n from v.1.1) -
                v.2 • (1 : RSqMat n)).det *
              H (Matrix.charpoly (Matrix.of
                (show RSqMat n from v.1.1))) v.2 *
              realGinibreDensityReal n (show RSqMat n from v.1.1) *
              (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
              gaussianPDFReal 0 1 v.2 := by
  let F := ginibreOrthogonalBlockToNuisanceLinearMap n Q
  let g : GinibreIncidenceNuisance n → ℝ := fun u =>
    (ginibreIncidenceDeflatedBlock (u, y) -
        ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det *
      H (Matrix.charpoly (Matrix.of (ginibreIncidenceDeflatedBlock (u, y))))
        (ginibreIncidenceEigenvalue (u, y)) *
      realGinibreDensityReal (n + 1)
        (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y)))
  let w : ℝ :=
    (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))
  have hw : 0 < w := by
    dsimp [w]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hdet : |LinearMap.det F| = w :=
    abs_det_ginibreOrthogonalBlockToNuisanceLinearMap_eq_projectiveWeight
      n y Q hQ hcol
  have hF : LinearMap.det F ≠ 0 := by
    intro hzero
    have habs : |LinearMap.det F| = 0 := by rw [hzero, abs_zero]
    exact (ne_of_gt hw) (hdet.symm.trans habs)
  have hcov := integral_linearMap_eq_abs_det_mul
    (volume : Measure (GinibreIncidenceNuisance n)) F hF g
  rw [hdet] at hcov
  calc
    (∫ u : GinibreIncidenceNuisance n,
      (ginibreIncidenceDeflatedBlock (u, y) -
          ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det *
        H (Matrix.charpoly (Matrix.of (ginibreIncidenceDeflatedBlock (u, y))))
          (ginibreIncidenceEigenvalue (u, y)) *
        realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y)))) =
        w * ∫ v : GinibreIncidenceNuisance n, g (F v) := hcov
    _ = w * ∫ v : GinibreIncidenceNuisance n,
          (gaussianPDFReal 0 1 0) ^ n *
            (((show RSqMat n from v.1.1) -
                v.2 • (1 : RSqMat n)).det *
              H (Matrix.charpoly (Matrix.of
                (show RSqMat n from v.1.1))) v.2 *
              realGinibreDensityReal n (show RSqMat n from v.1.1) *
              (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
              gaussianPDFReal 0 1 v.2) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with v
      exact ginibreSignedFixedFiber_integrand_eq n y Q hQ hcol H v
    _ = w * (gaussianPDFReal 0 1 0) ^ n *
          ∫ v : GinibreIncidenceNuisance n,
            ((show RSqMat n from v.1.1) -
                v.2 • (1 : RSqMat n)).det *
              H (Matrix.charpoly (Matrix.of
                (show RSqMat n from v.1.1))) v.2 *
              realGinibreDensityReal n (show RSqMat n from v.1.1) *
              (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
              gaussianPDFReal 0 1 v.2 := by
      rw [integral_const_mul]
      ring

/-- Integrating the block variables leaves exactly the absolute
characteristic-moment `lintegral`; the auxiliary bottom row has mass one. -/
theorem lintegral_ginibreOrthogonalBlockDensity (n : ℕ) :
    (∫⁻ v : GinibreIncidenceNuisance n,
      ENNReal.ofReal
        (|((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det| *
          realGinibreDensityReal n (show RSqMat n from v.1.1) *
          (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
          gaussianPDFReal 0 1 v.2)) =
      realGinibreAbsoluteCharacteristicMomentLIntegral n := by
  let Z : (Fin n → ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (∏ i : Fin n, gaussianPDFReal 0 1 (z i))
  let H : RSqMat n → ℝ → ℝ≥0∞ := fun C l =>
    ENNReal.ofReal
      (|(C - l • (1 : RSqMat n)).det| *
        realGinibreDensityReal n C * gaussianPDFReal 0 1 l)
  have hZ : Measurable Z := by
    unfold Z
    fun_prop
  have hH (C : RSqMat n) : Measurable (H C) := by
    unfold H
    apply Measurable.ennreal_ofReal
    have hdet := (measurable_abs_det_ginibreShiftReal n).comp
      ((show Measurable (fun _ : ℝ => C) from measurable_const).prodMk measurable_id)
    exact (hdet.mul (show Measurable (fun _ : ℝ =>
      realGinibreDensityReal n C) from measurable_const)).mul
        (measurable_gaussianPDFReal 0 1)
  have hpoint (C : RSqMat n) (z : Fin n → ℝ) (l : ℝ) :
      ENNReal.ofReal
        (|(C - l • (1 : RSqMat n)).det| *
          realGinibreDensityReal n C *
          (∏ i : Fin n, gaussianPDFReal 0 1 (z i)) *
          gaussianPDFReal 0 1 l) = Z z * H C l := by
    rw [show |(C - l • (1 : RSqMat n)).det| *
          realGinibreDensityReal n C *
          (∏ i : Fin n, gaussianPDFReal 0 1 (z i)) *
          gaussianPDFReal 0 1 l =
        (∏ i : Fin n, gaussianPDFReal 0 1 (z i)) *
          (|(C - l • (1 : RSqMat n)).det| *
            realGinibreDensityReal n C * gaussianPDFReal 0 1 l) by ring]
    rw [ENNReal.ofReal_mul
      (Finset.prod_nonneg fun i hi => gaussianPDFReal_nonneg 0 1 (z i))]
  have hfull : Measurable (fun v : GinibreIncidenceNuisance n =>
      ENNReal.ofReal
        (|((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det| *
          realGinibreDensityReal n (show RSqMat n from v.1.1) *
          (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
          gaussianPDFReal 0 1 v.2)) := by
    apply Measurable.ennreal_ofReal
    have hCcoord : Measurable (fun v : GinibreIncidenceNuisance n =>
        (show RSqMat n from v.1.1)) :=
      measurable_fst.comp measurable_fst
    have hlcoord : Measurable (fun v : GinibreIncidenceNuisance n => v.2) :=
      measurable_snd
    have hdet := (measurable_abs_det_ginibreShiftReal n).comp
      (hCcoord.prodMk hlcoord)
    have hC := (measurable_realGinibreDensityReal n).comp hCcoord
    have hz : Measurable (fun v : GinibreIncidenceNuisance n =>
        ∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) := by fun_prop
    have hl := (measurable_gaussianPDFReal 0 1).comp hlcoord
    exact ((hdet.mul hC).mul hz).mul hl
  calc
    (∫⁻ v : GinibreIncidenceNuisance n,
      ENNReal.ofReal
        (|((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det| *
          realGinibreDensityReal n (show RSqMat n from v.1.1) *
          (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
          gaussianPDFReal 0 1 v.2)) =
        ∫⁻ p : RSqMat n × (Fin n → ℝ), ∫⁻ l : ℝ,
          ENNReal.ofReal
            (|(p.1 - l • (1 : RSqMat n)).det| *
              realGinibreDensityReal n p.1 *
              (∏ i : Fin n, gaussianPDFReal 0 1 (p.2 i)) *
              gaussianPDFReal 0 1 l) := by
      rw [Measure.volume_eq_prod]
      exact lintegral_prod _ hfull.aemeasurable
    _ = ∫⁻ C : RSqMat n, ∫⁻ z : Fin n → ℝ, ∫⁻ l : ℝ,
          ENNReal.ofReal
            (|(C - l • (1 : RSqMat n)).det| *
              realGinibreDensityReal n C *
              (∏ i : Fin n, gaussianPDFReal 0 1 (z i)) *
              gaussianPDFReal 0 1 l) := by
      rw [Measure.volume_eq_prod]
      have hinner : Measurable (fun p : RSqMat n × (Fin n → ℝ) =>
          ∫⁻ l : ℝ,
            ENNReal.ofReal
              (|(p.1 - l • (1 : RSqMat n)).det| *
                realGinibreDensityReal n p.1 *
                (∏ i : Fin n, gaussianPDFReal 0 1 (p.2 i)) *
                gaussianPDFReal 0 1 l)) :=
        hfull.lintegral_prod_right'
      exact lintegral_prod _ hinner.aemeasurable
    _ = ∫⁻ C : RSqMat n, ∫⁻ z : Fin n → ℝ, ∫⁻ l : ℝ,
          Z z * H C l := by
      apply lintegral_congr
      intro C
      apply lintegral_congr
      intro z
      apply lintegral_congr
      intro l
      exact hpoint C z l
    _ = ∫⁻ C : RSqMat n,
          (∫⁻ z : Fin n → ℝ, Z z) * (∫⁻ l : ℝ, H C l) := by
      apply lintegral_congr
      intro C
      exact lintegral_lintegral_mul hZ.aemeasurable (hH C).aemeasurable
    _ = ∫⁻ C : RSqMat n, ∫⁻ l : ℝ, H C l := by
      rw [show (∫⁻ z : Fin n → ℝ, Z z) = 1 by
        exact lintegral_standardGaussianVectorDensity n]
      simp
    _ = realGinibreAbsoluteCharacteristicMomentLIntegral n := by
      rw [realGinibreAbsoluteCharacteristicMomentLIntegral_eq_jointDensity]
      have hjoint : Measurable (fun p : RSqMat n × ℝ =>
          ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
            ENNReal.ofReal
              (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2)) :=
        ((measurable_abs_det_ginibreShift n).mul
          (((measurable_realGinibreDensityReal n).comp measurable_fst).mul
            ((measurable_gaussianPDFReal 0 1).comp measurable_snd)).ennreal_ofReal)
      rw [lintegral_prod _ hjoint.aemeasurable]
      apply lintegral_congr
      intro C
      apply lintegral_congr
      intro l
      unfold H
      rw [show |(C - l • (1 : RSqMat n)).det| *
          realGinibreDensityReal n C * gaussianPDFReal 0 1 l =
        |(C - l • (1 : RSqMat n)).det| *
          (realGinibreDensityReal n C * gaussianPDFReal 0 1 l) by ring]
      rw [ENNReal.ofReal_mul (abs_nonneg _)]

/-- The fixed affine-direction incidence integral after choosing an
orthogonal representative of that direction.  The representative disappears
from the right-hand side: its only contribution is the projective Jacobian. -/
theorem lintegral_ginibreFixedFiber_of_orthogonal (n : ℕ)
    (y : Fin n → ℝ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (hcol : (fun i => Q i (Fin.last n)) =
      ginibreAffineDirectionScale n y • ginibreAffineFinEigenvector n y) :
    (∫⁻ u : GinibreIncidenceNuisance n,
      ENNReal.ofReal
        (|(ginibreIncidenceDeflatedBlock (u, y) -
            ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
          realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y))))) =
      ENNReal.ofReal
          ((1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) *
        ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
          realGinibreAbsoluteCharacteristicMomentLIntegral n := by
  let F := ginibreOrthogonalBlockToNuisanceLinearMap n Q
  let g : GinibreIncidenceNuisance n → ℝ≥0∞ := fun u =>
    ENNReal.ofReal
      (|(ginibreIncidenceDeflatedBlock (u, y) -
          ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
        realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y))))
  let w : ℝ :=
    (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))
  have hw : 0 < w := by
    dsimp [w]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hdet : |LinearMap.det F| = w := by
    exact abs_det_ginibreOrthogonalBlockToNuisanceLinearMap_eq_projectiveWeight
      n y Q hQ hcol
  have hF : LinearMap.det F ≠ 0 := by
    intro hzero
    have habs : |LinearMap.det F| = 0 := by rw [hzero, abs_zero]
    exact (ne_of_gt hw) (hdet.symm.trans habs)
  have hcov := lintegral_linearMap_eq_abs_det_mul
    (volume : Measure (GinibreIncidenceNuisance n)) F hF g
  rw [hdet] at hcov
  calc
    (∫⁻ u : GinibreIncidenceNuisance n,
      ENNReal.ofReal
        (|(ginibreIncidenceDeflatedBlock (u, y) -
            ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
          realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y))))) =
        ENNReal.ofReal w * ∫⁻ v : GinibreIncidenceNuisance n, g (F v) := by
      exact hcov
    _ = ENNReal.ofReal w *
        ∫⁻ v : GinibreIncidenceNuisance n,
          ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
            ENNReal.ofReal
              (|((show RSqMat n from v.1.1) -
                    v.2 • (1 : RSqMat n)).det| *
                realGinibreDensityReal n (show RSqMat n from v.1.1) *
                (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
                gaussianPDFReal 0 1 v.2) := by
      congr 1
      apply lintegral_congr
      intro v
      have hpoint := congrArg ENNReal.ofReal
        (ginibreFixedFiber_integrand_eq n y Q hQ hcol v)
      rw [ENNReal.ofReal_mul
        (pow_nonneg (gaussianPDFReal_nonneg 0 1 0) n)] at hpoint
      exact hpoint
    _ = ENNReal.ofReal w * ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
          realGinibreAbsoluteCharacteristicMomentLIntegral n := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_ginibreOrthogonalBlockDensity]
      ring

/-- Premise-free fixed-direction formula.  The orthogonal representative is
chosen pointwise, so no measurable-selection hypothesis is needed. -/
theorem lintegral_ginibreFixedFiber (n : ℕ) (y : Fin n → ℝ) :
    (∫⁻ u : GinibreIncidenceNuisance n,
      ENNReal.ofReal
        (|(ginibreIncidenceDeflatedBlock (u, y) -
            ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
          realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y))))) =
      ENNReal.ofReal
          ((1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) *
        ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
          realGinibreAbsoluteCharacteristicMomentLIntegral n := by
  obtain ⟨Q, hQ, hcol⟩ := exists_orthogonal_lastColumn_affine n y
  exact lintegral_ginibreFixedFiber_of_orthogonal n y Q hQ hcol

/-- Integrability of the affine projective weight, extracted from its already
evaluated (strictly positive) ordinary integral. -/
theorem integrable_ginibreProjectiveWeight (n : ℕ) :
    Integrable (fun y : Fin n → ℝ =>
      (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) := by
  by_contra h
  have hzero : (∫ y : Fin n → ℝ,
      (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) = 0 :=
    integral_undef h
  rw [integral_ginibreProjectiveWeight] at hzero
  have hpos : 0 <
      Real.pi ^ (((n : ℝ) + 1) / 2) /
        Real.Gamma (((n : ℝ) + 1) / 2) := by
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.Gamma_pos_of_pos (by positivity))
  linarith

/-- The full affine incidence integral is the Corollary 3.1 normalization
times the absolute characteristic-moment `lintegral`. -/
theorem lintegral_ginibreIncidence_gaussian_eq_corollary31Factor_mul_momentLIntegral
    (n : ℕ) :
    (∫⁻ q : GinibreIncidenceCoordinates n,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))
      ∂ginibreIncidenceLebesgueMeasure n) =
      ENNReal.ofReal (ginibreCorollary31Factor (n + 1)) *
        realGinibreAbsoluteCharacteristicMomentLIntegral n := by
  let W : (Fin n → ℝ) → ℝ := fun y =>
    (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))
  have hW : Measurable W := by
    unfold W
    fun_prop
  have hweight_eq :
      (fun q : GinibreIncidenceCoordinates n =>
        |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det|) =
      (fun q => |(ginibreIncidenceTangentMatrix q).det|) := by
    funext q
    have hneg : ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n) =
        -(ginibreIncidenceTangentMatrix q) := by
      unfold ginibreIncidenceTangentMatrix
      abel
    rw [hneg, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul]
  have hdet : Measurable (fun q : GinibreIncidenceCoordinates n =>
      ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det|) := by
    apply Measurable.ennreal_ofReal
    rw [hweight_eq]
    exact continuous_ginibreIncidenceTangentDet.abs.measurable
  have hdensity : Measurable (fun q : GinibreIncidenceCoordinates n =>
      ENNReal.ofReal (realGinibreDensityReal (n + 1)
        (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))) :=
    ((measurable_realGinibreDensityReal (n + 1)).comp
      (measurable_ginibreCoordinatesFinMatrix.comp
        measurable_ginibreIncidenceChart)).ennreal_ofReal
  have hfull : Measurable (fun q : GinibreIncidenceCoordinates n =>
      ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
        ENNReal.ofReal (realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))) :=
    hdet.mul hdensity
  rw [ginibreIncidenceLebesgueMeasure_eq_volume]
  calc
    (∫⁻ q : GinibreIncidenceCoordinates n,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))) =
      ∫⁻ y : Fin n → ℝ, ∫⁻ u : GinibreIncidenceNuisance n,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock (u, y) -
          ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y)))) := by
      exact lintegral_prod_symm' _ hfull
    _ = ∫⁻ y : Fin n → ℝ,
        ENNReal.ofReal (W y) *
          ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
            realGinibreAbsoluteCharacteristicMomentLIntegral n := by
      apply lintegral_congr
      intro y
      calc
        (∫⁻ u : GinibreIncidenceNuisance n,
          ENNReal.ofReal |(ginibreIncidenceDeflatedBlock (u, y) -
            ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
            ENNReal.ofReal (realGinibreDensityReal (n + 1)
              (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y))))) =
            ∫⁻ u : GinibreIncidenceNuisance n,
              ENNReal.ofReal
                (|(ginibreIncidenceDeflatedBlock (u, y) -
                    ginibreIncidenceEigenvalue (u, y) •
                      (1 : RSqMat n)).det| *
                  realGinibreDensityReal (n + 1)
                    (ginibreCoordinatesFinMatrix
                      (ginibreIncidenceChart (u, y)))) := by
          apply lintegral_congr
          intro u
          rw [ENNReal.ofReal_mul (abs_nonneg _)]
        _ = ENNReal.ofReal (W y) *
              ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
                realGinibreAbsoluteCharacteristicMomentLIntegral n := by
          exact lintegral_ginibreFixedFiber n y
    _ = (∫⁻ y : Fin n → ℝ, ENNReal.ofReal (W y)) *
          (ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
            realGinibreAbsoluteCharacteristicMomentLIntegral n) := by
      simp_rw [mul_assoc]
      exact lintegral_mul_const'' _ hW.ennreal_ofReal.aemeasurable
    _ = ENNReal.ofReal (∫ y : Fin n → ℝ, W y) *
          (ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
            realGinibreAbsoluteCharacteristicMomentLIntegral n) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        (integrable_ginibreProjectiveWeight n)
        (ae_of_all _ fun y => Real.rpow_nonneg (by positivity) _)]
    _ = ENNReal.ofReal (ginibreCorollary31Factor (n + 1)) *
          realGinibreAbsoluteCharacteristicMomentLIntegral n := by
      rw [show ENNReal.ofReal (∫ y : Fin n → ℝ, W y) *
            (ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
              realGinibreAbsoluteCharacteristicMomentLIntegral n) =
          (ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
            ENNReal.ofReal (∫ y : Fin n → ℝ, W y)) *
              realGinibreAbsoluteCharacteristicMomentLIntegral n by ac_rfl]
      rw [← ENNReal.ofReal_mul
        (pow_nonneg (gaussianPDFReal_nonneg 0 1 0) n)]
      rw [show (∫ y : Fin n → ℝ, W y) =
          ∫ y : Fin n → ℝ,
            (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2)) by rfl]
      rw [gaussianZeroPow_mul_integral_ginibreProjectiveWeight]

/-- `ENNReal` form of the exact Corollary 3.1 bridge. -/
theorem ofReal_expectedRealEigenvalueCount_succ_eq_corollary31Factor_mul_momentLIntegral
    (n : ℕ) :
    ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) =
      ENNReal.ofReal (ginibreCorollary31Factor (n + 1)) *
        realGinibreAbsoluteCharacteristicMomentLIntegral n := by
  calc
    ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) =
        ∫⁻ q : GinibreIncidenceCoordinates n,
          ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
            ENNReal.ofReal (realGinibreDensityReal (n + 1)
              (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))
          ∂ginibreIncidenceLebesgueMeasure n :=
      (lintegral_ginibreIncidence_gaussian_eq_expected n).symm
    _ = _ :=
      lintegral_ginibreIncidence_gaussian_eq_corollary31Factor_mul_momentLIntegral n

/-- The unconditional real-valued Corollary 3.1 identity. -/
theorem expectedRealEigenvalueCount_succ_eq_corollary31Factor_mul_moment
    (n : ℕ) :
    expectedRealEigenvalueCount (n + 1) =
      ginibreCorollary31Factor (n + 1) *
        realGinibreAbsoluteCharacteristicMoment n := by
  have hexpected : 0 ≤ expectedRealEigenvalueCount (n + 1) := by
    unfold expectedRealEigenvalueCount
    exact integral_nonneg fun A => Nat.cast_nonneg _
  have hfactor : 0 ≤ ginibreCorollary31Factor (n + 1) := by
    unfold ginibreCorollary31Factor
    exact div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (le_of_lt (Real.Gamma_pos_of_pos (by positivity))))
  have h := congrArg ENNReal.toReal
    (ofReal_expectedRealEigenvalueCount_succ_eq_corollary31Factor_mul_momentLIntegral n)
  rw [ENNReal.toReal_ofReal hexpected, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hfactor,
    ← realGinibreAbsoluteCharacteristicMoment_eq_toReal_lintegral] at h
  exact h

end NumStability

end
