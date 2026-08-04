import NumStability.Algorithms.TestMatrices.Higham28GinibrePlaneIncidence
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes.GinibrePlaneChart

/-!
# Higham28GinibrePlaneChart (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibrePlaneChart`
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

private noncomputable abbrev ginibrePlaneRectangularModule (m : ℕ) :
    Module ℝ (Matrix (Fin m) (Fin 2) ℝ) :=
  @Matrix.module (Fin m) (Fin 2) ℝ ℝ inferInstance inferInstance inferInstance

local instance ginibrePlaneMatrixNormedAddCommGroup (a b : ℕ) :
    NormedAddCommGroup (Matrix (Fin a) (Fin b) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin a → Fin b → ℝ))

local instance ginibrePlaneMatrixNormedSpace (a b : ℕ) :
    NormedSpace ℝ (Matrix (Fin a) (Fin b) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin a → Fin b → ℝ))

local instance ginibrePlaneChartMeasurableSpace (m : ℕ) :
    MeasurableSpace (GinibrePlaneChartCoordinates m) :=
  borel (GinibrePlaneChartCoordinates m)

local instance ginibrePlaneChartBorelSpace (m : ℕ) :
    BorelSpace (GinibrePlaneChartCoordinates m) := ⟨rfl⟩

/-- The full derivative candidate.  In the nuisance/graph splitting it is
block lower triangular with identity in the nuisance block. -/
def ginibrePlaneChartDerivativeLinearMap {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    GinibrePlaneChartCoordinates m →ₗ[ℝ]
      GinibrePlaneChartCoordinates m :=
  @LinearMap.lowerBlock (GinibrePlaneChartNuisance m)
    (Matrix (Fin m) (Fin 2) ℝ)
    inferInstance inferInstance inferInstance (ginibrePlaneRectangularModule m)
    (ginibrePlaneChartNuisanceDerivative q) (ginibrePlaneSylvesterLinearMap q)

/-- The chart Jacobian reduces exactly to the determinant of the Sylvester
operator. -/
theorem ginibrePlaneChartDerivativeLinearMap_det {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    (ginibrePlaneChartDerivativeLinearMap q).det =
      (@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
        inferInstance (ginibrePlaneRectangularModule m))
        (ginibrePlaneSylvesterLinearMap q) := by
  simpa [ginibrePlaneChartDerivativeLinearMap] using
    (@LinearMap.det_lowerBlock (GinibrePlaneChartNuisance m)
      (Matrix (Fin m) (Fin 2) ℝ)
      inferInstance inferInstance inferInstance
      (ginibrePlaneRectangularModule m)
      inferInstance inferInstance
      inferInstance inferInstance
      (ginibrePlaneChartNuisanceDerivative q)
      (ginibrePlaneSylvesterLinearMap q))

set_option maxHeartbeats 1200000 in
/-- The displayed block-lower map is the actual Fréchet derivative of the
forced upper-right block. -/
theorem hasFDerivAt_ginibrePlaneChartTopRight {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    HasFDerivAt ginibrePlaneChartTopRight
      ((ContinuousLinearMap.snd ℝ (GinibrePlaneChartNuisance m)
          (Matrix (Fin m) (Fin 2) ℝ)).comp
        (ginibrePlaneChartDerivativeLinearMap q).toContinuousLinearMap) q := by
  change HasFDerivAt
    (fun q' => fun i => fun j => ginibrePlaneChartTopRight q' i j)
    ((ContinuousLinearMap.snd ℝ (GinibrePlaneChartNuisance m)
        (Matrix (Fin m) (Fin 2) ℝ)).comp
      (ginibrePlaneChartDerivativeLinearMap q).toContinuousLinearMap) q
  refine hasFDerivAt_pi'' (𝕜 := ℝ) (E := GinibrePlaneChartCoordinates m)
    (ι := Fin m) (F' := fun _ : Fin m => Fin 2 → ℝ) (x := q)
    (Φ := fun q' i => fun j => ginibrePlaneChartTopRight q' i j)
    (Φ' := (ContinuousLinearMap.snd ℝ (GinibrePlaneChartNuisance m)
      (Matrix (Fin m) (Fin 2) ℝ)).comp
        (ginibrePlaneChartDerivativeLinearMap q).toContinuousLinearMap) ?_
  intro i
  refine hasFDerivAt_pi'' (𝕜 := ℝ) (E := GinibrePlaneChartCoordinates m)
    (ι := Fin 2) (F' := fun _ : Fin 2 => ℝ) (x := q)
    (Φ := fun q' j => ginibrePlaneChartTopRight q' i j)
    (Φ' := (ContinuousLinearMap.proj i).comp <|
      (ContinuousLinearMap.snd ℝ (GinibrePlaneChartNuisance m)
        (Matrix (Fin m) (Fin 2) ℝ)).comp
          (ginibrePlaneChartDerivativeLinearMap q).toContinuousLinearMap) ?_
  intro j
  let fstQ : GinibrePlaneChartCoordinates m →L[ℝ]
      GinibrePlaneChartNuisance m := ContinuousLinearMap.fst ℝ _ _
  let sndQ : GinibrePlaneChartCoordinates m →L[ℝ]
      Matrix (Fin m) (Fin 2) ℝ := ContinuousLinearMap.snd ℝ _ _
  let fstN : GinibrePlaneChartNuisance m →L[ℝ]
      (RSqMat m × Matrix (Fin 2) (Fin m) ℝ) :=
    ContinuousLinearMap.fst ℝ _ _
  let sndN : GinibrePlaneChartNuisance m →L[ℝ] RSqMat 2 :=
    ContinuousLinearMap.snd ℝ _ _
  let fstBW : (RSqMat m × Matrix (Fin 2) (Fin m) ℝ) →L[ℝ]
      RSqMat m := ContinuousLinearMap.fst ℝ _ _
  let sndBW : (RSqMat m × Matrix (Fin 2) (Fin m) ℝ) →L[ℝ]
      Matrix (Fin 2) (Fin m) ℝ := ContinuousLinearMap.snd ℝ _ _
  let BEntry (a b : Fin m) : GinibrePlaneChartCoordinates m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj b).comp <|
      (ContinuousLinearMap.proj a).comp <| fstBW.comp <| fstN.comp fstQ
  let WEntry (a : Fin 2) (b : Fin m) :
      GinibrePlaneChartCoordinates m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj b).comp <|
      (ContinuousLinearMap.proj a).comp <| sndBW.comp <| fstN.comp fstQ
  let EEntry (a b : Fin 2) : GinibrePlaneChartCoordinates m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj b).comp <|
      (ContinuousLinearMap.proj a).comp <| sndN.comp fstQ
  let YEntry (a : Fin m) (b : Fin 2) :
      GinibrePlaneChartCoordinates m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj b).comp <|
      (ContinuousLinearMap.proj a).comp sndQ
  have hBEntry_apply (a b : Fin m) (dq : GinibrePlaneChartCoordinates m) :
      BEntry a b dq = dq.1.1.1 a b := rfl
  have hWEntry_apply (a : Fin 2) (b : Fin m)
      (dq : GinibrePlaneChartCoordinates m) :
      WEntry a b dq = dq.1.1.2 a b := rfl
  have hEEntry_apply (a b : Fin 2) (dq : GinibrePlaneChartCoordinates m) :
      EEntry a b dq = dq.1.2 a b := rfl
  have hYEntry_apply (a : Fin m) (b : Fin 2)
      (dq : GinibrePlaneChartCoordinates m) :
      YEntry a b dq = dq.2 a b := rfl
  have hB (a b : Fin m) :
      HasFDerivAt (fun q' : GinibrePlaneChartCoordinates m => q'.1.1.1 a b)
        (BEntry a b) q := by
    simpa [BEntry, fstBW, fstN, fstQ] using (BEntry a b).hasFDerivAt
  have hW (a : Fin 2) (b : Fin m) :
      HasFDerivAt (fun q' : GinibrePlaneChartCoordinates m => q'.1.1.2 a b)
        (WEntry a b) q := by
    simpa [WEntry, sndBW, fstN, fstQ] using (WEntry a b).hasFDerivAt
  have hE (a b : Fin 2) :
      HasFDerivAt (fun q' : GinibrePlaneChartCoordinates m => q'.1.2 a b)
        (EEntry a b) q := by
    simpa [EEntry, sndN, fstQ] using (EEntry a b).hasFDerivAt
  have hY (a : Fin m) (b : Fin 2) :
      HasFDerivAt (fun q' : GinibrePlaneChartCoordinates m => q'.2 a b)
        (YEntry a b) q := by
    simpa [YEntry, sndQ] using (YEntry a b).hasFDerivAt
  have hWY (a b : Fin 2) : HasFDerivAt
      (fun q' : GinibrePlaneChartCoordinates m =>
        ∑ l : Fin m, q'.1.1.2 a l * q'.2 l b)
      (∑ l : Fin m,
        (q.1.1.2 a l • YEntry l b + q.2 l b • WEntry a l)) q := by
    convert HasFDerivAt.sum (u := Finset.univ)
      (fun l hl => (hW a l).mul (hY l b)) using 1
    funext dq
    simp [Finset.sum_apply]
  have hC (a b : Fin 2) : HasFDerivAt
      (fun q' : GinibrePlaneChartCoordinates m =>
        ginibrePlaneChartAction q' a b)
      (EEntry a b + ∑ l : Fin m,
        (q.1.1.2 a l • YEntry l b + q.2 l b • WEntry a l)) q := by
    simpa [ginibrePlaneChartAction, Matrix.mul_apply] using (hE a b).add (hWY a b)
  have hYC : HasFDerivAt
      (fun q' : GinibrePlaneChartCoordinates m =>
        ∑ k : Fin 2, q'.2 i k * ginibrePlaneChartAction q' k j)
      (∑ k : Fin 2,
        (q.2 i k •
            (EEntry k j + ∑ l : Fin m,
              (q.1.1.2 k l • YEntry l j + q.2 l j • WEntry k l)) +
          ginibrePlaneChartAction q k j • YEntry i k)) q := by
    convert HasFDerivAt.sum (u := Finset.univ)
      (fun k hk => (hY i k).mul (hC k j)) using 1
  have hBY : HasFDerivAt
      (fun q' : GinibrePlaneChartCoordinates m =>
        ∑ l : Fin m, q'.1.1.1 i l * q'.2 l j)
      (∑ l : Fin m,
        (q.1.1.1 i l • YEntry l j + q.2 l j • BEntry i l)) q := by
    convert HasFDerivAt.sum (u := Finset.univ)
      (fun l hl => (hB i l).mul (hY l j)) using 1
    funext dq
    simp [Finset.sum_apply]
  have hcoord := hYC.sub hBY
  convert hcoord using 1
  · apply ContinuousLinearMap.ext
    intro dq
    change
      (ginibrePlaneChartNuisanceDerivative q dq.1 +
        ginibrePlaneSylvesterLinearMap q dq.2) i j = _
    rw [ContinuousLinearMap.sub_apply]
    simp_rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    simp [ginibrePlaneChartNuisanceDerivative, ginibrePlaneSylvesterLinearMap,
      ginibrePlaneChartAction, ginibrePlaneChartDeflatedBlock,
      Matrix.mul_apply, Finset.sum_apply]
    simp_rw [hBEntry_apply, hWEntry_apply, hEEntry_apply, hYEntry_apply]
    simp_rw [Finset.sum_add_distrib]
    ring_nf
    simp only [Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib]
    have hW0 :
        (∑ x : Fin m, q.2 i 0 * dq.1.1.2 0 x * q.2 x j) =
          ∑ x : Fin m, q.2 i 0 * q.2 x j * dq.1.1.2 0 x := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    have hW1 :
        (∑ x : Fin m, q.2 i 1 * dq.1.1.2 1 x * q.2 x j) =
          ∑ x : Fin m, q.2 i 1 * q.2 x j * dq.1.1.2 1 x := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    have hBswap :
        (∑ x : Fin m, dq.1.1.1 i x * q.2 x j) =
          ∑ x : Fin m, q.2 x j * dq.1.1.1 i x := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hW0, hW1, hBswap]
    simp only [mul_assoc]
    ring

/-- The block chart itself has the advertised derivative everywhere. -/
theorem hasFDerivAt_ginibrePlaneChart {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    HasFDerivAt ginibrePlaneChart
      (ginibrePlaneChartDerivativeLinearMap q).toContinuousLinearMap q := by
  have hpair := (hasFDerivAt_fst (p := q)).prodMk
    (hasFDerivAt_ginibrePlaneChartTopRight q)
  have hderiv :
      (ContinuousLinearMap.fst ℝ (GinibrePlaneChartNuisance m)
        (Matrix (Fin m) (Fin 2) ℝ)).prod
      ((ContinuousLinearMap.snd ℝ (GinibrePlaneChartNuisance m)
        (Matrix (Fin m) (Fin 2) ℝ)).comp
        (ginibrePlaneChartDerivativeLinearMap q).toContinuousLinearMap) =
      (ginibrePlaneChartDerivativeLinearMap q).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro dq
    simp [ginibrePlaneChartDerivativeLinearMap, LinearMap.lowerBlock,
      LinearMap.coe_toContinuousLinearMap']
  have hpair' := hderiv ▸ hpair
  simpa [ginibrePlaneChart] using hpair'

theorem fderiv_ginibrePlaneChart {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    fderiv ℝ ginibrePlaneChart q =
      (ginibrePlaneChartDerivativeLinearMap q).toContinuousLinearMap :=
  (hasFDerivAt_ginibrePlaneChart q).fderiv

theorem differentiable_ginibrePlaneChart {m : ℕ} :
    Differentiable ℝ (@ginibrePlaneChart m) :=
  fun q => (hasFDerivAt_ginibrePlaneChart q).differentiableAt

theorem continuous_ginibrePlaneChart {m : ℕ} :
    Continuous (@ginibrePlaneChart m) :=
  differentiable_ginibrePlaneChart.continuous

theorem measurable_ginibrePlaneChart {m : ℕ} :
    Measurable (@ginibrePlaneChart m) :=
  continuous_ginibrePlaneChart.measurable

end NumStability

end
