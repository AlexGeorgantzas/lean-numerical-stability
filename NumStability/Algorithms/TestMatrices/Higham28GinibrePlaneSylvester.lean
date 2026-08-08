import Mathlib.RingTheory.Norm.Transitivity
import NumStability.Algorithms.TestMatrices.Higham28GinibreCharacteristicProduct
import NumStability.Algorithms.TestMatrices.Higham28GinibrePlaneChart
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes.GinibrePlaneSylvester

/-!
# Higham28GinibrePlaneSylvester (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibrePlaneSylvester`
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

open MeasureTheory

open scoped BigOperators Polynomial

local instance ginibrePlaneSylvesterBridgeModule (m : ℕ) :
    Module ℝ (Matrix (Fin m) (Fin 2) ℝ) :=
  @Matrix.module (Fin m) (Fin 2) ℝ ℝ inferInstance inferInstance inferInstance

private local instance ginibrePlaneSylvesterMeasurableSpace (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- The Sylvester operator with independent deflated block `D` and
two-dimensional action `C`. -/
def ginibrePlaneSylvesterOperator {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2) :
    Matrix (Fin m) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin 2) ℝ where
  toFun X := X * C - D * X
  map_add' X Y := by
    simp [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg]
    abel
  map_smul' r X := by
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- The standard-basis matrix coefficient of the Sylvester operator. -/
theorem ginibrePlaneSylvesterOperator_toMatrix_apply {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2) (ia jb : Fin m × Fin 2) :
    LinearMap.toMatrix (Matrix.stdBasis ℝ (Fin m) (Fin 2))
        (Matrix.stdBasis ℝ (Fin m) (Fin 2))
        (ginibrePlaneSylvesterOperator D C) ia jb =
      (if ia.1 = jb.1 then C jb.2 ia.2 else 0) -
        (if ia.2 = jb.2 then D ia.1 jb.1 else 0) := by
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single]
  simp only [ginibrePlaneSylvesterOperator, LinearMap.coe_mk,
    AddHom.coe_mk, map_sub, Finsupp.sub_apply]
  rw [ginibrePlane_stdBasis_repr_apply_pair,
    ginibrePlane_stdBasis_repr_apply_pair]
  fin_cases b
  · by_cases h : a = 0 <;>
      simp [Matrix.mul_apply, Matrix.single_apply, eq_comm, h]
  · by_cases h : a = 1 <;>
      simp [Matrix.mul_apply, Matrix.single_apply, eq_comm, h]

/-- Reindexing the polynomial block matrix gives the ordinary
standard-basis matrix of the Sylvester operator. -/
theorem ginibrePlaneSylvesterOperator_toMatrix_eq_reindex_block {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2) :
    LinearMap.toMatrix (Matrix.stdBasis ℝ (Fin m) (Fin 2))
        (Matrix.stdBasis ℝ (Fin m) (Fin 2))
        (ginibrePlaneSylvesterOperator D C) =
      Matrix.reindex (Equiv.prodComm (Fin 2) (Fin m))
        (Equiv.prodComm (Fin 2) (Fin m))
        (ginibrePlaneSylvesterBlockMatrix D C) := by
  ext ia jb
  rw [ginibrePlaneSylvesterOperator_toMatrix_apply]
  simp [ginibrePlaneSylvesterBlockMatrix, Matrix.reindex_apply,
    Matrix.comp_apply, ginibrePlanePolynomialEvalMatrix_block_apply]

/-- Exact algebraic Sylvester determinant identity, with no spectral
assumption:

`det(X ↦ XC-DX) = det(charpoly(C) evaluated at D)`.
-/
theorem ginibrePlaneSylvesterOperator_det_eq_charpoly_aeval {m : ℕ}
    (D : RSqMat m) (C : RSqMat 2) :
    (@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
      inferInstance (ginibrePlaneSylvesterBridgeModule m))
        (ginibrePlaneSylvesterOperator D C) =
      ((Polynomial.aeval D) C.charpoly).det := by
  rw [← @LinearMap.det_toMatrix
    (Matrix (Fin m) (Fin 2) ℝ) inferInstance
    (Fin m × Fin 2) inferInstance inferInstance ℝ inferInstance
    (ginibrePlaneSylvesterBridgeModule m)
    (Matrix.stdBasis ℝ (Fin m) (Fin 2))
    (ginibrePlaneSylvesterOperator D C)]
  calc
    ((LinearMap.toMatrix (Matrix.stdBasis ℝ (Fin m) (Fin 2))
        (Matrix.stdBasis ℝ (Fin m) (Fin 2)))
        (ginibrePlaneSylvesterOperator D C)).det =
        (Matrix.reindex (Equiv.prodComm (Fin 2) (Fin m))
          (Equiv.prodComm (Fin 2) (Fin m))
          (ginibrePlaneSylvesterBlockMatrix D C)).det := by
      exact congrArg Matrix.det
        (ginibrePlaneSylvesterOperator_toMatrix_eq_reindex_block D C)
    _ = (ginibrePlaneSylvesterBlockMatrix D C).det :=
      Matrix.det_reindex_self (Equiv.prodComm (Fin 2) (Fin m)) _
    _ = (ginibrePlanePolynomialEvalMatrix D
          (ginibrePlaneSylvesterPolynomialBlock C).det).det := by
      exact (Matrix.det_det (ginibrePlaneSylvesterPolynomialBlock C)
        (ginibrePlanePolynomialEvalMatrix D)).symm
    _ = ((Polynomial.aeval D) C.charpoly).det := by
      rw [ginibrePlaneSylvesterPolynomialBlock_det]
      rfl

/-- The chart's actual Sylvester block satisfies the same no-premise
characteristic-polynomial evaluation identity. -/
theorem ginibrePlaneSylvesterLinearMap_det_eq_charpoly_aeval {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    (@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
      inferInstance (ginibrePlaneSylvesterBridgeModule m))
        (ginibrePlaneSylvesterLinearMap q) =
      ((Polynomial.aeval (ginibrePlaneChartDeflatedBlock q))
        (ginibrePlaneChartAction q).charpoly).det := by
  simpa [ginibrePlaneSylvesterOperator, ginibrePlaneSylvesterLinearMap] using
    ginibrePlaneSylvesterOperator_det_eq_charpoly_aeval
      (ginibrePlaneChartDeflatedBlock q) (ginibrePlaneChartAction q)

/-- Pointwise conjugate characteristic-product form of the real Sylvester
determinant. -/
theorem ginibrePlaneSylvesterOperator_det_complex_eq_characteristicProduct
    {m : ℕ} (D : RSqMat m) (C : RSqMat 2)
    (hdisc : ginibrePlaneActionDiscriminant C < 0) :
    Complex.ofReal
        ((@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
          inferInstance (ginibrePlaneSylvesterBridgeModule m))
          (ginibrePlaneSylvesterOperator D C)) =
      (Matrix.scalar (Fin m) (ginibrePlaneActionUpperRoot C) -
          D.map Complex.ofReal).det *
        (Matrix.scalar (Fin m)
            (starRingEnd ℂ (ginibrePlaneActionUpperRoot C)) -
          D.map Complex.ofReal).det := by
  rw [ginibrePlaneSylvesterOperator_det_eq_charpoly_aeval]
  calc
    Complex.ofReal (((Polynomial.aeval D) C.charpoly).det) =
        (((Polynomial.aeval D) C.charpoly).map Complex.ofReal).det := by
      exact RingHom.map_det Complex.ofRealHom
        ((Polynomial.aeval D) C.charpoly)
    _ = ((Matrix.scalar (Fin m) (ginibrePlaneActionUpperRoot C) -
            D.map Complex.ofReal) *
          (Matrix.scalar (Fin m)
              (starRingEnd ℂ (ginibrePlaneActionUpperRoot C)) -
            D.map Complex.ofReal)).det := by
      rw [ginibrePlane_charpoly_aeval_map_complex_eq_product D C hdisc]
    _ = _ := Matrix.det_mul _ _

/-- The chart Sylvester block itself has the conjugate
characteristic-product form. -/
theorem ginibrePlaneSylvesterLinearMap_det_complex_eq_characteristicProduct
    {m : ℕ} (q : GinibrePlaneChartCoordinates m)
    (hdisc : ginibrePlaneActionDiscriminant
      (ginibrePlaneChartAction q) < 0) :
    Complex.ofReal
        ((@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
          inferInstance (ginibrePlaneSylvesterBridgeModule m))
          (ginibrePlaneSylvesterLinearMap q)) =
      (Matrix.scalar (Fin m)
          (ginibrePlaneActionUpperRoot (ginibrePlaneChartAction q)) -
        (ginibrePlaneChartDeflatedBlock q).map Complex.ofReal).det *
      (Matrix.scalar (Fin m)
          (starRingEnd ℂ
            (ginibrePlaneActionUpperRoot (ginibrePlaneChartAction q))) -
        (ginibrePlaneChartDeflatedBlock q).map Complex.ofReal).det := by
  simpa [ginibrePlaneSylvesterOperator, ginibrePlaneSylvesterLinearMap] using
    ginibrePlaneSylvesterOperator_det_complex_eq_characteristicProduct
      (ginibrePlaneChartDeflatedBlock q) (ginibrePlaneChartAction q) hdisc

/-- Exact expectation of the invariant-plane Sylvester determinant for an
independent standard real-Ginibre deflated block.  It depends on `C` only
through `det C`:

`𝔼_D det(X ↦ XC-DX) = m! ∑_{k=0}^m det(C)^k/k!`.
-/
theorem integral_realGinibre_ginibrePlaneSylvesterOperator_det
    {m : ℕ} (C : RSqMat 2)
    (hdisc : ginibrePlaneActionDiscriminant C < 0) :
    (∫ D : RSqMat m,
        (@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
          inferInstance (ginibrePlaneSylvesterBridgeModule m))
          (ginibrePlaneSylvesterOperator D C)
      ∂realGinibreMeasure m) =
      (m.factorial : ℝ) *
        ∑ k ∈ Finset.range (m + 1),
          C.det ^ k / (k.factorial : ℝ) := by
  apply Complex.ofReal_injective
  calc
    Complex.ofReal
        (∫ D : RSqMat m,
          (@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
            inferInstance (ginibrePlaneSylvesterBridgeModule m))
            (ginibrePlaneSylvesterOperator D C)
          ∂realGinibreMeasure m) =
        ∫ D : RSqMat m,
          Complex.ofReal
            ((@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
              inferInstance (ginibrePlaneSylvesterBridgeModule m))
              (ginibrePlaneSylvesterOperator D C))
          ∂realGinibreMeasure m := by
      exact (integral_complex_ofReal
        (μ := realGinibreMeasure m)
        (f := fun D : RSqMat m =>
          (@LinearMap.det (Matrix (Fin m) (Fin 2) ℝ) inferInstance ℝ
            inferInstance (ginibrePlaneSylvesterBridgeModule m))
            (ginibrePlaneSylvesterOperator D C))).symm
    _ = ∫ D : RSqMat m,
          (Matrix.scalar (Fin m) (ginibrePlaneActionUpperRoot C) -
              D.map Complex.ofReal).det *
            (Matrix.scalar (Fin m)
                (starRingEnd ℂ (ginibrePlaneActionUpperRoot C)) -
              D.map Complex.ofReal).det
          ∂realGinibreMeasure m := by
      apply integral_congr_ae
      filter_upwards with D
      exact
        ginibrePlaneSylvesterOperator_det_complex_eq_characteristicProduct
          D C hdisc
    _ = (m.factorial : ℂ) *
          ∑ k ∈ Finset.range (m + 1),
            (ginibrePlaneActionUpperRoot C *
              starRingEnd ℂ (ginibrePlaneActionUpperRoot C)) ^ k /
                (k.factorial : ℂ) :=
      integral_realGinibre_characteristicProduct_conj m
        (ginibrePlaneActionUpperRoot C)
    _ = Complex.ofReal
          ((m.factorial : ℝ) *
            ∑ k ∈ Finset.range (m + 1),
              C.det ^ k / (k.factorial : ℝ)) := by
      rw [ginibrePlaneActionUpperRoot_mul_conj C hdisc]
      norm_num

end NumStability

end
