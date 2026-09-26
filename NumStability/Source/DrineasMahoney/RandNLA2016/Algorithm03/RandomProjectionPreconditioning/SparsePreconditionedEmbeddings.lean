import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.UniformRowEmbedding
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.FloatingPoint
import NumStability.Source.Higham.Chapter23.ThreeM

/-!
Relocated from the historical wave owners NumStability.Algorithms.RandNLA.UniformRowSamplingFP under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

open scoped BigOperators

namespace NumStability
-- ============================================================
-- High-probability floating-point transfer for Algorithm 3
-- ============================================================

















































































































































-- ============================================================
-- Exact right-factor congruence for Algorithm 3 input matrices
-- ============================================================












































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/- ============================================================
-- CountSketch computed preprocessing plus uniform-row FP transfer
-- ============================================================ -/














































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Nonconditional sparse CountSketch FP endpoint with rounded sparse
CountSketch application, computed uniform row-scale denominator, rounded row
divisions, and rounded Gram dot products.

The only exact probability losses are the CountSketch hash-collision bound
`m^2 / r` and the downstream uniform-row sampling tail budget.  All
non-probability computations displayed in the event are charged by the explicit
radius `countSketchSparseUniformRowComputedDenPerturbBudget`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (countSketchSparseComputedPreconditionedBasis fp U)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat)) := by
  have hExact :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowSampleGramTwoSidedEvent U ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U hr hU hs htheta hδSample hsampleBudget
  have hCompEq :
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp U
          (countSketchSparseComputedPreconditionedBasis fp U)
          dhat
          (countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat)) = 1 := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp U dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp U
            (countSketchSparseComputedPreconditionedBasis fp U)
            dhat
            (countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (U := U)
      (Vhat := countSketchSparseComputedPreconditionedBasis fp U)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample)
      (δComp := 0)
      (τ := countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat)
      hExact hComp
  simpa [add_zero] using hTransfer

/-- Concrete-denominator specialization of the collision-free sparse
CountSketch FP endpoint for an exact orthonormal analysis basis.

The uniform row-scale denominator is computed by the modeled scalar routine
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`, so the final theorem has no
generic denominator parameter. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (countSketchSparseComputedPreconditionedBasis fp U)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp U
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
      fp U (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget




















































































































































/-- Nonconditional CountSketch FP endpoint for an actual Algorithm 3 input
matrix factored as `A = U C`.  The algorithm computes the sparse rounded
CountSketch apply to `A`, uses a computed uniform row-scale denominator, rounds
sampled-row divisions, and rounds Gram dot products.  The exact factors `U,C`
are analysis witnesses; they are not computed quantities in this theorem. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasis fp A)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)) := by
  intro A
  have hExact :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
            U C ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U C hr hU hs htheta hδSample hsampleBudget
  have hCompEq :
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp A
          (countSketchSparseComputedPreconditionedBasis fp A)
          dhat
          (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)) = 1 := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp A
            (countSketchSparseComputedPreconditionedBasis fp A)
            dhat
            (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (U := U) (C := C)
      (Vhat := countSketchSparseComputedPreconditionedBasis fp A)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample)
      (δComp := 0)
      (τ := countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)
      hExact hComp
  simpa [A, add_zero] using hTransfer

/-- Target-failure-budget form of the collision-free actual-input CountSketch
endpoint.

This packages the same fully computed event as
`..._ge_one_sub_square_inv_add_delta` with a single user-facing failure
probability `δ`.  The only probability losses are the exact collision-free
hash bound and the exact downstream row-sampling tail budget; all
non-probability computations are charged by the concrete displayed radius. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasis fp A)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)) := by
  intro A
  have hbase :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
            fp U C
            (countSketchSparseComputedPreconditionedBasis fp A)
            dhat
            ε
            (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)) := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        fp U C dhat hr hU hs hγm hγs htheta hδSample hsampleBudget
  have hleft :
      1 - δ ≤ 1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator specialization of the collision-free actual-input
CountSketch FP endpoint.

The algorithm computes with \(A=UC\), not with the analysis factors.  The
uniform row-scale denominator is fixed to the locally proved routine
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasis fp A)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp A
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
      fp U C (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget

/-- Direct target-failure-budget form of the concrete-denominator actual-input
CountSketch endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasis fp A)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp A
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Stored-sign collision-free CountSketch FP endpoint for an actual Algorithm 3
input matrix factored as `A = U C`, using a computed uniform row-scale
denominator.

The algorithm computes with the actual input `A`, stores the realized signs via
`storedSignOf`, applies sparse CountSketch arithmetic to `A`, rounds sampled-row
divisions, and rounds Gram dot products.  The exact factors `U,C` are analysis
witnesses; they are not computed quantities in this theorem. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A storedSignOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A storedSignOf dhat)) := by
  intro A
  have hExact :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
            U C ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U C hr hU hs htheta hδSample hsampleBudget
  have hCompEq :
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp A
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A storedSignOf)
          dhat
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A storedSignOf dhat)) = 1 := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp A
            (countSketchSparseComputedPreconditionedBasisWithStoredSign
              fp A storedSignOf)
            dhat
            (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
              fp A storedSignOf dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (U := U) (C := C)
      (Vhat := countSketchSparseComputedPreconditionedBasisWithStoredSign
        fp A storedSignOf)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample)
      (δComp := 0)
      (τ := countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
        fp A storedSignOf dhat)
      hExact hComp
  simpa [A, add_zero] using hTransfer

/-- Target-failure-budget form of the stored-sign collision-free actual-input
CountSketch endpoint with a computed denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A storedSignOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A storedSignOf dhat)) := by
  intro A
  have hbase :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
            fp U C
            (countSketchSparseComputedPreconditionedBasisWithStoredSign
              fp A storedSignOf)
            dhat
            ε
            (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
              fp A storedSignOf dhat)) := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        fp U C storedSignOf dhat hr hU hs hγm hγs htheta hδSample hsampleBudget
  have hleft :
      1 - δ ≤ 1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator specialization of the stored-sign collision-free
actual-input CountSketch FP endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A storedSignOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A storedSignOf (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
      fp U C storedSignOf (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget

/-- Target-failure-budget form of the concrete-denominator stored-sign
collision-free actual-input CountSketch endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A storedSignOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A storedSignOf (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C storedSignOf (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_mul sign 1` stored-sign collision-free CountSketch endpoint for
an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω)))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_add sign 0` stored-sign collision-free CountSketch endpoint for
an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω)))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_sub sign 0` stored-sign collision-free CountSketch endpoint for
an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω)))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Permuted-bucket stored-sign collision-free CountSketch FP endpoint for an
actual Algorithm 3 input matrix factored as `A = U C`, using a computed
uniform row-scale denominator.

The algorithm computes with the actual input `A`, stores the realized signs via
`storedSignOf`, applies sparse CountSketch arithmetic to `A` in the supplied
per-bucket traversal order, rounds sampled-row divisions, and rounds Gram dot
products.  The exact factors `U,C` are analysis witnesses; they are not
computed quantities in this theorem. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A storedSignOf orderOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A storedSignOf orderOf dhat)) := by
  intro A
  have hExact :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
            U C ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U C hr hU hs htheta hδSample hsampleBudget
  have hCompEq :
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp A
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A storedSignOf orderOf)
          dhat
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A storedSignOf orderOf dhat)) = 1 := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf orderOf dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp A
            (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
              fp A storedSignOf orderOf)
            dhat
            (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
              fp A storedSignOf orderOf dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (U := U) (C := C)
      (Vhat := countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
        fp A storedSignOf orderOf)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample)
      (δComp := 0)
      (τ := countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
        fp A storedSignOf orderOf dhat)
      hExact hComp
  simpa [A, add_zero] using hTransfer

/-- Target-failure-budget form of the permuted-bucket stored-sign
collision-free actual-input CountSketch endpoint with a computed denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A storedSignOf orderOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A storedSignOf orderOf dhat)) := by
  intro A
  have hbase :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
            fp U C
            (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
              fp A storedSignOf orderOf)
            dhat
            ε
            (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
              fp A storedSignOf orderOf dhat)) := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        fp U C storedSignOf orderOf dhat hr hU hs hγm hγs htheta
        hδSample hsampleBudget
  have hleft :
      1 - δ ≤ 1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator specialization of the permuted-bucket stored-sign
collision-free actual-input CountSketch FP endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A storedSignOf orderOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A storedSignOf orderOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
      fp U C storedSignOf orderOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget

/-- Target-failure-budget form of the concrete-denominator permuted-bucket
stored-sign collision-free actual-input CountSketch endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A storedSignOf orderOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A storedSignOf orderOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C storedSignOf orderOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_mul sign 1` permuted-bucket stored-sign collision-free
CountSketch endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf hr hU hs hγm hγs htheta hδSample hsampleBudget
      htotalBudget

/-- Final `fl_add sign 0` permuted-bucket stored-sign collision-free
CountSketch endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf hr hU hs hγm hγs htheta hδSample hsampleBudget
      htotalBudget

/-- Final `fl_sub sign 0` permuted-bucket stored-sign collision-free
CountSketch endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf hr hU hs hγm hγs htheta hδSample hsampleBudget
      htotalBudget

/-- Tree-reduced stored-sign collision-free CountSketch FP endpoint for an
actual Algorithm 3 input matrix factored as `A = U C`, using a computed
uniform row-scale denominator.

The algorithm computes with the actual input `A`, stores the realized signs via
`storedSignOf`, applies sparse CountSketch arithmetic to `A` with the supplied
per-bucket summation tree, rounds sampled-row divisions, and rounds Gram dot
products.  The exact factors `U,C` are analysis witnesses; they are not
computed quantities in this theorem. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A storedSignOf treeOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A storedSignOf treeOf dhat)) := by
  intro A
  have hExact :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
            U C ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U C hr hU hs htheta hδSample hsampleBudget
  have hCompEq :
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp A
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A storedSignOf treeOf)
          dhat
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A storedSignOf treeOf dhat)) = 1 := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf treeOf dhat hr hs hdepth hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp A
            (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
              fp A storedSignOf treeOf)
            dhat
            (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
              fp A storedSignOf treeOf dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (U := U) (C := C)
      (Vhat := countSketchSparseComputedPreconditionedBasisWithStoredSignTree
        fp A storedSignOf treeOf)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample)
      (δComp := 0)
      (τ := countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
        fp A storedSignOf treeOf dhat)
      hExact hComp
  simpa [A, add_zero] using hTransfer

/-- Target-failure-budget form of the tree-reduced stored-sign collision-free
actual-input CountSketch endpoint with a computed denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A storedSignOf treeOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A storedSignOf treeOf dhat)) := by
  intro A
  have hbase :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
            fp U C
            (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
              fp A storedSignOf treeOf)
            dhat
            ε
            (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
              fp A storedSignOf treeOf dhat)) := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        fp U C storedSignOf treeOf dhat hr hU hs hdepth hγs htheta
        hδSample hsampleBudget
  have hleft :
      1 - δ ≤ 1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator specialization of the tree-reduced stored-sign
collision-free actual-input CountSketch FP endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A storedSignOf treeOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A storedSignOf treeOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
      fp U C storedSignOf treeOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hdepth hγs htheta hδSample hsampleBudget

/-- Target-failure-budget form of the concrete-denominator tree-reduced
stored-sign collision-free actual-input CountSketch endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A storedSignOf treeOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A storedSignOf treeOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C storedSignOf treeOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hdepth hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_mul sign 1` tree-reduced stored-sign collision-free CountSketch
endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf hr hU hs hdepth hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_add sign 0` tree-reduced stored-sign collision-free CountSketch
endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf hr hU hs hdepth hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_sub sign 0` tree-reduced stored-sign collision-free CountSketch
endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf hr hU hs hdepth hγs htheta hδSample hsampleBudget htotalBudget






































/-- Implementation-facing Frobenius/Markov endpoint for non-injective
CountSketch followed by computed-denominator iid uniform-row sampling.

The exact hash/sign and row-sampling laws remain mathematical probability
objects.  The computed quantities are the sparse CountSketch apply, the
uniform-row denominator, the sampled-row divisions, and the sampled-Gram dot
products; all are charged in the realized radius
`countSketchSparseUniformRowComputedDenPerturbBudget`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ηCS ηRow : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let δCS : ℝ :=
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ηCS ^ 2
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
          fp A dhat ηCS ηRow) := by
  intro δCS δRow
  classical
  let Ptot :=
    countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let Eexact :=
    countSketchUniformRowSampleGramRowGramFrobEvent
      (r := r) (m := m) (s := s) A ηCS ηRow
  let Epert :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A
      (countSketchSparseComputedPreconditionedBasis fp A)
      dhat
      (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)
  have hExact : 1 - (δCS + δRow) ≤ Ptot.eventProb Eexact := by
    simpa [Ptot, Eexact, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_rowGram_frob_error_le_ge_one_sub
        (r := r) (m := m) (s := s) hr A hηCS hηRow hs
  have hPertEq : Ptot.eventProb Epert = 1 := by
    simpa [Ptot, Epert] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A dhat hr hs hγm hγs
  have hPert : 1 - (0 : ℝ) ≤ Ptot.eventProb Epert := by
    rw [hPertEq]
    norm_num
  have hInter :
      1 - ((δCS + δRow) + 0) ≤ Ptot.eventProb (Eexact ∩ Epert) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Ptot Eexact Epert (δCS + δRow) 0 hExact hPert
  have hsubset :
      Eexact ∩ Epert ⊆
        countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
          fp A dhat ηCS ηRow := by
    intro x hx
    rcases hx with ⟨hexact, hpert⟩
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let V : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasis fp A x.1
    let τ : ℝ := countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat x
    let DeltaPert : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k
    let DeltaRow : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - rowGram V j k
    let DeltaCS : Fin n → Fin n → ℝ :=
      fun j k => rowGram V j k - rowGram A j k
    have hCS : frobNorm DeltaCS ≤ ηCS := by
      simpa [Eexact, countSketchUniformRowSampleGramRowGramFrobEvent,
        DeltaCS, V, sign] using hexact.1
    have hRow : frobNorm DeltaRow ≤ ηRow := by
      simpa [Eexact, countSketchUniformRowSampleGramRowGramFrobEvent,
        DeltaRow, V, sign] using hexact.2
    have hPertBound : frobNorm DeltaPert ≤ τ := by
      simpa [Epert,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        DeltaPert, V, Vhat, τ, sign] using hpert
    have hsplit :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n =>
          DeltaPert j k + (DeltaRow j k + DeltaCS j k)) := by
      funext j k
      dsimp [DeltaPert, DeltaRow, DeltaCS]
      ring
    have htri₁ := frobNorm_add_le DeltaPert (fun j k => DeltaRow j k + DeltaCS j k)
    have htri₂ := frobNorm_add_le DeltaRow DeltaCS
    have hbound :
        frobNorm
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k) ≤
          ηCS + ηRow + τ := by
      calc
        frobNorm
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k)
            =
          frobNorm
            (fun j k : Fin n =>
              DeltaPert j k + (DeltaRow j k + DeltaCS j k)) := by
              rw [hsplit]
        _ ≤ frobNorm DeltaPert + frobNorm (fun j k => DeltaRow j k + DeltaCS j k) :=
              htri₁
        _ ≤ τ + (ηRow + ηCS) := by
              linarith
        _ = ηCS + ηRow + τ := by ring
    simpa [countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent,
      Vhat, τ] using hbound
  have hmono := FiniteProbability.eventProb_mono Ptot hsubset
  have hfinal := hInter.trans hmono
  simpa [add_assoc] using hfinal

end NumStability
