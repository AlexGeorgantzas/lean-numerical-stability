import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.RandNLA.UniformRowSamplingComposition
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.FloatingPoint
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.FloatingPoint

/-!
# NumStability.Algorithms.RandNLA.UniformRowSamplingFP compatibility facade

Historical declaration-bearing W11 facade. The genuine-private reverse closure remains here with its original identity; all movable commands are re-exported from canonical modules.
-/

-- Algorithms/RandNLA/UniformRowSamplingFP.lean
--
-- Floating-point transfer for Algorithm 3 uniform row sampling after
-- signed-Hadamard preprocessing.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602







namespace NumStability

open scoped BigOperators

/-!
## Floating-point uniform row sketches

The exact Algorithm 3 uniform row sketch samples row `i` and rescales it by
`1 / sqrt(s / m)`, so its Gram matrix is the uniform sample-average matrix
already analyzed in `UniformRowSamplingMGF`.  This file adds the corresponding
rounded row-scaling and rounded Gram-dot-product layer, reusing the repository's
division, row-sketch Gram, and dot-product perturbation lemmas.
-/

-- ============================================================
-- Uniform row-scaling kernels
-- ============================================================




























namespace ComputedUniformRowScaleDen

variable {fp : FPModel} {m s : ℕ}













































































































































































































































































































































































































































































































































































































































































































































































































































































































end ComputedUniformRowScaleDen

/- ============================================================
   Concrete denominator routine used by the final SRHT endpoints
   ============================================================ -/
















































































































































































































































































































































































































































































-- ============================================================
-- Fully floating-point uniform sample Gram
-- ============================================================



























































































































































































































































































































































































































































































































































































-- ============================================================
-- High-probability Frobenius FP transfer for arbitrary uniform-row inputs
-- ============================================================



























































































































































/-- High-probability Frobenius/Markov theorem for the fully floating-point
uniform-row sampled Gram of an arbitrary exact matrix, using the exact
mathematical row-scale denominator in the division operation. -/
theorem uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_rowGram_frob_error_le_ge_one_sub
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) (hη : 0 < η) :
    1 - (((m : ℝ) / (s : ℝ)) *
        ∑ i : Fin m, rowNormSq U i ^ 2) / η ^ 2 ≤
      (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
        (uniformRowFlSampleGramDotRowGramFrobErrorEvent fp U η) := by
  have hExact :=
    uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub
      U hm hs η hη
  have hsubset :=
    uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDot
      fp U hm hs hγ η
  have hExactEvent :
      1 - (((m : ℝ) / (s : ℝ)) *
          ∑ i : Fin m, rowNormSq U i ^ 2) / η ^ 2 ≤
        (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
          (uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η) := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent] using hExact
  exact
    hExactEvent.trans
      (FiniteProbability.eventProb_mono
        (uniformRowTraceProbability (m := m) (steps := s) hm) hsubset)

/-- Readable Frobenius-norm simplification of
`uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_rowGram_frob_error_le_ge_one_sub`.
-/
theorem uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_rowGram_frob_error_le_ge_one_sub_frobNorm
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) (hη : 0 < η) :
    1 - (((m : ℝ) / (s : ℝ)) * frobNormSqRect U ^ 2) / η ^ 2 ≤
      (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
        (uniformRowFlSampleGramDotRowGramFrobErrorEvent fp U η) := by
  have hExact :=
    uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
      U hm hs η hη
  have hsubset :=
    uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDot
      fp U hm hs hγ η
  have hExactEvent :
      1 - (((m : ℝ) / (s : ℝ)) * frobNormSqRect U ^ 2) / η ^ 2 ≤
        (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
          (uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η) := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent] using hExact
  exact
    hExactEvent.trans
      (FiniteProbability.eventProb_mono
        (uniformRowTraceProbability (m := m) (steps := s) hm) hsubset)

/-- High-probability Frobenius/Markov theorem for the fully floating-point
uniform-row sampled Gram of an arbitrary exact matrix, with a computed
non-probability row-scale denominator. -/
theorem uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) (hη : 0 < η) :
    1 - (((m : ℝ) / (s : ℝ)) *
        ∑ i : Fin m, rowNormSq U i ^ 2) / η ^ 2 ≤
      (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
        (uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent
          fp U dhat η) := by
  have hExact :=
    uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub
      U hm hs η hη
  have hsubset :=
    uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDotWithComputedDen
      fp U dhat hm hs hγ η
  have hExactEvent :
      1 - (((m : ℝ) / (s : ℝ)) *
          ∑ i : Fin m, rowNormSq U i ^ 2) / η ^ 2 ≤
        (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
          (uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η) := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent] using hExact
  exact
    hExactEvent.trans
      (FiniteProbability.eventProb_mono
        (uniformRowTraceProbability (m := m) (steps := s) hm) hsubset)

/-- Readable Frobenius-norm simplification of the computed-denominator
uniform-row sampled-Gram Frobenius/Markov theorem. -/
theorem uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub_frobNorm
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) (hη : 0 < η) :
    1 - (((m : ℝ) / (s : ℝ)) * frobNormSqRect U ^ 2) / η ^ 2 ≤
      (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
        (uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent
          fp U dhat η) := by
  have hExact :=
    uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
      U hm hs η hη
  have hsubset :=
    uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDotWithComputedDen
      fp U dhat hm hs hγ η
  have hExactEvent :
      1 - (((m : ℝ) / (s : ℝ)) * frobNormSqRect U ^ 2) / η ^ 2 ≤
        (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
          (uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η) := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent] using hExact
  exact
    hExactEvent.trans
      (FiniteProbability.eventProb_mono
        (uniformRowTraceProbability (m := m) (steps := s) hm) hsubset)

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




















































































































































/-- Exact CountSketch preprocessing plus uniform row sampling for an actual
input matrix `A = U C`.  The hash/sign and row-sampling laws remain exact; `U`
and `C` are exact analysis witnesses, not computed algorithm outputs. -/
theorem countSketchUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    {r m q n s : ℕ} (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta)
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
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent U C ε) := by
  have hExactU :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowSampleGramTwoSidedEvent U ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U hr hU hs htheta hδSample hsampleBudget
  exact hExactU.trans
    (FiniteProbability.eventProb_mono
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr)
      (countSketchUniformRowSampleGramTwoSidedEvent_subset_factoredInput
        (r := r) (m := m) (q := q) (n := n) (s := s) U C ε hU hr hs))





































































































































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






































/-- Exact-product-law Frobenius/Markov composition for non-injective
CountSketch followed by exact iid uniform-row sampling.

The CountSketch probability term is the exact non-injective Frobenius/Markov
coefficient term.  The downstream uniform-row term is made deterministic using
`frobNormSqRect_preconditionRows_countSketchRows_le`, so there is no conditional
row-sampling certificate. -/
theorem countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_rowGram_frob_error_le_ge_one_sub
    {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) {ηCS ηRow : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) :
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
        (countSketchUniformRowSampleGramRowGramFrobEvent A ηCS ηRow) := by
  intro δCS δRow
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramFrobErrorEvent (r := r) (m := m) A ηCS
  let V : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) A
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      uniformRowSampleGramRowGramFrobErrorEvent (s := s) (V x) ηRow
  have hPre : 1 - δCS ≤ P.eventProb Epre := by
    simpa [P, Epre, δCS] using
      countSketchProbability_eventProb_rowGram_frob_error_le_ge_one_sub
        (r := r) (m := m) hr A hηCS
  have hδRow_nonneg : 0 ≤ δRow := by
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    exact div_nonneg
      (mul_nonneg hrs_nonneg (sq_nonneg ((m : ℝ) * frobNormSqRect A)))
      (sq_nonneg ηRow)
  have hSample :
      ∀ x ∈ Epre, 1 - δRow ≤ Q.eventProb (Fsample x) := by
    intro x _hx
    have hbase :
        1 -
            (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          Q.eventProb (Fsample x) := by
      simpa [Q, Fsample] using
        uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
          (m := r) (s := s) (U := V x) hr hs ηRow hηRow
    have hsign_abs : ∀ k : Fin m, |rademacherSignVector x.2 k| ≤ 1 := by
      intro k
      simp [rademacherSignVector_abs x.2 k]
    have hV :
        frobNormSqRect (V x) ≤ (m : ℝ) * frobNormSqRect A := by
      simpa [V] using
        frobNormSqRect_preconditionRows_countSketchRows_le
          x.1 (rademacherSignVector x.2) A hsign_abs
    have hM_nonneg : 0 ≤ (m : ℝ) * frobNormSqRect A := by
      exact mul_nonneg (Nat.cast_nonneg m) (frobNormSqRect_nonneg A)
    have hV_abs :
        |frobNormSqRect (V x)| ≤ |(m : ℝ) * frobNormSqRect A| := by
      simpa [abs_of_nonneg (frobNormSqRect_nonneg (V x)),
        abs_of_nonneg hM_nonneg] using hV
    have hV_sq :
        frobNormSqRect (V x) ^ 2 ≤
          ((m : ℝ) * frobNormSqRect A) ^ 2 :=
      sq_le_sq.mpr hV_abs
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    have hbudget :
        (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          δRow := by
      have hmul :
          ((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2 ≤
            ((r : ℝ) / (s : ℝ)) *
              ((m : ℝ) * frobNormSqRect A) ^ 2 :=
        mul_le_mul_of_nonneg_left hV_sq hrs_nonneg
      simpa [δRow] using
        div_le_div_of_nonneg_right hmul (sq_nonneg ηRow)
    have hleft :
        1 - δRow ≤
          1 - (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 := by
      linarith
    exact hleft.trans hbase
  have hprod :
      1 - (δCS + δRow) ≤
        (P.prod Q).eventProb
          {x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s |
            x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δCS δRow hδRow_nonneg hPre hSample
  have hsubset :
      {x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s |
        x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} ⊆
        countSketchUniformRowSampleGramRowGramFrobEvent A ηCS ηRow := by
    intro x hx
    rcases hx with ⟨hcs, hrow⟩
    constructor
    · simpa [Epre, countSketchRowGramFrobErrorEvent, V] using hcs
    · simpa [Fsample, uniformRowSampleGramRowGramFrobErrorEvent, V] using hrow
  exact hprod.trans (by
    simpa [countSketchUniformRowTraceProbability, P, Q] using
      FiniteProbability.eventProb_mono (P.prod Q) hsubset)

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

/-- Readable Frobenius-norm simplification of the non-injective CountSketch
plus computed-denominator uniform-row FP endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub_frobNorm
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ηCS ηRow : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let δCS : ℝ :=
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ηCS ^ 2
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
          fp A dhat ηCS ηRow) := by
  intro δCS δRow
  classical
  let coeff : ℝ :=
    ∑ j : Fin n, ∑ k : Fin n,
      ∑ p : CountSketchDistinctPair m,
        (A p.1.1 j * A p.1.2 k) ^ 2
  let δCoeff : ℝ := (2 * (r : ℝ)⁻¹ * coeff) / ηCS ^ 2
  have hbase :
      1 - (δCoeff + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
            fp A dhat ηCS ηRow) := by
    simpa [δCoeff, δRow, coeff] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub
        fp (r := r) (m := m) (s := s) hr A dhat hηCS hηRow hs hγm hγs
  have hcoeff : coeff ≤ frobNormSqRect A ^ 2 := by
    simpa [coeff] using
      countSketchDistinctPair_gramCoeffSq_sum_le_frobNormSqRect_sq A
  have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
  have hδCS :
      δCoeff ≤ δCS := by
    have hmul :
        2 * (r : ℝ)⁻¹ * coeff ≤
          2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
    simpa [δCoeff, δCS] using
      div_le_div_of_nonneg_right hmul (sq_nonneg ηCS)
  have hleft : 1 - (δCS + δRow) ≤ 1 - (δCoeff + δRow) := by
    linarith
  exact hleft.trans hbase





























































































































































































/-- Non-injective CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint.

The probability loss is the same exact coefficient loss as S9z; the conclusion
is the two-sided finite-Loewner event obtained from the computed Frobenius
event.  This remains Markov/Frobenius-derived rather than optimal CountSketch
subspace-embedding concentration. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub
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
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat ηCS ηRow) := by
  intro δCS δRow
  classical
  let P := countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  have hbase :
      1 - (δCS + δRow) ≤
        P.eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
            fp A dhat ηCS ηRow) := by
    simpa [P, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub
        fp (r := r) (m := m) (s := s) hr A dhat hηCS hηRow hs hγm hγs
  have hsubset :=
    countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent_subset_twoSidedLoewnerEvent
      fp (r := r) (m := m) (s := s) A dhat ηCS ηRow
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Exact-coefficient sample-budget form of the non-injective CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint.

This wrapper keeps the sharp S9z CountSketch coefficient loss instead of
replacing it by `||A||_F^4`; the downstream uniform-row loss remains the
proved Frobenius growth bound for `S_{h,ω} A`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ηCS ηRow δ : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ηCS ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat ηCS ηRow) := by
  classical
  let δCS : ℝ :=
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / ηCS ^ 2
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A dhat ηCS ηRow) := by
    simpa [δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub
        fp (r := r) (m := m) (s := s) hr A dhat hηCS hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Readable Frobenius-norm simplification of the non-injective CountSketch
plus downstream uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_frobNorm
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ηCS ηRow : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let δCS : ℝ :=
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ηCS ^ 2
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat ηCS ηRow) := by
  intro δCS δRow
  classical
  let P := countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  have hbase :
      1 - (δCS + δRow) ≤
        P.eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
            fp A dhat ηCS ηRow) := by
    simpa [P, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub_frobNorm
        fp (r := r) (m := m) (s := s) hr A dhat hηCS hηRow hs hγm hγs
  have hsubset :=
    countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent_subset_twoSidedLoewnerEvent
      fp (r := r) (m := m) (s := s) A dhat ηCS ηRow
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Sample-budget form of the non-injective CountSketch plus downstream
uniform-row floating-point finite-Loewner endpoint.

The hypothesis is the readable S9za failure loss bounded by the target
failure probability `δ`.  The exact probability laws are unchanged, while the
event still charges the concrete sparse CountSketch apply, computed uniform
denominator, sampled-row divisions, and sampled-Gram dot products. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ηCS ηRow δ : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ηCS ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat ηCS ηRow) := by
  classical
  let δCS : ℝ :=
    (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ηCS ^ 2
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A dhat ηCS ηRow) := by
    simpa [δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_frobNorm
        fp (r := r) (m := m) (s := s) hr A dhat hηCS hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Equal-radius sample-budget form of the S9za endpoint.

Taking `ηCS = ηRow = ε / 2` makes the exact part of the finite-Loewner radius
equal to `ε`, so every realization in the event satisfies
`-((ε + T_fp) I) <= Ghat - A^T A <= (ε + T_fp) I`, where `T_fp` is the
irreducible concrete floating-point perturbation budget already built into the
event definition. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let η : ℝ := ε / 2
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / η ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat (ε / 2) (ε / 2)) := by
  have hη : 0 < ε / 2 := by
    linarith
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget
      fp (r := r) (m := m) (s := s) hr A dhat hη hη hs hγm hγs (by
        simpa using hbudget)

/-- Expanded equal-radius readable sample-budget form of the S9za endpoint.

This theorem is algebraically the same as the preceding equal-radius wrapper,
but substitutes `η = ε / 2` in the hypothesis. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget_expanded
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (8 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ε ^ 2 +
        (4 * (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2)) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat (ε / 2) (ε / 2)) := by
  have hη : 0 < ε / 2 := by
    linarith
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget
      fp (r := r) (m := m) (s := s) hr A dhat hη hη hs hγm hγs (by
        convert hbudget using 1
        field_simp [ne_of_gt hε]
        ring)

/-- Equal-radius exact-coefficient sample-budget form of the S9za endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let η : ℝ := ε / 2
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / η ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat (ε / 2) (ε / 2)) := by
  have hη : 0 < ε / 2 := by
    linarith
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget
      fp (r := r) (m := m) (s := s) hr A dhat hη hη hs hγm hγs (by
        simpa using hbudget)

/-- Expanded equal-radius exact-coefficient sample-budget form of the S9za
endpoint.  The hypothesis substitutes `η = ε / 2` explicitly, so the
CountSketch term carries the factor `8 / ε^2` and the downstream row-sampling
term carries the factor `4 / ε^2`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget_expanded
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (8 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ε ^ 2 +
        (4 * (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2)) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat (ε / 2) (ε / 2)) := by
  have hη : 0 < ε / 2 := by
    linarith
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget
      fp (r := r) (m := m) (s := s) hr A dhat hη hη hs hγm hγs (by
        convert hbudget using 1
        field_simp [ne_of_gt hε]
        ring)

/-- Concrete-denominator exact-coefficient sample-budget form of the
non-injective CountSketch plus downstream uniform-row finite-Loewner endpoint.
-/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ηCS ηRow δ : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ηCS ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) ηCS ηRow) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hηCS hηRow hs hγm hγs hbudget

/-- Concrete-denominator equal-radius exact-coefficient sample-budget form of
the non-injective CountSketch plus downstream uniform-row finite-Loewner
endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let η : ℝ := ε / 2
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / η ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          (ε / 2) (ε / 2)) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hε hs hγm hγs hbudget

/-- Concrete-denominator expanded equal-radius exact-coefficient sample-budget
form of the non-injective CountSketch plus downstream uniform-row
finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget_expanded
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (8 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ε ^ 2 +
        (4 * (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2)) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          (ε / 2) (ε / 2)) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget_expanded
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hε hs hγm hγs hbudget

/-- Concrete-denominator sample-budget form of the non-injective CountSketch
plus downstream uniform-row finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ηCS ηRow δ : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ηCS ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) ηCS ηRow) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hηCS hηRow hs hγm hγs hbudget

/-- Concrete-denominator equal-radius sample-budget form of the non-injective
CountSketch plus downstream uniform-row finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let η : ℝ := ε / 2
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / η ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          (ε / 2) (ε / 2)) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hε hs hγm hγs hbudget

/-- Concrete-denominator expanded equal-radius readable sample-budget form of
the non-injective CountSketch plus downstream uniform-row finite-Loewner
endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget_expanded
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (8 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ε ^ 2 +
        (4 * (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2)) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          (ε / 2) (ε / 2)) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget_expanded
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hε hs hγm hγs hbudget

/-- Finite-cover CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint.

The CountSketch preprocessing event is the exact finite-cover two-sided Loewner
event with radius `η + L * (2 * ρ + ρ^2)`.  The downstream uniform-row
sampling contributes the exact Frobenius radius `ηRow`, and the sparse apply,
computed denominator, row divisions, and sampled-Gram dot products are charged
through the concrete realized perturbation budget in the event. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Ptot :=
    countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L
  let V : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) A
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      uniformRowSampleGramRowGramFrobErrorEvent (s := s) (V x) ηRow
  let Eprod : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    {x | x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1}
  let Epert : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A
      (countSketchSparseComputedPreconditionedBasis fp A)
      dhat
      (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)
  have hPre : 1 - δCS ≤ P.eventProb Epre := by
    simpa [P, Epre, δCS] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
        (r := r) (m := m) (n := n) (ι := ι)
        hr A net hcover hη hL hρ
  have hδRow_nonneg : 0 ≤ δRow := by
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    exact div_nonneg
      (mul_nonneg hrs_nonneg (sq_nonneg ((m : ℝ) * frobNormSqRect A)))
      (sq_nonneg ηRow)
  have hSample :
      ∀ x ∈ Epre, 1 - δRow ≤ Q.eventProb (Fsample x) := by
    intro x _hx
    have hbase :
        1 -
            (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          Q.eventProb (Fsample x) := by
      simpa [Q, Fsample] using
        uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
          (m := r) (s := s) (U := V x) hr hs ηRow hηRow
    have hsign_abs : ∀ k : Fin m, |rademacherSignVector x.2 k| ≤ 1 := by
      intro k
      simp [rademacherSignVector_abs x.2 k]
    have hV :
        frobNormSqRect (V x) ≤ (m : ℝ) * frobNormSqRect A := by
      simpa [V] using
        frobNormSqRect_preconditionRows_countSketchRows_le
          x.1 (rademacherSignVector x.2) A hsign_abs
    have hM_nonneg : 0 ≤ (m : ℝ) * frobNormSqRect A := by
      exact mul_nonneg (Nat.cast_nonneg m) (frobNormSqRect_nonneg A)
    have hV_abs :
        |frobNormSqRect (V x)| ≤ |(m : ℝ) * frobNormSqRect A| := by
      simpa [abs_of_nonneg (frobNormSqRect_nonneg (V x)),
        abs_of_nonneg hM_nonneg] using hV
    have hV_sq :
        frobNormSqRect (V x) ^ 2 ≤
          ((m : ℝ) * frobNormSqRect A) ^ 2 :=
      sq_le_sq.mpr hV_abs
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    have hbudgetRow :
        (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          δRow := by
      have hmul :
          ((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2 ≤
            ((r : ℝ) / (s : ℝ)) *
              ((m : ℝ) * frobNormSqRect A) ^ 2 :=
        mul_le_mul_of_nonneg_left hV_sq hrs_nonneg
      simpa [δRow] using
        div_le_div_of_nonneg_right hmul (sq_nonneg ηRow)
    have hleft :
        1 - δRow ≤
          1 - (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 := by
      linarith
    exact hleft.trans hbase
  have hprod :
      1 - (δCS + δRow) ≤ (P.prod Q).eventProb Eprod :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δCS δRow hδRow_nonneg hPre hSample
  have hprod' : 1 - (δCS + δRow) ≤ Ptot.eventProb Eprod := by
    simpa [Ptot, P, Q, Eprod, countSketchUniformRowTraceProbability] using hprod
  have hPertEq : Ptot.eventProb Epert = 1 := by
    simpa [Ptot, Epert] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A dhat hr hs hγm hγs
  have hPert : 1 - (0 : ℝ) ≤ Ptot.eventProb Epert := by
    rw [hPertEq]
    norm_num
  have hinter :
      1 - ((δCS + δRow) + 0) ≤ Ptot.eventProb (Eprod ∩ Epert) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Ptot Eprod Epert (δCS + δRow) 0 hprod' hPert
  have hsubset :
      Eprod ∩ Epert ⊆
        countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat τCS ηRow := by
    intro x hx
    rcases hx with ⟨hprodMem, hpert⟩
    rcases hprodMem with ⟨hcs, hrow⟩
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let Vexact : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasis fp A x.1
    let τfp : ℝ := countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat x
    let DeltaCS : Fin n → Fin n → ℝ :=
      fun j k => rowGram Vexact j k - rowGram A j k
    let DeltaRow : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Vexact x.2 j k - rowGram Vexact j k
    let DeltaPert : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          uniformRowSampleGram Vexact x.2 j k
    have hCS :
        finiteLoewnerLe DeltaCS
            (fun j k : Fin n => τCS * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin n => -DeltaCS j k)
            (fun j k : Fin n => τCS * finiteIdMatrix j k) := by
      simpa [Epre, countSketchRowGramTwoSidedLoewnerCoverEvent,
        DeltaCS, Vexact, sign, τCS] using hcs
    have hRow : frobNorm DeltaRow ≤ ηRow := by
      simpa [Fsample, uniformRowSampleGramRowGramFrobErrorEvent,
        DeltaRow, V, Vexact, sign] using hrow
    have hPertBound : frobNorm DeltaPert ≤ τfp := by
      simpa [Epert,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        DeltaPert, V, Vexact, Vhat, τfp, sign] using hpert
    have hrowAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        DeltaCS DeltaRow hCS.1 hCS.2 hRow
    have hallAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        (fun j k : Fin n => DeltaCS j k + DeltaRow j k)
        DeltaPert hrowAdd.1 hrowAdd.2 hPertBound
    have hsplit :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n =>
          (DeltaCS j k + DeltaRow j k) + DeltaPert j k) := by
      funext j k
      dsimp [DeltaCS, DeltaRow, DeltaPert]
      ring
    have hsplitNeg :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n =>
          -((DeltaCS j k + DeltaRow j k) + DeltaPert j k)) := by
      funext j k
      exact congrArg (fun z : ℝ => -z) (congrFun (congrFun hsplit j) k)
    have hUpper :
        finiteLoewnerLe
          (fun j k =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplit]
      simpa [add_assoc] using hallAdd.1
    have hLower :
        finiteLoewnerLe
          (fun j k =>
            -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplitNeg]
      simpa [add_assoc] using hallAdd.2
    exact ⟨hUpper, hLower⟩
  have hmono := FiniteProbability.eventProb_mono Ptot hsubset
  have hfinal := hinter.trans hmono
  simpa [add_assoc] using hfinal

/-- Target-failure-budget wrapper for the finite-cover CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow δ : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : ι,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (net a) p.1.1 *
                rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat τCS ηRow) := by
  intro τCS
  classical
  let δCS : ℝ :=
    ((∑ a : ι,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (net a) p.1.1 *
            rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A dhat τCS ηRow) := by
    simpa [τCS, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
        fp (r := r) (m := m) (n := n) (s := s) (ι := ι)
        hr A dhat net hcover hη hL hρ hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow, add_assoc] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator target-failure-budget wrapper for the finite-cover
CountSketch plus downstream uniform-row floating-point finite-Loewner endpoint.

The denominator routine is the locally proved computation
`fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow δ : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : ι,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (net a) p.1.1 *
                rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (ι := ι)
      hr A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      net hcover hη hL hρ hηRow hs hγm hγs hbudget

/-- Product-grid specialization of the finite-cover CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint.

The one-dimensional grid is an exact analysis object.  The computed event still
charges sparse CountSketch apply, computed denominator, row divisions, and
sampled-Gram dot products through the existing realized perturbation budget. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  have hcover :
      finiteUnitBallCover
        (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ :=
    finiteUnitBallCover_product_grid grid hgrid hδgrid hρgrid
  have hρ_nonneg : 0 ≤ ρ := by
    exact le_trans
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hδgrid) hρgrid
  simpa [τCS, δCS, δRow] using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
      fp (r := r) (m := m) (n := n) (s := s) (ι := Fin n → α)
      hr A dhat
      (fun a : Fin n → α => fun j : Fin n => grid (a j))
      hcover hη hL hρ_nonneg hηRow hs hγm hγs

/-- Target-failure-budget wrapper for the product-grid CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat τCS ηRow) := by
  intro τCS
  classical
  let δCS : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A dhat τCS ηRow) := by
    simpa [τCS, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
        fp (r := r) (m := m) (n := n) (s := s) (α := α)
        hr A dhat grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow, add_assoc] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator target-failure-budget wrapper for the product-grid
CountSketch plus downstream uniform-row floating-point finite-Loewner endpoint.

The denominator routine is the locally proved computation
`fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Finite-cover CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint when the realized Rademacher signs are stored or copied
before sparse bucket accumulation.

The exact probability terms are unchanged from the exact-sign theorem.  The
computed event radius uses the stored-sign sparse-apply/downstream uniform-row
budget, so sign storage/copying is charged rather than assumed exact. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Ptot :=
    countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L
  let V : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) A
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      uniformRowSampleGramRowGramFrobErrorEvent (s := s) (V x) ηRow
  let Eprod : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    {x | x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1}
  let Epert : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A
      (countSketchSparseComputedPreconditionedBasisWithStoredSign
        fp A storedSignOf)
      dhat
      (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
        fp A storedSignOf dhat)
  have hPre : 1 - δCS ≤ P.eventProb Epre := by
    simpa [P, Epre, δCS] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
        (r := r) (m := m) (n := n) (ι := ι)
        hr A net hcover hη hL hρ
  have hδRow_nonneg : 0 ≤ δRow := by
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    exact div_nonneg
      (mul_nonneg hrs_nonneg (sq_nonneg ((m : ℝ) * frobNormSqRect A)))
      (sq_nonneg ηRow)
  have hSample :
      ∀ x ∈ Epre, 1 - δRow ≤ Q.eventProb (Fsample x) := by
    intro x _hx
    have hbase :
        1 -
            (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          Q.eventProb (Fsample x) := by
      simpa [Q, Fsample] using
        uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
          (m := r) (s := s) (U := V x) hr hs ηRow hηRow
    have hsign_abs : ∀ k : Fin m, |rademacherSignVector x.2 k| ≤ 1 := by
      intro k
      simp [rademacherSignVector_abs x.2 k]
    have hV :
        frobNormSqRect (V x) ≤ (m : ℝ) * frobNormSqRect A := by
      simpa [V] using
        frobNormSqRect_preconditionRows_countSketchRows_le
          x.1 (rademacherSignVector x.2) A hsign_abs
    have hM_nonneg : 0 ≤ (m : ℝ) * frobNormSqRect A := by
      exact mul_nonneg (Nat.cast_nonneg m) (frobNormSqRect_nonneg A)
    have hV_abs :
        |frobNormSqRect (V x)| ≤ |(m : ℝ) * frobNormSqRect A| := by
      simpa [abs_of_nonneg (frobNormSqRect_nonneg (V x)),
        abs_of_nonneg hM_nonneg] using hV
    have hV_sq :
        frobNormSqRect (V x) ^ 2 ≤
          ((m : ℝ) * frobNormSqRect A) ^ 2 :=
      sq_le_sq.mpr hV_abs
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    have hbudgetRow :
        (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          δRow := by
      have hmul :
          ((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2 ≤
            ((r : ℝ) / (s : ℝ)) *
              ((m : ℝ) * frobNormSqRect A) ^ 2 :=
        mul_le_mul_of_nonneg_left hV_sq hrs_nonneg
      simpa [δRow] using
        div_le_div_of_nonneg_right hmul (sq_nonneg ηRow)
    have hleft :
        1 - δRow ≤
          1 - (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 := by
      linarith
    exact hleft.trans hbase
  have hprod :
      1 - (δCS + δRow) ≤ (P.prod Q).eventProb Eprod :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δCS δRow hδRow_nonneg hPre hSample
  have hprod' : 1 - (δCS + δRow) ≤ Ptot.eventProb Eprod := by
    simpa [Ptot, P, Q, Eprod, countSketchUniformRowTraceProbability] using hprod
  have hPertEq : Ptot.eventProb Epert = 1 := by
    simpa [Ptot, Epert] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf dhat hr hs hγm hγs
  have hPert : 1 - (0 : ℝ) ≤ Ptot.eventProb Epert := by
    rw [hPertEq]
    norm_num
  have hinter :
      1 - ((δCS + δRow) + 0) ≤ Ptot.eventProb (Eprod ∩ Epert) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Ptot Eprod Epert (δCS + δRow) 0 hprod' hPert
  have hsubset :
      Eprod ∩ Epert ⊆
        countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf dhat τCS ηRow := by
    intro x hx
    rcases hx with ⟨hprodMem, hpert⟩
    rcases hprodMem with ⟨hcs, hrow⟩
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let Vexact : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSign
        fp A storedSignOf x.1
    let τfp : ℝ :=
      countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
        fp A storedSignOf dhat x
    let DeltaCS : Fin n → Fin n → ℝ :=
      fun j k => rowGram Vexact j k - rowGram A j k
    let DeltaRow : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Vexact x.2 j k - rowGram Vexact j k
    let DeltaPert : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          uniformRowSampleGram Vexact x.2 j k
    have hCS :
        finiteLoewnerLe DeltaCS
            (fun j k : Fin n => τCS * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin n => -DeltaCS j k)
            (fun j k : Fin n => τCS * finiteIdMatrix j k) := by
      simpa [Epre, countSketchRowGramTwoSidedLoewnerCoverEvent,
        DeltaCS, Vexact, sign, τCS] using hcs
    have hRow : frobNorm DeltaRow ≤ ηRow := by
      simpa [Fsample, uniformRowSampleGramRowGramFrobErrorEvent,
        DeltaRow, V, Vexact, sign] using hrow
    have hPertBound : frobNorm DeltaPert ≤ τfp := by
      simpa [Epert,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        DeltaPert, V, Vexact, Vhat, τfp, sign] using hpert
    have hrowAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        DeltaCS DeltaRow hCS.1 hCS.2 hRow
    have hallAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        (fun j k : Fin n => DeltaCS j k + DeltaRow j k)
        DeltaPert hrowAdd.1 hrowAdd.2 hPertBound
    have hsplit :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n =>
          (DeltaCS j k + DeltaRow j k) + DeltaPert j k) := by
      funext j k
      dsimp [DeltaCS, DeltaRow, DeltaPert]
      ring
    have hsplitNeg :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n =>
          -((DeltaCS j k + DeltaRow j k) + DeltaPert j k)) := by
      funext j k
      exact congrArg (fun z : ℝ => -z) (congrFun (congrFun hsplit j) k)
    have hUpper :
        finiteLoewnerLe
          (fun j k =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplit]
      simpa [add_assoc] using hallAdd.1
    have hLower :
        finiteLoewnerLe
          (fun j k =>
            -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplitNeg]
      simpa [add_assoc] using hallAdd.2
    exact ⟨hUpper, hLower⟩
  have hmono := FiniteProbability.eventProb_mono Ptot hsubset
  have hfinal := hinter.trans hmono
  simpa [add_assoc] using hfinal

/-- Product-grid specialization of the finite-cover CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint with stored
realized signs.

The product grid is an exact analysis object.  The computed event charges the
stored sign table, sparse bucket arithmetic, computed denominator, sampled-row
divisions, and sampled-Gram dot products through the realized stored-sign
budget. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  have hcover :
      finiteUnitBallCover
        (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ :=
    finiteUnitBallCover_product_grid grid hgrid hδgrid hρgrid
  have hρ_nonneg : 0 ≤ ρ := by
    exact le_trans
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hδgrid) hρgrid
  simpa [τCS, δCS, δRow] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
      fp (r := r) (m := m) (n := n) (s := s) (ι := Fin n → α)
      hr A storedSignOf dhat
      (fun a : Fin n → α => fun j : Fin n => grid (a j))
      hcover hη hL hρ_nonneg hηRow hs hγm hγs

/-- Target-failure-budget wrapper for the stored-sign product-grid CountSketch
plus downstream uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf dhat τCS ηRow) := by
  intro τCS
  classical
  let δCS : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A storedSignOf dhat τCS ηRow) := by
    simpa [τCS, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
        fp (r := r) (m := m) (n := n) (s := s) (α := α)
        hr A storedSignOf dhat grid hgrid hδgrid hρgrid hη hL
        hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow, add_assoc] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint, using `fl_sqrt ((s : R) * (r : R)^{-1})` with an
exactly supplied scalar input ratio. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtExactInputDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf
          (uniformRowFlSqrtExactInputScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf (uniformRowFlSqrtExactInputScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint, using `fl_sqrt (fl_div (s : R) (r : R))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlDivThenSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf
          (uniformRowFlDivThenSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf (uniformRowFlDivThenSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint, using
`fl_sqrt (fl_mul (s : R) (fl_div 1 (r : R)))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlInvMulThenSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf
          (uniformRowFlInvMulThenSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf (uniformRowFlInvMulThenSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint, using
`fl_div (fl_sqrt (s : R)) (fl_sqrt (r : R))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtDivSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf
          (uniformRowFlSqrtDivSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf (uniformRowFlSqrtDivSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for signs copied by
`fl_mul sign_i 1` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for signs copied by
`fl_add sign_i 0` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for signs copied by
`fl_sub sign_i 0` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget





















































































































































/-- Orthonormal-input readable-budget wrapper for stored-sign product-grid
CountSketch plus downstream uniform-row floating-point finite-Loewner endpoint.

This theorem replaces the exact CountSketch coefficient loss by the sufficient
orthonormal loss involving only the product-grid vector norms and `n`, while
retaining the downstream uniform-row loss with `||U||_F^2 = n`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf dhat τCS ηRow) := by
  intro τCS
  classical
  let δCoeff : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
  let δCoeffReadable : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
  let δRowExact : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
  let δRowReadable : ℝ :=
    (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
  have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
  have hvecTerm :
      ∀ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2 ≤
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
            η ^ 2 := by
    intro a
    have hpair :
        (∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) ≤
          vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 := by
      calc
        (∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2)
            ≤
          vecNorm2Sq (rectMatMulVec U (fun j : Fin n => grid (a j))) ^ 2 :=
            countSketchDistinctPair_vecCoeffSq_sum_le_vecNorm2Sq_sq
              (rectMatMulVec U (fun j : Fin n => grid (a j)))
        _ = vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 := by
            rw [hasOrthonormalColumns_vecNorm2Sq_rectMatMulVec_eq U hU]
    have hmul :
        2 * (r : ℝ)⁻¹ *
            (∑ p : CountSketchDistinctPair m,
              (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) ≤
          2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 :=
      mul_le_mul_of_nonneg_left hpair hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg η)
  have hvecSum :
      (∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) ≤
        ∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2 :=
    Finset.sum_le_sum (fun a _ => hvecTerm a)
  have hgram :
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2 ≤
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2 := by
    have hcoeff :
        (∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2) ≤
          (n : ℝ) ^ 2 := by
      calc
        (∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2)
            ≤ frobNormSqRect U ^ 2 :=
              countSketchDistinctPair_gramCoeffSq_sum_le_frobNormSqRect_sq U
        _ = (n : ℝ) ^ 2 := by
              rw [frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU]
    have hmul :
        2 * (r : ℝ)⁻¹ *
            (∑ j : Fin n, ∑ k : Fin n,
              ∑ p : CountSketchDistinctPair m,
                (U p.1.1 j * U p.1.2 k) ^ 2) ≤
          2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg L)
  have hcoeffReadable : δCoeff ≤ δCoeffReadable := by
    dsimp [δCoeff, δCoeffReadable]
    linarith
  have hrowEq : δRowExact = δRowReadable := by
    dsimp [δRowExact, δRowReadable]
    rw [frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU]
  have hbudgetExact :
      (let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) := by
    dsimp
    have hreadable : δCoeffReadable + δRowReadable ≤ δ := by
      simpa [δCoeffReadable, δRowReadable] using hbudget
    have hmono : δCoeff + δRowExact ≤ δCoeffReadable + δRowReadable := by
      rw [hrowEq]
      linarith
    exact hmono.trans hreadable
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U storedSignOf dhat grid hgrid hδgrid hρgrid hη hL hηRow
      hs hγm hγs hbudgetExact

/-- Concrete-denominator form of the orthonormal-input readable-budget wrapper
for stored-sign product-grid CountSketch plus downstream uniform-row
floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU storedSignOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for signs copied by
`fl_mul sign_i 1` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for signs copied by
`fl_add sign_i 0` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for signs copied by
`fl_sub sign_i 0` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Finite-cover CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint when realized Rademacher signs are stored or copied
and each realized bucket is traversed in an exact fixed order.

The exact probability terms are unchanged from the exact-sign theorem.  The
computed event radius uses the stored-sign permuted-bucket
sparse-apply/downstream uniform-row budget, so every modeled non-probability
operation on this implementation path is charged. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf orderOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Ptot :=
    countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L
  let V : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) A
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      uniformRowSampleGramRowGramFrobErrorEvent (s := s) (V x) ηRow
  let Eprod : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    {x | x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1}
  let Epert : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A
      (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
        fp A storedSignOf orderOf)
      dhat
      (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
        fp A storedSignOf orderOf dhat)
  have hPre : 1 - δCS ≤ P.eventProb Epre := by
    simpa [P, Epre, δCS] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
        (r := r) (m := m) (n := n) (ι := ι)
        hr A net hcover hη hL hρ
  have hδRow_nonneg : 0 ≤ δRow := by
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    exact div_nonneg
      (mul_nonneg hrs_nonneg (sq_nonneg ((m : ℝ) * frobNormSqRect A)))
      (sq_nonneg ηRow)
  have hSample :
      ∀ x ∈ Epre, 1 - δRow ≤ Q.eventProb (Fsample x) := by
    intro x _hx
    have hbase :
        1 -
            (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          Q.eventProb (Fsample x) := by
      simpa [Q, Fsample] using
        uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
          (m := r) (s := s) (U := V x) hr hs ηRow hηRow
    have hsign_abs : ∀ k : Fin m, |rademacherSignVector x.2 k| ≤ 1 := by
      intro k
      simp [rademacherSignVector_abs x.2 k]
    have hV :
        frobNormSqRect (V x) ≤ (m : ℝ) * frobNormSqRect A := by
      simpa [V] using
        frobNormSqRect_preconditionRows_countSketchRows_le
          x.1 (rademacherSignVector x.2) A hsign_abs
    have hM_nonneg : 0 ≤ (m : ℝ) * frobNormSqRect A := by
      exact mul_nonneg (Nat.cast_nonneg m) (frobNormSqRect_nonneg A)
    have hV_abs :
        |frobNormSqRect (V x)| ≤ |(m : ℝ) * frobNormSqRect A| := by
      simpa [abs_of_nonneg (frobNormSqRect_nonneg (V x)),
        abs_of_nonneg hM_nonneg] using hV
    have hV_sq :
        frobNormSqRect (V x) ^ 2 ≤
          ((m : ℝ) * frobNormSqRect A) ^ 2 :=
      sq_le_sq.mpr hV_abs
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    have hbudgetRow :
        (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          δRow := by
      have hmul :
          ((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2 ≤
            ((r : ℝ) / (s : ℝ)) *
              ((m : ℝ) * frobNormSqRect A) ^ 2 :=
        mul_le_mul_of_nonneg_left hV_sq hrs_nonneg
      simpa [δRow] using
        div_le_div_of_nonneg_right hmul (sq_nonneg ηRow)
    have hleft :
        1 - δRow ≤
          1 - (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 := by
      linarith
    exact hleft.trans hbase
  have hprod :
      1 - (δCS + δRow) ≤ (P.prod Q).eventProb Eprod :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δCS δRow hδRow_nonneg hPre hSample
  have hprod' : 1 - (δCS + δRow) ≤ Ptot.eventProb Eprod := by
    simpa [Ptot, P, Q, Eprod, countSketchUniformRowTraceProbability] using hprod
  have hPertEq : Ptot.eventProb Epert = 1 := by
    simpa [Ptot, Epert] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf orderOf dhat hr hs hγm hγs
  have hPert : 1 - (0 : ℝ) ≤ Ptot.eventProb Epert := by
    rw [hPertEq]
    norm_num
  have hinter :
      1 - ((δCS + δRow) + 0) ≤ Ptot.eventProb (Eprod ∩ Epert) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Ptot Eprod Epert (δCS + δRow) 0 hprod' hPert
  have hsubset :
      Eprod ∩ Epert ⊆
        countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf orderOf dhat τCS ηRow := by
    intro x hx
    rcases hx with ⟨hprodMem, hpert⟩
    rcases hprodMem with ⟨hcs, hrow⟩
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let Vexact : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
        fp A storedSignOf orderOf x.1
    let τfp : ℝ :=
      countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
        fp A storedSignOf orderOf dhat x
    let DeltaCS : Fin n → Fin n → ℝ :=
      fun j k => rowGram Vexact j k - rowGram A j k
    let DeltaRow : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Vexact x.2 j k - rowGram Vexact j k
    let DeltaPert : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          uniformRowSampleGram Vexact x.2 j k
    have hCS :
        finiteLoewnerLe DeltaCS
            (fun j k : Fin n => τCS * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin n => -DeltaCS j k)
            (fun j k : Fin n => τCS * finiteIdMatrix j k) := by
      simpa [Epre, countSketchRowGramTwoSidedLoewnerCoverEvent,
        DeltaCS, Vexact, sign, τCS] using hcs
    have hRow : frobNorm DeltaRow ≤ ηRow := by
      simpa [Fsample, uniformRowSampleGramRowGramFrobErrorEvent,
        DeltaRow, V, Vexact, sign] using hrow
    have hPertBound : frobNorm DeltaPert ≤ τfp := by
      simpa [Epert,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        DeltaPert, V, Vexact, Vhat, τfp, sign] using hpert
    have hrowAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        DeltaCS DeltaRow hCS.1 hCS.2 hRow
    have hallAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        (fun j k : Fin n => DeltaCS j k + DeltaRow j k)
        DeltaPert hrowAdd.1 hrowAdd.2 hPertBound
    have hsplit :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n =>
          (DeltaCS j k + DeltaRow j k) + DeltaPert j k) := by
      funext j k
      dsimp [DeltaCS, DeltaRow, DeltaPert]
      ring
    have hsplitNeg :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n =>
          -((DeltaCS j k + DeltaRow j k) + DeltaPert j k)) := by
      funext j k
      exact congrArg (fun z : ℝ => -z) (congrFun (congrFun hsplit j) k)
    have hUpper :
        finiteLoewnerLe
          (fun j k =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplit]
      simpa [add_assoc] using hallAdd.1
    have hLower :
        finiteLoewnerLe
          (fun j k =>
            -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplitNeg]
      simpa [add_assoc] using hallAdd.2
    exact ⟨hUpper, hLower⟩
  have hmono := FiniteProbability.eventProb_mono Ptot hsubset
  have hfinal := hinter.trans hmono
  simpa [add_assoc] using hfinal

/-- Product-grid specialization of the finite-cover CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint with stored
realized signs and exact per-bucket traversal orders. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf orderOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  have hcover :
      finiteUnitBallCover
        (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ :=
    finiteUnitBallCover_product_grid grid hgrid hδgrid hρgrid
  have hρ_nonneg : 0 ≤ ρ := by
    exact le_trans
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hδgrid) hρgrid
  simpa [τCS, δCS, δRow] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
      fp (r := r) (m := m) (n := n) (s := s) (ι := Fin n → α)
      hr A storedSignOf orderOf dhat
      (fun a : Fin n → α => fun j : Fin n => grid (a j))
      hcover hη hL hρ_nonneg hηRow hs hγm hγs

/-- Target-failure-budget wrapper for the stored-sign permuted-bucket
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf orderOf dhat τCS ηRow) := by
  intro τCS
  classical
  let δCS : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A storedSignOf orderOf dhat τCS ηRow) := by
    simpa [τCS, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
        fp (r := r) (m := m) (n := n) (s := s) (α := α)
        hr A storedSignOf orderOf dhat grid hgrid hδgrid hρgrid hη hL
        hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow, add_assoc] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
permuted-bucket product-grid CountSketch plus downstream uniform-row
floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf orderOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for per-bucket permuted sparse
CountSketch, signs copied by `fl_mul sign_i 1`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for per-bucket permuted sparse
CountSketch, signs copied by `fl_add sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for per-bucket permuted sparse
CountSketch, signs copied by `fl_sub sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Orthonormal-input readable-budget wrapper for permuted-bucket stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf orderOf dhat τCS ηRow) := by
  intro τCS
  have hbudgetExact :
      (let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :=
    countSketchUniformRow_productGrid_orthonormal_coeff_add_frob_add_row_budget
      (r := r) (m := m) (n := n) (s := s) (α := α)
      U hU grid hbudget
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U storedSignOf orderOf dhat grid hgrid hδgrid hρgrid hη hL
      hηRow hs hγm hγs hbudgetExact

/-- Concrete-denominator form of the orthonormal-input readable-budget wrapper
for permuted-bucket stored-sign product-grid CountSketch plus downstream
uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU storedSignOf orderOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for per-bucket permuted
CountSketch, signs copied by `fl_mul sign_i 1`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for per-bucket permuted
CountSketch, signs copied by `fl_add sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for per-bucket permuted
CountSketch, signs copied by `fl_sub sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Finite-cover CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint when realized Rademacher signs are stored or copied
and each realized bucket is accumulated by an exact supplied summation tree.

The exact probability terms are unchanged from the exact-sign theorem.  The
computed event radius uses the stored-sign tree-reduced sparse-apply/downstream
uniform-row budget, so every modeled non-probability operation on this
implementation path is charged. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf treeOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Ptot :=
    countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L
  let V : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) A
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      uniformRowSampleGramRowGramFrobErrorEvent (s := s) (V x) ηRow
  let Eprod : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    {x | x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1}
  let Epert : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A
      (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
        fp A storedSignOf treeOf)
      dhat
      (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
        fp A storedSignOf treeOf dhat)
  have hPre : 1 - δCS ≤ P.eventProb Epre := by
    simpa [P, Epre, δCS] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
        (r := r) (m := m) (n := n) (ι := ι)
        hr A net hcover hη hL hρ
  have hδRow_nonneg : 0 ≤ δRow := by
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    exact div_nonneg
      (mul_nonneg hrs_nonneg (sq_nonneg ((m : ℝ) * frobNormSqRect A)))
      (sq_nonneg ηRow)
  have hSample :
      ∀ x ∈ Epre, 1 - δRow ≤ Q.eventProb (Fsample x) := by
    intro x _hx
    have hbase :
        1 -
            (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          Q.eventProb (Fsample x) := by
      simpa [Q, Fsample] using
        uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
          (m := r) (s := s) (U := V x) hr hs ηRow hηRow
    have hsign_abs : ∀ k : Fin m, |rademacherSignVector x.2 k| ≤ 1 := by
      intro k
      simp [rademacherSignVector_abs x.2 k]
    have hV :
        frobNormSqRect (V x) ≤ (m : ℝ) * frobNormSqRect A := by
      simpa [V] using
        frobNormSqRect_preconditionRows_countSketchRows_le
          x.1 (rademacherSignVector x.2) A hsign_abs
    have hM_nonneg : 0 ≤ (m : ℝ) * frobNormSqRect A := by
      exact mul_nonneg (Nat.cast_nonneg m) (frobNormSqRect_nonneg A)
    have hV_abs :
        |frobNormSqRect (V x)| ≤ |(m : ℝ) * frobNormSqRect A| := by
      simpa [abs_of_nonneg (frobNormSqRect_nonneg (V x)),
        abs_of_nonneg hM_nonneg] using hV
    have hV_sq :
        frobNormSqRect (V x) ^ 2 ≤
          ((m : ℝ) * frobNormSqRect A) ^ 2 :=
      sq_le_sq.mpr hV_abs
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    have hbudgetRow :
        (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          δRow := by
      have hmul :
          ((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2 ≤
            ((r : ℝ) / (s : ℝ)) *
              ((m : ℝ) * frobNormSqRect A) ^ 2 :=
        mul_le_mul_of_nonneg_left hV_sq hrs_nonneg
      simpa [δRow] using
        div_le_div_of_nonneg_right hmul (sq_nonneg ηRow)
    have hleft :
        1 - δRow ≤
          1 - (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 := by
      linarith
    exact hleft.trans hbase
  have hprod :
      1 - (δCS + δRow) ≤ (P.prod Q).eventProb Eprod :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δCS δRow hδRow_nonneg hPre hSample
  have hprod' : 1 - (δCS + δRow) ≤ Ptot.eventProb Eprod := by
    simpa [Ptot, P, Q, Eprod, countSketchUniformRowTraceProbability] using hprod
  have hPertEq : Ptot.eventProb Epert = 1 := by
    simpa [Ptot, Epert] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf treeOf dhat hr hs hdepth hγs
  have hPert : 1 - (0 : ℝ) ≤ Ptot.eventProb Epert := by
    rw [hPertEq]
    norm_num
  have hinter :
      1 - ((δCS + δRow) + 0) ≤ Ptot.eventProb (Eprod ∩ Epert) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Ptot Eprod Epert (δCS + δRow) 0 hprod' hPert
  have hsubset :
      Eprod ∩ Epert ⊆
        countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf treeOf dhat τCS ηRow := by
    intro x hx
    rcases hx with ⟨hprodMem, hpert⟩
    rcases hprodMem with ⟨hcs, hrow⟩
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let Vexact : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSignTree
        fp A storedSignOf treeOf x.1
    let τfp : ℝ :=
      countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
        fp A storedSignOf treeOf dhat x
    let DeltaCS : Fin n → Fin n → ℝ :=
      fun j k => rowGram Vexact j k - rowGram A j k
    let DeltaRow : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Vexact x.2 j k - rowGram Vexact j k
    let DeltaPert : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          uniformRowSampleGram Vexact x.2 j k
    have hCS :
        finiteLoewnerLe DeltaCS
            (fun j k : Fin n => τCS * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin n => -DeltaCS j k)
            (fun j k : Fin n => τCS * finiteIdMatrix j k) := by
      simpa [Epre, countSketchRowGramTwoSidedLoewnerCoverEvent,
        DeltaCS, Vexact, sign, τCS] using hcs
    have hRow : frobNorm DeltaRow ≤ ηRow := by
      simpa [Fsample, uniformRowSampleGramRowGramFrobErrorEvent,
        DeltaRow, V, Vexact, sign] using hrow
    have hPertBound : frobNorm DeltaPert ≤ τfp := by
      simpa [Epert,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        DeltaPert, V, Vexact, Vhat, τfp, sign] using hpert
    have hrowAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        DeltaCS DeltaRow hCS.1 hCS.2 hRow
    have hallAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        (fun j k : Fin n => DeltaCS j k + DeltaRow j k)
        DeltaPert hrowAdd.1 hrowAdd.2 hPertBound
    have hsplit :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n =>
          (DeltaCS j k + DeltaRow j k) + DeltaPert j k) := by
      funext j k
      dsimp [DeltaCS, DeltaRow, DeltaPert]
      ring
    have hsplitNeg :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n =>
          -((DeltaCS j k + DeltaRow j k) + DeltaPert j k)) := by
      funext j k
      exact congrArg (fun z : ℝ => -z) (congrFun (congrFun hsplit j) k)
    have hUpper :
        finiteLoewnerLe
          (fun j k =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplit]
      simpa [add_assoc] using hallAdd.1
    have hLower :
        finiteLoewnerLe
          (fun j k =>
            -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplitNeg]
      simpa [add_assoc] using hallAdd.2
    exact ⟨hUpper, hLower⟩
  have hmono := FiniteProbability.eventProb_mono Ptot hsubset
  have hfinal := hinter.trans hmono
  simpa [add_assoc] using hfinal

/-- Product-grid specialization of the finite-cover CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint with stored
realized signs and tree-reduced bucket accumulation. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf treeOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  have hcover :
      finiteUnitBallCover
        (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ :=
    finiteUnitBallCover_product_grid grid hgrid hδgrid hρgrid
  have hρ_nonneg : 0 ≤ ρ := by
    exact le_trans
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hδgrid) hρgrid
  simpa [τCS, δCS, δRow] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
      fp (r := r) (m := m) (n := n) (s := s) (ι := Fin n → α)
      hr A storedSignOf treeOf dhat
      (fun a : Fin n → α => fun j : Fin n => grid (a j))
      hcover hη hL hρ_nonneg hηRow hs hdepth hγs

/-- Target-failure-budget wrapper for the stored-sign tree-reduced product-grid
CountSketch plus downstream uniform-row floating-point finite-Loewner
endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf treeOf dhat τCS ηRow) := by
  intro τCS
  classical
  let δCS : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A storedSignOf treeOf dhat τCS ηRow) := by
    simpa [τCS, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
        fp (r := r) (m := m) (n := n) (s := s) (α := α)
        hr A storedSignOf treeOf dhat grid hgrid hδgrid hρgrid hη hL
        hηRow hs hdepth hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow, add_assoc] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
tree-reduced product-grid CountSketch plus downstream uniform-row
floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf treeOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete product-grid downstream endpoint for tree-reduced sparse
CountSketch, signs copied by `fl_mul sign_i 1`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete product-grid downstream endpoint for tree-reduced sparse
CountSketch, signs copied by `fl_add sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete product-grid downstream endpoint for tree-reduced sparse
CountSketch, signs copied by `fl_sub sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Orthonormal-input readable-budget wrapper for tree-reduced stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf treeOf dhat τCS ηRow) := by
  intro τCS
  have hbudgetExact :
      (let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :=
    countSketchUniformRow_productGrid_orthonormal_coeff_add_frob_add_row_budget
      (r := r) (m := m) (n := n) (s := s) (α := α)
      U hU grid hbudget
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U storedSignOf treeOf dhat grid hgrid hδgrid hρgrid hη hL
      hηRow hs hdepth hγs hbudgetExact

/-- Concrete-denominator form of the orthonormal-input readable-budget wrapper
for tree-reduced stored-sign product-grid CountSketch plus downstream
uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU storedSignOf treeOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete orthonormal downstream endpoint for tree-reduced CountSketch,
signs copied by `fl_mul sign_i 1`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete orthonormal downstream endpoint for tree-reduced CountSketch,
signs copied by `fl_add sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete orthonormal downstream endpoint for tree-reduced CountSketch,
signs copied by `fl_sub sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget


































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
