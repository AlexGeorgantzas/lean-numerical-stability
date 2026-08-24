import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.SketchedGramLoewnerCovers
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.FloatingPoint
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.SparsePreconditionedEmbeddings
import NumStability.Source.Higham.Chapter23.ThreeM
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.RandNLA.UniformRowSamplingFP under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

open scoped BigOperators

namespace NumStability
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

end NumStability
