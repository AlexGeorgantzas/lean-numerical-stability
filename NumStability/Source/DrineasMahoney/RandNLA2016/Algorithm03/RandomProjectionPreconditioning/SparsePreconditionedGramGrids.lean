import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.FloatingPoint
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.SparsePreconditionedGramBounds
import NumStability.Source.Higham.Chapter23.ThreeM

/-!
Relocated from the historical wave owners NumStability.Algorithms.RandNLA.UniformRowSamplingFP under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

open scoped BigOperators

namespace NumStability
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
