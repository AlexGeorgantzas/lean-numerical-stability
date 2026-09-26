import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.SketchedGramMoments
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.Preconditioning
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.RandNLA.Preconditioning under the R09/R10 completion waves; reusable-tier destination per the reviewed route ledger.
-/

open scoped BigOperators

namespace NumStability
/-- Exact finite-cover CountSketch row-Gram Loewner probability theorem.

The probability loss is the sum of the finite-test quadratic-form loss and the
Frobenius/Markov loss that supplies the coarse cover radius `L`.  This is exact
probability/exact arithmetic only; no floating-point computation appears. -/
theorem countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
    {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (net : ι → Fin n → ℝ) {ρ η L : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ) :
    1 -
        ((∑ a : ι,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (net a) p.1.1 *
                rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ l : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 l) ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
          A ρ η L) := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Etest : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramFiniteTestEvent (r := r) (m := m) A net η
  let Efrob : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramFrobErrorEvent (r := r) (m := m) A L
  let Btest : ℝ :=
    ∑ a : ι,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (net a) p.1.1 *
            rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2
  let Bfrob : ℝ :=
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ l : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 l) ^ 2) / L ^ 2
  have htest : 1 - Btest ≤ P.eventProb Etest := by
    simpa [P, Etest, Btest, countSketchRowGramFiniteTestEvent] using
      countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_sum_coeff_budget
        (r := r) (m := m) (n := n) (ι := ι) hr A net (fun _a : ι => η)
        (fun _a => hη)
  have hfrob : 1 - Bfrob ≤ P.eventProb Efrob := by
    simpa [P, Efrob, Bfrob, countSketchRowGramFrobErrorEvent] using
      countSketchProbability_eventProb_rowGram_frob_error_le_ge_one_sub
        (r := r) (m := m) hr A hL
  have hinter :
      1 - (Btest + Bfrob) ≤ P.eventProb (Etest ∩ Efrob) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Etest Efrob
      Btest Bfrob htest hfrob
  have hsubset : Etest ∩ Efrob ⊆
      countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L :=
    countSketchRowGramFiniteTestFrobEvent_subset_twoSidedLoewnerCoverEvent
      A net hcover (le_of_lt hL) hρ
  simpa [P, Etest, Efrob, Btest, Bfrob] using
    hinter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Target-budget form of the exact finite-cover CountSketch row-Gram Loewner
theorem.  If the fully displayed finite-test-plus-Frobenius loss is at most
`δ`, the cover Loewner event holds with probability at least `1 - δ`. -/
theorem countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_budget
    {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (net : ι → Fin n → ℝ) {ρ η L δ : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hbudget :
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ l : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 l) ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
          A ρ η L) := by
  have hbase :=
    countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
      (r := r) (m := m) (n := n) (ι := ι) hr A net hcover hη hL hρ
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : ι,
            (2 * (r : ℝ)⁻¹ *
              ∑ p : CountSketchDistinctPair m,
                (rectMatMulVec A (net a) p.1.1 *
                  rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
          (2 * (r : ℝ)⁻¹ *
            ∑ j : Fin n, ∑ l : Fin n,
              ∑ p : CountSketchDistinctPair m,
                (A p.1.1 j * A p.1.2 l) ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase















































































/-- Full exact-product-law non-injective sparse CountSketch floating-point Gram
Frobenius endpoint.  The probability is the exact CountSketch hash/sign law;
the computed quantity is `fl_countSketchSparseGramDot`, which charges sparse
signed products, bucket accumulation, and rounded Gram dot products. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub
    (fp : FPModel) {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) {η : ℝ} (hη : 0 < η)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 -
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ l : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 l) ^ 2) / η ^ 2 ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramFrobErrorEvent fp A η) := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  have hbase :
      1 -
          (2 * (r : ℝ)⁻¹ *
            ∑ j : Fin n, ∑ l : Fin n,
              ∑ p : CountSketchDistinctPair m,
                (A p.1.1 j * A p.1.2 l) ^ 2) / η ^ 2 ≤
        P.eventProb (countSketchRowGramFrobErrorEvent (r := r) (m := m) A η) := by
    simpa [P, countSketchRowGramFrobErrorEvent] using
      countSketchProbability_eventProb_rowGram_frob_error_le_ge_one_sub
        (r := r) (m := m) hr A hη
  have hsubset :=
    countSketchRowGramFrobErrorEvent_subset_flSparseGramDotRowGramFrobErrorEvent
      fp A η hγm hγr
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)




































































/-- Readable exact finite-cover CountSketch row-Gram Loewner probability
theorem.  The finite-test coefficient sums are bounded by `||A z_a||₂⁴`, and
the Frobenius coefficient sum is bounded by `||A||_F⁴`. -/
theorem countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_vecNorm_add_frobNorm
    {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (net : ι → Fin n → ℝ) {ρ η L : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ) :
    1 -
        ((∑ a : ι,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (rectMatMulVec A (net a)) ^ 2) / η ^ 2) +
        (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
          A ρ η L) := by
  classical
  let coeffTest : ι → ℝ :=
    fun a =>
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (net a) p.1.1 *
            rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2
  let readableTest : ι → ℝ :=
    fun a =>
      (2 * (r : ℝ)⁻¹ *
        vecNorm2Sq (rectMatMulVec A (net a)) ^ 2) / η ^ 2
  let coeffFrob : ℝ :=
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ l : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 l) ^ 2) / L ^ 2
  let readableFrob : ℝ :=
    (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2
  have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
  have htest_term : ∀ a : ι, coeffTest a ≤ readableTest a := by
    intro a
    have hcoeff :
        (∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (net a) p.1.1 *
            rectMatMulVec A (net a) p.1.2) ^ 2) ≤
          vecNorm2Sq (rectMatMulVec A (net a)) ^ 2 := by
      exact
        countSketchDistinctPair_vecCoeffSq_sum_le_vecNorm2Sq_sq
          (rectMatMulVec A (net a))
    have hmul :
        2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2 ≤
        2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (net a)) ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg η)
  have htest :
      (∑ a : ι, coeffTest a) ≤ ∑ a : ι, readableTest a :=
    Finset.sum_le_sum (fun a _ => htest_term a)
  have hfrob : coeffFrob ≤ readableFrob := by
    have hcoeff :
        (∑ j : Fin n, ∑ l : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 l) ^ 2) ≤
          frobNormSqRect A ^ 2 :=
      countSketchDistinctPair_gramCoeffSq_sum_le_frobNormSqRect_sq A
    have hmul :
        2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ l : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 l) ^ 2 ≤
        2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg L)
  have hbudget :
      (∑ a : ι, coeffTest a) + coeffFrob ≤
        (∑ a : ι, readableTest a) + readableFrob :=
    add_le_add htest hfrob
  have hbase :=
    countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
      (r := r) (m := m) (n := n) (ι := ι) hr A net hcover hη hL hρ
  have hleft :
      1 - ((∑ a : ι, readableTest a) + readableFrob) ≤
        1 - ((∑ a : ι, coeffTest a) + coeffFrob) := by
    linarith
  simpa [coeffTest, readableTest, coeffFrob, readableFrob]
    using hleft.trans hbase

/-- Target-budget form of the readable exact finite-cover CountSketch
row-Gram Loewner theorem. -/
theorem countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (net : ι → Fin n → ℝ) {ρ η L δ : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hbudget :
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (net a)) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
          A ρ η L) := by
  have hbase :=
    countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_vecNorm_add_frobNorm
      (r := r) (m := m) (n := n) (ι := ι) hr A net hcover hη hL hρ
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : ι,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq (rectMatMulVec A (net a)) ^ 2) / η ^ 2) +
          (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase

/-- Readable exact finite-cover CountSketch row-Gram Loewner probability
theorem with the finite cover instantiated by a coordinate product grid.

The one-dimensional grid is an exact analysis object; no floating-point
operation is introduced at this layer.  The product-grid index type has
cardinality `Fintype.card α ^ n` by `fintype_card_product_grid_index`. -/
theorem countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
    {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ) {δgrid ρ η L : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L) :
    1 -
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
          A ρ η L) := by
  classical
  have hcover :
      finiteUnitBallCover
        (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ :=
    finiteUnitBallCover_product_grid grid hgrid hδgrid hρgrid
  have hρ_nonneg : 0 ≤ ρ := by
    exact le_trans
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hδgrid) hρgrid
  simpa using
    countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_vecNorm_add_frobNorm
      (r := r) (m := m) (n := n) (ι := Fin n → α)
      hr A (fun a : Fin n → α => fun j : Fin n => grid (a j))
      hcover hη hL hρ_nonneg

/-- Target-budget form of the product-grid exact CountSketch row-Gram Loewner
theorem.  The displayed loss is fully expanded in terms of the grid vectors and
the Frobenius norm of the exact input. -/
theorem countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
          A ρ η L) := by
  have hbase :=
    countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
      (r := r) (m := m) (n := n) (α := α)
      hr A grid hgrid hδgrid hρgrid hη hL
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : Fin n → α,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
                η ^ 2) +
          (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase

/-- Readable non-injective sparse CountSketch floating-point Gram endpoint,
using the simplified coefficient bound `||A||_F^4`. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub_frobNorm
    (fp : FPModel) {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) {η : ℝ} (hη : 0 < η)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 - (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / η ^ 2 ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramFrobErrorEvent fp A η) := by
  classical
  let coeff : ℝ :=
    ∑ j : Fin n, ∑ l : Fin n,
      ∑ p : CountSketchDistinctPair m,
        (A p.1.1 j * A p.1.2 l) ^ 2
  let Bfull : ℝ := 2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2
  let Bcoeff : ℝ := 2 * (r : ℝ)⁻¹ * coeff
  have hcoeff : coeff ≤ frobNormSqRect A ^ 2 := by
    simpa [coeff] using
      countSketchDistinctPair_gramCoeffSq_sum_le_frobNormSqRect_sq A
  have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
  have hbudget : Bcoeff ≤ Bfull := by
    simpa [Bcoeff, Bfull] using
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
  have hbase :
      1 - Bcoeff / η ^ 2 ≤
        (countSketchProbability (r := r) (m := m) hr).eventProb
          (countSketchFlSparseGramDotRowGramFrobErrorEvent fp A η) := by
    simpa [Bcoeff, coeff] using
      countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub
        fp (r := r) (m := m) hr A hη hγm hγr
  have hleft : 1 - Bfull / η ^ 2 ≤ 1 - Bcoeff / η ^ 2 := by
    have hdiv : Bcoeff / η ^ 2 ≤ Bfull / η ^ 2 :=
      div_le_div_of_nonneg_right hbudget (sq_nonneg η)
    linarith
  exact hleft.trans hbase




















/-- Orthonormal-basis specialization of the exact product-grid CountSketch
row-Gram Loewner theorem.

For `U^T U = I`, the finite-test loss depends only on the exact grid-vector
norms, and the Frobenius loss becomes `(n : ℝ)^2`.  The product grid and
CountSketch probability laws are exact analysis/probability objects. -/
theorem countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_gridNorm_add_nat_orthonormal
    {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    (grid : α → ℝ) {δgrid ρ η L : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L) :
    1 -
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
          U ρ η L) := by
  classical
  have hbase :=
    countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
      (r := r) (m := m) (n := n) (α := α)
      hr U grid hgrid hδgrid hρgrid hη hL
  have hnorm : ∀ a : Fin n → α,
      vecNorm2Sq (rectMatMulVec U (fun j : Fin n => grid (a j))) =
        vecNorm2Sq (fun j : Fin n => grid (a j)) := by
    intro a
    simpa [rectMatMulVec] using
      hasOrthonormalColumns_vecNorm2Sq_mul_vec_eq U hU
        (fun j : Fin n => grid (a j))
  have hfrob : frobNormSqRect U = (n : ℝ) :=
    frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU
  simpa [hnorm, hfrob] using hbase

/-- Target-budget form of the orthonormal-basis exact product-grid
CountSketch Loewner theorem. -/
theorem countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget
    {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
          U ρ η L) := by
  have hbase :=
    countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_gridNorm_add_nat_orthonormal
      (r := r) (m := m) (n := n) (α := α)
      hr U hU grid hgrid hδgrid hρgrid hη hL
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : Fin n → α,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
                η ^ 2) +
          (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase

/-- Orthonormal-basis specialization of the non-injective sparse CountSketch
floating-point Gram endpoint.  For `U^T U = I`, the simplified failure
numerator is `2 n^2 / r`. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub_orthonormal
    (fp : FPModel) {r m n : ℕ} (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    {η : ℝ} (hη : 0 < η)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 - (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / η ^ 2 ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramFrobErrorEvent fp U η) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub_frobNorm
      fp (r := r) (m := m) hr U hη hγm hγr
  simpa [frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU] using hbase










































































































































/-- Exact-product-law non-injective sparse CountSketch floating-point
finite-Loewner Gram endpoint.  This is the S9v Frobenius/Markov endpoint
converted deterministically to two-sided Loewner form; it does not assume
collision-freeness or an external perturbation certificate. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub
    (fp : FPModel) {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) {η : ℝ} (hη : 0 < η)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 -
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ l : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 l) ^ 2) / η ^ 2 ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent fp A η) := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  have hbase :
      1 -
          (2 * (r : ℝ)⁻¹ *
            ∑ j : Fin n, ∑ l : Fin n,
              ∑ p : CountSketchDistinctPair m,
                (A p.1.1 j * A p.1.2 l) ^ 2) / η ^ 2 ≤
        P.eventProb (countSketchFlSparseGramDotRowGramFrobErrorEvent fp A η) := by
    simpa [P] using
      countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub
        fp (r := r) (m := m) hr A hη hγm hγr
  have hsubset :=
    countSketchFlSparseGramDotRowGramFrobErrorEvent_subset_twoSidedLoewnerEvent
      fp (r := r) A η
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Exact-product-law sparse CountSketch floating-point finite-cover Loewner
endpoint.  The probability loss is the same exact finite-test-plus-Frobenius
loss as in the exact cover theorem; the event radius additionally charges the
realized sparse Gram floating-point budget for `fl_countSketchSparseGramDot`. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
    (fp : FPModel) {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (net : ι → Fin n → ℝ) {ρ η L : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 -
        ((∑ a : ι,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (net a) p.1.1 *
                rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ l : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 l) ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))) := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  have hbase :
      1 -
          ((∑ a : ι,
            (2 * (r : ℝ)⁻¹ *
              ∑ p : CountSketchDistinctPair m,
                (rectMatMulVec A (net a) p.1.1 *
                  rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
          (2 * (r : ℝ)⁻¹ *
            ∑ j : Fin n, ∑ l : Fin n,
              ∑ p : CountSketchDistinctPair m,
                (A p.1.1 j * A p.1.2 l) ^ 2) / L ^ 2) ≤
        P.eventProb
          (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
            A ρ η L) := by
    simpa [P] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
        (r := r) (m := m) (n := n) (ι := ι)
        hr A net hcover hη hL hρ
  have hsubset :
      countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L ⊆
        countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2)) :=
    countSketchRowGramTwoSidedLoewnerCoverEvent_subset_flSparseGramDotRowGramTwoSidedLoewnerEvent
      fp A ρ η L hγm hγr
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Readable sparse CountSketch floating-point finite-cover Loewner endpoint.
This replaces the finite-test coefficient sums by `||A z_a||₂⁴` and the
Frobenius coefficient sum by `||A||_F⁴`; the computed event still charges the
realized sparse Gram floating-point budget. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_vecNorm_add_frobNorm
    (fp : FPModel) {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (net : ι → Fin n → ℝ) {ρ η L : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 -
        ((∑ a : ι,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (rectMatMulVec A (net a)) ^ 2) / η ^ 2) +
        (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))) := by
  classical
  let coeffTest : ι → ℝ :=
    fun a =>
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (net a) p.1.1 *
            rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2
  let readableTest : ι → ℝ :=
    fun a =>
      (2 * (r : ℝ)⁻¹ *
        vecNorm2Sq (rectMatMulVec A (net a)) ^ 2) / η ^ 2
  let coeffFrob : ℝ :=
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ l : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 l) ^ 2) / L ^ 2
  let readableFrob : ℝ :=
    (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2
  have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
  have htest_term : ∀ a : ι, coeffTest a ≤ readableTest a := by
    intro a
    have hcoeff :
        (∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (net a) p.1.1 *
            rectMatMulVec A (net a) p.1.2) ^ 2) ≤
          vecNorm2Sq (rectMatMulVec A (net a)) ^ 2 := by
      exact
        countSketchDistinctPair_vecCoeffSq_sum_le_vecNorm2Sq_sq
          (rectMatMulVec A (net a))
    have hmul :
        2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2 ≤
        2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (net a)) ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg η)
  have htest :
      (∑ a : ι, coeffTest a) ≤ ∑ a : ι, readableTest a :=
    Finset.sum_le_sum (fun a _ => htest_term a)
  have hfrob : coeffFrob ≤ readableFrob := by
    have hcoeff :
        (∑ j : Fin n, ∑ l : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 l) ^ 2) ≤
          frobNormSqRect A ^ 2 :=
      countSketchDistinctPair_gramCoeffSq_sum_le_frobNormSqRect_sq A
    have hmul :
        2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ l : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 l) ^ 2 ≤
        2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg L)
  have hbudget :
      (∑ a : ι, coeffTest a) + coeffFrob ≤
        (∑ a : ι, readableTest a) + readableFrob :=
    add_le_add htest hfrob
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
      fp (r := r) (m := m) (n := n) (ι := ι)
      hr A net hcover hη hL hρ hγm hγr
  have hleft :
      1 - ((∑ a : ι, readableTest a) + readableFrob) ≤
        1 - ((∑ a : ι, coeffTest a) + coeffFrob) := by
    linarith
  simpa [coeffTest, readableTest, coeffFrob, readableFrob]
    using hleft.trans hbase

/-- Target-budget form of the readable computed finite-cover CountSketch
Loewner endpoint.  The displayed readable loss is sufficient for probability
at least `1 - δ`; the sparse Gram floating-point budget remains in the event
radius. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (net : ι → Fin n → ℝ) {ρ η L δ : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (net a)) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_vecNorm_add_frobNorm
      fp (r := r) (m := m) (n := n) (ι := ι)
      hr A net hcover hη hL hρ hγm hγr
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : ι,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq (rectMatMulVec A (net a)) ^ 2) / η ^ 2) +
          (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase

/-- Readable finite-Loewner version of the non-injective sparse CountSketch
floating-point Gram endpoint, using the simplified failure numerator
`2 ||A||_F^4 / r`. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_frobNorm
    (fp : FPModel) {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) {η : ℝ} (hη : 0 < η)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 - (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / η ^ 2 ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent fp A η) := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  have hbase :
      1 - (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / η ^ 2 ≤
        P.eventProb (countSketchFlSparseGramDotRowGramFrobErrorEvent fp A η) := by
    simpa [P] using
      countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub_frobNorm
        fp (r := r) (m := m) hr A hη hγm hγr
  have hsubset :=
    countSketchFlSparseGramDotRowGramFrobErrorEvent_subset_twoSidedLoewnerEvent
      fp (r := r) A η
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Orthonormal-basis specialization of the non-injective sparse CountSketch
floating-point finite-Loewner Gram endpoint. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_orthonormal
    (fp : FPModel) {r m n : ℕ} (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    {η : ℝ} (hη : 0 < η)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 - (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / η ^ 2 ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent fp U η) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_frobNorm
      fp (r := r) (m := m) hr U hη hγm hγr
  simpa [frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU] using hbase

/-- Target-budget version of the exact-coefficient non-injective sparse
CountSketch finite-Loewner endpoint.  If the exact Markov loss is at most
`δ`, then the already charged computed sparse Gram event has probability at
least `1 - δ`. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget
    (fp : FPModel) {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) {η δ : ℝ} (hη : 0 < η)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ l : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 l) ^ 2) / η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent fp A η) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub
      fp (r := r) (m := m) hr A hη hγm hγr
  have hleft :
      1 - δ ≤
        1 -
          (2 * (r : ℝ)⁻¹ *
            ∑ j : Fin n, ∑ l : Fin n,
              ∑ p : CountSketchDistinctPair m,
                (A p.1.1 j * A p.1.2 l) ^ 2) / η ^ 2 := by
    linarith
  exact hleft.trans hbase

/-- Target-budget version of the computed sparse CountSketch finite-cover
Loewner endpoint.  If the fully displayed finite-test-plus-Frobenius exact-law
loss is at most `δ`, then the computed sparse Gram event holds with probability
at least `1 - δ`; all floating-point sparse Gram arithmetic is charged in the
realized event radius. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_budget
    (fp : FPModel) {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (net : ι → Fin n → ℝ) {ρ η L δ : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ l : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 l) ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
      fp (r := r) (m := m) (n := n) (ι := ι)
      hr A net hcover hη hL hρ hγm hγr
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : ι,
            (2 * (r : ℝ)⁻¹ *
              ∑ p : CountSketchDistinctPair m,
                (rectMatMulVec A (net a) p.1.1 *
                  rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
          (2 * (r : ℝ)⁻¹ *
            ∑ j : Fin n, ∑ l : Fin n,
              ∑ p : CountSketchDistinctPair m,
                (A p.1.1 j * A p.1.2 l) ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase

/-- Readable computed sparse CountSketch finite-cover Loewner endpoint with the
finite cover instantiated by a coordinate product grid.  Sparse apply and
Gram-dot arithmetic remain charged by the realized floating-point radius in the
event. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ) {δgrid ρ η L : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 -
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))) := by
  classical
  have hcover :
      finiteUnitBallCover
        (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ :=
    finiteUnitBallCover_product_grid grid hgrid hδgrid hρgrid
  have hρ_nonneg : 0 ≤ ρ := by
    exact le_trans
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hδgrid) hρgrid
  simpa using
    countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_vecNorm_add_frobNorm
      fp (r := r) (m := m) (n := n) (ι := Fin n → α)
      hr A (fun a : Fin n → α => fun j : Fin n => grid (a j))
      hcover hη hL hρ_nonneg hγm hγr

/-- Target-budget form of the product-grid computed sparse CountSketch
finite-cover Loewner endpoint.  The probability loss is exact-law and
analysis-only; the event radius still contains the concrete sparse Gram
floating-point budget. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
      fp (r := r) (m := m) (n := n) (α := α)
      hr A grid hgrid hδgrid hρgrid hη hL hγm hγr
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : Fin n → α,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
                η ^ 2) +
          (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase

/-- Orthonormal-basis specialization of the computed sparse CountSketch
product-grid finite-cover Loewner endpoint.

The event is fully computed at the sparse-Gram layer: it charges rounded
sparse signed products, bucket accumulation, and rounded Gram dot products
through the realized sparse-Gram perturbation budget.  The probability loss is
still exact-law and analysis-only. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_gridNorm_add_nat_orthonormal
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    (grid : α → ℝ) {δgrid ρ η L : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 -
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent
          (r := r) fp U (η + L * (2 * ρ + ρ ^ 2))) := by
  classical
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
      fp (r := r) (m := m) (n := n) (α := α)
      hr U grid hgrid hδgrid hρgrid hη hL hγm hγr
  have hnorm : ∀ a : Fin n → α,
      vecNorm2Sq (rectMatMulVec U (fun j : Fin n => grid (a j))) =
        vecNorm2Sq (fun j : Fin n => grid (a j)) := by
    intro a
    simpa [rectMatMulVec] using
      hasOrthonormalColumns_vecNorm2Sq_mul_vec_eq U hU
        (fun j : Fin n => grid (a j))
  have hfrob : frobNormSqRect U = (n : ℝ) :=
    frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU
  simpa [hnorm, hfrob] using hbase

/-- Target-budget form of the orthonormal-basis computed sparse CountSketch
product-grid endpoint. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent
          (r := r) fp U (η + L * (2 * ρ + ρ ^ 2))) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_gridNorm_add_nat_orthonormal
      fp (r := r) (m := m) (n := n) (α := α)
      hr U hU grid hgrid hδgrid hρgrid hη hL hγm hγr
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : Fin n → α,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
                η ^ 2) +
          (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase























































































































/-- Readable product-grid CountSketch finite-cover endpoint with stored
Rademacher signs.  The displayed probability loss is exact-law and
analysis-only; the event radius contains the concrete stored-sign sparse Gram
floating-point budget for the realized hash/sign pair. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) →
        ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ) {δgrid ρ η L : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 -
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2)) storedSignOf) := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  have hbase :
      1 -
          ((∑ a : Fin n → α,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq
                (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
                η ^ 2) +
          (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤
        P.eventProb
          (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
            A ρ η L) := by
    simpa [P] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
        (r := r) (m := m) (n := n) (α := α)
        hr A grid hgrid hδgrid hρgrid hη hL
  have hsubset :
      countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L ⊆
        countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2)) storedSignOf :=
    countSketchRowGramTwoSidedLoewnerCoverEvent_subset_flSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
      fp A ρ η L storedSignOf hγm hγr
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Target-budget version of the product-grid CountSketch endpoint with stored
Rademacher signs. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) →
        ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2)) storedSignOf) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
      fp (r := r) (m := m) (n := n) (α := α)
      hr A storedSignOf grid hgrid hδgrid hρgrid hη hL hγm hγr
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : Fin n → α,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq
                (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
                η ^ 2) +
          (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase

/-- Orthonormal-basis specialization of the product-grid CountSketch endpoint
with stored Rademacher signs.

This is an implementation-facing sparse-Gram theorem: the event charges the
stored sign table, rounded sparse signed products, bucket accumulation, and
rounded Gram dot products.  Only the probability laws and product-grid cover
remain exact analysis/probability objects. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_gridNorm_add_nat_orthonormal
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) →
        ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ) {δgrid ρ η L : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 -
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
          (r := r) fp U (η + L * (2 * ρ + ρ ^ 2)) storedSignOf) := by
  classical
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
      fp (r := r) (m := m) (n := n) (α := α)
      hr U storedSignOf grid hgrid hδgrid hρgrid hη hL hγm hγr
  have hnorm : ∀ a : Fin n → α,
      vecNorm2Sq (rectMatMulVec U (fun j : Fin n => grid (a j))) =
        vecNorm2Sq (fun j : Fin n => grid (a j)) := by
    intro a
    simpa [rectMatMulVec] using
      hasOrthonormalColumns_vecNorm2Sq_mul_vec_eq U hU
        (fun j : Fin n => grid (a j))
  have hfrob : frobNormSqRect U = (n : ℝ) :=
    frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU
  simpa [hnorm, hfrob] using hbase

/-- Target-budget form of the orthonormal-basis stored-sign product-grid
CountSketch endpoint. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) →
        ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
          (r := r) fp U (η + L * (2 * ρ + ρ ^ 2)) storedSignOf) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_gridNorm_add_nat_orthonormal
      fp (r := r) (m := m) (n := n) (α := α)
      hr U hU storedSignOf grid hgrid hδgrid hρgrid hη hL hγm hγr
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : Fin n → α,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
                η ^ 2) +
          (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase

/-- Concrete orthonormal product-grid stored-sign endpoint for signs copied
with `fl_mul sign_i 1`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
          (r := r) fp U (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hγm hγr hbudget

/-- Concrete orthonormal product-grid stored-sign endpoint for signs copied
with `fl_add sign_i 0`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignAddZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
          (r := r) fp U (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hγm hγr hbudget

/-- Concrete orthonormal product-grid stored-sign endpoint for signs copied
with `fl_sub sign_i 0`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignSubZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
          (r := r) fp U (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hγm hγr hbudget

/-- Concrete product-grid stored-sign endpoint for signs copied with
`fl_mul sign_i 1`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hγm hγr hbudget

/-- Concrete product-grid stored-sign endpoint for signs copied with
`fl_add sign_i 0`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignAddZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hγm hγr hbudget

/-- Concrete product-grid stored-sign endpoint for signs copied with
`fl_sub sign_i 0`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignSubZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hγm hγr hbudget































































































































/-- Product-grid CountSketch finite-cover endpoint with stored signs and
arbitrary fixed per-bucket traversal orders. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) →
        ComputedVector fp (rademacherSignVector ω))
    (orderOf : (hash : CountSketchHash r m) → (i : Fin r) →
      Fin (countSketchBucketSize hash i) ≃
        Fin (countSketchBucketSize hash i))
    (grid : α → ℝ) {δgrid ρ η L : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 -
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignPermutedRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          storedSignOf orderOf) := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  have hbase :
      1 -
          ((∑ a : Fin n → α,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq
                (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
                η ^ 2) +
          (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤
        P.eventProb
          (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
            A ρ η L) := by
    simpa [P] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
        (r := r) (m := m) (n := n) (α := α)
        hr A grid hgrid hδgrid hρgrid hη hL
  have hsubset :
      countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L ⊆
        countSketchFlSparseGramDotWithStoredSignPermutedRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          storedSignOf orderOf :=
    countSketchRowGramTwoSidedLoewnerCoverEvent_subset_flSparseGramDotWithStoredSignPermutedRowGramTwoSidedLoewnerEvent
      fp A ρ η L storedSignOf orderOf hγm hγr
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Target-budget product-grid endpoint with stored signs and arbitrary fixed
per-bucket traversal orders. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) →
        ComputedVector fp (rademacherSignVector ω))
    (orderOf : (hash : CountSketchHash r m) → (i : Fin r) →
      Fin (countSketchBucketSize hash i) ≃
        Fin (countSketchBucketSize hash i))
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignPermutedRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          storedSignOf orderOf) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDotWithStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
      fp (r := r) (m := m) (n := n) (α := α)
      hr A storedSignOf orderOf grid hgrid hδgrid hρgrid hη hL hγm hγr
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : Fin n → α,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq
                (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
                η ^ 2) +
          (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase

/-- Concrete permuted-bucket product-grid stored-sign endpoint for signs copied
with `fl_mul sign_i 1`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (orderOf : (hash : CountSketchHash r m) → (i : Fin r) →
      Fin (countSketchBucketSize hash i) ≃
        Fin (countSketchBucketSize hash i))
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignPermutedRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hγm hγr hbudget

/-- Concrete permuted-bucket product-grid stored-sign endpoint for signs copied
with `fl_add sign_i 0`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignAddZeroRightPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (orderOf : (hash : CountSketchHash r m) → (i : Fin r) →
      Fin (countSketchBucketSize hash i) ≃
        Fin (countSketchBucketSize hash i))
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignPermutedRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hγm hγr hbudget

/-- Concrete permuted-bucket product-grid stored-sign endpoint for signs copied
with `fl_sub sign_i 0`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignSubZeroRightPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (orderOf : (hash : CountSketchHash r m) → (i : Fin r) →
      Fin (countSketchBucketSize hash i) ≃
        Fin (countSketchBucketSize hash i))
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignPermutedRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hγm hγr hbudget




























































































































/-- Product-grid CountSketch finite-cover endpoint with stored signs and
tree-reduced bucket accumulation. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithStoredSignTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) →
        ComputedVector fp (rademacherSignVector ω))
    (treeOf : (hash : CountSketchHash r m) → (i : Fin r) →
      SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ) {δgrid ρ η L : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash) i).depth)
    (hγr : gammaValid fp r) :
    1 -
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignTreeRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          storedSignOf treeOf) := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  have hbase :
      1 -
          ((∑ a : Fin n → α,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq
                (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
                η ^ 2) +
          (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤
        P.eventProb
          (countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m)
            A ρ η L) := by
    simpa [P] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
        (r := r) (m := m) (n := n) (α := α)
        hr A grid hgrid hδgrid hρgrid hη hL
  have hsubset :
      countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L ⊆
        countSketchFlSparseGramDotWithStoredSignTreeRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          storedSignOf treeOf :=
    countSketchRowGramTwoSidedLoewnerCoverEvent_subset_flSparseGramDotWithStoredSignTreeRowGramTwoSidedLoewnerEvent
      fp A ρ η L storedSignOf treeOf hdepth hγr
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Target-budget product-grid endpoint with stored signs and tree-reduced
bucket accumulation. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithStoredSignTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) →
        ComputedVector fp (rademacherSignVector ω))
    (treeOf : (hash : CountSketchHash r m) → (i : Fin r) →
      SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash) i).depth)
    (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignTreeRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          storedSignOf treeOf) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDotWithStoredSignTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm
      fp (r := r) (m := m) (n := n) (α := α)
      hr A storedSignOf treeOf grid hgrid hδgrid hρgrid hη hL hdepth hγr
  have hleft :
      1 - δ ≤
        1 -
          ((∑ a : Fin n → α,
            (2 * (r : ℝ)⁻¹ *
              vecNorm2Sq
                (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
                η ^ 2) +
          (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) := by
    linarith
  exact hleft.trans hbase

/-- Concrete tree-reduced product-grid stored-sign endpoint for signs copied
with `fl_mul sign_i 1`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (treeOf : (hash : CountSketchHash r m) → (i : Fin r) →
      SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash) i).depth)
    (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignTreeRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSignTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hdepth hγr hbudget

/-- Concrete tree-reduced product-grid stored-sign endpoint for signs copied
with `fl_add sign_i 0`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignAddZeroRightTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (treeOf : (hash : CountSketchHash r m) → (i : Fin r) →
      SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash) i).depth)
    (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignTreeRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSignTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hdepth hγr hbudget

/-- Concrete tree-reduced product-grid stored-sign endpoint for signs copied
with `fl_sub sign_i 0`. -/
theorem countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignSubZeroRightTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (treeOf : (hash : CountSketchHash r m) → (i : Fin r) →
      SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ) {δgrid ρ η L δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash) i).depth)
    (hγr : gammaValid fp r)
    (hbudget :
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (fun j : Fin n => grid (a j))) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / L ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotWithStoredSignTreeRowGramTwoSidedLoewnerEvent
          (r := r) fp A (η + L * (2 * ρ + ρ ^ 2))
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf) := by
  exact
    countSketchProbability_eventProb_flSparseGramDotWithStoredSignTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget
      fp (r := r) (m := m) (n := n) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hdepth hγr hbudget

/-- Readable target-budget version of the non-injective sparse CountSketch
finite-Loewner endpoint.  The non-vacuity condition is the simplified loss
`2 ||A||_F^4 / (r η^2) <= δ`; all sparse apply and Gram-dot arithmetic remains
charged in the event radius. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget
    (fp : FPModel) {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) {η δ : ℝ} (hη : 0 < η)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget : (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent fp A η) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_frobNorm
      fp (r := r) (m := m) hr A hη hγm hγr
  have hleft :
      1 - δ ≤ 1 - (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / η ^ 2 := by
    linarith
  exact hleft.trans hbase

/-- Orthonormal-basis target-budget version of the non-injective sparse
CountSketch finite-Loewner endpoint.  For `UᵀU = I`, the simplified Markov
loss is `2 n^2 / (r η^2)`. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_delta_of_orthonormal_budget
    (fp : FPModel) {r m n : ℕ} (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    {η δ : ℝ} (hη : 0 < η)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r)
    (hbudget : (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent fp U η) := by
  have hbase :=
    countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_orthonormal
      fp (r := r) (m := m) hr U hU hη hγm hγr
  have hleft :
      1 - δ ≤ 1 - (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / η ^ 2 := by
    linarith
  exact hleft.trans hbase

































end NumStability
