import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.TraceMGF.UniformRows
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Gram
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.GramMoments
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixConcentration
import NumStability.Analysis.MatrixInequalities.LiebTrace.Concavity
import NumStability.FloatingPoint.Model
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm02.RowSampling.Endpoints
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.UniformRows
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation04.RowSamplingProbability.Normalization
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation05.GramApproximation.Bounds
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation05.GramApproximation.SampledGramEndpoints
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation06.LeverageProbability.Normalization
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.Leverage
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.SampledGramOperatorNorm
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.SketchedGramMoments
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.SketchInjectivityBounds
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.FloatingPoint

/-!
Relocated from the historical wave owners NumStability.Algorithms.RandNLA.UniformRowSamplingComposition, NumStability.Algorithms.RandNLA.UniformRowSamplingFP under the R09/R10 completion waves; reusable-tier destination per the reviewed route ledger.
-/

namespace NumStability

open scoped BigOperators

/-!
## Joint signed-preprocessing and uniform-row sampling law

The preceding files prove two separate probability statements:

* a Rademacher/sign event that makes leverage probabilities small after a flat
  signed-Hadamard preprocessing step;
* a uniform-row trace-MGF theorem for a fixed preconditioned matrix satisfying
  the resulting deterministic one-step row bounds.

This file puts both stages on one product probability space and composes the
events.  It still does not add the floating-point uniform-sketch transfer.
-/









































































































































































































/-- Collision-free CountSketch preprocessing composed with iid uniform-row
matrix concentration.

The only preprocessing failure is the exact hash-collision event, bounded by
`m^2 / r`.  Conditional on collision-freeness, exact Rademacher signs make the
CountSketch table an isometry on the input rows, so an orthonormal-column input
basis remains orthonormal after preprocessing.  Therefore every preconditioned
row has squared norm at most one, and the uniform-row MGF theorem is
instantiated with the explicit radius `L = r`. -/
theorem countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
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
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchUniformRowSampleGramTwoSidedEvent U ε) := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    {x | x.1 ∈ countSketchHashInjectiveEvent (r := r) (m := m)}
  let M : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) U
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      {samples |
        finiteLoewnerLe
          (fun j k : Fin n =>
            uniformRowSampleGram (M x) samples j k - finiteIdMatrix j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(uniformRowSampleGram (M x) samples j k - finiteIdMatrix j k))
          (fun j k : Fin n => ε * finiteIdMatrix j k)}
  let Ph := countSketchHashProbability (r := r) (m := m) hr
  let Pw := rademacherTraceProbability m
  let Ehash : Set (CountSketchHash r m) :=
    countSketchHashInjectiveEvent (r := r) (m := m)
  have hPreBase :
      1 - (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ ≤ Ph.eventProb Ehash := by
    simpa [Ph, Ehash] using
      countSketchHashProbability_eventProb_injective_ge_one_sub_square_inv
        (r := r) (m := m) hr
  have hPre : 1 - (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ ≤ P.eventProb Epre := by
    rw [show P = Ph.prod Pw by rfl]
    rw [show Epre = {x : CountSketchHash r m × RademacherTrace m | x.1 ∈ Ehash} by
      ext x
      rfl]
    rw [FiniteProbability.prod_eventProb_fst_eq Ph Pw Ehash]
    exact hPreBase
  have hrRpos : 0 < (r : ℝ) := by exact_mod_cast hr
  let L : ℝ := (r : ℝ)
  have hLpos : 0 < L := by
    simpa [L] using hrRpos
  have hSample : ∀ x, x ∈ Epre → 1 - δSample ≤ Q.eventProb (Fsample x) := by
    intro x hx
    have hhash : Function.Injective x.1 := by
      simpa [Epre, Ehash, countSketchHashInjectiveEvent] using hx
    have hMorth : HasOrthonormalColumns (M x) := by
      simpa [M] using
        countSketchRows_preconditionRows_hasOrthonormalColumns_of_hash_injective
          x.1 (rademacherSignVector x.2) U hhash
          (rademacherSignVector_sq x.2) hU
    have hrowOne : ∀ i : RowSample r, rowNormSq (M x) i ≤ 1 := by
      intro i
      exact rowNormSq_le_one_of_hasOrthonormalColumns (M x) hMorth i
    have hrowBound :
        ∀ i : RowSample r, (r : ℝ) * rowNormSq (M x) i ≤ L := by
      intro i
      calc
        (r : ℝ) * rowNormSq (M x) i
            ≤ (r : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left (hrowOne i) (le_of_lt hrRpos)
        _ = L := by simp [L]
    have hY :
        ∀ i : RowSample r,
          finiteLoewnerLe
            (fun j k : Fin n => uniformRowOuterGramSample (M x) i j k)
            (fun j k : Fin n => L * finiteIdMatrix j k) := by
      intro i
      have hbase :=
        uniformRowOuterGramSample_finiteLoewnerLe_of_rowNormSq_le
          (M x) i (hrowOne i)
      simpa [L] using hbase
    have hbudget' :
        let betaUpper : ℝ :=
          (Real.exp (theta * L) - theta * L - 1) / L ^ 2
        let betaLower : ℝ := Real.exp theta - theta - 1
        let tailUpper : ℝ :=
          Real.exp (-(theta * (s : ℝ) * ε)) *
            ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
        let tailLower : ℝ :=
          Real.exp (-(theta * (s : ℝ) * ε)) *
            ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
        tailUpper + tailLower ≤ δSample := by
      simpa [L] using hsampleBudget
    simpa [Q, Fsample] using
      uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget
        (s := s) (theta := theta) (ε := ε) (δ := δSample) (L := L)
        (M x) hMorth hr hs htheta hLpos hrowBound hY hbudget'
  have hprod :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (P.prod Q).eventProb
          {x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s |
            x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample
      ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹) δSample
      hδSample hPre hSample
  have hsubset :
      {x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s |
        x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} ⊆
      countSketchUniformRowSampleGramTwoSidedEvent U ε := by
    intro x hx
    exact hx.2
  exact hprod.trans (by
    simpa [countSketchUniformRowTraceProbability, P, Q] using
      FiniteProbability.eventProb_mono (P.prod Q) hsubset)














































































































































































































































































































































end NumStability

namespace NumStability
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

end NumStability
