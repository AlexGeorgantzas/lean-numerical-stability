import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.HashCollisionProbabilities
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.Preconditioning
import NumStability.Source.Higham.Chapter04.Problem04
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.RandNLA.Preconditioning under the R09/R10 completion waves; reusable-tier destination per the reviewed route ledger.
-/

open scoped BigOperators

namespace NumStability
/-- Full exact CountSketch product-law second-moment bound for one Gram entry.

Both hash and sign probability laws are exact.  The theorem has no conditional
embedding event: the actual CountSketch Gram entry error is expanded, the
Rademacher fourth moment is bounded by the sharp two-survivor factor `2`, and
the exact hash collision law contributes `1 / r`. -/
theorem countSketchProbability_expectationReal_rowGram_entry_error_sq_le
    {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) (j l : Fin n) :
    (countSketchProbability (r := r) (m := m) hr).expectationReal
      (fun x : CountSketchHash r m × RademacherTrace m =>
        (rowGram
            (preconditionRows
              (countSketchRows x.1 (rademacherSignVector x.2)) A) j l -
          rowGram A j l) ^ 2) ≤
      2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 l) ^ 2 := by
  classical
  let P := countSketchHashProbability (r := r) (m := m) hr
  let Q := rademacherTraceProbability m
  let X : CountSketchHash r m × RademacherTrace m → ℝ :=
    fun x =>
      (rowGram
          (preconditionRows
            (countSketchRows x.1 (rademacherSignVector x.2)) A) j l -
        rowGram A j l) ^ 2
  let B : CountSketchHash r m → ℝ :=
    fun hash =>
      2 * ∑ p : CountSketchDistinctPair m,
        (if hash p.1.1 = hash p.1.2 then
          A p.1.1 j * A p.1.2 l
        else 0) ^ 2
  have hprod :
      (countSketchProbability (r := r) (m := m) hr).expectationReal X =
        P.expectationReal
          (fun hash : CountSketchHash r m =>
            Q.expectationReal (fun ω : RademacherTrace m => X (hash, ω))) := by
    simpa [countSketchProbability, P, Q] using
      (FiniteProbability.prod_expectationReal_eq P Q X)
  have hfixed : ∀ hash : CountSketchHash r m,
      Q.expectationReal (fun ω : RademacherTrace m => X (hash, ω)) ≤ B hash := by
    intro hash
    simpa [Q, X, B] using
      rademacherTraceProbability_expectationReal_countSketchRows_rowGram_entry_error_sq_le
        hash A j l
  have hhash :
      P.expectationReal B =
        2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 l) ^ 2 := by
    calc
      P.expectationReal B
          =
        2 * P.expectationReal
          (fun hash : CountSketchHash r m =>
            ∑ p : CountSketchDistinctPair m,
              (if hash p.1.1 = hash p.1.2 then
                A p.1.1 j * A p.1.2 l
              else 0) ^ 2) := by
            simp [B, FiniteProbability.expectationReal_const_mul]
      _ =
        2 * ∑ p : CountSketchDistinctPair m,
          P.expectationReal
            (fun hash : CountSketchHash r m =>
              (if hash p.1.1 = hash p.1.2 then
                A p.1.1 j * A p.1.2 l
              else 0) ^ 2) := by
            rw [FiniteProbability.expectationReal_sum]
      _ =
        2 * ∑ p : CountSketchDistinctPair m,
          (r : ℝ)⁻¹ * (A p.1.1 j * A p.1.2 l) ^ 2 := by
            apply congrArg (fun z => 2 * z)
            apply Finset.sum_congr rfl
            intro p _
            exact
              countSketchHashProbability_expectationReal_collision_coeff_sq_eq_inv_mul
                (r := r) (m := m) hr p (A p.1.1 j * A p.1.2 l)
      _ =
        2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 l) ^ 2 := by
            rw [← Finset.mul_sum]
            ring
  rw [hprod]
  exact (FiniteProbability.expectationReal_mono P hfixed).trans_eq hhash



























































































































/-- Full exact CountSketch product-law second-moment bound for one fixed
quadratic form of the Gram error.

Both the hash and sign laws are exact.  The random matrix is the actual
CountSketch-preconditioned matrix, and the coefficient sum is the concrete
off-diagonal collision expression for the exact vector `A x`; no embedding
certificate or perturbation event is assumed. -/
theorem countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le
    {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    (countSketchProbability (r := r) (m := m) hr).expectationReal
      (fun y : CountSketchHash r m × RademacherTrace m =>
        (finiteQuadraticForm
          (fun j k : Fin n =>
            rowGram
                (preconditionRows
                  (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
              rowGram A j k) x) ^ 2) ≤
      2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A x p.1.1 * rectMatMulVec A x p.1.2) ^ 2 := by
  classical
  let Ax : Fin m → Fin 1 → ℝ :=
    fun a _ => rectMatMulVec A x a
  let P := countSketchProbability (r := r) (m := m) hr
  have hpoint : ∀ y : CountSketchHash r m × RademacherTrace m,
      finiteQuadraticForm
        (fun j k : Fin n =>
          rowGram
              (preconditionRows
                (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
            rowGram A j k) x =
        rowGram
            (preconditionRows
              (countSketchRows y.1 (rademacherSignVector y.2)) Ax)
            (0 : Fin 1) (0 : Fin 1) -
          rowGram Ax (0 : Fin 1) (0 : Fin 1) := by
    intro y
    simpa [Ax] using
      finiteQuadraticForm_rowGram_preconditionRows_sub_rowGram_eq_rowGram_singleton_error
        (Pi := countSketchRows y.1 (rademacherSignVector y.2))
        (A := A) (x := x)
  calc
    P.expectationReal
      (fun y : CountSketchHash r m × RademacherTrace m =>
        (finiteQuadraticForm
          (fun j k : Fin n =>
            rowGram
                (preconditionRows
                  (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
              rowGram A j k) x) ^ 2)
        =
      P.expectationReal
        (fun y : CountSketchHash r m × RademacherTrace m =>
          (rowGram
              (preconditionRows
                (countSketchRows y.1 (rademacherSignVector y.2)) Ax)
              (0 : Fin 1) (0 : Fin 1) -
            rowGram Ax (0 : Fin 1) (0 : Fin 1)) ^ 2) := by
          apply congrArg P.expectationReal
          funext y
          rw [hpoint y]
    _ ≤
      2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (Ax p.1.1 (0 : Fin 1) * Ax p.1.2 (0 : Fin 1)) ^ 2 :=
          countSketchProbability_expectationReal_rowGram_entry_error_sq_le
            (r := r) (m := m) (n := 1) hr Ax
            (0 : Fin 1) (0 : Fin 1)
    _ =
      2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A x p.1.1 * rectMatMulVec A x p.1.2) ^ 2 := by
          rfl















































/-- Readable fixed-vector CountSketch Gram quadratic-form moment bound using
`||A x||₂⁴`. -/
theorem countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le_vecNorm
    {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    (countSketchProbability (r := r) (m := m) hr).expectationReal
      (fun y : CountSketchHash r m × RademacherTrace m =>
        (finiteQuadraticForm
          (fun j k : Fin n =>
            rowGram
                (preconditionRows
                  (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
              rowGram A j k) x) ^ 2) ≤
      2 * (r : ℝ)⁻¹ * vecNorm2Sq (rectMatMulVec A x) ^ 2 := by
  classical
  let coeff : ℝ :=
    ∑ p : CountSketchDistinctPair m,
      (rectMatMulVec A x p.1.1 * rectMatMulVec A x p.1.2) ^ 2
  have hcoeff : coeff ≤ vecNorm2Sq (rectMatMulVec A x) ^ 2 := by
    simpa [coeff] using
      countSketchDistinctPair_vecCoeffSq_sum_le_vecNorm2Sq_sq
        (rectMatMulVec A x)
  have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
  have hbase :=
    countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le
      (r := r) (m := m) hr A x
  exact hbase.trans
    (by
      simpa [coeff, mul_assoc] using
        mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg)

/-- Readable fixed-vector CountSketch Gram quadratic-form moment bound using
the rectangular Frobenius norm of `A`. -/
theorem countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le_frobNorm
    {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    (countSketchProbability (r := r) (m := m) hr).expectationReal
      (fun y : CountSketchHash r m × RademacherTrace m =>
        (finiteQuadraticForm
          (fun j k : Fin n =>
            rowGram
                (preconditionRows
                  (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
              rowGram A j k) x) ^ 2) ≤
      2 * (r : ℝ)⁻¹ * (frobNormSqRect A * vecNorm2Sq x) ^ 2 := by
  classical
  have hAx :
      vecNorm2Sq (rectMatMulVec A x) ≤
        frobNormSqRect A * vecNorm2Sq x :=
    vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_mul A x
  have hAx_nonneg : 0 ≤ vecNorm2Sq (rectMatMulVec A x) :=
    vecNorm2Sq_nonneg (rectMatMulVec A x)
  have hright_nonneg : 0 ≤ frobNormSqRect A * vecNorm2Sq x :=
    mul_nonneg (frobNormSqRect_nonneg A) (vecNorm2Sq_nonneg x)
  have hsq :
      vecNorm2Sq (rectMatMulVec A x) ^ 2 ≤
        (frobNormSqRect A * vecNorm2Sq x) ^ 2 := by
    nlinarith
  have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
  have hbase :=
    countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le_vecNorm
      (r := r) (m := m) hr A x
  exact hbase.trans
    (by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hsq hfactor_nonneg)

/-- Exact-product-law high-probability fixed-vector quadratic-form bound for
the CountSketch Gram error.  This is a Chebyshev/Markov consequence of the
proved fixed-vector second moment; it uses no embedding certificate. -/
theorem countSketchProbability_eventProb_abs_rowGram_quadratic_error_le_ge_one_sub
    {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) {η : ℝ} (hη : 0 < η) :
    1 -
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A x p.1.1 * rectMatMulVec A x p.1.2) ^ 2) /
          η ^ 2 ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        {y : CountSketchHash r m × RademacherTrace m |
          |finiteQuadraticForm
            (fun j k : Fin n =>
              rowGram
                  (preconditionRows
                    (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
                rowGram A j k) x| ≤ η} := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let X : CountSketchHash r m × RademacherTrace m → ℝ :=
    fun y =>
      finiteQuadraticForm
        (fun j k : Fin n =>
          rowGram
              (preconditionRows
                (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
            rowGram A j k) x
  let B : ℝ :=
    2 * (r : ℝ)⁻¹ *
      ∑ p : CountSketchDistinctPair m,
        (rectMatMulVec A x p.1.1 * rectMatMulVec A x p.1.2) ^ 2
  have hsecond : P.expectationReal (fun y => X y ^ 2) ≤ B := by
    simpa [P, X, B] using
      countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le
        (r := r) (m := m) hr A x
  have hmoment :
      P.expectationReal (fun y => (X y - 0) ^ 2) / η ^ 2 ≤ B / η ^ 2 := by
    have hrewrite :
        P.expectationReal (fun y => (X y - 0) ^ 2) =
          P.expectationReal (fun y => X y ^ 2) := by
      apply congrArg P.expectationReal
      funext y
      ring
    rw [hrewrite]
    exact div_le_div_of_nonneg_right hsecond (sq_nonneg η)
  have hcheb :=
    FiniteProbability.eventProb_abs_sub_le_ge_one_sub_of_second_moment
      P X 0 η (B / η ^ 2) hη hmoment
  simpa [P, X, B] using hcheb

/-- Target-budget version of the fixed-vector CountSketch quadratic-form
event. -/
theorem countSketchProbability_eventProb_abs_rowGram_quadratic_error_le_ge_one_sub_delta_of_coeff_budget
    {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) {η δ : ℝ} (hη : 0 < η)
    (hbudget :
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A x p.1.1 * rectMatMulVec A x p.1.2) ^ 2) /
        η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        {y : CountSketchHash r m × RademacherTrace m |
          |finiteQuadraticForm
            (fun j k : Fin n =>
              rowGram
                  (preconditionRows
                    (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
                rowGram A j k) x| ≤ η} := by
  have hbase :=
    countSketchProbability_eventProb_abs_rowGram_quadratic_error_le_ge_one_sub
      (r := r) (m := m) hr A x hη
  have hleft :
      1 - δ ≤
        1 -
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A x p.1.1 * rectMatMulVec A x p.1.2) ^ 2) /
            η ^ 2 := by
    linarith
  exact hleft.trans hbase

/-- Simultaneous finite-test fixed-vector CountSketch quadratic-form event.

This is the exact finite-union wrapper around
`countSketchProbability_eventProb_abs_rowGram_quadratic_error_le_ge_one_sub`.
It is exact probability and exact arithmetic only: the finite family of test
vectors is an analysis object, and no floating-point computation appears. -/
theorem countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_sum_coeff_budget
    {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (x : ι → Fin n → ℝ) (η : ι → ℝ) (hη : ∀ a : ι, 0 < η a) :
    1 -
        (∑ a : ι,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (x a) p.1.1 *
                rectMatMulVec A (x a) p.1.2) ^ 2) / (η a) ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        {y : CountSketchHash r m × RademacherTrace m |
          ∀ a : ι,
            |finiteQuadraticForm
              (fun j k : Fin n =>
                rowGram
                    (preconditionRows
                      (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
                  rowGram A j k) (x a)| ≤ η a} := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let E : ι → Set (CountSketchHash r m × RademacherTrace m) :=
    fun a =>
      {y |
        |finiteQuadraticForm
          (fun j k : Fin n =>
            rowGram
                (preconditionRows
                  (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
              rowGram A j k) (x a)| ≤ η a}
  let δa : ι → ℝ :=
    fun a =>
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (x a) p.1.1 *
            rectMatMulVec A (x a) p.1.2) ^ 2) / (η a) ^ 2
  have hE : ∀ a : ι, 1 - δa a ≤ P.eventProb (E a) := by
    intro a
    simpa [P, E, δa] using
      countSketchProbability_eventProb_abs_rowGram_quadratic_error_le_ge_one_sub
        (r := r) (m := m) hr A (x a) (hη a)
  have hall :=
    FiniteProbability.eventProb_forall_ge_one_sub_sum P E δa hE
  simpa [P, E, δa] using hall

/-- Target-budget form of the finite-test fixed-vector CountSketch
quadratic-form event. -/
theorem countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_delta_of_sum_coeff_budget
    {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (x : ι → Fin n → ℝ) (η : ι → ℝ) {δ : ℝ}
    (hη : ∀ a : ι, 0 < η a)
    (hbudget :
      (∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (x a) p.1.1 *
              rectMatMulVec A (x a) p.1.2) ^ 2) / (η a) ^ 2) ≤ δ) :
    1 - δ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        {y : CountSketchHash r m × RademacherTrace m |
          ∀ a : ι,
            |finiteQuadraticForm
              (fun j k : Fin n =>
                rowGram
                    (preconditionRows
                      (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
                  rowGram A j k) (x a)| ≤ η a} := by
  have hbase :=
    countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_sum_coeff_budget
      (r := r) (m := m) (n := n) (ι := ι) hr A x η hη
  have hleft :
      1 - δ ≤
        1 -
          (∑ a : ι,
            (2 * (r : ℝ)⁻¹ *
              ∑ p : CountSketchDistinctPair m,
                (rectMatMulVec A (x a) p.1.1 *
                  rectMatMulVec A (x a) p.1.2) ^ 2) / (η a) ^ 2) := by
    linarith
  exact hleft.trans hbase

/-- Readable finite-test fixed-vector CountSketch event using
`||A x_a||₂⁴` in the failure sum. -/
theorem countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_sum_vecNorm_budget
    {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (x : ι → Fin n → ℝ) (η : ι → ℝ) (hη : ∀ a : ι, 0 < η a) :
    1 -
        (∑ a : ι,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (rectMatMulVec A (x a)) ^ 2) / (η a) ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        {y : CountSketchHash r m × RademacherTrace m |
          ∀ a : ι,
            |finiteQuadraticForm
              (fun j k : Fin n =>
                rowGram
                    (preconditionRows
                      (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
                  rowGram A j k) (x a)| ≤ η a} := by
  classical
  let coeff : ι → ℝ :=
    fun a =>
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (x a) p.1.1 *
            rectMatMulVec A (x a) p.1.2) ^ 2) / (η a) ^ 2
  let readable : ι → ℝ :=
    fun a =>
      (2 * (r : ℝ)⁻¹ *
        vecNorm2Sq (rectMatMulVec A (x a)) ^ 2) / (η a) ^ 2
  have hterm : ∀ a : ι, coeff a ≤ readable a := by
    intro a
    have hcoeff :
        (∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (x a) p.1.1 *
            rectMatMulVec A (x a) p.1.2) ^ 2) ≤
          vecNorm2Sq (rectMatMulVec A (x a)) ^ 2 := by
      exact
        countSketchDistinctPair_vecCoeffSq_sum_le_vecNorm2Sq_sq
          (rectMatMulVec A (x a))
    have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
      exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
    have hmul :
        2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (x a) p.1.1 *
              rectMatMulVec A (x a) p.1.2) ^ 2 ≤
        2 * (r : ℝ)⁻¹ *
          vecNorm2Sq (rectMatMulVec A (x a)) ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg (η a))
  have hsum : (∑ a : ι, coeff a) ≤ ∑ a : ι, readable a :=
    Finset.sum_le_sum (fun a _ => hterm a)
  have hbase :=
    countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_sum_coeff_budget
      (r := r) (m := m) (n := n) (ι := ι) hr A x η hη
  have hleft : 1 - (∑ a : ι, readable a) ≤ 1 - (∑ a : ι, coeff a) := by
    linarith
  simpa [coeff, readable] using hleft.trans hbase

/-- Readable finite-test fixed-vector CountSketch event using
`||A||_F⁴ ||x_a||₂⁴` in the failure sum. -/
theorem countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_sum_frobNorm_budget
    {r m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : 0 < r) (A : Fin m → Fin n → ℝ)
    (x : ι → Fin n → ℝ) (η : ι → ℝ) (hη : ∀ a : ι, 0 < η a) :
    1 -
        (∑ a : ι,
          (2 * (r : ℝ)⁻¹ *
            (frobNormSqRect A * vecNorm2Sq (x a)) ^ 2) / (η a) ^ 2) ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        {y : CountSketchHash r m × RademacherTrace m |
          ∀ a : ι,
            |finiteQuadraticForm
              (fun j k : Fin n =>
                rowGram
                    (preconditionRows
                      (countSketchRows y.1 (rademacherSignVector y.2)) A) j k -
                  rowGram A j k) (x a)| ≤ η a} := by
  classical
  let readable : ι → ℝ :=
    fun a =>
      (2 * (r : ℝ)⁻¹ *
        vecNorm2Sq (rectMatMulVec A (x a)) ^ 2) / (η a) ^ 2
  let frobReadable : ι → ℝ :=
    fun a =>
      (2 * (r : ℝ)⁻¹ *
        (frobNormSqRect A * vecNorm2Sq (x a)) ^ 2) / (η a) ^ 2
  have hterm : ∀ a : ι, readable a ≤ frobReadable a := by
    intro a
    have hAx :
        vecNorm2Sq (rectMatMulVec A (x a)) ≤
          frobNormSqRect A * vecNorm2Sq (x a) :=
      vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_mul A (x a)
    have hAx_nonneg : 0 ≤ vecNorm2Sq (rectMatMulVec A (x a)) :=
      vecNorm2Sq_nonneg (rectMatMulVec A (x a))
    have hright_nonneg : 0 ≤ frobNormSqRect A * vecNorm2Sq (x a) :=
      mul_nonneg (frobNormSqRect_nonneg A) (vecNorm2Sq_nonneg (x a))
    have hsq :
        vecNorm2Sq (rectMatMulVec A (x a)) ^ 2 ≤
          (frobNormSqRect A * vecNorm2Sq (x a)) ^ 2 := by
      nlinarith
    have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
      exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
    have hmul :
        2 * (r : ℝ)⁻¹ * vecNorm2Sq (rectMatMulVec A (x a)) ^ 2 ≤
        2 * (r : ℝ)⁻¹ * (frobNormSqRect A * vecNorm2Sq (x a)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg (η a))
  have hsum : (∑ a : ι, readable a) ≤ ∑ a : ι, frobReadable a :=
    Finset.sum_le_sum (fun a _ => hterm a)
  have hbase :=
    countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_sum_vecNorm_budget
      (r := r) (m := m) (n := n) (ι := ι) hr A x η hη
  have hleft :
      1 - (∑ a : ι, frobReadable a) ≤
        1 - (∑ a : ι, readable a) := by
    linarith
  simpa [readable, frobReadable] using hleft.trans hbase


















































































































/-- Full exact CountSketch product-law Frobenius second-moment bound for the
Gram error.  This is obtained by summing the proved entrywise bound over all
Gram coordinates. -/
theorem countSketchProbability_expectationReal_rowGram_frob_error_sq_le
    {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) :
    (countSketchProbability (r := r) (m := m) hr).expectationReal
      (fun x : CountSketchHash r m × RademacherTrace m =>
        frobNormSq
          (fun j l : Fin n =>
            rowGram
                (preconditionRows
                  (countSketchRows x.1 (rademacherSignVector x.2)) A) j l -
              rowGram A j l)) ≤
      2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ l : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 l) ^ 2 := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  calc
    P.expectationReal
      (fun x : CountSketchHash r m × RademacherTrace m =>
        frobNormSq
          (fun j l : Fin n =>
            rowGram
                (preconditionRows
                  (countSketchRows x.1 (rademacherSignVector x.2)) A) j l -
              rowGram A j l))
        =
      ∑ j : Fin n, ∑ l : Fin n,
        P.expectationReal
          (fun x : CountSketchHash r m × RademacherTrace m =>
            (rowGram
                (preconditionRows
                  (countSketchRows x.1 (rademacherSignVector x.2)) A) j l -
              rowGram A j l) ^ 2) := by
          unfold frobNormSq
          rw [FiniteProbability.expectationReal_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [FiniteProbability.expectationReal_sum]
    _ ≤
      ∑ j : Fin n, ∑ l : Fin n,
        2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 l) ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro l _
          exact countSketchProbability_expectationReal_rowGram_entry_error_sq_le
            (r := r) (m := m) hr A j l
    _ =
      2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ l : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 l) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]

/-- Exact non-injective CountSketch Frobenius high-probability Gram bound.

This is a Markov consequence of the proved second moment.  It is weaker than
the optimal subspace-embedding concentration theorem, but it is unconditional:
no injectivity event or certificate-existence assumption is used. -/
theorem countSketchProbability_eventProb_rowGram_frob_error_le_ge_one_sub
    {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) {η : ℝ} (hη : 0 < η) :
    1 -
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ l : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 l) ^ 2) / η ^ 2 ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        {x : CountSketchHash r m × RademacherTrace m |
          frobNorm
            (fun j l : Fin n =>
              rowGram
                  (preconditionRows
                    (countSketchRows x.1 (rademacherSignVector x.2)) A) j l -
                rowGram A j l) ≤ η} := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Z : CountSketchHash r m × RademacherTrace m → ℝ :=
    fun x =>
      frobNorm
        (fun j l : Fin n =>
          rowGram
              (preconditionRows
                (countSketchRows x.1 (rademacherSignVector x.2)) A) j l -
            rowGram A j l)
  let B : ℝ :=
    2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ l : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 l) ^ 2
  have hmarkov :
      1 - P.expectationReal (fun x => Z x ^ 2) / η ^ 2 ≤
        P.eventProb {x | Z x ≤ η} := by
    exact
      FiniteProbability.eventProb_le_ge_one_sub_expectationReal_sq_div
        P Z η (fun x => frobNorm_nonneg _) hη
  have hZsq :
      P.expectationReal (fun x => Z x ^ 2) =
        P.expectationReal
          (fun x : CountSketchHash r m × RademacherTrace m =>
            frobNormSq
              (fun j l : Fin n =>
                rowGram
                    (preconditionRows
                      (countSketchRows x.1 (rademacherSignVector x.2)) A) j l -
                  rowGram A j l)) := by
    apply congrArg P.expectationReal
    funext x
    exact frobNorm_sq _
  have hsecond :
      P.expectationReal (fun x => Z x ^ 2) ≤ B := by
    rw [hZsq]
    simpa [P, B] using
      countSketchProbability_expectationReal_rowGram_frob_error_sq_le
        (r := r) (m := m) hr A
  have hηsq_nonneg : 0 ≤ η ^ 2 := sq_nonneg η
  have hleft :
      1 - B / η ^ 2 ≤
        1 - P.expectationReal (fun x => Z x ^ 2) / η ^ 2 := by
    have hdiv :
        P.expectationReal (fun x => Z x ^ 2) / η ^ 2 ≤ B / η ^ 2 :=
      div_le_div_of_nonneg_right hsecond hηsq_nonneg
    linarith
  exact hleft.trans hmarkov

end NumStability
