import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.RandNLA.RowSamplingLeverage
import NumStability.Algorithms.RandNLA.UniformRowSampling
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.Core
import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixConcentration
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.Preconditioning

/-!
# NumStability.Algorithms.RandNLA.Preconditioning compatibility facade

Historical declaration-bearing W11 facade. The genuine-private reverse closure remains here with its original identity; all movable commands are re-exported from canonical modules.
-/

-- Algorithms/RandNLA/Preconditioning.lean
--
-- Random-projection/preconditioning consequences for Algorithm 3 of
-- Drineas--Mahoney's CACM RandNLA survey.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602
















namespace NumStability

open scoped BigOperators

/-!
## Algorithm 3: random-projection preconditioning

Algorithm 3 in Drineas--Mahoney is a meta-algorithm:

* to uniformize row information, return `PiL A`;
* to uniformize column information, return `A PiR`;
* to uniformize element information, return `PiL A PiR`.

This file formalizes the exact products and floating-point products.  The
probabilistic uniformization analysis depends on the distribution chosen for
`PiL` and `PiR`; the CACM survey states that role descriptively rather than as a
single theorem.  The stability results below are therefore deterministic once
the preprocessing matrices have been drawn, and they reuse the repository's
matrix-multiplication error theorem.
-/

-- ============================================================
-- Exact Algorithm 3 outputs
-- ============================================================

































namespace ComputedPreconditioner

variable {fp : FPModel} {r m : ℕ} {Pi : Fin r → Fin m → ℝ}






























end ComputedPreconditioner











namespace ComputedVector

variable {fp : FPModel} {n : ℕ} {x : Fin n → ℝ}


























































































































































































































































end ComputedVector





































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































namespace ComputedMatrix

variable {fp : FPModel} {m n : ℕ} {A : Fin m → Fin n → ℝ}













































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end ComputedMatrix






























































































-- ============================================================
-- Exact orthogonal-preconditioning consequences
-- ============================================================

























































































































-- ============================================================
-- Deterministic SRHT-style sign preprocessing prerequisites
-- ============================================================








































-- ============================================================
-- Finite Rademacher sign-vector model for SRHT-style routes
-- ============================================================






















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- Finite CountSketch/input-sparsity preprocessing foundations
-- ============================================================








































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Under the exact iid uniform CountSketch hash law, two distinct input rows
collide with probability exactly `1 / r`. -/
theorem countSketchHashProbability_eventProb_pairCollision_eq_inv
    {r m : ℕ} (hr : 0 < r) (a b : Fin m) (hab : a ≠ b) :
    (countSketchHashProbability (r := r) (m := m) hr).eventProb
      (countSketchHashPairCollision (r := r) a b) = (r : ℝ)⁻¹ := by
  simpa [countSketchHashProbability, countSketchHashProbMass,
    countSketchHashPairCollision, CountSketchHash, RowTrace] using
    uniformRowTraceProbability_eventProb_pair_collision_eq_inv
      (m := r) (steps := m) hr a b hab

/-- Under the exact iid uniform CountSketch hash law, the real-valued
collision indicator for two distinct input rows has mean `1 / r`. -/
theorem countSketchHashProbability_expectationReal_pairCollisionIndicator_eq_inv
    {r m : ℕ} (hr : 0 < r) (a b : Fin m) (hab : a ≠ b) :
    (countSketchHashProbability (r := r) (m := m) hr).expectationReal
      (fun hash : CountSketchHash r m =>
        if hash a = hash b then (1 : ℝ) else 0) = (r : ℝ)⁻¹ := by
  classical
  let P := countSketchHashProbability (r := r) (m := m) hr
  let E := countSketchHashPairCollision (r := r) a b
  calc
    P.expectationReal
      (fun hash : CountSketchHash r m =>
        if hash a = hash b then (1 : ℝ) else 0)
        =
      P.expectationReal
        (fun hash : CountSketchHash r m =>
          if hash ∈ E then (1 : ℝ) else 0) := by
            apply congrArg P.expectationReal
            funext hash
            simp [E, countSketchHashPairCollision]
    _ = P.eventProb E := by
            exact FiniteProbability.expectationReal_indicator_eq_eventProb P E
    _ = (r : ℝ)⁻¹ := by
            simpa [P, E] using
              countSketchHashProbability_eventProb_pairCollision_eq_inv
                (r := r) (m := m) hr a b hab

/-- Under the exact iid uniform CountSketch hash law, two distinct input rows
avoid collision with probability exactly `1 - 1 / r`. -/
theorem countSketchHashProbability_eventProb_pairNoCollision_eq_one_sub_inv
    {r m : ℕ} (hr : 0 < r) (a b : Fin m) (hab : a ≠ b) :
    (countSketchHashProbability (r := r) (m := m) hr).eventProb
      (countSketchHashPairNoCollision (r := r) a b) = 1 - (r : ℝ)⁻¹ := by
  classical
  let P := countSketchHashProbability (r := r) (m := m) hr
  let E := countSketchHashPairCollision (r := r) a b
  have hcoll : P.eventProb E = (r : ℝ)⁻¹ := by
    simpa [P, E] using
      countSketchHashProbability_eventProb_pairCollision_eq_inv
        (r := r) (m := m) hr a b hab
  have hcompl_set : Eᶜ = countSketchHashPairNoCollision (r := r) a b := by
    ext hash
    simp [E, countSketchHashPairCollision, countSketchHashPairNoCollision]
  have hsplit := P.eventProb_add_eventProb_compl E
  rw [hcoll, hcompl_set] at hsplit
  linarith












































































































































































































































































































































































































































































































































































































































































/-- Exact hash expectation of a collided coefficient square.  The probability
law is exact and contributes the factor `1 / r`. -/
theorem countSketchHashProbability_expectationReal_collision_coeff_sq_eq_inv_mul
    {r m : ℕ} (hr : 0 < r) (p : CountSketchDistinctPair m) (C : ℝ) :
    (countSketchHashProbability (r := r) (m := m) hr).expectationReal
      (fun hash : CountSketchHash r m =>
        (if hash p.1.1 = hash p.1.2 then C else 0) ^ 2) =
      (r : ℝ)⁻¹ * C ^ 2 := by
  classical
  let P := countSketchHashProbability (r := r) (m := m) hr
  calc
    P.expectationReal
      (fun hash : CountSketchHash r m =>
        (if hash p.1.1 = hash p.1.2 then C else 0) ^ 2)
        =
      P.expectationReal
        (fun hash : CountSketchHash r m =>
          (if hash p.1.1 = hash p.1.2 then (1 : ℝ) else 0) * C ^ 2) := by
          apply congrArg P.expectationReal
          funext hash
          by_cases hcollision : hash p.1.1 = hash p.1.2
          · simp [hcollision]
          · simp [hcollision]
    _ =
      P.expectationReal
        (fun hash : CountSketchHash r m =>
          if hash p.1.1 = hash p.1.2 then (1 : ℝ) else 0) * C ^ 2 := by
          rw [FiniteProbability.expectationReal_mul_const]
    _ = (r : ℝ)⁻¹ * C ^ 2 := by
          rw [countSketchHashProbability_expectationReal_pairCollisionIndicator_eq_inv
            (r := r) (m := m) hr p.1.1 p.1.2 p.2]









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

































/-- Union-bound probability lower bound for the exact CountSketch hash to be
injective, in exact ordered-pair-sum form. -/
theorem countSketchHashProbability_eventProb_injective_ge_one_sub_pair_sum
    {r m : ℕ} (hr : 0 < r) :
    1 - (∑ _p : CountSketchDistinctPair m, (r : ℝ)⁻¹) ≤
      (countSketchHashProbability (r := r) (m := m) hr).eventProb
        (countSketchHashInjectiveEvent (r := r) (m := m)) := by
  classical
  let P := countSketchHashProbability (r := r) (m := m) hr
  let E : CountSketchDistinctPair m → Set (CountSketchHash r m) :=
    fun p => countSketchHashPairNoCollision (r := r) p.1.1 p.1.2
  let δ : CountSketchDistinctPair m → ℝ := fun _ => (r : ℝ)⁻¹
  have hE : ∀ p : CountSketchDistinctPair m, 1 - δ p ≤ P.eventProb (E p) := by
    intro p
    have hpair :=
      countSketchHashProbability_eventProb_pairNoCollision_eq_one_sub_inv
        (r := r) (m := m) hr p.1.1 p.1.2 p.2
    simpa [P, E, δ] using le_of_eq hpair.symm
  have hforall :=
    FiniteProbability.eventProb_forall_ge_one_sub_sum
      P E δ hE
  have hset :
      {hash : CountSketchHash r m |
        ∀ (a b : Fin m), a ≠ b →
          hash ∈ countSketchHashPairNoCollision (r := r) a b} =
        countSketchHashInjectiveEvent (r := r) (m := m) := by
    ext hash
    constructor
    · intro hall
      exact
        (countSketchHash_forall_pairNoCollision_iff_injective hash).mp
          (by
            intro p
            exact hall p.1.1 p.1.2 p.2)
    · intro hinj a b hab
      exact
        (countSketchHash_forall_pairNoCollision_iff_injective hash).mpr
          hinj ⟨(a, b), hab⟩
  simpa [P, E, δ, hset] using hforall




























/-- Readable global injectivity lower bound for the exact CountSketch hash:
the union-bound failure radius is at most `m^2 / r`. -/
theorem countSketchHashProbability_eventProb_injective_ge_one_sub_square_inv
    {r m : ℕ} (hr : 0 < r) :
    1 - (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ ≤
      (countSketchHashProbability (r := r) (m := m) hr).eventProb
        (countSketchHashInjectiveEvent (r := r) (m := m)) := by
  have hbase :=
    countSketchHashProbability_eventProb_injective_ge_one_sub_pair_sum
      (r := r) (m := m) hr
  have hbudget := countSketchDistinctPairBudget_le_square_inv (r := r) (m := m)
  linarith

/-- Collision-free exact hash probability transferred to the computed sparse
CountSketch Gram perturbation event for a fixed exact sign vector.

The probability loss is only the exact hash-injectivity union-bound loss.  All
displayed arithmetic in the event is deterministic floating-point arithmetic
charged by `countSketchSparseGramFullFpPerturbBudget`. -/
theorem countSketchHashProbability_eventProb_flSparseGramDot_rowGram_perturb_ge_one_sub_square_inv
    (fp : FPModel) {r m n : ℕ} (hr : 0 < r)
    (sign : Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hsign : ∀ k : Fin m, sign k ^ 2 = 1)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 - (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ ≤
      (countSketchHashProbability (r := r) (m := m) hr).eventProb
        (countSketchHashFlSparseGramDotRowGramPerturbEvent fp sign A) := by
  classical
  let P := countSketchHashProbability (r := r) (m := m) hr
  have hbase :
      1 - (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ ≤
        P.eventProb (countSketchHashInjectiveEvent (r := r) (m := m)) := by
    simpa [P] using
      countSketchHashProbability_eventProb_injective_ge_one_sub_square_inv
        (r := r) (m := m) hr
  have hsubset :=
    countSketchHashInjectiveEvent_subset_flSparseGramDot_rowGram_perturbEvent
      fp sign A hsign hγm hγr
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Under the full exact CountSketch hash-sign product law, the collision
indicator for two distinct input rows still has mean `1 / r`; the Rademacher
sign coordinate is marginalized exactly. -/
theorem countSketchProbability_expectationReal_pairCollisionIndicator_eq_inv
    {r m : ℕ} (hr : 0 < r) (a b : Fin m) (hab : a ≠ b) :
    (countSketchProbability (r := r) (m := m) hr).expectationReal
      (fun x : CountSketchHash r m × RademacherTrace m =>
        if x.1 a = x.1 b then (1 : ℝ) else 0) = (r : ℝ)⁻¹ := by
  classical
  let P := countSketchHashProbability (r := r) (m := m) hr
  let Q := rademacherTraceProbability m
  calc
    (countSketchProbability (r := r) (m := m) hr).expectationReal
      (fun x : CountSketchHash r m × RademacherTrace m =>
        if x.1 a = x.1 b then (1 : ℝ) else 0)
        =
      (P.prod Q).expectationReal
        (fun x : CountSketchHash r m × RademacherTrace m =>
          (fun hash : CountSketchHash r m =>
            if hash a = hash b then (1 : ℝ) else 0) x.1) := by
            rfl
    _ = P.expectationReal
        (fun hash : CountSketchHash r m =>
          if hash a = hash b then (1 : ℝ) else 0) := by
            exact FiniteProbability.prod_expectationReal_fst_eq P Q
              (fun hash : CountSketchHash r m =>
                if hash a = hash b then (1 : ℝ) else 0)
    _ = (r : ℝ)⁻¹ := by
            simpa [P] using
              countSketchHashProbability_expectationReal_pairCollisionIndicator_eq_inv
                (r := r) (m := m) hr a b hab































/-- Collision-free sparse CountSketch FP Gram endpoint under the full exact
CountSketch law over hashes and Rademacher signs.

All probability construction is exact by project convention.  All displayed
non-probability computation in the event is deterministic floating-point
arithmetic from `fl_countSketchSparseGramDot`: sparse signed products, sparse
bucket accumulation, and rounded Gram dot products. -/
theorem countSketchProbability_eventProb_flSparseGramDot_rowGram_perturb_ge_one_sub_square_inv
    (fp : FPModel) {r m n : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (hγm : gammaValid fp m) (hγr : gammaValid fp r) :
    1 - (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ ≤
      (countSketchProbability (r := r) (m := m) hr).eventProb
        (countSketchFlSparseGramDotRowGramPerturbEvent fp A) := by
  classical
  let P := countSketchHashProbability (r := r) (m := m) hr
  let Q := rademacherTraceProbability m
  let E : Set (CountSketchHash r m) :=
    countSketchHashInjectiveEvent (r := r) (m := m)
  have hbase :
      1 - (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ ≤ P.eventProb E := by
    simpa [P, E] using
      countSketchHashProbability_eventProb_injective_ge_one_sub_square_inv
        (r := r) (m := m) hr
  have hfst :
      1 - (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ ≤
        (P.prod Q).eventProb
          {x : CountSketchHash r m × RademacherTrace m | x.1 ∈ E} := by
    rw [FiniteProbability.prod_eventProb_fst_eq P Q E]
    exact hbase
  have hsubset :
      {x : CountSketchHash r m × RademacherTrace m | x.1 ∈ E} ⊆
        countSketchFlSparseGramDotRowGramPerturbEvent fp A := by
    simpa [E] using
      countSketchProbability_injectiveFst_subset_flSparseGramDot_rowGram_perturbEvent
        fp A hγm hγr
  exact hfst.trans
    (FiniteProbability.eventProb_mono (P.prod Q) hsubset)








































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































namespace ComputedMatrix





































end ComputedMatrix










































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- Floating-point Algorithm 3 outputs
-- ============================================================




































































































































































































































































































































namespace ComputedMatrix































end ComputedMatrix

namespace ComputedPreconditioner








































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end ComputedPreconditioner
















































































































































































































































































































































































































































































































































































































































namespace ComputedPreconditioner




















































































































































































































































































































































































































































































































































































































































































end ComputedPreconditioner



























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
