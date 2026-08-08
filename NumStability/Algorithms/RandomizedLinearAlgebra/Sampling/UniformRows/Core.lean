import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Gram
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.Core

W11 canonical reusable randomized linear algebra destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.UniformRowSampling`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/UniformRowSampling.lean
--
-- Uniform row-sampling foundations for preconditioned RandNLA sketches.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602









namespace NumStability

open scoped BigOperators

/-!
## Uniform row-sampling outer products

After Algorithm 3 preconditions a matrix so that its leverage scores are nearly
uniform, the next randomized sketch samples rows uniformly.  This file contains
the exact one-step rank-one facts for that route.

For an orthonormal-column matrix `U`, uniform row sampling uses the one-step
estimator

`m * U_i*^T U_i*`.

Its expectation is `I`, and a row leverage bound
`leverageScoreProb U i <= B^2` gives the Loewner bound
`m n B^2 I`.  These are the deterministic hypotheses needed before proving the
remaining uniform row-sampling concentration inequality.
-/

-- ============================================================
-- One-step uniform row outer products
-- ============================================================

/-- Uniform one-step row outer-product estimator for `UᵀU`.

When row `i` is drawn uniformly from `m` rows, this is the rank-one sample
`m u_i u_iᵀ`; its expectation is `UᵀU`. -/
noncomputable def uniformRowOuterGramSample {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) (j k : Fin n) : ℝ :=
  (m : ℝ) * U i j * U i k

/-- Uniform one-step row outer-product estimators are symmetric. -/
theorem uniformRowOuterGramSample_symmetric {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) :
    IsSymmetricFiniteMatrix (fun j k : Fin n =>
      uniformRowOuterGramSample U i j k) := by
  intro j k
  unfold uniformRowOuterGramSample
  ring

/-- Quadratic form of one uniform row outer-product estimator. -/
theorem finiteQuadraticForm_uniformRowOuterGramSample_eq {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) (x : Fin n → ℝ) :
    finiteQuadraticForm
        (fun j k : Fin n => uniformRowOuterGramSample U i j k) x =
      (m : ℝ) * (∑ j : Fin n, U i j * x j) ^ 2 := by
  classical
  unfold finiteQuadraticForm finiteMatVec uniformRowOuterGramSample
  calc
    ∑ j : Fin n,
        x j * (∑ k : Fin n, ((m : ℝ) * U i j * U i k) * x k)
        =
      ∑ j : Fin n,
        x j * ((m : ℝ) * U i j * ∑ k : Fin n, U i k * x k) := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ =
      (m : ℝ) * (∑ j : Fin n, U i j * x j) *
        (∑ k : Fin n, U i k * x k) := by
          let S : ℝ := ∑ k : Fin n, U i k * x k
          have hrewrite :
              (∑ j : Fin n,
                x j * ((m : ℝ) * U i j * ∑ k : Fin n, U i k * x k)) =
                ∑ j : Fin n, ((m : ℝ) * (U i j * x j)) * S := by
            apply Finset.sum_congr rfl
            intro j _
            simp [S]
            ring
          rw [hrewrite]
          have hsumS :
              (∑ j : Fin n, ((m : ℝ) * (U i j * x j)) * S) =
                (∑ j : Fin n, (m : ℝ) * (U i j * x j)) * S := by
            rw [Finset.sum_mul]
          have hsumM :
              (∑ j : Fin n, (m : ℝ) * (U i j * x j)) =
                (m : ℝ) * ∑ j : Fin n, U i j * x j := by
            rw [Finset.mul_sum]
          rw [hsumS, hsumM]
    _ = (m : ℝ) * (∑ j : Fin n, U i j * x j) ^ 2 := by
          ring

/-- Uniform one-step row outer-product estimators are positive semidefinite. -/
theorem finitePSD_uniformRowOuterGramSample {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) :
    finitePSD (fun j k : Fin n => uniformRowOuterGramSample U i j k) := by
  intro x
  rw [finiteQuadraticForm_uniformRowOuterGramSample_eq]
  exact mul_nonneg (Nat.cast_nonneg m) (sq_nonneg _)

/-- Uniform row outer-product estimators have expectation `I` for an
orthonormal-column matrix. -/
theorem uniform_rowOuterGramSample_mean_eq_id {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hm : 0 < m) (j k : Fin n) :
    ∑ i : Fin m, (m : ℝ)⁻¹ * uniformRowOuterGramSample U i j k =
      idMatrix n j k := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  calc
    ∑ i : Fin m, (m : ℝ)⁻¹ * uniformRowOuterGramSample U i j k
        = ∑ i : Fin m, U i j * U i k := by
            apply Finset.sum_congr rfl
            intro i _
            unfold uniformRowOuterGramSample
            field_simp [hmR]
    _ = idMatrix n j k := by
            unfold idMatrix
            exact hU j k

/-- A row-norm bound gives a uniform-sampling Loewner bound. -/
theorem uniformRowOuterGramSample_finiteLoewnerLe_of_rowNormSq_le
    {m n : ℕ} (U : Fin m → Fin n → ℝ) (i : Fin m)
    {L : ℝ} (hL : rowNormSq U i ≤ L) :
    finiteLoewnerLe
      (fun j k : Fin n => uniformRowOuterGramSample U i j k)
      (fun j k : Fin n => ((m : ℝ) * L) * finiteIdMatrix j k) := by
  intro x
  rw [finiteQuadraticForm_uniformRowOuterGramSample_eq]
  rw [finiteQuadraticForm_smul_finiteIdMatrix]
  have hinner :
      (∑ j : Fin n, U i j * x j) ^ 2 ≤
        rowNormSq U i * finiteVecNorm2Sq x := by
    simpa [rowNormSq, finiteVecNorm2Sq, vecNorm2Sq] using
      vecInnerProduct_sq_le (fun j : Fin n => U i j) x
  have hrow :
      rowNormSq U i * finiteVecNorm2Sq x ≤ L * finiteVecNorm2Sq x :=
    mul_le_mul_of_nonneg_right hL (finiteVecNorm2Sq_nonneg x)
  have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  calc
    (m : ℝ) * (∑ j : Fin n, U i j * x j) ^ 2
        ≤ (m : ℝ) * (rowNormSq U i * finiteVecNorm2Sq x) :=
          mul_le_mul_of_nonneg_left hinner hm_nonneg
    _ ≤ (m : ℝ) * (L * finiteVecNorm2Sq x) :=
          mul_le_mul_of_nonneg_left hrow hm_nonneg
    _ = (m : ℝ) * L * finiteVecNorm2Sq x := by ring
























-- ============================================================
-- Uniform product law and sample averages
-- ============================================================

/-- One-sample uniform row probability. -/
noncomputable def uniformRowProb {m : ℕ} (_i : RowSample m) : ℝ :=
  (m : ℝ)⁻¹

/-- Uniform row probabilities are nonnegative. -/
theorem uniformRowProb_nonneg {m : ℕ} (i : RowSample m) :
    0 ≤ uniformRowProb i := by
  unfold uniformRowProb
  exact inv_nonneg.mpr (Nat.cast_nonneg m)

/-- Uniform row probabilities sum to one on a nonempty row index type. -/
theorem uniformRowProb_sum_eq_one {m : ℕ} (hm : 0 < m) :
    ∑ i : RowSample m, uniformRowProb i = 1 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  unfold uniformRowProb
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (m : ℝ) * (m : ℝ)⁻¹ = 1
  exact mul_inv_cancel₀ hmR

/-- Uniform row outer-product estimators have expectation `UᵀU` for an
arbitrary input matrix. -/
theorem uniform_rowOuterGramSample_mean_eq_rowGram {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hm : 0 < m) (j k : Fin n) :
    ∑ i : Fin m, uniformRowProb i * uniformRowOuterGramSample U i j k =
      rowGram U j k := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  unfold uniformRowProb uniformRowOuterGramSample rowGram
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hmR]

/-- The one-sample uniform row probability space. -/
noncomputable def uniformRowSampleProbability {m : ℕ}
    (hm : 0 < m) : FiniteProbability (RowSample m) where
  prob := uniformRowProb
  prob_nonneg := uniformRowProb_nonneg
  prob_sum := uniformRowProb_sum_eq_one hm

/-- Product mass for an iid uniform row trace. -/
noncomputable def uniformRowTraceProbMass {m steps : ℕ}
    (samples : RowTrace m steps) : ℝ :=
  ∏ t : Fin steps, uniformRowProb (samples t)

/-- Uniform row-trace masses are nonnegative. -/
theorem uniformRowTraceProbMass_nonneg {m steps : ℕ}
    (samples : RowTrace m steps) :
    0 ≤ uniformRowTraceProbMass samples := by
  unfold uniformRowTraceProbMass
  exact Finset.prod_nonneg fun t _ => uniformRowProb_nonneg (samples t)

/-- Uniform row-trace masses sum to one when the row index type is nonempty. -/
theorem uniformRowTraceProbMass_sum_eq_one {m steps : ℕ}
    (hm : 0 < m) :
    (∑ samples : RowTrace m steps,
      uniformRowTraceProbMass samples) = 1 := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (RowSample m)))
      (f := fun _ x => uniformRowProb x)
  have hleft :
      (∏ _ : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (RowSample m)), uniformRowProb x) = 1 := by
    simp [uniformRowProb_sum_eq_one hm]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (RowSample m))),
        ∏ i, uniformRowProb (x i))
        = ∑ samples : RowTrace m steps,
          uniformRowTraceProbMass samples := by
    simp [uniformRowTraceProbMass, RowTrace]
  rw [← hright, ← hprod]
  exact hleft

/-- The finite probability space for iid uniform row traces. -/
noncomputable def uniformRowTraceProbability {m steps : ℕ}
    (hm : 0 < m) : FiniteProbability (RowTrace m steps) where
  prob := uniformRowTraceProbMass
  prob_nonneg := uniformRowTraceProbMass_nonneg
  prob_sum := uniformRowTraceProbMass_sum_eq_one hm

/-- Under the iid uniform row-trace law, a function of one sampled row has
expectation equal to its one-step uniform expectation. -/
theorem uniformRowTraceProbMass_marginal_one {m steps : ℕ}
    (hm : 0 < m) (t0 : Fin steps) (f : Fin m → ℝ) :
    (∑ samples : RowTrace m steps,
      uniformRowTraceProbMass samples * f (samples t0)) =
      ∑ i : Fin m, uniformRowProb i * f i := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (RowSample m)))
      (f := fun t x =>
        if t = t0 then uniformRowProb x * f x else uniformRowProb x)
  have hleft :
      (∏ t : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (RowSample m)),
          (if t = t0 then uniformRowProb x * f x else uniformRowProb x)) =
        ∑ i : Fin m, uniformRowProb i * f i := by
    simp [uniformRowProb_sum_eq_one hm]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (RowSample m))),
        ∏ i, (if i = t0 then uniformRowProb (x i) * f (x i)
          else uniformRowProb (x i)))
        = ∑ samples : RowTrace m steps,
          uniformRowTraceProbMass samples * f (samples t0) := by
    simp [uniformRowTraceProbMass, RowTrace]
    apply Finset.sum_congr rfl
    intro x _
    have h1 := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t0
      (fun i : Fin steps =>
        if i = t0 then uniformRowProb (x i) * f (x i)
        else uniformRowProb (x i))
      (by intro h; simp at h)
    have h2 := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t0
      (fun i : Fin steps => uniformRowProb (x i))
      (by intro h; simp at h)
    simp at h1 h2
    rw [h1, h2]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t0},
          (if x_1 = t0 then uniformRowProb (x x_1) * f (x x_1)
          else uniformRowProb (x x_1))) =
        ∏ x_1 ∈ Finset.univ \ {t0}, uniformRowProb (x x_1) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hi_ne : i ≠ t0 := by
        simp at hi
        exact hi
      simp [hi_ne]
    rw [herase]
    ring
  rw [← hright, ← hprod]
  exact hleft





















































































































































































































































/-- The exact sampled Gram matrix for iid uniform sampling from `U`, written
as the average of one-step estimators. -/
noncomputable def uniformRowSampleGram {m n s : ℕ}
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m s) :
    Fin n → Fin n → ℝ :=
  fun j k =>
    (∑ t : Fin s, uniformRowOuterGramSample U (samples t) j k) / (s : ℝ)

/-- The uniform sampled Gram error against the identity is the average of the
centered uniform row outer-product estimators. -/
theorem uniformRowSampleGram_sub_finiteIdMatrix_eq_centered_average
    {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hs : 0 < (s : ℝ)) (samples : RowTrace m s) (j k : Fin n) :
    uniformRowSampleGram U samples j k - finiteIdMatrix j k =
      (∑ t : Fin s,
        (uniformRowOuterGramSample U (samples t) j k - finiteIdMatrix j k)) /
          (s : ℝ) := by
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  unfold uniformRowSampleGram
  calc
    (∑ t : Fin s, uniformRowOuterGramSample U (samples t) j k) / (s : ℝ) -
        finiteIdMatrix j k =
      ((∑ t : Fin s, uniformRowOuterGramSample U (samples t) j k) -
          (s : ℝ) * finiteIdMatrix j k) / (s : ℝ) := by
        field_simp [hs_ne]
    _ =
      ((∑ t : Fin s, uniformRowOuterGramSample U (samples t) j k) -
          (∑ _t : Fin s, finiteIdMatrix j k)) / (s : ℝ) := by
        simp
    _ =
      (∑ t : Fin s,
        (uniformRowOuterGramSample U (samples t) j k - finiteIdMatrix j k)) /
          (s : ℝ) := by
        rw [Finset.sum_sub_distrib]

/-- The uniform sampled Gram error against the exact input Gram is the average
of centered uniform row outer-product estimators. -/
theorem uniformRowSampleGram_sub_rowGram_eq_centered_average
    {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hs : 0 < (s : ℝ)) (samples : RowTrace m s) (j k : Fin n) :
    uniformRowSampleGram U samples j k - rowGram U j k =
      (∑ t : Fin s,
        (uniformRowOuterGramSample U (samples t) j k - rowGram U j k)) /
          (s : ℝ) := by
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  unfold uniformRowSampleGram
  calc
    (∑ t : Fin s, uniformRowOuterGramSample U (samples t) j k) / (s : ℝ) -
        rowGram U j k =
      ((∑ t : Fin s, uniformRowOuterGramSample U (samples t) j k) -
          (s : ℝ) * rowGram U j k) / (s : ℝ) := by
        field_simp [hs_ne]
    _ =
      ((∑ t : Fin s, uniformRowOuterGramSample U (samples t) j k) -
          (∑ _t : Fin s, rowGram U j k)) / (s : ℝ) := by
        simp
    _ =
      (∑ t : Fin s,
        (uniformRowOuterGramSample U (samples t) j k - rowGram U j k)) /
          (s : ℝ) := by
        rw [Finset.sum_sub_distrib]













































































































































































/-- Raw second moment of one uniform row outer-product estimator. -/
theorem uniformRowOuterGramSample_row_second_moment {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hm : 0 < m) (i : Fin m) :
    ∑ j : Fin n, ∑ k : Fin n,
      uniformRowProb i * uniformRowOuterGramSample U i j k ^ 2 =
      (m : ℝ) * rowNormSq U i ^ 2 := by
  classical
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  calc
    ∑ j : Fin n, ∑ k : Fin n,
      uniformRowProb i * uniformRowOuterGramSample U i j k ^ 2
        = ∑ j : Fin n, ∑ k : Fin n,
            (m : ℝ) * (U i j ^ 2 * U i k ^ 2) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            unfold uniformRowProb uniformRowOuterGramSample
            field_simp [hmR]
    _ = (m : ℝ) * ∑ j : Fin n, ∑ k : Fin n,
          U i j ^ 2 * U i k ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
    _ = (m : ℝ) * rowNormSq U i ^ 2 := by
          rw [rowNormSq_sq_eq_sum_pair]

/-- Total raw second moment of the uniform row outer-product estimator. -/
theorem uniformRowOuterGramSample_total_second_moment {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hm : 0 < m) :
    ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
      uniformRowProb i * uniformRowOuterGramSample U i j k ^ 2 =
      (m : ℝ) * ∑ i : Fin m, rowNormSq U i ^ 2 := by
  classical
  calc
    ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
      uniformRowProb i * uniformRowOuterGramSample U i j k ^ 2
        = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
            uniformRowProb i * uniformRowOuterGramSample U i j k ^ 2 := by
            calc
              ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
                uniformRowProb i * uniformRowOuterGramSample U i j k ^ 2
                  = ∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin n,
                      uniformRowProb i * uniformRowOuterGramSample U i j k ^ 2 := by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [Finset.sum_comm]
              _ = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
                    uniformRowProb i * uniformRowOuterGramSample U i j k ^ 2 := by
                    rw [Finset.sum_comm]
    _ = ∑ i : Fin m, (m : ℝ) * rowNormSq U i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          exact uniformRowOuterGramSample_row_second_moment U hm i
    _ = (m : ℝ) * ∑ i : Fin m, rowNormSq U i ^ 2 := by
          rw [Finset.mul_sum]

/-- The sum of squared row norms is bounded by the square of the Frobenius
norm squared. -/
theorem rowNormSq_sq_sum_le_frobNormSqRect_sq {m n : ℕ}
    (U : Fin m → Fin n → ℝ) :
    (∑ i : Fin m, rowNormSq U i ^ 2) ≤ frobNormSqRect U ^ 2 := by
  classical
  let S : ℝ := ∑ i : Fin m, rowNormSq U i
  have hpoint : ∀ i : Fin m, rowNormSq U i ^ 2 ≤ rowNormSq U i * S := by
    intro i
    have hle : rowNormSq U i ≤ S := by
      exact Finset.single_le_sum
        (fun k _ => rowNormSq_nonneg U k) (Finset.mem_univ i)
    have hnonneg : 0 ≤ rowNormSq U i := rowNormSq_nonneg U i
    nlinarith [mul_le_mul_of_nonneg_left hle hnonneg]
  calc
    (∑ i : Fin m, rowNormSq U i ^ 2)
        ≤ ∑ i : Fin m, rowNormSq U i * S := by
          exact Finset.sum_le_sum (fun i _ => hpoint i)
    _ = S ^ 2 := by
          rw [← Finset.sum_mul]
          ring
    _ = frobNormSqRect U ^ 2 := by
          simp [S, rowNormSq_sum_eq_frobNormSqRect]


















































































































































































end NumStability
