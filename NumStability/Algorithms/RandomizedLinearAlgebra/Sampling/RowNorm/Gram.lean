import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Gram

W11 canonical reusable randomized linear algebra destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.RowSamplingGram`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/RowSamplingGram.lean
--
-- Gram-matrix expectation and stability consequences for Algorithm 2 of
-- Drineas--Mahoney's CACM RandNLA survey.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602










namespace NumStability

open scoped BigOperators

/-!
## Algorithm 2 Gram analysis

Algorithm 2 returns an `s × n` sampled row sketch `Ã`; the paper measures its
quality through the square Gram matrices `AᵀA` and `ÃᵀÃ`. This file contains
the modular Gram-matrix layer for row sampling:

* exact and floating-point sampled Gram matrices;
* the product-law marginal facts needed for independent row traces;
* elementwise unbiasedness of `ÃᵀÃ` under norm-squared row probabilities;
* the squared-Frobenius second moment and high-probability Markov form of
  equation (5);
* expected and high-probability consequences of an entrywise floating-point
  stability bound on the sampled sketch.

The final floating-point equation (5) corollaries keep the exact sampling
failure probability when the Gram perturbation budget is deterministic; the
generic `δτ` theorem is only a reusable union-bound transfer lemma.
-/

-- ============================================================
-- Gram matrices for exact and sampled row sketches
-- ============================================================

/-- Exact rectangular Gram matrix: `(AᵀA)_{jk} = ∑ᵢ Aᵢⱼ Aᵢₖ`. -/
noncomputable def rowGram {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ i : Fin m, A i j * A i k

/-- Gram matrix of an arbitrary row sketch. -/
noncomputable def rowSketchGram {steps n : ℕ}
    (B : Fin steps → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun j k => ∑ t : Fin steps, B t j * B t k

/-- Quadratic form of a row-sketch Gram matrix as a squared sketch norm. -/
theorem vecNorm2Sq_rowSketch_linearCombination_eq_quadratic_rowSketchGram
    {steps n : ℕ} (B : Fin steps → Fin n → ℝ) (y : Fin n → ℝ) :
    vecNorm2Sq (fun t : Fin steps => ∑ j : Fin n, B t j * y j) =
      ∑ j : Fin n, y j * matMulVec n (rowSketchGram B) y j := by
  classical
  unfold vecNorm2Sq matMulVec rowSketchGram
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Exact sampled Gram matrix `(ÃᵀÃ)` for an Algorithm 2 trace. -/
noncomputable def rowSampleGram {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ t : Fin steps,
    rowSampleSketch s A samples t j * rowSampleSketch s A samples t k

/-- Quadratic form of an exact Algorithm 2 sampled Gram matrix. -/
theorem vecNorm2Sq_rowSampleSketch_linearCombination_eq_quadratic_rowSampleGram
    {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps)
    (y : Fin n → ℝ) :
    vecNorm2Sq
        (fun t : Fin steps => ∑ j : Fin n, rowSampleSketch s A samples t j * y j) =
      ∑ j : Fin n, y j * matMulVec n (rowSampleGram s A samples) y j := by
  simpa [rowSampleGram] using
    vecNorm2Sq_rowSketch_linearCombination_eq_quadratic_rowSketchGram
      (B := rowSampleSketch s A samples) y

/-- Floating-point sampled Gram matrix formed from the rounded sampled sketch. -/
noncomputable def fl_rowSampleGram (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ t : Fin steps,
    fl_rowSampleSketch fp s A samples t j *
      fl_rowSampleSketch fp s A samples t k

/-- Fully floating-point sampled Gram matrix: form the rounded sampled sketch,
    then compute each Gram entry with the library's floating-point dot-product
    algorithm. -/
noncomputable def fl_rowSampleGramDot (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k =>
    fl_dotProduct fp steps
      (fun t => fl_rowSampleSketch fp s A samples t j)
      (fun t => fl_rowSampleSketch fp s A samples t k)

/-- Floating-point sampled Gram matrix formed from a sketch whose row-scale
    denominators were first computed approximately. -/
noncomputable def fl_rowSampleGramWithComputedDen (fp : FPModel)
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (den : Fin m → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  rowSketchGram (fl_rowSampleSketchWithComputedDen fp A den samples)

/-- Fully floating-point sampled Gram matrix for the computed-denominator
    Algorithm 2 path: compute denominators, round row scaling, then compute
    Gram entries with floating-point dot products. -/
noncomputable def fl_rowSampleGramDotWithComputedDen (fp : FPModel)
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (den : Fin m → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k =>
    fl_dotProduct fp steps
      (fun t => fl_rowSampleSketchWithComputedDen fp A den samples t j)
      (fun t => fl_rowSampleSketchWithComputedDen fp A den samples t k)

-- ============================================================
-- Marginals of the independent row trace product law
-- ============================================================



























































































































































































































-- ============================================================
-- Unbiasedness of the sampled Gram matrix
-- ============================================================

/-- One-step cancellation for a row-sampled Gram entry. Rows with zero sampling
    probability are zero rows, so the identity also covers the zero-probability
    case without an extra support predicate. -/
theorem rowSqNormProb_mul_rowSampleIncrement_mul_eq {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (hs : 0 < (s : ℝ)) (i : Fin m) (j k : Fin n) :
    rowSqNormProb A i *
      (rowSampleIncrement s A i j * rowSampleIncrement s A i k) =
      (A i j * A i k) / (s : ℝ) := by
  classical
  by_cases hpzero : rowSqNormProb A i = 0
  · have hrowzero : rowNormSq A i = 0 := by
      unfold rowSqNormProb at hpzero
      rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
      · exact hrow
      · exact False.elim (hden.ne' hdenzero)
    have hij : A i j = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero j
    have hik : A i k = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero k
    simp [hpzero, hij, hik]
  · have hp_nonneg : 0 ≤ rowSqNormProb A i := rowSqNormProb_nonneg A hden i
    have hp_pos : 0 < rowSqNormProb A i :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hp_ne : rowSqNormProb A i ≠ 0 := ne_of_gt hp_pos
    have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
    have hmul_nonneg : 0 ≤ (s : ℝ) * rowSqNormProb A i :=
      mul_nonneg (le_of_lt hs) hp_nonneg
    have hscale_sq : rowSampleScaleDen s A i * rowSampleScaleDen s A i =
        (s : ℝ) * rowSqNormProb A i := by
      unfold rowSampleScaleDen
      exact Real.mul_self_sqrt hmul_nonneg
    unfold rowSampleIncrement
    field_simp [rowSampleScaleDen_ne_zero s A i hs hp_pos, hp_ne, hs_ne]
    rw [sq, hscale_sq]
    ring









































-- ============================================================
-- Scalar second-moment kernel for independent row traces
-- ============================================================





























































































































































/-- Weighted centered second moments are bounded by raw second moments. -/
theorem weighted_centered_sq_le_sq {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (μ : ℝ) (hsum : ∑ i, p i = 1)
    (hμ : μ = ∑ i, p i * f i) :
    ∑ i, p i * (f i - μ) ^ 2 ≤ ∑ i, p i * f i ^ 2 := by
  classical
  have hidentity : ∑ i, p i * (f i - μ) ^ 2 =
      ∑ i, p i * f i ^ 2 - μ ^ 2 := by
    calc
      ∑ i, p i * (f i - μ) ^ 2
          = ∑ i, (p i * f i ^ 2 - 2 * μ * (p i * f i) + p i * μ ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = ∑ i, p i * f i ^ 2 - 2 * μ * (∑ i, p i * f i) +
            μ ^ 2 * (∑ i, p i) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              rw [← Finset.mul_sum]
              have hsum_mu : (∑ x : ι, p x * μ ^ 2) =
                  (∑ x : ι, p x) * μ ^ 2 := by
                rw [Finset.sum_mul]
              rw [hsum_mu]
              ring
      _ = ∑ i, p i * f i ^ 2 - μ ^ 2 := by
              rw [← hμ, hsum]
              ring
  rw [hidentity]
  nlinarith [sq_nonneg μ]

-- ============================================================
-- Row-outer-product specialization of the variance kernel
-- ============================================================

/-- One unscaled row outer-product estimator for a Gram entry:
    `Aᵢⱼ Aᵢₖ / pᵢ`. Its one-step expectation is `(AᵀA)ⱼₖ`. -/
noncomputable def rowOuterGramSample {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j k : Fin n) : ℝ :=
  (A i j * A i k) / rowSqNormProb A i

/-- If a row has zero sampling probability, then its row outer-product
    estimator is the zero matrix. -/
theorem rowOuterGramSample_eq_zero_of_prob_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) (hpzero : rowSqNormProb A i = 0) :
    rowOuterGramSample A i = fun _j _k : Fin n => 0 := by
  ext j k
  have hrowzero : rowNormSq A i = 0 := by
    unfold rowSqNormProb at hpzero
    rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
    · exact hrow
    · exact False.elim (hden.ne' hdenzero)
  have hij : A i j = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero j
  have hik : A i k = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero k
  simp [rowOuterGramSample, hpzero, hij, hik]

/-- Quadratic form of one row outer-product estimator.  On positive-probability
    rows it is the squared row/vector inner product divided by the sampling
    probability. -/
theorem finiteQuadraticForm_rowOuterGramSample_eq_sq_div {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m)
    (hprob : 0 < rowSqNormProb A i) (x : Fin n → ℝ) :
    finiteQuadraticForm (fun j k : Fin n => rowOuterGramSample A i j k) x =
      (∑ j : Fin n, A i j * x j) ^ 2 / rowSqNormProb A i := by
  classical
  have hp_ne : rowSqNormProb A i ≠ 0 := ne_of_gt hprob
  unfold finiteQuadraticForm finiteMatVec rowOuterGramSample
  simp_rw [div_eq_mul_inv]
  calc
    ∑ j : Fin n,
        x j *
          (∑ k : Fin n, (A i j * A i k) * (rowSqNormProb A i)⁻¹ * x k)
        =
      ∑ j : Fin n,
        x j * (A i j * (rowSqNormProb A i)⁻¹ *
          ∑ k : Fin n, A i k * x k) := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ =
      (∑ j : Fin n, A i j * x j) *
        ((rowSqNormProb A i)⁻¹ * ∑ k : Fin n, A i k * x k) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (∑ j : Fin n, A i j * x j) ^ 2 *
        (rowSqNormProb A i)⁻¹ := by ring
    _ = (∑ j : Fin n, A i j * x j) ^ 2 / rowSqNormProb A i := by
          rw [div_eq_mul_inv]

/-- A one-step row outer-product estimator is positive semidefinite. -/
theorem finitePSD_rowOuterGramSample {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) :
    finitePSD (fun j k : Fin n => rowOuterGramSample A i j k) := by
  classical
  intro x
  by_cases hpzero : rowSqNormProb A i = 0
  · have hzero := rowOuterGramSample_eq_zero_of_prob_zero A hden i hpzero
    simp [finiteQuadraticForm, finiteMatVec, hzero]
  · have hp_nonneg : 0 ≤ rowSqNormProb A i := rowSqNormProb_nonneg A hden i
    have hprob : 0 < rowSqNormProb A i :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    rw [finiteQuadraticForm_rowOuterGramSample_eq_sq_div A i hprob x]
    exact div_nonneg (sq_nonneg _) hp_nonneg

/-- The probability weight cancels the `1 / pᵢ` in a row outer-product
    estimator. The zero-probability case is covered because `pᵢ = 0` implies
    row `i` is zero. -/
theorem rowSqNormProb_mul_rowOuterGramSample_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) (j k : Fin n) :
    rowSqNormProb A i * rowOuterGramSample A i j k = A i j * A i k := by
  classical
  by_cases hpzero : rowSqNormProb A i = 0
  · have hrowzero : rowNormSq A i = 0 := by
      unfold rowSqNormProb at hpzero
      rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
      · exact hrow
      · exact False.elim (hden.ne' hdenzero)
    have hij : A i j = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero j
    have hik : A i k = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero k
    simp [rowOuterGramSample, hpzero, hij, hik]
  · unfold rowOuterGramSample
    field_simp [hpzero]

/-- One-step unbiasedness of the row outer-product estimator for a Gram entry. -/
theorem rowOuterGramSample_mean_eq_rowGram {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (j k : Fin n) :
    ∑ i : Fin m, rowSqNormProb A i * rowOuterGramSample A i j k =
      rowGram A j k := by
  unfold rowGram
  apply Finset.sum_congr rfl
  intro i _
  exact rowSqNormProb_mul_rowOuterGramSample_eq A hden i j k

/-- The scaled sketch-row product is the sample-average contribution of the
    unscaled row outer-product estimator. -/
theorem rowSampleIncrement_mul_eq_rowOuterGramSample_div {m n : ℕ}
    (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (i : Fin m) (j k : Fin n) :
    rowSampleIncrement s A i j * rowSampleIncrement s A i k =
      rowOuterGramSample A i j k / (s : ℝ) := by
  classical
  by_cases hpzero : rowSqNormProb A i = 0
  · have hrowzero : rowNormSq A i = 0 := by
      unfold rowSqNormProb at hpzero
      rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
      · exact hrow
      · exact False.elim (hden.ne' hdenzero)
    have hij : A i j = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero j
    have hik : A i k = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero k
    simp [rowSampleIncrement, rowOuterGramSample, hpzero, hij, hik]
  · have hp_nonneg : 0 ≤ rowSqNormProb A i := rowSqNormProb_nonneg A hden i
    have hp_pos : 0 < rowSqNormProb A i :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hp_ne : rowSqNormProb A i ≠ 0 := ne_of_gt hp_pos
    have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
    have hmul_nonneg : 0 ≤ (s : ℝ) * rowSqNormProb A i :=
      mul_nonneg (le_of_lt hs) hp_nonneg
    have hscale_sq : rowSampleScaleDen s A i * rowSampleScaleDen s A i =
        (s : ℝ) * rowSqNormProb A i := by
      unfold rowSampleScaleDen
      exact Real.mul_self_sqrt hmul_nonneg
    unfold rowSampleIncrement rowOuterGramSample
    field_simp [rowSampleScaleDen_ne_zero s A i hs hp_pos, hp_ne, hs_ne]
    rw [sq, hscale_sq]
    ring

/-- Each sampled Gram entry is the average of iid row outer-product
    estimators. -/
theorem rowSampleGram_eq_rowOuterGramSample_average {m n s : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (hs : 0 < (s : ℝ)) (samples : RowTrace m s) (j k : Fin n) :
    rowSampleGram s A samples j k =
      (∑ t : Fin s, rowOuterGramSample A (samples t) j k) / (s : ℝ) := by
  unfold rowSampleGram rowSampleSketch
  calc
    ∑ t : Fin s,
        rowSampleIncrement s A (samples t) j *
          rowSampleIncrement s A (samples t) k
        = ∑ t : Fin s,
            rowOuterGramSample A (samples t) j k / (s : ℝ) := by
          apply Finset.sum_congr rfl
          intro t _
          exact rowSampleIncrement_mul_eq_rowOuterGramSample_div
            s A hden hs (samples t) j k
    _ = (∑ t : Fin s, rowOuterGramSample A (samples t) j k) / (s : ℝ) := by
          simp_rw [div_eq_mul_inv]
          rw [Finset.sum_mul]

/-- The sampled Gram error against the identity is the average of the centered
row outer-product estimators. -/
theorem rowSampleGram_sub_finiteIdMatrix_eq_centered_rowOuterGramSample_average
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (samples : RowTrace m s) (j k : Fin n) :
    rowSampleGram s A samples j k - finiteIdMatrix j k =
      (∑ t : Fin s,
        (rowOuterGramSample A (samples t) j k - finiteIdMatrix j k)) /
          (s : ℝ) := by
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  rw [rowSampleGram_eq_rowOuterGramSample_average A hden hs samples j k]
  calc
    (∑ t : Fin s, rowOuterGramSample A (samples t) j k) / (s : ℝ) -
        finiteIdMatrix j k =
      ((∑ t : Fin s, rowOuterGramSample A (samples t) j k) -
          (s : ℝ) * finiteIdMatrix j k) / (s : ℝ) := by
        field_simp [hs_ne]
    _ =
      ((∑ t : Fin s, rowOuterGramSample A (samples t) j k) -
          (∑ _t : Fin s, finiteIdMatrix j k)) / (s : ℝ) := by
        simp
    _ =
      (∑ t : Fin s,
        (rowOuterGramSample A (samples t) j k - finiteIdMatrix j k)) /
          (s : ℝ) := by
        rw [Finset.sum_sub_distrib]



















/-- Pair-expansion of the squared row norm. -/
theorem rowNormSq_sq_eq_sum_pair {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    rowNormSq A i ^ 2 =
      ∑ j : Fin n, ∑ k : Fin n, A i j ^ 2 * A i k ^ 2 := by
  unfold rowNormSq
  rw [sq, Finset.sum_mul]
  simp_rw [Finset.mul_sum]

/-- Raw second moment of one row outer-product estimator. -/
theorem rowOuterGramSample_row_second_moment {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) :
    ∑ j : Fin n, ∑ k : Fin n,
      rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 =
      rowSqNormProbDen A * rowNormSq A i := by
  classical
  by_cases hpzero : rowSqNormProb A i = 0
  · have hrowzero : rowNormSq A i = 0 := by
      unfold rowSqNormProb at hpzero
      rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
      · exact hrow
      · exact False.elim (hden.ne' hdenzero)
    simp [hpzero, hrowzero]
  · have hp_nonneg : 0 ≤ rowSqNormProb A i := rowSqNormProb_nonneg A hden i
    have hp_pos : 0 < rowSqNormProb A i :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hrow_pos : 0 < rowNormSq A i := by
      unfold rowSqNormProb at hp_pos
      exact (div_pos_iff_of_pos_right hden).mp hp_pos
    have hrow_ne : rowNormSq A i ≠ 0 := ne_of_gt hrow_pos
    have hp_eq : rowSqNormProb A i =
        rowNormSq A i / rowSqNormProbDen A := rfl
    have hpair := rowNormSq_sq_eq_sum_pair A i
    calc
      ∑ j : Fin n, ∑ k : Fin n,
        rowSqNormProb A i * rowOuterGramSample A i j k ^ 2
          = ∑ j : Fin n, ∑ k : Fin n,
              (A i j ^ 2 * A i k ^ 2) / rowSqNormProb A i := by
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro k _
              unfold rowOuterGramSample
              field_simp [hpzero]
      _ = (∑ j : Fin n, ∑ k : Fin n, A i j ^ 2 * A i k ^ 2) /
            rowSqNormProb A i := by
              simp_rw [div_eq_mul_inv]
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
      _ = rowNormSq A i ^ 2 / rowSqNormProb A i := by rw [← hpair]
      _ = rowSqNormProbDen A * rowNormSq A i := by
              rw [hp_eq]
              field_simp [hrow_ne, hden.ne']

/-- Total raw second moment of the row outer-product estimator. -/
theorem rowOuterGramSample_total_second_moment {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A) :
    ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
      rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 =
      rowSqNormProbDen A ^ 2 := by
  classical
  calc
    ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
      rowSqNormProb A i * rowOuterGramSample A i j k ^ 2
        = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
            rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 := by
            calc
              ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
                rowSqNormProb A i * rowOuterGramSample A i j k ^ 2
                  = ∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin n,
                      rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 := by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [Finset.sum_comm]
              _ = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
                    rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 := by
                    rw [Finset.sum_comm]
    _ = ∑ i : Fin m, rowSqNormProbDen A * rowNormSq A i := by
            apply Finset.sum_congr rfl
            intro i _
            exact rowOuterGramSample_row_second_moment A hden i
    _ = rowSqNormProbDen A * ∑ i : Fin m, rowNormSq A i := by
            rw [Finset.mul_sum]
    _ = rowSqNormProbDen A ^ 2 := by
            rw [rowNormSq_sum_eq_frobNormSqRect A]
            unfold rowSqNormProbDen
            ring
























































































































-- ============================================================
-- Floating-point perturbation of the sampled Gram matrix
-- ============================================================

/-- Deterministic entrywise Gram perturbation from relative entrywise sampled
    sketch errors. If each sampled sketch entry has relative error at most
    `u`, then each Gram entry changes by at most
    `(2u + u²) ∑ₜ |B_{tj}| |B_{tk}|`. -/
theorem rowSampleGram_entry_error_bound_of_entrywise
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j,
      |Bhat t j - rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * u)
    (j k : Fin n) :
    |(∑ t : Fin steps, Bhat t j * Bhat t k) -
      rowSampleGram s A samples j k| ≤
      (2 * u + u ^ 2) *
        ∑ t : Fin steps,
          |rowSampleSketch s A samples t j| *
            |rowSampleSketch s A samples t k| := by
  classical
  unfold rowSampleGram
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t : Fin steps,
        (Bhat t j * Bhat t k -
          rowSampleSketch s A samples t j *
            rowSampleSketch s A samples t k)|
        ≤ ∑ t : Fin steps,
            |Bhat t j * Bhat t k -
              rowSampleSketch s A samples t j *
                rowSampleSketch s A samples t k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Fin steps,
          (2 * u + u ^ 2) *
            (|rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k|) := by
          apply Finset.sum_le_sum
          intro t _
          let bj := rowSampleSketch s A samples t j
          let bk := rowSampleSketch s A samples t k
          let ej := Bhat t j - bj
          let ek := Bhat t k - bk
          have hj : |ej| ≤ |bj| * u := hentry t j
          have hk : |ek| ≤ |bk| * u := hentry t k
          have hBj : Bhat t j = bj + ej := by
            simp [ej, bj]
          have hBk : Bhat t k = bk + ek := by
            simp [ek, bk]
          have hdecomp :
              Bhat t j * Bhat t k - bj * bk =
                ej * bk + bj * ek + ej * ek := by
            rw [hBj, hBk]
            ring
          have hnonneg_bj : 0 ≤ |bj| := abs_nonneg bj
          have hnonneg_bk : 0 ≤ |bk| := abs_nonneg bk
          have hnonneg_u2 : 0 ≤ u ^ 2 := sq_nonneg u
          calc
            |Bhat t j * Bhat t k - bj * bk|
                = |ej * bk + bj * ek + ej * ek| := by rw [hdecomp]
            _ ≤ |ej * bk| + |bj * ek| + |ej * ek| := by
                exact abs_add_three _ _ _
            _ = |ej| * |bk| + |bj| * |ek| + |ej| * |ek| := by
                rw [abs_mul, abs_mul, abs_mul]
            _ ≤ (|bj| * u) * |bk| + |bj| * (|bk| * u) +
                  (|bj| * u) * (|bk| * u) := by
                gcongr
            _ = (2 * u + u ^ 2) * (|bj| * |bk|) := by ring
    _ = (2 * u + u ^ 2) *
          ∑ t : Fin steps,
            |rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k| := by
          rw [Finset.mul_sum]

/-- Frobenius-norm Gram perturbation bound induced by entrywise sampled-sketch
    stability. -/
theorem rowSampleGram_frob_error_bound_of_entrywise
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j,
      |Bhat t j - rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * u) :
    frobNorm
      (fun j k =>
        rowSketchGram Bhat j k - rowSampleGram s A samples j k) ≤
      frobNorm
        (fun j k =>
          (2 * u + u ^ 2) *
            ∑ t : Fin steps,
              |rowSampleSketch s A samples t j| *
                |rowSampleSketch s A samples t k|) := by
  classical
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply mul_nonneg
    · nlinarith [hu, sq_nonneg u]
    · apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j k
    unfold rowSketchGram
    exact rowSampleGram_entry_error_bound_of_entrywise
      s A samples Bhat u hu hentry j k

/-- Generic deterministic entrywise Gram perturbation from relative row-sketch
    entry errors. If `Bhat` is componentwise within relative error `u` of an
    exact sketch `B`, then each Gram entry changes by at most
    `(2u + u²) ∑ₜ |B_{tj}| |B_{tk}|`. -/
theorem rowSketchGram_entry_error_bound_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u)
    (j k : Fin n) :
    |rowSketchGram Bhat j k - rowSketchGram B j k| ≤
      (2 * u + u ^ 2) *
        ∑ t : Fin steps, |B t j| * |B t k| := by
  classical
  unfold rowSketchGram
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t : Fin steps, (Bhat t j * Bhat t k - B t j * B t k)|
        ≤ ∑ t : Fin steps,
            |Bhat t j * Bhat t k - B t j * B t k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Fin steps,
          (2 * u + u ^ 2) * (|B t j| * |B t k|) := by
          apply Finset.sum_le_sum
          intro t _
          let bj := B t j
          let bk := B t k
          let ej := Bhat t j - bj
          let ek := Bhat t k - bk
          have hj : |ej| ≤ |bj| * u := hentry t j
          have hk : |ek| ≤ |bk| * u := hentry t k
          have hBj : Bhat t j = bj + ej := by
            simp [ej, bj]
          have hBk : Bhat t k = bk + ek := by
            simp [ek, bk]
          have hdecomp :
              Bhat t j * Bhat t k - bj * bk =
                ej * bk + bj * ek + ej * ek := by
            rw [hBj, hBk]
            ring
          calc
            |Bhat t j * Bhat t k - bj * bk|
                = |ej * bk + bj * ek + ej * ek| := by rw [hdecomp]
            _ ≤ |ej * bk| + |bj * ek| + |ej * ek| := by
                exact abs_add_three _ _ _
            _ = |ej| * |bk| + |bj| * |ek| + |ej| * |ek| := by
                rw [abs_mul, abs_mul, abs_mul]
            _ ≤ (|bj| * u) * |bk| + |bj| * (|bk| * u) +
                  (|bj| * u) * (|bk| * u) := by
                gcongr
            _ = (2 * u + u ^ 2) * (|bj| * |bk|) := by ring
    _ = (2 * u + u ^ 2) *
          ∑ t : Fin steps, |B t j| * |B t k| := by
          rw [Finset.mul_sum]

/-- Generic Frobenius-norm Gram perturbation bound induced by componentwise
    relative stability of an arbitrary row sketch. -/
theorem rowSketchGram_frob_error_bound_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u) :
    frobNorm
      (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k) ≤
      frobNorm
        (fun j k =>
          (2 * u + u ^ 2) *
            ∑ t : Fin steps, |B t j| * |B t k|) := by
  classical
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply mul_nonneg
    · nlinarith [hu, sq_nonneg u]
    · apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j k
    exact rowSketchGram_entry_error_bound_of_entrywise
      B Bhat u hu hentry j k

/-- Generic deterministic entrywise Gram perturbation from absolute row-sketch
    entry errors.  If `Bhat` is within an absolute error matrix `E` of `B`,
    then the Gram perturbation is bounded by the visible mixed exact/computed
    row products. -/
theorem rowSketchGram_entry_abs_error_bound_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (_hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j)
    (j k : Fin n) :
    |rowSketchGram Bhat j k - rowSketchGram B j k| ≤
      ∑ t : Fin steps,
        (E t j * |Bhat t k| + |B t j| * E t k) := by
  classical
  unfold rowSketchGram
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t : Fin steps, (Bhat t j * Bhat t k - B t j * B t k)|
        ≤ ∑ t : Fin steps,
            |Bhat t j * Bhat t k - B t j * B t k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Fin steps,
          (E t j * |Bhat t k| + |B t j| * E t k) := by
          apply Finset.sum_le_sum
          intro t _
          let ej := Bhat t j - B t j
          let ek := Bhat t k - B t k
          have hj : |ej| ≤ E t j := hentry t j
          have hk : |ek| ≤ E t k := hentry t k
          have hBj : Bhat t j = B t j + ej := by
            simp [ej]
          have hBk : Bhat t k = B t k + ek := by
            simp [ek]
          have hdecomp :
              Bhat t j * Bhat t k - B t j * B t k =
                ej * Bhat t k + B t j * ek := by
            rw [hBj, hBk]
            ring
          calc
            |Bhat t j * Bhat t k - B t j * B t k|
                = |ej * Bhat t k + B t j * ek| := by rw [hdecomp]
            _ ≤ |ej * Bhat t k| + |B t j * ek| := abs_add_le _ _
            _ = |ej| * |Bhat t k| + |B t j| * |ek| := by
                rw [abs_mul, abs_mul]
            _ ≤ E t j * |Bhat t k| + |B t j| * E t k := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right hj (abs_nonneg _))
                  (mul_le_mul_of_nonneg_left hk (abs_nonneg _))

/-- Frobenius-norm Gram perturbation bound induced by absolute entrywise
    row-sketch errors. -/
theorem rowSketchGram_frob_abs_error_bound_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j) :
    frobNorm
      (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k) ≤
      frobNorm
        (fun j k =>
          ∑ t : Fin steps,
            (E t j * |Bhat t k| + |B t j| * E t k)) := by
  classical
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply Finset.sum_nonneg
    intro t _
    exact add_nonneg
      (mul_nonneg (hE_nonneg t j) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (hE_nonneg t k))
  · intro j k
    exact rowSketchGram_entry_abs_error_bound_of_entrywise
      B Bhat E hE_nonneg hentry j k

/-- A componentwise relative perturbation bounds the absolute value of each
    perturbed sketch entry. -/
theorem rowSketch_abs_perturbed_le
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (_hu : 0 ≤ u)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u)
    (t : Fin steps) (j : Fin n) :
    |Bhat t j| ≤ (1 + u) * |B t j| := by
  calc
    |Bhat t j|
        = |(Bhat t j - B t j) + B t j| := by
            congr 1
            ring
    _ ≤ |Bhat t j - B t j| + |B t j| := abs_add_le _ _
    _ ≤ |B t j| * u + |B t j| := by
            exact add_le_add (hentry t j) le_rfl
    _ = (1 + u) * |B t j| := by ring

/-- Product form of `rowSketch_abs_perturbed_le`. -/
theorem rowSketch_abs_perturbed_mul_le
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u)
    (t : Fin steps) (j k : Fin n) :
    |Bhat t j| * |Bhat t k| ≤
      (1 + u) ^ 2 * (|B t j| * |B t k|) := by
  have hj := rowSketch_abs_perturbed_le B Bhat u hu hentry t j
  have hk := rowSketch_abs_perturbed_le B Bhat u hu hentry t k
  have hfac_nonneg : 0 ≤ 1 + u := by linarith
  have hbj_nonneg : 0 ≤ (1 + u) * |B t j| :=
    mul_nonneg hfac_nonneg (abs_nonneg _)
  calc
    |Bhat t j| * |Bhat t k|
        ≤ ((1 + u) * |B t j|) * ((1 + u) * |B t k|) := by
            exact mul_le_mul hj hk (abs_nonneg _) hbj_nonneg
    _ = (1 + u) ^ 2 * (|B t j| * |B t k|) := by ring

/-- Sum form of `rowSketch_abs_perturbed_mul_le`. -/
theorem rowSketch_abs_perturbed_mul_sum_le
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u)
    (j k : Fin n) :
    (∑ t : Fin steps, |Bhat t j| * |Bhat t k|) ≤
      (1 + u) ^ 2 * ∑ t : Fin steps, |B t j| * |B t k| := by
  calc
    (∑ t : Fin steps, |Bhat t j| * |Bhat t k|)
        ≤ ∑ t : Fin steps,
            (1 + u) ^ 2 * (|B t j| * |B t k|) := by
            apply Finset.sum_le_sum
            intro t _
            exact rowSketch_abs_perturbed_mul_le B Bhat u hu hentry t j k
    _ = (1 + u) ^ 2 * ∑ t : Fin steps, |B t j| * |B t k| := by
            rw [Finset.mul_sum]

/-- An absolute entrywise perturbation bounds the absolute value of each
    perturbed sketch entry. -/
theorem rowSketch_abs_perturbed_le_of_abs_error
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (_hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j)
    (t : Fin steps) (j : Fin n) :
    |Bhat t j| ≤ |B t j| + E t j := by
  calc
    |Bhat t j|
        = |(Bhat t j - B t j) + B t j| := by
            congr 1
            ring
    _ ≤ |Bhat t j - B t j| + |B t j| := abs_add_le _ _
    _ ≤ E t j + |B t j| := by
            exact add_le_add (hentry t j) le_rfl
    _ = |B t j| + E t j := by ring

/-- Product form of `rowSketch_abs_perturbed_le_of_abs_error`. -/
theorem rowSketch_abs_perturbed_mul_le_of_abs_error
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j)
    (t : Fin steps) (j k : Fin n) :
    |Bhat t j| * |Bhat t k| ≤
      (|B t j| + E t j) * (|B t k| + E t k) := by
  have hj :=
    rowSketch_abs_perturbed_le_of_abs_error
      B Bhat E hE_nonneg hentry t j
  have hk :=
    rowSketch_abs_perturbed_le_of_abs_error
      B Bhat E hE_nonneg hentry t k
  have hright_nonneg : 0 ≤ |B t j| + E t j :=
    add_nonneg (abs_nonneg _) (hE_nonneg t j)
  exact mul_le_mul hj hk (abs_nonneg _) hright_nonneg

/-- Sum form of `rowSketch_abs_perturbed_mul_le_of_abs_error`. -/
theorem rowSketch_abs_perturbed_mul_sum_le_of_abs_error
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j)
    (j k : Fin n) :
    (∑ t : Fin steps, |Bhat t j| * |Bhat t k|) ≤
      ∑ t : Fin steps,
        (|B t j| + E t j) * (|B t k| + E t k) := by
  apply Finset.sum_le_sum
  intro t _
  exact rowSketch_abs_perturbed_mul_le_of_abs_error
    B Bhat E hE_nonneg hentry t j k

/-- Absolute-entry Gram perturbation bound with no computed-entry term left in
    the right-hand side. -/
theorem rowSketchGram_entry_abs_error_bound_exact_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j)
    (j k : Fin n) :
    |rowSketchGram Bhat j k - rowSketchGram B j k| ≤
      ∑ t : Fin steps,
        (E t j * |B t k| + |B t j| * E t k + E t j * E t k) := by
  classical
  unfold rowSketchGram
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t : Fin steps, (Bhat t j * Bhat t k - B t j * B t k)|
        ≤ ∑ t : Fin steps,
            |Bhat t j * Bhat t k - B t j * B t k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Fin steps,
          (E t j * |B t k| + |B t j| * E t k +
            E t j * E t k) := by
          apply Finset.sum_le_sum
          intro t _
          let ej := Bhat t j - B t j
          let ek := Bhat t k - B t k
          have hj : |ej| ≤ E t j := hentry t j
          have hk : |ek| ≤ E t k := hentry t k
          have hBj : Bhat t j = B t j + ej := by
            simp [ej]
          have hBk : Bhat t k = B t k + ek := by
            simp [ek]
          have hdecomp :
              Bhat t j * Bhat t k - B t j * B t k =
                ej * B t k + B t j * ek + ej * ek := by
            rw [hBj, hBk]
            ring
          have h1 : |ej| * |B t k| ≤ E t j * |B t k| :=
            mul_le_mul_of_nonneg_right hj (abs_nonneg _)
          have h2 : |B t j| * |ek| ≤ |B t j| * E t k :=
            mul_le_mul_of_nonneg_left hk (abs_nonneg _)
          have h3 : |ej| * |ek| ≤ E t j * E t k :=
            mul_le_mul hj hk (abs_nonneg _) (hE_nonneg t j)
          calc
            |Bhat t j * Bhat t k - B t j * B t k|
                = |ej * B t k + B t j * ek + ej * ek| := by
                    rw [hdecomp]
            _ ≤ |ej * B t k| + |B t j * ek| + |ej * ek| := by
                    exact abs_add_three _ _ _
            _ = |ej| * |B t k| + |B t j| * |ek| +
                  |ej| * |ek| := by
                    rw [abs_mul, abs_mul, abs_mul]
            _ ≤ E t j * |B t k| + |B t j| * E t k +
                  E t j * E t k := by
                    linarith

/-- Frobenius-norm Gram perturbation bound from absolute entrywise sketch
    errors, with a right-hand side depending only on the exact sketch and the
    explicit absolute error matrix. -/
theorem rowSketchGram_frob_abs_error_bound_exact_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j) :
    frobNorm
      (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k) ≤
      frobNorm
        (fun j k =>
          ∑ t : Fin steps,
            (E t j * |B t k| + |B t j| * E t k +
              E t j * E t k)) := by
  classical
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply Finset.sum_nonneg
    intro t _
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (hE_nonneg t j) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (hE_nonneg t k)))
      (mul_nonneg (hE_nonneg t j) (hE_nonneg t k))
  · intro j k
    exact rowSketchGram_entry_abs_error_bound_exact_of_entrywise
      B Bhat E hE_nonneg hentry j k

/-- Fully floating-point Gram of an already-computed row sketch: each entry is
    evaluated with the repository floating-point dot-product algorithm. -/
noncomputable def fl_rowSketchGramDot (fp : FPModel)
    {steps n : ℕ} (Bhat : Fin steps → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k =>
    fl_dotProduct fp steps (fun t => Bhat t j) (fun t => Bhat t k)

/-- Exact-only dot-product roundoff budget for a computed row sketch whose
    entries are within the explicit absolute error matrix `E` of `B`. -/
noncomputable def rowSketchGramDotRoundoffExactBudget
    (fp : FPModel) {steps n : ℕ}
    (B : Fin steps → Fin n → ℝ) (E : Fin steps → Fin n → ℝ) : ℝ :=
  frobNorm
    (fun j k : Fin n =>
      gamma fp steps *
        ∑ t : Fin steps,
          (|B t j| + E t j) * (|B t k| + E t k))

/-- Exact-only sketch-formation perturbation budget for a Gram matrix built
    from a computed row sketch. -/
noncomputable def rowSketchGramAbsPerturbExactBudget
    {steps n : ℕ}
    (B : Fin steps → Fin n → ℝ) (E : Fin steps → Fin n → ℝ) : ℝ :=
  frobNorm
    (fun j k : Fin n =>
      ∑ t : Fin steps,
        (E t j * |B t k| + |B t j| * E t k + E t j * E t k))

/-- Total exact-only floating-point perturbation budget for the Gram of an
    already-computed row sketch.  The first term charges rounded dot products;
    the second charges the perturbation from exact sketch `B` to computed
    sketch `Bhat` through its explicit entrywise radius `E`. -/
noncomputable def rowSketchGramFullAbsFpExactBudget
    (fp : FPModel) {steps n : ℕ}
    (B : Fin steps → Fin n → ℝ) (E : Fin steps → Fin n → ℝ) : ℝ :=
  rowSketchGramDotRoundoffExactBudget fp B E +
    rowSketchGramAbsPerturbExactBudget B E

/-- Dot-product roundoff bound for an already-computed row sketch, stated with
    a right-hand side that depends only on the exact sketch and the explicit
    absolute entrywise error matrix. -/
theorem fl_rowSketchGramDot_roundoff_bound_of_abs_error
    (fp : FPModel) {steps n : ℕ}
    (B Bhat : Fin steps → Fin n → ℝ) (E : Fin steps → Fin n → ℝ)
    (hγ : gammaValid fp steps)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j) :
    frobNorm
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k) ≤
      rowSketchGramDotRoundoffExactBudget fp B E := by
  classical
  have hγ_nonneg : 0 ≤ gamma fp steps := gamma_nonneg fp hγ
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply mul_nonneg hγ_nonneg
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg
      (add_nonneg (abs_nonneg _) (hE_nonneg t j))
      (add_nonneg (abs_nonneg _) (hE_nonneg t k))
  · intro j k
    have hdot :=
      dotProduct_error_bound fp steps
        (fun t => Bhat t j) (fun t => Bhat t k) hγ
    have hsum :=
      rowSketch_abs_perturbed_mul_sum_le_of_abs_error
        B Bhat E hE_nonneg hentry j k
    calc
      |fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k|
          ≤ gamma fp steps *
              ∑ t : Fin steps, |Bhat t j| * |Bhat t k| := by
              simpa [fl_rowSketchGramDot, rowSketchGram] using hdot
      _ ≤ gamma fp steps *
            ∑ t : Fin steps,
              (|B t j| + E t j) * (|B t k| + E t k) := by
              exact mul_le_mul_of_nonneg_left hsum hγ_nonneg

/-- Fully floating-point Gram perturbation for an already-computed row sketch,
    with every non-probability computation charged by an explicit exact-only
    budget. -/
theorem fl_rowSketchGramDot_abs_perturb_bound_exact
    (fp : FPModel) {steps n : ℕ}
    (B Bhat : Fin steps → Fin n → ℝ) (E : Fin steps → Fin n → ℝ)
    (hγ : gammaValid fp steps)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j) :
    frobNorm
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram B j k) ≤
      rowSketchGramFullAbsFpExactBudget fp B E := by
  classical
  have hdot :=
    fl_rowSketchGramDot_roundoff_bound_of_abs_error
      fp B Bhat E hγ hE_nonneg hentry
  have hsketch :=
    rowSketchGram_frob_abs_error_bound_exact_of_entrywise
      B Bhat E hE_nonneg hentry
  have hsplit :
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram B j k) =
      (fun j k =>
        (fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k) +
          (rowSketchGram Bhat j k - rowSketchGram B j k)) := by
    funext j k
    ring
  have htri :=
    frobNorm_add_le
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k)
      (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k)
  calc
    frobNorm
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram B j k)
        =
      frobNorm
        (fun j k =>
          (fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k) +
            (rowSketchGram Bhat j k - rowSketchGram B j k)) := by
          rw [hsplit]
    _ ≤
        frobNorm
          (fun j k =>
            fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k) +
        frobNorm
          (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k) :=
          htri
    _ ≤ rowSketchGramDotRoundoffExactBudget fp B E +
        rowSketchGramAbsPerturbExactBudget B E :=
          add_le_add hdot hsketch
    _ = rowSketchGramFullAbsFpExactBudget fp B E := by
          rfl

/-- Dot-product computation error for the Gram matrix, reusing the library's
    `dotProduct_error_bound`. The only local work here is translating the
    entrywise sketch perturbation into a bound on the dot-product inputs. -/
theorem rowSketchGram_dot_frob_error_bound_of_entrywise
    (fp : FPModel) {steps n : ℕ}
    (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hγ : gammaValid fp steps)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u) :
    frobNorm
      (fun j k =>
        fl_dotProduct fp steps (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k) ≤
      frobNorm
        (fun j k =>
          gamma fp steps * (1 + u) ^ 2 *
            ∑ t : Fin steps, |B t j| * |B t k|) := by
  classical
  have hγ_nonneg : 0 ≤ gamma fp steps := gamma_nonneg fp hγ
  have hfac_nonneg : 0 ≤ (1 + u) ^ 2 := sq_nonneg (1 + u)
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply mul_nonneg
    · exact mul_nonneg hγ_nonneg hfac_nonneg
    · apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j k
    have hdot :=
      dotProduct_error_bound fp steps
        (fun t => Bhat t j) (fun t => Bhat t k) hγ
    have hsum :=
      rowSketch_abs_perturbed_mul_sum_le B Bhat u hu hentry j k
    calc
      |fl_dotProduct fp steps (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k|
          ≤ gamma fp steps *
              ∑ t : Fin steps, |Bhat t j| * |Bhat t k| := by
              simpa [rowSketchGram] using hdot
      _ ≤ gamma fp steps *
            ((1 + u) ^ 2 * ∑ t : Fin steps, |B t j| * |B t k|) := by
              exact mul_le_mul_of_nonneg_left hsum hγ_nonneg
      _ = gamma fp steps * (1 + u) ^ 2 *
            ∑ t : Fin steps, |B t j| * |B t k| := by ring

/-- The row outer-product estimator has magnitude at most `||A||_F²` in each
    entry. -/
theorem abs_rowOuterGramSample_le_den {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) (j k : Fin n) :
    |rowOuterGramSample A i j k| ≤ rowSqNormProbDen A := by
  classical
  by_cases hpzero : rowSqNormProb A i = 0
  · have hrowzero : rowNormSq A i = 0 := by
      unfold rowSqNormProb at hpzero
      rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
      · exact hrow
      · exact False.elim (hden.ne' hdenzero)
    have hij : A i j = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero j
    have hik : A i k = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero k
    simp [rowOuterGramSample, hpzero, hij, hik, le_of_lt hden]
  · have hp_nonneg : 0 ≤ rowSqNormProb A i := rowSqNormProb_nonneg A hden i
    have hp_pos : 0 < rowSqNormProb A i :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hrow_pos : 0 < rowNormSq A i := by
      unfold rowSqNormProb at hp_pos
      exact (div_pos_iff_of_pos_right hden).mp hp_pos
    have hrow_ne : rowNormSq A i ≠ 0 := ne_of_gt hrow_pos
    have hj_le : A i j ^ 2 ≤ rowNormSq A i := by
      unfold rowNormSq
      exact Finset.single_le_sum
        (fun x _ => sq_nonneg (A i x)) (Finset.mem_univ j)
    have hk_le : A i k ^ 2 ≤ rowNormSq A i := by
      unfold rowNormSq
      exact Finset.single_le_sum
        (fun x _ => sq_nonneg (A i x)) (Finset.mem_univ k)
    have htwo :
        2 * (|A i j| * |A i k|) ≤ A i j ^ 2 + A i k ^ 2 := by
      have hsq : 0 ≤ (|A i j| - |A i k|) ^ 2 := sq_nonneg _
      nlinarith [sq_abs (A i j), sq_abs (A i k)]
    have hsum : A i j ^ 2 + A i k ^ 2 ≤ 2 * rowNormSq A i := by
      nlinarith
    have hprod : |A i j * A i k| ≤ rowNormSq A i := by
      rw [abs_mul]
      nlinarith
    have hp_eq : rowSqNormProb A i =
        rowNormSq A i / rowSqNormProbDen A := rfl
    calc
      |rowOuterGramSample A i j k|
          = |A i j * A i k| / rowSqNormProb A i := by
              unfold rowOuterGramSample
              rw [abs_div, abs_of_nonneg hp_nonneg]
      _ ≤ rowNormSq A i / rowSqNormProb A i := by
              exact div_le_div_of_nonneg_right hprod hp_nonneg
      _ = rowSqNormProbDen A := by
              rw [hp_eq]
              field_simp [hrow_ne, hden.ne']

/-- A single exact sampled-row contribution to `ÃᵀÃ` has absolute product at
    most `||A||_F² / s`. -/
theorem rowSampleSketch_abs_mul_le_den_div_steps {m n s : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (hs : 0 < (s : ℝ)) (samples : RowTrace m s)
    (t : Fin s) (j k : Fin n) :
    |rowSampleSketch s A samples t j| *
        |rowSampleSketch s A samples t k| ≤
      rowSqNormProbDen A / (s : ℝ) := by
  classical
  have hprod :=
    rowSampleIncrement_mul_eq_rowOuterGramSample_div
      s A hden hs (samples t) j k
  have habs :
      |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k| =
        |rowOuterGramSample A (samples t) j k| / (s : ℝ) := by
    unfold rowSampleSketch
    rw [← abs_mul, hprod, abs_div, abs_of_nonneg (le_of_lt hs)]
  rw [habs]
  exact div_le_div_of_nonneg_right
    (abs_rowOuterGramSample_le_den A hden (samples t) j k) (le_of_lt hs)

/-- The entrywise absolute-product budget in the sampled Gram perturbation is
    bounded uniformly by `||A||_F²`. -/
theorem rowSampleSketch_abs_mul_sum_le_den {m n s : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (hs : 0 < (s : ℝ)) (samples : RowTrace m s)
    (j k : Fin n) :
    (∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|) ≤
      rowSqNormProbDen A := by
  classical
  calc
    (∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|)
        ≤ ∑ _t : Fin s, rowSqNormProbDen A / (s : ℝ) := by
            apply Finset.sum_le_sum
            intro t _
            exact rowSampleSketch_abs_mul_le_den_div_steps
              A hden hs samples t j k
    _ = rowSqNormProbDen A := by
            rw [Finset.sum_const]
            simp
            field_simp [ne_of_gt hs]

/-- Explicit deterministic floating-point Gram perturbation budget for
    Algorithm 2. This is a worst-case bound over the support of the row sampler:
    every Gram entry can change by at most
    `(2u + u²) ||A||_F²`, and the Frobenius norm packages those entrywise
    bounds. -/
noncomputable def rowSampleGramFpPerturbBudget (fp : FPModel)
    {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ :=
  frobNorm (fun _j _k : Fin n => (2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A)

/-- Explicit deterministic budget for computing each already-rounded sampled
    Gram entry with the library dot-product algorithm. -/
noncomputable def rowSampleGramDotProductBudget (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ) : ℝ :=
  frobNorm
    (fun _j _k : Fin n =>
      gamma fp s * (1 + fp.u) ^ 2 * rowSqNormProbDen A)

/-- Closed form of the row-scaling perturbation budget, exposing the implicit
    dependence on the number `n` of columns/Gram rows. -/
theorem rowSampleGramFpPerturbBudget_eq_nat_mul (fp : FPModel)
    {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    rowSampleGramFpPerturbBudget fp A =
      (n : ℝ) * ((2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A) := by
  have hC : 0 ≤ (2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A := by
    have hu : 0 ≤ 2 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg, sq_nonneg fp.u]
    have hden : 0 ≤ rowSqNormProbDen A := by
      unfold rowSqNormProbDen
      exact frobNormSqRect_nonneg A
    exact mul_nonneg hu hden
  unfold rowSampleGramFpPerturbBudget
  exact frobNorm_const hC

/-- Closed form of the dot-product perturbation budget, exposing the implicit
    dependence on the number `n` of columns/Gram rows. -/
theorem rowSampleGramDotProductBudget_eq_nat_mul (fp : FPModel)
    {m n : ℕ} {s : ℕ} (A : Fin m → Fin n → ℝ)
    (hγ : gammaValid fp s) :
    rowSampleGramDotProductBudget fp s A =
      (n : ℝ) *
        (gamma fp s * (1 + fp.u) ^ 2 * rowSqNormProbDen A) := by
  have hC :
      0 ≤ gamma fp s * (1 + fp.u) ^ 2 * rowSqNormProbDen A := by
    have hleft : 0 ≤ gamma fp s * (1 + fp.u) ^ 2 :=
      mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + fp.u))
    have hden : 0 ≤ rowSqNormProbDen A := by
      unfold rowSqNormProbDen
      exact frobNormSqRect_nonneg A
    exact mul_nonneg hleft hden
  unfold rowSampleGramDotProductBudget
  exact frobNorm_const hC

/-- The deterministic Gram perturbation matrix obtained from entrywise sampled
    sketch stability is bounded by the explicit worst-case budget. -/
theorem rowSampleGram_perturb_budget_le_explicit (fp : FPModel)
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (samples : RowTrace m s) :
    frobNorm
      (fun j k =>
        (2 * fp.u + fp.u ^ 2) *
          ∑ t : Fin s,
            |rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k|) ≤
      rowSampleGramFpPerturbBudget fp A := by
  classical
  let C : ℝ := 2 * fp.u + fp.u ^ 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hD_nonneg : 0 ≤ rowSqNormProbDen A := le_of_lt hden
  unfold rowSampleGramFpPerturbBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hC_nonneg hD_nonneg
  · intro j k
    have hsum_nonneg :
        0 ≤ ∑ t : Fin s,
          |rowSampleSketch s A samples t j| *
            |rowSampleSketch s A samples t k| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsum_le :=
      rowSampleSketch_abs_mul_sum_le_den A hden hs samples j k
    let S : ℝ :=
      ∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|
    calc
      |(2 * fp.u + fp.u ^ 2) * S|
          = C * S := by
              simp [C, S, abs_of_nonneg (mul_nonneg hC_nonneg hsum_nonneg)]
      _ ≤ C * rowSqNormProbDen A := by
              exact mul_le_mul_of_nonneg_left (by simpa [S] using hsum_le) hC_nonneg
      _ = (2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A := by
              simp [C]

/-- The dot-product computation budget is uniformly bounded by the explicit
    `rowSampleGramDotProductBudget`. -/
theorem rowSampleGram_dot_product_budget_le_explicit (fp : FPModel)
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) (samples : RowTrace m s) :
    frobNorm
      (fun j k =>
        gamma fp s * (1 + fp.u) ^ 2 *
          ∑ t : Fin s,
            |rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k|) ≤
      rowSampleGramDotProductBudget fp s A := by
  classical
  let C : ℝ := gamma fp s * (1 + fp.u) ^ 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + fp.u))
  have hD_nonneg : 0 ≤ rowSqNormProbDen A := le_of_lt hden
  unfold rowSampleGramDotProductBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hC_nonneg hD_nonneg
  · intro j k
    have hsum_nonneg :
        0 ≤ ∑ t : Fin s,
          |rowSampleSketch s A samples t j| *
            |rowSampleSketch s A samples t k| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsum_le :=
      rowSampleSketch_abs_mul_sum_le_den A hden hs samples j k
    let S : ℝ :=
      ∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|
    calc
      |gamma fp s * (1 + fp.u) ^ 2 * S|
          = C * S := by
              simp [C, S, abs_of_nonneg (mul_nonneg hC_nonneg hsum_nonneg)]
      _ ≤ C * rowSqNormProbDen A := by
              exact mul_le_mul_of_nonneg_left (by simpa [S] using hsum_le) hC_nonneg
      _ = gamma fp s * (1 + fp.u) ^ 2 * rowSqNormProbDen A := by
              simp [C]

/-- Total deterministic perturbation budget for the fully floating-point Gram:
    rounded row scaling plus rounded dot products for each Gram entry. -/
noncomputable def rowSampleGramFullFpPerturbBudget (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ) : ℝ :=
  rowSampleGramFpPerturbBudget fp A + rowSampleGramDotProductBudget fp s A

/-- Row-scaling Gram perturbation budget for an arbitrary proved relative
    sampled-sketch entry error `uEff`. -/
noncomputable def rowSampleGramRelPerturbBudget {m n : ℕ}
    (uEff : ℝ) (A : Fin m → Fin n → ℝ) : ℝ :=
  frobNorm (fun _j _k : Fin n => (2 * uEff + uEff ^ 2) * rowSqNormProbDen A)

/-- Dot-product perturbation budget when the already rounded sampled sketch is
    within relative error `uEff` of the exact sampled sketch. -/
noncomputable def rowSampleGramDotProductRelBudget (fp : FPModel)
    {m n : ℕ} (s : ℕ) (uEff : ℝ) (A : Fin m → Fin n → ℝ) : ℝ :=
  frobNorm
    (fun _j _k : Fin n =>
      gamma fp s * (1 + uEff) ^ 2 * rowSqNormProbDen A)

/-- Fully computed-denominator Algorithm 2 Gram perturbation budget.  The
    effective row error charges denominator computation and final rounded
    division; the dot-product term additionally charges the computed Gram
    entries. -/
noncomputable def rowSampleGramComputedDenFullFpPerturbBudget (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A)) : ℝ :=
  let uEff := rowScaleComputedDenEffectiveRelError fp (rowSqNormProb A) dhat
  rowSampleGramRelPerturbBudget uEff A +
    rowSampleGramDotProductRelBudget fp s uEff A

/-- Scaling-only computed-denominator budget, used when the Gram matrix is an
    exact mathematical object formed from the already rounded sketch. -/
noncomputable def rowSampleGramComputedDenScalePerturbBudget (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A)) : ℝ :=
  rowSampleGramRelPerturbBudget
    (rowScaleComputedDenEffectiveRelError fp (rowSqNormProb A) dhat) A

/-- The fully floating-point sampled-Gram perturbation budget is nonnegative. -/
theorem rowSampleGramFullFpPerturbBudget_nonneg (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ) :
    0 ≤ rowSampleGramFullFpPerturbBudget fp s A := by
  unfold rowSampleGramFullFpPerturbBudget rowSampleGramFpPerturbBudget
    rowSampleGramDotProductBudget
  exact add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

theorem rowSampleGramRelPerturbBudget_nonneg {m n : ℕ}
    (uEff : ℝ) (A : Fin m → Fin n → ℝ) :
    0 ≤ rowSampleGramRelPerturbBudget (m := m) (n := n) uEff A := by
  unfold rowSampleGramRelPerturbBudget
  exact frobNorm_nonneg _

theorem rowSampleGramDotProductRelBudget_nonneg (fp : FPModel)
    {m n : ℕ} (s : ℕ) (uEff : ℝ) (A : Fin m → Fin n → ℝ) :
    0 ≤ rowSampleGramDotProductRelBudget fp s uEff A := by
  unfold rowSampleGramDotProductRelBudget
  exact frobNorm_nonneg _

theorem rowSampleGramComputedDenFullFpPerturbBudget_nonneg (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A)) :
    0 ≤ rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat := by
  unfold rowSampleGramComputedDenFullFpPerturbBudget
  exact add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

/-- Closed form of the arbitrary-relative-error row-scaling budget. -/
theorem rowSampleGramRelPerturbBudget_eq_nat_mul {m n : ℕ}
    (uEff : ℝ) (A : Fin m → Fin n → ℝ)
    (huEff : 0 ≤ uEff) :
    rowSampleGramRelPerturbBudget (m := m) (n := n) uEff A =
      (n : ℝ) * ((2 * uEff + uEff ^ 2) * rowSqNormProbDen A) := by
  have hC : 0 ≤ (2 * uEff + uEff ^ 2) * rowSqNormProbDen A := by
    have hu : 0 ≤ 2 * uEff + uEff ^ 2 := by
      nlinarith [huEff, sq_nonneg uEff]
    have hden : 0 ≤ rowSqNormProbDen A := by
      unfold rowSqNormProbDen
      exact frobNormSqRect_nonneg A
    exact mul_nonneg hu hden
  unfold rowSampleGramRelPerturbBudget
  exact frobNorm_const hC

/-- Closed form of the arbitrary-relative-error dot-product budget. -/
theorem rowSampleGramDotProductRelBudget_eq_nat_mul (fp : FPModel)
    {m n : ℕ} {s : ℕ} (uEff : ℝ) (A : Fin m → Fin n → ℝ)
    (hγ : gammaValid fp s) :
    rowSampleGramDotProductRelBudget fp s uEff A =
      (n : ℝ) *
        (gamma fp s * (1 + uEff) ^ 2 * rowSqNormProbDen A) := by
  have hC :
      0 ≤ gamma fp s * (1 + uEff) ^ 2 * rowSqNormProbDen A := by
    have hleft : 0 ≤ gamma fp s * (1 + uEff) ^ 2 :=
      mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + uEff))
    have hden : 0 ≤ rowSqNormProbDen A := by
      unfold rowSqNormProbDen
      exact frobNormSqRect_nonneg A
    exact mul_nonneg hleft hden
  unfold rowSampleGramDotProductRelBudget
  exact frobNorm_const hC

/-- The deterministic Gram perturbation matrix from a relative sampled-sketch
    error `uEff` is bounded by the explicit arbitrary-relative-error budget. -/
theorem rowSampleGram_rel_perturb_budget_le_explicit
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (samples : RowTrace m s) (uEff : ℝ) (huEff : 0 ≤ uEff) :
    frobNorm
      (fun j k =>
        (2 * uEff + uEff ^ 2) *
          ∑ t : Fin s,
            |rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k|) ≤
      rowSampleGramRelPerturbBudget uEff A := by
  classical
  let C : ℝ := 2 * uEff + uEff ^ 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith [huEff, sq_nonneg uEff]
  have hD_nonneg : 0 ≤ rowSqNormProbDen A := le_of_lt hden
  unfold rowSampleGramRelPerturbBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hC_nonneg hD_nonneg
  · intro j k
    have hsum_nonneg :
        0 ≤ ∑ t : Fin s,
          |rowSampleSketch s A samples t j| *
            |rowSampleSketch s A samples t k| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsum_le :=
      rowSampleSketch_abs_mul_sum_le_den A hden hs samples j k
    let S : ℝ :=
      ∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|
    calc
      |(2 * uEff + uEff ^ 2) * S|
          = C * S := by
              simp [C, S, abs_of_nonneg (mul_nonneg hC_nonneg hsum_nonneg)]
      _ ≤ C * rowSqNormProbDen A := by
              exact mul_le_mul_of_nonneg_left (by simpa [S] using hsum_le) hC_nonneg
      _ = (2 * uEff + uEff ^ 2) * rowSqNormProbDen A := by
              simp [C]

/-- The dot-product computation budget under entrywise relative row error
    `uEff` is bounded by the explicit arbitrary-relative-error budget. -/
theorem rowSampleGram_dot_product_rel_budget_le_explicit
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) (samples : RowTrace m s)
    (uEff : ℝ) :
    frobNorm
      (fun j k =>
        gamma fp s * (1 + uEff) ^ 2 *
          ∑ t : Fin s,
            |rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k|) ≤
      rowSampleGramDotProductRelBudget fp s uEff A := by
  classical
  let C : ℝ := gamma fp s * (1 + uEff) ^ 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + uEff))
  have hD_nonneg : 0 ≤ rowSqNormProbDen A := le_of_lt hden
  unfold rowSampleGramDotProductRelBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hC_nonneg hD_nonneg
  · intro j k
    have hsum_nonneg :
        0 ≤ ∑ t : Fin s,
          |rowSampleSketch s A samples t j| *
            |rowSampleSketch s A samples t k| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsum_le :=
      rowSampleSketch_abs_mul_sum_le_den A hden hs samples j k
    let S : ℝ :=
      ∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|
    calc
      |gamma fp s * (1 + uEff) ^ 2 * S|
          = C * S := by
              simp [C, S, abs_of_nonneg (mul_nonneg hC_nonneg hsum_nonneg)]
      _ ≤ C * rowSqNormProbDen A := by
              exact mul_le_mul_of_nonneg_left (by simpa [S] using hsum_le) hC_nonneg
      _ = gamma fp s * (1 + uEff) ^ 2 * rowSqNormProbDen A := by
              simp [C]

/-- Deterministic fully-floating-point Gram perturbation from entrywise sketch
    stability and the library dot-product bound. -/
theorem fl_rowSampleGramDot_perturb_bound_of_entrywise
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) (samples : RowTrace m s)
    (hentry : ∀ t j,
      |fl_rowSampleSketch fp s A samples t j -
        rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * fp.u) :
    frobNorm
      (fun j k =>
        fl_rowSampleGramDot fp s A samples j k -
          rowSampleGram s A samples j k) ≤
      rowSampleGramFullFpPerturbBudget fp s A := by
  classical
  let B : Fin s → Fin n → ℝ := rowSampleSketch s A samples
  let Bhat : Fin s → Fin n → ℝ := fl_rowSampleSketch fp s A samples
  have hdot :
      frobNorm
        (fun j k =>
          fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) ≤
        rowSampleGramDotProductBudget fp s A := by
    have hlocal :=
      rowSketchGram_dot_frob_error_bound_of_entrywise
        fp B Bhat fp.u fp.u_nonneg hγ (by simpa [B, Bhat] using hentry)
    have hbudget :=
      rowSampleGram_dot_product_budget_le_explicit fp A hden hs hγ samples
    have hlocal' :
        frobNorm
          (fun j k =>
            fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) ≤
          frobNorm
            (fun j k =>
              gamma fp s * (1 + fp.u) ^ 2 *
                ∑ t : Fin s,
                  |rowSampleSketch s A samples t j| *
                    |rowSampleSketch s A samples t k|) := by
      simpa [B, Bhat] using hlocal
    exact hlocal'.trans hbudget
  have hscale :
      frobNorm
        (fun j k =>
          rowSketchGram Bhat j k - rowSampleGram s A samples j k) ≤
        rowSampleGramFpPerturbBudget fp A := by
    have hpoint :=
      rowSampleGram_frob_error_bound_of_entrywise
        s A samples Bhat fp.u fp.u_nonneg
        (by simpa [B, Bhat] using hentry)
    have hbudget :=
      rowSampleGram_perturb_budget_le_explicit fp A hden hs samples
    have hpoint' :
        frobNorm
          (fun j k =>
            rowSketchGram Bhat j k - rowSampleGram s A samples j k) ≤
          frobNorm
            (fun j k =>
              (2 * fp.u + fp.u ^ 2) *
                ∑ t : Fin s,
                  |rowSampleSketch s A samples t j| *
                    |rowSampleSketch s A samples t k|) := by
      simpa [Bhat] using hpoint
    exact hpoint'.trans hbudget
  have hsplit :
      (fun j k =>
        fl_rowSampleGramDot fp s A samples j k -
          rowSampleGram s A samples j k) =
      (fun j k =>
        (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k) +
        (rowSketchGram Bhat j k - rowSampleGram s A samples j k)) := by
    funext j k
    simp [fl_rowSampleGramDot, Bhat]
  have htri :=
    frobNorm_add_le
      (fun j k =>
        fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k)
      (fun j k => rowSketchGram Bhat j k - rowSampleGram s A samples j k)
  calc
    frobNorm
      (fun j k =>
        fl_rowSampleGramDot fp s A samples j k -
          rowSampleGram s A samples j k)
        = frobNorm
          (fun j k =>
            (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
            (rowSketchGram Bhat j k - rowSampleGram s A samples j k)) := by
            rw [hsplit]
    _ ≤
        frobNorm
          (fun j k =>
            fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
        frobNorm
          (fun j k => rowSketchGram Bhat j k - rowSampleGram s A samples j k) :=
          htri
    _ ≤ rowSampleGramDotProductBudget fp s A +
        rowSampleGramFpPerturbBudget fp A :=
          add_le_add hdot hscale
    _ = rowSampleGramFullFpPerturbBudget fp s A := by
          unfold rowSampleGramFullFpPerturbBudget
          ring

/-- Deterministic Gram perturbation for the computed-denominator Algorithm 2
    path when the Gram matrix is formed exactly from the rounded sampled
    sketch. -/
theorem fl_rowSampleGramWithComputedDen_perturb_bound
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A))
    (samples : RowTrace m s) (hgood : rowTracePositiveProb A samples) :
    frobNorm
      (fun j k =>
        fl_rowSampleGramWithComputedDen fp A dhat.den samples j k -
          rowSampleGram s A samples j k) ≤
      rowSampleGramComputedDenScalePerturbBudget fp s A dhat := by
  classical
  let uEff : ℝ :=
    rowScaleComputedDenEffectiveRelError fp (rowSqNormProb A) dhat
  have huEff : 0 ≤ uEff :=
    rowScaleComputedDenEffectiveRelError_nonneg fp (rowSqNormProb A) dhat
  let Bhat : Fin s → Fin n → ℝ :=
    fl_rowSampleSketchWithComputedDen fp A dhat.den samples
  have hentry : ∀ t j,
      |Bhat t j - rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * uEff := by
    intro t j
    have hprob : 0 < rowSqNormProb A (samples t) := hgood t
    have h :=
      fl_rowSampleSketchWithComputedDen_total_error_bound_le_budget
        fp A (rowSqNormProb A) dhat samples t j hs hprob
    simpa [Bhat, rowSampleSketchWithProb, rowSampleSketch,
      rowSampleIncrementWithProb, rowSampleIncrement,
      rowSampleScaleDenWithProb, rowSampleScaleDen, uEff] using h
  have hpoint :=
    rowSampleGram_frob_error_bound_of_entrywise
      s A samples Bhat uEff huEff hentry
  have hbudget :=
    rowSampleGram_rel_perturb_budget_le_explicit
      A hden hs samples uEff huEff
  have hpoint' :
      frobNorm
        (fun j k =>
          rowSketchGram Bhat j k - rowSampleGram s A samples j k) ≤
        rowSampleGramRelPerturbBudget uEff A :=
    hpoint.trans hbudget
  simpa [fl_rowSampleGramWithComputedDen, Bhat,
    rowSampleGramComputedDenScalePerturbBudget, uEff] using hpoint'

/-- Deterministic fully floating-point Gram perturbation for the
    computed-denominator Algorithm 2 path. -/
theorem fl_rowSampleGramDotWithComputedDen_perturb_bound
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A))
    (samples : RowTrace m s) (hgood : rowTracePositiveProb A samples) :
    frobNorm
      (fun j k =>
        fl_rowSampleGramDotWithComputedDen fp A dhat.den samples j k -
          rowSampleGram s A samples j k) ≤
      rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat := by
  classical
  let uEff : ℝ :=
    rowScaleComputedDenEffectiveRelError fp (rowSqNormProb A) dhat
  have huEff : 0 ≤ uEff :=
    rowScaleComputedDenEffectiveRelError_nonneg fp (rowSqNormProb A) dhat
  let B : Fin s → Fin n → ℝ := rowSampleSketch s A samples
  let Bhat : Fin s → Fin n → ℝ :=
    fl_rowSampleSketchWithComputedDen fp A dhat.den samples
  have hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * uEff := by
    intro t j
    have hprob : 0 < rowSqNormProb A (samples t) := hgood t
    have h :=
      fl_rowSampleSketchWithComputedDen_total_error_bound_le_budget
        fp A (rowSqNormProb A) dhat samples t j hs hprob
    simpa [B, Bhat, rowSampleSketchWithProb, rowSampleSketch,
      rowSampleIncrementWithProb, rowSampleIncrement,
      rowSampleScaleDenWithProb, rowSampleScaleDen, uEff] using h
  have hdot :
      frobNorm
        (fun j k =>
          fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) ≤
        rowSampleGramDotProductRelBudget fp s uEff A := by
    have hlocal :=
      rowSketchGram_dot_frob_error_bound_of_entrywise
        fp B Bhat uEff huEff hγ hentry
    have hbudget :=
      rowSampleGram_dot_product_rel_budget_le_explicit
        fp A hden hs hγ samples uEff
    exact hlocal.trans hbudget
  have hscale :
      frobNorm
        (fun j k =>
          rowSketchGram Bhat j k - rowSampleGram s A samples j k) ≤
        rowSampleGramRelPerturbBudget uEff A := by
    have hpoint :=
      rowSampleGram_frob_error_bound_of_entrywise
        s A samples Bhat uEff huEff (by simpa [B] using hentry)
    have hbudget :=
      rowSampleGram_rel_perturb_budget_le_explicit
        A hden hs samples uEff huEff
    exact hpoint.trans hbudget
  have hsplit :
      (fun j k =>
        fl_rowSampleGramDotWithComputedDen fp A dhat.den samples j k -
          rowSampleGram s A samples j k) =
      (fun j k =>
        (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k) +
        (rowSketchGram Bhat j k - rowSampleGram s A samples j k)) := by
    funext j k
    simp [fl_rowSampleGramDotWithComputedDen, Bhat]
  have htri :=
    frobNorm_add_le
      (fun j k =>
        fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k)
      (fun j k => rowSketchGram Bhat j k - rowSampleGram s A samples j k)
  calc
    frobNorm
      (fun j k =>
        fl_rowSampleGramDotWithComputedDen fp A dhat.den samples j k -
          rowSampleGram s A samples j k)
        = frobNorm
          (fun j k =>
            (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
            (rowSketchGram Bhat j k - rowSampleGram s A samples j k)) := by
            rw [hsplit]
    _ ≤
        frobNorm
          (fun j k =>
            fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
        frobNorm
          (fun j k => rowSketchGram Bhat j k - rowSampleGram s A samples j k) :=
          htri
    _ ≤ rowSampleGramDotProductRelBudget fp s uEff A +
        rowSampleGramRelPerturbBudget uEff A :=
          add_le_add hdot hscale
    _ = rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat := by
          unfold rowSampleGramComputedDenFullFpPerturbBudget
          dsimp [uEff]
          ring

-- ============================================================
-- Expected Gram perturbation from sampled-sketch stability
-- ============================================================
































































































































































































-- ============================================================
-- High-probability equation (5) and floating-point perturbation
-- ============================================================
















































































































































































































































































































































































































































































































































































































































end NumStability
