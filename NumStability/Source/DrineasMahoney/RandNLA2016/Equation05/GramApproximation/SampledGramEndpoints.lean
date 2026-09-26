import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.FloatingPoint.Model
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm02.RowSampling.Endpoints
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation04.RowSamplingProbability.Normalization
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation05.GramApproximation.Bounds
import NumStability.Source.Higham.Chapter04.Problem04

/-!
Relocated from the historical wave owners NumStability.Algorithms.RandNLA.RowSamplingGram under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

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























































































-- ============================================================
-- Marginals of the independent row trace product law
-- ============================================================



























































/-- Product-law pointwise factorization for two distinct trace coordinates. -/
private theorem rowSqNormTraceProbMass_two_point_factor
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (t u : Fin steps) (htu : t ≠ u) (f g : Fin m → ℝ)
    (x : RowTrace m steps) :
    (∏ r : Fin steps,
      if r = t then rowSqNormProb A (x r) * f (x r)
      else if r = u then rowSqNormProb A (x r) * g (x r)
      else rowSqNormProb A (x r)) =
    (∏ r : Fin steps, rowSqNormProb A (x r)) * f (x t) * g (x u) := by
  classical
  have hfactor : ∀ r : Fin steps,
      (if r = t then rowSqNormProb A (x r) * f (x r)
      else if r = u then rowSqNormProb A (x r) * g (x r)
      else rowSqNormProb A (x r)) =
      rowSqNormProb A (x r) *
        (if r = t then f (x r) else if r = u then g (x r) else 1) := by
    intro r
    by_cases hrt : r = t
    · simp [hrt]
    · by_cases hru : r = u
      · simp [hru]
      · simp [hru]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  have hprod_t := Finset.prod_eq_mul_prod_diff_singleton
    (s := (Finset.univ : Finset (Fin steps))) t
    (fun r : Fin steps =>
      if r = t then f (x r) else if r = u then g (x r) else 1)
    (by intro h; simp at h)
  simp at hprod_t
  have hfac :
      (∏ x_1 : Fin steps,
        if x_1 = t then f (x x_1) else if x_1 = u then g (x x_1) else 1)
      = f (x t) * g (x u) := by
    rw [hprod_t]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t},
          if x_1 = t then f (x x_1) else if x_1 = u then g (x x_1)
          else 1) = g (x u) := by
      have hprod_u := Finset.prod_eq_mul_prod_diff_singleton
        (s := ((Finset.univ : Finset (Fin steps)).erase t)) u
        (fun r : Fin steps =>
          if r = t then f (x r) else if r = u then g (x r) else 1)
        (by
          intro hu_notin
          have : u ∈ (Finset.univ : Finset (Fin steps)).erase t := by
            simp [htu.symm]
          exact False.elim (hu_notin this))
      simp [htu.symm] at hprod_u
      rw [Finset.sdiff_singleton_eq_erase]
      rw [hprod_u]
      have hrest :
          (∏ x_1 ∈ (Finset.univ : Finset (Fin steps)).erase t \ {u},
            if x_1 = t then f (x x_1) else if x_1 = u then g (x x_1)
            else 1) = 1 := by
        apply Finset.prod_eq_one
        intro r hr
        have hrt : r ≠ t := by
          simp at hr
          exact hr.1
        have hru : r ≠ u := by
          simp at hr
          exact hr.2
        simp [hrt, hru]
      rw [hrest]
      ring
    rw [herase]
  rw [hfac]
  ring

/-- Two distinct coordinates of the independent trace have product
    expectation equal to the product of their one-step expectations. -/
theorem rowSqNormTraceProbMass_marginal_two_ne {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : rowSqNormProbDen A ≠ 0)
    (t u : Fin steps) (htu : t ≠ u) (f g : Fin m → ℝ) :
    (∑ samples : RowTrace m steps,
      rowSqNormTraceProbMass A samples *
        (f (samples t) * g (samples u))) =
      (∑ i : Fin m, rowSqNormProb A i * f i) *
      (∑ i : Fin m, rowSqNormProb A i * g i) := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (RowSample m)))
      (f := fun r x =>
        if r = t then rowSqNormProb A x * f x
        else if r = u then rowSqNormProb A x * g x
        else rowSqNormProb A x)
  have hleft :
      (∏ r : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (RowSample m)),
          (if r = t then rowSqNormProb A x * f x
          else if r = u then rowSqNormProb A x * g x
          else rowSqNormProb A x)) =
      (∑ i : Fin m, rowSqNormProb A i * f i) *
      (∑ i : Fin m, rowSqNormProb A i * g i) := by
    simp [rowSqNormProb_sum_eq_one A hden]
    have hprod_t := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t
      (fun r : Fin steps =>
        if r = t then ∑ x : RowSample m, rowSqNormProb A x * f x
        else if r = u then ∑ x : RowSample m, rowSqNormProb A x * g x
        else 1)
      (by intro h; simp at h)
    simp at hprod_t
    rw [hprod_t]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t},
          if x_1 = t then ∑ x : RowSample m, rowSqNormProb A x * f x
          else if x_1 = u then ∑ x : RowSample m, rowSqNormProb A x * g x
          else 1) = ∑ x : RowSample m, rowSqNormProb A x * g x := by
      rw [Finset.sdiff_singleton_eq_erase]
      have hprod_u := Finset.prod_eq_mul_prod_diff_singleton
        (s := ((Finset.univ : Finset (Fin steps)).erase t)) u
        (fun r : Fin steps =>
          if r = t then ∑ x : RowSample m, rowSqNormProb A x * f x
          else if r = u then ∑ x : RowSample m, rowSqNormProb A x * g x
          else 1)
        (by
          intro hu_notin
          have : u ∈ (Finset.univ : Finset (Fin steps)).erase t := by
            simp [htu.symm]
          exact False.elim (hu_notin this))
      simp [htu.symm] at hprod_u
      rw [hprod_u]
      have hrest :
          (∏ x_1 ∈ (Finset.univ : Finset (Fin steps)).erase t \ {u},
            if x_1 = t then ∑ x : RowSample m, rowSqNormProb A x * f x
            else if x_1 = u then ∑ x : RowSample m, rowSqNormProb A x * g x
            else 1) = 1 := by
        apply Finset.prod_eq_one
        intro r hr
        have hrt : r ≠ t := by
          simp at hr
          exact hr.1
        have hru : r ≠ u := by
          simp at hr
          exact hr.2
        simp [hrt, hru]
      rw [hrest]
      ring
    rw [herase]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (RowSample m))),
        ∏ r, (if r = t then rowSqNormProb A (x r) * f (x r)
          else if r = u then rowSqNormProb A (x r) * g (x r)
          else rowSqNormProb A (x r)))
        = ∑ samples : RowTrace m steps,
          rowSqNormTraceProbMass A samples *
            (f (samples t) * g (samples u)) := by
    simp [rowSqNormTraceProbMass, RowTrace]
    apply Finset.sum_congr rfl
    intro x _
    simpa [mul_assoc] using
      rowSqNormTraceProbMass_two_point_factor A t u htu f g x
  rw [← hright, ← hprod]
  exact hleft

-- ============================================================
-- Unbiasedness of the sampled Gram matrix
-- ============================================================












































































-- ============================================================
-- Scalar second-moment kernel for independent row traces
-- ============================================================

/-- For any scalar quantity attached to a sampled row, the centered sum over an
    independent row trace has second moment `s` times the one-step centered
    second moment. This is the finite iid variance calculation used in the
    proof of the Algorithm 2 Frobenius estimate. -/
theorem rowSqNormTraceProbability_expectationReal_centered_sum_sq
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (f : Fin m → ℝ) :
    let μ : ℝ := ∑ i : Fin m, rowSqNormProb A i * f i
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => (∑ t : Fin s, (f (samples t) - μ)) ^ 2) =
      (s : ℝ) * ∑ i : Fin m, rowSqNormProb A i * (f i - μ) ^ 2 := by
  classical
  let μ : ℝ := ∑ i : Fin m, rowSqNormProb A i * f i
  have hcenter : ∑ i : Fin m, rowSqNormProb A i * (f i - μ) = 0 := by
    unfold μ
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [rowSqNormProb_sum_eq_one A hden.ne']
    ring
  have hsame : ∀ t : Fin s,
      (rowSqNormTraceProbability (steps := s) A hden).expectationReal
        (fun samples => (f (samples t) - μ) * (f (samples t) - μ)) =
        ∑ i : Fin m, rowSqNormProb A i * (f i - μ) ^ 2 := by
    intro t
    unfold FiniteProbability.expectationReal rowSqNormTraceProbability
    calc
      ∑ samples : RowTrace m s,
          rowSqNormTraceProbMass A samples *
            ((f (samples t) - μ) * (f (samples t) - μ))
          = ∑ i : Fin m, rowSqNormProb A i *
              ((f i - μ) * (f i - μ)) :=
            rowSqNormTraceProbMass_marginal_one A hden.ne' t
              (fun i => (f i - μ) * (f i - μ))
      _ = ∑ i : Fin m, rowSqNormProb A i * (f i - μ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
  have hdiff : ∀ t u : Fin s, t ≠ u →
      (rowSqNormTraceProbability (steps := s) A hden).expectationReal
        (fun samples => (f (samples t) - μ) * (f (samples u) - μ)) = 0 := by
    intro t u htu
    unfold FiniteProbability.expectationReal rowSqNormTraceProbability
    calc
      ∑ samples : RowTrace m s,
          rowSqNormTraceProbMass A samples *
            ((f (samples t) - μ) * (f (samples u) - μ))
          = (∑ i : Fin m, rowSqNormProb A i * (f i - μ)) *
            (∑ i : Fin m, rowSqNormProb A i * (f i - μ)) :=
            rowSqNormTraceProbMass_marginal_two_ne A hden.ne' t u htu
              (fun i => f i - μ) (fun i => f i - μ)
      _ = 0 := by rw [hcenter]; ring
  have hsquare : ∀ samples : RowTrace m s,
      (∑ t : Fin s, (f (samples t) - μ)) ^ 2 =
        ∑ t : Fin s, ∑ u : Fin s,
          (f (samples t) - μ) * (f (samples u) - μ) := by
    intro samples
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  calc
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => (∑ t : Fin s, (f (samples t) - μ)) ^ 2)
        = (rowSqNormTraceProbability (steps := s) A hden).expectationReal
            (fun samples => ∑ t : Fin s, ∑ u : Fin s,
              (f (samples t) - μ) * (f (samples u) - μ)) := by
            congr 1
            ext samples
            exact hsquare samples
    _ = ∑ t : Fin s, ∑ u : Fin s,
          (rowSqNormTraceProbability (steps := s) A hden).expectationReal
            (fun samples => (f (samples t) - μ) * (f (samples u) - μ)) := by
            rw [FiniteProbability.expectationReal_sum]
            apply Finset.sum_congr rfl
            intro t _
            rw [FiniteProbability.expectationReal_sum]
    _ = ∑ t : Fin s, ∑ i : Fin m,
          rowSqNormProb A i * (f i - μ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro t _
            calc
              (∑ u : Fin s,
                (rowSqNormTraceProbability (steps := s) A hden).expectationReal
                  (fun samples =>
                    (f (samples t) - μ) * (f (samples u) - μ)))
                  = (rowSqNormTraceProbability (steps := s) A hden).expectationReal
                      (fun samples =>
                        (f (samples t) - μ) * (f (samples t) - μ)) := by
                    apply Finset.sum_eq_single t
                    · intro u _ hut
                      exact hdiff t u hut.symm
                    · intro ht_not
                      exact False.elim (ht_not (Finset.mem_univ t))
              _ = ∑ i : Fin m,
                    rowSqNormProb A i * (f i - μ) ^ 2 := hsame t
    _ = (s : ℝ) * ∑ i : Fin m,
          rowSqNormProb A i * (f i - μ) ^ 2 := by
            rw [Finset.sum_const]
            simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Sample-average form of the finite iid variance calculation. -/
theorem rowSqNormTraceProbability_expectationReal_sampleAverage_sub_mean_sq
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (f : Fin m → ℝ) :
    let μ : ℝ := ∑ i : Fin m, rowSqNormProb A i * f i
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => ((∑ t : Fin s, f (samples t)) / (s : ℝ) - μ) ^ 2) =
      (1 / (s : ℝ)) *
        ∑ i : Fin m, rowSqNormProb A i * (f i - μ) ^ 2 := by
  classical
  let μ : ℝ := ∑ i : Fin m, rowSqNormProb A i * f i
  have hcentered :=
    rowSqNormTraceProbability_expectationReal_centered_sum_sq (s := s) A hden f
  have hpoint : ∀ samples : RowTrace m s,
      (∑ t : Fin s, f (samples t)) / (s : ℝ) - μ =
        (∑ t : Fin s, (f (samples t) - μ)) / (s : ℝ) := by
    intro samples
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt hs]
  calc
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => ((∑ t : Fin s, f (samples t)) / (s : ℝ) - μ) ^ 2)
        = (rowSqNormTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              ((∑ t : Fin s, (f (samples t) - μ)) / (s : ℝ)) ^ 2) := by
            congr 1
            ext samples
            rw [hpoint samples]
    _ = (rowSqNormTraceProbability (steps := s) A hden).expectationReal
          (fun samples => (∑ t : Fin s, (f (samples t) - μ)) ^ 2) /
            (s : ℝ) ^ 2 := by
          unfold FiniteProbability.expectationReal
          simp_rw [div_eq_mul_inv]
          calc
            ∑ samples : RowTrace m s,
                (rowSqNormTraceProbability (steps := s) A hden).prob samples *
                  ((∑ t : Fin s, (f (samples t) - μ)) * (s : ℝ)⁻¹) ^ 2
                = ∑ samples : RowTrace m s,
                    ((rowSqNormTraceProbability (steps := s) A hden).prob samples *
                      (∑ t : Fin s, (f (samples t) - μ)) ^ 2) *
                      ((s : ℝ) ^ 2)⁻¹ := by
                    apply Finset.sum_congr rfl
                    intro samples _
                    ring
            _ = (∑ samples : RowTrace m s,
                    (rowSqNormTraceProbability (steps := s) A hden).prob samples *
                      (∑ t : Fin s, (f (samples t) - μ)) ^ 2) *
                    ((s : ℝ) ^ 2)⁻¹ := by
                    rw [Finset.sum_mul]
    _ = ((s : ℝ) * ∑ i : Fin m,
          rowSqNormProb A i * (f i - μ) ^ 2) / (s : ℝ) ^ 2 := by
          rw [hcentered]
    _ = (1 / (s : ℝ)) *
        ∑ i : Fin m, rowSqNormProb A i * (f i - μ) ^ 2 := by
          field_simp [ne_of_gt hs]






























-- ============================================================
-- Row-outer-product specialization of the variance kernel
-- ============================================================

































































































































































































/-- Coordinate second-moment formula for the Algorithm 2 Gram estimator. -/
theorem rowSqNormTraceProbability_expectationReal_rowSampleGram_entry_error_sq
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (j k : Fin n) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => (rowSampleGram s A samples j k - rowGram A j k) ^ 2) =
      (1 / (s : ℝ)) *
        ∑ i : Fin m, rowSqNormProb A i *
          (rowOuterGramSample A i j k - rowGram A j k) ^ 2 := by
  classical
  have hvar :=
    rowSqNormTraceProbability_expectationReal_sampleAverage_sub_mean_sq
      (s := s) A hden hs (fun i => rowOuterGramSample A i j k)
  have hmean := rowOuterGramSample_mean_eq_rowGram A hden j k
  simpa [rowSampleGram_eq_rowOuterGramSample_average A hden hs,
    hmean] using hvar




























































































/-- Squared-Frobenius second-moment form of equation (5):
    `E ||ÃᵀÃ - AᵀA||_F² ≤ ||A||_F⁴ / s`. -/
theorem rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_sq_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ)) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        frobNormSq (fun j k => rowSampleGram s A samples j k - rowGram A j k)) ≤
      rowSqNormProbDen A ^ 2 / (s : ℝ) := by
  classical
  have hcoord := fun j k =>
    rowSqNormTraceProbability_expectationReal_rowSampleGram_entry_error_sq
      A hden hs j k
  have hcenter_le : ∀ j k : Fin n,
      ∑ i : Fin m, rowSqNormProb A i *
          (rowOuterGramSample A i j k - rowGram A j k) ^ 2 ≤
        ∑ i : Fin m, rowSqNormProb A i *
          rowOuterGramSample A i j k ^ 2 := by
    intro j k
    exact weighted_centered_sq_le_sq
      (fun i : Fin m => rowSqNormProb A i)
      (fun i : Fin m => rowOuterGramSample A i j k)
      (rowGram A j k)
      (rowSqNormProb_sum_eq_one A hden.ne')
      (rowOuterGramSample_mean_eq_rowGram A hden j k).symm
  calc
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        frobNormSq (fun j k => rowSampleGram s A samples j k - rowGram A j k))
        = ∑ j : Fin n, ∑ k : Fin n,
            (rowSqNormTraceProbability (steps := s) A hden).expectationReal
              (fun samples =>
                (rowSampleGram s A samples j k - rowGram A j k) ^ 2) := by
            unfold frobNormSq
            rw [FiniteProbability.expectationReal_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [FiniteProbability.expectationReal_sum]
    _ = ∑ j : Fin n, ∑ k : Fin n,
          (1 / (s : ℝ)) *
            ∑ i : Fin m, rowSqNormProb A i *
              (rowOuterGramSample A i j k - rowGram A j k) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            exact hcoord j k
    _ ≤ ∑ j : Fin n, ∑ k : Fin n,
          (1 / (s : ℝ)) *
            ∑ i : Fin m, rowSqNormProb A i *
              rowOuterGramSample A i j k ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left (hcenter_le j k)
              (by positivity)
    _ = (1 / (s : ℝ)) *
          ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
            rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
    _ = rowSqNormProbDen A ^ 2 / (s : ℝ) := by
            rw [rowOuterGramSample_total_second_moment A hden]
            ring

/-- Equation (5) in expectation for norm-squared row sampling:
    `E ||ÃᵀÃ - AᵀA||_F ≤ ||A||_F² / sqrt(s)`.  In this development
    `rowSqNormProbDen A` is `||A||_F²`. -/
theorem rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ)) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        frobNorm (fun j k => rowSampleGram s A samples j k - rowGram A j k)) ≤
      (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Z : RowTrace m s → ℝ := fun samples =>
    frobNorm (fun j k => rowSampleGram s A samples j k - rowGram A j k)
  have hZ_nonneg : ∀ samples, 0 ≤ Z samples := by
    intro samples
    exact frobNorm_nonneg _
  have hjensen := FiniteProbability.expectationReal_le_sqrt_expectationReal_sq
    P Z hZ_nonneg
  have hZsq :
      P.expectationReal (fun samples => Z samples ^ 2) =
        P.expectationReal
          (fun samples =>
            frobNormSq
              (fun j k => rowSampleGram s A samples j k - rowGram A j k)) := by
    unfold Z
    congr 1
    ext samples
    exact frobNorm_sq _
  have hsecond :=
    rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_sq_le
      A hden hs
  have hsqrt_bound :
      Real.sqrt (P.expectationReal (fun samples => Z samples ^ 2)) ≤
        Real.sqrt (rowSqNormProbDen A ^ 2 / (s : ℝ)) := by
    apply Real.sqrt_le_sqrt
    rw [hZsq]
    exact hsecond
  have hden_nonneg : 0 ≤ rowSqNormProbDen A := frobNormSqRect_nonneg A
  have hsqrt_eq :
      Real.sqrt (rowSqNormProbDen A ^ 2 / (s : ℝ)) =
        (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A := by
    rw [Real.sqrt_div (sq_nonneg (rowSqNormProbDen A)) (s : ℝ)]
    rw [Real.sqrt_sq hden_nonneg]
    ring
  calc
    P.expectationReal Z
        ≤ Real.sqrt (P.expectationReal (fun samples => Z samples ^ 2)) := hjensen
    _ ≤ Real.sqrt (rowSqNormProbDen A ^ 2 / (s : ℝ)) := hsqrt_bound
    _ = (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A := hsqrt_eq

-- ============================================================
-- Floating-point perturbation of the sampled Gram matrix
-- ============================================================














































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- Expected Gram perturbation from sampled-sketch stability
-- ============================================================
























































































/-- Stability decomposition for equation (5): for any perturbed sampled sketch,
    the expected Gram error is bounded by the exact row-sampling equation (5)
    term plus the expected perturbation from replacing `rowSampleSketch` by
    `Bhat`. -/
theorem rowSqNormTraceProbability_expectationReal_rowSketchGram_frob_error_le_add_perturb
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (Bhat : RowTrace m s → Fin s → Fin n → ℝ) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        frobNorm (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k)) ≤
      (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A +
        (rowSqNormTraceProbability (steps := s) A hden).expectationReal
          (fun samples =>
            frobNorm
              (fun j k =>
                rowSketchGram (Bhat samples) j k -
                  rowSampleGram s A samples j k)) := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  have hpoint : ∀ samples : RowTrace m s,
      frobNorm (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) ≤
        frobNorm (fun j k => rowSampleGram s A samples j k - rowGram A j k) +
          frobNorm
            (fun j k =>
              rowSketchGram (Bhat samples) j k -
                rowSampleGram s A samples j k) := by
    intro samples
    have h :=
      frobNorm_add_le
        (fun j k => rowSampleGram s A samples j k - rowGram A j k)
        (fun j k =>
          rowSketchGram (Bhat samples) j k -
            rowSampleGram s A samples j k)
    have hsame :
        (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) =
          fun j k =>
            (rowSampleGram s A samples j k - rowGram A j k) +
              (rowSketchGram (Bhat samples) j k -
                rowSampleGram s A samples j k) := by
      funext j k
      ring
    simpa [hsame] using h
  calc
    P.expectationReal
      (fun samples =>
        frobNorm (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k))
        ≤ P.expectationReal
            (fun samples =>
              frobNorm
                (fun j k => rowSampleGram s A samples j k - rowGram A j k) +
              frobNorm
                (fun j k =>
                  rowSketchGram (Bhat samples) j k -
                    rowSampleGram s A samples j k)) := by
            exact FiniteProbability.expectationReal_mono P hpoint
    _ = P.expectationReal
          (fun samples =>
            frobNorm
              (fun j k => rowSampleGram s A samples j k - rowGram A j k)) +
        P.expectationReal
          (fun samples =>
            frobNorm
              (fun j k =>
                rowSketchGram (Bhat samples) j k -
                  rowSampleGram s A samples j k)) := by
            rw [FiniteProbability.expectationReal_add]
    _ ≤ (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A +
        P.expectationReal
          (fun samples =>
            frobNorm
              (fun j k =>
                rowSketchGram (Bhat samples) j k -
                  rowSampleGram s A samples j k)) := by
            have h :=
              add_le_add_right
              (rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_le
                A hden hs)
              (P.expectationReal
                (fun samples =>
                  frobNorm
                    (fun j k =>
                      rowSketchGram (Bhat samples) j k -
                        rowSampleGram s A samples j k)))
            simpa [P, add_comm, add_left_comm, add_assoc] using h

/-- Floating-point version of the equation (5) stability decomposition. -/
theorem rowSqNormTraceProbability_expectationReal_fl_rowSampleGram_frob_error_le_add_perturb
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ)) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        frobNorm (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k)) ≤
      (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A +
        (rowSqNormTraceProbability (steps := s) A hden).expectationReal
          (fun samples =>
            frobNorm
              (fun j k =>
                fl_rowSampleGram fp s A samples j k -
                  rowSampleGram s A samples j k)) := by
  simpa [fl_rowSampleGram, rowSketchGram] using
    rowSqNormTraceProbability_expectationReal_rowSketchGram_frob_error_le_add_perturb
      A hden hs (fun samples => fl_rowSampleSketch fp s A samples)

-- ============================================================
-- High-probability equation (5) and floating-point perturbation
-- ============================================================

/-- High-probability squared-moment form of equation (5): for any threshold
    `η > 0`, the exact sampled Gram error is at most `η` with probability at
    least `1 - (||A||_F⁴ / s) / η²`. -/
theorem rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_ge_one_sub
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (η : ℝ) (hη : 0 < η) :
    1 - (rowSqNormProbDen A ^ 2 / (s : ℝ)) / η ^ 2 ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤ η} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Z : RowTrace m s → ℝ := fun samples =>
    frobNorm (fun j k => rowSampleGram s A samples j k - rowGram A j k)
  have hZ : ∀ samples, 0 ≤ Z samples := by
    intro samples
    exact frobNorm_nonneg _
  have hprob :=
    FiniteProbability.eventProb_le_ge_one_sub_expectationReal_sq_div
      P Z η hZ hη
  have hsecond :
      P.expectationReal (fun samples => Z samples ^ 2) ≤
        rowSqNormProbDen A ^ 2 / (s : ℝ) := by
    have h :=
      rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_sq_le
        A hden hs
    have hZsq :
        P.expectationReal (fun samples => Z samples ^ 2) =
          P.expectationReal
            (fun samples =>
              frobNormSq
                (fun j k => rowSampleGram s A samples j k - rowGram A j k)) := by
      unfold Z
      congr 1
      ext samples
      exact frobNorm_sq _
    simpa [P, hZsq] using h
  have hdiv :
      P.expectationReal (fun samples => Z samples ^ 2) / η ^ 2 ≤
        (rowSqNormProbDen A ^ 2 / (s : ℝ)) / η ^ 2 := by
    exact div_le_div_of_nonneg_right hsecond (sq_nonneg η)
  calc
    1 - (rowSqNormProbDen A ^ 2 / (s : ℝ)) / η ^ 2
        ≤ 1 - P.expectationReal (fun samples => Z samples ^ 2) / η ^ 2 := by
            linarith
    _ ≤ P.eventProb {samples | Z samples ≤ η} := hprob

/-- Equation (5) as a high-probability statement with explicit failure
    probability `1 / (s ε²)`. -/
theorem rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A} := by
  classical
  have hη : 0 < ε * rowSqNormProbDen A := mul_pos hε hden
  have hbase :=
    rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_ge_one_sub
      A hden hs (ε * rowSqNormProbDen A) hη
  have hfail :
      (rowSqNormProbDen A ^ 2 / (s : ℝ)) /
          (ε * rowSqNormProbDen A) ^ 2 =
        1 / ((s : ℝ) * ε ^ 2) := by
    have hD : rowSqNormProbDen A ≠ 0 := hden.ne'
    have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
    have hε_ne : ε ≠ 0 := hε.ne'
    field_simp [hD, hs_ne, hε_ne]
  simpa [hfail] using hbase

/-- `1 - δ` form of high-probability equation (5). It is enough to choose the
    sample size so that `1 / (s ε²) ≤ δ`. -/
theorem rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon_of_budget
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε δ : ℝ) (hε : 0 < ε)
    (hbudget : 1 / ((s : ℝ) * ε ^ 2) ≤ δ) :
    1 - δ ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A} := by
  have h :=
    rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon
      A hden hs ε hε
  linarith

/-- Generic high-probability transfer from exact sampled-Gram error to any
    computed Gram matrix whose perturbation from the exact sampled Gram is
    bounded with high probability. -/
theorem rowSqNormTraceProbability_eventProb_computedGram_frob_error_le_epsilon_add_tau
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (G : RowTrace m s → Fin n → Fin n → ℝ)
    (ε τ δτ : ℝ) (hε : 0 < ε)
    (hpertProb :
      1 - δτ ≤
        (rowSqNormTraceProbability (steps := s) A hden).eventProb
          {samples |
            frobNorm
              (fun j k =>
                G samples j k - rowSampleGram s A samples j k) ≤ τ}) :
    1 - (1 / ((s : ℝ) * ε ^ 2) + δτ) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => G samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + τ} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let E : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          G samples j k - rowSampleGram s A samples j k) ≤ τ}
  let H : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => G samples j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A + τ}
  have hE : 1 - 1 / ((s : ℝ) * ε ^ 2) ≤ P.eventProb E := by
    simpa [P, E] using
      rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon
        A hden hs ε hε
  have hF : 1 - δτ ≤ P.eventProb F := by
    simpa [P, F] using hpertProb
  have hinter :
      1 - (1 / ((s : ℝ) * ε ^ 2) + δτ) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F (1 / ((s : ℝ) * ε ^ 2)) δτ hE hF
  have hsubset : E ∩ F ⊆ H := by
    intro samples hsamples
    have hExact : frobNorm
        (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A := hsamples.1
    have hPert : frobNorm
        (fun j k =>
          G samples j k - rowSampleGram s A samples j k) ≤ τ := hsamples.2
    have htri :=
      frobNorm_add_le
        (fun j k => rowSampleGram s A samples j k - rowGram A j k)
        (fun j k => G samples j k - rowSampleGram s A samples j k)
    have hsame :
        (fun j k => G samples j k - rowGram A j k) =
          fun j k =>
            (rowSampleGram s A samples j k - rowGram A j k) +
              (G samples j k - rowSampleGram s A samples j k) := by
      funext j k
      ring
    have htotal :
        frobNorm
          (fun j k => G samples j k - rowGram A j k) ≤
          frobNorm
            (fun j k => rowSampleGram s A samples j k - rowGram A j k) +
          frobNorm
            (fun j k =>
              G samples j k - rowSampleGram s A samples j k) := by
      simpa [hsame] using htri
    exact htotal.trans (add_le_add hExact hPert)
  exact hinter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- High-probability floating-point equation (5) for an arbitrary perturbed row
    sketch. If the perturbation `BᵀB - ÃᵀÃ` is at most `τ` with probability at
    least `1 - δτ`, then the total Gram error is at most
    `ε ||A||_F² + τ` with probability at least
    `1 - (1 / (s ε²) + δτ)`. -/
theorem rowSqNormTraceProbability_eventProb_rowSketchGram_frob_error_le_epsilon_add_tau
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (Bhat : RowTrace m s → Fin s → Fin n → ℝ)
    (ε τ δτ : ℝ) (hε : 0 < ε)
    (hpertProb :
      1 - δτ ≤
        (rowSqNormTraceProbability (steps := s) A hden).eventProb
          {samples |
            frobNorm
              (fun j k =>
                rowSketchGram (Bhat samples) j k -
                  rowSampleGram s A samples j k) ≤ τ}) :
    1 - (1 / ((s : ℝ) * ε ^ 2) + δτ) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + τ} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let E : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          rowSketchGram (Bhat samples) j k -
            rowSampleGram s A samples j k) ≤ τ}
  let G : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A + τ}
  have hE : 1 - 1 / ((s : ℝ) * ε ^ 2) ≤ P.eventProb E := by
    simpa [P, E] using
      rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon
        A hden hs ε hε
  have hF : 1 - δτ ≤ P.eventProb F := by
    simpa [P, F] using hpertProb
  have hinter :
      1 - (1 / ((s : ℝ) * ε ^ 2) + δτ) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F (1 / ((s : ℝ) * ε ^ 2)) δτ hE hF
  have hsubset : E ∩ F ⊆ G := by
    intro samples hsamples
    have hExact : frobNorm
        (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A := hsamples.1
    have hPert : frobNorm
        (fun j k =>
          rowSketchGram (Bhat samples) j k -
            rowSampleGram s A samples j k) ≤ τ := hsamples.2
    have htri :=
      frobNorm_add_le
        (fun j k => rowSampleGram s A samples j k - rowGram A j k)
        (fun j k =>
          rowSketchGram (Bhat samples) j k -
            rowSampleGram s A samples j k)
    have hsame :
        (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) =
          fun j k =>
            (rowSampleGram s A samples j k - rowGram A j k) +
              (rowSketchGram (Bhat samples) j k -
                rowSampleGram s A samples j k) := by
      funext j k
      ring
    have htotal :
        frobNorm
          (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) ≤
          frobNorm
            (fun j k => rowSampleGram s A samples j k - rowGram A j k) +
          frobNorm
            (fun j k =>
              rowSketchGram (Bhat samples) j k -
                rowSampleGram s A samples j k) := by
      simpa [hsame] using htri
    exact htotal.trans (add_le_add hExact hPert)
  exact hinter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Floating-point high-probability equation (5): the exact sampling term is
    unchanged, and floating-point arithmetic contributes the perturbation event
    for `fl(Ã)ᵀ fl(Ã) - ÃᵀÃ`. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε τ δτ : ℝ) (hε : 0 < ε)
    (hpertProb :
      1 - δτ ≤
        (rowSqNormTraceProbability (steps := s) A hden).eventProb
          {samples |
            frobNorm
              (fun j k =>
                fl_rowSampleGram fp s A samples j k -
                  rowSampleGram s A samples j k) ≤ τ}) :
    1 - (1 / ((s : ℝ) * ε ^ 2) + δτ) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + τ} := by
  simpa [fl_rowSampleGram, rowSketchGram] using
    rowSqNormTraceProbability_eventProb_rowSketchGram_frob_error_le_epsilon_add_tau
      A hden hs (fun samples => fl_rowSampleSketch fp s A samples)
      ε τ δτ hε hpertProb

/-- Deterministic-perturbation version of the floating-point high-probability
    equation (5). If the floating-point Gram perturbation is always at most
    `τ`, the failure probability remains the exact sampling failure
    `1 / (s ε²)`. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_forall
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε τ : ℝ) (hε : 0 < ε)
    (hpert : ∀ samples : RowTrace m s,
      frobNorm
        (fun j k =>
          fl_rowSampleGram fp s A samples j k -
            rowSampleGram s A samples j k) ≤ τ) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + τ} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          fl_rowSampleGram fp s A samples j k -
            rowSampleGram s A samples j k) ≤ τ}
  have hF_eq : F = Set.univ := by
    ext samples
    simp [F, hpert samples]
  have hpertProb : 1 - (0 : ℝ) ≤ P.eventProb F := by
    rw [hF_eq, FiniteProbability.eventProb_univ]
    linarith
  have h :=
    rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau
      fp A hden hs ε τ 0 hε (by simpa [P, F] using hpertProb)
  simpa using h

/-- High-probability floating-point equation (5) from entrywise sampled-sketch
    stability plus an explicit deterministic Gram-perturbation budget. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_entrywise_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε τ : ℝ) (hε : 0 < ε)
    (hentry : ∀ (samples : RowTrace m s) (t : Fin s) (j : Fin n),
      |fl_rowSampleSketch fp s A samples t j -
        rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * fp.u)
    (hbudget : ∀ samples : RowTrace m s,
      frobNorm
        (fun j k =>
          (2 * fp.u + fp.u ^ 2) *
            ∑ t : Fin s,
              |rowSampleSketch s A samples t j| *
                |rowSampleSketch s A samples t k|) ≤ τ) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + τ} := by
  apply
    rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_forall
      fp A hden hs ε τ hε
  intro samples
  have hpoint :=
    rowSampleGram_frob_error_bound_of_entrywise
      s A samples (fl_rowSampleSketch fp s A samples)
      fp.u fp.u_nonneg (hentry samples)
  simpa [fl_rowSampleGram, rowSketchGram] using hpoint.trans (hbudget samples)

/-- High-probability floating-point equation (5) with no user-supplied
    perturbation event or budget. The exact sampling failure probability is
    unchanged; floating point adds the explicit deterministic budget
    `rowSampleGramFpPerturbBudget fp A`.

    The proof uses the product-law support theorem to apply the floating-point
    division model only on positive-probability sampled rows. Zero-probability
    traces contribute no probability mass. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_explicit_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + rowSampleGramFpPerturbBudget fp A} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb A samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          fl_rowSampleGram fp s A samples j k -
            rowSampleGram s A samples j k) ≤
        rowSampleGramFpPerturbBudget fp A}
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) A hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb A samples := by
      simpa [Good] using hgood
    have hentry : ∀ t : Fin s, ∀ j : Fin n,
        |fl_rowSampleSketch fp s A samples t j -
          rowSampleSketch s A samples t j| ≤
          |rowSampleSketch s A samples t j| * fp.u := by
      intro t j
      have hprob : 0 < rowSqNormProb A (samples t) := hgood_pos t
      exact fl_rowSampleSketch_error_bound fp s A samples t j
        (rowSampleScaleDen_ne_zero s A (samples t) hs hprob)
    have hpoint :=
      rowSampleGram_frob_error_bound_of_entrywise
        s A samples (fl_rowSampleSketch fp s A samples)
        fp.u fp.u_nonneg hentry
    have hbudget :=
      rowSampleGram_perturb_budget_le_explicit fp A hden hs samples
    simpa [F, fl_rowSampleGram, rowSketchGram] using hpoint.trans hbudget
  have hpertProb :
      1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have h :=
    rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau
      fp A hden hs ε (rowSampleGramFpPerturbBudget fp A) 0 hε
      (by simpa [P, F] using hpertProb)
  simpa using h

/-- Scaling-only floating-point high-probability equation (5).  This is the
    model where Algorithm 2 forms the sampled-and-scaled rows in floating point,
    but the Gram matrix is a mathematical object formed exactly from those
    rounded rows.  Thus the dot-product budget is zero, and the only FP term is
    the row-rescaling division budget. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_scaling_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A +
                (n : ℝ) * ((2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A)} := by
  have h :=
    rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_explicit_budget
      fp A hden hs ε hε
  simpa [rowSampleGramFpPerturbBudget_eq_nat_mul fp A] using h

/-- Scaling-only floating-point high-probability equation (5), written as the
    `tau_dot = 0` specialization.  This is the practical model where Algorithm
    2 computes the sampled-and-scaled rows in floating point, while the Gram
    matrix is used only as an exact mathematical object in the analysis of that
    rounded sketch. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_dot_zero
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A +
                ((n : ℝ) * ((2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A) + 0)} := by
  simpa using
    rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_scaling_budget
      fp A hden hs ε hε

/-- Fully floating-point high-probability equation (5), reusing the library dot
    product theorem for the Gram computation. The deterministic FP budget has
    two modular pieces: row-rescaling division error and dot-product evaluation
    error for the Gram entries. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s)
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGramDot fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A +
                rowSampleGramFullFpPerturbBudget fp s A} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb A samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          fl_rowSampleGramDot fp s A samples j k -
            rowSampleGram s A samples j k) ≤
        rowSampleGramFullFpPerturbBudget fp s A}
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) A hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb A samples := by
      simpa [Good] using hgood
    have hentry : ∀ t : Fin s, ∀ j : Fin n,
        |fl_rowSampleSketch fp s A samples t j -
          rowSampleSketch s A samples t j| ≤
          |rowSampleSketch s A samples t j| * fp.u := by
      intro t j
      have hprob : 0 < rowSqNormProb A (samples t) := hgood_pos t
      exact fl_rowSampleSketch_error_bound fp s A samples t j
        (rowSampleScaleDen_ne_zero s A (samples t) hs hprob)
    simpa [F] using
      fl_rowSampleGramDot_perturb_bound_of_entrywise
        fp A hden hs hγ samples hentry
  have hpertProb :
      1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have h :=
    rowSqNormTraceProbability_eventProb_computedGram_frob_error_le_epsilon_add_tau
      A hden hs (fun samples => fl_rowSampleGramDot fp s A samples)
      ε (rowSampleGramFullFpPerturbBudget fp s A) 0 hε
      (by simpa [P, F] using hpertProb)
  simpa using h

/-- High-probability equation (5) for the computed-denominator Algorithm 2
    path, with exact Gram arithmetic after the rounded sketch.  The sampling
    law is unchanged; the additive FP radius is the proved deterministic
    computed-denominator row-scaling budget. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGramWithComputedDen_frob_error_le_epsilon_add_explicit_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k =>
              fl_rowSampleGramWithComputedDen fp A dhat.den samples j k -
                rowGram A j k) ≤
              ε * rowSqNormProbDen A +
                rowSampleGramComputedDenScalePerturbBudget fp s A dhat} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb A samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          fl_rowSampleGramWithComputedDen fp A dhat.den samples j k -
            rowSampleGram s A samples j k) ≤
        rowSampleGramComputedDenScalePerturbBudget fp s A dhat}
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) A hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb A samples := by
      simpa [Good] using hgood
    simpa [F] using
      fl_rowSampleGramWithComputedDen_perturb_bound
        fp A hden hs dhat samples hgood_pos
  have hpertProb :
      1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have h :=
    rowSqNormTraceProbability_eventProb_computedGram_frob_error_le_epsilon_add_tau
      A hden hs
      (fun samples => fl_rowSampleGramWithComputedDen fp A dhat.den samples)
      ε (rowSampleGramComputedDenScalePerturbBudget fp s A dhat) 0 hε
      (by simpa [P, F] using hpertProb)
  simpa using h

/-- Fully floating-point high-probability equation (5) for the
    computed-denominator Algorithm 2 path.  This charges denominator
    computation, rounded row scaling, and floating-point dot products for the
    Gram entries. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGramDotWithComputedDen_frob_error_le_epsilon_add_explicit_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k =>
              fl_rowSampleGramDotWithComputedDen fp A dhat.den samples j k -
                rowGram A j k) ≤
              ε * rowSqNormProbDen A +
                rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb A samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          fl_rowSampleGramDotWithComputedDen fp A dhat.den samples j k -
            rowSampleGram s A samples j k) ≤
        rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat}
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) A hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb A samples := by
      simpa [Good] using hgood
    simpa [F] using
      fl_rowSampleGramDotWithComputedDen_perturb_bound
        fp A hden hs hγ dhat samples hgood_pos
  have hpertProb :
      1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have h :=
    rowSqNormTraceProbability_eventProb_computedGram_frob_error_le_epsilon_add_tau
      A hden hs
      (fun samples => fl_rowSampleGramDotWithComputedDen fp A dhat.den samples)
      ε (rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat) 0 hε
      (by simpa [P, F] using hpertProb)
  simpa using h

end NumStability
