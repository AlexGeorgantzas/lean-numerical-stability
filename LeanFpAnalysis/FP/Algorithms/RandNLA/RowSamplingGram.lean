-- Algorithms/RandNLA/RowSamplingGram.lean
--
-- Gram-matrix expectation and stability consequences for Algorithm 2 of
-- Drineas--Mahoney's CACM RandNLA survey.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Algorithms.RandNLA.RowSampling

namespace LeanFpAnalysis.FP

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

/-- Exact sampled Gram matrix `(ÃᵀÃ)` for an Algorithm 2 trace. -/
noncomputable def rowSampleGram {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ t : Fin steps,
    rowSampleSketch s A samples t j * rowSampleSketch s A samples t k

/-- Floating-point sampled Gram matrix formed from the rounded sampled sketch. -/
noncomputable def fl_rowSampleGram (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ t : Fin steps,
    fl_rowSampleSketch fp s A samples t j *
      fl_rowSampleSketch fp s A samples t k

-- ============================================================
-- Marginals of the independent row trace product law
-- ============================================================

/-- Under the independent product row-trace law, a function of one sampled row
    has expectation equal to its one-step row expectation. -/
theorem rowSqNormTraceProbMass_marginal_one {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : rowSqNormProbDen A ≠ 0)
    (t0 : Fin steps) (f : Fin m → ℝ) :
    (∑ samples : RowTrace m steps,
      rowSqNormTraceProbMass A samples * f (samples t0)) =
      ∑ i : Fin m, rowSqNormProb A i * f i := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (RowSample m)))
      (f := fun t x =>
        if t = t0 then rowSqNormProb A x * f x else rowSqNormProb A x)
  have hleft :
      (∏ t : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (RowSample m)),
          (if t = t0 then rowSqNormProb A x * f x else rowSqNormProb A x)) =
        ∑ i : Fin m, rowSqNormProb A i * f i := by
    simp [rowSqNormProb_sum_eq_one A hden]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (RowSample m))),
        ∏ i, (if i = t0 then rowSqNormProb A (x i) * f (x i)
          else rowSqNormProb A (x i)))
        = ∑ samples : RowTrace m steps,
          rowSqNormTraceProbMass A samples * f (samples t0) := by
    simp [rowSqNormTraceProbMass, RowTrace]
    apply Finset.sum_congr rfl
    intro x _
    have h1 := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t0
      (fun i : Fin steps =>
        if i = t0 then rowSqNormProb A (x i) * f (x i)
        else rowSqNormProb A (x i))
      (by intro h; simp at h)
    have h2 := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t0
      (fun i : Fin steps => rowSqNormProb A (x i))
      (by intro h; simp at h)
    simp at h1 h2
    rw [h1, h2]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t0},
          (if x_1 = t0 then rowSqNormProb A (x x_1) * f (x x_1)
          else rowSqNormProb A (x x_1))) =
        ∏ x_1 ∈ Finset.univ \ {t0}, rowSqNormProb A (x x_1) := by
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

/-- Elementwise unbiasedness of Algorithm 2's Gram estimator with the
    norm-squared row distribution of equation (4):
    `E[(ÃᵀÃ)_{jk}] = (AᵀA)_{jk}`. -/
theorem rowSqNormTraceProbability_expectationReal_rowSampleGram_entry
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (j k : Fin n) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => rowSampleGram s A samples j k) =
      rowGram A j k := by
  classical
  unfold rowSampleGram rowGram
  rw [FiniteProbability.expectationReal_sum]
  calc
    (∑ t : Fin s,
      (rowSqNormTraceProbability (steps := s) A hden).expectationReal
        (fun ω => rowSampleSketch s A ω t j * rowSampleSketch s A ω t k))
        = ∑ t : Fin s,
            ∑ i : Fin m, rowSqNormProb A i *
              (rowSampleIncrement s A i j * rowSampleIncrement s A i k) := by
          apply Finset.sum_congr rfl
          intro t _
          unfold FiniteProbability.expectationReal rowSqNormTraceProbability
            rowSampleSketch
          exact rowSqNormTraceProbMass_marginal_one A hden.ne' t
            (fun i => rowSampleIncrement s A i j * rowSampleIncrement s A i k)
    _ = ∑ t : Fin s, ∑ i : Fin m, (A i j * A i k) / (s : ℝ) := by
          apply Finset.sum_congr rfl
          intro t _
          apply Finset.sum_congr rfl
          intro i _
          exact rowSqNormProb_mul_rowSampleIncrement_mul_eq s A hden hs i j k
    _ = ∑ i : Fin m, A i j * A i k := by
          rw [Finset.sum_const]
          simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          field_simp [ne_of_gt hs]

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

-- ============================================================
-- Expected Gram perturbation from sampled-sketch stability
-- ============================================================

/-- Expected entrywise bias of a perturbed sampled Gram matrix. If every entry
    of a row sketch `Bhat` is within relative error `u` of the exact Algorithm 2
    sampled sketch, then the expected bias of the Gram entry is bounded by the
    expected deterministic Gram perturbation. -/
theorem rowSqNormTraceProbability_expectationReal_rowSketchGram_entry_bias_bound_of_entrywise
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (Bhat : RowTrace m s → Fin s → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ samples t j,
      |Bhat samples t j - rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * u)
    (j k : Fin n) :
    |(rowSqNormTraceProbability (steps := s) A hden).expectationReal
        (fun samples => rowSketchGram (Bhat samples) j k) -
      rowGram A j k| ≤
      (2 * u + u ^ 2) *
        (rowSqNormTraceProbability (steps := s) A hden).expectationReal
          (fun samples =>
            ∑ t : Fin s,
              |rowSampleSketch s A samples t j| *
                |rowSampleSketch s A samples t k|) := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let diff : RowTrace m s → ℝ := fun samples =>
    rowSketchGram (Bhat samples) j k - rowSampleGram s A samples j k
  have hunbiased :=
    rowSqNormTraceProbability_expectationReal_rowSampleGram_entry
      A hden hs j k
  have hsplit :
      P.expectationReal (fun samples => rowSketchGram (Bhat samples) j k) -
        rowGram A j k =
      P.expectationReal diff := by
    unfold diff P
    rw [FiniteProbability.expectationReal_sub]
    rw [hunbiased]
  calc
    |P.expectationReal (fun samples => rowSketchGram (Bhat samples) j k) -
        rowGram A j k|
        = |P.expectationReal diff| := by rw [hsplit]
    _ ≤ P.expectationReal (fun samples => |diff samples|) :=
        FiniteProbability.abs_expectationReal_le_expectationReal_abs P diff
    _ ≤ P.expectationReal
          (fun samples =>
            (2 * u + u ^ 2) *
              ∑ t : Fin s,
                |rowSampleSketch s A samples t j| *
                  |rowSampleSketch s A samples t k|) := by
        apply FiniteProbability.expectationReal_mono
        intro samples
        unfold diff rowSketchGram
        exact rowSampleGram_entry_error_bound_of_entrywise
          s A samples (Bhat samples) u hu (hentry samples) j k
    _ = (2 * u + u ^ 2) *
        P.expectationReal
          (fun samples =>
            ∑ t : Fin s,
              |rowSampleSketch s A samples t j| *
                |rowSampleSketch s A samples t k|) := by
        rw [FiniteProbability.expectationReal_const_mul]

/-- Floating-point sampled-Gram bias bound, stated directly for the rounded
    Algorithm 2 sketch. The entrywise sampled-sketch stability assumption is
    explicit; `fl_rowSampleSketch_error_bound` supplies it whenever the sampled
    row-scale denominators are nonzero. -/
theorem rowSqNormTraceProbability_expectationReal_fl_rowSampleGram_entry_bias_bound_of_entrywise
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hentry : ∀ (samples : RowTrace m s) (t : Fin s) (j : Fin n),
      |fl_rowSampleSketch fp s A samples t j -
        rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * fp.u)
    (j k : Fin n) :
    |(rowSqNormTraceProbability (steps := s) A hden).expectationReal
        (fun samples => fl_rowSampleGram fp s A samples j k) -
      rowGram A j k| ≤
      (2 * fp.u + fp.u ^ 2) *
        (rowSqNormTraceProbability (steps := s) A hden).expectationReal
          (fun samples =>
            ∑ t : Fin s,
              |rowSampleSketch s A samples t j| *
                |rowSampleSketch s A samples t k|) := by
  simpa [fl_rowSampleGram, rowSketchGram] using
    rowSqNormTraceProbability_expectationReal_rowSketchGram_entry_bias_bound_of_entrywise
      A hden hs (fun samples => fl_rowSampleSketch fp s A samples)
      fp.u fp.u_nonneg hentry j k

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

end LeanFpAnalysis.FP
