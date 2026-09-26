import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.HitCounts.Bounds
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.Elementwise.Core
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm01.ElementwiseSampling.Sampling

/-!
# NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm01.ElementwiseSampling.HitCountConcentration

W11 canonical source correspondence destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.HitCountConcentration`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/HitCountConcentration.lean
--
-- Elementary finite-probability concentration for the Algorithm 1 hit counter.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602










namespace NumStability

open scoped BigOperators

/-!
## Concentration for the element-wise sampling hit counter

This file adds a small finite-probability layer around the deterministic
Algorithm 1 trace formalization from Drineas and Mahoney's CACM RandNLA
survey (https://dl.acm.org/doi/10.1145/2842602). It proves a marginal-only
Markov upper-tail
bound, a pairwise-independence Chebyshev bound around the mean, and Chernoff
upper-tail bounds for

`qᵢⱼ = hitCount samples i j`.

If every sample step hits `(i, j)` with marginal probability `pᵢⱼ`, then
`E qᵢⱼ = steps * pᵢⱼ`, so Markov gives

`Pr(qᵢⱼ ≤ Q) ≥ 1 - steps * pᵢⱼ / (Q + 1)`.

With pairwise independence of distinct hit indicators, Chebyshev also gives an
around-mean bound for `|qᵢⱼ - steps * pᵢⱼ|`. For the canonical independent
Algorithm 1 sampler with squared-magnitude probabilities, Lean constructs the
finite product trace law and proves the Chernoff MGF bound from that law. This
gives both a tunable fixed-parameter budget and the optimized exponent obtained
from `lam = log((Q+1)/(steps*pᵢⱼ))`. Specializing `pᵢⱼ` to `sqMagProb A i j`
then gives high-probability stability theorems by composing these counter
bounds with the deterministic stability transfer.
-/

-- ============================================================
-- Hit-count expectation and concentration
-- ============================================================















































































































































































































































































































































































































































































-- ============================================================
-- The canonical independent squared-magnitude trace distribution
-- ============================================================












/-- The squared-magnitude probabilities sum to one over sampled pairs. -/
theorem sqMagProb_sum_samples_eq_one {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0) :
    (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2) = 1 := by
  change (∑ x : Fin m × Fin n, sqMagProb A x.1 x.2) = 1
  rw [← sqMagProb_sum_eq_one A hden]
  have h := Finset.sum_product
    (s := (Finset.univ : Finset (Fin m)))
    (t := (Finset.univ : Finset (Fin n)))
    (f := fun x : Fin m × Fin n => sqMagProb A x.1 x.2)
  simpa using h









theorem sqMagTraceProbMass_sum_eq_one {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0) :
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples) = 1 := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n)))
      (f := fun _ x => sqMagProb A x.1 x.2)
  have hleft :
      (∏ _ : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (ElementwiseSample m n)),
          sqMagProb A x.1 x.2) = 1 := by
    simp [sqMagProb_sum_samples_eq_one A hden]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n))),
        ∏ i, sqMagProb A (x i).1 (x i).2)
        = ∑ samples : ElementwiseTrace m n steps,
          sqMagTraceProbMass A samples := by
    simp [sqMagTraceProbMass, ElementwiseTrace]
  rw [← hright, ← hprod]
  exact hleft

/-- Under the independent product trace law, a function of one sampled entry
    has expectation equal to its one-step entry expectation. -/
theorem sqMagTraceProbMass_marginal_one {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0)
    (t0 : Fin steps) (f : ElementwiseSample m n → ℝ) :
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples * f (samples t0)) =
      ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n)))
      (f := fun t x =>
        if t = t0 then sqMagProb A x.1 x.2 * f x
        else sqMagProb A x.1 x.2)
  have hleft :
      (∏ t : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (ElementwiseSample m n)),
          (if t = t0 then sqMagProb A x.1 x.2 * f x
          else sqMagProb A x.1 x.2)) =
        ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x := by
    simp [sqMagProb_sum_samples_eq_one A hden]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n))),
        ∏ i, (if i = t0 then sqMagProb A (x i).1 (x i).2 * f (x i)
          else sqMagProb A (x i).1 (x i).2))
        = ∑ samples : ElementwiseTrace m n steps,
          sqMagTraceProbMass A samples * f (samples t0) := by
    simp [sqMagTraceProbMass, ElementwiseTrace]
    apply Finset.sum_congr rfl
    intro x _
    have h1 := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t0
      (fun i : Fin steps =>
        if i = t0 then sqMagProb A (x i).1 (x i).2 * f (x i)
        else sqMagProb A (x i).1 (x i).2)
      (by intro h; simp at h)
    have h2 := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t0
      (fun i : Fin steps => sqMagProb A (x i).1 (x i).2)
      (by intro h; simp at h)
    simp at h1 h2
    rw [h1, h2]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t0},
          (if x_1 = t0 then sqMagProb A (x x_1).1 (x x_1).2 * f (x x_1)
          else sqMagProb A (x x_1).1 (x x_1).2)) =
        ∏ x_1 ∈ Finset.univ \ {t0}, sqMagProb A (x x_1).1 (x x_1).2 := by
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















































































































































































/-- The canonical finite probability space for Algorithm 1 traces with
    independent squared-magnitude samples at every step. -/
noncomputable def sqMagTraceProbability {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A) :
    FiniteProbability (ElementwiseTrace m n steps) where
  prob := sqMagTraceProbMass A
  prob_nonneg := sqMagTraceProbMass_nonneg A hden
  prob_sum := sqMagTraceProbMass_sum_eq_one A hden.ne'

/-- Expectation form of `sqMagTraceProbMass_marginal_one` for the canonical
    finite probability space.  This is the reusable product-law adapter for
    lifting one-step calculations to any fixed trace coordinate. -/
theorem sqMagTraceProbability_expectationReal_step_eq {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (t0 : Fin steps) (f : ElementwiseSample m n → ℝ) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples => f (samples t0)) =
      ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x := by
  simpa [FiniteProbability.expectationReal, sqMagTraceProbability] using
    sqMagTraceProbMass_marginal_one A hden.ne' t0 f




















/-- The independent Algorithm 1 elementwise sampler assigns probability one to
    traces whose sampled entries all have positive squared-magnitude
    probability. -/
theorem sqMagTraceProbability_eventProb_elementwiseTracePositiveProb
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) :
    (sqMagTraceProbability (steps := steps) A hden).eventProb
      {samples | elementwiseTracePositiveProb A samples} = 1 := by
  classical
  let P := sqMagTraceProbability (steps := steps) A hden
  let Good : Set (ElementwiseTrace m n steps) :=
    {samples | elementwiseTracePositiveProb A samples}
  have hcompl_zero : P.eventProb Goodᶜ = 0 := by
    unfold FiniteProbability.eventProb
    apply Finset.sum_eq_zero
    intro samples _
    by_cases hbad : samples ∈ Goodᶜ
    · have hnot_good : samples ∉ Good := by simpa using hbad
      have hexists :
          ∃ t : Fin steps,
            sqMagProb A (samples t).1 (samples t).2 = 0 := by
        by_contra hno
        have hgood : samples ∈ Good := by
          intro t
          have hne : sqMagProb A (samples t).1 (samples t).2 ≠ 0 := by
            intro hzero
            exact hno ⟨t, hzero⟩
          exact lt_of_le_of_ne
            (sqMagProb_nonneg A hden (samples t).1 (samples t).2)
            (Ne.symm hne)
        exact hnot_good hgood
      have hmass :=
        sqMagTraceProbMass_eq_zero_of_exists_prob_zero A samples hexists
      simp [P, Good, sqMagTraceProbability, hbad, hmass]
    · simp [hbad]
  have hsplit := P.eventProb_add_eventProb_compl Good
  rw [hcompl_zero] at hsplit
  linarith

/-- In the canonical independent trace law, each step hits entry `(i, j)` with
    probability `pᵢⱼ = sqMagProb A i j`. -/
theorem sqMagTraceProbability_eventProb_sampleHits {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (t : Fin steps) (i : Fin m) (j : Fin n) :
    (sqMagTraceProbability (steps := steps) A hden).eventProb
      {samples | sampleHits samples t i j} =
      sqMagProb A i j := by
  classical
  let f : ElementwiseSample m n → ℝ :=
    fun x => if x.1 = i ∧ x.2 = j then 1 else 0
  have hmarg :=
    sqMagTraceProbMass_marginal_one A hden.ne' t f
  have hleft :
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples | sampleHits samples t i j} =
        ∑ samples : ElementwiseTrace m n steps,
          sqMagTraceProbMass A samples * f (samples t) := by
    unfold FiniteProbability.eventProb sqMagTraceProbability f sampleHits
    apply Finset.sum_congr rfl
    intro samples _
    by_cases h : (samples t).1 = i ∧ (samples t).2 = j <;> simp [h]
  have hright :
      (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x) =
        sqMagProb A i j := by
    rw [Finset.sum_eq_single (i, j)]
    · simp [f]
    · intro x _ hx
      have hnot : ¬ (x.1 = i ∧ x.2 = j) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      simp [f, hnot]
    · intro hnot
      simp at hnot
  rw [hleft, hmarg, hright]






















































/-- Expected hit count under the canonical independent Algorithm 1 trace law. -/
theorem sqMagTraceProbability_expectationReal_hitCount_eq {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples => (hitCount samples i j : ℝ)) =
      (steps : ℝ) * sqMagProb A i j := by
  exact expectationReal_hitCount_eq_steps_mul_hitProb
    (sqMagTraceProbability (steps := steps) A hden)
    (fun samples => samples) i j (sqMagProb A i j)
    (fun t => sqMagTraceProbability_eventProb_sampleHits A hden t i j)

/-- Nonzero-entry unbiasedness for the exact Algorithm 1 trace estimator under
    the canonical independent squared-magnitude trace law.  The trace length
    `steps` and the update denominator `s` are linked by `steps = s`. -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceSketch_nonzero_entry
    {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) (hsteps : steps = s)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples => elementwiseTraceSketch s A (fun _ _ => 0) samples i j) =
      A i j := by
  let P := sqMagTraceProbability (steps := steps) A hden
  let c : ℝ := frobNormSqRect A / ((s : ℝ) * A i j)
  have hpoint : ∀ samples : ElementwiseTrace m n steps,
      elementwiseTraceSketch s A (fun _ _ => 0) samples i j =
        (hitCount samples i j : ℝ) * c := by
    intro samples
    have h :=
      elementwiseTraceSketch_sqMag_eq s A (fun _ _ => 0) samples i j hs hAij
    simpa [c] using h
  have hE :
      P.expectationReal
        (fun samples : ElementwiseTrace m n steps =>
          elementwiseTraceSketch s A (fun _ _ => 0) samples i j) =
        P.expectationReal
          (fun samples : ElementwiseTrace m n steps =>
            (hitCount samples i j : ℝ) * c) := by
    apply Finset.sum_congr rfl
    intro samples _
    simp [hpoint samples]
  have hhit :
      P.expectationReal
        (fun samples : ElementwiseTrace m n steps => (hitCount samples i j : ℝ)) =
        (steps : ℝ) * sqMagProb A i j :=
    sqMagTraceProbability_expectationReal_hitCount_eq A hden i j
  have hconst :
      P.expectationReal
        (fun samples : ElementwiseTrace m n steps =>
          (hitCount samples i j : ℝ) * c) =
        ((steps : ℝ) * sqMagProb A i j) * c := by
    rw [FiniteProbability.expectationReal_mul_const, hhit]
  rw [hE, hconst]
  have hF : frobNormSqRect A ≠ 0 := by
    simpa [sqMagProbDen] using hden.ne'
  unfold c sqMagProb sqMagProbDen
  rw [hsteps]
  field_simp [hs, hAij]













/-- Zero-entry unbiasedness for the exact Algorithm 1 trace estimator. -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceSketch_zero_entry
    {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) (hAij : A i j = 0) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples => elementwiseTraceSketch s A (fun _ _ => 0) samples i j) =
      A i j := by
  classical
  unfold FiniteProbability.expectationReal
  simp [elementwiseTraceSketch_zero_init_of_entry_eq_zero s A, hAij]

/-- Entrywise unbiasedness for the exact Algorithm 1 trace estimator under the
    canonical independent squared-magnitude trace law.  The trace length
    `steps` and the algorithm parameter `s` are linked by `steps = s`. -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceSketch_entry
    {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) (hsteps : steps = s)
    (hs : (s : ℝ) ≠ 0) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples => elementwiseTraceSketch s A (fun _ _ => 0) samples i j) =
      A i j := by
  by_cases hAij_zero : A i j = 0
  · exact sqMagTraceProbability_expectationReal_elementwiseTraceSketch_zero_entry
      s A hden i j hAij_zero
  · exact sqMagTraceProbability_expectationReal_elementwiseTraceSketch_nonzero_entry
      s A hden i j hsteps hs hAij_zero

/-- Matrix form of Algorithm 1 unbiasedness for the exact trace estimator,
    stated entrywise as an equality of matrices. -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceSketch_matrix
    {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hsteps : steps = s) (hs : (s : ℝ) ≠ 0) :
    (fun i j =>
      (sqMagTraceProbability (steps := steps) A hden).expectationReal
        (fun samples => elementwiseTraceSketch s A (fun _ _ => 0) samples i j)) =
      A := by
  funext i j
  exact sqMagTraceProbability_expectationReal_elementwiseTraceSketch_entry
    s A hden i j hsteps hs

/-- The one-step exponential moment for a single squared-magnitude sample. -/
theorem sqMag_sampleHitIndicator_exp_sum {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0)
    (i : Fin m) (j : Fin n) (lam : ℝ) :
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * sampleHitIndicator x i j)) =
      1 + sqMagProb A i j * (Real.exp lam - 1) := by
  classical
  let p : ElementwiseSample m n → ℝ := fun x => sqMagProb A x.1 x.2
  have hsum : (∑ x : ElementwiseSample m n, p x) = 1 := by
    simpa [p] using sqMagProb_sum_samples_eq_one A hden
  have hrewrite : ∀ x : ElementwiseSample m n,
      p x * Real.exp (lam * sampleHitIndicator x i j) =
        p x + (if x.1 = i ∧ x.2 = j then p x * (Real.exp lam - 1) else 0) := by
    intro x
    by_cases h : x.1 = i ∧ x.2 = j
    · simp [p, sampleHitIndicator, h]
      ring
    · simp [p, sampleHitIndicator, h]
  calc
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * sampleHitIndicator x i j))
        = ∑ x : ElementwiseSample m n,
            (p x + (if x.1 = i ∧ x.2 = j then p x * (Real.exp lam - 1) else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            simpa [p] using hrewrite x
    _ = (∑ x : ElementwiseSample m n, p x) +
          ∑ x : ElementwiseSample m n,
            (if x.1 = i ∧ x.2 = j then p x * (Real.exp lam - 1) else 0) := by
            rw [Finset.sum_add_distrib]
    _ = 1 + p (i, j) * (Real.exp lam - 1) := by
            rw [hsum]
            congr 1
            rw [Finset.sum_eq_single (i, j)]
            · simp [p]
            · intro b _ hb
              have hnot : ¬ (b.1 = i ∧ b.2 = j) := by
                intro hh
                apply hb
                ext <;> simp [hh.1, hh.2]
              simp [hnot]
            · intro hnot
              simp at hnot
    _ = 1 + sqMagProb A i j * (Real.exp lam - 1) := by
            simp [p]
























































/-- Expectation form of the product-law MGF factorization for an arbitrary
    one-step scalar statistic. -/
theorem sqMagTraceProbability_expectationReal_exp_sum_stepFunction_eq
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) (lam : ℝ) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples =>
        Real.exp (lam * (∑ t : Fin steps, f (samples t)))) =
      (∑ x : ElementwiseSample m n,
        sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ^ steps := by
  simpa [sqMagTraceProbability, FiniteProbability.expectationReal,
    sqMagTraceProbMass] using
    sqMagTraceProbMass_exp_sum_stepFunction_eq
      (steps := steps) A f lam

/-- Exponential-Markov upper tail for a trace-sum of an arbitrary one-step
    scalar statistic, with the product-law MGF evaluated exactly. -/
theorem sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_mul_mgf
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {T lam : ℝ} (hlam : 0 < lam) :
    (sqMagTraceProbability (steps := steps) A hden).eventProb
      {samples |
        T ≤ ∑ t : Fin steps, f (samples t)} ≤
      Real.exp (-(lam * T)) *
        (∑ x : ElementwiseSample m n,
          sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ^ steps := by
  let P := sqMagTraceProbability (steps := steps) A hden
  have hmarkov :=
    FiniteProbability.eventProb_real_ge_le_exp_mul_mgf
      P (fun samples => ∑ t : Fin steps, f (samples t)) (T := T)
      (lam := lam) hlam
  rw [sqMagTraceProbability_expectationReal_exp_sum_stepFunction_eq
    A hden f lam] at hmarkov
  simpa [P] using hmarkov

/-- Lower-probability complement form of
    `sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_mul_mgf`. -/
theorem sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_mul_mgf
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {T lam : ℝ} (hlam : 0 < lam) :
    1 - Real.exp (-(lam * T)) *
        (∑ x : ElementwiseSample m n,
          sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ^ steps ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples |
          ∑ t : Fin steps, f (samples t) ≤ T} := by
  let P := sqMagTraceProbability (steps := steps) A hden
  have htail :=
    FiniteProbability.eventProb_real_le_ge_one_sub_exp_mul_mgf
      P (fun samples => ∑ t : Fin steps, f (samples t)) (T := T)
      (lam := lam) hlam
  rw [sqMagTraceProbability_expectationReal_exp_sum_stepFunction_eq
    A hden f lam] at htail
  simpa [P] using htail

/-- Exponential-Markov upper tail for a trace-sum from a one-step scalar MGF
    bound.  If `E exp(lam f(X)) <= exp(psi)` for one sampled entry, then the
    independent trace sum has the expected `exp(s*psi - lam*T)` tail. -/
theorem sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_of_one_step_mgf_bound
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {T lam psi : ℝ} (hlam : 0 < lam)
    (hmgf :
      (∑ x : ElementwiseSample m n,
        sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ≤ Real.exp psi) :
    (sqMagTraceProbability (steps := steps) A hden).eventProb
      {samples |
        T ≤ ∑ t : Fin steps, f (samples t)} ≤
      Real.exp ((steps : ℝ) * psi - lam * T) := by
  classical
  let M : ℝ :=
    ∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x)
  have hM_nonneg : 0 ≤ M := by
    unfold M
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (sqMagProb_nonneg A hden x.1 x.2)
        (le_of_lt (Real.exp_pos _))
  have htail :=
    sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_mul_mgf
      (steps := steps) A hden f (T := T) (lam := lam) hlam
  have hpow : M ^ steps ≤ (Real.exp psi) ^ steps :=
    pow_le_pow_left₀ hM_nonneg hmgf steps
  have hmul :
      Real.exp (-(lam * T)) * M ^ steps ≤
        Real.exp (-(lam * T)) * (Real.exp psi) ^ steps :=
    mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hexp :
      Real.exp (-(lam * T)) * (Real.exp psi) ^ steps =
        Real.exp ((steps : ℝ) * psi - lam * T) := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  exact htail.trans (hmul.trans_eq hexp)

/-- Complement form of the scalar trace-sum tail obtained from a one-step MGF
    bound. -/
theorem sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_of_one_step_mgf_bound
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {T lam psi : ℝ} (hlam : 0 < lam)
    (hmgf :
      (∑ x : ElementwiseSample m n,
        sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ≤ Real.exp psi) :
    1 - Real.exp ((steps : ℝ) * psi - lam * T) ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples |
          ∑ t : Fin steps, f (samples t) ≤ T} := by
  classical
  let M : ℝ :=
    ∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x)
  have hM_nonneg : 0 ≤ M := by
    unfold M
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (sqMagProb_nonneg A hden x.1 x.2)
        (le_of_lt (Real.exp_pos _))
  have htail :=
    sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_mul_mgf
      (steps := steps) A hden f (T := T) (lam := lam) hlam
  have hpow : M ^ steps ≤ (Real.exp psi) ^ steps :=
    pow_le_pow_left₀ hM_nonneg hmgf steps
  have hmul :
      Real.exp (-(lam * T)) * M ^ steps ≤
        Real.exp (-(lam * T)) * (Real.exp psi) ^ steps :=
    mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hexp :
      Real.exp (-(lam * T)) * (Real.exp psi) ^ steps =
        Real.exp ((steps : ℝ) * psi - lam * T) := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  linarith

/-- Finite-family complement form of the product-law scalar MGF tail.

This is the union-bound layer needed by finite-cover arguments: if each
one-step statistic `f a` has a scalar MGF bound at parameter `lam a`, then all
corresponding trace sums are below their thresholds simultaneously with the
displayed probability.  This is still scalar MGF infrastructure, not a matrix
Bernstein theorem. -/
theorem sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
    {m n steps : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (f : ι → ElementwiseSample m n → ℝ)
    (T psi lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hmgf : ∀ a,
      (∑ x : ElementwiseSample m n,
        sqMagProb A x.1 x.2 * Real.exp (lam a * f a x)) ≤
        Real.exp (psi a)) :
    1 - ∑ a : ι, Real.exp ((steps : ℝ) * psi a - lam a * T a) ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples |
          ∀ a : ι, ∑ t : Fin steps, f a (samples t) ≤ T a} := by
  classical
  let P := sqMagTraceProbability (steps := steps) A hden
  let E : ι → Set (ElementwiseTrace m n steps) := fun a =>
    {samples | ∑ t : Fin steps, f a (samples t) ≤ T a}
  let δ : ι → ℝ := fun a =>
    Real.exp ((steps : ℝ) * psi a - lam a * T a)
  have hEach : ∀ a : ι, 1 - δ a ≤ P.eventProb (E a) := by
    intro a
    simpa [P, E, δ] using
      sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_of_one_step_mgf_bound
        (steps := steps) A hden (f a) (T := T a) (lam := lam a)
        (psi := psi a) (hlam a) (hmgf a)
  have hAll :=
    FiniteProbability.eventProb_forall_ge_one_sub_sum
      P E δ hEach
  have hset :
      {samples : ElementwiseTrace m n steps |
        ∀ a : ι, samples ∈ E a} =
      {samples : ElementwiseTrace m n steps |
        ∀ a : ι, ∑ t : Fin steps, f a (samples t) ≤ T a} := by
    ext samples
    simp [E]
  simpa [P, E, δ, hset] using hAll

/-- A pointwise upper bound on a one-step statistic gives a one-step scalar MGF
    bound under the squared-magnitude sampling law. -/
theorem sqMagProb_sum_exp_stepFunction_le_exp_of_forall_le
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {lam B : ℝ} (hlam : 0 ≤ lam)
    (hf : ∀ x : ElementwiseSample m n, f x ≤ B) :
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ≤
      Real.exp (lam * B) := by
  classical
  calc
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x))
        ≤ ∑ x : ElementwiseSample m n,
            sqMagProb A x.1 x.2 * Real.exp (lam * B) := by
            apply Finset.sum_le_sum
            intro x _
            have harg : lam * f x ≤ lam * B :=
              mul_le_mul_of_nonneg_left (hf x) hlam
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr harg)
              (sqMagProb_nonneg A hden x.1 x.2)
    _ = (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2) *
          Real.exp (lam * B) := by
            rw [Finset.sum_mul]
    _ = Real.exp (lam * B) := by
            rw [sqMagProb_sum_samples_eq_one A hden.ne']
            ring

/-- A support-aware pointwise upper bound on a one-step statistic gives a
    one-step scalar MGF bound under the squared-magnitude sampling law.

This variant is important for truncated sampling: samples with zero probability
do not need to satisfy the pointwise bound, because their mass is zero in the
one-step law. -/
theorem sqMagProb_sum_exp_stepFunction_le_exp_of_support_forall_le
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {lam B : ℝ} (hlam : 0 ≤ lam)
    (hf : ∀ x : ElementwiseSample m n,
      0 < sqMagProb A x.1 x.2 → f x ≤ B) :
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ≤
      Real.exp (lam * B) := by
  classical
  calc
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x))
        ≤ ∑ x : ElementwiseSample m n,
            sqMagProb A x.1 x.2 * Real.exp (lam * B) := by
            apply Finset.sum_le_sum
            intro x _
            by_cases hpos : 0 < sqMagProb A x.1 x.2
            · have harg : lam * f x ≤ lam * B :=
                mul_le_mul_of_nonneg_left (hf x hpos) hlam
              exact mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr harg)
                (sqMagProb_nonneg A hden x.1 x.2)
            · have hzero : sqMagProb A x.1 x.2 = 0 :=
                le_antisymm (le_of_not_gt hpos)
                  (sqMagProb_nonneg A hden x.1 x.2)
              simp [hzero]
    _ = (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2) *
          Real.exp (lam * B) := by
            rw [Finset.sum_mul]
    _ = Real.exp (lam * B) := by
            rw [sqMagProb_sum_samples_eq_one A hden.ne']
            ring

/-- Finite-family scalar trace-sum tail from pointwise one-step bounds.

This is weaker than a Bernstein/Hoeffding-type MGF estimate, but it is fully
proved from the local squared-magnitude product law and is useful as a
bookkeeping-free finite-test support theorem. -/
theorem sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_pointwise_bound
    {m n steps : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (f : ι → ElementwiseSample m n → ℝ)
    (T B lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hbound : ∀ a x, f a x ≤ B a) :
    1 - ∑ a : ι, Real.exp ((steps : ℝ) * (lam a * B a) - lam a * T a) ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples |
          ∀ a : ι, ∑ t : Fin steps, f a (samples t) ≤ T a} := by
  classical
  exact
    sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
      (steps := steps) A hden f T (fun a => lam a * B a) lam hlam
      (by
        intro a
        exact sqMagProb_sum_exp_stepFunction_le_exp_of_forall_le
          A hden (f a) (le_of_lt (hlam a)) (hbound a))

/-- Finite-family scalar trace-sum tail from support-aware pointwise one-step
    bounds.

The pointwise hypothesis only needs to hold on one-step samples with positive
squared-magnitude probability.  This avoids adding artificial hypotheses for
zero-mass truncated samples. -/
theorem sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_support_pointwise_bound
    {m n steps : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (f : ι → ElementwiseSample m n → ℝ)
    (T B lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hbound : ∀ a x, 0 < sqMagProb A x.1 x.2 → f a x ≤ B a) :
    1 - ∑ a : ι, Real.exp ((steps : ℝ) * (lam a * B a) - lam a * T a) ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples |
          ∀ a : ι, ∑ t : Fin steps, f a (samples t) ≤ T a} := by
  classical
  exact
    sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
      (steps := steps) A hden f T (fun a => lam a * B a) lam hlam
      (by
        intro a
        exact sqMagProb_sum_exp_stepFunction_le_exp_of_support_forall_le
          A hden (f a) (le_of_lt (hlam a)) (hbound a))























/-- Exact moment-generating identity for the hit counter under the canonical
    independent squared-magnitude trace distribution. -/
theorem sqMagTraceProbMass_exp_hitCount_sum_eq {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0)
    (i : Fin m) (j : Fin n) (lam : ℝ) :
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples *
        Real.exp (lam * (hitCount samples i j : ℝ))) =
      (1 + sqMagProb A i j * (Real.exp lam - 1)) ^ steps := by
  classical
  calc
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples *
        Real.exp (lam * (hitCount samples i j : ℝ)))
        = ∑ samples : ElementwiseTrace m n steps,
            ∏ t : Fin steps,
              sqMagProb A (samples t).1 (samples t).2 *
                Real.exp (lam * sampleHitIndicator (samples t) i j) := by
            apply Finset.sum_congr rfl
            intro samples _
            rw [exp_hitCount_eq_prod_sampleHitIndicator]
            simp [sqMagTraceProbMass, Finset.prod_mul_distrib]
    _ = ∏ t : Fin steps,
          ∑ x : ElementwiseSample m n,
            sqMagProb A x.1 x.2 * Real.exp (lam * sampleHitIndicator x i j) := by
            have hprod :=
              Finset.prod_univ_sum
                (t := fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n)))
                (f := fun _ x =>
                  sqMagProb A x.1 x.2 * Real.exp (lam * sampleHitIndicator x i j))
            symm
            simpa [ElementwiseTrace] using hprod
    _ = ∏ _ : Fin steps, (1 + sqMagProb A i j * (Real.exp lam - 1)) := by
            apply Finset.prod_congr rfl
            intro t _
            exact sqMag_sampleHitIndicator_exp_sum A hden i j lam
    _ = (1 + sqMagProb A i j * (Real.exp lam - 1)) ^ steps := by
            simp [Fintype.card_fin]

/-- Exact expectation form of the hit-count MGF identity for the canonical
    independent squared-magnitude trace distribution. -/
theorem sqMagTraceProbability_expectationReal_exp_hitCount_eq {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) (lam : ℝ) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
        (fun samples => Real.exp (lam * (hitCount samples i j : ℝ))) =
      (1 + sqMagProb A i j * (Real.exp lam - 1)) ^ steps := by
  simpa [sqMagTraceProbability, FiniteProbability.expectationReal,
    sqMagTraceProbMass] using
    sqMagTraceProbMass_exp_hitCount_sum_eq
      (steps := steps) A hden.ne' i j lam

-- ============================================================
-- Chernoff concentration from an exponential-moment bound
-- ============================================================

























/-- The Chernoff MGF condition is a theorem for the canonical independent
    Algorithm 1 trace distribution with squared-magnitude sampling. -/
theorem sqMagTraceProbability_chernoff_mgf_bound {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) :
    sqMagHitCountChernoffMGFBound
      (sqMagTraceProbability (steps := steps) A hden)
      A (fun samples => samples) i j := by
  intro lam hlam
  let x : ℝ := sqMagProb A i j * (Real.exp lam - 1)
  have hexact :=
    sqMagTraceProbability_expectationReal_exp_hitCount_eq
      (steps := steps) A hden i j lam
  have hp : 0 ≤ sqMagProb A i j :=
    sqMagProb_nonneg A hden i j
  have hexp_ge_one : 1 ≤ Real.exp lam := by
    have hadd := Real.add_one_le_exp lam
    linarith
  have hx_nonneg : 0 ≤ x := by
    unfold x
    exact mul_nonneg hp (by linarith)
  have hbase_nonneg : 0 ≤ 1 + x := by
    linarith
  have hbase_le_exp : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hpow : (1 + x) ^ steps ≤ (Real.exp x) ^ steps :=
    pow_le_pow_left₀ hbase_nonneg hbase_le_exp steps
  have hexp_pow : (Real.exp x) ^ steps = Real.exp ((steps : ℝ) * x) :=
    (Real.exp_nat_mul x steps).symm
  calc
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
        (fun samples => Real.exp (lam * (hitCount ((fun samples => samples) samples) i j : ℝ)))
        = (1 + sqMagProb A i j * (Real.exp lam - 1)) ^ steps := by
            simpa using hexact
    _ = (1 + x) ^ steps := by
            simp [x]
    _ ≤ (Real.exp x) ^ steps := hpow
    _ = Real.exp ((steps : ℝ) * x) := hexp_pow
    _ = Real.exp ((steps : ℝ) * sqMagProb A i j * (Real.exp lam - 1)) := by
            congr 1
            simp [x]
            ring







































/-- Chernoff concentration for the canonical independent squared-magnitude
    Algorithm 1 sampler, with no abstract MGF hypothesis. -/
theorem hitCount_concentrates_sqMag_chernoff_independent {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) (lam : ℝ) (Q : ℕ) (hlam : 0 < lam) :
    1 - sqMagChernoffHitCountTail steps A i j lam Q ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (hitCountAtMostEvent (fun samples => samples) i j Q) := by
  exact hitCount_concentrates_sqMag_chernoff_of_mgf_bound
    (sqMagTraceProbability (steps := steps) A hden) A
    (fun samples => samples) i j lam Q hlam
    (sqMagTraceProbability_chernoff_mgf_bound A hden i j)
























































/-- `1 - δ` Chernoff concentration for the canonical independent
    squared-magnitude sampler with the fixed-`lam` budget already selected. -/
theorem hitCount_concentrates_sqMag_chernoff_independent_budget
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (i : Fin m) (j : Fin n)
    (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) :
    1 - δ ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (hitCountAtMostEvent (fun samples => samples) i j
          (sqMagChernoffHitCountBudget steps A i j lam δ)) := by
  have htail :=
    sqMagChernoffHitCountBudget_tail
      (steps := steps) A i j hlam hδ
  have hconc :=
    hitCount_concentrates_sqMag_chernoff_independent
      (steps := steps) A hden i j lam
      (sqMagChernoffHitCountBudget steps A i j lam δ) hlam
  linarith































































/-- Optimized Chernoff concentration for the canonical independent
    squared-magnitude Algorithm 1 sampler. -/
theorem hitCount_concentrates_sqMag_chernoff_optimized_independent
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (i : Fin m) (j : Fin n)
    (Q : ℕ)
    (hμ : 0 < (steps : ℝ) * sqMagProb A i j)
    (hQ : (steps : ℝ) * sqMagProb A i j <
      (((Q + 1 : ℕ) : ℝ))) :
    1 - sqMagChernoffOptimizedHitCountTail steps A i j Q ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (hitCountAtMostEvent (fun samples => samples) i j Q) := by
  exact hitCount_concentrates_sqMag_chernoff_optimized_of_mgf_bound
    (sqMagTraceProbability (steps := steps) A hden) A
    (fun samples => samples) i j Q hμ hQ
    (sqMagTraceProbability_chernoff_mgf_bound A hden i j)

/-- `1 - δ` optimized Chernoff concentration for the canonical independent
    squared-magnitude sampler from a supplied optimized-tail budget. -/
theorem hitCount_concentrates_sqMag_chernoff_optimized_independent_of_tail_budget
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (i : Fin m) (j : Fin n)
    (δ : ℝ) (Q : ℕ)
    (hμ : 0 < (steps : ℝ) * sqMagProb A i j)
    (hQ : (steps : ℝ) * sqMagProb A i j <
      (((Q + 1 : ℕ) : ℝ)))
    (htail : sqMagChernoffOptimizedHitCountTail steps A i j Q ≤ δ) :
    1 - δ ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (hitCountAtMostEvent (fun samples => samples) i j Q) := by
  have hconc :=
    hitCount_concentrates_sqMag_chernoff_optimized_independent
      A hden i j Q hμ hQ
  linarith








































































































































theorem highProbability_sqMagTraceStability_of_pairwise_hitCount_deviation
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (δ ε : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hε : 0 < ε)
    (hQreal : (steps : ℝ) * sqMagProb A i j + ε ≤ (Q : ℝ))
    (hQvalid : gammaValid fp Q) (hQ1valid : gammaValid fp (Q + 1))
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} =
          sqMagProb A i j * sqMagProb A i j)
    (htail :
      hitCountPairwiseCenteredMoment steps (sqMagProb A i j) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      P.eventProb (sqMagTraceStabilityEvent fp s A Atilde X i j Q) := by
  have hdev :=
    hitCount_concentrates_sqMag_around_mean_pairwise P A X i j ε δ hε
      hmarginal hpairwise htail
  exact probability_sqMagTraceStability_of_hitCount_deviation fp P
    (1 - δ) s A Atilde X i j ((steps : ℝ) * sqMagProb A i j) ε Q
    hs hAij hQreal hQvalid hQ1valid hdev

theorem highProbability_sqMagTraceStability_of_pairwise_chebyshev_budget
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (δ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0) (hδ : 0 < δ)
    (hQvalid :
      gammaValid fp (sqMagChebyshevHitCountBudget steps A i j δ))
    (hQ1valid :
      gammaValid fp (sqMagChebyshevHitCountBudget steps A i j δ + 1))
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} =
          sqMagProb A i j * sqMagProb A i j) :
    1 - δ ≤
      P.eventProb
        (sqMagTraceStabilityEvent fp s A Atilde X i j
          (sqMagChebyshevHitCountBudget steps A i j δ)) := by
  let p : ℝ := sqMagProb A i j
  have hmoment_eq :=
    expectationReal_hitCount_centered_sq_eq_pairwise P X i j p
      (by simpa [p] using hmarginal)
      (by simpa [p] using hpairwise)
  have hM_nonneg : 0 ≤ hitCountPairwiseCenteredMoment steps p := by
    rw [← hmoment_eq]
    unfold FiniteProbability.expectationReal
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (P.prob_nonneg ω) (sq_nonneg _)
  have hε :
      0 < chebyshevHitCountRadius steps (sqMagProb A i j) δ := by
    simpa [p] using chebyshevHitCountRadius_pos
      (steps := steps) (p := p) hδ hM_nonneg
  have hQreal :
      (steps : ℝ) * sqMagProb A i j +
          chebyshevHitCountRadius steps (sqMagProb A i j) δ ≤
        (sqMagChebyshevHitCountBudget steps A i j δ : ℝ) :=
    sqMagChebyshevHitCountBudget_mean_add_radius_le A i j δ
  have htail :
      hitCountPairwiseCenteredMoment steps (sqMagProb A i j) /
          (chebyshevHitCountRadius steps (sqMagProb A i j) δ) ^ 2 ≤ δ := by
    simpa [p] using
      hitCountPairwiseCenteredMoment_div_chebyshevRadius_sq_le
        (steps := steps) (p := p) hδ hM_nonneg
  exact highProbability_sqMagTraceStability_of_pairwise_hitCount_deviation fp
    P δ (chebyshevHitCountRadius steps (sqMagProb A i j) δ) s
    A Atilde X i j (sqMagChebyshevHitCountBudget steps A i j δ)
    hs hAij hε hQreal hQvalid hQ1valid hmarginal hpairwise htail

-- ============================================================
-- Stability with the proved hit-count concentration
-- ============================================================

/-- High-probability floating-point stability using the proved Markov
    concentration location for the hit counter. -/
theorem highProbability_sqMagTraceStability_of_marginal_hitProb
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQ : gammaValid fp Q) (hQ1 : gammaValid fp (Q + 1))
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j) :
    1 - (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ) ≤
      P.eventProb (sqMagTraceStabilityEvent fp s A Atilde X i j Q) := by
  have hconc :=
    hitCount_concentration_sqMag_markov P A X i j Q hmarginal
  exact probability_sqMagTraceStability_of_hitCount_concentration fp
    P.eventProb
    (1 - (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ))
    s A Atilde X i j Q hs hAij hQ hQ1
    (FiniteProbability.eventProb_mono P) hconc

/-- `1 - δ` high-probability floating-point stability using the proved Markov
    concentration bound for the hit counter.  The hypothesis on `Q` is the
    explicit location where the random counter concentrates. -/
theorem highProbability_sqMagTraceStability_of_marginal_hitProb_of_tail_budget
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (δ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQvalid : gammaValid fp Q) (hQ1valid : gammaValid fp (Q + 1))
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hQtail :
      (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ) ≤ δ) :
    1 - δ ≤
      P.eventProb (sqMagTraceStabilityEvent fp s A Atilde X i j Q) := by
  have hstab :=
    highProbability_sqMagTraceStability_of_marginal_hitProb fp
      P s A Atilde X i j Q hs hAij hQvalid hQ1valid hmarginal
  linarith

/-- Markov high-probability stability with the natural counter budget already
    chosen as `ceil(steps * pᵢⱼ / δ)`. -/
theorem highProbability_sqMagTraceStability_of_markov_budget
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (δ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0) (hδ : 0 < δ)
    (hQvalid : gammaValid fp (sqMagMarkovHitCountBudget steps A i j δ))
    (hQ1valid :
      gammaValid fp (sqMagMarkovHitCountBudget steps A i j δ + 1))
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j) :
    1 - δ ≤
      P.eventProb
        (sqMagTraceStabilityEvent fp s A Atilde X i j
          (sqMagMarkovHitCountBudget steps A i j δ)) := by
  have htail :=
    sqMagMarkovHitCountBudget_tail (steps := steps) A i j hδ
  exact highProbability_sqMagTraceStability_of_marginal_hitProb_of_tail_budget
    fp P δ s A Atilde X i j
    (sqMagMarkovHitCountBudget steps A i j δ)
    hs hAij hQvalid hQ1valid hmarginal htail

/-- Chernoff high-probability stability for the canonical independent
    squared-magnitude Algorithm 1 sampler. The exponential-moment hypothesis
    is proved from the product trace distribution in
    `sqMagTraceProbability_chernoff_mgf_bound`. -/
theorem highProbability_sqMagTraceStability_of_independent_chernoff_budget
    (fp : FPModel) {m n steps : ℕ}
    (δ lam : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hlam : 0 < lam) (hδ : 0 < δ)
    (hQvalid :
      gammaValid fp (sqMagChernoffHitCountBudget steps A i j lam δ))
    (hQ1valid :
      gammaValid fp (sqMagChernoffHitCountBudget steps A i j lam δ + 1)) :
    1 - δ ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (sqMagTraceStabilityEvent fp s A Atilde
          (fun samples => samples) i j
          (sqMagChernoffHitCountBudget steps A i j lam δ)) := by
  have hconc :=
    hitCount_concentrates_sqMag_chernoff_independent_budget
      (steps := steps) A hden i j lam δ hlam hδ
  exact highProbability_sqMagTraceStability_of_hitCount_concentration fp
    (sqMagTraceProbability (steps := steps) A hden).eventProb δ s
    A Atilde (fun samples => samples) i j
    (sqMagChernoffHitCountBudget steps A i j lam δ)
    hs hAij hQvalid hQ1valid
    (FiniteProbability.eventProb_mono
      (sqMagTraceProbability (steps := steps) A hden)) hconc

/-- Optimized Chernoff high-probability stability for the canonical independent
    squared-magnitude Algorithm 1 sampler and a supplied budget `Q`. -/
theorem highProbability_sqMagTraceStability_of_independent_chernoff_optimized_tail_budget
    (fp : FPModel) {m n steps : ℕ}
    (δ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQvalid : gammaValid fp Q) (hQ1valid : gammaValid fp (Q + 1))
    (hμ : 0 < (steps : ℝ) * sqMagProb A i j)
    (hQtailThreshold :
      (steps : ℝ) * sqMagProb A i j < (((Q + 1 : ℕ) : ℝ)))
    (htail : sqMagChernoffOptimizedHitCountTail steps A i j Q ≤ δ) :
    1 - δ ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (sqMagTraceStabilityEvent fp s A Atilde
          (fun samples => samples) i j Q) := by
  have hconc :=
    hitCount_concentrates_sqMag_chernoff_optimized_independent_of_tail_budget
      A hden i j δ Q hμ hQtailThreshold htail
  exact highProbability_sqMagTraceStability_of_hitCount_concentration fp
    (sqMagTraceProbability (steps := steps) A hden).eventProb δ s
    A Atilde (fun samples => samples) i j Q hs hAij hQvalid hQ1valid
    (FiniteProbability.eventProb_mono
      (sqMagTraceProbability (steps := steps) A hden)) hconc

end NumStability
