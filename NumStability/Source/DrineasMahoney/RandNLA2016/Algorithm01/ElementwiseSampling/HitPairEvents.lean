import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.Elementwise.Core
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm01.ElementwiseSampling.Sampling
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm01.ElementwiseSampling.HitCountConcentration
import NumStability.Source.Higham.Chapter04.Problem04

/-!
Relocated from the historical wave owners NumStability.Algorithms.RandNLA.HitCountConcentration under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

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




















































































































/-- Product-law pointwise factorization for two distinct elementwise trace
    coordinates. -/
private theorem sqMagTraceProbMass_two_point_factor
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (t u : Fin steps) (htu : t ≠ u)
    (f g : ElementwiseSample m n → ℝ)
    (x : ElementwiseTrace m n steps) :
    (∏ r : Fin steps,
      if r = t then sqMagProb A (x r).1 (x r).2 * f (x r)
      else if r = u then sqMagProb A (x r).1 (x r).2 * g (x r)
      else sqMagProb A (x r).1 (x r).2) =
    (∏ r : Fin steps, sqMagProb A (x r).1 (x r).2) *
      f (x t) * g (x u) := by
  classical
  have hfactor : ∀ r : Fin steps,
      (if r = t then sqMagProb A (x r).1 (x r).2 * f (x r)
      else if r = u then sqMagProb A (x r).1 (x r).2 * g (x r)
      else sqMagProb A (x r).1 (x r).2) =
      sqMagProb A (x r).1 (x r).2 *
        (if r = t then f (x r) else if r = u then g (x r) else 1) := by
    intro r
    by_cases hrt : r = t
    · simp [hrt]
    · by_cases hru : r = u
      · simp [hru]
      · simp [hrt, hru]
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

/-- Two distinct coordinates of the independent elementwise trace have product
    expectation equal to the product of their one-step expectations. -/
theorem sqMagTraceProbMass_marginal_two_ne {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0)
    (t u : Fin steps) (htu : t ≠ u)
    (f g : ElementwiseSample m n → ℝ) :
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples *
        (f (samples t) * g (samples u))) =
      (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x) *
      (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x) := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps =>
        (Finset.univ : Finset (ElementwiseSample m n)))
      (f := fun r x =>
        if r = t then sqMagProb A x.1 x.2 * f x
        else if r = u then sqMagProb A x.1 x.2 * g x
        else sqMagProb A x.1 x.2)
  have hleft :
      (∏ r : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (ElementwiseSample m n)),
          (if r = t then sqMagProb A x.1 x.2 * f x
          else if r = u then sqMagProb A x.1 x.2 * g x
          else sqMagProb A x.1 x.2)) =
      (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x) *
      (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x) := by
    simp [sqMagProb_sum_samples_eq_one A hden]
    have hprod_t := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t
      (fun r : Fin steps =>
        if r = t then
          ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x
        else if r = u then
          ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x
        else 1)
      (by intro h; simp at h)
    simp at hprod_t
    rw [hprod_t]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t},
          if x_1 = t then
            ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x
          else if x_1 = u then
            ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x
          else 1) =
          ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x := by
      rw [Finset.sdiff_singleton_eq_erase]
      have hprod_u := Finset.prod_eq_mul_prod_diff_singleton
        (s := ((Finset.univ : Finset (Fin steps)).erase t)) u
        (fun r : Fin steps =>
          if r = t then
            ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x
          else if r = u then
            ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x
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
            if x_1 = t then
              ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x
            else if x_1 = u then
              ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x
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
        (fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n))),
        ∏ r, (if r = t then sqMagProb A (x r).1 (x r).2 * f (x r)
          else if r = u then sqMagProb A (x r).1 (x r).2 * g (x r)
          else sqMagProb A (x r).1 (x r).2))
        = ∑ samples : ElementwiseTrace m n steps,
          sqMagTraceProbMass A samples *
            (f (samples t) * g (samples u)) := by
    simp [sqMagTraceProbMass, ElementwiseTrace]
    apply Finset.sum_congr rfl
    intro x _
    simpa [mul_assoc] using
      sqMagTraceProbMass_two_point_factor A t u htu f g x
  rw [← hright, ← hprod]
  exact hleft





















































































































/-- In the canonical independent trace law, two distinct steps hit the same
    entry with product probability `pᵢⱼ^2`. -/
theorem sqMagTraceProbability_eventProb_sampleHits_pair_ne {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (t u : Fin steps) (htu : t ≠ u) (i : Fin m) (j : Fin n) :
    (sqMagTraceProbability (steps := steps) A hden).eventProb
      {samples | sampleHits samples t i j ∧ sampleHits samples u i j} =
      sqMagProb A i j * sqMagProb A i j := by
  classical
  let f : ElementwiseSample m n → ℝ :=
    fun x => if x.1 = i ∧ x.2 = j then 1 else 0
  have hsingle :
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
  have hE :
      (sqMagTraceProbability (steps := steps) A hden).expectationReal
        (fun samples =>
          hitIndicator samples t i j * hitIndicator samples u i j) =
        sqMagProb A i j * sqMagProb A i j := by
    unfold FiniteProbability.expectationReal sqMagTraceProbability
    calc
      ∑ samples : ElementwiseTrace m n steps,
          sqMagTraceProbMass A samples *
            (hitIndicator samples t i j * hitIndicator samples u i j)
          = ∑ samples : ElementwiseTrace m n steps,
              sqMagTraceProbMass A samples *
                (f (samples t) * f (samples u)) := by
              apply Finset.sum_congr rfl
              intro samples _
              unfold f hitIndicator sampleHits
              by_cases ht : (samples t).1 = i ∧ (samples t).2 = j <;>
                by_cases hu : (samples u).1 = i ∧ (samples u).2 = j <;>
                  simp [ht, hu]
      _ = (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x) *
            (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x) :=
              sqMagTraceProbMass_marginal_two_ne A hden.ne' t u htu f f
      _ = sqMagProb A i j * sqMagProb A i j := by
              rw [hsingle]
  rw [expectationReal_hitIndicator_mul_eq_eventProb_inter
    (sqMagTraceProbability (steps := steps) A hden)
    (fun samples : ElementwiseTrace m n steps => samples) t u i j] at hE
  exact hE


















































































































































































































































































































































































































































































































































































































-- ============================================================
-- Chernoff concentration from an exponential-moment bound
-- ============================================================





















































































































































































































































































































































































































































































































-- ============================================================
-- Stability with the proved hit-count concentration
-- ============================================================




























































































































end NumStability
