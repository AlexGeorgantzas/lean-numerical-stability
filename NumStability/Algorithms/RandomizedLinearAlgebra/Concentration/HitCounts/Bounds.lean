import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.Elementwise.Core
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.HitCounts.Bounds

W11 canonical reusable randomized linear algebra destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.HitCountConcentration`; the historical path re-exports this module.
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

/-- Real-valued indicator of a trace step hitting `(i, j)`. -/
noncomputable def hitIndicator {m n steps : ℕ}
    (samples : ElementwiseTrace m n steps) (t : Fin steps)
    (i : Fin m) (j : Fin n) : ℝ :=
  by
    classical
    exact if sampleHits samples t i j then 1 else 0

/-- The hit count is the sum of the stepwise hit indicators. -/
theorem hitCount_eq_sum_indicator {m n steps : ℕ}
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n) :
    (hitCount samples i j : ℝ) =
      ∑ t : Fin steps, hitIndicator samples t i j := by
  classical
  induction steps with
  | zero =>
      simp [hitCount]
  | succ steps ih =>
      let samplePrefix : ElementwiseTrace m n steps :=
        fun t => samples t.castSucc
      by_cases hlast : sampleHits samples (Fin.last steps) i j
      · have hcount := hitCount_succ_last_of_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j + 1 at hcount
        calc
          (hitCount samples i j : ℝ)
              = (hitCount samplePrefix i j : ℝ) + 1 := by
                  exact_mod_cast hcount
          _ = (∑ t : Fin steps, hitIndicator samplePrefix t i j) + 1 := by
                  rw [ih samplePrefix]
          _ = ∑ t : Fin (steps + 1), hitIndicator samples t i j := by
                  have hlast_ind :
                      hitIndicator samples (Fin.last steps) i j = 1 := by
                    simp [hitIndicator, hlast]
                  have hprefix :
                      (∑ t : Fin steps, hitIndicator samplePrefix t i j) =
                        ∑ t : Fin steps, hitIndicator samples t.castSucc i j := by
                    apply Finset.sum_congr rfl
                    intro t _
                    rfl
                  rw [Fin.sum_univ_castSucc]
                  rw [← hprefix, hlast_ind]
      · have hcount := hitCount_succ_last_of_not_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j at hcount
        calc
          (hitCount samples i j : ℝ)
              = (hitCount samplePrefix i j : ℝ) := by
                  exact_mod_cast hcount
          _ = ∑ t : Fin steps, hitIndicator samplePrefix t i j := by
                  rw [ih samplePrefix]
          _ = ∑ t : Fin (steps + 1), hitIndicator samples t i j := by
                  have hlast_ind :
                      hitIndicator samples (Fin.last steps) i j = 0 := by
                    simp [hitIndicator, hlast]
                  have hprefix :
                      (∑ t : Fin steps, hitIndicator samplePrefix t i j) =
                        ∑ t : Fin steps, hitIndicator samples t.castSucc i j := by
                    apply Finset.sum_congr rfl
                    intro t _
                    rfl
                  rw [Fin.sum_univ_castSucc]
                  rw [← hprefix, hlast_ind]
                  ring

/-- Expectation of the hit counter as the sum of marginal hit probabilities. -/
theorem expectationNat_hitCount_eq_sum_step_hit_probs {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n) :
    P.expectationNat (fun ω => hitCount (X ω) i j) =
      ∑ t : Fin steps,
        P.eventProb {ω | sampleHits (X ω) t i j} := by
  classical
  unfold FiniteProbability.expectationNat FiniteProbability.eventProb
  calc
    ∑ ω, P.prob ω * (hitCount (X ω) i j : ℝ)
        = ∑ ω, P.prob ω *
            (∑ t : Fin steps, hitIndicator (X ω) t i j) := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [hitCount_eq_sum_indicator]
    _ = ∑ ω, ∑ t : Fin steps,
            P.prob ω * hitIndicator (X ω) t i j := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [Finset.mul_sum]
    _ = ∑ t : Fin steps, ∑ ω,
            P.prob ω * hitIndicator (X ω) t i j := by
            rw [Finset.sum_comm]
    _ = ∑ t : Fin steps, ∑ ω,
            if sampleHits (X ω) t i j then P.prob ω else 0 := by
            apply Finset.sum_congr rfl
            intro t _
            apply Finset.sum_congr rfl
            intro ω _
            by_cases hhit : sampleHits (X ω) t i j <;>
              simp [hitIndicator, hhit]

/-- If every step has marginal hit probability `p`, the expected hit count is
    `steps * p`. No independence is needed for this expectation identity. -/
theorem expectationNat_hitCount_eq_steps_mul_hitProb {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p) :
    P.expectationNat (fun ω => hitCount (X ω) i j) = (steps : ℝ) * p := by
  rw [expectationNat_hitCount_eq_sum_step_hit_probs P X i j]
  simp [hmarginal, Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]

/-- Real-expectation version of `expectationNat_hitCount_eq_steps_mul_hitProb`. -/
theorem expectationReal_hitCount_eq_steps_mul_hitProb {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p) :
    P.expectationReal (fun ω => (hitCount (X ω) i j : ℝ)) =
      (steps : ℝ) * p := by
  simpa [FiniteProbability.expectationReal, FiniteProbability.expectationNat]
    using expectationNat_hitCount_eq_steps_mul_hitProb P X i j p hmarginal

/-- The expectation of a hit indicator is the hit probability of that step. -/
theorem expectationReal_hitIndicator_eq_eventProb {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (t : Fin steps)
    (i : Fin m) (j : Fin n) :
    P.expectationReal (fun ω => hitIndicator (X ω) t i j) =
      P.eventProb {ω | sampleHits (X ω) t i j} := by
  classical
  unfold FiniteProbability.expectationReal FiniteProbability.eventProb
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hhit : sampleHits (X ω) t i j <;>
    simp [hitIndicator, hhit]

/-- The expectation of a product of two hit indicators is the probability that
    both corresponding steps hit the entry. -/
theorem expectationReal_hitIndicator_mul_eq_eventProb_inter {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (t u : Fin steps)
    (i : Fin m) (j : Fin n) :
    P.expectationReal
      (fun ω => hitIndicator (X ω) t i j * hitIndicator (X ω) u i j) =
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} := by
  classical
  unfold FiniteProbability.expectationReal FiniteProbability.eventProb
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ht : sampleHits (X ω) t i j
  · by_cases hu : sampleHits (X ω) u i j <;>
      simp [hitIndicator, ht, hu]
  · simp [hitIndicator, ht]

/-- Sum of a diagonal/off-diagonal constant kernel over `Fin steps × Fin steps`.
    This is the ordered-pair count used in the hit-count second-moment proof. -/
theorem sum_pairwise_diag_offdiag (steps : ℕ) (p : ℝ) :
    (∑ t : Fin steps, ∑ u : Fin steps, if u = t then p else p * p)
      = (steps : ℝ) * p +
        (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) := by
  classical
  have hinner : ∀ t : Fin steps,
      (∑ u : Fin steps, if u = t then p else p * p)
        = p + ((steps - 1 : ℕ) : ℝ) * (p * p) := by
    intro t
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin steps))
      (fun u : Fin steps => if u = t then p else p * p) (Finset.mem_univ t)
    have herase :
        (∑ x ∈ (Finset.univ : Finset (Fin steps)).erase t,
          (if x = t then p else p * p))
          = ∑ x ∈ (Finset.univ : Finset (Fin steps)).erase t, p * p := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxt : x ≠ t := by
        simpa using (Finset.mem_erase.mp hx).1
      simp [hxt]
    have hcard : ((Finset.univ : Finset (Fin steps)).erase t).card =
        steps - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ,
        Fintype.card_fin]
    calc
      (∑ u : Fin steps, if u = t then p else p * p)
          = ∑ u ∈ (Finset.univ : Finset (Fin steps)),
              if u = t then p else p * p := by
              simp
      _ = (∑ x ∈ (Finset.univ : Finset (Fin steps)).erase t,
              (if x = t then p else p * p)) +
            (if t = t then p else p * p) := by
              rw [← hsum]
      _ = (∑ x ∈ (Finset.univ : Finset (Fin steps)).erase t, p * p) + p := by
              rw [herase]
              simp
      _ = ((steps - 1 : ℕ) : ℝ) * (p * p) + p := by
              rw [Finset.sum_const, hcard]
              simp [nsmul_eq_mul]
      _ = p + ((steps - 1 : ℕ) : ℝ) * (p * p) := by ring
  calc
    (∑ t : Fin steps, ∑ u : Fin steps, if u = t then p else p * p)
        = ∑ t : Fin steps, (p + ((steps - 1 : ℕ) : ℝ) * (p * p)) := by
            apply Finset.sum_congr rfl
            intro t _
            exact hinner t
    _ = (steps : ℝ) * p +
        (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
            ring

/-- Under marginal probability `p` and pairwise independence of distinct hit
    indicators, the second moment of the hit counter is the usual ordered-pair
    count for Bernoulli sums. -/
theorem expectationReal_hitCount_sq_eq_pairwise {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} = p * p) :
    P.expectationReal (fun ω => ((hitCount (X ω) i j : ℝ) ^ 2)) =
      (steps : ℝ) * p +
        (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) := by
  classical
  let I : Fin steps → Ω → ℝ := fun t ω => hitIndicator (X ω) t i j
  have hcount : ∀ ω, (hitCount (X ω) i j : ℝ) = ∑ t, I t ω := by
    intro ω
    exact hitCount_eq_sum_indicator (X ω) i j
  calc
    P.expectationReal (fun ω => ((hitCount (X ω) i j : ℝ) ^ 2))
        = P.expectationReal (fun ω => (∑ t, I t ω) ^ 2) := by
            unfold FiniteProbability.expectationReal
            apply Finset.sum_congr rfl
            intro ω _
            simp [hcount ω]
    _ = P.expectationReal
          (fun ω => ∑ t : Fin steps, ∑ u : Fin steps, I t ω * I u ω) := by
            unfold FiniteProbability.expectationReal
            apply Finset.sum_congr rfl
            intro ω _
            congr 1
            calc
              (∑ t : Fin steps, I t ω) ^ 2
                  = (∑ t : Fin steps, I t ω) *
                    (∑ u : Fin steps, I u ω) := by ring
              _ = ∑ t : Fin steps, ∑ u : Fin steps, I t ω * I u ω := by
                    rw [Finset.sum_mul]
                    simp_rw [Finset.mul_sum]
    _ = ∑ t : Fin steps, ∑ u : Fin steps,
          P.expectationReal (fun ω => I t ω * I u ω) := by
            rw [FiniteProbability.expectationReal_sum]
            apply Finset.sum_congr rfl
            intro t _
            rw [FiniteProbability.expectationReal_sum]
    _ = ∑ t : Fin steps, ∑ u : Fin steps, if u = t then p else p * p := by
            apply Finset.sum_congr rfl
            intro t _
            apply Finset.sum_congr rfl
            intro u _
            by_cases hut : u = t
            · subst u
              have hset :
                  {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) t i j} =
                    {ω | sampleHits (X ω) t i j} := by
                ext ω
                simp
              rw [expectationReal_hitIndicator_mul_eq_eventProb_inter]
              rw [hset, hmarginal t]
              simp
            · have htu : t ≠ u := by
                intro h
                exact hut h.symm
              rw [expectationReal_hitIndicator_mul_eq_eventProb_inter]
              simp [hut, hpairwise t u htu]
    _ = (steps : ℝ) * p +
        (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) :=
            sum_pairwise_diag_offdiag steps p

/-- Closed-form centered second moment for a pairwise-independent hit counter
    with `steps` trials and marginal hit probability `p`. -/
noncomputable def hitCountPairwiseCenteredMoment (steps : ℕ) (p : ℝ) : ℝ :=
  ((steps : ℝ) * p +
    (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p)) -
    ((steps : ℝ) * p) ^ 2

/-- The pairwise-independent hit-count centered second-moment expression is at
    most its mean when the marginal probability is nonnegative. -/
theorem hitCountPairwiseCenteredMoment_le_steps_mul
    (steps : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    hitCountPairwiseCenteredMoment steps p ≤ (steps : ℝ) * p := by
  have hsteps : 0 ≤ (steps : ℝ) := by exact_mod_cast Nat.zero_le steps
  have hpred : ((steps - 1 : ℕ) : ℝ) ≤ (steps : ℝ) := by
    exact_mod_cast Nat.sub_le steps 1
  have hp2 : 0 ≤ p * p := mul_nonneg hp hp
  have hmul1 :
      (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) ≤
        (steps : ℝ) * (steps : ℝ) :=
    mul_le_mul_of_nonneg_left hpred hsteps
  have hmul :
      (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) ≤
        (steps : ℝ) * (steps : ℝ) * (p * p) :=
    mul_le_mul_of_nonneg_right hmul1 hp2
  unfold hitCountPairwiseCenteredMoment
  nlinarith [hmul]

/-- Centered second moment of the hit counter around its mean `steps * p`, under
    pairwise independence of distinct hit indicators.  The expression is kept in
    a form that is valid without splitting off the `steps = 0` case. -/
theorem expectationReal_hitCount_centered_sq_eq_pairwise {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} = p * p) :
    P.expectationReal
        (fun ω => ((hitCount (X ω) i j : ℝ) - (steps : ℝ) * p) ^ 2) =
      hitCountPairwiseCenteredMoment steps p := by
  classical
  let μ : ℝ := (steps : ℝ) * p
  let Q : Ω → ℝ := fun ω => (hitCount (X ω) i j : ℝ)
  have hmean : P.expectationReal Q = μ := by
    simpa [Q, μ] using
      expectationReal_hitCount_eq_steps_mul_hitProb P X i j p hmarginal
  have hsecond :
      P.expectationReal (fun ω => Q ω ^ 2) =
        (steps : ℝ) * p +
          (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) := by
    simpa [Q] using
      expectationReal_hitCount_sq_eq_pairwise P X i j p hmarginal hpairwise
  calc
    P.expectationReal (fun ω => (Q ω - μ) ^ 2)
        = P.expectationReal
            (fun ω => Q ω ^ 2 - (2 * μ) * Q ω + μ ^ 2) := by
            unfold FiniteProbability.expectationReal
            apply Finset.sum_congr rfl
            intro ω _
            ring
    _ = P.expectationReal (fun ω => Q ω ^ 2) -
          P.expectationReal (fun ω => (2 * μ) * Q ω) +
          P.expectationReal (fun _ => μ ^ 2) := by
            rw [FiniteProbability.expectationReal_add,
              FiniteProbability.expectationReal_sub]
    _ = P.expectationReal (fun ω => Q ω ^ 2) - (2 * μ) * P.expectationReal Q +
          μ ^ 2 := by
            rw [FiniteProbability.expectationReal_const_mul,
              FiniteProbability.expectationReal_const]
    _ = ((steps : ℝ) * p +
          (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p)) -
          ((steps : ℝ) * p) ^ 2 := by
            rw [hmean, hsecond]
            simp [μ]
            ring
    _ = hitCountPairwiseCenteredMoment steps p := by
            rfl

/-- Markov concentration for the hit counter from a marginal hit probability
    `p`: with probability at least `1 - steps * p / (Q+1)`, the hit count is
    at most `Q`. -/
theorem hitCount_concentration_markov_of_marginal_hitProb {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ) (Q : ℕ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p) :
    1 - (steps : ℝ) * p / ((Q + 1 : ℕ) : ℝ) ≤
      P.eventProb (hitCountAtMostEvent X i j Q) := by
  have hmarkov :=
    FiniteProbability.eventProb_nat_le_ge_one_sub_expectationNat_div_succ
      P (fun ω => hitCount (X ω) i j) Q
  have hexpect :=
    expectationNat_hitCount_eq_steps_mul_hitProb P X i j p hmarginal
  simpa [hitCountAtMostEvent, hexpect] using hmarkov

/-- `1 - δ` form of the Markov concentration theorem. -/
theorem hitCount_concentrates_of_marginal_hitProb {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p δ : ℝ) (Q : ℕ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p)
    (hQ : (steps : ℝ) * p / ((Q + 1 : ℕ) : ℝ) ≤ δ) :
    1 - δ ≤ P.eventProb (hitCountAtMostEvent X i j Q) := by
  have hconc :=
    hitCount_concentration_markov_of_marginal_hitProb P X i j p Q hmarginal
  linarith

/-- Squared-magnitude specialization of the Markov concentration theorem for
    Algorithm 1: if each step hits `(i, j)` with marginal probability
    `pᵢⱼ = sqMagProb A i j`, then `qᵢⱼ ≤ Q` with probability at least
    `1 - steps * pᵢⱼ / (Q+1)`. -/
theorem hitCount_concentration_sqMag_markov {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j) :
    1 - (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ) ≤
      P.eventProb (hitCountAtMostEvent X i j Q) :=
  hitCount_concentration_markov_of_marginal_hitProb P X i j
    (sqMagProb A i j) Q hmarginal

/-- `1 - δ` squared-magnitude concentration theorem for the hit counter. -/
theorem hitCount_concentrates_sqMag {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (δ : ℝ) (Q : ℕ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hQ : (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ) ≤ δ) :
    1 - δ ≤ P.eventProb (hitCountAtMostEvent X i j Q) :=
  hitCount_concentrates_of_marginal_hitProb P X i j
    (sqMagProb A i j) δ Q hmarginal hQ

/-- Markov-selected natural budget:
    `Q = ceil(steps * p / δ)`.

With `δ > 0`, this choice ensures
`steps * p / (Q+1) ≤ δ`, hence a `1 - δ` Markov bound. -/
noncomputable def markovHitCountBudget (steps : ℕ) (p δ : ℝ) : ℕ :=
  Nat.ceil ((steps : ℝ) * p / δ)

/-- Squared-magnitude specialization of the Markov-selected hit-count budget. -/
noncomputable def sqMagMarkovHitCountBudget {m n : ℕ} (steps : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (δ : ℝ) : ℕ :=
  markovHitCountBudget steps (sqMagProb A i j) δ

theorem markovHitCountBudget_tail {steps : ℕ} {p δ : ℝ} (hδ : 0 < δ) :
    (steps : ℝ) * p /
        (((markovHitCountBudget steps p δ) + 1 : ℕ) : ℝ) ≤ δ := by
  have hceil :
      (steps : ℝ) * p / δ ≤ (markovHitCountBudget steps p δ : ℝ) := by
    unfold markovHitCountBudget
    exact Nat.le_ceil ((steps : ℝ) * p / δ)
  have hQle :
      (markovHitCountBudget steps p δ : ℝ) ≤
        (((markovHitCountBudget steps p δ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ (markovHitCountBudget steps p δ)
  have hdiv_le :
      (steps : ℝ) * p / δ ≤
        (((markovHitCountBudget steps p δ) + 1 : ℕ) : ℝ) :=
    le_trans hceil hQle
  have hnum_le :
      (steps : ℝ) * p ≤
        (((markovHitCountBudget steps p δ) + 1 : ℕ) : ℝ) * δ := by
    rwa [div_le_iff₀ hδ] at hdiv_le
  have hden :
      0 < ((((markovHitCountBudget steps p δ) + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos (markovHitCountBudget steps p δ)
  rw [div_le_iff₀ hden]
  nlinarith

theorem sqMagMarkovHitCountBudget_tail {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    {δ : ℝ} (hδ : 0 < δ) :
    (steps : ℝ) * sqMagProb A i j /
        (((sqMagMarkovHitCountBudget steps A i j δ) + 1 : ℕ) : ℝ) ≤ δ := by
  simpa [sqMagMarkovHitCountBudget] using
    markovHitCountBudget_tail (steps := steps) (p := sqMagProb A i j) hδ

-- ============================================================
-- The canonical independent squared-magnitude trace distribution
-- ============================================================

/-- One-step real indicator for the sampled pair being `(i, j)`. -/
noncomputable def sampleHitIndicator {m n : ℕ}
    (x : ElementwiseSample m n) (i : Fin m) (j : Fin n) : ℝ :=
  if x.1 = i ∧ x.2 = j then 1 else 0

/-- Product probability mass of an Algorithm 1 trace when each step samples
    independently from the squared-magnitude probabilities. -/
noncomputable def sqMagTraceProbMass {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) : ℝ :=
  ∏ t : Fin steps, sqMagProb A (samples t).1 (samples t).2













theorem sqMagTraceProbMass_nonneg {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (samples : ElementwiseTrace m n steps) :
    0 ≤ sqMagTraceProbMass A samples := by
  unfold sqMagTraceProbMass
  exact Finset.prod_nonneg fun t _ =>
    sqMagProb_nonneg A hden (samples t).1 (samples t).2
























































































































































































































































































/-- Trace-support predicate for Algorithm 1: every sampled entry has positive
    squared-magnitude probability.  Entries with zero probability carry zero
    mass under the canonical product law, so this is the event on which all
    sampled-entry divisions have nonzero denominators. -/
def elementwiseTracePositiveProb {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Prop :=
  ∀ t : Fin steps, 0 < sqMagProb A (samples t).1 (samples t).2

theorem sqMagTraceProbMass_eq_zero_of_exists_prob_zero {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (hzero :
      ∃ t : Fin steps, sqMagProb A (samples t).1 (samples t).2 = 0) :
    sqMagTraceProbMass A samples = 0 := by
  classical
  rcases hzero with ⟨t, ht⟩
  unfold sqMagTraceProbMass
  exact Finset.prod_eq_zero (Finset.mem_univ t) ht






























































































































































































/-- If the target entry is zero, the exact Algorithm 1 trace contribution at
    that entry is identically zero, independently of the sampled trace. -/
theorem elementwiseTraceSketch_zero_init_of_entry_eq_zero {m n steps : ℕ}
    (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hAij : A i j = 0) :
    elementwiseTraceSketch s A (fun _ _ => 0) samples i j = 0 := by
  classical
  have hinc : elementwiseIncrement s A i j = 0 := by
    simp [elementwiseIncrement, elementwiseIncrementWithProb, hAij]
  simp [elementwiseTraceSketch, elementwiseTraceContribution, hinc]



























































































/-- Exponential of a trace-sum of an arbitrary one-step scalar function
    factors into the product of one-step exponentials. -/
theorem exp_sum_stepFunction_eq_prod {m n steps : ℕ}
    (samples : ElementwiseTrace m n steps)
    (f : ElementwiseSample m n → ℝ) (lam : ℝ) :
    Real.exp (lam * (∑ t : Fin steps, f (samples t))) =
      ∏ t : Fin steps, Real.exp (lam * f (samples t)) := by
  classical
  calc
    Real.exp (lam * (∑ t : Fin steps, f (samples t)))
        = Real.exp (∑ t : Fin steps, lam * f (samples t)) := by
            rw [Finset.mul_sum]
    _ = ∏ t : Fin steps, Real.exp (lam * f (samples t)) := by
            simpa using
              (Real.exp_sum (Finset.univ : Finset (Fin steps))
                (fun t => lam * f (samples t)))

/-- Product-law MGF factorization for an arbitrary one-step scalar statistic
    under the canonical independent squared-magnitude trace distribution. -/
theorem sqMagTraceProbMass_exp_sum_stepFunction_eq {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ)
    (f : ElementwiseSample m n → ℝ) (lam : ℝ) :
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples *
        Real.exp (lam * (∑ t : Fin steps, f (samples t)))) =
      (∑ x : ElementwiseSample m n,
        sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ^ steps := by
  classical
  calc
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples *
        Real.exp (lam * (∑ t : Fin steps, f (samples t))))
        = ∑ samples : ElementwiseTrace m n steps,
            ∏ t : Fin steps,
              sqMagProb A (samples t).1 (samples t).2 *
                Real.exp (lam * f (samples t)) := by
            apply Finset.sum_congr rfl
            intro samples _
            rw [exp_sum_stepFunction_eq_prod samples f lam]
            simp [sqMagTraceProbMass, Finset.prod_mul_distrib]
    _ = ∏ t : Fin steps,
          ∑ x : ElementwiseSample m n,
            sqMagProb A x.1 x.2 * Real.exp (lam * f x) := by
            have hprod :=
              Finset.prod_univ_sum
                (t := fun _ : Fin steps =>
                  (Finset.univ : Finset (ElementwiseSample m n)))
                (f := fun _ x =>
                  sqMagProb A x.1 x.2 * Real.exp (lam * f x))
            symm
            simpa [ElementwiseTrace] using hprod
    _ = (∑ x : ElementwiseSample m n,
          sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ^ steps := by
            simp [Fintype.card_fin]















































































































































































































































































































/-- The trace hit-count exponential is the product of the one-step
    exponential indicators. -/
theorem exp_hitCount_eq_prod_sampleHitIndicator {m n steps : ℕ}
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (lam : ℝ) :
    Real.exp (lam * (hitCount samples i j : ℝ)) =
      ∏ t : Fin steps, Real.exp (lam * sampleHitIndicator (samples t) i j) := by
  classical
  have hcount := hitCount_eq_sum_indicator samples i j
  calc
    Real.exp (lam * (hitCount samples i j : ℝ))
        = Real.exp (∑ t : Fin steps, lam * hitIndicator samples t i j) := by
            rw [hcount]
            rw [Finset.mul_sum]
    _ = ∏ t : Fin steps, Real.exp (lam * hitIndicator samples t i j) := by
            simpa using (Real.exp_sum (Finset.univ : Finset (Fin steps))
              (fun t => lam * hitIndicator samples t i j))
    _ = ∏ t : Fin steps, Real.exp (lam * sampleHitIndicator (samples t) i j) := by
            apply Finset.prod_congr rfl
            intro t _
            simp [hitIndicator, sampleHitIndicator, sampleHits]





















































-- ============================================================
-- Chernoff concentration from an exponential-moment bound
-- ============================================================

/-- The standard Bernoulli-sum exponential-moment upper bound used by the
    Chernoff argument:

`E exp(lam qᵢⱼ) ≤ exp(steps * pᵢⱼ * (exp lam - 1))`.

For Algorithm 1 this is the condition supplied by fully independent sampling
of the step-hit indicators. It is stronger than the marginal law used by
Markov and stronger than the pairwise law used by Chebyshev. -/
def hitCountChernoffMGFBound {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam →
    P.expectationReal
        (fun ω => Real.exp (lam * (hitCount (X ω) i j : ℝ))) ≤
      Real.exp ((steps : ℝ) * p * (Real.exp lam - 1))

/-- Squared-magnitude specialization of the Chernoff MGF condition. -/
def sqMagHitCountChernoffMGFBound {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n) : Prop :=
  hitCountChernoffMGFBound P X i j (sqMagProb A i j)












































/-- Chernoff upper-tail expression for `qᵢⱼ > Q`, written as
    `Pr(Q+1 ≤ qᵢⱼ)`. -/
noncomputable def chernoffHitCountTail (steps : ℕ) (p lam : ℝ) (Q : ℕ) : ℝ :=
  Real.exp ((steps : ℝ) * p * (Real.exp lam - 1) -
    lam * (((Q + 1 : ℕ) : ℝ)))

/-- Squared-magnitude specialization of the Chernoff tail expression. -/
noncomputable def sqMagChernoffHitCountTail {m n : ℕ} (steps : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (lam : ℝ) (Q : ℕ) : ℝ :=
  chernoffHitCountTail steps (sqMagProb A i j) lam Q

/-- Chernoff concentration for the Algorithm 1 hit counter from the MGF bound. -/
theorem hitCount_concentrates_chernoff_of_mgf_bound {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p lam : ℝ) (Q : ℕ) (hlam : 0 < lam)
    (hmgf : hitCountChernoffMGFBound P X i j p) :
    1 - chernoffHitCountTail steps p lam Q ≤
      P.eventProb (hitCountAtMostEvent X i j Q) := by
  simpa [hitCountAtMostEvent, chernoffHitCountTail] using
    FiniteProbability.eventProb_nat_le_ge_one_sub_chernoff_of_mgf_bound
      P (fun ω => hitCount (X ω) i j) Q (lam := lam)
      (μ := (steps : ℝ) * p) hlam (hmgf lam hlam)

/-- Squared-magnitude Chernoff concentration for the Algorithm 1 hit counter. -/
theorem hitCount_concentrates_sqMag_chernoff_of_mgf_bound {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (lam : ℝ) (Q : ℕ) (hlam : 0 < lam)
    (hmgf : sqMagHitCountChernoffMGFBound P A X i j) :
    1 - sqMagChernoffHitCountTail steps A i j lam Q ≤
      P.eventProb (hitCountAtMostEvent X i j Q) := by
  simpa [sqMagChernoffHitCountTail, sqMagHitCountChernoffMGFBound] using
    hitCount_concentrates_chernoff_of_mgf_bound P X i j
      (sqMagProb A i j) lam Q hlam hmgf














/-- Chernoff-selected natural budget for a fixed exponential parameter `lam`:

`Q = ceil((steps * p * (exp lam - 1) - log δ) / lam)`.

With `lam > 0` and `δ > 0`, this makes the Chernoff tail at most `δ`. -/
noncomputable def chernoffHitCountBudget (steps : ℕ)
    (p lam δ : ℝ) : ℕ :=
  Nat.ceil (((steps : ℝ) * p * (Real.exp lam - 1) - Real.log δ) / lam)

/-- Squared-magnitude specialization of the Chernoff-selected budget. -/
noncomputable def sqMagChernoffHitCountBudget {m n : ℕ} (steps : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (lam δ : ℝ) : ℕ :=
  chernoffHitCountBudget steps (sqMagProb A i j) lam δ

theorem chernoffHitCountBudget_tail {steps : ℕ} {p lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) :
    chernoffHitCountTail steps p lam
        (chernoffHitCountBudget steps p lam δ) ≤ δ := by
  let a : ℝ := (steps : ℝ) * p * (Real.exp lam - 1)
  let Q : ℕ := chernoffHitCountBudget steps p lam δ
  have hceil :
      (a - Real.log δ) / lam ≤ (Q : ℝ) := by
    unfold Q chernoffHitCountBudget
    exact Nat.le_ceil ((a - Real.log δ) / lam)
  have hQle :
      (Q : ℝ) ≤ (((Q + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_succ Q
  have htarget :
      a - Real.log δ ≤ lam * (((Q + 1 : ℕ) : ℝ)) := by
    have hdiv :
        (a - Real.log δ) / lam ≤ (((Q + 1 : ℕ) : ℝ)) :=
      le_trans hceil hQle
    have hdiv' : a - Real.log δ ≤ (((Q + 1 : ℕ) : ℝ)) * lam := by
      rwa [div_le_iff₀ hlam] at hdiv
    linarith
  have hexponent :
      a - lam * (((Q + 1 : ℕ) : ℝ)) ≤ Real.log δ := by
    linarith
  have hexp :
      Real.exp (a - lam * (((Q + 1 : ℕ) : ℝ))) ≤
        Real.exp (Real.log δ) :=
    Real.exp_le_exp.mpr hexponent
  have hlog : Real.exp (Real.log δ) = δ := Real.exp_log hδ
  simpa [chernoffHitCountTail, a, Q, hlog] using hexp

theorem sqMagChernoffHitCountBudget_tail {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    sqMagChernoffHitCountTail steps A i j lam
        (sqMagChernoffHitCountBudget steps A i j lam δ) ≤ δ := by
  simpa [sqMagChernoffHitCountTail, sqMagChernoffHitCountBudget] using
    chernoffHitCountBudget_tail
      (steps := steps) (p := sqMagProb A i j) hlam hδ




















/-- Optimized Chernoff upper-tail expression, obtained from
    `chernoffHitCountTail` by choosing
    `lam = log((Q+1)/(steps*p))`.

This is the sharp Chernoff exponent for a Bernoulli-sum upper tail at the
threshold `Q+1`, under the side conditions `0 < steps*p` and
`steps*p < Q+1`. -/
noncomputable def chernoffOptimizedHitCountTail
    (steps : ℕ) (p : ℝ) (Q : ℕ) : ℝ :=
  chernoffHitCountTail steps p
    (Real.log ((((Q + 1 : ℕ) : ℝ)) / ((steps : ℝ) * p))) Q

/-- Squared-magnitude specialization of the optimized Chernoff tail. -/
noncomputable def sqMagChernoffOptimizedHitCountTail {m n : ℕ}
    (steps : ℕ) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (Q : ℕ) : ℝ :=
  chernoffOptimizedHitCountTail steps (sqMagProb A i j) Q

/-- Optimized Chernoff concentration for the hit counter. The exponential
    parameter is chosen as `log((Q+1)/(steps*p))`, which minimizes the
    Chernoff upper-tail expression for this threshold. -/
theorem hitCount_concentrates_chernoff_optimized_of_mgf_bound {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ) (Q : ℕ)
    (hμ : 0 < (steps : ℝ) * p)
    (hQ : (steps : ℝ) * p < (((Q + 1 : ℕ) : ℝ)))
    (hmgf : hitCountChernoffMGFBound P X i j p) :
    1 - chernoffOptimizedHitCountTail steps p Q ≤
      P.eventProb (hitCountAtMostEvent X i j Q) := by
  let T : ℝ := (((Q + 1 : ℕ) : ℝ))
  let μ : ℝ := (steps : ℝ) * p
  have hTpos : 0 < T := by
    unfold T
    exact_mod_cast Nat.succ_pos Q
  have hratio_pos : 0 < T / μ := div_pos hTpos hμ
  have hratio_gt_one : 1 < T / μ := by
    rw [one_lt_div hμ]
    simpa [T, μ] using hQ
  have hlam : 0 < Real.log (T / μ) :=
    (Real.log_pos_iff (le_of_lt hratio_pos)).mpr hratio_gt_one
  simpa [chernoffOptimizedHitCountTail, T, μ] using
    hitCount_concentrates_chernoff_of_mgf_bound P X i j p
      (Real.log (T / μ)) Q hlam hmgf

/-- Squared-magnitude optimized Chernoff concentration for the hit counter. -/
theorem hitCount_concentrates_sqMag_chernoff_optimized_of_mgf_bound
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ)
    (hμ : 0 < (steps : ℝ) * sqMagProb A i j)
    (hQ : (steps : ℝ) * sqMagProb A i j <
      (((Q + 1 : ℕ) : ℝ)))
    (hmgf : sqMagHitCountChernoffMGFBound P A X i j) :
    1 - sqMagChernoffOptimizedHitCountTail steps A i j Q ≤
      P.eventProb (hitCountAtMostEvent X i j Q) := by
  simpa [sqMagChernoffOptimizedHitCountTail,
    sqMagHitCountChernoffMGFBound] using
    hitCount_concentrates_chernoff_optimized_of_mgf_bound
      P X i j (sqMagProb A i j) Q hμ hQ hmgf




































/-- Event that the hit counter lies within real radius `ε` of a center `μ`. -/
def hitCountDeviationEvent {Ω : Type*} {m n steps : ℕ}
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (μ ε : ℝ) : Set Ω :=
  {ω | |(hitCount (X ω) i j : ℝ) - μ| ≤ ε}

/-- Chebyshev concentration of the hit counter around `steps * p`, assuming
    marginal hit probability `p` and pairwise independence of distinct hit
    indicators. -/
theorem hitCount_concentrates_around_mean_pairwise {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p ε δ : ℝ) (hε : 0 < ε)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} = p * p)
    (htail :
      hitCountPairwiseCenteredMoment steps p / ε ^ 2 ≤ δ) :
    1 - δ ≤
      P.eventProb
        (hitCountDeviationEvent X i j ((steps : ℝ) * p) ε) := by
  have hmoment :=
    expectationReal_hitCount_centered_sq_eq_pairwise P X i j p hmarginal hpairwise
  exact FiniteProbability.eventProb_abs_sub_le_ge_one_sub_of_second_moment
    P (fun ω => (hitCount (X ω) i j : ℝ)) ((steps : ℝ) * p) ε δ hε
    (by simpa [hmoment])

/-- Squared-magnitude specialization of the pairwise Chebyshev concentration:
    `qᵢⱼ` concentrates around `steps * pᵢⱼ`, where
    `pᵢⱼ = sqMagProb A i j`. -/
theorem hitCount_concentrates_sqMag_around_mean_pairwise {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (ε δ : ℝ) (hε : 0 < ε)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} =
          sqMagProb A i j * sqMagProb A i j)
    (htail :
      hitCountPairwiseCenteredMoment steps (sqMagProb A i j) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      P.eventProb
        (hitCountDeviationEvent X i j
          ((steps : ℝ) * sqMagProb A i j) ε) :=
  hitCount_concentrates_around_mean_pairwise P X i j
    (sqMagProb A i j) ε δ hε hmarginal hpairwise htail

/-- Chebyshev radius selected from the pairwise second moment:
    `ε = M / δ + 1`, where `M` is the centered second moment.

The extra `+1` keeps the radius strictly positive and avoids a square-root
dependency while still giving `M / ε² ≤ δ` for `δ > 0`. -/
noncomputable def chebyshevHitCountRadius (steps : ℕ) (p δ : ℝ) : ℝ :=
  hitCountPairwiseCenteredMoment steps p / δ + 1

/-- Chebyshev-selected natural budget:
    `Q = ceil(steps * p + ε)`, with
    `ε = hitCountPairwiseCenteredMoment steps p / δ + 1`. -/
noncomputable def chebyshevHitCountBudget (steps : ℕ) (p δ : ℝ) : ℕ :=
  Nat.ceil ((steps : ℝ) * p + chebyshevHitCountRadius steps p δ)

/-- Squared-magnitude specialization of the Chebyshev-selected budget. -/
noncomputable def sqMagChebyshevHitCountBudget {m n : ℕ} (steps : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (δ : ℝ) : ℕ :=
  chebyshevHitCountBudget steps (sqMagProb A i j) δ

theorem chebyshevHitCountRadius_pos {steps : ℕ} {p δ : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ hitCountPairwiseCenteredMoment steps p) :
    0 < chebyshevHitCountRadius steps p δ := by
  unfold chebyshevHitCountRadius
  have hdiv : 0 ≤ hitCountPairwiseCenteredMoment steps p / δ :=
    div_nonneg hM (le_of_lt hδ)
  linarith

theorem hitCountPairwiseCenteredMoment_div_chebyshevRadius_sq_le
    {steps : ℕ} {p δ : ℝ} (hδ : 0 < δ)
    (hM : 0 ≤ hitCountPairwiseCenteredMoment steps p) :
    hitCountPairwiseCenteredMoment steps p /
        (chebyshevHitCountRadius steps p δ) ^ 2 ≤ δ := by
  have hε := chebyshevHitCountRadius_pos (steps := steps) (p := p) hδ hM
  rw [div_le_iff₀ (sq_pos_of_pos hε)]
  unfold chebyshevHitCountRadius
  field_simp [hδ.ne']
  nlinarith [sq_nonneg (hitCountPairwiseCenteredMoment steps p),
    hM, hδ]

theorem chebyshevHitCountBudget_mean_add_radius_le {steps : ℕ} {p δ : ℝ} :
    (steps : ℝ) * p + chebyshevHitCountRadius steps p δ ≤
      (chebyshevHitCountBudget steps p δ : ℝ) := by
  unfold chebyshevHitCountBudget
  exact Nat.le_ceil ((steps : ℝ) * p + chebyshevHitCountRadius steps p δ)

theorem sqMagChebyshevHitCountBudget_mean_add_radius_le {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (δ : ℝ) :
    (steps : ℝ) * sqMagProb A i j +
        chebyshevHitCountRadius steps (sqMagProb A i j) δ ≤
      (sqMagChebyshevHitCountBudget steps A i j δ : ℝ) := by
  simpa [sqMagChebyshevHitCountBudget] using
    chebyshevHitCountBudget_mean_add_radius_le
      (steps := steps) (p := sqMagProb A i j) (δ := δ)

theorem hitCountDeviationEvent_subset_hitCountAtMostEvent {Ω : Type*}
    {m n steps : ℕ} (X : Ω → ElementwiseTrace m n steps)
    (i : Fin m) (j : Fin n) (μ ε : ℝ) (Q : ℕ)
    (hQ : μ + ε ≤ (Q : ℝ)) :
    hitCountDeviationEvent X i j μ ε ⊆ hitCountAtMostEvent X i j Q := by
  intro ω hω
  have hupper : (hitCount (X ω) i j : ℝ) - μ ≤ ε :=
    (abs_le.mp hω).2
  have hreal : (hitCount (X ω) i j : ℝ) ≤ Q := by
    linarith
  exact_mod_cast hreal

theorem probability_sqMagTraceStability_of_hitCount_deviation
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (ρ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (μ ε : ℝ) (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQreal : μ + ε ≤ (Q : ℝ))
    (hQvalid : gammaValid fp Q) (hQ1valid : gammaValid fp (Q + 1))
    (hprob : ρ ≤ P.eventProb (hitCountDeviationEvent X i j μ ε)) :
    ρ ≤ P.eventProb (sqMagTraceStabilityEvent fp s A Atilde X i j Q) := by
  exact le_trans hprob
    (FiniteProbability.eventProb_mono P
      (Set.Subset.trans
        (hitCountDeviationEvent_subset_hitCountAtMostEvent X i j μ ε Q hQreal)
        (hitCountAtMostEvent_subset_sqMagTraceStabilityEvent fp s A Atilde
          X i j Q hs hAij hQvalid hQ1valid)))













































































-- ============================================================
-- Stability with the proved hit-count concentration
-- ============================================================




























































































































end NumStability
