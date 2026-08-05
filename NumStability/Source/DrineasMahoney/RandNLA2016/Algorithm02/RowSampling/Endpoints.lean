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
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation04.RowSamplingProbability.Normalization

/-!
# NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm02.RowSampling.Endpoints

W11 canonical source correspondence destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.RowSampling`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/RowSampling.lean
--
-- Floating-point stability infrastructure for the row-sampling
-- meta-algorithm in Drineas--Mahoney's CACM RandNLA survey, Algorithm 2.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602













namespace NumStability

open scoped BigOperators

/-!
## Algorithm 2: row sampling

Algorithm 2 of Drineas and Mahoney's CACM RandNLA survey samples rows of
`A` independently with probabilities `p_i`, and inserts the rescaled sampled
row in the output sketch. Equation (4) gives the norm-squared row distribution

`p_i = ||A_i*||_2^2 / ||A||_F^2`.

This file formalizes the literal sampled output matrix: output row `t` is the
sampled input row rescaled by `1 / sqrt(s * p_i)`. Unlike Algorithm 1,
Algorithm 2 does not accumulate repeated samples into a single entry. The
probabilistic analysis therefore studies the Gram matrix `Ãᵀ Ã`, which is the
quantity compared with `Aᵀ A` in equation (5) of the paper.
-/

-- ============================================================
-- Norm-squared row sampling probabilities
-- ============================================================





























































































-- ============================================================
-- Exact and floating-point row-sampling updates
-- ============================================================







































namespace ComputedRowScaleDen

variable {fp : FPModel} {m : ℕ} {s : ℕ} {p : Fin m → ℝ}

































































































































































































end ComputedRowScaleDen











































































































































































































































































































































































-- ============================================================
-- Random row traces for the literal Algorithm 2 sampler
-- ============================================================















theorem rowSqNormTraceProbMass_sum_eq_one {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : rowSqNormProbDen A ≠ 0) :
    (∑ samples : RowTrace m steps,
      rowSqNormTraceProbMass A samples) = 1 := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (RowSample m)))
      (f := fun _ x => rowSqNormProb A x)
  have hleft :
      (∏ _ : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (RowSample m)),
          rowSqNormProb A x) = 1 := by
    simp [rowSqNormProb_sum_eq_one A hden]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (RowSample m))),
        ∏ i, rowSqNormProb A (x i))
        = ∑ samples : RowTrace m steps,
          rowSqNormTraceProbMass A samples := by
    simp [rowSqNormTraceProbMass, RowTrace]
  rw [← hright, ← hprod]
  exact hleft

/-- The canonical finite probability space for Algorithm 2 row traces with
    independent norm-squared row samples at every step. -/
noncomputable def rowSqNormTraceProbability {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A) :
    FiniteProbability (RowTrace m steps) where
  prob := rowSqNormTraceProbMass A
  prob_nonneg := rowSqNormTraceProbMass_nonneg A hden
  prob_sum := rowSqNormTraceProbMass_sum_eq_one A hden.ne'


















/-- The independent Algorithm 2 row sampler assigns probability one to traces
    whose sampled rows all have positive row-sampling probability. -/
theorem rowSqNormTraceProbability_eventProb_rowTracePositiveProb
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) :
    (rowSqNormTraceProbability (steps := steps) A hden).eventProb
      {samples | rowTracePositiveProb A samples} = 1 := by
  classical
  let P := rowSqNormTraceProbability (steps := steps) A hden
  let Good : Set (RowTrace m steps) := {samples | rowTracePositiveProb A samples}
  have hcompl_zero : P.eventProb Goodᶜ = 0 := by
    unfold FiniteProbability.eventProb
    apply Finset.sum_eq_zero
    intro samples _
    by_cases hbad : samples ∈ Goodᶜ
    · have hnot_good : samples ∉ Good := by simpa using hbad
      have hexists : ∃ t : Fin steps, rowSqNormProb A (samples t) = 0 := by
        by_contra hno
        have hgood : samples ∈ Good := by
          intro t
          have hne : rowSqNormProb A (samples t) ≠ 0 := by
            intro hzero
            exact hno ⟨t, hzero⟩
          exact lt_of_le_of_ne
            (rowSqNormProb_nonneg A hden (samples t)) (Ne.symm hne)
        exact hnot_good hgood
      have hmass :=
        rowSqNormTraceProbMass_eq_zero_of_exists_prob_zero A samples hexists
      simp [P, Good, rowSqNormTraceProbability, hbad, hmass]
    · simp [hbad]
  have hsplit := P.eventProb_add_eventProb_compl Good
  rw [hcompl_zero] at hsplit
  linarith

end NumStability
