-- Algorithms/RandNLA/RowSampling.lean
--
-- Floating-point stability infrastructure for the row-sampling
-- meta-algorithm in Drineas--Mahoney's CACM RandNLA survey, Algorithm 2.
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
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Analysis.FiniteProbability

namespace LeanFpAnalysis.FP

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

/-- Squared Euclidean norm of row `i`: `||A_i*||_2^2`. -/
noncomputable def rowNormSq {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : ℝ :=
  ∑ j : Fin n, A i j ^ 2

/-- Denominator for norm-squared row sampling probabilities:
    `∑ᵢ ||A_i*||_2^2 = ||A||_F^2`. -/
noncomputable def rowSqNormProbDen {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  frobNormSqRect A

/-- Norm-squared row sampling probability from equation (4):
    `p_i = ||A_i*||_2^2 / ||A||_F^2`. -/
noncomputable def rowSqNormProb {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : ℝ :=
  rowNormSq A i / rowSqNormProbDen A

/-- The squared row norms sum to the squared Frobenius norm. -/
theorem rowNormSq_sum_eq_frobNormSqRect {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    ∑ i : Fin m, rowNormSq A i = frobNormSqRect A := rfl

/-- Squared row norms are nonnegative. -/
theorem rowNormSq_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : 0 ≤ rowNormSq A i := by
  unfold rowNormSq
  exact Finset.sum_nonneg fun j _ => sq_nonneg (A i j)

/-- A squared row norm is zero iff the whole row is zero. -/
theorem rowNormSq_eq_zero_iff {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : rowNormSq A i = 0 ↔ ∀ j : Fin n, A i j = 0 := by
  unfold rowNormSq
  constructor
  · intro h
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)), A i j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (A i j))).mp h
    intro j
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp
      (hterm j (Finset.mem_univ j))
  · intro h
    apply Finset.sum_eq_zero
    intro j _
    rw [h j]
    ring

/-- A row containing a nonzero entry has positive squared row norm. -/
theorem rowNormSq_pos_of_entry_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m)
    (j : Fin n) (hAij : A i j ≠ 0) :
    0 < rowNormSq A i := by
  exact lt_of_le_of_ne (rowNormSq_nonneg A i)
    (fun hzero => hAij ((rowNormSq_eq_zero_iff A i).mp hzero.symm j))

/-- Norm-squared row probabilities are nonnegative when the Frobenius
    denominator is positive. -/
theorem rowSqNormProb_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (i : Fin m) :
    0 ≤ rowSqNormProb A i := by
  unfold rowSqNormProb
  exact div_nonneg (rowNormSq_nonneg A i) (le_of_lt hden)

/-- A row containing a nonzero entry has positive norm-squared probability. -/
theorem rowSqNormProb_pos_of_entry_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) (j : Fin n) (hAij : A i j ≠ 0) :
    0 < rowSqNormProb A i := by
  unfold rowSqNormProb
  exact div_pos (rowNormSq_pos_of_entry_ne_zero A i j hAij) hden

/-- Norm-squared row probabilities sum to one for a nonzero matrix. -/
theorem rowSqNormProb_sum_eq_one {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : rowSqNormProbDen A ≠ 0) :
    ∑ i : Fin m, rowSqNormProb A i = 1 := by
  unfold rowSqNormProb rowSqNormProbDen
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  change frobNormSqRect A * (frobNormSqRect A)⁻¹ = 1
  exact mul_inv_cancel₀ hden

/-- A row containing a nonzero entry has nonzero norm-squared probability. -/
theorem rowSqNormProb_ne_zero_of_entry_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m)
    (j : Fin n) (hAij : A i j ≠ 0) :
    rowSqNormProb A i ≠ 0 := by
  unfold rowSqNormProb rowSqNormProbDen
  have hrow : rowNormSq A i ≠ 0 :=
    ne_of_gt (rowNormSq_pos_of_entry_ne_zero A i j hAij)
  have hden : frobNormSqRect A ≠ 0 :=
    frobNormSqRect_ne_zero_of_entry_ne_zero A i j hAij
  exact div_ne_zero hrow hden

-- ============================================================
-- Exact and floating-point row-sampling updates
-- ============================================================

/-- A sampled row of an `m × n` matrix. -/
abbrev RowSample (m : ℕ) := Fin m

/-- A deterministic trace of sampled rows. -/
abbrev RowTrace (m steps : ℕ) := Fin steps → RowSample m

/-- Algorithm 2 row-rescaling denominator `sqrt(s * p_i)`. -/
noncomputable def rowSampleScaleDen {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  Real.sqrt ((s : ℝ) * rowSqNormProb A i)

/-- The row-rescaling denominator is nonzero when `s > 0` and the sampled row
    has positive probability. -/
theorem rowSampleScaleDen_ne_zero {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m)
    (hs : 0 < (s : ℝ)) (hprob : 0 < rowSqNormProb A i) :
    rowSampleScaleDen s A i ≠ 0 := by
  have hmul : 0 < (s : ℝ) * rowSqNormProb A i :=
    mul_pos hs hprob
  exact ne_of_gt (by
    unfold rowSampleScaleDen
    exact Real.sqrt_pos.2 hmul)

/-- Exact Algorithm 2 row-scaling contribution for entry `(i, j)`. -/
noncomputable def rowSampleIncrement {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  A i j / rowSampleScaleDen s A i

/-- Floating-point Algorithm 2 row-scaling contribution for entry `(i, j)`. -/
noncomputable def fl_rowSampleIncrement (fp : FPModel) {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  fp.fl_div (A i j) (rowSampleScaleDen s A i)

/-- Forward-error bound for a floating-point division. -/
theorem fl_div_error_bound (fp : FPModel) (a denom : ℝ)
    (hdenom : denom ≠ 0) :
    |fp.fl_div a denom - a / denom| ≤ |a / denom| * fp.u := by
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div a denom hdenom
  let t : ℝ := a / denom
  have herr : fp.fl_div a denom - t = t * δ := by
    rw [hdiv]
    ring
  calc
    |fp.fl_div a denom - a / denom|
        = |t * δ| := by
            rw [herr]
    _ = |t| * |δ| := abs_mul _ _
    _ ≤ |t| * fp.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = |a / denom| * fp.u := by
            simp [t]

/-- Forward-error bound for one row-sampled output entry. This is the local
    division kernel used by Algorithm 2. -/
theorem fl_rowSampleIncrement_error_bound (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n)
    (hdenom : rowSampleScaleDen s A i ≠ 0) :
    |fl_rowSampleIncrement fp s A i j -
      rowSampleIncrement s A i j| ≤
      |rowSampleIncrement s A i j| * fp.u := by
  unfold fl_rowSampleIncrement rowSampleIncrement
  exact fl_div_error_bound fp (A i j) (rowSampleScaleDen s A i) hdenom

/-- Exact Algorithm 2 output sketch: output row `t` is the sampled input row
    rescaled by `1 / sqrt(s * p_i)`. -/
noncomputable def rowSampleSketch {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin steps → Fin n → ℝ :=
  fun t j => rowSampleIncrement s A (samples t) j

/-- Floating-point Algorithm 2 output sketch, using the rounded division for
    each sampled row entry. -/
noncomputable def fl_rowSampleSketch (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin steps → Fin n → ℝ :=
  fun t j => fl_rowSampleIncrement fp s A (samples t) j

/-- Entrywise forward-error bound for the literal `s × n` Algorithm 2 output
    sketch. -/
theorem fl_rowSampleSketch_error_bound (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hdenom : rowSampleScaleDen s A (samples t) ≠ 0) :
    |fl_rowSampleSketch fp s A samples t j -
      rowSampleSketch s A samples t j| ≤
      |rowSampleSketch s A samples t j| * fp.u := by
  exact fl_rowSampleIncrement_error_bound fp s A (samples t) j hdenom

-- ============================================================
-- Random row traces for the literal Algorithm 2 sampler
-- ============================================================

/-- Product probability mass of an Algorithm 2 row trace when each step samples
    independently from the norm-squared row probabilities. -/
noncomputable def rowSqNormTraceProbMass {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) : ℝ :=
  ∏ t : Fin steps, rowSqNormProb A (samples t)

theorem rowSqNormTraceProbMass_nonneg {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (samples : RowTrace m steps) :
    0 ≤ rowSqNormTraceProbMass A samples := by
  unfold rowSqNormTraceProbMass
  exact Finset.prod_nonneg fun t _ =>
    rowSqNormProb_nonneg A hden (samples t)

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

/-- Trace-support predicate for Algorithm 2: every sampled row has positive
    norm-squared probability. Zero-probability rows have zero mass under the
    product trace law, but this predicate is exactly where the floating-point
    division model can be applied without a denominator-zero premise. -/
def rowTracePositiveProb {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) : Prop :=
  ∀ t : Fin steps, 0 < rowSqNormProb A (samples t)

theorem rowSqNormTraceProbMass_eq_zero_of_exists_prob_zero {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps)
    (hzero : ∃ t : Fin steps, rowSqNormProb A (samples t) = 0) :
    rowSqNormTraceProbMass A samples = 0 := by
  classical
  rcases hzero with ⟨t, ht⟩
  unfold rowSqNormTraceProbMass
  exact Finset.prod_eq_zero (Finset.mem_univ t) ht

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

end LeanFpAnalysis.FP
