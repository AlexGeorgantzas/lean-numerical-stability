import NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.HitCounts.Bounds
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.Elementwise.Core
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixConcentration
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.SpectralTransfer.Elementwise

W11 canonical reusable randomized linear algebra destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.ElementwiseSpectral`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/ElementwiseSpectral.lean
--
-- Deterministic spectral-norm transfer infrastructure for Algorithm 1.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602
--
-- The hard-thresholded source-alignment layer follows:
-- Petros Drineas and Anastasios Zouzias, "A Note on Element-wise Matrix
-- Sparsification via a Matrix-valued Bernstein Inequality," arXiv:1006.0407.
-- https://arxiv.org/pdf/1006.0407









namespace NumStability

open scoped BigOperators ComplexOrder

/-!
## Algorithm 1 spectral transfer layer

The CACM RandNLA survey states a high-probability spectral-norm concentration
bound for Algorithm 1, equation (2).  This file proves deterministic spectral
and floating-point transfer infrastructure and several exact concentration
layers for the truncated self-adjoint dilation route, including parameterized
trace-MGF-to-eigenvalue tails.  The remaining open piece is the final
theta-optimization/source-constant conversion from the scaled dilation
eigenvalue statement to the exact CACM equation (2) spectral-norm theorem:

* if the exact sampled residual satisfies a rectangular vector-action
  operator-2 bound, and
* if the floating-point sampled sketch is entrywise close to the exact sampled
  sketch,

then the floating-point sampled residual satisfies the same operator-2 bound
with the rectangular Frobenius norm of the entrywise perturbation budget added.

This keeps the equation (2) backlog explicit: the missing piece is the final
source-constant concentration conversion, not the lower-level trace-MGF or
floating-point transfer infrastructure.
-/

-- ============================================================
-- Residuals and spectral events
-- ============================================================

/-- Exact Algorithm 1 residual `A - Atilde` for a deterministic trace, starting
    the sketch from zero. -/
noncomputable def elementwiseTraceResidual {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) :
    Fin m → Fin n → ℝ :=
  fun i j => A i j - elementwiseTraceSketch s A (fun _ _ => 0) samples i j

/-- Floating-point Algorithm 1 residual `A - fl(Atilde)` for a deterministic
    trace, starting the sketch from zero. -/
noncomputable def fl_elementwiseTraceResidual (fp : FPModel) {m n steps : ℕ}
    (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Fin m → Fin n → ℝ :=
  fun i j => A i j - fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j

/-- Exact Algorithm 1 residual when the sampler rescales with a supplied exact
    probability table `p`. -/
noncomputable def elementwiseTraceResidualWithProb {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Fin m → Fin n → ℝ :=
  fun i j =>
    A i j - elementwiseTraceSketchWithProb s A (fun _ _ => 0) p samples i j

/-- Floating-point Algorithm 1 residual when the sampler rescales with a
    supplied exact probability table `p`. -/
noncomputable def fl_elementwiseTraceResidualWithProb (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    A i j -
      fl_elementwiseTraceSketchWithProb fp s A (fun _ _ => 0) p samples i j

/-- Entrywise hard-thresholding used by the primary Drineas--Zouzias
    matrix-Bernstein source for elementwise sparsification.  Entries with
    magnitude below `tau` are zeroed; all other entries are left unchanged. -/
noncomputable def elementwiseTruncate {m n : ℕ} (tau : ℝ)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => if |A i j| < tau then 0 else A i j

/-- Exact residual of the truncated Algorithm 1 sketch against the original
    input matrix.  The sketch is built from `elementwiseTruncate tau A`, while
    the final error is measured against `A`. -/
noncomputable def elementwiseTruncatedTraceResidual {m n steps : ℕ}
    (tau : ℝ) (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Fin m → Fin n → ℝ :=
  fun i j =>
    A i j -
      elementwiseTraceSketch s (elementwiseTruncate tau A) (fun _ _ => 0)
        samples i j

/-- Floating-point residual of the truncated Algorithm 1 sketch against the
    original input matrix. -/
noncomputable def fl_elementwiseTruncatedTraceResidual (fp : FPModel)
    {m n steps : ℕ} (tau : ℝ) (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Fin m → Fin n → ℝ :=
  fun i j =>
    A i j -
      fl_elementwiseTraceSketch fp s (elementwiseTruncate tau A)
        (fun _ _ => 0) samples i j

/-- Exact residual of the truncated Algorithm 1 sketch when the sampler uses a
    supplied exact probability table for the truncated matrix. -/
noncomputable def elementwiseTruncatedTraceResidualWithProb {m n steps : ℕ}
    (tau : ℝ) (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    A i j -
      elementwiseTraceSketchWithProb s (elementwiseTruncate tau A)
        (fun _ _ => 0) p samples i j

/-- Floating-point residual of the truncated Algorithm 1 sketch when the
    sampler uses a supplied exact probability table for the
    truncated matrix. -/
noncomputable def fl_elementwiseTruncatedTraceResidualWithProb (fp : FPModel)
    {m n steps : ℕ} (tau : ℝ) (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    A i j -
      fl_elementwiseTraceSketchWithProb fp s (elementwiseTruncate tau A)
        (fun _ _ => 0) p samples i j

/-- The deterministic truncation error is entrywise bounded by the threshold. -/
theorem elementwiseTruncate_error_entry_abs_le {m n : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (htau : 0 ≤ tau)
    (i : Fin m) (j : Fin n) :
    |A i j - elementwiseTruncate tau A i j| ≤ tau := by
  unfold elementwiseTruncate
  by_cases hsmall : |A i j| < tau
  · simp [hsmall]
    exact le_of_lt hsmall
  · simp [hsmall, htau]

/-- Hard-thresholding cannot increase the magnitude of any entry. -/
theorem elementwiseTruncate_abs_le {m n : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    |elementwiseTruncate tau A i j| ≤ |A i j| := by
  unfold elementwiseTruncate
  by_cases hsmall : |A i j| < tau
  · simp [hsmall]
  · simp [hsmall]

/-- If every nonzero entry already has magnitude at least the threshold, then
hard-thresholding does not change the matrix.

This is used only as an adapter from the source-aligned truncated
matrix-Bernstein theorem back to the literal Algorithm 1 law on inputs for
which the source truncation is the identity. -/
theorem elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge
    {m n : ℕ} {tau : ℝ} (A : Fin m → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → tau ≤ |A i j|) :
    elementwiseTruncate tau A = A := by
  funext i j
  unfold elementwiseTruncate
  by_cases hsmall : |A i j| < tau
  · have hzero : A i j = 0 := by
      by_contra hne
      exact (not_lt_of_ge (hentry i j hne)) hsmall
    simp [hzero]
  · simp [hsmall]

/-- Hard-thresholding cannot increase the squared rectangular Frobenius norm. -/
theorem frobNormSqRect_elementwiseTruncate_le {m n : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) :
    frobNormSqRect (elementwiseTruncate tau A) ≤ frobNormSqRect A := by
  unfold frobNormSqRect
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact (sq_le_sq).mpr (elementwiseTruncate_abs_le tau A i j)

/-- Hard-thresholding cannot increase the rectangular Frobenius norm. -/
theorem frobNormRect_elementwiseTruncate_le {m n : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) :
    frobNormRect (elementwiseTruncate tau A) ≤ frobNormRect A := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt (frobNormSqRect_elementwiseTruncate_le tau A)

/-- A nonzero retained entry of the hard-thresholded matrix has magnitude at
    least the threshold. -/
theorem elementwiseTruncate_nonzero_abs_ge {m n : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hij : elementwiseTruncate tau A i j ≠ 0) :
    tau ≤ |elementwiseTruncate tau A i j| := by
  unfold elementwiseTruncate at hij ⊢
  by_cases hsmall : |A i j| < tau
  · simp [hsmall] at hij
  · simp [hsmall]
    exact le_of_not_gt hsmall

/-- If the truncated matrix has nonzero squared-magnitude denominator, then
its Frobenius norm is at least the truncation threshold.  This is the local
source-sample-complexity fact used to control the linear `eps * ||Ahat||_F`
term in the Bernstein denominator. -/
theorem elementwiseTruncate_tau_le_frobNormRect_of_sqMagProbDen_pos
    {m n : ℕ} {tau : ℝ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    tau ≤ frobNormRect (elementwiseTruncate tau A) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  have hnot_all_zero : ¬ ∀ i j, Ahat i j = 0 := by
    intro hall
    have hzero : frobNormSqRect Ahat = 0 :=
      (frobNormSqRect_eq_zero_iff Ahat).mpr hall
    have hpos : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    linarith
  push_neg at hnot_all_zero
  rcases hnot_all_zero with ⟨i, j, hij⟩
  have htaule : tau ≤ |Ahat i j| := by
    simpa [Ahat] using
      elementwiseTruncate_nonzero_abs_ge (tau := tau) A i j hij
  have hentry_sq_le :
      Ahat i j ^ 2 ≤ frobNormSqRect Ahat := by
    unfold frobNormSqRect
    have hrow :
        Ahat i j ^ 2 ≤ ∑ b : Fin n, Ahat i b ^ 2 :=
      Finset.single_le_sum (fun b _ => sq_nonneg (Ahat i b))
        (Finset.mem_univ j)
    have hrow_nonneg :
        ∀ a : Fin m, 0 ≤ ∑ b : Fin n, Ahat a b ^ 2 :=
      fun a => Finset.sum_nonneg (fun b _ => sq_nonneg (Ahat a b))
    exact hrow.trans
      (Finset.single_le_sum (fun a _ => hrow_nonneg a) (Finset.mem_univ i))
  have habs_le_frob : |Ahat i j| ≤ frobNormRect Ahat := by
    have hsq :
        |Ahat i j| ^ 2 ≤ frobNormRect Ahat ^ 2 := by
      rw [sq_abs, frobNormRect_sq]
      exact hentry_sq_le
    have hsq_abs := (sq_le_sq).mp hsq
    simpa [abs_of_nonneg (frobNormRect_nonneg Ahat)] using hsq_abs
  exact htaule.trans habs_le_frob

/-- For the hard-thresholded matrix, a one-sample contribution from a retained
    entry is entrywise bounded by `||Ahat||_F^2 / (s*tau)`.  This is the
    bounded-increment side condition needed before a Bernstein proof can be
    instantiated for the truncated source route. -/
theorem elementwiseSampleContribution_truncated_entry_abs_le
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0)
    (i : Fin m) (j : Fin n) :
    |elementwiseSampleContribution s (elementwiseTruncate tau A) sample i j| ≤
      frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have hF_nonneg : 0 ≤ frobNormSqRect Ahat := frobNormSqRect_nonneg Ahat
  have hden_tau_pos : 0 < (s : ℝ) * tau := mul_pos hs htau
  have hbound_nonneg :
      0 ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) :=
    div_nonneg hF_nonneg (le_of_lt hden_tau_pos)
  by_cases hhit : sample.1 = i ∧ sample.2 = j
  · have hi : sample.1 = i := hhit.1
    have hj : sample.2 = j := hhit.2
    have hAij_ne : Ahat i j ≠ 0 := by
      simpa [Ahat, ← hi, ← hj] using hsample
    have htaule : tau ≤ |Ahat i j| := by
      simpa [Ahat] using
        elementwiseTruncate_nonzero_abs_ge tau A i j (by simpa [Ahat] using hAij_ne)
    have hAij_abs_pos : 0 < |Ahat i j| := lt_of_lt_of_le htau htaule
    have hden_abs_pos : 0 < (s : ℝ) * |Ahat i j| :=
      mul_pos hs hAij_abs_pos
    have hden_le : (s : ℝ) * tau ≤ (s : ℝ) * |Ahat i j| :=
      mul_le_mul_of_nonneg_left htaule (le_of_lt hs)
    have hdiv_le :
        frobNormSqRect Ahat / ((s : ℝ) * |Ahat i j|) ≤
          frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_le_div_of_nonneg_left hF_nonneg hden_tau_pos hden_le
    have hinc :
        elementwiseIncrement s Ahat i j =
          frobNormSqRect Ahat / ((s : ℝ) * Ahat i j) := by
      simpa [Ahat] using
        elementwiseIncrement_sqMag_eq s Ahat i j hs_ne hAij_ne
    calc
      |elementwiseSampleContribution s Ahat sample i j|
          = |frobNormSqRect Ahat / ((s : ℝ) * Ahat i j)| := by
              simp [elementwiseSampleContribution, hhit, hinc]
      _ = frobNormSqRect Ahat / ((s : ℝ) * |Ahat i j|) := by
              rw [abs_div, abs_mul, abs_of_nonneg (le_of_lt hs),
                abs_of_nonneg hF_nonneg]
      _ ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) := hdiv_le
  · simp [elementwiseSampleContribution, hhit]
    exact hbound_nonneg

/-- Frobenius form of
    `elementwiseSampleContribution_truncated_entry_abs_le`: for a retained
    sampled entry of the hard-thresholded matrix, the one-sample contribution
    has Frobenius norm at most `||Ahat||_F^2 / (s*tau)`. -/
theorem frobNormRect_elementwiseSampleContribution_truncated_le
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    frobNormRect
      (elementwiseSampleContribution s (elementwiseTruncate tau A) sample) ≤
      frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  have hshape :
      elementwiseSampleContribution s Ahat sample =
        fun r c =>
          if sample.1 = r ∧ sample.2 = c then
            elementwiseIncrement s Ahat sample.1 sample.2
          else
            0 := by
    ext r c
    by_cases hhit : sample.1 = r ∧ sample.2 = c
    · simp [elementwiseSampleContribution, hhit]
    · simp [elementwiseSampleContribution, hhit]
  have hentry :=
    elementwiseSampleContribution_truncated_entry_abs_le
      htau hs A sample hsample sample.1 sample.2
  have hentry' :
      |elementwiseIncrement s Ahat sample.1 sample.2| ≤
        frobNormSqRect Ahat / ((s : ℝ) * tau) := by
    simpa [Ahat, elementwiseSampleContribution] using hentry
  calc
    frobNormRect (elementwiseSampleContribution s Ahat sample)
        = |elementwiseIncrement s Ahat sample.1 sample.2| := by
            rw [hshape]
            exact frobNormRect_single_left sample.1 sample.2
              (elementwiseIncrement s Ahat sample.1 sample.2)
    _ ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) := hentry'

/-- Exact input-dependent contribution radius for the literal, untruncated
Algorithm 1 squared-magnitude sampler.

This is deliberately not a uniform source constant: it is the finite sum of the
reciprocal nonzero entry magnitudes that controls the one-sample rescaled
contribution under the exact literal law.  Tiny nonzero entries therefore make
the displayed radius large, which is the behavior exposed by the route
obstruction above. -/
noncomputable def elementwiseLiteralContributionRadius {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n,
    if A i j = 0 then 0
    else frobNormSqRect A / ((s : ℝ) * |A i j|)

/-- Exact input-dependent one-sample residual radius for the literal,
untruncated Algorithm 1 sampler. -/
noncomputable def elementwiseLiteralResidualSupportRadius {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) : ℝ :=
  (1 / (s : ℝ)) * frobNormRect A +
    elementwiseLiteralContributionRadius s A

/-- Every summand in the literal contribution radius is nonnegative when the
sample count is positive. -/
theorem elementwiseLiteralContributionRadius_term_nonneg
    {m n s : ℕ} (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    0 ≤
      (if A i j = 0 then 0
       else frobNormSqRect A / ((s : ℝ) * |A i j|)) := by
  by_cases hzero : A i j = 0
  · simp [hzero]
  · have habs_pos : 0 < |A i j| := abs_pos.mpr hzero
    have hden_pos : 0 < (s : ℝ) * |A i j| := mul_pos hs habs_pos
    simp [hzero, div_nonneg (frobNormSqRect_nonneg A) (le_of_lt hden_pos)]

/-- The literal contribution radius is nonnegative when the sample count is
positive. -/
theorem elementwiseLiteralContributionRadius_nonneg
    {m n s : ℕ} (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ) :
    0 ≤ elementwiseLiteralContributionRadius s A := by
  unfold elementwiseLiteralContributionRadius
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact elementwiseLiteralContributionRadius_term_nonneg hs A i j

/-- If every nonzero entry is bounded below by `alpha`, then the literal
reciprocal-entry contribution radius is bounded by a simple floor-dependent
quantity.

This is a deterministic exact-arithmetic simplification of
`elementwiseLiteralContributionRadius`; it is not a probability statement. -/
theorem elementwiseLiteralContributionRadius_le_of_entry_abs_ge
    {m n s : ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|) :
    elementwiseLiteralContributionRadius s A ≤
      ((m : ℝ) * (n : ℝ)) *
        (frobNormSqRect A / ((s : ℝ) * alpha)) := by
  classical
  let C : ℝ := frobNormSqRect A / ((s : ℝ) * alpha)
  have hC_nonneg : 0 ≤ C :=
    div_nonneg (frobNormSqRect_nonneg A)
      (mul_nonneg (le_of_lt hs) (le_of_lt halpha))
  have hterm_le :
      ∀ i j,
        (if A i j = 0 then 0
         else frobNormSqRect A / ((s : ℝ) * |A i j|)) ≤ C := by
    intro i j
    by_cases hzero : A i j = 0
    · simpa [hzero, C] using hC_nonneg
    · have habs_pos : 0 < |A i j| := abs_pos.mpr hzero
      have halpha_le : alpha ≤ |A i j| := hentry i j hzero
      have hden_alpha_pos : 0 < (s : ℝ) * alpha := mul_pos hs halpha
      have hden_le : (s : ℝ) * alpha ≤ (s : ℝ) * |A i j| :=
        mul_le_mul_of_nonneg_left halpha_le (le_of_lt hs)
      have hle :
          frobNormSqRect A / ((s : ℝ) * |A i j|) ≤
            frobNormSqRect A / ((s : ℝ) * alpha) :=
        div_le_div_of_nonneg_left (frobNormSqRect_nonneg A)
          hden_alpha_pos hden_le
      simpa [hzero, C] using hle
  calc
    elementwiseLiteralContributionRadius s A
        = ∑ i : Fin m, ∑ j : Fin n,
            (if A i j = 0 then 0
             else frobNormSqRect A / ((s : ℝ) * |A i j|)) := by
              rfl
    _ ≤ ∑ i : Fin m, ∑ _j : Fin n, C := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact hterm_le i j
    _ = ((m : ℝ) * (n : ℝ)) * C := by
          simp [C, Finset.sum_const, nsmul_eq_mul]
          ring
    _ = ((m : ℝ) * (n : ℝ)) *
        (frobNormSqRect A / ((s : ℝ) * alpha)) := by
          simp [C]

/-- Entry-floor simplification for the literal one-sample residual support
radius. -/
theorem elementwiseLiteralResidualSupportRadius_le_of_entry_abs_ge
    {m n s : ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|) :
    elementwiseLiteralResidualSupportRadius s A ≤
      (1 / (s : ℝ)) * frobNormRect A +
        ((m : ℝ) * (n : ℝ)) *
          (frobNormSqRect A / ((s : ℝ) * alpha)) := by
  have hR :=
    elementwiseLiteralContributionRadius_le_of_entry_abs_ge
      halpha hs A hentry
  simpa [elementwiseLiteralResidualSupportRadius] using
    add_le_add_left hR ((1 / (s : ℝ)) * frobNormRect A)

/-- Scaled version of the entry-floor contribution-radius bound, in the form
used by the literal floating-point scalar radius. -/
theorem smul_elementwiseLiteralContributionRadius_le_of_entry_abs_ge
    {m n s : ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|) :
    (s : ℝ) * elementwiseLiteralContributionRadius s A ≤
      ((m : ℝ) * (n : ℝ)) * (frobNormSqRect A / alpha) := by
  have hR :=
    elementwiseLiteralContributionRadius_le_of_entry_abs_ge
      halpha hs A hentry
  have hmul :=
    mul_le_mul_of_nonneg_left hR (le_of_lt hs)
  have hcancel_core :
      (s : ℝ) * (frobNormSqRect A / (alpha * (s : ℝ))) =
        frobNormSqRect A / alpha := by
    field_simp [hs.ne', halpha.ne']
  simpa [hcancel_core, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Any nonzero entry's reciprocal contribution is bounded by the finite
literal contribution radius. -/
theorem literal_entry_contribution_le_elementwiseLiteralContributionRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    (if A i j = 0 then 0
     else frobNormSqRect A / ((s : ℝ) * |A i j|)) ≤
      elementwiseLiteralContributionRadius s A := by
  classical
  unfold elementwiseLiteralContributionRadius
  let term : Fin m → Fin n → ℝ :=
    fun a b =>
      if A a b = 0 then 0
      else frobNormSqRect A / ((s : ℝ) * |A a b|)
  have hterm_nonneg : ∀ a b, 0 ≤ term a b := by
    intro a b
    exact elementwiseLiteralContributionRadius_term_nonneg hs A a b
  have hrow :
      term i j ≤ ∑ b : Fin n, term i b :=
    Finset.single_le_sum (fun b _ => hterm_nonneg i b) (Finset.mem_univ j)
  have hrow_nonneg : ∀ a : Fin m, 0 ≤ ∑ b : Fin n, term a b := by
    intro a
    exact Finset.sum_nonneg (fun b _ => hterm_nonneg a b)
  exact hrow.trans
    (Finset.single_le_sum (fun a _ => hrow_nonneg a) (Finset.mem_univ i))

/-- For the literal untruncated matrix, a one-sample contribution from a
positive-probability entry is bounded by the explicit input-dependent
contribution radius. -/
theorem elementwiseSampleContribution_literal_entry_abs_le
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample : A sample.1 sample.2 ≠ 0)
    (i : Fin m) (j : Fin n) :
    |elementwiseSampleContribution s A sample i j| ≤
      elementwiseLiteralContributionRadius s A := by
  classical
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have hRadius_nonneg :
      0 ≤ elementwiseLiteralContributionRadius s A :=
    elementwiseLiteralContributionRadius_nonneg hs A
  by_cases hhit : sample.1 = i ∧ sample.2 = j
  · have hi : sample.1 = i := hhit.1
    have hj : sample.2 = j := hhit.2
    have hAij_ne : A i j ≠ 0 := by
      simpa [← hi, ← hj] using hsample
    have hF_nonneg : 0 ≤ frobNormSqRect A := frobNormSqRect_nonneg A
    have hinc :
        elementwiseIncrement s A i j =
          frobNormSqRect A / ((s : ℝ) * A i j) := by
      simpa using elementwiseIncrement_sqMag_eq s A i j hs_ne hAij_ne
    calc
      |elementwiseSampleContribution s A sample i j|
          = |frobNormSqRect A / ((s : ℝ) * A i j)| := by
              simp [elementwiseSampleContribution, hhit, hinc]
      _ = frobNormSqRect A / ((s : ℝ) * |A i j|) := by
              rw [abs_div, abs_mul, abs_of_nonneg (le_of_lt hs),
                abs_of_nonneg hF_nonneg]
      _ =
          (if A i j = 0 then 0
           else frobNormSqRect A / ((s : ℝ) * |A i j|)) := by
              simp [hAij_ne]
      _ ≤ elementwiseLiteralContributionRadius s A :=
          literal_entry_contribution_le_elementwiseLiteralContributionRadius
            hs A i j
  · simp [elementwiseSampleContribution, hhit]
    exact hRadius_nonneg

/-- Frobenius form of
`elementwiseSampleContribution_literal_entry_abs_le`: for a sampled nonzero
entry of the literal matrix, the one-sample contribution has Frobenius norm at
most the finite input-dependent contribution radius. -/
theorem frobNormRect_elementwiseSampleContribution_literal_le
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample : A sample.1 sample.2 ≠ 0) :
    frobNormRect (elementwiseSampleContribution s A sample) ≤
      elementwiseLiteralContributionRadius s A := by
  classical
  have hshape :
      elementwiseSampleContribution s A sample =
        fun r c =>
          if sample.1 = r ∧ sample.2 = c then
            elementwiseIncrement s A sample.1 sample.2
          else
            0 := by
    ext r c
    by_cases hhit : sample.1 = r ∧ sample.2 = c
    · simp [elementwiseSampleContribution, hhit]
    · simp [elementwiseSampleContribution, hhit]
  have hentry :=
    elementwiseSampleContribution_literal_entry_abs_le
      hs A sample hsample sample.1 sample.2
  have hentry' :
      |elementwiseIncrement s A sample.1 sample.2| ≤
        elementwiseLiteralContributionRadius s A := by
    simpa [elementwiseSampleContribution] using hentry
  calc
    frobNormRect (elementwiseSampleContribution s A sample)
        = |elementwiseIncrement s A sample.1 sample.2| := by
            rw [hshape]
            exact frobNormRect_single_left sample.1 sample.2
              (elementwiseIncrement s A sample.1 sample.2)
    _ ≤ elementwiseLiteralContributionRadius s A := hentry'

/-- Frobenius norm of a constant square matrix. -/
theorem frobNormRect_const_square {n : ℕ} (c : ℝ) (hc : 0 ≤ c) :
    frobNormRect (fun _i : Fin n => fun _j : Fin n => c) =
      (n : ℝ) * c := by
  unfold frobNormRect frobNormSqRect
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n, c ^ 2) =
        (n : ℝ) * (n : ℝ) * c ^ 2 := by
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hprod : 0 ≤ (n : ℝ) * c := mul_nonneg hn hc
  have hsquare : (n : ℝ) * (n : ℝ) * c ^ 2 = ((n : ℝ) * c) ^ 2 := by
    ring
  rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hprod]

/-- Square-matrix truncation at `eps / (2n)` costs at most `eps / 2` in
    rectangular Frobenius norm. -/
theorem elementwiseTruncate_square_error_frobNormRect_le_half
    {n : ℕ} (A : Fin n → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 0 < n) :
    frobNormRect
      (fun i j =>
        A i j - elementwiseTruncate (eps / (2 * (n : ℝ))) A i j) ≤
      eps / 2 := by
  let tau : ℝ := eps / (2 * (n : ℝ))
  have hden_nonneg : 0 ≤ 2 * (n : ℝ) := by positivity
  have htau : 0 ≤ tau := div_nonneg heps hden_nonneg
  calc
    frobNormRect
        (fun i j => A i j - elementwiseTruncate tau A i j)
        ≤ frobNormRect (fun _i : Fin n => fun _j : Fin n => tau) := by
          apply frobNormRect_le_of_entry_abs_le
          · intro _ _
            exact htau
          · intro i j
            exact elementwiseTruncate_error_entry_abs_le tau A htau i j
    _ = (n : ℝ) * tau := frobNormRect_const_square tau htau
    _ = eps / 2 := by
          have hn_ne : (n : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hn)
          unfold tau
          field_simp [hn_ne]

/-- Square-matrix truncation at `eps / (2n)` costs at most `eps / 2` in the
    repository's rectangular operator-2 predicate.  This is the deterministic
    first half of the Drineas--Zouzias truncated elementwise-sampling proof. -/
theorem elementwiseTruncate_square_error_rectOpNorm2Le_half
    {n : ℕ} (A : Fin n → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 0 < n) :
    rectOpNorm2Le
      (fun i j =>
        A i j - elementwiseTruncate (eps / (2 * (n : ℝ))) A i j)
      (eps / 2) := by
  apply rectOpNorm2Le_of_frobNormRect_le
  exact elementwiseTruncate_square_error_frobNormRect_le_half A heps hn

/-- Rectangular truncation at `eps / (2*sqrt(mn))` costs at most `eps / 2`
    in rectangular Frobenius norm. -/
theorem elementwiseTruncate_rect_error_frobNormRect_le_half
    {m n : ℕ} (A : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ)) :
    frobNormRect
      (fun i j =>
        A i j -
          elementwiseTruncate
            (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j) ≤
      eps / 2 := by
  let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
  let tau : ℝ := eps / (2 * R)
  have hR_pos : 0 < R := by
    dsimp [R]
    exact Real.sqrt_pos.mpr hmn
  have htau : 0 ≤ tau := by
    dsimp [tau]
    positivity
  have hentry :
      ∀ i j,
        |(fun i j => A i j - elementwiseTruncate tau A i j) i j| ≤ tau := by
    intro i j
    exact elementwiseTruncate_error_entry_abs_le tau A htau i j
  have hnorm :
      frobNormRect
          (fun i j => A i j - elementwiseTruncate tau A i j) ≤
        Real.sqrt ((m : ℝ) * (n : ℝ)) * tau :=
    frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
      (fun i j => A i j - elementwiseTruncate tau A i j) htau hentry
  have hmul : Real.sqrt ((m : ℝ) * (n : ℝ)) * tau = eps / 2 := by
    dsimp [tau, R]
    field_simp [ne_of_gt hR_pos]
  calc
    frobNormRect
        (fun i j =>
          A i j -
            elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j)
        ≤ Real.sqrt ((m : ℝ) * (n : ℝ)) * tau := by
          simpa [tau, R] using hnorm
    _ = eps / 2 := hmul

/-- Rectangular truncation at `eps / (2*sqrt(mn))` costs at most `eps / 2`
    in the repository's rectangular operator-2 predicate. -/
theorem elementwiseTruncate_rect_error_rectOpNorm2Le_half
    {m n : ℕ} (A : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ)) :
    rectOpNorm2Le
      (fun i j =>
        A i j -
          elementwiseTruncate
            (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j)
      (eps / 2) := by
  apply rectOpNorm2Le_of_frobNormRect_le
  exact elementwiseTruncate_rect_error_frobNormRect_le_half A heps hmn

/-- If the sampled residual of the truncated matrix is operator-bounded and
    the deterministic truncation error has Frobenius budget `alpha`, then the
    truncated sketch is operator-bounded against the original matrix. -/
theorem elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
    {m n steps : ℕ} (tau : ℝ) (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    {beta alpha : ℝ}
    (hSample :
      rectOpNorm2Le
        (elementwiseTraceResidual s (elementwiseTruncate tau A) samples)
        beta)
    (hTrunc :
      frobNormRect
        (fun i j => A i j - elementwiseTruncate tau A i j) ≤ alpha) :
    rectOpNorm2Le (elementwiseTruncatedTraceResidual tau s A samples)
      (beta + alpha) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let M : Fin m → Fin n → ℝ := elementwiseTraceResidual s Ahat samples
  let E : Fin m → Fin n → ℝ := fun i j => A i j - Ahat i j
  have hsum : rectOpNorm2Le (fun i j => M i j + E i j) (beta + alpha) :=
    rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le M E hSample hTrunc
  convert hsum using 1
  ext i j
  simp [elementwiseTruncatedTraceResidual, elementwiseTraceResidual, Ahat, M, E]

/-- Square-matrix specialization of the truncated transfer: if the sampled
    residual for the truncated matrix is at most `eps / 2`, then the exact
    truncated sketch is within `eps` of the original matrix. -/
theorem elementwiseTruncatedTraceResidual_square_rectOpNorm2Le_of_half
    {n steps : ℕ} (s : ℕ) (A : Fin n → Fin n → ℝ)
    (samples : ElementwiseTrace n n steps) {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 0 < n)
    (hSample :
      rectOpNorm2Le
        (elementwiseTraceResidual s
          (elementwiseTruncate (eps / (2 * (n : ℝ))) A) samples)
        (eps / 2)) :
    rectOpNorm2Le
      (elementwiseTruncatedTraceResidual (eps / (2 * (n : ℝ))) s A samples)
      eps := by
  have hTruncFrob :
      frobNormRect
        (fun i j =>
          A i j - elementwiseTruncate (eps / (2 * (n : ℝ))) A i j) ≤
        eps / 2 :=
    elementwiseTruncate_square_error_frobNormRect_le_half A heps hn
  have h :=
    elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
      (eps / (2 * (n : ℝ))) s A samples hSample hTruncFrob
  convert h using 1
  ring

/-- One-sample exact residual increment for Algorithm 1.  When the trace has
    exactly `s` samples, the exact residual `A - Atilde` is the sum of these
    increments over the trace. -/
noncomputable def elementwiseSampleResidualIncrement {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n) :
    Fin m → Fin n → ℝ :=
  fun i j => A i j / (s : ℝ) -
    elementwiseSampleContribution s A sample i j

/-- Literal untruncated one-sample residual increments are bounded in
rectangular operator norm by the exact input-dependent support radius. -/
theorem rectOpNorm2Le_elementwiseSampleResidualIncrement_literal_supportRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample : A sample.1 sample.2 ≠ 0) :
    rectOpNorm2Le (elementwiseSampleResidualIncrement s A sample)
      (elementwiseLiteralResidualSupportRadius s A) := by
  classical
  apply rectOpNorm2Le_of_frobNormRect_le
  let C : Fin m → Fin n → ℝ := elementwiseSampleContribution s A sample
  have htri :
      frobNormRect (fun i j => (1 / (s : ℝ)) * A i j + (-1) * C i j) ≤
        frobNormRect (fun i j => (1 / (s : ℝ)) * A i j) +
          frobNormRect (fun i j => (-1) * C i j) :=
    frobNormRect_add_le
      (fun i j => (1 / (s : ℝ)) * A i j)
      (fun i j => (-1) * C i j)
  have hscaleA :
      frobNormRect (fun i j => (1 / (s : ℝ)) * A i j) =
        (1 / (s : ℝ)) * frobNormRect A := by
    rw [frobNormRect_smul]
    simp
  have hscaleC :
      frobNormRect (fun i j => (-1) * C i j) = frobNormRect C := by
    rw [frobNormRect_smul]
    norm_num
  have hcontrib :
      frobNormRect C ≤ elementwiseLiteralContributionRadius s A :=
    frobNormRect_elementwiseSampleContribution_literal_le hs A sample hsample
  have hres_shape :
      elementwiseSampleResidualIncrement s A sample =
        fun i j => (1 / (s : ℝ)) * A i j + (-1) * C i j := by
    ext i j
    simp [elementwiseSampleResidualIncrement, C]
    ring_nf
  calc
    frobNormRect (elementwiseSampleResidualIncrement s A sample)
        = frobNormRect
            (fun i j => (1 / (s : ℝ)) * A i j + (-1) * C i j) := by
            rw [hres_shape]
    _ ≤ frobNormRect (fun i j => (1 / (s : ℝ)) * A i j) +
          frobNormRect (fun i j => (-1) * C i j) := htri
    _ = (1 / (s : ℝ)) * frobNormRect A + frobNormRect C := by
          rw [hscaleA, hscaleC]
    _ ≤ (1 / (s : ℝ)) * frobNormRect A +
          elementwiseLiteralContributionRadius s A := by
          exact add_le_add (le_refl _) hcontrib
    _ = elementwiseLiteralResidualSupportRadius s A := by
          rfl

/-- The literal support radius is nonnegative when the sample count is
positive. -/
theorem elementwiseLiteralResidualSupportRadius_nonneg
    {m n s : ℕ} (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ) :
    0 ≤ elementwiseLiteralResidualSupportRadius s A := by
  unfold elementwiseLiteralResidualSupportRadius
  exact add_nonneg
    (mul_nonneg (by positivity) (frobNormRect_nonneg A))
    (elementwiseLiteralContributionRadius_nonneg hs A)

/-- The literal support radius is strictly positive for a nonzero matrix and a
positive sample count. -/
theorem elementwiseLiteralResidualSupportRadius_pos
    {m n s : ℕ} (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) :
    0 < elementwiseLiteralResidualSupportRadius s A := by
  have hF_sq_pos : 0 < frobNormSqRect A := by
    simpa [sqMagProbDen] using hden
  have hF_pos : 0 < frobNormRect A := by
    unfold frobNormRect
    exact Real.sqrt_pos.mpr hF_sq_pos
  unfold elementwiseLiteralResidualSupportRadius
  exact add_pos_of_pos_of_nonneg
    (mul_pos (by positivity) hF_pos)
    (elementwiseLiteralContributionRadius_nonneg hs A)

/-- Literal self-adjoint dilation increments are bounded above by the explicit
input-dependent support radius. -/
theorem finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_literal_supportRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample : A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample))
      (fun a b =>
        elementwiseLiteralResidualSupportRadius s A * finiteIdMatrix a b) := by
  exact
    finiteLoewnerLe_rectSelfAdjointDilation_of_rectOpNorm2Le
      (elementwiseSampleResidualIncrement s A sample)
      (elementwiseLiteralResidualSupportRadius_nonneg hs A)
      (rectOpNorm2Le_elementwiseSampleResidualIncrement_literal_supportRadius
        hs A sample hsample)

/-- Literal self-adjoint dilation increments are bounded below by the negative
of the same explicit input-dependent support radius. -/
theorem finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_literal_supportRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample : A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b)
      (fun a b =>
        elementwiseLiteralResidualSupportRadius s A * finiteIdMatrix a b) := by
  exact
    finiteLoewnerLe_neg_rectSelfAdjointDilation_of_rectOpNorm2Le
      (elementwiseSampleResidualIncrement s A sample)
      (elementwiseLiteralResidualSupportRadius_nonneg hs A)
      (rectOpNorm2Le_elementwiseSampleResidualIncrement_literal_supportRadius
        hs A sample hsample)












































































































































































































































































































































































/-- A retained hard-thresholded one-sample residual increment has Frobenius
    norm bounded by the input share plus the contribution bound.  This is the
    scalar bounded-increment prerequisite for the matrix-Bernstein route. -/
theorem frobNormRect_elementwiseSampleResidualIncrement_truncated_le
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    frobNormRect
      (elementwiseSampleResidualIncrement s (elementwiseTruncate tau A) sample) ≤
      (1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
        frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let C : Fin m → Fin n → ℝ :=
    elementwiseSampleContribution s Ahat sample
  have htri :
      frobNormRect
        (fun i j => (1 / (s : ℝ)) * Ahat i j + (-1) * C i j) ≤
        frobNormRect (fun i j => (1 / (s : ℝ)) * Ahat i j) +
          frobNormRect (fun i j => (-1) * C i j) :=
    frobNormRect_add_le
      (fun i j => (1 / (s : ℝ)) * Ahat i j)
      (fun i j => (-1) * C i j)
  have hscaleA :
      frobNormRect (fun i j => (1 / (s : ℝ)) * Ahat i j) =
        (1 / (s : ℝ)) * frobNormRect Ahat := by
    rw [frobNormRect_smul]
    have hnonneg : 0 ≤ (1 / (s : ℝ)) := by positivity
    rw [abs_of_nonneg hnonneg]
  have hscaleC :
      frobNormRect (fun i j => (-1) * C i j) = frobNormRect C := by
    rw [frobNormRect_smul]
    norm_num
  have hcontrib :
      frobNormRect C ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) := by
    simpa [Ahat, C] using
      frobNormRect_elementwiseSampleContribution_truncated_le
        htau hs A sample hsample
  have hres_shape :
      elementwiseSampleResidualIncrement s Ahat sample =
        fun i j => (1 / (s : ℝ)) * Ahat i j + (-1) * C i j := by
    ext i j
    simp [elementwiseSampleResidualIncrement, C]
    ring_nf
  calc
    frobNormRect (elementwiseSampleResidualIncrement s Ahat sample)
        = frobNormRect
            (fun i j => (1 / (s : ℝ)) * Ahat i j + (-1) * C i j) := by
            rw [hres_shape]
    _ ≤ frobNormRect (fun i j => (1 / (s : ℝ)) * Ahat i j) +
          frobNormRect (fun i j => (-1) * C i j) := htri
    _ = (1 / (s : ℝ)) * frobNormRect Ahat + frobNormRect C := by
          rw [hscaleA, hscaleC]
    _ ≤ (1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau) := by
          exact add_le_add (le_refl _) hcontrib

/-- Operator-norm predicate version of the retained truncated one-sample
    residual-increment Frobenius bound. -/
theorem rectOpNorm2Le_elementwiseSampleResidualIncrement_truncated
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    rectOpNorm2Le
      (elementwiseSampleResidualIncrement s (elementwiseTruncate tau A) sample)
      ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
        frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)) := by
  apply rectOpNorm2Le_of_frobNormRect_le
  exact frobNormRect_elementwiseSampleResidualIncrement_truncated_le
    htau hs A sample hsample

/-- Event that every one-sample residual increment in a trace of the truncated
    matrix is bounded by `L` in the rectangular operator-2 predicate. -/
def truncatedResidualIncrementsBoundedEvent {m n s : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (L : ℝ) :
    Set (ElementwiseTrace m n s) :=
  {samples |
    ∀ t : Fin s,
      rectOpNorm2Le
        (elementwiseSampleResidualIncrement s
          (elementwiseTruncate tau A) (samples t)) L}














































/-- Self-adjoint-dilation version of the retained truncated one-sample
    residual-increment bound.  The `sqrt 2` factor is the elementary
    Frobenius bound for the dilation. -/
theorem finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteOpNorm2Le
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s (elementwiseTruncate tau A) sample))
      (Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hL_nonneg : 0 ≤ L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hden_pos : 0 < (s : ℝ) * tau := mul_pos hs htau
    have hsecond : 0 ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt hden_pos)
    unfold L
    exact add_nonneg hfirst hsecond
  have hF :
      frobNormRect (elementwiseSampleResidualIncrement s Ahat sample) ≤ L := by
    simpa [Ahat, L] using
      frobNormRect_elementwiseSampleResidualIncrement_truncated_le
        htau hs A sample hsample
  simpa [Ahat, L] using
    finiteOpNorm2Le_rectSelfAdjointDilation_of_frobNormRect_le
      (elementwiseSampleResidualIncrement s Ahat sample) hL_nonneg hF

/-- Quadratic-form version of the retained truncated one-sample
    self-adjoint-dilation increment bound.

This is the scalar form consumed by support-aware finite-family MGF bounds.
The retained-entry hypothesis is later discharged from positive sampling
probability. -/
theorem finiteQuadraticForm_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_le
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0)
    (z : Fin m ⊕ Fin n → ℝ) :
    finiteQuadraticForm
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s (elementwiseTruncate tau A) sample)) z ≤
      (Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) *
        finiteVecNorm2Sq z := by
  exact
    finiteQuadraticForm_le_of_finiteOpNorm2Le
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s (elementwiseTruncate tau A) sample))
      (finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample) z

/-- One-sided Loewner upper bound for each retained truncated self-adjoint
    dilation increment.  This is the `X_t <= L I` side condition used by
    largest-eigenvalue matrix Bernstein routes. -/
theorem finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s
          (elementwiseTruncate tau A) sample))
      (fun a b =>
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) *
          finiteIdMatrix a b) := by
  exact
    finiteLoewnerLe_smul_id_of_finiteOpNorm2Le
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s
          (elementwiseTruncate tau A) sample))
      (finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample)

/-- Lower Loewner side for each retained truncated self-adjoint dilation
    increment, written as `-X_t <= L I`. -/
theorem finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) sample) a b)
      (fun a b =>
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) *
          finiteIdMatrix a b) := by
  exact
    finiteLoewnerLe_neg_smul_id_of_finiteOpNorm2Le
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s
          (elementwiseTruncate tau A) sample))
      (finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample)

/-- Sharper one-sided Loewner upper bound for each retained truncated
    self-adjoint dilation increment.

Unlike `finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated`,
this uses the rectangular operator bound directly and therefore avoids the
auxiliary `sqrt 2` Frobenius-to-dilation loss.  This is the source-aligned
bounded-increment radius needed for the Drineas--Zouzias matrix Bernstein
constants. -/
theorem finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_sharp
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s
          (elementwiseTruncate tau A) sample))
      (fun a b =>
        (((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) *
          finiteIdMatrix a b) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hL_nonneg : 0 ≤ L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hden_pos : 0 < (s : ℝ) * tau := mul_pos hs htau
    have hsecond : 0 ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt hden_pos)
    unfold L
    exact add_nonneg hfirst hsecond
  have hrect :
      rectOpNorm2Le
        (elementwiseSampleResidualIncrement s Ahat sample) L := by
    simpa [Ahat, L] using
      rectOpNorm2Le_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample
  simpa [Ahat, L] using
    finiteLoewnerLe_rectSelfAdjointDilation_of_rectOpNorm2Le
      (elementwiseSampleResidualIncrement s Ahat sample) hL_nonneg hrect

/-- Sharper lower-tail companion for retained truncated dilation increments,
    also avoiding the `sqrt 2` Frobenius-to-dilation loss. -/
theorem finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_sharp
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) sample) a b)
      (fun a b =>
        (((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) *
          finiteIdMatrix a b) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hL_nonneg : 0 ≤ L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hden_pos : 0 < (s : ℝ) * tau := mul_pos hs htau
    have hsecond : 0 ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt hden_pos)
    unfold L
    exact add_nonneg hfirst hsecond
  have hrect :
      rectOpNorm2Le
        (elementwiseSampleResidualIncrement s Ahat sample) L := by
    simpa [Ahat, L] using
      rectOpNorm2Le_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample
  simpa [Ahat, L] using
    finiteLoewnerLe_neg_rectSelfAdjointDilation_of_rectOpNorm2Le
      (elementwiseSampleResidualIncrement s Ahat sample) hL_nonneg hrect

/-- Event that every self-adjoint dilation of a truncated residual increment is
    bounded by `L` in the finite square operator predicate. -/
def truncatedDilationIncrementsBoundedEvent {m n s : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (L : ℝ) :
    Set (ElementwiseTrace m n s) :=
  {samples |
    ∀ t : Fin s,
      finiteOpNorm2Le
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) (samples t))) L}

/-- Event that every retained truncated self-adjoint dilation increment is
    bounded above and below in Loewner order by `L I`. -/
def truncatedDilationIncrementLoewnerBoundedEvent {m n s : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (L : ℝ) :
    Set (ElementwiseTrace m n s) :=
  {samples |
    ∀ t : Fin s,
      finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) (samples t)))
        (fun a b => L * finiteIdMatrix a b) ∧
      finiteLoewnerLe
        (fun a b =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) (samples t)) a b)
        (fun a b => L * finiteIdMatrix a b)}




































































































/-- Squared-Loewner form of the retained truncated self-adjoint dilation
    increment bound.  This is the deterministic bounded-square hypothesis used
    by Bernstein-style matrix concentration. -/
theorem finiteLoewnerLe_rectSelfAdjointDilation_square_elementwiseSampleResidualIncrement_truncated
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (finiteMatMul
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) sample))
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) sample)))
      (fun a b =>
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) ^ 2 *
          finiteIdMatrix a b) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hinner_nonneg :
      0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau) := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hden_pos : 0 < (s : ℝ) * tau := mul_pos hs htau
    have hsecond : 0 ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt hden_pos)
    exact add_nonneg hfirst hsecond
  have hL_nonneg : 0 ≤ L := by
    unfold L
    exact mul_nonneg (Real.sqrt_nonneg 2) hinner_nonneg
  have hD :
      finiteOpNorm2Le
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample)) L := by
    simpa [Ahat, L] using
      finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample
  simpa [Ahat, L] using
    rectSelfAdjointDilation_square_loewnerLe_scalar_id_of_finiteOpNorm2Le
      (elementwiseSampleResidualIncrement s Ahat sample) hD hL_nonneg

/-- Event that every squared self-adjoint dilation increment is bounded in
    Loewner order by `L^2 I`. -/
def truncatedDilationIncrementSquaresBoundedEvent {m n s : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (L : ℝ) :
    Set (ElementwiseTrace m n s) :=
  {samples |
    ∀ t : Fin s,
      finiteLoewnerLe
        (finiteMatMul
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) (samples t)))
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) (samples t))))
        (fun a b => L ^ 2 * finiteIdMatrix a b)}















































/-- Simultaneous bounded-operator and bounded-square event for the
    self-adjoint dilation increments in the truncated Algorithm 1 route.  The
    two-sided Loewner component is included because Tropp-style Bernstein
    hypotheses are usually stated as `-L I <= X_t <= L I` or `lambda_max X_t
    <= L`, while the squared component is useful for variance proxies. -/
def truncatedDilationBernsteinBoundedEvent {m n s : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (L : ℝ) :
    Set (ElementwiseTrace m n s) :=
  (truncatedDilationIncrementsBoundedEvent tau A L ∩
    truncatedDilationIncrementLoewnerBoundedEvent tau A L) ∩
    truncatedDilationIncrementSquaresBoundedEvent tau A L


















































/-- The exact residual of an `s`-step Algorithm 1 trace is a sum of one-sample
    residual increments.  This is the algebraic shape needed by matrix
    concentration arguments. -/
theorem elementwiseTraceResidual_eq_sum_sampleResidualIncrement
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n s) (hs : (s : ℝ) ≠ 0)
    (i : Fin m) (j : Fin n) :
    elementwiseTraceResidual s A samples i j =
      ∑ t : Fin s, elementwiseSampleResidualIncrement s A (samples t) i j := by
  classical
  have hconst :
      (∑ _t : Fin s, A i j / (s : ℝ)) = A i j := by
    calc
      (∑ _t : Fin s, A i j / (s : ℝ))
          = (s : ℝ) * (A i j / (s : ℝ)) := by
              simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
      _ = A i j := by
              field_simp [hs]
  have hcontrib :
      (∑ t : Fin s, elementwiseSampleContribution s A (samples t) i j) =
        ∑ t : Fin s, elementwiseTraceContribution s A samples t i j := by
    apply Finset.sum_congr rfl
    intro t _
    rw [elementwiseTraceContribution_eq_sampleContribution]
  calc
    elementwiseTraceResidual s A samples i j
        = A i j -
            ∑ t : Fin s, elementwiseTraceContribution s A samples t i j := by
            simp [elementwiseTraceResidual, elementwiseTraceSketch]
    _ = (∑ t : Fin s, A i j / (s : ℝ)) -
            ∑ t : Fin s, elementwiseSampleContribution s A (samples t) i j := by
            rw [hconst, hcontrib]
    _ = ∑ t : Fin s, elementwiseSampleResidualIncrement s A (samples t) i j := by
            rw [← Finset.sum_sub_distrib]
            rfl

/-- One-step expectation of the exact Algorithm 1 contribution at a fixed
    entry under squared-magnitude probabilities. -/
theorem sqMagProb_sum_elementwiseSampleContribution_entry
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (i : Fin m) (j : Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleContribution s A sample i j) =
      A i j / (s : ℝ) := by
  classical
  by_cases hAij_zero : A i j = 0
  · have hcontrib : ∀ sample : ElementwiseSample m n,
        elementwiseSampleContribution s A sample i j = 0 := by
      intro sample
      simp [elementwiseSampleContribution, elementwiseIncrement,
        elementwiseIncrementWithProb, hAij_zero]
    simp [hcontrib, hAij_zero]
  · have hp_ne : sqMagProb A i j ≠ 0 :=
      sqMagProb_ne_zero_of_entry_ne_zero A i j hAij_zero
    rw [Finset.sum_eq_single (i, j)]
    · simp [elementwiseSampleContribution]
      unfold elementwiseIncrement elementwiseIncrementWithProb
      field_simp [hs, hp_ne]
    · intro sample _ hsample
      have hnot : ¬ (sample.1 = i ∧ sample.2 = j) := by
        intro h
        apply hsample
        ext <;> simp [h.1, h.2]
      simp [elementwiseSampleContribution, hnot]
    · intro hnot
      simp at hnot





































/-- The one-step contribution at a fixed entry has squared expectation at
    most `||A||_F^2 / s^2` under the squared-magnitude one-step law. -/
theorem sqMagProb_sum_elementwiseSampleContribution_entry_sq_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (i : Fin m) (j : Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleContribution s A sample i j ^ 2) ≤
      frobNormSqRect A / (s : ℝ) ^ 2 := by
  classical
  by_cases hAij_zero : A i j = 0
  · have hcontrib : ∀ sample : ElementwiseSample m n,
        elementwiseSampleContribution s A sample i j = 0 := by
      intro sample
      simp [elementwiseSampleContribution, elementwiseIncrement,
        elementwiseIncrementWithProb, hAij_zero]
    have hden_nonneg : 0 ≤ (s : ℝ) ^ 2 := sq_nonneg (s : ℝ)
    simp [hcontrib]
    exact div_nonneg (frobNormSqRect_nonneg A) hden_nonneg
  · have hp_ne : sqMagProb A i j ≠ 0 :=
      sqMagProb_ne_zero_of_entry_ne_zero A i j hAij_zero
    have hF_ne : frobNormSqRect A ≠ 0 :=
      frobNormSqRect_ne_zero_of_entry_ne_zero A i j hAij_zero
    have hsingle :
        sqMagProb A i j *
          elementwiseSampleContribution s A (i, j) i j ^ 2 =
          frobNormSqRect A / (s : ℝ) ^ 2 := by
      simp [elementwiseSampleContribution]
      unfold elementwiseIncrement elementwiseIncrementWithProb sqMagProb
        sqMagProbDen
      field_simp [hs, hAij_zero, hF_ne]
    calc
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          elementwiseSampleContribution s A sample i j ^ 2)
          = sqMagProb A i j *
              elementwiseSampleContribution s A (i, j) i j ^ 2 := by
            rw [Finset.sum_eq_single (i, j)]
            · intro sample _ hsample
              have hnot : ¬ (sample.1 = i ∧ sample.2 = j) := by
                intro h
                apply hsample
                ext <;> simp [h.1, h.2]
              simp [elementwiseSampleContribution, hnot]
            · intro hnot
              simp at hnot
      _ = frobNormSqRect A / (s : ℝ) ^ 2 := hsingle
      _ ≤ frobNormSqRect A / (s : ℝ) ^ 2 := le_rfl

/-- Applying a one-sample contribution matrix to a vector leaves only the
    sampled row active. -/
theorem vecNorm2Sq_rectMatMulVec_elementwiseSampleContribution_eq
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (sample : ElementwiseSample m n) (x : Fin n → ℝ) :
    vecNorm2Sq
      (rectMatMulVec (elementwiseSampleContribution s A sample) x) =
      (elementwiseIncrement s A sample.1 sample.2 * x sample.2) ^ 2 := by
  classical
  unfold vecNorm2Sq rectMatMulVec
  rw [Finset.sum_eq_single sample.1]
  · have hinner :
        (∑ j : Fin n,
          elementwiseSampleContribution s A sample sample.1 j * x j) =
          elementwiseIncrement s A sample.1 sample.2 * x sample.2 := by
      rw [Finset.sum_eq_single sample.2]
      · simp [elementwiseSampleContribution]
      · intro j _ hj
        have hneq : sample.2 ≠ j := by
          intro h
          exact hj h.symm
        simp [elementwiseSampleContribution, hneq]
      · intro hnot
        simp at hnot
    change
      (∑ j : Fin n,
        elementwiseSampleContribution s A sample sample.1 j * x j) ^ 2 =
        (elementwiseIncrement s A sample.1 sample.2 * x sample.2) ^ 2
    rw [hinner]
  · intro i _ hi
    have hinner :
        (∑ j : Fin n,
          elementwiseSampleContribution s A sample i j * x j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hneq : sample.1 ≠ i := by
        intro h
        exact hi h.symm
      simp [elementwiseSampleContribution, hneq]
    rw [hinner]
    ring
  · intro hnot
    simp at hnot

/-- Under squared-magnitude sampling, the weighted square of one contribution
    scalar cancels the sampling probability. -/
theorem sqMagProb_mul_elementwiseIncrement_sq_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (i : Fin m) (j : Fin n) (x : ℝ) :
    sqMagProb A i j * (elementwiseIncrement s A i j * x) ^ 2 ≤
      (frobNormSqRect A / (s : ℝ) ^ 2) * x ^ 2 := by
  classical
  by_cases hAij_zero : A i j = 0
  · have hrhs_nonneg :
        0 ≤ (frobNormSqRect A / (s : ℝ) ^ 2) * x ^ 2 := by
      exact mul_nonneg
        (div_nonneg (frobNormSqRect_nonneg A) (sq_nonneg (s : ℝ)))
        (sq_nonneg x)
    simp [sqMagProb, elementwiseIncrement, elementwiseIncrementWithProb,
      hAij_zero, hrhs_nonneg]
  · have hp_ne : sqMagProb A i j ≠ 0 :=
      sqMagProb_ne_zero_of_entry_ne_zero A i j hAij_zero
    have hF_ne : frobNormSqRect A ≠ 0 :=
      frobNormSqRect_ne_zero_of_entry_ne_zero A i j hAij_zero
    have heq :
        sqMagProb A i j * (elementwiseIncrement s A i j * x) ^ 2 =
          (frobNormSqRect A / (s : ℝ) ^ 2) * x ^ 2 := by
      let p : ℝ := sqMagProb A i j
      have hp_ne' : p ≠ 0 := by
        simpa [p] using hp_ne
      calc
        sqMagProb A i j * (elementwiseIncrement s A i j * x) ^ 2
            = p * ((A i j / ((s : ℝ) * p) * x) ^ 2) := by
                simp [p, elementwiseIncrement, elementwiseIncrementWithProb]
        _ = (A i j ^ 2 / ((s : ℝ) ^ 2 * p)) * x ^ 2 := by
                field_simp [hs, hp_ne']
        _ = (frobNormSqRect A / (s : ℝ) ^ 2) * x ^ 2 := by
                unfold p sqMagProb sqMagProbDen
                field_simp [hs, hAij_zero, hF_ne]
    rw [heq]

/-- Source-aligned one-step vector-action second-moment bound for the sampled
    contribution itself.  The dimension factor is the number of rows because a
    contribution has only one active row. -/
theorem sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleContribution_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (x : Fin n → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleContribution s A sample) x)) ≤
      ((m : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        vecNorm2Sq x := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleContribution s A sample) x))
        = ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              (elementwiseIncrement s A sample.1 sample.2 * x sample.2) ^ 2 := by
            apply Finset.sum_congr rfl
            intro sample _
            rw [vecNorm2Sq_rectMatMulVec_elementwiseSampleContribution_eq]
    _ ≤ ∑ sample : ElementwiseSample m n,
          (frobNormSqRect A / (s : ℝ) ^ 2) * x sample.2 ^ 2 := by
          apply Finset.sum_le_sum
          intro sample _
          exact sqMagProb_mul_elementwiseIncrement_sq_le
            s A hs sample.1 sample.2 (x sample.2)
    _ = ((m : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          vecNorm2Sq x := by
          change
            (∑ sample : Fin m × Fin n,
              (frobNormSqRect A / (s : ℝ) ^ 2) * x sample.2 ^ 2) =
            ((m : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
              vecNorm2Sq x
          rw [Fintype.sum_prod_type]
          unfold vecNorm2Sq
          simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.mul_sum]
          ring

/-- One-step vector-action mean identity for the sampled contribution. -/
theorem sqMagProb_sum_rectMatMulVec_elementwiseSampleContribution_eq
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (x : Fin n → ℝ) (i : Fin m) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        rectMatMulVec (elementwiseSampleContribution s A sample) x i) =
      (1 / (s : ℝ)) * rectMatMulVec A x i := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        rectMatMulVec (elementwiseSampleContribution s A sample) x i)
        = ∑ j : Fin n,
            (∑ sample : ElementwiseSample m n,
              sqMagProb A sample.1 sample.2 *
                elementwiseSampleContribution s A sample i j) * x j := by
            unfold rectMatMulVec
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro sample _
            ring
    _ = ∑ j : Fin n, (A i j / (s : ℝ)) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [sqMagProb_sum_elementwiseSampleContribution_entry
              s A hs i j]
    _ = (1 / (s : ℝ)) * rectMatMulVec A x i := by
            unfold rectMatMulVec
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring



























































































































































/-- Applying the transpose-action of a one-sample contribution matrix to a
    vector leaves only the sampled column active. -/
theorem vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleContribution_eq
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (sample : ElementwiseSample m n) (y : Fin m → ℝ) :
    vecNorm2Sq
      (fun j : Fin n =>
        ∑ i : Fin m, elementwiseSampleContribution s A sample i j * y i) =
      (elementwiseIncrement s A sample.1 sample.2 * y sample.1) ^ 2 := by
  classical
  unfold vecNorm2Sq
  rw [Finset.sum_eq_single sample.2]
  · have hinner :
        (∑ i : Fin m,
          elementwiseSampleContribution s A sample i sample.2 * y i) =
          elementwiseIncrement s A sample.1 sample.2 * y sample.1 := by
      rw [Finset.sum_eq_single sample.1]
      · simp [elementwiseSampleContribution]
      · intro i _ hi
        have hneq : sample.1 ≠ i := by
          intro h
          exact hi h.symm
        simp [elementwiseSampleContribution, hneq]
      · intro hnot
        simp at hnot
    change
      (∑ i : Fin m,
        elementwiseSampleContribution s A sample i sample.2 * y i) ^ 2 =
        (elementwiseIncrement s A sample.1 sample.2 * y sample.1) ^ 2
    rw [hinner]
  · intro j _ hj
    have hinner :
        (∑ i : Fin m,
          elementwiseSampleContribution s A sample i j * y i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hneq : sample.2 ≠ j := by
        intro h
        exact hj h.symm
      simp [elementwiseSampleContribution, hneq]
    change
      (∑ i : Fin m,
        elementwiseSampleContribution s A sample i j * y i) ^ 2 = 0
    rw [hinner]
    ring
  · intro hnot
    simp at hnot

/-- Source-aligned one-step transpose-vector second-moment bound for sampled
    contributions.  The dimension factor is the number of columns. -/
theorem sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleContribution_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (y : Fin m → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin m,
              elementwiseSampleContribution s A sample i j * y i)) ≤
      ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        vecNorm2Sq y := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin m,
              elementwiseSampleContribution s A sample i j * y i))
        = ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              (elementwiseIncrement s A sample.1 sample.2 * y sample.1) ^ 2 := by
            apply Finset.sum_congr rfl
            intro sample _
            rw [vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleContribution_eq]
    _ ≤ ∑ sample : ElementwiseSample m n,
          (frobNormSqRect A / (s : ℝ) ^ 2) * y sample.1 ^ 2 := by
          apply Finset.sum_le_sum
          intro sample _
          exact sqMagProb_mul_elementwiseIncrement_sq_le
            s A hs sample.1 sample.2 (y sample.1)
    _ = ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          vecNorm2Sq y := by
          change
            (∑ sample : Fin m × Fin n,
              (frobNormSqRect A / (s : ℝ) ^ 2) * y sample.1 ^ 2) =
            ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
              vecNorm2Sq y
          rw [Fintype.sum_prod_type]
          unfold vecNorm2Sq
          simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
          calc
            (∑ x : Fin m,
              (n : ℝ) * ((frobNormSqRect A / (s : ℝ) ^ 2) * y x ^ 2))
                = ∑ x : Fin m,
                    ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
                      y x ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro x _
                    ring
            _ = ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
                  ∑ i : Fin m, y i ^ 2 := by
                    rw [Finset.mul_sum]

/-- One-step transpose-vector mean identity for the sampled contribution. -/
theorem sqMagProb_sum_transposeRectMatMulVec_elementwiseSampleContribution_eq
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (y : Fin m → ℝ) (j : Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        (∑ i : Fin m,
          elementwiseSampleContribution s A sample i j * y i)) =
      (1 / (s : ℝ)) * ∑ i : Fin m, A i j * y i := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        (∑ i : Fin m,
          elementwiseSampleContribution s A sample i j * y i))
        = ∑ i : Fin m,
            (∑ sample : ElementwiseSample m n,
              sqMagProb A sample.1 sample.2 *
                elementwiseSampleContribution s A sample i j) * y i := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro sample _
            ring
    _ = ∑ i : Fin m, (A i j / (s : ℝ)) * y i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [sqMagProb_sum_elementwiseSampleContribution_entry
              s A hs i j]
    _ = (1 / (s : ℝ)) * ∑ i : Fin m, A i j * y i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring

































































































































































































































































































































































































































































































































































































































































































































































/-- The one-step self-adjoint dilation variance matrix is positive
    semidefinite. -/
theorem sqMagProb_sum_rectSelfAdjointDilation_square_psd
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) :
    finitePSD
      (fun a b =>
        ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b) := by
  classical
  apply finitePSD_fintype_sum_smul_of_nonneg
  · intro sample
    exact sqMagProb_nonneg A hden sample.1 sample.2
  · intro sample
    exact finitePSD_rectSelfAdjointDilation_square
      (elementwiseSampleResidualIncrement s A sample)









































































































































































































/-- The summed self-adjoint dilation variance matrix is positive
    semidefinite. -/
theorem sqMagProb_sum_steps_rectSelfAdjointDilation_square_psd
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) :
    finitePSD
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) := by
  classical
  apply finitePSD_fintype_sum_of_finitePSD
  intro _t
  exact sqMagProb_sum_rectSelfAdjointDilation_square_psd s A hden







































































































































































































































































































































































































































































































































/-- Applying the exact residual to a fixed vector preserves the sum of
    one-sample residual increments. -/
theorem rectMatMulVec_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n s) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) (i : Fin m) :
    rectMatMulVec (elementwiseTraceResidual s A samples) x i =
      ∑ t : Fin s,
        rectMatMulVec (elementwiseSampleResidualIncrement s A (samples t)) x i := by
  classical
  have hentry :
      elementwiseTraceResidual s A samples =
        fun i j =>
          ∑ t : Fin s,
            elementwiseSampleResidualIncrement s A (samples t) i j := by
    ext i j
    exact elementwiseTraceResidual_eq_sum_sampleResidualIncrement
      A samples hs i j
  rw [hentry]
  unfold rectMatMulVec
  calc
    (∑ j : Fin n,
      (∑ t : Fin s,
        elementwiseSampleResidualIncrement s A (samples t) i j) * x j)
        = ∑ j : Fin n, ∑ t : Fin s,
            elementwiseSampleResidualIncrement s A (samples t) i j * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ = ∑ t : Fin s, ∑ j : Fin n,
            elementwiseSampleResidualIncrement s A (samples t) i j * x j := by
            rw [Finset.sum_comm]

/-- The self-adjoint dilation of the exact residual is the sum of the
    self-adjoint dilations of the one-sample residual increments.  This is the
    square-matrix random object needed by a future Bernstein/Khintchine proof. -/
theorem rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n s) (hs : (s : ℝ) ≠ 0)
    (a b : Fin m ⊕ Fin n) :
    rectSelfAdjointDilation (elementwiseTraceResidual s A samples) a b =
      ∑ t : Fin s,
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A (samples t)) a b := by
  cases a with
  | inl i =>
      cases b with
      | inl k =>
          simp [rectSelfAdjointDilation]
      | inr j =>
          simpa [rectSelfAdjointDilation] using
            elementwiseTraceResidual_eq_sum_sampleResidualIncrement
              A samples hs i j
  | inr j =>
      cases b with
      | inl i =>
          simpa [rectSelfAdjointDilation] using
            elementwiseTraceResidual_eq_sum_sampleResidualIncrement
              A samples hs i j
      | inr k =>
          simp [rectSelfAdjointDilation]

/-- Quadratic forms of the residual dilation decompose as sums of the
    corresponding one-step quadratic forms.

This is the scalar-projection bridge between the exact residual decomposition
and finite-family MGF or finite-cover concentration arguments. -/
theorem finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n s) (hs : (s : ℝ) ≠ 0)
    (x : Fin m ⊕ Fin n → ℝ) :
    finiteQuadraticForm
        (rectSelfAdjointDilation (elementwiseTraceResidual s A samples)) x =
      ∑ t : Fin s,
        finiteQuadraticForm
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A (samples t))) x := by
  classical
  have hmat :
      rectSelfAdjointDilation (elementwiseTraceResidual s A samples) =
        fun a b =>
          ∑ t : Fin s,
            rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t)) a b := by
    ext a b
    exact rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
      A samples hs a b
  calc
    finiteQuadraticForm
        (rectSelfAdjointDilation (elementwiseTraceResidual s A samples)) x
        = finiteQuadraticForm
            (fun a b =>
              ∑ t : Fin s,
                rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)) a b) x := by
            rw [hmat]
    _ = ∑ t : Fin s,
          finiteQuadraticForm
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t))) x := by
            rw [finiteQuadraticForm_fintype_sum]

/-- The one-step self-adjoint dilation residual increment, scaled by a scalar
    parameter, is symmetric.  This is the domain side condition for feeding the
    Algorithm 1 dilation increments into the finite-real trace-MGF theorem. -/
theorem rectSelfAdjointDilation_elementwiseSampleResidualIncrement_smul_symmetric
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (sample : ElementwiseSample m n) (theta : ℝ) :
    IsSymmetricFiniteMatrix
      (fun a b : Fin m ⊕ Fin n =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) := by
  intro a b
  exact congrArg (fun x => theta * x)
    (rectSelfAdjointDilation_symmetric
      (elementwiseSampleResidualIncrement s A sample) a b)

















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































namespace FiniteProbability

/-- Jensen/duality bound for the Euclidean norm of a finite-probability vector
mean.

This avoids adding a matrix-algebra dependency to `FiniteProbability.lean`
itself, but gives the Khintchine route the standard finite-dimensional
ingredient `||E Y||_2 <= E ||Y||_2`. -/
theorem expectationReal_vecNorm2_mean_le_expectationReal_vecNorm2
    {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) {n : ℕ}
    (Y : Ω → Fin n → ℝ) :
    vecNorm2 (fun i : Fin n => P.expectationReal (fun ω => Y ω i)) ≤
      P.expectationReal (fun ω => vecNorm2 (Y ω)) := by
  classical
  let z : Fin n → ℝ := fun i => P.expectationReal (fun ω => Y ω i)
  by_cases hz : vecNorm2 z = 0
  · have hright_nonneg :
        0 ≤ P.expectationReal (fun ω => vecNorm2 (Y ω)) := by
      unfold FiniteProbability.expectationReal
      exact Finset.sum_nonneg fun ω _ =>
        mul_nonneg (P.prob_nonneg ω) (vecNorm2_nonneg (Y ω))
    have hleft : vecNorm2 (fun i : Fin n => P.expectationReal (fun ω => Y ω i)) = 0 := by
      simpa [z] using hz
    rw [hleft]
    exact hright_nonneg
  · have hzpos : 0 < vecNorm2 z :=
      lt_of_le_of_ne (vecNorm2_nonneg z) (Ne.symm hz)
    let u : Fin n → ℝ := fun i => (vecNorm2 z)⁻¹ * z i
    have hinner_z :
        (∑ i : Fin n, u i * z i) = vecNorm2 z := by
      simpa [u] using vecInnerProduct_inv_smul_self_eq_norm z hzpos
    have hu_norm : vecNorm2 u = 1 := by
      simpa [u] using vecNorm2_inv_smul_self_of_pos z hzpos
    have hmean_inner :
        vecNorm2 z =
          P.expectationReal (fun ω => ∑ i : Fin n, u i * Y ω i) := by
      calc
        vecNorm2 z = ∑ i : Fin n, u i * z i := hinner_z.symm
        _ = ∑ i : Fin n, P.expectationReal (fun ω => u i * Y ω i) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [FiniteProbability.expectationReal_const_mul]
        _ = P.expectationReal (fun ω => ∑ i : Fin n, u i * Y ω i) := by
              rw [FiniteProbability.expectationReal_sum]
    have hinner_abs :
        P.expectationReal (fun ω => ∑ i : Fin n, u i * Y ω i) ≤
          P.expectationReal (fun ω => |∑ i : Fin n, u i * Y ω i|) :=
      FiniteProbability.expectationReal_mono P fun ω => le_abs_self _
    have habs_norm :
        P.expectationReal (fun ω => |∑ i : Fin n, u i * Y ω i|) ≤
          P.expectationReal (fun ω => vecNorm2 (Y ω)) := by
      apply FiniteProbability.expectationReal_mono
      intro ω
      have hcs := abs_vecInnerProduct_le_vecNorm2_mul u (Y ω)
      simpa [hu_norm] using hcs
    have hmain :
        vecNorm2 z ≤ P.expectationReal (fun ω => vecNorm2 (Y ω)) :=
      hmean_inner.trans_le (hinner_abs.trans habs_norm)
    simpa [z] using hmain

/-- Finite vector-valued symmetrization around the mean. -/
theorem expectationReal_vecNorm2_sub_mean_le_prod_expectationReal_vecNorm2_sub
    {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) {n : ℕ}
    (X : Ω → Fin n → ℝ) :
    P.expectationReal
        (fun ω => vecNorm2
          (fun i : Fin n => X ω i - P.expectationReal (fun η => X η i))) ≤
      (P.prod P).expectationReal
        (fun x : Ω × Ω => vecNorm2 (fun i : Fin n => X x.1 i - X x.2 i)) := by
  classical
  have hpoint :
      ∀ ω,
        vecNorm2
            (fun i : Fin n => X ω i - P.expectationReal (fun η => X η i)) ≤
          P.expectationReal
            (fun η => vecNorm2 (fun i : Fin n => X ω i - X η i)) := by
    intro ω
    have h :=
      expectationReal_vecNorm2_mean_le_expectationReal_vecNorm2 P
        (fun η : Ω => fun i : Fin n => X ω i - X η i)
    have hmean :
        (fun i : Fin n =>
            P.expectationReal (fun η : Ω => X ω i - X η i)) =
          fun i : Fin n => X ω i - P.expectationReal (fun η : Ω => X η i) := by
      ext i
      calc
        P.expectationReal (fun η : Ω => X ω i - X η i)
            = P.expectationReal (fun _η : Ω => X ω i) -
                P.expectationReal (fun η : Ω => X η i) := by
                simpa using
                  (FiniteProbability.expectationReal_sub P
                    (fun _η : Ω => X ω i) (fun η : Ω => X η i))
        _ = X ω i - P.expectationReal (fun η : Ω => X η i) := by
                rw [FiniteProbability.expectationReal_const]
    simpa [hmean] using h
  calc
    P.expectationReal
        (fun ω => vecNorm2
          (fun i : Fin n => X ω i - P.expectationReal (fun η => X η i)))
        ≤ P.expectationReal
            (fun ω =>
              P.expectationReal
                (fun η => vecNorm2 (fun i : Fin n => X ω i - X η i))) :=
          FiniteProbability.expectationReal_mono P hpoint
    _ = (P.prod P).expectationReal
        (fun x : Ω × Ω => vecNorm2 (fun i : Fin n => X x.1 i - X x.2 i)) := by
          rw [FiniteProbability.prod_expectationReal_eq]

/-- Centered finite vector-valued symmetrization. -/
theorem expectationReal_vecNorm2_le_prod_expectationReal_vecNorm2_sub_of_expectation_eq_zero
    {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) {n : ℕ}
    (X : Ω → Fin n → ℝ)
    (hmean : ∀ i : Fin n, P.expectationReal (fun ω => X ω i) = 0) :
    P.expectationReal (fun ω => vecNorm2 (X ω)) ≤
      (P.prod P).expectationReal
        (fun x : Ω × Ω => vecNorm2 (fun i : Fin n => X x.1 i - X x.2 i)) := by
  simpa [hmean] using
    expectationReal_vecNorm2_sub_mean_le_prod_expectationReal_vecNorm2_sub P X

end FiniteProbability










































































namespace FiniteProbability

/-- Operator-predicate independent-copy symmetrization for rectangular
matrix-valued random variables.

For a fixed outcome `ω`, if every independent-copy difference `X ω - X η` is
bounded by `L` in the rectangular operator predicate, and if the matrix entries
of `X` are centered under `P`, then `X ω` itself is bounded by `L`.

This is a deterministic Jensen/convexity adapter.  It does not prove a tail
bound for the copy-difference event; that is the future Khintchine/matrix-tail
step. -/
theorem rectOpNorm2Le_of_entrywise_mean_zero_of_copy_diff_rectOpNorm2Le
    {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) {m n : ℕ}
    (X : Ω → Fin m → Fin n → ℝ)
    (hmean : ∀ i j, P.expectationReal (fun η => X η i j) = 0)
    (ω : Ω) {L : ℝ}
    (hdiff : ∀ η : Ω,
      rectOpNorm2Le (fun i j => X ω i j - X η i j) L) :
    rectOpNorm2Le (X ω) L := by
  classical
  intro x
  let Y : Ω → Fin m → ℝ :=
    fun η => rectMatMulVec (fun i j => X ω i j - X η i j) x
  have hmean_vec :
      (fun i : Fin m => P.expectationReal (fun η => Y η i)) =
        rectMatMulVec (X ω) x := by
    ext i
    calc
      P.expectationReal (fun η : Ω => Y η i)
          =
            P.expectationReal
              (fun η : Ω =>
                ∑ j : Fin n, (X ω i j - X η i j) * x j) := by
              rfl
      _ = ∑ j : Fin n,
            P.expectationReal
              (fun η : Ω => (X ω i j - X η i j) * x j) := by
              rw [FiniteProbability.expectationReal_sum]
      _ = ∑ j : Fin n,
            (X ω i j - P.expectationReal (fun η : Ω => X η i j)) * x j := by
              apply Finset.sum_congr rfl
              intro j _
              calc
                P.expectationReal
                    (fun η : Ω => (X ω i j - X η i j) * x j)
                    =
                  P.expectationReal
                    (fun η : Ω => X ω i j - X η i j) * x j := by
                    rw [FiniteProbability.expectationReal_mul_const]
                _ =
                  (P.expectationReal (fun _η : Ω => X ω i j) -
                    P.expectationReal (fun η : Ω => X η i j)) * x j := by
                    rw [FiniteProbability.expectationReal_sub]
                _ =
                  (X ω i j - P.expectationReal (fun η : Ω => X η i j)) *
                    x j := by
                    rw [FiniteProbability.expectationReal_const]
      _ = ∑ j : Fin n, X ω i j * x j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hmean i j]
              ring
      _ = rectMatMulVec (X ω) x i := by
              rfl
  have hleft :
      vecNorm2 (rectMatMulVec (X ω) x) ≤
        P.expectationReal (fun η => vecNorm2 (Y η)) := by
    calc
      vecNorm2 (rectMatMulVec (X ω) x)
          = vecNorm2 (fun i : Fin m => P.expectationReal (fun η => Y η i)) := by
              rw [hmean_vec]
      _ ≤ P.expectationReal (fun η => vecNorm2 (Y η)) :=
              expectationReal_vecNorm2_mean_le_expectationReal_vecNorm2 P Y
  have hright :
      P.expectationReal (fun η => vecNorm2 (Y η)) ≤ L * vecNorm2 x := by
    calc
      P.expectationReal (fun η => vecNorm2 (Y η))
          ≤ P.expectationReal (fun _η : Ω => L * vecNorm2 x) := by
              apply FiniteProbability.expectationReal_mono
              intro η
              exact hdiff η x
      _ = L * vecNorm2 x := by
              rw [FiniteProbability.expectationReal_const]
  exact hleft.trans hright

end FiniteProbability





































































































































































































































































































































/-- Logarithmic form of a power-mass obstruction.  If a bad trace of one-step
mass `p` occurs with product mass `p^s`, then any failure budget `δ` that
dominates that trace mass must satisfy the corresponding logarithmic
sample-count lower bound. -/
theorem log_inv_delta_le_nat_mul_log_inv_of_pow_le
    {s : ℕ} {p δ : ℝ} (hp : 0 < p) (hδ : 0 < δ)
    (hpow : p ^ s ≤ δ) :
    Real.log (1 / δ) ≤ (s : ℝ) * Real.log (1 / p) := by
  have hpows : 0 < p ^ s := pow_pos hp s
  have hrecip : 1 / δ ≤ 1 / (p ^ s) :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hpows hpow
  have hlog :=
    Real.log_le_log (one_div_pos.mpr hδ) hrecip
  have hrewrite :
      Real.log (1 / (p ^ s)) = (s : ℝ) * Real.log (1 / p) := by
    rw [one_div, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
    ring
  simpa [hrewrite] using hlog

/-- Divided logarithmic form of a power-mass obstruction.  If `0 < p < 1`,
then the logarithmic denominator is positive, so the logarithmic obstruction
can be stated as a direct lower bound on the sample count. -/
theorem log_inv_delta_div_log_inv_le_nat_of_pow_le
    {s : ℕ} {p δ : ℝ} (hp : 0 < p) (hp_lt_one : p < 1)
    (hδ : 0 < δ) (hpow : p ^ s ≤ δ) :
    Real.log (1 / δ) / Real.log (1 / p) ≤ (s : ℝ) := by
  have hlog :
      Real.log (1 / δ) ≤ (s : ℝ) * Real.log (1 / p) :=
    log_inv_delta_le_nat_mul_log_inv_of_pow_le hp hδ hpow
  have hden_pos : 0 < Real.log (1 / p) :=
    Real.log_pos (one_lt_one_div hp hp_lt_one)
  exact (div_le_iff₀ hden_pos).mpr hlog























































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- Deterministic floating-point transfer
-- ============================================================

/-- Deterministic transfer for Algorithm 1 spectral residuals.

If the exact residual has rectangular operator-2 bound `ε`, and the computed
sketch differs entrywise from the exact sketch by a nonnegative budget `B`,
then the floating-point residual has rectangular operator-2 bound
`ε + ||B||_F`.

This theorem is intentionally deterministic: the exact high-probability
concentration theorem for CACM equation (2) remains a separate obligation. -/
theorem fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    {ε : ℝ} (B : Fin m → Fin n → ℝ)
    (hExact : rectOpNorm2Le (elementwiseTraceResidual s A samples) ε)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤ B i j) :
    rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
      (ε + frobNormRect B) := by
  let E : Fin m → Fin n → ℝ := fun i j =>
    elementwiseTraceSketch s A (fun _ _ => 0) samples i j -
      fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j
  have hE : frobNormRect E ≤ frobNormRect B := by
    apply frobNormRect_le_of_entry_abs_le E B hB_nonneg
    intro i j
    have h := hEntry i j
    simpa [E, abs_sub_comm] using h
  have hsum :=
    rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le
      (elementwiseTraceResidual s A samples) E hExact hE
  have hres :
      fl_elementwiseTraceResidual fp s A samples =
        fun i j => elementwiseTraceResidual s A samples i j + E i j := by
    ext i j
    unfold fl_elementwiseTraceResidual elementwiseTraceResidual E
    ring
  simpa [hres] using hsum

/-- Deterministic floating-point transfer for Algorithm 1 when the sampler uses
    a supplied exact probability table.

The hypothesis `hProbEntry` is the exact-sketch perturbation caused by using
`p` in the rescaling denominator instead of the ideal squared-magnitude
probability.  The hypothesis `hFlEntry` is the usual floating-point perturbation
while using the supplied exact table `p`. -/
theorem fl_elementwiseTraceResidualWithProb_rectOpNorm2Le_of_ideal
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps)
    {ε : ℝ} (C B : Fin m → Fin n → ℝ)
    (hExact : rectOpNorm2Le (elementwiseTraceResidual s A samples) ε)
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hProbEntry : ∀ i j,
      |elementwiseTraceSketchWithProb s A (fun _ _ => 0) p samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤ C i j)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hFlEntry : ∀ i j,
      |fl_elementwiseTraceSketchWithProb fp s A (fun _ _ => 0) p samples i j -
        elementwiseTraceSketchWithProb s A (fun _ _ => 0) p samples i j| ≤
          B i j) :
    rectOpNorm2Le (fl_elementwiseTraceResidualWithProb fp s A p samples)
      (ε + frobNormRect C + frobNormRect B) := by
  let Eprob : Fin m → Fin n → ℝ := fun i j =>
    elementwiseTraceSketch s A (fun _ _ => 0) samples i j -
      elementwiseTraceSketchWithProb s A (fun _ _ => 0) p samples i j
  have hEprob : frobNormRect Eprob ≤ frobNormRect C := by
    apply frobNormRect_le_of_entry_abs_le Eprob C hC_nonneg
    intro i j
    have h := hProbEntry i j
    simpa [Eprob, abs_sub_comm] using h
  have hExactComputed :
      rectOpNorm2Le (elementwiseTraceResidualWithProb s A p samples)
        (ε + frobNormRect C) := by
    have hsum :=
      rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le
        (elementwiseTraceResidual s A samples) Eprob hExact hEprob
    have hres :
        elementwiseTraceResidualWithProb s A p samples =
          fun i j => elementwiseTraceResidual s A samples i j + Eprob i j := by
      ext i j
      unfold elementwiseTraceResidualWithProb elementwiseTraceResidual Eprob
      ring
    simpa [hres] using hsum
  let Efp : Fin m → Fin n → ℝ := fun i j =>
    elementwiseTraceSketchWithProb s A (fun _ _ => 0) p samples i j -
      fl_elementwiseTraceSketchWithProb fp s A (fun _ _ => 0) p samples i j
  have hEfp : frobNormRect Efp ≤ frobNormRect B := by
    apply frobNormRect_le_of_entry_abs_le Efp B hB_nonneg
    intro i j
    have h := hFlEntry i j
    simpa [Efp, abs_sub_comm] using h
  have hsum :=
    rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le
      (elementwiseTraceResidualWithProb s A p samples) Efp
      hExactComputed hEfp
  have hres :
      fl_elementwiseTraceResidualWithProb fp s A p samples =
        fun i j => elementwiseTraceResidualWithProb s A p samples i j + Efp i j := by
    ext i j
    unfold fl_elementwiseTraceResidualWithProb elementwiseTraceResidualWithProb Efp
    ring
  simpa [hres, add_assoc] using hsum

/-- Floating-point version of the truncated transfer.  The sampled residual
    for the truncated matrix is first transferred through the existing
    Algorithm 1 floating-point perturbation theorem, and then the deterministic
    truncation error is added back. -/
theorem fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
    (fp : FPModel) {m n steps : ℕ} (tau : ℝ) (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    {beta alpha : ℝ} (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hSample :
      rectOpNorm2Le
        (elementwiseTraceResidual s (elementwiseTruncate tau A) samples)
        beta)
    (hPoint :
      ∀ i j,
        |fl_elementwiseTraceSketch fp s (elementwiseTruncate tau A)
            (fun _ _ => 0) samples i j -
          elementwiseTraceSketch s (elementwiseTruncate tau A)
            (fun _ _ => 0) samples i j| ≤ B i j)
    (hTrunc :
      frobNormRect
        (fun i j => A i j - elementwiseTruncate tau A i j) ≤ alpha) :
    rectOpNorm2Le (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
      (beta + frobNormRect B + alpha) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  have hFl :
      rectOpNorm2Le (fl_elementwiseTraceResidual fp s Ahat samples)
        (beta + frobNormRect B) :=
    fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
      fp s Ahat samples B hSample hB_nonneg hPoint
  let M : Fin m → Fin n → ℝ := fl_elementwiseTraceResidual fp s Ahat samples
  let E : Fin m → Fin n → ℝ := fun i j => A i j - Ahat i j
  have hsum :
      rectOpNorm2Le (fun i j => M i j + E i j)
        ((beta + frobNormRect B) + alpha) :=
    rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le M E hFl hTrunc
  have hmain :
      rectOpNorm2Le (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
        ((beta + frobNormRect B) + alpha) := by
    convert hsum using 1
    ext i j
    simp [fl_elementwiseTruncatedTraceResidual, fl_elementwiseTraceResidual,
      Ahat, M, E]
  exact hmain

/-- Truncated floating-point transfer for Algorithm 1 when the sampler uses a
    supplied exact probability table for the truncated matrix. The radius
    separates truncation error, exact-sketch perturbation from changing the
    exact law, and floating-point arithmetic while using that law. -/
theorem fl_elementwiseTruncatedTraceResidualWithProb_rectOpNorm2Le_of_ideal
    (fp : FPModel) {m n steps : ℕ} (tau : ℝ) (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps)
    {beta alpha : ℝ} (C B : Fin m → Fin n → ℝ)
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hSample :
      rectOpNorm2Le
        (elementwiseTraceResidual s (elementwiseTruncate tau A) samples)
        beta)
    (hProbEntry :
      ∀ i j,
        |elementwiseTraceSketchWithProb s (elementwiseTruncate tau A)
            (fun _ _ => 0) p samples i j -
          elementwiseTraceSketch s (elementwiseTruncate tau A)
            (fun _ _ => 0) samples i j| ≤ C i j)
    (hFlEntry :
      ∀ i j,
        |fl_elementwiseTraceSketchWithProb fp s (elementwiseTruncate tau A)
            (fun _ _ => 0) p samples i j -
          elementwiseTraceSketchWithProb s (elementwiseTruncate tau A)
            (fun _ _ => 0) p samples i j| ≤ B i j)
    (hTrunc :
      frobNormRect
        (fun i j => A i j - elementwiseTruncate tau A i j) ≤ alpha) :
    rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidualWithProb fp tau s A p samples)
      (beta + frobNormRect C + frobNormRect B + alpha) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  have hFl :
      rectOpNorm2Le (fl_elementwiseTraceResidualWithProb fp s Ahat p samples)
        (beta + frobNormRect C + frobNormRect B) :=
    fl_elementwiseTraceResidualWithProb_rectOpNorm2Le_of_ideal
      fp s Ahat p samples C B hSample hC_nonneg
      (by simpa [Ahat] using hProbEntry) hB_nonneg
      (by simpa [Ahat] using hFlEntry)
  let M : Fin m → Fin n → ℝ :=
    fl_elementwiseTraceResidualWithProb fp s Ahat p samples
  let E : Fin m → Fin n → ℝ := fun i j => A i j - Ahat i j
  have hsum :
      rectOpNorm2Le (fun i j => M i j + E i j)
        ((beta + frobNormRect C + frobNormRect B) + alpha) :=
    rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le M E hFl hTrunc
  have hmain :
      rectOpNorm2Le
        (fl_elementwiseTruncatedTraceResidualWithProb fp tau s A p samples)
        ((beta + frobNormRect C + frobNormRect B) + alpha) := by
    convert hsum using 1
    ext i j
    simp [fl_elementwiseTruncatedTraceResidualWithProb,
      fl_elementwiseTraceResidualWithProb, Ahat, M, E]
  simpa [add_assoc] using hmain













































































































































































































































/-- Fixed-vector deterministic floating-point transfer for Algorithm 1
residuals.  This is the vector version of the spectral transfer above: an
exact bound for one vector `x` transfers to the rounded residual with the
Frobenius norm of the entrywise perturbation budget multiplied by `||x||₂`. -/
theorem fl_elementwiseTraceResidual_vecNorm2_le_of_exact_fixed_vector
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (x : Fin n → ℝ) {η : ℝ} (B : Fin m → Fin n → ℝ)
    (hExact :
      vecNorm2 (rectMatMulVec (elementwiseTraceResidual s A samples) x) ≤ η)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤ B i j) :
    vecNorm2 (rectMatMulVec (fl_elementwiseTraceResidual fp s A samples) x) ≤
      η + frobNormRect B * vecNorm2 x := by
  let E : Fin m → Fin n → ℝ := fun i j =>
    elementwiseTraceSketch s A (fun _ _ => 0) samples i j -
      fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j
  have hE : frobNormRect E ≤ frobNormRect B := by
    apply frobNormRect_le_of_entry_abs_le E B hB_nonneg
    intro i j
    have h := hEntry i j
    simpa [E, abs_sub_comm] using h
  have hres :
      fl_elementwiseTraceResidual fp s A samples =
        fun i j => elementwiseTraceResidual s A samples i j + E i j := by
    ext i j
    unfold fl_elementwiseTraceResidual elementwiseTraceResidual E
    ring
  have hsplit :
      rectMatMulVec (fl_elementwiseTraceResidual fp s A samples) x =
        fun i =>
          rectMatMulVec (elementwiseTraceResidual s A samples) x i +
            rectMatMulVec E x i := by
    rw [hres]
    ext i
    unfold rectMatMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  calc
    vecNorm2
      (fun i =>
        rectMatMulVec (elementwiseTraceResidual s A samples) x i +
          rectMatMulVec E x i)
        ≤ vecNorm2 (rectMatMulVec (elementwiseTraceResidual s A samples) x) +
            vecNorm2 (rectMatMulVec E x) :=
          vecNorm2_add_le _ _
    _ ≤ η + frobNormRect E * vecNorm2 x := by
          exact add_le_add hExact (vecNorm2_rectMatMulVec_le_frobNormRect_mul E x)
    _ ≤ η + frobNormRect B * vecNorm2 x := by
          exact add_le_add (le_refl η)
            (mul_le_mul_of_nonneg_right hE (vecNorm2_nonneg x))

/-- Algorithm 1 spectral FP transfer with the existing squared-magnitude
    hit-count stability budget.  This is useful only after an exact spectral
    theorem has supplied `hExact`; it does not prove CACM equation (2) by
    itself. -/
theorem fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact_and_hitCount_le
    (fp : FPModel) {m n steps : ℕ} (s Q : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    {ε : ℝ}
    (hExact : rectOpNorm2Le (elementwiseTraceResidual s A samples) ε)
    (hs : (s : ℝ) ≠ 0)
    (hA_ne : ∀ i j, A i j ≠ 0)
    (hcount : ∀ i j, hitCount samples i j ≤ Q)
    (hQ : gammaValid fp Q) (hQ1 : gammaValid fp (Q + 1)) :
    rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
      (ε + frobNormRect
        (fun i j => sqMagTraceErrorBudget fp Q s A (fun _ _ => 0) i j)) := by
  apply fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
      fp s A samples (fun i j =>
        sqMagTraceErrorBudget fp Q s A (fun _ _ => 0) i j)
      hExact
  · intro i j
    unfold sqMagTraceErrorBudget
    have hQnonneg : 0 ≤ (Q : ℝ) := by exact_mod_cast Nat.zero_le Q
    have hgammaQ : 0 ≤ gamma fp Q := gamma_nonneg fp hQ
    have hgamma : 0 ≤ gamma fp (Q + 1) := gamma_nonneg fp hQ1
    exact add_nonneg
      (mul_nonneg
        (abs_nonneg ((fun _ _ => 0 : Fin m → Fin n → ℝ) i j))
        hgammaQ)
      (mul_nonneg
        (mul_nonneg hQnonneg
          (abs_nonneg (frobNormSqRect A / ((s : ℝ) * A i j))))
        hgamma)
  · intro i j
    have h :=
      fl_elementwiseTraceSketch_sqMag_error_bound_of_hitCount_le fp
        s A (fun _ _ => 0) samples i j Q hs (hA_ne i j)
        (hcount i j) hQ hQ1
    rw [← elementwiseTraceSketch_sqMag_eq
      s A (fun _ _ => 0) samples i j hs (hA_ne i j)] at h
    simpa using h

-- ============================================================
-- Exact Frobenius residual concentration under the product trace law
-- ============================================================
































































































































































































































































































































































































































































































































































-- ============================================================
-- Probabilistic transfer
-- ============================================================




















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































set_option maxHeartbeats 800000






































































































































































































































































































































































































































































































































































































































































































































































































































/-- On the positive-probability support of the squared-magnitude trace law, the
zero-initialized floating-point trace admits the repository's deterministic
gamma budget with `Q = steps`.

This support-aware statement is needed for truncated sampling: traces that hit
zero-probability entries have probability zero, and the floating-point model
does not constrain division by a zero denominator on those impossible traces. -/
theorem fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (hs : (s : ℝ) ≠ 0)
    (hsteps : gammaValid fp steps) (hsteps1 : gammaValid fp (steps + 1))
    (hpos : elementwiseTracePositiveProb A samples) :
    ∀ i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤
        sqMagTraceErrorBudget fp steps s A (fun _ _ => 0) i j := by
  intro i j
  by_cases hzero : A i j = 0
  · have hnohit : ∀ t : Fin steps, ¬ sampleHits samples t i j := by
      intro t hhit
      have hp : 0 < sqMagProb A i j := by
        rcases hhit with ⟨hi, hj⟩
        simpa [hi, hj] using hpos t
      exact (entry_ne_zero_of_sqMagProb_pos A i j hp) hzero
    have hfl :
        fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j = 0 :=
      fl_elementwiseTraceSketch_zero_init_eq_zero_of_forall_not_hit
        fp s A samples i j hnohit
    have hexact :
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j = 0 :=
      elementwiseTraceSketch_zero_init_of_entry_eq_zero s A samples i j hzero
    have hbudget :
        0 ≤ sqMagTraceErrorBudget fp steps s A (fun _ _ => 0) i j :=
      sqMagTraceErrorBudget_nonneg fp steps s A (fun _ _ => 0) i j
        hsteps hsteps1
    simpa [hfl, hexact] using hbudget
  · have hcount : hitCount samples i j ≤ steps :=
      hitCount_le_steps samples i j
    have hdet :=
      fl_elementwiseTraceSketch_sqMag_error_bound_exact fp s A (fun _ _ => 0)
        samples i j hs hzero
        (gammaValid_mono fp hcount hsteps)
        (gammaValid_mono fp (Nat.succ_le_succ hcount) hsteps1)
    exact le_trans hdet
      (sqMagTraceErrorBudget_mono fp s A (fun _ _ => 0) i j
        hcount hsteps hsteps1)






















































































































































































































































































































































/-- The zero-initialized literal Algorithm 1 FP perturbation budget is bounded
by a scalar constant when all nonzero entries of `A` are bounded below in
absolute value by `alpha`.

This is the nontruncated analogue of the explicit budget expansion used for the
hard-thresholded route.  Zero entries cause no difficulty on the sampler's
positive-probability support: they are never hit, and Lean's total division
convention makes the displayed budget term zero at those entries. -/
theorem sqMagTraceErrorBudget_zero_init_le_const_of_entry_abs_ge
    (fp : FPModel) {m n s : ℕ} {alpha : ℝ}
    (halpha : 0 < alpha) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|)
    (hgamma1 : gammaValid fp (s + 1)) :
    ∀ i j,
      sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j ≤
        (frobNormSqRect A / alpha) * gamma fp (s + 1) := by
  classical
  intro i j
  by_cases hAij : A i j = 0
  · have hC_nonneg :
        0 ≤ (frobNormSqRect A / alpha) * gamma fp (s + 1) :=
      mul_nonneg
        (div_nonneg (frobNormSqRect_nonneg A) (le_of_lt halpha))
        (gamma_nonneg fp hgamma1)
    simpa [sqMagTraceErrorBudget, hAij] using hC_nonneg
  · have habs_pos : 0 < |A i j| := abs_pos.mpr hAij
    have halpha_le : alpha ≤ |A i j| := hentry i j hAij
    have hinv :
        |frobNormSqRect A / ((s : ℝ) * A i j)| ≤
          frobNormSqRect A / ((s : ℝ) * alpha) := by
      have hnum_nonneg : 0 ≤ frobNormSqRect A := frobNormSqRect_nonneg A
      have hden_abs :
          |(s : ℝ) * A i j| = (s : ℝ) * |A i j| := by
        rw [abs_mul, abs_of_pos hs]
      have hden_pos : 0 < (s : ℝ) * |A i j| :=
        mul_pos hs habs_pos
      have hden_alpha_pos : 0 < (s : ℝ) * alpha :=
        mul_pos hs halpha
      have hden_le : (s : ℝ) * alpha ≤ (s : ℝ) * |A i j| :=
        mul_le_mul_of_nonneg_left halpha_le (le_of_lt hs)
      calc
        |frobNormSqRect A / ((s : ℝ) * A i j)|
            = frobNormSqRect A / ((s : ℝ) * |A i j|) := by
                rw [abs_div, abs_of_nonneg hnum_nonneg, hden_abs]
        _ ≤ frobNormSqRect A / ((s : ℝ) * alpha) :=
              div_le_div_of_nonneg_left hnum_nonneg hden_alpha_pos hden_le
    have hbase :
        (s : ℝ) * |frobNormSqRect A / ((s : ℝ) * A i j)| ≤
          frobNormSqRect A / alpha := by
      have hmul :=
        mul_le_mul_of_nonneg_left hinv (le_of_lt hs)
      have hcancel :
          (s : ℝ) * (frobNormSqRect A / ((s : ℝ) * alpha)) =
            frobNormSqRect A / alpha := by
        field_simp [hs.ne', halpha.ne']
      simpa [hcancel] using hmul
    have hterm :
        (s : ℝ) *
            |frobNormSqRect A / ((s : ℝ) * A i j)| *
            gamma fp (s + 1) ≤
          (frobNormSqRect A / alpha) * gamma fp (s + 1) :=
      mul_le_mul_of_nonneg_right hbase (gamma_nonneg fp hgamma1)
    simpa [sqMagTraceErrorBudget, hAij] using hterm

/-- Square-matrix Frobenius expansion of the literal Algorithm 1 gamma budget
under an explicit nonzero-entry lower bound `alpha`.

The conclusion contains no hidden budget matrix:
`||B||_F <= n * (||A||_F^2 / alpha) * gamma_{s+1}`. -/
theorem frobNormRect_sqMagTraceErrorBudget_zero_init_le_const_square_of_entry_abs_ge
    (fp : FPModel) {n s : ℕ} {alpha : ℝ}
    (halpha : 0 < alpha) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|)
    (hgamma1 : gammaValid fp (s + 1)) :
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j) ≤
      (n : ℝ) * ((frobNormSqRect A / alpha) * gamma fp (s + 1)) := by
  classical
  let C : ℝ := (frobNormSqRect A / alpha) * gamma fp (s + 1)
  have hgamma : gammaValid fp s :=
    gammaValid_mono fp (Nat.le_succ s) hgamma1
  have hC_nonneg : 0 ≤ C :=
    mul_nonneg
      (div_nonneg (frobNormSqRect_nonneg A) (le_of_lt halpha))
      (gamma_nonneg fp hgamma1)
  calc
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j)
        ≤ frobNormRect (fun _i : Fin n => fun _j : Fin n => C) := by
          apply frobNormRect_le_of_entry_abs_le
          · intro _ _
            exact hC_nonneg
          · intro i j
            have hnonneg :
                0 ≤ sqMagTraceErrorBudget fp s s A
                    (fun _ _ => 0) i j :=
              sqMagTraceErrorBudget_nonneg fp s s A
                (fun _ _ => 0) i j hgamma hgamma1
            have hle :
                sqMagTraceErrorBudget fp s s A
                    (fun _ _ => 0) i j ≤ C := by
              simpa [C] using
                sqMagTraceErrorBudget_zero_init_le_const_of_entry_abs_ge
                  fp halpha hs A hentry hgamma1 i j
            simpa [abs_of_nonneg hnonneg] using hle
    _ = (n : ℝ) * C := frobNormRect_const_square C hC_nonneg
    _ = (n : ℝ) * ((frobNormSqRect A / alpha) * gamma fp (s + 1)) := by
          simp [C]

/-- The zero-initialized literal Algorithm 1 FP perturbation budget is bounded
entrywise by the input-dependent reciprocal-entry contribution radius.

The right hand side is completely determined by the exact input matrix, the
sample count, and the local floating-point `gamma` factor.  No lower bound on
the nonzero entries is assumed; very small nonzero entries are charged through
`elementwiseLiteralContributionRadius`. -/
theorem sqMagTraceErrorBudget_zero_init_le_literalContributionRadius
    (fp : FPModel) {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hgamma1 : gammaValid fp (s + 1)) :
    ∀ i j,
      sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j ≤
        ((s : ℝ) * elementwiseLiteralContributionRadius s A) *
          gamma fp (s + 1) := by
  classical
  intro i j
  let Rlit : ℝ := elementwiseLiteralContributionRadius s A
  have hRlit_nonneg : 0 ≤ Rlit := by
    simpa [Rlit] using elementwiseLiteralContributionRadius_nonneg hs A
  have hgamma_nonneg : 0 ≤ gamma fp (s + 1) :=
    gamma_nonneg fp hgamma1
  have hC_nonneg :
      0 ≤ ((s : ℝ) * Rlit) * gamma fp (s + 1) :=
    mul_nonneg
      (mul_nonneg (le_of_lt hs) hRlit_nonneg)
      hgamma_nonneg
  by_cases hAij : A i j = 0
  · simpa [sqMagTraceErrorBudget, hAij, Rlit] using hC_nonneg
  · have hsingle :
        frobNormSqRect A / ((s : ℝ) * |A i j|) ≤ Rlit := by
      have h :=
        literal_entry_contribution_le_elementwiseLiteralContributionRadius
          hs A i j
      simpa [hAij, Rlit] using h
    have hF_nonneg : 0 ≤ frobNormSqRect A := frobNormSqRect_nonneg A
    have habs :
        |frobNormSqRect A / ((s : ℝ) * A i j)| =
          frobNormSqRect A / ((s : ℝ) * |A i j|) := by
      rw [abs_div, abs_mul, abs_of_nonneg hF_nonneg,
        abs_of_pos hs]
    have hbase :
        (s : ℝ) * |frobNormSqRect A / ((s : ℝ) * A i j)| ≤
          (s : ℝ) * Rlit := by
      rw [habs]
      exact mul_le_mul_of_nonneg_left hsingle (le_of_lt hs)
    have hterm :
        (s : ℝ) * |frobNormSqRect A / ((s : ℝ) * A i j)| *
            gamma fp (s + 1) ≤
          ((s : ℝ) * Rlit) * gamma fp (s + 1) :=
      mul_le_mul_of_nonneg_right hbase hgamma_nonneg
    simpa [sqMagTraceErrorBudget, hAij, Rlit] using hterm

/-- Rectangular Frobenius expansion of the literal Algorithm 1 gamma budget
using the input-dependent reciprocal-entry contribution radius.

The conclusion contains no hidden budget matrix:
`||B||_F <= sqrt(m*n) * (s * R_lit(A,s)) * gamma_{s+1}`. -/
theorem frobNormRect_sqMagTraceErrorBudget_zero_init_le_literalContributionRadius
    (fp : FPModel) {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j) ≤
      Real.sqrt ((m : ℝ) * (n : ℝ)) *
        (((s : ℝ) * elementwiseLiteralContributionRadius s A) *
          gamma fp (s + 1)) := by
  classical
  let C : ℝ :=
    ((s : ℝ) * elementwiseLiteralContributionRadius s A) *
      gamma fp (s + 1)
  have hRlit_nonneg :
      0 ≤ elementwiseLiteralContributionRadius s A :=
    elementwiseLiteralContributionRadius_nonneg hs A
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt hs) hRlit_nonneg)
      (gamma_nonneg fp hgamma1)
  have hentry :
      ∀ i j,
        |sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j| ≤ C := by
    intro i j
    have hnonneg :
        0 ≤ sqMagTraceErrorBudget fp s s A
            (fun _ _ => 0) i j :=
      sqMagTraceErrorBudget_nonneg fp s s A
        (fun _ _ => 0) i j hgamma hgamma1
    have hle :
        sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j ≤ C := by
      simpa [C] using
        sqMagTraceErrorBudget_zero_init_le_literalContributionRadius
          fp hs A hgamma1 i j
    simpa [abs_of_nonneg hnonneg] using hle
  simpa [C] using
    frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
      (fun i j =>
        sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j)
      hC_nonneg hentry






















































































































































































































































































































































































































/-- The zero-initialized truncated Algorithm 1 FP perturbation budget is
bounded by a scalar constant on each entry.  This is the local expansion of the
internal budget matrix used by the gamma-square corollary. -/
theorem sqMagTraceErrorBudget_zero_init_truncated_le_const
    (fp : FPModel) {m n s : ℕ} {tau : ℝ} (htau : 0 < tau)
    (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hgamma1 : gammaValid fp (s + 1)) :
    ∀ i j,
      sqMagTraceErrorBudget fp s s (elementwiseTruncate tau A)
          (fun _ _ => 0) i j ≤
        (frobNormSqRect (elementwiseTruncate tau A) / tau) *
          gamma fp (s + 1) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  intro i j
  by_cases hAij : Ahat i j = 0
  · have hC_nonneg :
        0 ≤ (frobNormSqRect Ahat / tau) * gamma fp (s + 1) :=
      mul_nonneg
        (div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt htau))
        (gamma_nonneg fp hgamma1)
    simpa [sqMagTraceErrorBudget, Ahat, hAij] using hC_nonneg
  · have hsample : elementwiseTruncate tau A i j ≠ 0 := by
      simpa [Ahat] using hAij
    have hcontrib :=
      elementwiseSampleContribution_truncated_entry_abs_le
        (m := m) (n := n) (tau := tau) htau (s := s) hs
        A (i, j) hsample i j
    have hinc :
        |elementwiseIncrement s Ahat i j| ≤
          frobNormSqRect Ahat / ((s : ℝ) * tau) := by
      simpa [Ahat, elementwiseSampleContribution] using hcontrib
    have hinc_eq :
        elementwiseIncrement s Ahat i j =
          frobNormSqRect Ahat / ((s : ℝ) * Ahat i j) :=
      elementwiseIncrement_sqMag_eq s Ahat i j hs.ne' hAij
    have habs :
        |frobNormSqRect Ahat / ((s : ℝ) * Ahat i j)| ≤
          frobNormSqRect Ahat / ((s : ℝ) * tau) := by
      simpa [hinc_eq] using hinc
    have hbase :
        (s : ℝ) * |frobNormSqRect Ahat / ((s : ℝ) * Ahat i j)| ≤
          frobNormSqRect Ahat / tau := by
      have hmul :=
        mul_le_mul_of_nonneg_left habs (le_of_lt hs)
      have hcancel :
          (s : ℝ) * (frobNormSqRect Ahat / ((s : ℝ) * tau)) =
            frobNormSqRect Ahat / tau := by
        field_simp [hs.ne', htau.ne']
      simpa [hcancel] using hmul
    have hterm :
        (s : ℝ) *
            |frobNormSqRect Ahat / ((s : ℝ) * Ahat i j)| *
            gamma fp (s + 1) ≤
          (frobNormSqRect Ahat / tau) * gamma fp (s + 1) :=
      mul_le_mul_of_nonneg_right hbase (gamma_nonneg fp hgamma1)
    simpa [sqMagTraceErrorBudget, Ahat] using hterm

/-- Frobenius expansion of the internal Algorithm 1 gamma budget in the square
truncated route.  The budget matrix is bounded by the Frobenius norm of the
constant matrix with entry
`(||Ahat||_F^2 / tau) * gamma fp (s+1)`, hence by
`n * (||Ahat||_F^2 / tau) * gamma fp (s+1)`. -/
theorem frobNormRect_sqMagTraceErrorBudget_zero_init_truncated_le_const_square
    (fp : FPModel) {n s : ℕ} {tau : ℝ} (htau : 0 < tau)
    (hs : 0 < (s : ℝ)) (A : Fin n → Fin n → ℝ)
    (hgamma1 : gammaValid fp (s + 1)) :
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s (elementwiseTruncate tau A)
            (fun _ _ => 0) i j) ≤
      (n : ℝ) *
        ((frobNormSqRect (elementwiseTruncate tau A) / tau) *
          gamma fp (s + 1)) := by
  classical
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  let C : ℝ := (frobNormSqRect Ahat / tau) * gamma fp (s + 1)
  have hgamma : gammaValid fp s :=
    gammaValid_mono fp (Nat.le_succ s) hgamma1
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg
      (div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt htau))
      (gamma_nonneg fp hgamma1)
  calc
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j)
        ≤ frobNormRect (fun _i : Fin n => fun _j : Fin n => C) := by
          apply frobNormRect_le_of_entry_abs_le
          · intro _ _
            exact hC_nonneg
          · intro i j
            have hnonneg :
                0 ≤ sqMagTraceErrorBudget fp s s Ahat
                    (fun _ _ => 0) i j :=
              sqMagTraceErrorBudget_nonneg fp s s Ahat
                (fun _ _ => 0) i j hgamma hgamma1
            have hle :
                sqMagTraceErrorBudget fp s s Ahat
                    (fun _ _ => 0) i j ≤ C := by
              simpa [Ahat, C] using
                sqMagTraceErrorBudget_zero_init_truncated_le_const
                  fp htau hs A hgamma1 i j
            simpa [abs_of_nonneg hnonneg] using hle
    _ = (n : ℝ) * C := frobNormRect_const_square C hC_nonneg
    _ = (n : ℝ) *
        ((frobNormSqRect (elementwiseTruncate tau A) / tau) *
          gamma fp (s + 1)) := by
          simp [Ahat, C]


































































































































































/-- Frobenius expansion of the internal Algorithm 1 gamma budget in the
rectangular truncated route.

The budget matrix is bounded by the rectangular Frobenius norm of the constant
matrix with entry `(||Ahat||_F^2/tau) * gamma fp (s+1)`, hence by
`sqrt(mn) * (||Ahat||_F^2/tau) * gamma fp (s+1)`. -/
theorem frobNormRect_sqMagTraceErrorBudget_zero_init_truncated_le_const_rect
    (fp : FPModel) {m n s : ℕ} {tau : ℝ} (htau : 0 < tau)
    (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hgamma1 : gammaValid fp (s + 1)) :
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s (elementwiseTruncate tau A)
            (fun _ _ => 0) i j) ≤
      Real.sqrt ((m : ℝ) * (n : ℝ)) *
        ((frobNormSqRect (elementwiseTruncate tau A) / tau) *
          gamma fp (s + 1)) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let C : ℝ := (frobNormSqRect Ahat / tau) * gamma fp (s + 1)
  have hgamma : gammaValid fp s :=
    gammaValid_mono fp (Nat.le_succ s) hgamma1
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg
      (div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt htau))
      (gamma_nonneg fp hgamma1)
  calc
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j)
        ≤ frobNormRect (fun _i : Fin m => fun _j : Fin n => C) := by
          apply frobNormRect_le_of_entry_abs_le
          · intro _ _
            exact hC_nonneg
          · intro i j
            have hnonneg :
                0 ≤ sqMagTraceErrorBudget fp s s Ahat
                    (fun _ _ => 0) i j :=
              sqMagTraceErrorBudget_nonneg fp s s Ahat
                (fun _ _ => 0) i j hgamma hgamma1
            have hle :
                sqMagTraceErrorBudget fp s s Ahat
                    (fun _ _ => 0) i j ≤ C := by
              simpa [Ahat, C] using
                sqMagTraceErrorBudget_zero_init_truncated_le_const
                  fp htau hs A hgamma1 i j
            simpa [abs_of_nonneg hnonneg] using hle
    _ ≤ Real.sqrt ((m : ℝ) * (n : ℝ)) * C :=
          frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
            (fun _i : Fin m => fun _j : Fin n => C) hC_nonneg
            (by
              intro _ _
              simp [abs_of_nonneg hC_nonneg])
    _ = Real.sqrt ((m : ℝ) * (n : ℝ)) *
        ((frobNormSqRect (elementwiseTruncate tau A) / tau) *
          gamma fp (s + 1)) := by
          simp [Ahat, C]

































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
