import NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.HitCounts.Bounds
import NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.SpectralTransfer.Elementwise
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.Elementwise.Core
import NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge
import NumStability.Analysis.CStarMatrices.Expectation.Finite
import NumStability.Analysis.CStarMatrices.Trace.Basic
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.FunctionalCalculus.OperatorLog.Monotonicity
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixConcentration
import NumStability.Analysis.MatrixInequalities.LiebTrace.Concavity
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm01.ElementwiseSampling.HitCountConcentration
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm01.ElementwiseSampling.TraceMGF
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.Preconditioning

/-!
# NumStability.Source.DrineasMahoney.RandNLA2016.Equation02.SpectralApproximation.ElementwiseSpectral

W11 canonical source correspondence destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.ElementwiseSpectral`; the historical path re-exports this module.
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





















































































































































































































































































































































































































































































































































































































































































































































































































































/-- Positive-probability support under the literal squared-magnitude law gives
the spectral upper-bound hypothesis needed by the support-aware C⋆ Bernstein
log-CGF theorem, with an explicit input-dependent radius. -/
theorem sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_literal_spectrum_le_supportRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (sample : ElementwiseSample m n)
    (hsampleProb : 0 < (sqMagSampleProbability A hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)))) :
    x ≤ elementwiseLiteralResidualSupportRadius s A := by
  classical
  let L : ℝ := elementwiseLiteralResidualSupportRadius s A
  have hsampleSq : 0 < sqMagProb A sample.1 sample.2 := by
    simpa [sqMagSampleProbability] using hsampleProb
  have hsample_ne : A sample.1 sample.2 ≠ 0 :=
    entry_ne_zero_of_sqMagProb_pos A sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample))
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
    simpa [L] using
      finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_literal_supportRadius
        hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample)) :=
    rectSelfAdjointDilation_symmetric
      (elementwiseSampleResidualIncrement s A sample)
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample))
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  exact cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hx

/-- Negative-increment companion of the literal support-radius spectral bound. -/
theorem sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_literal_spectrum_le_supportRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (sample : ElementwiseSample m n)
    (hsampleProb : 0 < (sqMagSampleProbability A hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) :
    x ≤ elementwiseLiteralResidualSupportRadius s A := by
  classical
  let L : ℝ := elementwiseLiteralResidualSupportRadius s A
  have hsampleSq : 0 < sqMagProb A sample.1 sample.2 := by
    simpa [sqMagSampleProbability] using hsampleProb
  have hsample_ne : A sample.1 sample.2 ≠ 0 :=
    entry_ne_zero_of_sqMagProb_pos A sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
    simpa [L] using
      finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_literal_supportRadius
        hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) := by
    intro a b
    change
      -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b =
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) b a
    rw [rectSelfAdjointDilation_symmetric]
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      -finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_neg, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  exact cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hx

/-- A one-row, two-column family with one unit entry and one arbitrarily small
positive entry.  It is used to show that literal squared-magnitude sampling
does not supply a uniform bounded-increment radius for untruncated Algorithm 1:
the small entry is sampled with positive probability, but its rescaled
contribution is proportional to the reciprocal of that entry. -/
noncomputable def algorithm1SmallEntrySupportMatrix (L : ℝ) :
    Fin 1 → Fin 2 → ℝ :=
  fun _ j => if j = (0 : Fin 2) then 1 else (|L| + 2)⁻¹

/-- The counterexample family has positive squared-magnitude denominator. -/
theorem sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos (L : ℝ) :
    0 < sqMagProbDen (algorithm1SmallEntrySupportMatrix L) := by
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  simp [sqMagProbDen, frobNormSqRect, algorithm1SmallEntrySupportMatrix,
    add_pos_of_pos_of_nonneg zero_lt_one
      (le_of_lt (inv_pos.mpr (sq_pos_of_pos hbase)))]

/-- The small entry in the counterexample family has positive
squared-magnitude sampling probability. -/
theorem sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos (L : ℝ) :
    0 <
      sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2) := by
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  exact
    sqMagProb_pos_of_entry_ne_zero
      (algorithm1SmallEntrySupportMatrix L)
      (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
      (0 : Fin 1) (1 : Fin 2)
      (by
        simp [algorithm1SmallEntrySupportMatrix,
          inv_ne_zero (ne_of_gt hbase)])

/-- The small-entry sampling probability in the counterexample family is
strictly less than one. -/
theorem sqMagProb_algorithm1SmallEntrySupportMatrix_small_lt_one (L : ℝ) :
    sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2) < 1 := by
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  have hβ : 0 < ((|L| + 2) ^ 2)⁻¹ :=
    inv_pos.mpr (sq_pos_of_pos hbase)
  simp [sqMagProb, sqMagProbDen, frobNormSqRect,
    algorithm1SmallEntrySupportMatrix]
  change
    ((|L| + 2) ^ 2)⁻¹ /
        (1 + ((|L| + 2) ^ 2)⁻¹) < 1
  have hden : 0 < 1 + ((|L| + 2) ^ 2)⁻¹ := by
    nlinarith
  have hnum_lt_den :
      ((|L| + 2) ^ 2)⁻¹ < 1 + ((|L| + 2) ^ 2)⁻¹ := by
    nlinarith
  exact (div_lt_iff₀ hden).mpr (by simp [hnum_lt_den])

/-- On the positive-probability small-entry sample, the one-step literal
residual increment has arbitrarily large entry magnitude.

This is a formal obstruction to instantiating the repository's current
bounded-increment matrix-Bernstein route for the untruncated squared-magnitude
sampler by a radius depending only on dimensions, sample count, and the
Frobenius scale. -/
theorem algorithm1SmallEntrySupportMatrix_residual_increment_abs_eq (L : ℝ) :
    |elementwiseSampleResidualIncrement 1
        (algorithm1SmallEntrySupportMatrix L)
        ((0 : Fin 1), (1 : Fin 2)) (0 : Fin 1) (1 : Fin 2)| =
      |L| + 2 := by
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  have hbase_ne : |L| + 2 ≠ 0 := ne_of_gt hbase
  have hden_ne : (1 + ((|L| + 2)⁻¹) ^ 2) ≠ 0 := by
    positivity
  have hres :
      elementwiseSampleResidualIncrement 1
          (algorithm1SmallEntrySupportMatrix L)
          ((0 : Fin 1), (1 : Fin 2)) (0 : Fin 1) (1 : Fin 2) =
        -(|L| + 2) := by
    simp [elementwiseSampleResidualIncrement, elementwiseSampleContribution,
      elementwiseIncrement, elementwiseIncrementWithProb, sqMagProb,
      sqMagProbDen, frobNormSqRect, algorithm1SmallEntrySupportMatrix]
    field_simp [hbase_ne]
    ring
  rw [hres, abs_neg, abs_of_pos hbase]

/-- The positive-probability small-entry sample in the counterexample family
violates the rectangular operator-2 support predicate at radius `L`. -/
theorem algorithm1SmallEntrySupportMatrix_residual_increment_not_rectOpNorm2Le
    (L : ℝ) :
    ¬ rectOpNorm2Le
      (elementwiseSampleResidualIncrement 1
        (algorithm1SmallEntrySupportMatrix L)
        ((0 : Fin 1), (1 : Fin 2))) L := by
  intro hnorm
  let M : Fin 1 → Fin 2 → ℝ :=
    elementwiseSampleResidualIncrement 1
      (algorithm1SmallEntrySupportMatrix L)
      ((0 : Fin 1), (1 : Fin 2))
  let x : Fin 2 → ℝ := finiteBasisVec (1 : Fin 2)
  have hxnorm : vecNorm2 x = 1 := by
    simp [x, finiteBasisVec, vecNorm2, vecNorm2Sq]
  have hleft :
      vecNorm2 (rectMatMulVec M x) =
        |elementwiseSampleResidualIncrement 1
          (algorithm1SmallEntrySupportMatrix L)
          ((0 : Fin 1), (1 : Fin 2)) (0 : Fin 1) (1 : Fin 2)| := by
    simp [M, x, rectMatMulVec, finiteBasisVec, vecNorm2, vecNorm2Sq]
    rw [Real.sqrt_sq_eq_abs]
  have hbound := hnorm x
  rw [hleft, hxnorm, mul_one,
    algorithm1SmallEntrySupportMatrix_residual_increment_abs_eq] at hbound
  nlinarith [le_abs_self L]

/-- For every proposed entrywise support radius `L`, literal untruncated
squared-magnitude sampling admits a positive-probability sample whose exact
one-step residual increment exceeds that radius. -/
theorem exists_sqMagPositive_sampleResidualIncrement_entry_abs_gt (L : ℝ) :
    ∃ (A : Fin 1 → Fin 2 → ℝ) (sample : ElementwiseSample 1 2),
      0 < sqMagProbDen A ∧
      0 < sqMagProb A sample.1 sample.2 ∧
      L < |elementwiseSampleResidualIncrement 1 A sample
        (0 : Fin 1) (1 : Fin 2)| := by
  refine
    ⟨algorithm1SmallEntrySupportMatrix L,
      ((0 : Fin 1), (1 : Fin 2)),
      sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L,
      sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L, ?_⟩
  rw [algorithm1SmallEntrySupportMatrix_residual_increment_abs_eq]
  nlinarith [le_abs_self L]

/-- Therefore no proposed scalar radius `L` can bound all positive-probability
literal squared-magnitude one-step residual increments in the rectangular
operator-2 predicate used by the spectral concentration layer. -/
theorem exists_sqMagPositive_sampleResidualIncrement_not_rectOpNorm2Le
    (L : ℝ) :
    ∃ (A : Fin 1 → Fin 2 → ℝ) (sample : ElementwiseSample 1 2),
      0 < sqMagProbDen A ∧
      0 < sqMagProb A sample.1 sample.2 ∧
      ¬ rectOpNorm2Le (elementwiseSampleResidualIncrement 1 A sample) L := by
  refine
    ⟨algorithm1SmallEntrySupportMatrix L,
      ((0 : Fin 1), (1 : Fin 2)),
      sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L,
      sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L, ?_⟩
  exact algorithm1SmallEntrySupportMatrix_residual_increment_not_rectOpNorm2Le L

/-- For the one-step exact squared-magnitude trace law, the counterexample
family violates the radius-`L` exact Algorithm 1 spectral event with strictly
positive probability.  Thus the obstruction is not merely existential: it
occurs on an event of positive mass under the exact product law. -/
theorem sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_smallEntry_pos
    (L : ℝ) :
    0 <
      (sqMagTraceProbability (steps := 1)
        (algorithm1SmallEntrySupportMatrix L)
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
        {samples : ElementwiseTrace 1 2 1 |
          ¬ rectOpNorm2Le
            (elementwiseTraceResidual 1
              (algorithm1SmallEntrySupportMatrix L) samples) L} := by
  classical
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let P := sqMagTraceProbability (steps := 1) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let Hit : Set (ElementwiseTrace 1 2 1) :=
    {samples | sampleHits samples (0 : Fin 1) (0 : Fin 1) (1 : Fin 2)}
  let Bad : Set (ElementwiseTrace 1 2 1) :=
    {samples |
      ¬ rectOpNorm2Le (elementwiseTraceResidual 1 A samples) L}
  have hHitProb :
      P.eventProb Hit =
        sqMagProb A (0 : Fin 1) (1 : Fin 2) := by
    simpa [P, Hit, A] using
      sqMagTraceProbability_eventProb_sampleHits
        (algorithm1SmallEntrySupportMatrix L)
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
        (0 : Fin 1) (0 : Fin 1) (1 : Fin 2)
  have hHitProb_pos : 0 < P.eventProb Hit := by
    rw [hHitProb]
    exact sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hsubset : Hit ⊆ Bad := by
    intro samples hhit
    have hsamp :
        samples (0 : Fin 1) = ((0 : Fin 1), (1 : Fin 2)) :=
      Prod.ext hhit.1 hhit.2
    have htrace :
        elementwiseTraceResidual 1 A samples =
          elementwiseSampleResidualIncrement 1 A
            ((0 : Fin 1), (1 : Fin 2)) := by
      ext i j
      simp [elementwiseTraceResidual, elementwiseTraceSketch,
        elementwiseTraceContribution, elementwiseSampleResidualIncrement,
        elementwiseSampleContribution, sampleHits, hsamp]
    intro hnorm
    exact
      algorithm1SmallEntrySupportMatrix_residual_increment_not_rectOpNorm2Le L
        (by simpa [A, htrace] using hnorm)
  exact hHitProb_pos.trans_le (P.eventProb_mono hsubset)

/-- The same small-entry family also breaks an exact one-step copy-difference
operator bound: compare the trace that samples the tiny entry with the trace
that samples the unit entry. -/
theorem algorithm1SmallEntrySupportMatrix_trace_residual_small_unit_diff_not_rectOpNorm2Le
    (L : ℝ) :
    ¬ rectOpNorm2Le
      (fun i j =>
        elementwiseTraceResidual 1 (algorithm1SmallEntrySupportMatrix L)
          (fun _ : Fin 1 => ((0 : Fin 1), (1 : Fin 2))) i j -
        elementwiseTraceResidual 1 (algorithm1SmallEntrySupportMatrix L)
          (fun _ : Fin 1 => ((0 : Fin 1), (0 : Fin 2))) i j)
      L := by
  classical
  intro hnorm
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let samplesSmall : ElementwiseTrace 1 2 1 :=
    fun _ : Fin 1 => ((0 : Fin 1), (1 : Fin 2))
  let samplesUnit : ElementwiseTrace 1 2 1 :=
    fun _ : Fin 1 => ((0 : Fin 1), (0 : Fin 2))
  let M : Fin 1 → Fin 2 → ℝ :=
    fun i j =>
      elementwiseTraceResidual 1 A samplesSmall i j -
        elementwiseTraceResidual 1 A samplesUnit i j
  let x : Fin 2 → ℝ := finiteBasisVec (1 : Fin 2)
  have hxnorm : vecNorm2 x = 1 := by
    simp [x, finiteBasisVec, vecNorm2, vecNorm2Sq]
  have hleft :
      vecNorm2 (rectMatMulVec M x) = |M (0 : Fin 1) (1 : Fin 2)| := by
    simp [M, x, rectMatMulVec, finiteBasisVec, vecNorm2, vecNorm2Sq]
    rw [Real.sqrt_sq_eq_abs]
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  have hbase_ne : |L| + 2 ≠ 0 := ne_of_gt hbase
  have hentry :
      M (0 : Fin 1) (1 : Fin 2) =
        -((|L| + 2) + (|L| + 2)⁻¹) := by
    simp [M, A, samplesSmall, samplesUnit, elementwiseTraceResidual,
      elementwiseTraceSketch, elementwiseTraceContribution,
      sampleHits, elementwiseIncrement, elementwiseIncrementWithProb, sqMagProb,
      sqMagProbDen, frobNormSqRect, algorithm1SmallEntrySupportMatrix]
    field_simp [hbase_ne]
    ring_nf
  have hentry_gt : L < |M (0 : Fin 1) (1 : Fin 2)| := by
    rw [hentry, abs_neg]
    have hinv_pos : 0 < (|L| + 2)⁻¹ := inv_pos.mpr hbase
    rw [abs_of_pos (add_pos hbase hinv_pos)]
    nlinarith [le_abs_self L, hinv_pos]
  have hbound := hnorm x
  rw [hleft, hxnorm, mul_one] at hbound
  exact not_le_of_gt hentry_gt hbound





















































































/-- Under the canonical squared-magnitude product law for the truncated
    matrix, the retained-sample bounded-increment side condition holds with
    probability one.  This discharges the support issue for later
    Bernstein-style concentration theorems; it is not itself a tail bound. -/
theorem sqMagTraceProbability_eventProb_truncatedResidualIncrementsBoundedEvent_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (truncatedResidualIncrementsBoundedEvent tau A
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let Bound : Set (ElementwiseTrace m n s) :=
    truncatedResidualIncrementsBoundedEvent tau A
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hgood_prob : P.eventProb Good = 1 := by
    simpa [P, Good, Ahat] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hsubset : Good ⊆ Bound := by
    intro samples hgood t
    have hsample_pos : 0 < sqMagProb Ahat (samples t).1 (samples t).2 :=
      hgood t
    have hsample_ne :
        elementwiseTruncate tau A (samples t).1 (samples t).2 ≠ 0 := by
      simpa [Ahat] using
        entry_ne_zero_of_sqMagProb_pos Ahat (samples t).1 (samples t).2
          hsample_pos
    exact
      rectOpNorm2Le_elementwiseSampleResidualIncrement_truncated
        htau hs A (samples t) hsample_ne
  have hmono : P.eventProb Good ≤ P.eventProb Bound :=
    FiniteProbability.eventProb_mono P hsubset
  have hge : 1 ≤ P.eventProb Bound := by
    linarith
  have hle : P.eventProb Bound ≤ 1 :=
    FiniteProbability.eventProb_le_one P Bound
  have hbound_prob : P.eventProb Bound = 1 := le_antisymm hle hge
  simpa [P, Bound, Ahat] using hbound_prob
































































































































































































































/-- Under the canonical squared-magnitude product law for the truncated
    matrix, the self-adjoint dilation bounded-increment condition holds with
    probability one.  This is a Bernstein prerequisite, not the Bernstein tail
    theorem itself. -/
theorem sqMagTraceProbability_eventProb_truncatedDilationIncrementsBoundedEvent_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (truncatedDilationIncrementsBoundedEvent tau A
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let Bound : Set (ElementwiseTrace m n s) :=
    truncatedDilationIncrementsBoundedEvent tau A
      (Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau)))
  have hgood_prob : P.eventProb Good = 1 := by
    simpa [P, Good, Ahat] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hsubset : Good ⊆ Bound := by
    intro samples hgood t
    have hsample_pos : 0 < sqMagProb Ahat (samples t).1 (samples t).2 :=
      hgood t
    have hsample_ne :
        elementwiseTruncate tau A (samples t).1 (samples t).2 ≠ 0 := by
      simpa [Ahat] using
        entry_ne_zero_of_sqMagProb_pos Ahat (samples t).1 (samples t).2
          hsample_pos
    exact
      finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A (samples t) hsample_ne
  have hmono : P.eventProb Good ≤ P.eventProb Bound :=
    FiniteProbability.eventProb_mono P hsubset
  have hge : 1 ≤ P.eventProb Bound := by
    linarith
  have hle : P.eventProb Bound ≤ 1 :=
    FiniteProbability.eventProb_le_one P Bound
  have hbound_prob : P.eventProb Bound = 1 := le_antisymm hle hge
  simpa [P, Bound, Ahat] using hbound_prob

/-- Under the truncated squared-magnitude product law, the two-sided Loewner
    bounded-increment side condition for the self-adjoint dilation increments
    holds with probability one.  This is still a Bernstein prerequisite, not a
    trace-MGF or spectral tail theorem. -/
theorem sqMagTraceProbability_eventProb_truncatedDilationIncrementLoewnerBoundedEvent_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (truncatedDilationIncrementLoewnerBoundedEvent tau A
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  let Bound : Set (ElementwiseTrace m n s) :=
    truncatedDilationIncrementLoewnerBoundedEvent tau A L
  have hgood_prob : P.eventProb Good = 1 := by
    simpa [P, Good, Ahat] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hsubset : Good ⊆ Bound := by
    intro samples hgood t
    have hsample_pos : 0 < sqMagProb Ahat (samples t).1 (samples t).2 :=
      hgood t
    have hsample_ne :
        elementwiseTruncate tau A (samples t).1 (samples t).2 ≠ 0 := by
      simpa [Ahat] using
        entry_ne_zero_of_sqMagProb_pos Ahat (samples t).1 (samples t).2
          hsample_pos
    constructor
    · simpa [Ahat, L, Bound, truncatedDilationIncrementLoewnerBoundedEvent] using
        finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
          htau hs A (samples t) hsample_ne
    · simpa [Ahat, L, Bound, truncatedDilationIncrementLoewnerBoundedEvent] using
        finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
          htau hs A (samples t) hsample_ne
  have hmono : P.eventProb Good ≤ P.eventProb Bound :=
    FiniteProbability.eventProb_mono P hsubset
  have hge : 1 ≤ P.eventProb Bound := by
    linarith
  have hle : P.eventProb Bound ≤ 1 :=
    FiniteProbability.eventProb_le_one P Bound
  have hbound_prob : P.eventProb Bound = 1 := le_antisymm hle hge
  simpa [P, Bound, Ahat, L] using hbound_prob



































































/-- The squared-Loewner bounded-increment event for truncated self-adjoint
    dilation increments has probability one under the truncated product law. -/
theorem sqMagTraceProbability_eventProb_truncatedDilationIncrementSquaresBoundedEvent_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (truncatedDilationIncrementSquaresBoundedEvent tau A
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  let Bound : Set (ElementwiseTrace m n s) :=
    truncatedDilationIncrementSquaresBoundedEvent tau A L
  have hgood_prob : P.eventProb Good = 1 := by
    simpa [P, Good, Ahat] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hsubset : Good ⊆ Bound := by
    intro samples hgood t
    have hsample_pos : 0 < sqMagProb Ahat (samples t).1 (samples t).2 :=
      hgood t
    have hsample_ne :
        elementwiseTruncate tau A (samples t).1 (samples t).2 ≠ 0 := by
      simpa [Ahat] using
        entry_ne_zero_of_sqMagProb_pos Ahat (samples t).1 (samples t).2
          hsample_pos
    simpa [Ahat, L, Bound, truncatedDilationIncrementSquaresBoundedEvent] using
      finiteLoewnerLe_rectSelfAdjointDilation_square_elementwiseSampleResidualIncrement_truncated
        htau hs A (samples t) hsample_ne
  have hmono : P.eventProb Good ≤ P.eventProb Bound :=
    FiniteProbability.eventProb_mono P hsubset
  have hge : 1 ≤ P.eventProb Bound := by
    linarith
  have hle : P.eventProb Bound ≤ 1 :=
    FiniteProbability.eventProb_le_one P Bound
  have hbound_prob : P.eventProb Bound = 1 := le_antisymm hle hge
  simpa [P, Bound, Ahat, L] using hbound_prob













/-- Under the truncated squared-magnitude product law, the simultaneous
    bounded-operator, two-sided Loewner, and bounded-square side conditions for
    the self-adjoint dilation increments have probability one. -/
theorem sqMagTraceProbability_eventProb_truncatedDilationBernsteinBoundedEvent_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (truncatedDilationBernsteinBoundedEvent tau A
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hOp :
      P.eventProb (truncatedDilationIncrementsBoundedEvent tau A L) = 1 := by
    simpa [P, Ahat, L] using
      sqMagTraceProbability_eventProb_truncatedDilationIncrementsBoundedEvent_eq_one
        htau hs A hden
  have hLoewner :
      P.eventProb (truncatedDilationIncrementLoewnerBoundedEvent tau A L) = 1 := by
    simpa [P, Ahat, L] using
      sqMagTraceProbability_eventProb_truncatedDilationIncrementLoewnerBoundedEvent_eq_one
        htau hs A hden
  have hSq :
      P.eventProb (truncatedDilationIncrementSquaresBoundedEvent tau A L) = 1 := by
    simpa [P, Ahat, L] using
      sqMagTraceProbability_eventProb_truncatedDilationIncrementSquaresBoundedEvent_eq_one
        htau hs A hden
  have hOpLoewner :
      P.eventProb
        (truncatedDilationIncrementsBoundedEvent tau A L ∩
          truncatedDilationIncrementLoewnerBoundedEvent tau A L) = 1 :=
    FiniteProbability.eventProb_inter_eq_one_of_eq_one P
      (truncatedDilationIncrementsBoundedEvent tau A L)
      (truncatedDilationIncrementLoewnerBoundedEvent tau A L)
      hOp hLoewner
  simpa [P, Ahat, L, truncatedDilationBernsteinBoundedEvent] using
    FiniteProbability.eventProb_inter_eq_one_of_eq_one P
      (truncatedDilationIncrementsBoundedEvent tau A L ∩
        truncatedDilationIncrementLoewnerBoundedEvent tau A L)
      (truncatedDilationIncrementSquaresBoundedEvent tau A L)
      hOpLoewner hSq





































































/-- The one-sample residual increment has zero mean under the squared-magnitude
    one-step law. -/
theorem sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (i : Fin m) (j : Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleResidualIncrement s A sample i j) = 0 := by
  classical
  have hprob :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2) = 1 :=
    sqMagProb_sum_samples_eq_one A hden.ne'
  have hcontrib :=
    sqMagProb_sum_elementwiseSampleContribution_entry s A hs i j
  have hconst :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * (A i j / (s : ℝ))) =
        A i j / (s : ℝ) := by
    rw [← Finset.sum_mul, hprob, one_mul]
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleResidualIncrement s A sample i j)
        = (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * (A i j / (s : ℝ))) -
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              elementwiseSampleContribution s A sample i j) := by
            simp [elementwiseSampleResidualIncrement, mul_sub,
              Finset.sum_sub_distrib]
    _ = A i j / (s : ℝ) - A i j / (s : ℝ) := by
            rw [hconst, hcontrib]
    _ = 0 := by ring




















































































































































































































/-- Source-aligned one-step vector-action second-moment bound for the centered
    residual increment.  This avoids the Frobenius detour used by the older
    `m*n` bound. -/
theorem sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x)) ≤
      ((m : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        vecNorm2Sq x := by
  classical
  let p : ElementwiseSample m n → ℝ := fun sample =>
    sqMagProb A sample.1 sample.2
  let a : Fin m → ℝ := fun i => (1 / (s : ℝ)) * rectMatMulVec A x i
  let C : ElementwiseSample m n → Fin m → ℝ := fun sample i =>
    rectMatMulVec (elementwiseSampleContribution s A sample) x i
  have hprob : (∑ sample : ElementwiseSample m n, p sample) = 1 := by
    simpa [p] using sqMagProb_sum_samples_eq_one A hden.ne'
  have hCmean : ∀ i : Fin m,
      (∑ sample : ElementwiseSample m n, p sample * C sample i) = a i := by
    intro i
    simpa [p, C, a] using
      sqMagProb_sum_rectMatMulVec_elementwiseSampleContribution_eq
        s A hs x i
  have hres : ∀ sample : ElementwiseSample m n,
      rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x =
        fun i => a i - C sample i := by
    intro sample
    ext i
    unfold rectMatMulVec elementwiseSampleResidualIncrement a C
    calc
      (∑ j : Fin n,
        (A i j / (s : ℝ) -
            elementwiseSampleContribution s A sample i j) * x j)
          = (∑ j : Fin n, (A i j / (s : ℝ)) * x j) -
              ∑ j : Fin n,
                elementwiseSampleContribution s A sample i j * x j := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (1 / (s : ℝ)) * (∑ j : Fin n, A i j * x j) -
              ∑ j : Fin n,
                elementwiseSampleContribution s A sample i j * x j := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
  have hrow : ∀ i : Fin m,
      (∑ sample : ElementwiseSample m n,
        p sample * (a i - C sample i) ^ 2) ≤
        ∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2 := by
    intro i
    have hcross :
        (∑ sample : ElementwiseSample m n,
          p sample * (2 * a i * C sample i)) = 2 * a i ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n,
          p sample * (2 * a i * C sample i))
            = 2 * a i *
                (∑ sample : ElementwiseSample m n, p sample * C sample i) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = 2 * a i ^ 2 := by
                rw [hCmean i]
                ring
    have hconst :
        (∑ sample : ElementwiseSample m n, p sample * a i ^ 2) =
          a i ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n, p sample * a i ^ 2)
            = a i ^ 2 * (∑ sample : ElementwiseSample m n, p sample) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = a i ^ 2 := by
                rw [hprob]
                ring
    have hvariance :
        (∑ sample : ElementwiseSample m n,
          p sample * (a i - C sample i) ^ 2) =
          (∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2) -
            a i ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n,
          p sample * (a i - C sample i) ^ 2)
            = ∑ sample : ElementwiseSample m n,
                p sample * (C sample i ^ 2 -
                  2 * a i * C sample i + a i ^ 2) := by
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = (∑ sample : ElementwiseSample m n,
              p sample * C sample i ^ 2) -
            (∑ sample : ElementwiseSample m n,
              p sample * (2 * a i * C sample i)) +
            (∑ sample : ElementwiseSample m n, p sample * a i ^ 2) := by
                simp [mul_sub, mul_add, Finset.sum_sub_distrib,
                  Finset.sum_add_distrib]
        _ = (∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2) -
              a i ^ 2 := by
                rw [hcross, hconst]
                ring
    calc
      (∑ sample : ElementwiseSample m n,
        p sample * (a i - C sample i) ^ 2)
          = (∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2) -
              a i ^ 2 := hvariance
      _ ≤ ∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2 := by
          nlinarith [sq_nonneg (a i)]
  have hcontrib :=
    sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleContribution_le
      s A hs x
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x))
        = ∑ i : Fin m,
            ∑ sample : ElementwiseSample m n,
              p sample * (a i - C sample i) ^ 2 := by
            unfold vecNorm2Sq
            simp_rw [p, hres]
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin m,
          ∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact hrow i
    _ = ∑ sample : ElementwiseSample m n,
          p sample * vecNorm2Sq (C sample) := by
          unfold vecNorm2Sq
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro sample _
          rw [Finset.mul_sum]
    _ = ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            vecNorm2Sq
              (rectMatMulVec (elementwiseSampleContribution s A sample) x) := by
          apply Finset.sum_congr rfl
          intro sample _
          simp [p, C]
    _ ≤ ((m : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          vecNorm2Sq x := hcontrib















































































































































/-- Source-aligned one-step transpose-vector second-moment bound for the
    centered residual increment. -/
theorem sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (y : Fin m → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin m,
              elementwiseSampleResidualIncrement s A sample i j * y i)) ≤
      ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        vecNorm2Sq y := by
  classical
  let p : ElementwiseSample m n → ℝ := fun sample =>
    sqMagProb A sample.1 sample.2
  let a : Fin n → ℝ := fun j => (1 / (s : ℝ)) * ∑ i : Fin m, A i j * y i
  let C : ElementwiseSample m n → Fin n → ℝ := fun sample j =>
    ∑ i : Fin m, elementwiseSampleContribution s A sample i j * y i
  have hprob : (∑ sample : ElementwiseSample m n, p sample) = 1 := by
    simpa [p] using sqMagProb_sum_samples_eq_one A hden.ne'
  have hCmean : ∀ j : Fin n,
      (∑ sample : ElementwiseSample m n, p sample * C sample j) = a j := by
    intro j
    simpa [p, C, a] using
      sqMagProb_sum_transposeRectMatMulVec_elementwiseSampleContribution_eq
        s A hs y j
  have hres : ∀ sample : ElementwiseSample m n,
      (fun j : Fin n =>
        ∑ i : Fin m,
          elementwiseSampleResidualIncrement s A sample i j * y i) =
        fun j => a j - C sample j := by
    intro sample
    ext j
    unfold elementwiseSampleResidualIncrement a C
    calc
      (∑ i : Fin m,
        (A i j / (s : ℝ) -
            elementwiseSampleContribution s A sample i j) * y i)
          = (∑ i : Fin m, (A i j / (s : ℝ)) * y i) -
              ∑ i : Fin m,
                elementwiseSampleContribution s A sample i j * y i := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (1 / (s : ℝ)) * (∑ i : Fin m, A i j * y i) -
              ∑ i : Fin m,
                elementwiseSampleContribution s A sample i j * y i := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
  have hrow : ∀ j : Fin n,
      (∑ sample : ElementwiseSample m n,
        p sample * (a j - C sample j) ^ 2) ≤
        ∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2 := by
    intro j
    have hcross :
        (∑ sample : ElementwiseSample m n,
          p sample * (2 * a j * C sample j)) = 2 * a j ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n,
          p sample * (2 * a j * C sample j))
            = 2 * a j *
                (∑ sample : ElementwiseSample m n, p sample * C sample j) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = 2 * a j ^ 2 := by
                rw [hCmean j]
                ring
    have hconst :
        (∑ sample : ElementwiseSample m n, p sample * a j ^ 2) =
          a j ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n, p sample * a j ^ 2)
            = a j ^ 2 * (∑ sample : ElementwiseSample m n, p sample) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = a j ^ 2 := by
                rw [hprob]
                ring
    have hvariance :
        (∑ sample : ElementwiseSample m n,
          p sample * (a j - C sample j) ^ 2) =
          (∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2) -
            a j ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n,
          p sample * (a j - C sample j) ^ 2)
            = ∑ sample : ElementwiseSample m n,
                p sample * (C sample j ^ 2 -
                  2 * a j * C sample j + a j ^ 2) := by
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = (∑ sample : ElementwiseSample m n,
              p sample * C sample j ^ 2) -
            (∑ sample : ElementwiseSample m n,
              p sample * (2 * a j * C sample j)) +
            (∑ sample : ElementwiseSample m n, p sample * a j ^ 2) := by
                simp [mul_sub, mul_add, Finset.sum_sub_distrib,
                  Finset.sum_add_distrib]
        _ = (∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2) -
              a j ^ 2 := by
                rw [hcross, hconst]
                ring
    calc
      (∑ sample : ElementwiseSample m n,
        p sample * (a j - C sample j) ^ 2)
          = (∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2) -
              a j ^ 2 := hvariance
      _ ≤ ∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2 := by
          nlinarith [sq_nonneg (a j)]
  have hcontrib :=
    sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleContribution_le
      s A hs y
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin m,
              elementwiseSampleResidualIncrement s A sample i j * y i))
        = ∑ sample : ElementwiseSample m n,
            p sample * vecNorm2Sq (fun j : Fin n => a j - C sample j) := by
            apply Finset.sum_congr rfl
            intro sample _
            rw [hres sample]
    _ = ∑ j : Fin n,
            ∑ sample : ElementwiseSample m n,
              p sample * (a j - C sample j) ^ 2 := by
            unfold vecNorm2Sq
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
    _ ≤ ∑ j : Fin n,
          ∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          exact hrow j
    _ = ∑ sample : ElementwiseSample m n,
          p sample * vecNorm2Sq (C sample) := by
          unfold vecNorm2Sq
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro sample _
          rw [Finset.mul_sum]
    _ = ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            vecNorm2Sq
              (fun j : Fin n =>
                ∑ i : Fin m,
                  elementwiseSampleContribution s A sample i j * y i) := by
          apply Finset.sum_congr rfl
          intro sample _
          simp [p, C]
    _ ≤ ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          vecNorm2Sq y := hcontrib

/-- The one-step residual increment at a fixed entry has squared expectation
    at most `||A||_F^2 / s^2` under the squared-magnitude one-step law.  This
    is the scalar variance proxy needed before a matrix concentration theorem
    can be formalized for CACM equation (2). -/
theorem sqMagProb_sum_elementwiseSampleResidualIncrement_entry_sq_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (i : Fin m) (j : Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleResidualIncrement s A sample i j ^ 2) ≤
      frobNormSqRect A / (s : ℝ) ^ 2 := by
  classical
  let a : ℝ := A i j / (s : ℝ)
  let C : ElementwiseSample m n → ℝ := fun sample =>
    elementwiseSampleContribution s A sample i j
  have hprob :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2) = 1 :=
    sqMagProb_sum_samples_eq_one A hden.ne'
  have hCmean :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * C sample) = a := by
    simpa [C, a] using
      sqMagProb_sum_elementwiseSampleContribution_entry s A hs i j
  have hCsq :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * C sample ^ 2) ≤
        frobNormSqRect A / (s : ℝ) ^ 2 := by
    simpa [C] using
      sqMagProb_sum_elementwiseSampleContribution_entry_sq_le s A hs i j
  have hcross :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * (2 * a * C sample)) = 2 * a ^ 2 := by
    calc
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * (2 * a * C sample))
          = 2 * a *
              (∑ sample : ElementwiseSample m n,
                sqMagProb A sample.1 sample.2 * C sample) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro sample _
              ring
      _ = 2 * a ^ 2 := by
              rw [hCmean]
              ring
  have hconst_sq :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * a ^ 2) = a ^ 2 := by
    calc
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * a ^ 2)
          = a ^ 2 *
              (∑ sample : ElementwiseSample m n,
                sqMagProb A sample.1 sample.2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro sample _
              ring
      _ = a ^ 2 := by
              rw [hprob]
              ring
  have hres :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          elementwiseSampleResidualIncrement s A sample i j ^ 2) =
        (∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 * C sample ^ 2) - a ^ 2 := by
    calc
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          elementwiseSampleResidualIncrement s A sample i j ^ 2)
          = ∑ sample : ElementwiseSample m n,
              sqMagProb A sample.1 sample.2 *
                (a - C sample) ^ 2 := by
              apply Finset.sum_congr rfl
              intro sample _
              simp [elementwiseSampleResidualIncrement, C, a]
      _ = ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              (C sample ^ 2 - 2 * a * C sample + a ^ 2) := by
              apply Finset.sum_congr rfl
              intro sample _
              ring
      _ = (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * C sample ^ 2) -
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * (2 * a * C sample)) +
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * a ^ 2) := by
              simp [mul_sub, mul_add, Finset.sum_sub_distrib,
                Finset.sum_add_distrib]
      _ = (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * C sample ^ 2) - a ^ 2 := by
              rw [hcross, hconst_sq]
              ring
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleResidualIncrement s A sample i j ^ 2)
        = (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * C sample ^ 2) - a ^ 2 := hres
    _ ≤ ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 * C sample ^ 2 := by
          nlinarith [sq_nonneg a]
    _ ≤ frobNormSqRect A / (s : ℝ) ^ 2 := hCsq

/-- The one-step residual increment has a squared-Frobenius second-moment
    bound obtained by summing the entrywise variance proxy. -/
theorem sqMagProb_sum_elementwiseSampleResidualIncrement_frob_sq_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        frobNormSqRect (elementwiseSampleResidualIncrement s A sample)) ≤
      (m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2) := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        frobNormSqRect (elementwiseSampleResidualIncrement s A sample))
        = ∑ sample : ElementwiseSample m n, ∑ i : Fin m, ∑ j : Fin n,
            sqMagProb A sample.1 sample.2 *
              elementwiseSampleResidualIncrement s A sample i j ^ 2 := by
            unfold frobNormSqRect
            apply Finset.sum_congr rfl
            intro sample _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ i : Fin m, ∑ j : Fin n, ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            elementwiseSampleResidualIncrement s A sample i j ^ 2 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin m, ∑ j : Fin n,
          frobNormSqRect A / (s : ℝ) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            exact
              sqMagProb_sum_elementwiseSampleResidualIncrement_entry_sq_le
                s A hden hs i j
    _ = (m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2) := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
            ring

/-- The self-adjoint dilation of the one-step residual increment has a
    squared-Frobenius second-moment bound.  The factor `2` comes from the two
    off-diagonal blocks in the dilation. -/
theorem sqMagProb_sum_finiteFrobNormSq_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteFrobNormSq
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample))) ≤
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) := by
  classical
  have hFrob :=
    sqMagProb_sum_elementwiseSampleResidualIncrement_frob_sq_le
      s A hden hs
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteFrobNormSq
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)))
        = 2 *
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              frobNormSqRect
                (elementwiseSampleResidualIncrement s A sample)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro sample _
            rw [finiteFrobNormSq_rectSelfAdjointDilation]
            ring
    _ ≤ 2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hFrob (by linarith)

/-- Quadratic-form variance proxy for the one-step self-adjoint dilation
    residual increment.

This is the matrix-concentration object behind a Bernstein-style proof: for
every deterministic test vector, the expected quadratic form of the squared
dilation increment is controlled by the same explicit Frobenius proxy. -/
theorem sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin m ⊕ Fin n → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2))) *
        finiteVecNorm2Sq x := by
  classical
  have hFrob :=
    sqMagProb_sum_finiteFrobNormSq_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_le
      s A hden hs
  have hx_nonneg : 0 ≤ finiteVecNorm2Sq x := finiteVecNorm2Sq_nonneg x
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
        ≤ ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              (finiteFrobNormSq
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) *
                finiteVecNorm2Sq x) := by
            apply Finset.sum_le_sum
            intro sample _
            exact mul_le_mul_of_nonneg_left
              (finiteQuadraticForm_finiteMatMul_self_le_finiteFrobNormSq_mul_of_symmetric
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation_symmetric
                  (elementwiseSampleResidualIncrement s A sample)) x)
              (sqMagProb_nonneg A hden sample.1 sample.2)
    _ = (∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteFrobNormSq
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))) *
          finiteVecNorm2Sq x := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro sample _
            ring
    _ ≤ (2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2))) *
          finiteVecNorm2Sq x :=
            mul_le_mul_of_nonneg_right hFrob hx_nonneg

/-- Source-sharp square-matrix quadratic-form variance proxy for the one-step
    self-adjoint dilation residual increment.

This is the Drineas--Zouzias variance scale: for an `n × n` matrix, the
one-step dilation variance is controlled by
`n * ||A||_F^2 / s^2`, not by the older Frobenius-detour
`2 * n^2 * ||A||_F^2 / s^2` proxy. -/
theorem sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_square
    {n : ℕ} (s : ℕ) (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n ⊕ Fin n → ℝ) :
    (∑ sample : ElementwiseSample n n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x) ≤
      ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        finiteVecNorm2Sq x := by
  classical
  let y : Fin n → ℝ := fun i => x (Sum.inl i)
  let z : Fin n → ℝ := fun j => x (Sum.inr j)
  let C : ℝ := (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)
  have hx_decomp : sumBothVec y z = x := by
    ext a
    cases a <;> rfl
  have hqform : ∀ sample : ElementwiseSample n n,
      finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x =
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) z) +
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin n,
              elementwiseSampleResidualIncrement s A sample i j * y i) := by
    intro sample
    let M : Fin n → Fin n → ℝ :=
      elementwiseSampleResidualIncrement s A sample
    calc
      finiteQuadraticForm
          (finiteMatMul (rectSelfAdjointDilation M)
            (rectSelfAdjointDilation M)) x
          = finiteQuadraticForm
              (finiteMatMul (rectSelfAdjointDilation M)
                (rectSelfAdjointDilation M)) (sumBothVec y z) := by
              rw [hx_decomp]
      _ = finiteVecNorm2Sq
            (finiteMatVec (rectSelfAdjointDilation M) (sumBothVec y z)) := by
              rw [finiteQuadraticForm_finiteMatMul_self_of_symmetric
                (rectSelfAdjointDilation M)
                (rectSelfAdjointDilation_symmetric M)]
      _ = finiteVecNorm2Sq
            (sumBothVec (rectMatMulVec M z)
              (fun j : Fin n => ∑ i : Fin n, M i j * y i)) := by
              rw [finiteMatVec_rectSelfAdjointDilation_sumBothVec]
      _ = vecNorm2Sq (rectMatMulVec M z) +
            vecNorm2Sq
              (fun j : Fin n => ∑ i : Fin n, M i j * y i) := by
              rw [finiteVecNorm2Sq_sumBothVec]
              simp [finiteVecNorm2Sq_fin]
  have hright :=
    sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
      s A hden hs z
  have hleft :=
    sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
      s A hden hs y
  have hnorm :
      finiteVecNorm2Sq x = vecNorm2Sq y + vecNorm2Sq z := by
    rw [← hx_decomp, finiteVecNorm2Sq_sumBothVec]
    simp [finiteVecNorm2Sq_fin]
  calc
    (∑ sample : ElementwiseSample n n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
        = (∑ sample : ElementwiseSample n n,
            sqMagProb A sample.1 sample.2 *
              vecNorm2Sq
                (rectMatMulVec
                  (elementwiseSampleResidualIncrement s A sample) z)) +
          (∑ sample : ElementwiseSample n n,
            sqMagProb A sample.1 sample.2 *
              vecNorm2Sq
                (fun j : Fin n =>
                  ∑ i : Fin n,
                    elementwiseSampleResidualIncrement s A sample i j * y i)) := by
            simp_rw [hqform]
            simp [mul_add, Finset.sum_add_distrib]
    _ ≤ C * vecNorm2Sq z + C * vecNorm2Sq y := by
          exact add_le_add (by simpa [C] using hright) (by simpa [C] using hleft)
    _ = C * finiteVecNorm2Sq x := by
          rw [hnorm]
          ring
    _ = ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          finiteVecNorm2Sq x := by
          rfl

/-- Source-aligned rectangular quadratic-form variance proxy for the one-step
    self-adjoint dilation residual increment.

For an `m × n` matrix, the vector-action decomposition gives the variance
scale `max m n * ||A||_F^2 / s^2`, improving the older Frobenius-detour
`2mn * ||A||_F^2 / s^2` proxy without imposing truncation or a small-entry
floor. -/
theorem sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin m ⊕ Fin n → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)) *
        finiteVecNorm2Sq x := by
  classical
  let y : Fin m → ℝ := fun i => x (Sum.inl i)
  let z : Fin n → ℝ := fun j => x (Sum.inr j)
  let F : ℝ := frobNormSqRect A / (s : ℝ) ^ 2
  let C : ℝ := max (m : ℝ) (n : ℝ) * F
  have hF_nonneg : 0 ≤ F := by
    exact div_nonneg (frobNormSqRect_nonneg A) (sq_nonneg (s : ℝ))
  have hx_decomp : sumBothVec y z = x := by
    ext a
    cases a <;> rfl
  have hqform : ∀ sample : ElementwiseSample m n,
      finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x =
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) z) +
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin m,
              elementwiseSampleResidualIncrement s A sample i j * y i) := by
    intro sample
    let M : Fin m → Fin n → ℝ :=
      elementwiseSampleResidualIncrement s A sample
    calc
      finiteQuadraticForm
          (finiteMatMul (rectSelfAdjointDilation M)
            (rectSelfAdjointDilation M)) x
          = finiteQuadraticForm
              (finiteMatMul (rectSelfAdjointDilation M)
                (rectSelfAdjointDilation M)) (sumBothVec y z) := by
              rw [hx_decomp]
      _ = finiteVecNorm2Sq
            (finiteMatVec (rectSelfAdjointDilation M) (sumBothVec y z)) := by
              rw [finiteQuadraticForm_finiteMatMul_self_of_symmetric
                (rectSelfAdjointDilation M)
                (rectSelfAdjointDilation_symmetric M)]
      _ = finiteVecNorm2Sq
            (sumBothVec (rectMatMulVec M z)
              (fun j : Fin n => ∑ i : Fin m, M i j * y i)) := by
              rw [finiteMatVec_rectSelfAdjointDilation_sumBothVec]
      _ = vecNorm2Sq (rectMatMulVec M z) +
            vecNorm2Sq
              (fun j : Fin n => ∑ i : Fin m, M i j * y i) := by
              rw [finiteVecNorm2Sq_sumBothVec]
              simp [finiteVecNorm2Sq_fin]
  have hright :=
    sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
      s A hden hs z
  have hleft :=
    sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
      s A hden hs y
  have hrightC :
      ((m : ℝ) * F) * vecNorm2Sq z ≤ C * vecNorm2Sq z := by
    have hmC : (m : ℝ) * F ≤ C := by
      exact mul_le_mul_of_nonneg_right
        (le_max_left (m : ℝ) (n : ℝ)) hF_nonneg
    exact mul_le_mul_of_nonneg_right hmC (vecNorm2Sq_nonneg z)
  have hleftC :
      ((n : ℝ) * F) * vecNorm2Sq y ≤ C * vecNorm2Sq y := by
    have hnC : (n : ℝ) * F ≤ C := by
      exact mul_le_mul_of_nonneg_right
        (le_max_right (m : ℝ) (n : ℝ)) hF_nonneg
    exact mul_le_mul_of_nonneg_right hnC (vecNorm2Sq_nonneg y)
  have hnorm :
      finiteVecNorm2Sq x = vecNorm2Sq y + vecNorm2Sq z := by
    rw [← hx_decomp, finiteVecNorm2Sq_sumBothVec]
    simp [finiteVecNorm2Sq_fin]
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
        = (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              vecNorm2Sq
                (rectMatMulVec
                  (elementwiseSampleResidualIncrement s A sample) z)) +
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              vecNorm2Sq
                (fun j : Fin n =>
                  ∑ i : Fin m,
                    elementwiseSampleResidualIncrement s A sample i j * y i)) := by
            simp_rw [hqform]
            simp [mul_add, Finset.sum_add_distrib]
    _ ≤ ((m : ℝ) * F) * vecNorm2Sq z +
          ((n : ℝ) * F) * vecNorm2Sq y := by
          exact add_le_add
            (by simpa [F] using hright)
            (by simpa [F] using hleft)
    _ ≤ C * vecNorm2Sq z + C * vecNorm2Sq y := by
          exact add_le_add hrightC hleftC
    _ = C * finiteVecNorm2Sq x := by
          rw [hnorm]
          ring
    _ = (max (m : ℝ) (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2)) *
          finiteVecNorm2Sq x := by
          rfl

/-- Loewner-form one-step variance proxy for the squared self-adjoint dilation
    residual increment.

This is the same mathematical content as
`sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le`, packaged
as a matrix-order statement.  It is a matrix-concentration prerequisite, not a
tail theorem. -/
theorem sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b)
      (fun a b =>
        (2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2))) *
          finiteIdMatrix a b) := by
  classical
  intro x
  rw [finiteQuadraticForm_fintype_sum_smul,
    finiteQuadraticForm_smul_finiteIdMatrix]
  exact sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le
    s A hden hs x

/-- Source-sharp square-matrix Loewner variance proxy for the squared
    self-adjoint dilation residual increment. -/
theorem sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_square
    {n : ℕ} (s : ℕ) (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        ∑ sample : ElementwiseSample n n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b)
      (fun a b =>
        ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          finiteIdMatrix a b) := by
  classical
  intro x
  rw [finiteQuadraticForm_fintype_sum_smul,
    finiteQuadraticForm_smul_finiteIdMatrix]
  exact
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_square
      s A hden hs x

/-- Source-aligned rectangular Loewner variance proxy for the squared
    self-adjoint dilation residual increment. -/
theorem sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b)
      (fun a b =>
        (max (m : ℝ) (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2)) *
          finiteIdMatrix a b) := by
  classical
  intro x
  rw [finiteQuadraticForm_fintype_sum_smul,
    finiteQuadraticForm_smul_finiteIdMatrix]
  exact
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
      s A hden hs x























/-- Summed quadratic-form variance proxy over the `s` independent one-step
    dilation increments.  This is the deterministic variance-parameter shape
    used by a future matrix Bernstein theorem: the per-step proxy above sums
    to an order `||A||_F^2 / s` quantity. -/
theorem sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : Fin m ⊕ Fin n → ℝ) :
    (∑ _t : Fin s,
      ∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))) x) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ)))) *
        finiteVecNorm2Sq x := by
  classical
  have hstep :=
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le
      s A hden (ne_of_gt hs) x
  calc
    (∑ _t : Fin s,
      ∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))) x)
        ≤ ∑ _t : Fin s,
            (2 * ((m : ℝ) * (n : ℝ) *
              (frobNormSqRect A / (s : ℝ) ^ 2))) *
              finiteVecNorm2Sq x := by
            apply Finset.sum_le_sum
            intro t _
            exact hstep
    _ = (s : ℝ) *
          ((2 * ((m : ℝ) * (n : ℝ) *
            (frobNormSqRect A / (s : ℝ) ^ 2))) *
            finiteVecNorm2Sq x) := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
    _ = (2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ)))) *
          finiteVecNorm2Sq x := by
            field_simp [ne_of_gt hs]

/-- Source-aligned rectangular summed quadratic-form variance proxy over the
    `s` independent one-step dilation increments. -/
theorem sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : Fin m ⊕ Fin n → ℝ) :
    (∑ _t : Fin s,
      ∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))) x) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ))) *
        finiteVecNorm2Sq x := by
  classical
  have hstep :=
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
      s A hden (ne_of_gt hs) x
  calc
    (∑ _t : Fin s,
      ∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))) x)
        ≤ ∑ _t : Fin s,
            (max (m : ℝ) (n : ℝ) *
              (frobNormSqRect A / (s : ℝ) ^ 2)) *
              finiteVecNorm2Sq x := by
            apply Finset.sum_le_sum
            intro t _
            exact hstep
    _ = (s : ℝ) *
          ((max (m : ℝ) (n : ℝ) *
            (frobNormSqRect A / (s : ℝ) ^ 2)) *
            finiteVecNorm2Sq x) := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
    _ = (max (m : ℝ) (n : ℝ) *
          (frobNormSqRect A / (s : ℝ))) *
          finiteVecNorm2Sq x := by
            field_simp [ne_of_gt hs]

/-- Summed Loewner-form variance proxy over the `s` independent one-step
    self-adjoint dilation residual increments.  This is the variance matrix
    shape expected by a future matrix Bernstein theorem. -/
theorem sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteLoewnerLe
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b)
      (fun a b =>
        (2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ)))) *
          finiteIdMatrix a b) := by
  classical
  intro x
  have hrewrite :
      finiteQuadraticForm
        (fun a b =>
          ∑ _t : Fin s,
            ∑ sample : ElementwiseSample m n,
              sqMagProb A sample.1 sample.2 *
                finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample)) a b) x =
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteQuadraticForm
                (finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))) x := by
    rw [finiteQuadraticForm_fintype_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [finiteQuadraticForm_fintype_sum_smul]
  rw [hrewrite, finiteQuadraticForm_smul_finiteIdMatrix]
  exact sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le
    A hden hs x

/-- Source-aligned rectangular summed Loewner variance proxy over the `s`
    independent one-step self-adjoint dilation residual increments. -/
theorem sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteLoewnerLe
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b)
      (fun a b =>
        (max (m : ℝ) (n : ℝ) *
          (frobNormSqRect A / (s : ℝ))) *
          finiteIdMatrix a b) := by
  classical
  intro x
  have hrewrite :
      finiteQuadraticForm
        (fun a b =>
          ∑ _t : Fin s,
            ∑ sample : ElementwiseSample m n,
              sqMagProb A sample.1 sample.2 *
                finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample)) a b) x =
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteQuadraticForm
                (finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))) x := by
    rw [finiteQuadraticForm_fintype_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [finiteQuadraticForm_fintype_sum_smul]
  rw [hrewrite, finiteQuadraticForm_smul_finiteIdMatrix]
  exact
    sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
      A hden hs x





















/-- Product-law expectation form of the one-step self-adjoint dilation square
    variance proxy at a fixed trace coordinate.

This is the bridge from the one-step `sqMagProb` variance calculation to the
canonical independent trace probability space. -/
theorem sqMagTraceProbability_expectationReal_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (t : Fin s) (x : Fin m ⊕ Fin n → ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t)))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t)))) x) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2))) *
        finiteVecNorm2Sq x := by
  classical
  have hstep :=
    sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
  rw [hstep]
  exact
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le
      s A hden hs x

/-- Product-law expectation form of the source-aligned rectangular one-step
    self-adjoint dilation square variance proxy. -/
theorem sqMagTraceProbability_expectationReal_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (t : Fin s) (x : Fin m ⊕ Fin n → ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t)))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t)))) x) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)) *
        finiteVecNorm2Sq x := by
  classical
  have hstep :=
    sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
  rw [hstep]
  exact
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
      s A hden hs x

/-- Product-law expectation form of the summed self-adjoint dilation variance
    proxy.  The left side is the trace-law expectation of the sum of the
    quadratic forms of the squared one-step dilation increments. -/
theorem sqMagTraceProbability_expectationReal_sum_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : Fin m ⊕ Fin n → ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        ∑ t : Fin s,
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A (samples t)))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A (samples t)))) x) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ)))) *
        finiteVecNorm2Sq x := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  have hrewrite :
      P.expectationReal
        (fun samples : ElementwiseTrace m n s =>
          ∑ t : Fin s,
            finiteQuadraticForm
              (finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))) x) =
        ∑ t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteQuadraticForm
                (finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))) x := by
    rw [FiniteProbability.expectationReal_sum]
    apply Finset.sum_congr rfl
    intro t _
    exact sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
  rw [hrewrite]
  exact sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le
    A hden hs x

/-- Product-law expectation form of the source-aligned rectangular summed
    self-adjoint dilation variance proxy. -/
theorem sqMagTraceProbability_expectationReal_sum_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : Fin m ⊕ Fin n → ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        ∑ t : Fin s,
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A (samples t)))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A (samples t)))) x) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ))) *
        finiteVecNorm2Sq x := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  have hrewrite :
      P.expectationReal
        (fun samples : ElementwiseTrace m n s =>
          ∑ t : Fin s,
            finiteQuadraticForm
              (finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))) x) =
        ∑ t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteQuadraticForm
                (finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))) x := by
    rw [FiniteProbability.expectationReal_sum]
    apply Finset.sum_congr rfl
    intro t _
    exact sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
  rw [hrewrite]
  exact
    sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
      A hden hs x

/-- Loewner-form trace-law expectation of the summed squared dilation
    increments.  This packages the product-law expectation adapter in the
    exact matrix order shape needed by a future Bernstein theorem. -/
theorem sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_loewnerLe_scalar_id
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteLoewnerLe
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b))
      (fun a b =>
        (2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ)))) *
          finiteIdMatrix a b) := by
  classical
  have hmatrix :
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b)) =
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) := by
    ext a b
    apply Finset.sum_congr rfl
    intro t _
    exact sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteMatMul
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample))
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) a b)
  rw [hmatrix]
  exact
    sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id
      A hden hs

/-- Source-aligned rectangular Loewner-form trace-law expectation of the summed
    squared dilation increments. -/
theorem sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteLoewnerLe
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b))
      (fun a b =>
        (max (m : ℝ) (n : ℝ) *
          (frobNormSqRect A / (s : ℝ))) *
          finiteIdMatrix a b) := by
  classical
  have hmatrix :
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b)) =
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) := by
    ext a b
    apply Finset.sum_congr rfl
    intro t _
    exact sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteMatMul
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample))
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) a b)
  rw [hmatrix]
  exact
    sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
      A hden hs

/-- The trace-law expectation of the summed squared dilation increments is
    positive semidefinite. -/
theorem sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_psd
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) :
    finitePSD
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b)) := by
  classical
  have hmatrix :
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b)) =
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) := by
    ext a b
    apply Finset.sum_congr rfl
    intro t _
    exact sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteMatMul
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample))
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) a b)
  rw [hmatrix]
  exact sqMagProb_sum_steps_rectSelfAdjointDilation_square_psd A hden

/-- Trace form of the one-step self-adjoint dilation variance proxy.  This is
    obtained from the Loewner proxy by trace monotonicity, and is one of the
    scalar quantities used by trace-moment and matrix-Bernstein routes. -/
theorem sqMagProb_sum_finiteTrace_rectSelfAdjointDilation_square_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    finiteTrace
      (fun a b =>
        ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2))) *
        ((m : ℝ) + (n : ℝ)) := by
  classical
  have hmono :=
    finiteTrace_mono_of_finiteLoewnerLe
      (sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id
        s A hden hs)
  rw [finiteTrace_smul_finiteIdMatrix] at hmono
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using hmono

/-- Trace form of the source-aligned rectangular one-step self-adjoint dilation
    variance proxy. -/
theorem sqMagProb_sum_finiteTrace_rectSelfAdjointDilation_square_le_sharp_rect
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    finiteTrace
      (fun a b =>
        ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)) *
        ((m : ℝ) + (n : ℝ)) := by
  classical
  have hmono :=
    finiteTrace_mono_of_finiteLoewnerLe
      (sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
        s A hden hs)
  rw [finiteTrace_smul_finiteIdMatrix] at hmono
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using hmono

/-- Trace form of the summed self-adjoint dilation variance proxy.  After `s`
    independent samples the scalar variance trace is order
    `||A||_F^2 / s`, with the explicit dilation dimension `m + n`. -/
theorem sqMagProb_sum_steps_finiteTrace_rectSelfAdjointDilation_square_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteTrace
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ)))) *
        ((m : ℝ) + (n : ℝ)) := by
  classical
  have hmono :=
    finiteTrace_mono_of_finiteLoewnerLe
      (sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id
        A hden hs)
  rw [finiteTrace_smul_finiteIdMatrix] at hmono
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using hmono

/-- Trace form of the source-aligned rectangular summed self-adjoint dilation
    variance proxy. -/
theorem sqMagProb_sum_steps_finiteTrace_rectSelfAdjointDilation_square_le_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteTrace
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ))) *
        ((m : ℝ) + (n : ℝ)) := by
  classical
  have hmono :=
    finiteTrace_mono_of_finiteLoewnerLe
      (sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
        A hden hs)
  rw [finiteTrace_smul_finiteIdMatrix] at hmono
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using hmono

/-- Applying a one-step residual increment to a fixed vector has squared
    second moment controlled by the Frobenius variance proxy. -/
theorem sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x)) ≤
      ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        vecNorm2Sq x := by
  classical
  have hFrob :=
    sqMagProb_sum_elementwiseSampleResidualIncrement_frob_sq_le
      s A hden hs
  have hx_nonneg : 0 ≤ vecNorm2Sq x := vecNorm2Sq_nonneg x
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x))
        ≤ ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              (frobNormSqRect (elementwiseSampleResidualIncrement s A sample) *
                vecNorm2Sq x) := by
            apply Finset.sum_le_sum
            intro sample _
            exact mul_le_mul_of_nonneg_left
              (vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_mul
                (elementwiseSampleResidualIncrement s A sample) x)
              (sqMagProb_nonneg A hden sample.1 sample.2)
    _ = (∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            frobNormSqRect (elementwiseSampleResidualIncrement s A sample)) *
          vecNorm2Sq x := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro sample _
            ring
    _ ≤ ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2)) *
          vecNorm2Sq x :=
            mul_le_mul_of_nonneg_right hFrob hx_nonneg

/-- The exact Algorithm 1 residual is entrywise mean-zero under the canonical
    independent squared-magnitude trace law. -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_eq_zero
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (i : Fin m) (j : Fin n) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples => elementwiseTraceResidual s A samples i j) = 0 := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  have hsketch :
      P.expectationReal
        (fun samples : ElementwiseTrace m n s =>
          elementwiseTraceSketch s A (fun _ _ => 0) samples i j) =
        A i j :=
    sqMagTraceProbability_expectationReal_elementwiseTraceSketch_entry
      (steps := s) s A hden i j rfl hs
  calc
    P.expectationReal
      (fun samples : ElementwiseTrace m n s =>
        elementwiseTraceResidual s A samples i j)
        = P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              A i j -
                elementwiseTraceSketch s A (fun _ _ => 0) samples i j) := by
            rfl
    _ = P.expectationReal (fun _samples : ElementwiseTrace m n s => A i j) -
          P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              elementwiseTraceSketch s A (fun _ _ => 0) samples i j) := by
            rw [FiniteProbability.expectationReal_sub]
    _ = A i j - A i j := by
            rw [FiniteProbability.expectationReal_const, hsketch]
    _ = 0 := by ring























































































































/-- Algorithm 1 trace-MGF domination instantiated with the self-adjoint
    dilation residual increments.

This is the source-aligned trace-MGF target that the scalar
matrix-CGF/log-MGF Bernstein step must bound next.  It does not assume a CGF
bound; it is the no-hidden-Lieb iid trace-MGF theorem specialized to
\(\theta D(Z_t)\), where \(D(\cdot)\) is the self-adjoint dilation. -/
theorem sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_sum_rectSelfAdjointDilation_sampleResidualIncrement_le
    {m n s : ℕ} [Fintype (Fin m ⊕ Fin n)] [DecidableEq (Fin m ⊕ Fin n)]
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (theta : ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        finiteTrace
          (finiteMatrixExp
            (fun a b : Fin m ⊕ Fin n =>
              ∑ t : Fin s,
                theta *
                  rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A (samples t)) a b))) ≤
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) A hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) := by
  classical
  let zeroMat : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ := fun _ _ => 0
  let X : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample a b =>
      theta *
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b
  have hzero : IsSymmetricFiniteMatrix zeroMat := by
    intro a b
    rfl
  have hX : ∀ sample, IsSymmetricFiniteMatrix (X sample) := by
    intro sample
    exact
      rectSelfAdjointDilation_elementwiseSampleResidualIncrement_smul_symmetric
        A sample theta
  have h :=
    sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
      (steps := s) A hden (H := zeroMat) hzero (X := X) hX
  simpa [zeroMat, X, sqMagTraceProbabilityFiniteRealTraceMGFLogBound] using h

/-- Algorithm 1 trace-MGF domination for the actual self-adjoint dilation of
    the full exact residual.

The left side is now the finite-real trace exponential of
\(\theta D(A-\widetilde A)\).  The right side is the same logarithmic
one-sample mean increment produced by the no-hidden-Lieb trace-MGF iteration.
The remaining red-bottleneck theorem is to bound this logarithmic increment by
a scalar/variance proxy and then apply the eigenvalue Markov interface. -/
theorem sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le
    {m n s : ℕ} [Fintype (Fin m ⊕ Fin n)] [DecidableEq (Fin m ⊕ Fin n)]
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) (theta : ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        finiteTrace
          (finiteMatrixExp
            (fun a b : Fin m ⊕ Fin n =>
              theta *
                rectSelfAdjointDilation
                  (elementwiseTraceResidual s A samples) a b))) ≤
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) A hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  have hleft :
      P.expectationReal
        (fun samples =>
          finiteTrace
            (finiteMatrixExp
              (fun a b : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s A samples) a b))) =
      P.expectationReal
        (fun samples =>
          finiteTrace
            (finiteMatrixExp
              (fun a b : Fin m ⊕ Fin n =>
                ∑ t : Fin s,
                  theta *
                    rectSelfAdjointDilation
                      (elementwiseSampleResidualIncrement s A (samples t)) a b))) := by
    unfold P FiniteProbability.expectationReal
    apply Finset.sum_congr rfl
    intro samples _
    apply congrArg (fun z : ℝ => (sqMagTraceProbability A hden).prob samples * z)
    apply congrArg
      (fun M : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ =>
        finiteTrace (finiteMatrixExp M))
    funext a b
    rw [rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
      A samples hs a b]
    rw [Finset.mul_sum]
  rw [hleft]
  exact
    sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_sum_rectSelfAdjointDilation_sampleResidualIncrement_le
      A hden theta

/-- Algorithm 1 upper-tail eigenvalue Markov step after the no-hidden-Lieb
    trace-MGF iteration has been specialized to the actual self-adjoint
    dilation residual.

This is the final trace-exponential-to-largest-eigenvalue interface for the
scaled residual `theta * D(A - Atilde)`.  It does not prove the scalar
matrix-CGF/Bernstein estimate for the logarithmic one-step mean increment; that
quantity remains exposed on the right-hand side. -/
theorem sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_ge_le
    {m n s : ℕ} [Fintype (Fin m ⊕ Fin n)] [DecidableEq (Fin m ⊕ Fin n)]
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (theta T : ℝ) :
    (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∃ a : Fin m ⊕ Fin n,
            T ≤ finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s A samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s A samples) b c))
              a} ≤
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta *
              rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let M : ElementwiseTrace m n s → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun samples b c =>
      theta *
        rectSelfAdjointDilation
          (elementwiseTraceResidual s A samples) b c
  have hM : ∀ samples, IsSymmetricFiniteMatrix (M samples) := by
    intro samples b c
    exact congrArg (fun x => theta * x)
      (rectSelfAdjointDilation_symmetric
        (elementwiseTraceResidual s A samples) b c)
  have hTrace :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (M samples))) ≤
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta *
              rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) := by
    simpa [P, M] using
      sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le
        A hden hs theta
  simpa [P, M] using
    FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_trace_bound
      (P := P) (M := M) hM T
      (sqMagTraceProbabilityFiniteRealTraceMGFLogBound
        (steps := s) A hden
        (fun _a _b : Fin m ⊕ Fin n => 0)
        (fun sample a b =>
          theta *
            rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample) a b))
      hTrace

/-- Two-sided eigenvalue Markov step for the scaled Algorithm 1 dilation
    residual.

The positive trace-MGF bound is supplied by the trace-MGF instantiation with
`theta`; the negative trace-MGF bound is the same theorem with `-theta`.
The remaining open source obligation is still the scalar
matrix-CGF/Bernstein--Khintchine bound that turns the two logarithmic
trace-MGF quantities into explicit CACM equation (2) constants. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge
    {m n s : ℕ} [Fintype (Fin m ⊕ Fin n)] [DecidableEq (Fin m ⊕ Fin n)]
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (theta T : ℝ) :
    1 -
        (Real.exp (-T) *
            sqMagTraceProbabilityFiniteRealTraceMGFLogBound
              (steps := s) A hden
              (fun _a _b : Fin m ⊕ Fin n => 0)
              (fun sample a b =>
                (-theta) *
                  rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample) a b) +
          Real.exp (-T) *
            sqMagTraceProbabilityFiniteRealTraceMGFLogBound
              (steps := s) A hden
              (fun _a _b : Fin m ⊕ Fin n => 0)
              (fun sample a b =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample) a b)) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s A samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s A samples) b c))
              a| < T} := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let M : ElementwiseTrace m n s → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun samples b c =>
      theta *
        rectSelfAdjointDilation
          (elementwiseTraceResidual s A samples) b c
  have hM : ∀ samples, IsSymmetricFiniteMatrix (M samples) := by
    intro samples b c
    exact congrArg (fun x => theta * x)
      (rectSelfAdjointDilation_symmetric
        (elementwiseTraceResidual s A samples) b c)
  have hTracePos :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (M samples))) ≤
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta *
              rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) := by
    simpa [P, M] using
      sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le
        A hden hs theta
  have hTraceNeg :
      P.expectationReal
          (fun samples => finiteTrace
            (finiteMatrixExp (fun b c : Fin m ⊕ Fin n => -M samples b c))) ≤
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            (-theta) *
              rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) := by
    simpa [P, M, neg_mul] using
      sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le
        A hden hs (-theta)
  simpa [P, M] using
    FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound_add
      (P := P) (M := M) hM T
      (sqMagTraceProbabilityFiniteRealTraceMGFLogBound
        (steps := s) A hden
        (fun _a _b : Fin m ⊕ Fin n => 0)
        (fun sample a b =>
          (-theta) *
            rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample) a b))
      (sqMagTraceProbabilityFiniteRealTraceMGFLogBound
        (steps := s) A hden
        (fun _a _b : Fin m ⊕ Fin n => 0)
        (fun sample a b =>
          theta *
            rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample) a b))
      hTraceNeg hTracePos

/-- Finite-family scalar MGF tail for quadratic forms of the Algorithm 1
    self-adjoint dilation residual.

The theorem consumes one-step scalar MGF bounds for a supplied finite family of
test vectors and proves simultaneous control of the corresponding residual
quadratic forms under the canonical product trace law.  It is a concentration
foundation for cover or trace-exponential routes; it is not yet the CACM
equation (2) matrix Bernstein/Khintchine theorem. -/
theorem sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hs : (s : ℝ) ≠ 0)
    (z : ι → Fin m ⊕ Fin n → ℝ)
    (T psi lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hmgf : ∀ a,
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          Real.exp
            (lam a *
              finiteQuadraticForm
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) (z a))) ≤
        Real.exp (psi a)) :
    1 - ∑ a : ι, Real.exp ((s : ℝ) * psi a - lam a * T a) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : ι,
            finiteQuadraticForm
              (rectSelfAdjointDilation
                (elementwiseTraceResidual s A samples)) (z a) ≤ T a} := by
  classical
  let f : ι → ElementwiseSample m n → ℝ := fun a sample =>
    finiteQuadraticForm
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)) (z a)
  have htail :=
    sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
      (steps := s) A hden f T psi lam hlam
      (by
        intro a
        simpa [f] using hmgf a)
  have hset :
      {samples : ElementwiseTrace m n s |
        ∀ a : ι, ∑ t : Fin s, f a (samples t) ≤ T a} =
      {samples : ElementwiseTrace m n s |
        ∀ a : ι,
          finiteQuadraticForm
            (rectSelfAdjointDilation
              (elementwiseTraceResidual s A samples)) (z a) ≤ T a} := by
    ext samples
    constructor
    · intro h a
      rw [
        finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
          A samples hs (z a)]
      simpa [f] using h a
    · intro h a
      change
        (∑ t : Fin s,
          finiteQuadraticForm
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t))) (z a)) ≤
          T a
      rw [←
        finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
          A samples hs (z a)]
      exact h a
  simpa [hset] using htail

/-- Finite-family quadratic-form tail from pointwise one-step bounds.

This removes the explicit one-step MGF hypothesis from the previous theorem
when each supplied test-vector quadratic form has a proved pointwise upper
bound.  The resulting estimate is generally too weak to be the CACM equation
(2) matrix Bernstein theorem, but it is a fully proved finite-test support
layer. -/
theorem sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_pointwise_bound
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hs : (s : ℝ) ≠ 0)
    (z : ι → Fin m ⊕ Fin n → ℝ)
    (T B lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hbound : ∀ a sample,
      finiteQuadraticForm
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample)) (z a) ≤ B a) :
    1 - ∑ a : ι, Real.exp ((s : ℝ) * (lam a * B a) - lam a * T a) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : ι,
            finiteQuadraticForm
              (rectSelfAdjointDilation
                (elementwiseTraceResidual s A samples)) (z a) ≤ T a} := by
  classical
  exact
    sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
      A hden hs z T (fun a => lam a * B a) lam hlam
      (by
        intro a
        simpa using
          sqMagProb_sum_exp_stepFunction_le_exp_of_forall_le
            A hden
            (fun sample : ElementwiseSample m n =>
              finiteQuadraticForm
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) (z a))
            (le_of_lt (hlam a)) (hbound a))

/-- Finite-family quadratic-form tail from support-aware pointwise one-step
    bounds.

This is the same finite-test theorem as
`..._of_pointwise_bound`, but the one-step bound is only required on samples
with positive squared-magnitude probability.  It is designed for truncated
sampling laws where zero-mass samples need not satisfy retained-entry side
conditions. -/
theorem sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_support_pointwise_bound
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hs : (s : ℝ) ≠ 0)
    (z : ι → Fin m ⊕ Fin n → ℝ)
    (T B lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hbound : ∀ a sample,
      0 < sqMagProb A sample.1 sample.2 →
        finiteQuadraticForm
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) (z a) ≤ B a) :
    1 - ∑ a : ι, Real.exp ((s : ℝ) * (lam a * B a) - lam a * T a) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : ι,
            finiteQuadraticForm
              (rectSelfAdjointDilation
                (elementwiseTraceResidual s A samples)) (z a) ≤ T a} := by
  classical
  let f : ι → ElementwiseSample m n → ℝ := fun a sample =>
    finiteQuadraticForm
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)) (z a)
  have htail :=
    sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_support_pointwise_bound
      (steps := s) A hden f T B lam hlam
      (by
        intro a sample hsample
        simpa [f] using hbound a sample hsample)
  have hset :
      {samples : ElementwiseTrace m n s |
        ∀ a : ι, ∑ t : Fin s, f a (samples t) ≤ T a} =
      {samples : ElementwiseTrace m n s |
        ∀ a : ι,
          finiteQuadraticForm
            (rectSelfAdjointDilation
              (elementwiseTraceResidual s A samples)) (z a) ≤ T a} := by
    ext samples
    constructor
    · intro h a
      rw [
        finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
          A samples hs (z a)]
      simpa [f] using h a
    · intro h a
      change
        (∑ t : Fin s,
          finiteQuadraticForm
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t))) (z a)) ≤
          T a
      rw [←
        finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
          A samples hs (z a)]
      exact h a
  simpa [hset] using htail

/-- Truncated Algorithm 1 finite-family quadratic-form tail from the retained
    one-step dilation bound.

Positive probability under the truncated squared-magnitude law implies the
sampled entry is retained, so the one-step operator bound applies without any
extra support hypothesis.  This is still a finite-test scalar support theorem,
not the trace-exponential or matrix Bernstein proof of CACM equation (2). -/
theorem sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_truncatedTraceResidual_le_ge_one_sub_sum_exp_of_support_bound
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (z : ι → Fin m ⊕ Fin n → ℝ)
    (T lam : ι → ℝ) (hlam : ∀ a, 0 < lam a) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau))
    1 -
        ∑ a : ι,
          Real.exp ((s : ℝ) * (lam a * (L * finiteVecNorm2Sq (z a))) -
            lam a * T a) ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : ι,
            finiteQuadraticForm
              (rectSelfAdjointDilation
                (elementwiseTraceResidual s Ahat samples)) (z a) ≤ T a} := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have htail :=
    sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_support_pointwise_bound
      (A := Ahat) hden hsne z T (fun a => L * finiteVecNorm2Sq (z a))
      lam hlam
      (by
        intro a sample hprob
        have hsample_ne :
            elementwiseTruncate tau A sample.1 sample.2 ≠ 0 := by
          simpa [Ahat] using
            entry_ne_zero_of_sqMagProb_pos Ahat sample.1 sample.2 hprob
        simpa [Ahat, L] using
          finiteQuadraticForm_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_le
            htau hs A sample hsample_ne (z a))
  simpa [Ahat, L] using htail

/-- The one-sample residual increment has zero mean after applying it to a
    fixed vector. -/
theorem sqMagProb_sum_rectMatMulVec_elementwiseSampleResidualIncrement_eq_zero
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) (i : Fin m) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x i) = 0 := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x i)
        = ∑ sample : ElementwiseSample m n, ∑ j : Fin n,
            sqMagProb A sample.1 sample.2 *
              (elementwiseSampleResidualIncrement s A sample i j * x j) := by
            apply Finset.sum_congr rfl
            intro sample _
            rw [rectMatMulVec, Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ sample : ElementwiseSample m n,
            (sqMagProb A sample.1 sample.2 *
              elementwiseSampleResidualIncrement s A sample i j) * x j := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro sample _
            ring
    _ = ∑ j : Fin n,
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              elementwiseSampleResidualIncrement s A sample i j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ = 0 := by
            simp [sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero
              s A hden hs]

/-- The one-step self-adjoint dilation residual increment has zero mean in
    every square-matrix entry. -/
theorem sqMagProb_sum_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_eq_zero
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (a b : Fin m ⊕ Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b) = 0 := by
  cases a with
  | inl i =>
      cases b with
      | inl k =>
          simp [rectSelfAdjointDilation]
      | inr j =>
          simpa [rectSelfAdjointDilation] using
            sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero
              s A hden hs i j
  | inr j =>
      cases b with
      | inl i =>
          simpa [rectSelfAdjointDilation] using
            sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero
              s A hden hs i j
      | inr k =>
          simp [rectSelfAdjointDilation]

/-- One-sample C⋆-matrix zero mean for the self-adjoint dilation residual
increment under the squared-magnitude sampling law. -/
theorem sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (sqMagSampleProbability A hden).expectationCStarMatrix
      (fun sample : ElementwiseSample m n =>
        finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample))) = 0 := by
  classical
  rw [FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix]
  ext a b
  change
    ((sqMagSampleProbability A hden).expectationReal
      (fun sample : ElementwiseSample m n =>
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b) : ℂ) = 0
  have hsum :=
    sqMagProb_sum_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_eq_zero
      s A hden hs a b
  simpa [FiniteProbability.expectationReal, sqMagSampleProbability] using
    congrArg (fun x : ℝ => (x : ℂ)) hsum

/-- C⋆-matrix Loewner variance proxy for the one-sample self-adjoint dilation
residual increment under the squared-magnitude sampling law.

This is the complex C⋆ form consumed by the one-sample log-CGF theorem.  It is
obtained from the repository's finite-real Loewner variance proxy and the
finite-real-to-C⋆ embedding. -/
theorem sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (sqMagSampleProbability A hden).expectationCStarMatrix
      (fun sample : ElementwiseSample m n =>
        (finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) *
          finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) :
        CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
      ((2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2))) : ℂ) •
        (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
  classical
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)
  let V : ℝ := 2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2))
  have hprod :
      (fun sample : ElementwiseSample m n =>
        (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
      (fun sample : ElementwiseSample m n =>
        finiteComplexCStarMatrix (finiteMatMul (D sample) (D sample))) := by
    funext sample
    rw [finiteComplexCStarMatrix_mul]
  rw [hprod]
  rw [FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix]
  let M : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ := fun a b =>
    ∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 * finiteMatMul (D sample) (D sample) a b
  have hM_eq :
      (fun a b : Fin m ⊕ Fin n =>
          (sqMagSampleProbability A hden).expectationReal
            (fun sample : ElementwiseSample m n =>
              finiteMatMul (D sample) (D sample) a b)) = M := by
    ext a b
    simp [M, FiniteProbability.expectationReal, sqMagSampleProbability]
  rw [hM_eq]
  have hMsym : IsSymmetricFiniteMatrix M := by
    dsimp [M]
    exact IsSymmetricFiniteMatrix.sum_smul
      (fun sample : ElementwiseSample m n => sqMagProb A sample.1 sample.2)
      (fun sample : ElementwiseSample m n => finiteMatMul (D sample) (D sample))
      (fun sample =>
        finiteMatMul_self_symmetric_of_symmetric (D sample)
          (rectSelfAdjointDilation_symmetric
            (elementwiseSampleResidualIncrement s A sample)))
  have hNsym :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric V
  have hLe :
      finiteLoewnerLe M
        (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) := by
    dsimp [M, V, D]
    exact sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id
      s A hden hs
  have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M
    (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) hMsym hNsym hLe
  simpa [V, D, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC

/-- Source-sharp square-matrix C⋆ variance proxy for the one-sample
    self-adjoint dilation residual increment. -/
theorem sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square
    {n s : ℕ} (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (sqMagSampleProbability A hden).expectationCStarMatrix
      (fun sample : ElementwiseSample n n =>
        (finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) *
          finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) :
        CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) ≤
      (((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) : ℂ) •
        (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
  classical
  let D : ElementwiseSample n n → Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)
  let V : ℝ := (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)
  have hprod :
      (fun sample : ElementwiseSample n n =>
        (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) =
      (fun sample : ElementwiseSample n n =>
        finiteComplexCStarMatrix (finiteMatMul (D sample) (D sample))) := by
    funext sample
    rw [finiteComplexCStarMatrix_mul]
  rw [hprod]
  rw [FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix]
  let M : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ := fun a b =>
    ∑ sample : ElementwiseSample n n,
      sqMagProb A sample.1 sample.2 * finiteMatMul (D sample) (D sample) a b
  have hM_eq :
      (fun a b : Fin n ⊕ Fin n =>
          (sqMagSampleProbability A hden).expectationReal
            (fun sample : ElementwiseSample n n =>
              finiteMatMul (D sample) (D sample) a b)) = M := by
    ext a b
    simp [M, FiniteProbability.expectationReal, sqMagSampleProbability]
  rw [hM_eq]
  have hMsym : IsSymmetricFiniteMatrix M := by
    dsimp [M]
    exact IsSymmetricFiniteMatrix.sum_smul
      (fun sample : ElementwiseSample n n => sqMagProb A sample.1 sample.2)
      (fun sample : ElementwiseSample n n => finiteMatMul (D sample) (D sample))
      (fun sample =>
        finiteMatMul_self_symmetric_of_symmetric (D sample)
          (rectSelfAdjointDilation_symmetric
            (elementwiseSampleResidualIncrement s A sample)))
  have hNsym :
      IsSymmetricFiniteMatrix
        (fun a b : Fin n ⊕ Fin n => V * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric V
  have hLe :
      finiteLoewnerLe M
        (fun a b : Fin n ⊕ Fin n => V * finiteIdMatrix a b) := by
    dsimp [M, V, D]
    exact
      sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_square
        s A hden hs
  have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M
    (fun a b : Fin n ⊕ Fin n => V * finiteIdMatrix a b) hMsym hNsym hLe
  simpa [V, D, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC

/-- Source-aligned rectangular C⋆ variance proxy for the one-sample
    self-adjoint dilation residual increment. -/
theorem sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (sqMagSampleProbability A hden).expectationCStarMatrix
      (fun sample : ElementwiseSample m n =>
        (finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) *
          finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) :
        CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
      ((max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)) : ℂ) •
        (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
  classical
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)
  let V : ℝ := max (m : ℝ) (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)
  have hprod :
      (fun sample : ElementwiseSample m n =>
        (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
      (fun sample : ElementwiseSample m n =>
        finiteComplexCStarMatrix (finiteMatMul (D sample) (D sample))) := by
    funext sample
    rw [finiteComplexCStarMatrix_mul]
  rw [hprod]
  rw [FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix]
  let M : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ := fun a b =>
    ∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 * finiteMatMul (D sample) (D sample) a b
  have hM_eq :
      (fun a b : Fin m ⊕ Fin n =>
          (sqMagSampleProbability A hden).expectationReal
            (fun sample : ElementwiseSample m n =>
              finiteMatMul (D sample) (D sample) a b)) = M := by
    ext a b
    simp [M, FiniteProbability.expectationReal, sqMagSampleProbability]
  rw [hM_eq]
  have hMsym : IsSymmetricFiniteMatrix M := by
    dsimp [M]
    exact IsSymmetricFiniteMatrix.sum_smul
      (fun sample : ElementwiseSample m n => sqMagProb A sample.1 sample.2)
      (fun sample : ElementwiseSample m n => finiteMatMul (D sample) (D sample))
      (fun sample =>
        finiteMatMul_self_symmetric_of_symmetric (D sample)
          (rectSelfAdjointDilation_symmetric
            (elementwiseSampleResidualIncrement s A sample)))
  have hNsym :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric V
  have hLe :
      finiteLoewnerLe M
        (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) := by
    dsimp [M, V, D]
    exact
      sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
        s A hden hs
  have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M
    (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) hMsym hNsym hLe
  simpa [V, D, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC

/-- Positive support for the truncated squared-magnitude law gives the spectral
upper-bound hypothesis needed by the support-aware C⋆ Bernstein log-CGF
theorem. -/
theorem sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (sample : ElementwiseSample m n)
    (hsampleProb :
      0 < (sqMagSampleProbability (elementwiseTruncate tau A) hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) sample)))) :
    x ≤
      Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hsampleSq : 0 < sqMagProb Ahat sample.1 sample.2 := by
    simpa [Ahat, sqMagSampleProbability] using hsampleProb
  have hsample_ne :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0 := by
    simpa [Ahat] using
      entry_ne_zero_of_sqMagProb_pos Ahat sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
        (fun a b : Fin m ⊕ Fin n =>
          L * finiteIdMatrix a b) := by
    simpa [Ahat, L] using
      finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample)) :=
    rectSelfAdjointDilation_symmetric
      (elementwiseSampleResidualIncrement s Ahat sample)
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hxAhat :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample))) := by
    simpa [Ahat] using hx
  have hxle : x ≤ L :=
    cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxAhat
  simpa [Ahat, L] using hxle

/-- Negative-increment companion of
`sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le`.

Positive support under the truncated law also gives the upper spectral bound
for `-D(Z_t)`, needed for the lower-tail Bernstein route. -/
theorem sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (sample : ElementwiseSample m n)
    (hsampleProb :
      0 < (sqMagSampleProbability (elementwiseTruncate tau A) hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) sample)) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) :
    x ≤
      Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hsampleSq : 0 < sqMagProb Ahat sample.1 sample.2 := by
    simpa [Ahat, sqMagSampleProbability] using hsampleProb
  have hsample_ne :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0 := by
    simpa [Ahat] using
      entry_ne_zero_of_sqMagProb_pos Ahat sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
    simpa [Ahat, L] using
      finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) := by
    intro a b
    change
      -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample) a b =
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample) b a
    rw [rectSelfAdjointDilation_symmetric]
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      -finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_neg, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hxAhat :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    simpa [Ahat] using hx
  have hxle : x ≤ L :=
    cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxAhat
  simpa [Ahat, L] using hxle

/-- Sharper positive-support spectral upper bound for the truncated
squared-magnitude law.

This version uses the direct rectangular-operator-to-dilation Loewner adapter,
so the radius is
`(1/s) * ||Ahat||_F + ||Ahat||_F^2/(s*tau)` without the auxiliary `sqrt 2`
factor. -/
theorem sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le_sharp
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (sample : ElementwiseSample m n)
    (hsampleProb :
      0 < (sqMagSampleProbability (elementwiseTruncate tau A) hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) sample)))) :
    x ≤
      (1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
        frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hsampleSq : 0 < sqMagProb Ahat sample.1 sample.2 := by
    simpa [Ahat, sqMagSampleProbability] using hsampleProb
  have hsample_ne :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0 := by
    simpa [Ahat] using
      entry_ne_zero_of_sqMagProb_pos Ahat sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
    simpa [Ahat, L] using
      finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_sharp
        htau hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample)) :=
    rectSelfAdjointDilation_symmetric
      (elementwiseSampleResidualIncrement s Ahat sample)
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hxAhat :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample))) := by
    simpa [Ahat] using hx
  have hxle : x ≤ L :=
    cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxAhat
  simpa [Ahat, L] using hxle

/-- Sharper negative-increment spectral upper bound for the truncated
squared-magnitude law, again without the auxiliary `sqrt 2` factor. -/
theorem sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le_sharp
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (sample : ElementwiseSample m n)
    (hsampleProb :
      0 < (sqMagSampleProbability (elementwiseTruncate tau A) hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) sample)) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) :
    x ≤
      (1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
        frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hsampleSq : 0 < sqMagProb Ahat sample.1 sample.2 := by
    simpa [Ahat, sqMagSampleProbability] using hsampleProb
  have hsample_ne :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0 := by
    simpa [Ahat] using
      entry_ne_zero_of_sqMagProb_pos Ahat sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
    simpa [Ahat, L] using
      finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_sharp
        htau hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) := by
    intro a b
    change
      -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample) a b =
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample) b a
    rw [rectSelfAdjointDilation_symmetric]
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      -finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_neg, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hxAhat :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    simpa [Ahat] using hx
  have hxle : x ≤ L :=
    cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxAhat
  simpa [Ahat, L] using hxle

/-- Algorithm 1 literal one-sample Bernstein log-CGF for the self-adjoint
dilation residual increment with the exact input-dependent support radius.

Unlike the source-aligned truncated theorem, this statement keeps the literal
law `p_ij = A_ij^2 / ||A||_F^2` and uses the finite reciprocal-entry radius
`elementwiseLiteralResidualSupportRadius s A`.  The result is therefore
nonconditional for the literal sampler, but the displayed radius necessarily
depends on the small nonzero entries of `A`. -/
theorem sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
    {m n s : ℕ} {theta : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 ≤ theta) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    CFC.log
        ((sqMagSampleProbability A hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            NormedSpace.exp
              (theta •
                finiteComplexCStarMatrix
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample)) :
                CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
      ((Real.exp (theta * L) - theta * L - 1) / L ^ 2) •
        (sqMagSampleProbability A hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            (finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) *
              finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) :
            CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
  classical
  intro L
  let P := sqMagSampleProbability A hden
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample =>
      finiteComplexCStarMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample))
  have hL_pos : 0 < L := by
    simpa [L] using
      elementwiseLiteralResidualSupportRadius_pos hs A hden
  have hX : ∀ sample, IsSelfAdjoint (X sample) := by
    intro sample
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample))
      (rectSelfAdjointDilation_symmetric
        (elementwiseSampleResidualIncrement s A sample))
  have hmean : P.expectationCStarMatrix X = 0 := by
    simpa [P, X] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        A hden (ne_of_gt hs)
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (X sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, L] using
      sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_literal_spectrum_le_supportRadius
        hs A hden sample (by simpa [P] using hsample) hx
  simpa [P, X, L] using
    P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
      hX hmean htheta hL_pos hspec

/-- Algorithm 1 truncated one-sample Bernstein log-CGF for the self-adjoint
dilation residual increment.

This instantiates the generic support-aware one-sample C⋆ Bernstein theorem
with the squared-magnitude row-entry law, the zero-mean dilation residual
increment, and the retained-entry truncated spectral bound.  It is still a
one-sample log-CGF theorem; the iid trace-MGF iteration and final optimized
matrix-Bernstein tail remain separate ledger items. -/
theorem sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    CFC.log
        ((sqMagSampleProbability (elementwiseTruncate tau A) hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            NormedSpace.exp
              (theta •
                finiteComplexCStarMatrix
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s
                      (elementwiseTruncate tau A) sample)) :
                CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
      ((Real.exp
          (theta *
            (Real.sqrt 2 *
              ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
                frobNormSqRect (elementwiseTruncate tau A) /
                  ((s : ℝ) * tau)))) -
          theta *
            (Real.sqrt 2 *
              ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
                frobNormSqRect (elementwiseTruncate tau A) /
                  ((s : ℝ) * tau))) - 1) /
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) ^ 2) •
        (sqMagSampleProbability (elementwiseTruncate tau A) hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            (finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s
                    (elementwiseTruncate tau A) sample)) *
              finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s
                    (elementwiseTruncate tau A) sample)) :
            CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagSampleProbability Ahat hden
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample =>
      finiteComplexCStarMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hdenA : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hparen :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hparen
  have hX : ∀ sample, IsSelfAdjoint (X sample) := by
    intro sample
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample))
      (rectSelfAdjointDilation_symmetric
        (elementwiseSampleResidualIncrement s Ahat sample))
  have hmean : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, Ahat] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        Ahat hden (ne_of_gt hs)
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (X sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Ahat, L] using
      sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le
        htau hs A hden sample (by simpa [P, Ahat] using hsample) hx
  simpa [P, X, Ahat, L] using
    P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
      hX hmean htheta hL_pos hspec

/-- Source-sharpened version of the Algorithm 1 truncated one-sample
Bernstein log-CGF bound.

The only change from
`sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`
is the spectral radius: this theorem uses the direct rectangular
operator-to-dilation bridge, so the bounded-increment parameter is
`(1/s)||Ahat||_F + ||Ahat||_F^2/(s*tau)` rather than that quantity multiplied
by `sqrt 2`. -/
theorem sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    CFC.log
        ((sqMagSampleProbability (elementwiseTruncate tau A) hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            NormedSpace.exp
              (theta •
                finiteComplexCStarMatrix
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s
                      (elementwiseTruncate tau A) sample)) :
                CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
      ((Real.exp
          (theta *
            ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
              frobNormSqRect (elementwiseTruncate tau A) /
                ((s : ℝ) * tau))) -
          theta *
            ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
              frobNormSqRect (elementwiseTruncate tau A) /
                ((s : ℝ) * tau)) - 1) /
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)) ^ 2) •
        (sqMagSampleProbability (elementwiseTruncate tau A) hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            (finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s
                    (elementwiseTruncate tau A) sample)) *
              finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s
                    (elementwiseTruncate tau A) sample)) :
            CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagSampleProbability Ahat hden
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample =>
      finiteComplexCStarMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hL_pos : 0 < L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hdenA : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    exact add_pos_of_nonneg_of_pos hfirst hsecond
  have hX : ∀ sample, IsSelfAdjoint (X sample) := by
    intro sample
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample))
      (rectSelfAdjointDilation_symmetric
        (elementwiseSampleResidualIncrement s Ahat sample))
  have hmean : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, Ahat] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        Ahat hden (ne_of_gt hs)
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (X sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Ahat, L] using
      sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le_sharp
        htau hs A hden sample (by simpa [P, Ahat] using hsample) hx
  simpa [P, X, Ahat, L] using
    P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
      hX hmean htheta hL_pos hspec

/-- Algorithm 1 literal scalar trace-MGF bound after combining the
input-dependent support-radius log-CGF theorem with the sharp rectangular
variance proxy.

This is a nonconditional trace-MGF bound for the literal squared-magnitude
sampler.  Its bounded-increment parameter is the exact finite quantity
`elementwiseLiteralResidualSupportRadius s A`, not a uniform source constant. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
    {m n s : ℕ} {theta : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 ≤ theta) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) A hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro L beta V
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)
  have hlog :
      CFC.log
          ((sqMagSampleProbability A hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • finiteComplexCStarMatrix (D sample) :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          (sqMagSampleProbability A hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
    simpa [D, L, beta] using
      sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
        (m := m) (n := n) (s := s) (theta := theta)
        hs A hden htheta
  have hvar :
      (sqMagSampleProbability A hden).expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    simpa [D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
        A hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          (sqMagSampleProbability A hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          ((sqMagSampleProbability A hden).expectationCStarMatrix
            (fun x : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => theta * D x a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => theta * D x a b))) =
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • finiteComplexCStarMatrix (D x) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext x
      rw [finiteComplexCStarMatrix_smul]
      rfl
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) A hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        theta * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, D, L, beta, V]
    using hbound

/-- Negative-increment literal scalar trace-MGF bound with the same exact
input-dependent support radius. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
    {m n s : ℕ} {theta : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 ≤ theta) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) A hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        (-theta) *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro L beta V
  let P := sqMagSampleProbability A hden
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => finiteComplexCStarMatrix (D sample)
  let Xneg : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => -X sample
  have hL_pos : 0 < L := by
    simpa [L] using
      elementwiseLiteralResidualSupportRadius_pos hs A hden
  have hX : ∀ sample, IsSelfAdjoint (Xneg sample) := by
    intro sample
    have hD : IsSelfAdjoint (X sample) :=
      finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
        (D sample)
        (rectSelfAdjointDilation_symmetric
          (elementwiseSampleResidualIncrement s A sample))
    simpa [Xneg] using hD.neg
  have hmeanX : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, D] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        A hden (ne_of_gt hs)
  have hmean : P.expectationCStarMatrix Xneg = 0 := by
    calc
      P.expectationCStarMatrix Xneg
          = -P.expectationCStarMatrix X := by
              simpa [Xneg] using
                (FiniteProbability.expectationCStarMatrix_neg P X)
      _ = 0 := by simp [hmeanX]
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (Xneg sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Xneg, D, L] using
      sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_literal_spectrum_le_supportRadius
        hs A hden sample (by simpa [P] using hsample) hx
  have hlog :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • Xneg sample :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) := by
    simpa [P, Xneg, X, D, L, beta] using
      P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
        hX hmean htheta hL_pos hspec
  have hsq :
      (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) =
        (fun sample : ElementwiseSample m n =>
          X sample * X sample) := by
    funext sample
    ext a b
    simp [Xneg, X, CStarMatrix.mul_apply]
  have hvar :
      P.expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    rw [hsq]
    simpa [P, X, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
        A hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b))) =
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • Xneg sample :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext sample
      congr 1
      ext a b
      simp [Xneg, X, D]
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) A hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        (-theta) * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, D, L, beta, V]
    using hbound

/-- Algorithm 1 truncated scalar trace-MGF bound after combining the
support-aware one-sample log-CGF theorem with the proved C⋆ variance proxy.

This is the matrix-Bernstein trace-MGF scalarization layer for the
self-adjoint dilation increments.  It still leaves the final optimization of
`theta` and the conversion to the exact CACM equation (2) constants as the next
tail step. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  have hlog :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • finiteComplexCStarMatrix (D sample) :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
    simpa [Ahat, D, L, beta] using
      sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
        htau hs A hden htheta
  have hvar :
      (sqMagSampleProbability Ahat hden).expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    simpa [Ahat, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun x : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => theta * D x a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => theta * D x a b))) =
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • finiteComplexCStarMatrix (D x) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext x
      rw [finiteComplexCStarMatrix_smul]
      rfl
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        theta * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Rectangular source-sharp Algorithm 1 truncated scalar trace-MGF bound.

This is the rectangular companion to the square source-sharp theorem below,
but it keeps the generic truncated support radius with the `sqrt 2` factor.
The improvement is in the variance proxy:
`V = max(m,n) * ||Ahat||_F^2 / s^2`, using the already formalized
self-adjoint-dilation rectangular variance theorem. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_rect
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  have hlog :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • finiteComplexCStarMatrix (D sample) :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
    simpa [Ahat, D, L, beta] using
      sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
        htau hs A hden htheta
  have hvar :
      (sqMagSampleProbability Ahat hden).expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    simpa [Ahat, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun x : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => theta * D x a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => theta * D x a b))) =
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • finiteComplexCStarMatrix (D x) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext x
      rw [finiteComplexCStarMatrix_smul]
      rfl
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        theta * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Source-sharp square-matrix Algorithm 1 truncated scalar trace-MGF bound.

This combines the no-`sqrt 2` one-sample log-CGF support radius with the
Drineas--Zouzias square variance proxy
`V = n * ||Ahat||_F^2 / s^2`. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square
    {n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau)
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin n ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let D : ElementwiseSample n n → Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  have hlog :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              NormedSpace.exp
                (theta • finiteComplexCStarMatrix (D sample) :
                  CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ))) ≤
        beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) := by
    simpa [Ahat, D, L, beta] using
      sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp
        (m := n) (n := n) (s := s) (tau := tau) (theta := theta)
        htau hs A hden htheta
  have hvar :
      (sqMagSampleProbability Ahat hden).expectationCStarMatrix
        (fun sample : ElementwiseSample n n =>
          (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    simpa [Ahat, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun x : ElementwiseSample n n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin n ⊕ Fin n => theta * D x a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    have hexp :
        (fun x : ElementwiseSample n n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin n ⊕ Fin n => theta * D x a b))) =
        (fun x : ElementwiseSample n n =>
          NormedSpace.exp
            (theta • finiteComplexCStarMatrix (D x) :
              CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) := by
      funext x
      rw [finiteComplexCStarMatrix_smul]
      rfl
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample n n) (a b : Fin n ⊕ Fin n) =>
        theta * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Algorithm 1 truncated upper-tail eigenvalue bound obtained from the
proved one-sample log-CGF, the C⋆ variance proxy, the iid trace-MGF iteration,
and the finite-dimensional trace-exponential Markov interface.

The theorem is still parameterized by `theta` and `T`; optimizing these
parameters and adding the lower-tail/spectral-norm conversion is the remaining
Bernstein tail step. -/
theorem sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_ge_le_exp
    {m n s : ℕ} {tau theta T : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∃ a : Fin m ⊕ Fin n,
            T ≤ finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a} ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
  classical
  intro Ahat L beta V
  have hmarkov :=
    sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_ge_le
      (A := Ahat) hden (ne_of_gt hs) theta T
  have htrace :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
      (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hmul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using htrace)
      (le_of_lt (Real.exp_pos _))
  exact hmarkov.trans hmul

/-- Negative-increment companion of
`sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`.

This proves the scalar trace-MGF bound needed for the lower-tail half of the
two-sided matrix-Bernstein route.  The proof applies the same one-sample
log-CGF theorem to `-D(Z_t)`, using the negative support bound and the fact
that `(-X)^2 = X^2`. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        (-theta) *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let P := sqMagSampleProbability Ahat hden
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => finiteComplexCStarMatrix (D sample)
  let Xneg : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => -X sample
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hdenA : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hparen :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hparen
  have hX : ∀ sample, IsSelfAdjoint (Xneg sample) := by
    intro sample
    have hD : IsSelfAdjoint (X sample) :=
      finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
        (D sample)
        (rectSelfAdjointDilation_symmetric
          (elementwiseSampleResidualIncrement s Ahat sample))
    simpa [Xneg] using hD.neg
  have hmeanX : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, D, Ahat] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        Ahat hden (ne_of_gt hs)
  have hmean : P.expectationCStarMatrix Xneg = 0 := by
    calc
      P.expectationCStarMatrix Xneg
          = -P.expectationCStarMatrix X := by
              simpa [Xneg] using
                (FiniteProbability.expectationCStarMatrix_neg P X)
      _ = 0 := by simp [hmeanX]
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (Xneg sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Xneg, D, Ahat, L] using
      sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le
        htau hs A hden sample (by simpa [P, Ahat] using hsample) hx
  have hlog :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • Xneg sample :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) := by
    simpa [P, Xneg, X, D, L, beta] using
      P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
        hX hmean htheta hL_pos hspec
  have hsq :
      (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) =
        (fun sample : ElementwiseSample m n =>
          X sample * X sample) := by
    funext sample
    ext a b
    simp [Xneg, X, CStarMatrix.mul_apply]
  have hvar :
      P.expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    rw [hsq]
    simpa [P, X, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b))) =
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • Xneg sample :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext sample
      congr 1
      ext a b
      simp [Xneg, X, D]
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        (-theta) * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Negative-increment companion of the rectangular source-sharp truncated
trace-MGF bound.

The support radius is the same generic truncated radius as in the positive
bound, while the variance proxy is the rectangular
`max(m,n) * ||Ahat||_F^2 / s^2` proxy. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_rect
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        (-theta) *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let P := sqMagSampleProbability Ahat hden
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => finiteComplexCStarMatrix (D sample)
  let Xneg : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => -X sample
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hdenA : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hparen :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hparen
  have hX : ∀ sample, IsSelfAdjoint (Xneg sample) := by
    intro sample
    have hD : IsSelfAdjoint (X sample) :=
      finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
        (D sample)
        (rectSelfAdjointDilation_symmetric
          (elementwiseSampleResidualIncrement s Ahat sample))
    simpa [Xneg] using hD.neg
  have hmeanX : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, D, Ahat] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        Ahat hden (ne_of_gt hs)
  have hmean : P.expectationCStarMatrix Xneg = 0 := by
    calc
      P.expectationCStarMatrix Xneg
          = -P.expectationCStarMatrix X := by
              simpa [Xneg] using
                (FiniteProbability.expectationCStarMatrix_neg P X)
      _ = 0 := by simp [hmeanX]
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (Xneg sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Xneg, D, Ahat, L] using
      sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le
        htau hs A hden sample (by simpa [P, Ahat] using hsample) hx
  have hlog :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • Xneg sample :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) := by
    simpa [P, Xneg, X, D, L, beta] using
      P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
        hX hmean htheta hL_pos hspec
  have hsq :
      (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) =
        (fun sample : ElementwiseSample m n =>
          X sample * X sample) := by
    funext sample
    ext a b
    simp [Xneg, X, CStarMatrix.mul_apply]
  have hvar :
      P.expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    rw [hsq]
    simpa [P, X, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b))) =
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • Xneg sample :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext sample
      congr 1
      ext a b
      simp [Xneg, X, D]
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        (-theta) * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Source-sharp square-matrix negative-increment trace-MGF bound for
    Algorithm 1. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square
    {n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau)
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin n ⊕ Fin n => 0)
      (fun sample a b =>
        (-theta) *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let P := sqMagSampleProbability Ahat hden
  let D : ElementwiseSample n n → Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  let X : ElementwiseSample n n →
      CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    fun sample => finiteComplexCStarMatrix (D sample)
  let Xneg : ElementwiseSample n n →
      CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    fun sample => -X sample
  have hL_pos : 0 < L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hdenA : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    exact add_pos_of_nonneg_of_pos hfirst hsecond
  have hX : ∀ sample, IsSelfAdjoint (Xneg sample) := by
    intro sample
    have hD : IsSelfAdjoint (X sample) :=
      finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
        (D sample)
        (rectSelfAdjointDilation_symmetric
          (elementwiseSampleResidualIncrement s Ahat sample))
    simpa [Xneg] using hD.neg
  have hmeanX : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, D, Ahat] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        Ahat hden (ne_of_gt hs)
  have hmean : P.expectationCStarMatrix Xneg = 0 := by
    calc
      P.expectationCStarMatrix Xneg
          = -P.expectationCStarMatrix X := by
              simpa [Xneg] using
                (FiniteProbability.expectationCStarMatrix_neg P X)
      _ = 0 := by simp [hmeanX]
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (Xneg sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Xneg, D, Ahat, L] using
      sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le_sharp
        htau hs A hden sample (by simpa [P, Ahat] using hsample) hx
  have hlog :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              NormedSpace.exp
                (theta • Xneg sample :
                  CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ))) ≤
        beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              Xneg sample * Xneg sample) := by
    simpa [P, Xneg, X, D, L, beta] using
      P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
        hX hmean htheta hL_pos hspec
  have hsq :
      (fun sample : ElementwiseSample n n =>
          Xneg sample * Xneg sample) =
        (fun sample : ElementwiseSample n n =>
          X sample * X sample) := by
    funext sample
    ext a b
    simp [Xneg, X, CStarMatrix.mul_apply]
  have hvar :
      P.expectationCStarMatrix
        (fun sample : ElementwiseSample n n =>
          Xneg sample * Xneg sample) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    rw [hsq]
    simpa [P, X, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              Xneg sample * Xneg sample) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin n ⊕ Fin n => (-theta) * D sample a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    have hexp :
        (fun sample : ElementwiseSample n n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin n ⊕ Fin n => (-theta) * D sample a b))) =
        (fun sample : ElementwiseSample n n =>
          NormedSpace.exp
            (theta • Xneg sample :
              CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) := by
      funext sample
      congr 1
      ext a b
      simp [Xneg, X, D]
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample n n) (a b : Fin n ⊕ Fin n) =>
        (-theta) * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Source-sharp square-matrix two-sided truncated eigenvalue tail skeleton
    before optimizing `theta`. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_square
    {n s : ℕ} {tau theta T : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau)
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    1 -
        (Real.exp (-T) *
            (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
          Real.exp (-T) *
            (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin n ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin n ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < T} := by
  classical
  intro Ahat L beta V
  have htwo :=
    sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge
      (A := Ahat) hden (ne_of_gt hs) theta T
  have hpos :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square
      (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hneg :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square
      (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hposMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin n ⊕ Fin n => 0)
          (fun sample a b =>
            theta * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hpos)
      (le_of_lt (Real.exp_pos _))
  have hnegMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin n ⊕ Fin n => 0)
          (fun sample a b =>
            (-theta) * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hneg)
      (le_of_lt (Real.exp_pos _))
  have hsum :
      Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin n ⊕ Fin n => 0)
            (fun sample a b =>
              (-theta) * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) +
        Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin n ⊕ Fin n => 0)
            (fun sample a b =>
              theta * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
          (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
        Real.exp (-T) *
          (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) :=
    add_le_add hnegMul hposMul
  have hsub :
      1 -
          (Real.exp (-T) *
              (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
            Real.exp (-T) *
              (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
        1 -
          (Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin n ⊕ Fin n => 0)
                (fun sample a b =>
                  (-theta) * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b) +
            Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin n ⊕ Fin n => 0)
                (fun sample a b =>
                  theta * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b)) := by
    linarith
  exact hsub.trans htwo

/-- Two-sided literal Algorithm 1 eigenvalue tail bound before optimizing
`theta`, using the exact input-dependent support radius.

This is the literal-law counterpart of the truncated Bernstein skeleton.  It
is fully nonconditional for exact squared-magnitude sampling, but the rate is
controlled by the irreducible finite radius
`elementwiseLiteralResidualSupportRadius s A`, which expands to
`(1/s)||A||_F + sum_{A_ij != 0} ||A||_F^2/(s |A_ij|)`. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_literalTraceResidual_lt_ge_exp_supportRadius
    {m n s : ℕ} {theta T : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 ≤ theta) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    1 -
        (Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
          Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s A samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s A samples) b c))
              a| < T} := by
  classical
  intro L beta V
  have htwo :=
    sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge
      (A := A) hden (ne_of_gt hs) theta T
  have hpos :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
      (m := m) (n := n) (s := s) (theta := theta)
      hs A hden htheta
  have hneg :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
      (m := m) (n := n) (s := s) (theta := theta)
      hs A hden htheta
  have hposMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [L, beta, V] using hpos)
      (le_of_lt (Real.exp_pos _))
  have hnegMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            (-theta) * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [L, beta, V] using hneg)
      (le_of_lt (Real.exp_pos _))
  have hsum :
      Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) A hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              (-theta) * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) +
        Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) A hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              theta * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) ≤
      Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
        Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) :=
    add_le_add hnegMul hposMul
  have hsub :
      1 -
          (Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
            Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
        1 -
          (Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) A hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  (-theta) * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample) a b) +
            Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) A hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  theta * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample) a b)) := by
    linarith
  exact hsub.trans htwo

/-- Two-sided Algorithm 1 truncated eigenvalue tail bound before optimizing
`theta`.

This combines the positive and negative scalar trace-MGF bounds with the
repository's two-sided trace-exponential Markov interface.  It is the
two-sided Bernstein tail skeleton for the truncated self-adjoint dilation; the
remaining CACM equation (2) work is the parameter optimization and conversion
from this eigenvalue event to the final stated spectral-norm constants. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp
    {m n s : ℕ} {tau theta T : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    1 -
        (Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
          Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < T} := by
  classical
  intro Ahat L beta V
  have htwo :=
    sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge
      (A := Ahat) hden (ne_of_gt hs) theta T
  have hpos :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
      (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hneg :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
      (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hposMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hpos)
      (le_of_lt (Real.exp_pos _))
  have hnegMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            (-theta) * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hneg)
      (le_of_lt (Real.exp_pos _))
  have hsum :
      Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              (-theta) * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) +
        Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              theta * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
        Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) :=
    add_le_add hnegMul hposMul
  have hsub :
      1 -
          (Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
            Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
        1 -
          (Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  (-theta) * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b) +
            Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  theta * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b)) := by
    linarith
  exact hsub.trans htwo

/-- Rectangular source-sharp two-sided truncated eigenvalue tail skeleton.

This is the same scaled-eigenvalue statement as the generic rectangular
truncated theorem, but it uses the sharpened rectangular variance proxy
`max(m,n) * ||Ahat||_F^2 / s^2`.  The support radius remains the generic
truncated radius with the `sqrt 2` factor. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_rect
    {m n s : ℕ} {tau theta T : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    1 -
        (Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
          Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < T} := by
  classical
  intro Ahat L beta V
  have htwo :=
    sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge
      (A := Ahat) hden (ne_of_gt hs) theta T
  have hpos :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_rect
      (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hneg :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_rect
      (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hposMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hpos)
      (le_of_lt (Real.exp_pos _))
  have hnegMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            (-theta) * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hneg)
      (le_of_lt (Real.exp_pos _))
  have hsum :
      Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              (-theta) * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) +
        Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              theta * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
        Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) :=
    add_le_add hnegMul hposMul
  have hsub :
      1 -
          (Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
            Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
        1 -
          (Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  (-theta) * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b) +
            Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  theta * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b)) := by
    linarith
  exact hsub.trans htwo

/-- Explicit high-probability form of the two-sided Algorithm 1 truncated
eigenvalue tail skeleton.

This corollary chooses
`T = log (2 B / δ)`, where
`B = (m + n) * exp (s * beta * V)` is the scalar trace-MGF bound from the
parameterized theorem above.  The choice makes the two equal
trace-exponential failure terms sum to `δ`.  The result is still a scaled
eigenvalue statement; optimizing `theta` and converting to the exact CACM
equation (2) constants remain the next red-bottleneck dependency. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta
    {m n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < Real.log ((2 * B) / δ)} := by
  classical
  intro Ahat L beta V B
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos hdim (Real.exp_pos _)
  have htail :
      1 -
          (Real.exp (-Real.log ((2 * B) / δ)) * B +
            Real.exp (-Real.log ((2 * B) / δ)) * B) ≤
        (sqMagTraceProbability (steps := s) Ahat hden).eventProb
          {samples |
            ∀ a : Fin m ⊕ Fin n,
              |finiteHermitianEigenvalues
                (fun b c : Fin m ⊕ Fin n =>
                  theta *
                    rectSelfAdjointDilation
                      (elementwiseTraceResidual s Ahat samples) b c)
                (by
                  intro b c
                  exact congrArg (fun x => theta * x)
                    (rectSelfAdjointDilation_symmetric
                      (elementwiseTraceResidual s Ahat samples) b c))
                a| < Real.log ((2 * B) / δ)} := by
    simpa [Ahat, L, beta, V, B] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
        (T := Real.log ((2 * B) / δ)) htau hs A hden htheta
  have hfailure :
      Real.exp (-Real.log ((2 * B) / δ)) * B +
          Real.exp (-Real.log ((2 * B) / δ)) * B = δ :=
    real_exp_neg_log_two_mul_div_mul_self_add (B := B) (δ := δ) hB_pos hδ
  simpa [hfailure] using htail

/-- Explicit high-probability form of the rectangular source-sharp two-sided
truncated eigenvalue tail skeleton. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_rect
    {m n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < Real.log ((2 * B) / δ)} := by
  classical
  intro Ahat L beta V B
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos hdim (Real.exp_pos _)
  have htail :
      1 -
          (Real.exp (-Real.log ((2 * B) / δ)) * B +
            Real.exp (-Real.log ((2 * B) / δ)) * B) ≤
        (sqMagTraceProbability (steps := s) Ahat hden).eventProb
          {samples |
            ∀ a : Fin m ⊕ Fin n,
              |finiteHermitianEigenvalues
                (fun b c : Fin m ⊕ Fin n =>
                  theta *
                    rectSelfAdjointDilation
                      (elementwiseTraceResidual s Ahat samples) b c)
                (by
                  intro b c
                  exact congrArg (fun x => theta * x)
                    (rectSelfAdjointDilation_symmetric
                      (elementwiseTraceResidual s Ahat samples) b c))
                a| < Real.log ((2 * B) / δ)} := by
    simpa [Ahat, L, beta, V, B] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_rect
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
        (T := Real.log ((2 * B) / δ)) htau hs A hden htheta
  have hfailure :
      Real.exp (-Real.log ((2 * B) / δ)) * B +
          Real.exp (-Real.log ((2 * B) / δ)) * B = δ :=
    real_exp_neg_log_two_mul_div_mul_self_add (B := B) (δ := δ) hB_pos hδ
  simpa [hfailure] using htail

/-- Explicit high-probability scaled-eigenvalue form for the literal
Algorithm 1 trace-MGF bound with input-dependent support radius. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_literalTraceResidual_lt_ge_one_sub_delta_supportRadius
    {m n s : ℕ} {theta δ : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 ≤ theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s A samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s A samples) b c))
              a| < Real.log ((2 * B) / δ)} := by
  classical
  intro L beta V B
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos hdim (Real.exp_pos _)
  have htail :
      1 -
          (Real.exp (-Real.log ((2 * B) / δ)) * B +
            Real.exp (-Real.log ((2 * B) / δ)) * B) ≤
        (sqMagTraceProbability (steps := s) A hden).eventProb
          {samples |
            ∀ a : Fin m ⊕ Fin n,
              |finiteHermitianEigenvalues
                (fun b c : Fin m ⊕ Fin n =>
                  theta *
                    rectSelfAdjointDilation
                      (elementwiseTraceResidual s A samples) b c)
                (by
                  intro b c
                  exact congrArg (fun x => theta * x)
                    (rectSelfAdjointDilation_symmetric
                      (elementwiseTraceResidual s A samples) b c))
                a| < Real.log ((2 * B) / δ)} := by
    simpa [L, beta, V, B] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_literalTraceResidual_lt_ge_exp_supportRadius
        (m := m) (n := n) (s := s) (theta := theta)
        (T := Real.log ((2 * B) / δ)) hs A hden htheta
  have hfailure :
      Real.exp (-Real.log ((2 * B) / δ)) * B +
          Real.exp (-Real.log ((2 * B) / δ)) * B = δ :=
    real_exp_neg_log_two_mul_div_mul_self_add (B := B) (δ := δ) hB_pos hδ
  simpa [hfailure] using htail

/-- Explicit high-probability form of the source-sharp square-matrix
    two-sided truncated eigenvalue tail skeleton. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_square
    {n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta)
    (hdim : 0 < (n : ℝ) + (n : ℝ)) (hδ : 0 < δ) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau)
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    let B : ℝ := ((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin n ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin n ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < Real.log ((2 * B) / δ)} := by
  classical
  intro Ahat L beta V B
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos hdim (Real.exp_pos _)
  have htail :
      1 -
          (Real.exp (-Real.log ((2 * B) / δ)) * B +
            Real.exp (-Real.log ((2 * B) / δ)) * B) ≤
        (sqMagTraceProbability (steps := s) Ahat hden).eventProb
          {samples |
            ∀ a : Fin n ⊕ Fin n,
              |finiteHermitianEigenvalues
                (fun b c : Fin n ⊕ Fin n =>
                  theta *
                    rectSelfAdjointDilation
                      (elementwiseTraceResidual s Ahat samples) b c)
                (by
                  intro b c
                  exact congrArg (fun x => theta * x)
                    (rectSelfAdjointDilation_symmetric
                      (elementwiseTraceResidual s Ahat samples) b c))
                a| < Real.log ((2 * B) / δ)} := by
    simpa [Ahat, L, beta, V, B] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_square
        (n := n) (s := s) (tau := tau) (theta := theta)
        (T := Real.log ((2 * B) / δ)) htau hs A hden htheta
  have hfailure :
      Real.exp (-Real.log ((2 * B) / δ)) * B +
          Real.exp (-Real.log ((2 * B) / δ)) * B = δ :=
    real_exp_neg_log_two_mul_div_mul_self_add (B := B) (δ := δ) hB_pos hδ
  simpa [hfailure] using htail

/-- Product-law expectation form of one-step zero mean for the self-adjoint
    dilation residual increment at a fixed trace coordinate. -/
theorem sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (t : Fin s) (a b : Fin m ⊕ Fin n) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A (samples t)) a b) = 0 := by
  classical
  have hstep :=
    sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b)
  rw [hstep]
  exact sqMagProb_sum_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_eq_zero
    s A hden hs a b

/-- The full self-adjoint dilation residual is entrywise mean-zero under the
    canonical independent squared-magnitude trace law. -/
theorem sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_elementwiseTraceResidual_eq_zero
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (a b : Fin m ⊕ Fin n) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        rectSelfAdjointDilation (elementwiseTraceResidual s A samples) a b) =
      0 := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  calc
    P.expectationReal
      (fun samples : ElementwiseTrace m n s =>
        rectSelfAdjointDilation (elementwiseTraceResidual s A samples) a b)
        = P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              ∑ t : Fin s,
                rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)) a b) := by
            congr 1
            ext samples
            exact rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
              A samples hs a b
    _ = ∑ t : Fin s,
          P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A (samples t)) a b) := by
            rw [FiniteProbability.expectationReal_sum]
    _ = ∑ _t : Fin s, 0 := by
            apply Finset.sum_congr rfl
            intro t _
            exact
              sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
                A hden hs t a b
    _ = 0 := by simp

/-- Scalar symmetrization for a fixed coordinate of the Algorithm 1
self-adjoint dilation residual.

This is a source-uniform-route foundation: the exact residual coordinate is
centered under the literal squared-magnitude product law, so its expected
absolute value is bounded by the expected absolute difference between two
independent copies of the same exact sketch. -/
theorem sqMagTraceProbability_expectationReal_abs_rectSelfAdjointDilation_elementwiseTraceResidual_le_prod_abs_sub
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (a b : Fin m ⊕ Fin n) :
    let P := sqMagTraceProbability (steps := s) A hden
    P.expectationReal
        (fun samples =>
          |rectSelfAdjointDilation (elementwiseTraceResidual s A samples) a b|) ≤
      (P.prod P).expectationReal
        (fun x : ElementwiseTrace m n s × ElementwiseTrace m n s =>
          |rectSelfAdjointDilation (elementwiseTraceResidual s A x.1) a b -
            rectSelfAdjointDilation (elementwiseTraceResidual s A x.2) a b|) := by
  classical
  intro P
  exact
    FiniteProbability.expectationReal_abs_le_prod_expectationReal_abs_sub_of_expectation_eq_zero
      P
      (fun samples : ElementwiseTrace m n s =>
        rectSelfAdjointDilation (elementwiseTraceResidual s A samples) a b)
      (sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_elementwiseTraceResidual_eq_zero
        A hden hs a b)

namespace FiniteProbability






















































































































end FiniteProbability

/-- The exact Algorithm 1 residual is mean-zero after applying it to any fixed
    vector. -/
theorem sqMagTraceProbability_expectationReal_rectMatMulVec_elementwiseTraceResidual_eq_zero
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) (i : Fin m) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        rectMatMulVec (elementwiseTraceResidual s A samples) x i) = 0 := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  calc
    P.expectationReal
      (fun samples : ElementwiseTrace m n s =>
        rectMatMulVec (elementwiseTraceResidual s A samples) x i)
        = P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              ∑ j : Fin n,
                elementwiseTraceResidual s A samples i j * x j) := by
            rfl
    _ = ∑ j : Fin n,
          P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              elementwiseTraceResidual s A samples i j * x j) := by
            rw [FiniteProbability.expectationReal_sum]
    _ = ∑ j : Fin n,
          P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              elementwiseTraceResidual s A samples i j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [FiniteProbability.expectationReal_mul_const]
    _ = ∑ _j : Fin n, 0 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_eq_zero
              A hden hs]
            ring
    _ = 0 := by
            simp

/-- Fixed-vector Algorithm 1 symmetrization.

For any fixed vector `x`, the expected Euclidean norm of the exact residual
action is bounded by the expected Euclidean norm of the difference of two
independent exact residual actions.  This is a matrix-action version of the
scalar symmetrization checkpoint and is a reusable dependency for a future
matrix Khintchine route. -/
theorem sqMagTraceProbability_expectationReal_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_prod_vecNorm2_sub
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) :
    let P := sqMagTraceProbability (steps := s) A hden
    P.expectationReal
        (fun samples =>
          vecNorm2 (rectMatMulVec (elementwiseTraceResidual s A samples) x)) ≤
      (P.prod P).expectationReal
        (fun y : ElementwiseTrace m n s × ElementwiseTrace m n s =>
          vecNorm2
            (fun i : Fin m =>
              rectMatMulVec (elementwiseTraceResidual s A y.1) x i -
                rectMatMulVec (elementwiseTraceResidual s A y.2) x i)) := by
  classical
  intro P
  exact
    FiniteProbability.expectationReal_vecNorm2_le_prod_expectationReal_vecNorm2_sub_of_expectation_eq_zero
      P
      (fun samples : ElementwiseTrace m n s =>
        rectMatMulVec (elementwiseTraceResidual s A samples) x)
      (fun i =>
        sqMagTraceProbability_expectationReal_rectMatMulVec_elementwiseTraceResidual_eq_zero
          A hden hs x i)

namespace FiniteProbability





















































































end FiniteProbability

/-- Operator-predicate independent-copy symmetrization specialized to
Algorithm 1.

For a fixed realized trace, if every independent exact copy of the Algorithm 1
trace residual differs from it by an operator-`L` matrix, then the realized
residual itself is operator-`L`.  The only probability input is the exact
squared-magnitude law used to know that the residual entries are mean-zero. -/
theorem sqMagTraceProbability_rectOpNorm2Le_elementwiseTraceResidual_of_all_copy_diffs
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (samples : ElementwiseTrace m n s) {L : ℝ}
    (hdiff : ∀ samples' : ElementwiseTrace m n s,
      rectOpNorm2Le
        (fun i j =>
          elementwiseTraceResidual s A samples i j -
            elementwiseTraceResidual s A samples' i j)
        L) :
    rectOpNorm2Le (elementwiseTraceResidual s A samples) L := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  exact
    FiniteProbability.rectOpNorm2Le_of_entrywise_mean_zero_of_copy_diff_rectOpNorm2Le
      P
      (fun samples : ElementwiseTrace m n s =>
        elementwiseTraceResidual s A samples)
      (fun i j =>
        sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_eq_zero
          A hden hs i j)
      samples hdiff

/-- Event that the exact Algorithm 1 residual satisfies a rectangular
    vector-action operator-2 bound.  This is the repository's formal target
    shape for the exact spectral-norm statement in CACM equation (2). -/
def algorithm1ExactSpectralEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω | rectOpNorm2Le (elementwiseTraceResidual s A (X ω)) ε}

/-- Event that all exact independent-copy differences from a realized
Algorithm 1 trace are rectangular operator-bounded by `L`.  This is a
symmetrization support event; it is not itself a probability tail theorem. -/
def algorithm1ExactAllCopyDiffSpectralEvent {m n s : ℕ}
    (A : Fin m → Fin n → ℝ) (L : ℝ) : Set (ElementwiseTrace m n s) :=
  {samples |
    ∀ samples' : ElementwiseTrace m n s,
      rectOpNorm2Le
        (fun i j =>
          elementwiseTraceResidual s A samples i j -
            elementwiseTraceResidual s A samples' i j)
        L}

/-- Independent-copy difference event implies the exact Algorithm 1 spectral
event at the same radius. -/
theorem algorithm1ExactAllCopyDiffSpectralEvent_subset_exactSpectralEvent
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) (L : ℝ) :
    algorithm1ExactAllCopyDiffSpectralEvent (m := m) (n := n) (s := s) A L ⊆
      algorithm1ExactSpectralEvent s A
        (fun samples : ElementwiseTrace m n s => samples) L := by
  intro samples hdiff
  exact
    sqMagTraceProbability_rectOpNorm2Le_elementwiseTraceResidual_of_all_copy_diffs
      A hden hs samples hdiff

/-- Probability transfer from the all-independent-copy-differences event to
the exact Algorithm 1 spectral event.  This is exact-law infrastructure for a
future Khintchine tail on copy differences. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_of_all_copy_diff
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (ρ L : ℝ)
    (hCopy :
      ρ ≤
        (sqMagTraceProbability (steps := s) A hden).eventProb
          (algorithm1ExactAllCopyDiffSpectralEvent
            (m := m) (n := n) (s := s) A L)) :
    ρ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) L) := by
  exact le_trans hCopy
    ((sqMagTraceProbability (steps := s) A hden).eventProb_mono
      (algorithm1ExactAllCopyDiffSpectralEvent_subset_exactSpectralEvent
        A hden hs L))

/-- For the small-entry counterexample, the exact all-copy-difference support
event fails with probability at least the probability of sampling the tiny
entry in the first trace.  Thus this copy-difference event cannot be silently
treated as probability-one for the literal untruncated squared-magnitude law. -/
theorem sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_ge
    (L : ℝ) :
    let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
    sqMagProb A (0 : Fin 1) (1 : Fin 2) ≤
      (sqMagTraceProbability (steps := 1) A
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
        {samples : ElementwiseTrace 1 2 1 |
          samples ∉
            algorithm1ExactAllCopyDiffSpectralEvent
              (m := 1) (n := 2) (s := 1) A L} := by
  classical
  intro A
  let P := sqMagTraceProbability (steps := 1) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let Hit : Set (ElementwiseTrace 1 2 1) :=
    {samples | sampleHits samples (0 : Fin 1) (0 : Fin 1) (1 : Fin 2)}
  let Bad : Set (ElementwiseTrace 1 2 1) :=
    {samples |
      samples ∉
        algorithm1ExactAllCopyDiffSpectralEvent
          (m := 1) (n := 2) (s := 1) A L}
  have hHitProb :
      P.eventProb Hit =
        sqMagProb A (0 : Fin 1) (1 : Fin 2) := by
    simpa [P, Hit, A] using
      sqMagTraceProbability_eventProb_sampleHits
        (algorithm1SmallEntrySupportMatrix L)
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
        (0 : Fin 1) (0 : Fin 1) (1 : Fin 2)
  have hsubset : Hit ⊆ Bad := by
    intro samples hhit hall
    let samplesUnit : ElementwiseTrace 1 2 1 :=
      fun _ : Fin 1 => ((0 : Fin 1), (0 : Fin 2))
    have hsamp0 :
        samples (0 : Fin 1) = ((0 : Fin 1), (1 : Fin 2)) :=
      Prod.ext hhit.1 hhit.2
    have hsamples :
        samples = (fun _ : Fin 1 => ((0 : Fin 1), (1 : Fin 2))) := by
      funext t
      fin_cases t
      exact hsamp0
    have hdiff := hall samplesUnit
    exact
      algorithm1SmallEntrySupportMatrix_trace_residual_small_unit_diff_not_rectOpNorm2Le
        L
        (by
          simpa [A, samplesUnit, hsamples] using hdiff)
  calc
    sqMagProb A (0 : Fin 1) (1 : Fin 2) = P.eventProb Hit := hHitProb.symm
    _ ≤ P.eventProb Bad := P.eventProb_mono hsubset

/-- Positive-probability form of
`sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_ge`. -/
theorem sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_pos
    (L : ℝ) :
    0 <
      (sqMagTraceProbability (steps := 1)
        (algorithm1SmallEntrySupportMatrix L)
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
        {samples : ElementwiseTrace 1 2 1 |
          samples ∉
            algorithm1ExactAllCopyDiffSpectralEvent
              (m := 1) (n := 2) (s := 1)
              (algorithm1SmallEntrySupportMatrix L) L} := by
  have hpos :=
    sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hle :=
    sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_ge
      L
  exact hpos.trans_le hle

/-- Quantitative necessary condition for any high-probability all-copy support
claim on the small-entry family.

If the literal all-copy-differences event for `[1,(|L|+2)^{-1}]` is claimed to
hold with probability at least `1 - delta`, then `delta` must be at least the
exact probability of sampling the tiny entry. -/
theorem sqMagTraceProbability_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_delta_ge
    (L δ : ℝ)
    (hAll :
      1 - δ ≤
        (sqMagTraceProbability (steps := 1)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactAllCopyDiffSpectralEvent
            (m := 1) (n := 2) (s := 1)
            (algorithm1SmallEntrySupportMatrix L) L)) :
    sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2) ≤ δ := by
  classical
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let P := sqMagTraceProbability (steps := 1) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let E : Set (ElementwiseTrace 1 2 1) :=
    algorithm1ExactAllCopyDiffSpectralEvent
      (m := 1) (n := 2) (s := 1) A L
  have hbad :
      sqMagProb A (0 : Fin 1) (1 : Fin 2) ≤ P.eventProb Eᶜ := by
    simpa [A, P, E, Set.mem_compl_iff] using
      sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_ge
        L
  have hsplit := P.eventProb_add_eventProb_compl E
  have hAll' : 1 - δ ≤ P.eventProb E := by
    simpa [A, P, E] using hAll
  have hcompl_le : P.eventProb Eᶜ ≤ δ := by
    linarith
  simpa [A] using hbad.trans hcompl_le

/-- Product-law mass of the trace that samples the tiny entry at every step in
the small-entry obstruction family. -/
theorem sqMagTraceProbMass_algorithm1SmallEntrySupportMatrix_all_tiny
    (s : ℕ) (L : ℝ) :
    sqMagTraceProbMass (algorithm1SmallEntrySupportMatrix L)
      (fun _ : Fin s => ((0 : Fin 1), (1 : Fin 2))) =
      (sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2)) ^ s := by
  classical
  simp [sqMagTraceProbMass]

/-- For any positive sample count, the trace that samples the tiny entry at
every step violates the exact spectral event at radius `L`.  This strengthens
the one-step obstruction from a support-radius failure to a failure of the
Algorithm 1 exact residual event itself. -/
theorem algorithm1SmallEntrySupportMatrix_all_tiny_trace_residual_not_rectOpNorm2Le
    {s : ℕ} (hs : 0 < s) (L : ℝ) :
    ¬ rectOpNorm2Le
      (elementwiseTraceResidual s (algorithm1SmallEntrySupportMatrix L)
        (fun _ : Fin s => ((0 : Fin 1), (1 : Fin 2)))) L := by
  classical
  intro hnorm
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let samplesTiny : ElementwiseTrace 1 2 s :=
    fun _ : Fin s => ((0 : Fin 1), (1 : Fin 2))
  let M : Fin 1 → Fin 2 → ℝ :=
    elementwiseTraceResidual s A samplesTiny
  let x : Fin 2 → ℝ := finiteBasisVec (1 : Fin 2)
  have hxnorm : vecNorm2 x = 1 := by
    simp [x, finiteBasisVec, vecNorm2, vecNorm2Sq]
  have hleft :
      vecNorm2 (rectMatMulVec M x) = |M (0 : Fin 1) (1 : Fin 2)| := by
    simp [M, x, rectMatMulVec, finiteBasisVec, vecNorm2, vecNorm2Sq]
    rw [Real.sqrt_sq_eq_abs]
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  have hbase_ne : |L| + 2 ≠ 0 := ne_of_gt hbase
  have hs_ne : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hentry :
      M (0 : Fin 1) (1 : Fin 2) = -(|L| + 2) := by
    simp [M, A, samplesTiny, elementwiseTraceResidual, elementwiseTraceSketch,
      elementwiseTraceContribution, sampleHits, elementwiseIncrement,
      elementwiseIncrementWithProb, sqMagProb, sqMagProbDen, frobNormSqRect,
      algorithm1SmallEntrySupportMatrix, Finset.sum_const, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [hbase_ne, hs_ne]
    ring_nf
  have hentry_gt : L < |M (0 : Fin 1) (1 : Fin 2)| := by
    rw [hentry, abs_neg, abs_of_pos hbase]
    nlinarith [le_abs_self L]
  have hbound := hnorm x
  rw [hleft, hxnorm, mul_one] at hbound
  exact not_le_of_gt hentry_gt hbound

/-- Quantitative lower bound on exact spectral-event failure for the
small-entry family at any positive sample count: the all-tiny trace alone has
mass `p_tiny ^ s` and is outside the radius-`L` event. -/
theorem sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_ge
    {s : ℕ} (hs : 0 < s) (L : ℝ) :
    let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
    (sqMagProb A (0 : Fin 1) (1 : Fin 2)) ^ s ≤
      (sqMagTraceProbability (steps := s) A
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
        {samples : ElementwiseTrace 1 2 s |
          samples ∉
            algorithm1ExactSpectralEvent s A
              (fun samples : ElementwiseTrace 1 2 s => samples) L} := by
  classical
  intro A
  let P := sqMagTraceProbability (steps := s) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let tinyTrace : ElementwiseTrace 1 2 s :=
    fun _ : Fin s => ((0 : Fin 1), (1 : Fin 2))
  let Bad : Set (ElementwiseTrace 1 2 s) :=
    {samples |
      samples ∉
        algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace 1 2 s => samples) L}
  have htiny_bad : tinyTrace ∈ Bad := by
    intro htiny_good
    exact
      algorithm1SmallEntrySupportMatrix_all_tiny_trace_residual_not_rectOpNorm2Le
        hs L
        (by
          simpa [A, tinyTrace, algorithm1ExactSpectralEvent] using htiny_good)
  have hmass :
      P.prob tinyTrace =
        (sqMagProb A (0 : Fin 1) (1 : Fin 2)) ^ s := by
    simp [P, tinyTrace, A, sqMagTraceProbability,
      sqMagTraceProbMass_algorithm1SmallEntrySupportMatrix_all_tiny]
  rw [← hmass]
  exact FiniteProbability.prob_le_eventProb_of_mem P htiny_bad

/-- Necessary condition for any `1 - delta` lower bound on the exact spectral
event for the small-entry family at a positive sample count.  Even the exact
Algorithm 1 spectral event must pay at least the all-tiny trace mass. -/
theorem sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_delta_ge
    {s : ℕ} (hs : 0 < s) (L δ : ℝ)
    (hEvent :
      1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactSpectralEvent s
            (algorithm1SmallEntrySupportMatrix L)
            (fun samples : ElementwiseTrace 1 2 s => samples) L)) :
    (sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2)) ^ s ≤ δ := by
  classical
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let P := sqMagTraceProbability (steps := s) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let E : Set (ElementwiseTrace 1 2 s) :=
    algorithm1ExactSpectralEvent s A
      (fun samples : ElementwiseTrace 1 2 s => samples) L
  have hbad :
      (sqMagProb A (0 : Fin 1) (1 : Fin 2)) ^ s ≤ P.eventProb Eᶜ := by
    simpa [A, P, E, Set.mem_compl_iff] using
      sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_ge
        hs L
  have hsplit := P.eventProb_add_eventProb_compl E
  have hEvent' : 1 - δ ≤ P.eventProb E := by
    simpa [A, P, E] using hEvent
  have hcompl_le : P.eventProb Eᶜ ≤ δ := by
    linarith
  simpa [A] using hbad.trans hcompl_le


































/-- Logarithmic necessary condition for a `1 - delta` exact spectral-event
claim on the Algorithm 1 small-entry obstruction family.  The displayed
inequality is the order form of the all-tiny mass condition
`p_tiny^s <= delta`. -/
theorem sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_log_delta_le
    {s : ℕ} (hs : 0 < s) (L δ : ℝ) (hδ : 0 < δ)
    (hEvent :
      1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactSpectralEvent s
            (algorithm1SmallEntrySupportMatrix L)
            (fun samples : ElementwiseTrace 1 2 s => samples) L)) :
    let pTiny : ℝ :=
      sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2)
    Real.log (1 / δ) ≤ (s : ℝ) * Real.log (1 / pTiny) := by
  classical
  intro pTiny
  have hp : 0 < pTiny := by
    simpa [pTiny] using sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hpow : pTiny ^ s ≤ δ := by
    simpa [pTiny] using
      sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_delta_ge
        hs L δ hEvent
  exact log_inv_delta_le_nat_mul_log_inv_of_pow_le hp hδ hpow

/-- Sample-count lower-bound form of the Algorithm 1 all-tiny obstruction.
The small-entry probability is strictly between zero and one, so any `1 -
delta` exact spectral-event claim on this family forces the displayed divided
logarithmic lower bound on `s`. -/
theorem sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_sample_count_ge
    {s : ℕ} (hs : 0 < s) (L δ : ℝ) (hδ : 0 < δ)
    (hEvent :
      1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactSpectralEvent s
            (algorithm1SmallEntrySupportMatrix L)
            (fun samples : ElementwiseTrace 1 2 s => samples) L)) :
    let pTiny : ℝ :=
      sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2)
    Real.log (1 / δ) / Real.log (1 / pTiny) ≤ (s : ℝ) := by
  classical
  intro pTiny
  have hp : 0 < pTiny := by
    simpa [pTiny] using sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hp_lt_one : pTiny < 1 := by
    simpa [pTiny] using sqMagProb_algorithm1SmallEntrySupportMatrix_small_lt_one L
  have hpow : pTiny ^ s ≤ δ := by
    simpa [pTiny] using
        sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_delta_ge
        hs L δ hEvent
  exact log_inv_delta_div_log_inv_le_nat_of_pow_le hp hp_lt_one hδ hpow

/-- Direct incompatibility form of the all-tiny obstruction.

If the claimed failure budget `delta` is smaller than the exact all-tiny trace
mass `p_tiny ^ s`, then the radius-`L` exact Algorithm 1 spectral event cannot
hold with probability at least `1 - delta` on the small-entry family. -/
theorem sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_delta_lt_pow
    {s : ℕ} (hs : 0 < s) (L δ : ℝ)
    (hδ_small :
      let pTiny : ℝ :=
        sqMagProb (algorithm1SmallEntrySupportMatrix L)
          (0 : Fin 1) (1 : Fin 2)
      δ < pTiny ^ s) :
    ¬
      (1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactSpectralEvent s
            (algorithm1SmallEntrySupportMatrix L)
            (fun samples : ElementwiseTrace 1 2 s => samples) L)) := by
  classical
  intro hEvent
  let pTiny : ℝ :=
    sqMagProb (algorithm1SmallEntrySupportMatrix L)
      (0 : Fin 1) (1 : Fin 2)
  have hpow_le : pTiny ^ s ≤ δ := by
    simpa [pTiny] using
      sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_delta_ge
        hs L δ hEvent
  have hδ_small' : δ < pTiny ^ s := by
    simpa [pTiny] using hδ_small
  exact (not_lt_of_ge hpow_le) hδ_small'

/-- Divided-log incompatibility form of the all-tiny obstruction.

For positive `delta`, if the sample count is strictly below the exact
lower-bound threshold
`log (1 / delta) / log (1 / p_tiny)`, then the radius-`L` exact Algorithm 1
spectral event cannot have probability at least `1 - delta` on the
small-entry family. -/
theorem sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_sample_count_lt
    {s : ℕ} (hs : 0 < s) (L δ : ℝ) (hδ : 0 < δ)
    (hs_lt :
      let pTiny : ℝ :=
        sqMagProb (algorithm1SmallEntrySupportMatrix L)
          (0 : Fin 1) (1 : Fin 2)
      (s : ℝ) < Real.log (1 / δ) / Real.log (1 / pTiny)) :
    ¬
      (1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactSpectralEvent s
            (algorithm1SmallEntrySupportMatrix L)
            (fun samples : ElementwiseTrace 1 2 s => samples) L)) := by
  classical
  intro hEvent
  let pTiny : ℝ :=
    sqMagProb (algorithm1SmallEntrySupportMatrix L)
      (0 : Fin 1) (1 : Fin 2)
  have hlower :
      Real.log (1 / δ) / Real.log (1 / pTiny) ≤ (s : ℝ) := by
    simpa [pTiny] using
      sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_sample_count_ge
        hs L δ hδ hEvent
  have hs_lt' :
      (s : ℝ) < Real.log (1 / δ) / Real.log (1 / pTiny) := by
    simpa [pTiny] using hs_lt
  exact (not_lt_of_ge hlower) hs_lt'

/-- Success-probability upper bound from the all-tiny obstruction.

For the literal small-entry family, the exact radius-`L` spectral event has
success probability at most `1 - p_tiny ^ s`, because the all-tiny trace alone
has exact product-law mass `p_tiny ^ s` and lies outside the event. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_le_one_sub_pow
    {s : ℕ} (hs : 0 < s) (L : ℝ) :
    let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
    let pTiny : ℝ := sqMagProb A (0 : Fin 1) (1 : Fin 2)
    (sqMagTraceProbability (steps := s) A
      (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
      (algorithm1ExactSpectralEvent s A
        (fun samples : ElementwiseTrace 1 2 s => samples) L) ≤
      1 - pTiny ^ s := by
  classical
  intro A pTiny
  let P := sqMagTraceProbability (steps := s) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let E : Set (ElementwiseTrace 1 2 s) :=
    algorithm1ExactSpectralEvent s A
      (fun samples : ElementwiseTrace 1 2 s => samples) L
  have hbad :
      pTiny ^ s ≤ P.eventProb Eᶜ := by
    simpa [A, pTiny, P, E, Set.mem_compl_iff] using
      sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_ge
        hs L
  have hsplit := P.eventProb_add_eventProb_compl E
  nlinarith

/-- Strict form of the all-tiny success-probability obstruction.

For every positive sample count, the exact radius-`L` spectral event for the
literal small-entry family has probability strictly below one. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_lt_one
    {s : ℕ} (hs : 0 < s) (L : ℝ) :
    let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
    (sqMagTraceProbability (steps := s) A
      (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
      (algorithm1ExactSpectralEvent s A
        (fun samples : ElementwiseTrace 1 2 s => samples) L) < 1 := by
  classical
  intro A
  let pTiny : ℝ := sqMagProb A (0 : Fin 1) (1 : Fin 2)
  have hp : 0 < pTiny := by
    simpa [A, pTiny] using sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hpow_pos : 0 < pTiny ^ s := pow_pos hp s
  have hle :
      (sqMagTraceProbability (steps := s) A
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace 1 2 s => samples) L) ≤
        1 - pTiny ^ s := by
    simpa [A, pTiny] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_le_one_sub_pow
        hs L
  nlinarith

/-- Fixed-sample impossibility form.

For any fixed positive sample count and radius `L`, there is a positive
failure budget `delta` for which the literal small-entry exact spectral event
cannot have probability at least `1 - delta`. -/
theorem exists_delta_not_sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry
    {s : ℕ} (hs : 0 < s) (L : ℝ) :
    ∃ δ : ℝ,
      0 < δ ∧
      ¬
        (1 - δ ≤
          (sqMagTraceProbability (steps := s)
            (algorithm1SmallEntrySupportMatrix L)
            (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
            (algorithm1ExactSpectralEvent s
              (algorithm1SmallEntrySupportMatrix L)
              (fun samples : ElementwiseTrace 1 2 s => samples) L)) := by
  classical
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let pTiny : ℝ := sqMagProb A (0 : Fin 1) (1 : Fin 2)
  have hp : 0 < pTiny := by
    simpa [A, pTiny] using sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hpow_pos : 0 < pTiny ^ s := pow_pos hp s
  refine ⟨pTiny ^ s / 2, ?_, ?_⟩
  · nlinarith
  · have hsmall : pTiny ^ s / 2 < pTiny ^ s := by
      nlinarith
    exact
      sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_delta_lt_pow
        (s := s) hs L (pTiny ^ s / 2)
        (by simpa [A, pTiny] using hsmall)

/-- A small numerical logarithm certificate used by the concrete Algorithm 1
source-budget obstruction below.  The proof uses only `2 ≤ exp 1`, so it is a
coarse exact certificate rather than an external decimal approximation. -/
theorem real_log_180000_le_18 : Real.log (180000 : ℝ) ≤ 18 := by
  have hpos : (0 : ℝ) < 180000 := by norm_num
  rw [Real.log_le_iff_le_exp hpos]
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have hpow : (2 : ℝ) ^ 18 ≤ (Real.exp 1) ^ 18 :=
    pow_le_pow_left₀ (by norm_num) h2e 18
  have hexp : (Real.exp 1) ^ 18 = Real.exp 18 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h180 : (180000 : ℝ) ≤ (2 : ℝ) ^ 18 := by norm_num
  exact h180.trans (by simpa [hexp] using hpow)

/-- The concrete rectangular source-style budget at `m = 1`, `n = 2`,
`s = 1`, radius `100`, and failure budget `1/30000`.

This predicate is exact arithmetic only.  It records the budget surface whose
source-uniform use is refuted by the concrete small-entry witness below. -/
def algorithm1RectSourceBudget_1_2_100_one_div_30000
    (A : Fin 1 → Fin 2 → ℝ) : Prop :=
  4 *
      (let M : ℝ := max (1 : ℝ) (2 : ℝ)
       let R : ℝ := Real.sqrt ((1 : ℝ) * (2 : ℝ))
       let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
       C) *
      frobNormSqRect A *
      Real.log ((2 * ((1 : ℝ) + (2 : ℝ))) / ((1 : ℝ) / 30000)) ≤
    (1 : ℝ) * (100 : ℝ) ^ 2

/-- In the concrete small-entry witness with radius `100` and
`δ = 1/30000`, the tiny entry has one-step sampling probability larger than
`δ`. -/
theorem algorithm1SmallEntrySupportMatrix_100_small_prob_gt_one_div_30000 :
    (1 / 30000 : ℝ) <
      sqMagProb (algorithm1SmallEntrySupportMatrix (100 : ℝ))
        (0 : Fin 1) (1 : Fin 2) := by
  norm_num [sqMagProb, sqMagProbDen, frobNormSqRect,
    algorithm1SmallEntrySupportMatrix]

/-- The concrete small-entry witness satisfies the rectangular source-style
sample-budget inequality with `m = 1`, `n = 2`, `s = 1`, radius `eps = 100`,
and `δ = 1/30000`.

This theorem is exact arithmetic/probability only.  It says the displayed
source-budget premise can be true for the literal untruncated law even though
the spectral event lower bound is refuted by the next theorem. -/
theorem algorithm1SmallEntrySupportMatrix_100_rect_source_budget_one_div_30000 :
    algorithm1RectSourceBudget_1_2_100_one_div_30000
      (algorithm1SmallEntrySupportMatrix (100 : ℝ)) := by
  have hlog : Real.log (180000 : ℝ) ≤ 18 := real_log_180000_le_18
  have hC :
      (let M : ℝ := max (1 : ℝ) (2 : ℝ)
       let R : ℝ := Real.sqrt ((1 : ℝ) * (2 : ℝ))
       let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
       C) ≤ 7 := by
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
      rw [← sq, Real.sq_sqrt]
      norm_num
    calc
      (let M : ℝ := max (1 : ℝ) (2 : ℝ)
       let R : ℝ := Real.sqrt ((1 : ℝ) * (2 : ℝ))
       let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
       C)
          = 4 + ((4 * Real.sqrt 2) / 3) * Real.sqrt 2 := by
              norm_num [max_eq_right]
      _ = 4 + 8 / 3 := by
              rw [div_mul_eq_mul_div, mul_assoc, hsqrt]
              norm_num
      _ ≤ 7 := by norm_num
  have hF :
      frobNormSqRect (algorithm1SmallEntrySupportMatrix (100 : ℝ)) ≤ 2 := by
    norm_num [frobNormSqRect, algorithm1SmallEntrySupportMatrix]
  have hnonnegC :
      0 ≤
        (let M : ℝ := max (1 : ℝ) (2 : ℝ)
         let R : ℝ := Real.sqrt ((1 : ℝ) * (2 : ℝ))
         let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
         C) := by positivity
  have hnonnegF :
      0 ≤ frobNormSqRect (algorithm1SmallEntrySupportMatrix (100 : ℝ)) :=
    frobNormSqRect_nonneg _
  have hlog_nonneg : 0 ≤ Real.log (180000 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hmain :
      4 *
          (let M : ℝ := max (1 : ℝ) (2 : ℝ)
           let R : ℝ := Real.sqrt ((1 : ℝ) * (2 : ℝ))
           let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
           C) *
          frobNormSqRect (algorithm1SmallEntrySupportMatrix (100 : ℝ)) *
          Real.log (180000 : ℝ) ≤
        4 * 7 * 2 * 18 := by
    gcongr
  have htarget : 4 * 7 * 2 * 18 ≤ (1 : ℝ) * (100 : ℝ) ^ 2 := by
    norm_num
  have harg :
      (2 * ((1 : ℝ) + (2 : ℝ))) / ((1 : ℝ) / 30000) =
        (180000 : ℝ) := by
    norm_num
  unfold algorithm1RectSourceBudget_1_2_100_one_div_30000
  rw [harg]
  exact hmain.trans htarget

/-- Concrete source-budget incompatibility witness for the literal
untruncated Algorithm 1 law.

For `m = 1`, `n = 2`, `s = 1`, radius `100`, and `δ = 1/30000`, the usual
rectangular source-style sample budget is true, but the exact squared-magnitude
law cannot satisfy the advertised spectral-event lower bound.  Thus a literal
source-uniform equation-(2) theorem cannot be justified by this source budget
alone on inputs with arbitrarily small nonzero entries. -/
theorem sqMagTraceProbability_not_algorithm1ExactSpectralEvent_rect_source_budget_witness :
    let A : Fin 1 → Fin 2 → ℝ :=
      algorithm1SmallEntrySupportMatrix (100 : ℝ)
    algorithm1RectSourceBudget_1_2_100_one_div_30000 A ∧
      ¬
        (1 - (1 / 30000 : ℝ) ≤
          (sqMagTraceProbability (steps := 1) A
            (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos (100 : ℝ))).eventProb
            (algorithm1ExactSpectralEvent 1 A
              (fun samples : ElementwiseTrace 1 2 1 => samples) (100 : ℝ))) := by
  classical
  intro A
  refine ⟨?_, ?_⟩
  · simpa [A] using
      algorithm1SmallEntrySupportMatrix_100_rect_source_budget_one_div_30000
  · have hδ_small :
        let pTiny : ℝ := sqMagProb A (0 : Fin 1) (1 : Fin 2)
        (1 / 30000 : ℝ) < pTiny ^ 1 := by
      norm_num [A, sqMagProb, sqMagProbDen, frobNormSqRect,
        algorithm1SmallEntrySupportMatrix]
    exact
      sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_delta_lt_pow
        (s := 1) (by norm_num) (100 : ℝ) (1 / 30000 : ℝ) hδ_small

/-- No theorem with only the concrete rectangular source-style budget as
premise can imply the advertised literal exact Algorithm 1 success probability
for all inputs at these parameters.

This is a schema-refutation wrapper around the concrete small-entry witness:
the probability law is exact, no floating-point quantity is computed, and the
failure is caused by the literal untruncated squared-magnitude law assigning
positive mass to the tiny entry. -/
theorem not_forall_algorithm1ExactSpectralEvent_of_rect_source_budget_one_div_30000 :
    ¬
      (∀ (A : Fin 1 → Fin 2 → ℝ) (hden : 0 < sqMagProbDen A),
        algorithm1RectSourceBudget_1_2_100_one_div_30000 A →
        1 - (1 / 30000 : ℝ) ≤
          (sqMagTraceProbability (steps := 1) A hden).eventProb
            (algorithm1ExactSpectralEvent 1 A
              (fun samples : ElementwiseTrace 1 2 1 => samples) (100 : ℝ))) := by
  classical
  intro hschema
  let A : Fin 1 → Fin 2 → ℝ :=
    algorithm1SmallEntrySupportMatrix (100 : ℝ)
  have hbudget :
      algorithm1RectSourceBudget_1_2_100_one_div_30000 A := by
    simpa [A] using
      algorithm1SmallEntrySupportMatrix_100_rect_source_budget_one_div_30000
  have hδ_small :
      let pTiny : ℝ := sqMagProb A (0 : Fin 1) (1 : Fin 2)
      (1 / 30000 : ℝ) < pTiny ^ 1 := by
    norm_num [A, sqMagProb, sqMagProbDen, frobNormSqRect,
      algorithm1SmallEntrySupportMatrix]
  have hnot :
      ¬
        (1 - (1 / 30000 : ℝ) ≤
          (sqMagTraceProbability (steps := 1) A
            (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos (100 : ℝ))).eventProb
            (algorithm1ExactSpectralEvent 1 A
              (fun samples : ElementwiseTrace 1 2 1 => samples) (100 : ℝ))) := by
    simpa [A] using
      sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_delta_lt_pow
        (s := 1) (by norm_num) (100 : ℝ) (1 / 30000 : ℝ) hδ_small
  exact hnot
    (hschema A
      (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos (100 : ℝ))
      hbudget)

/-- Rademacher finite-test tail for fixed Algorithm 1 stepwise copy
differences.

Fix two exact Algorithm 1 traces.  If the quadratic-form coefficients of the
stepwise self-adjoint dilation differences have variance proxy `σ a ^ 2` for
each finite test vector `z a`, then exact Rademacher signs over the step index
satisfy the simultaneous two-sided Hoeffding event.  This is the first
Algorithm-1-specific adapter from copy differences to the generic finite-test
matrix-Khintchine primitive; it is exact-probability and exact-arithmetic only. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteQuadraticForm_rademacher_signed_rectSelfAdjointDilation_sampleResidualIncrement_diff_le_ge_one_sub_sum_two_mul_exp_neg_sq_div
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ)
    (samples samples' : ElementwiseTrace m n s)
    (z : ι → Fin m ⊕ Fin n → ℝ) (T σ : ι → ℝ)
    (hT : ∀ a : ι, 0 < T a) (hσ : ∀ a : ι, 0 < σ a)
    (hvar :
      ∀ a : ι,
        (∑ t : Fin s,
          finiteQuadraticForm
            (fun b c : Fin m ⊕ Fin n =>
              rectSelfAdjointDilation
                (fun i j =>
                  elementwiseSampleResidualIncrement s A (samples t) i j -
                    elementwiseSampleResidualIncrement s A (samples' t) i j)
                b c)
            (z a) ^ 2) ≤ σ a ^ 2) :
    1 - (∑ a : ι, 2 * Real.exp (-(T a ^ 2 / (2 * σ a ^ 2)))) ≤
      (rademacherTraceProbability s).eventProb
        {ω | ∀ a : ι,
          |finiteQuadraticForm
            (fun b c : Fin m ⊕ Fin n =>
              ∑ t : Fin s,
                rademacherSignVector ω t *
                  rectSelfAdjointDilation
                    (fun i j =>
                      elementwiseSampleResidualIncrement s A (samples t) i j -
                        elementwiseSampleResidualIncrement s A (samples' t) i j)
                    b c)
            (z a)| ≤ T a} := by
  classical
  simpa using
    rademacherTraceProbability_eventProb_forall_abs_finiteQuadraticForm_signed_matrix_sum_fintype_le_ge_one_sub_sum_two_mul_exp_neg_sq_div
      (m := s) (κ := Fin m ⊕ Fin n) (ι := ι)
      (M := fun t b c =>
        rectSelfAdjointDilation
          (fun i j =>
            elementwiseSampleResidualIncrement s A (samples t) i j -
              elementwiseSampleResidualIncrement s A (samples' t) i j)
          b c)
      (z := z) (T := T) (σ := σ) hT hσ hvar

/-- Cover-to-operator Rademacher tail for fixed Algorithm 1 copy-difference
increments.

This theorem composes the finite-test Rademacher quadratic-form tail with a
supplied finite unit-ball cover of the self-adjoint-dilation space and a coarse
operator radius for each signed dilation sum.  It is exact-law/exact-arithmetic
infrastructure: no sampling probabilities are approximated and no
floating-point computation appears.  The coarse radius is an explicit remaining
deterministic input, so this is not a final source-uniform CACM equation-(2)
spectral theorem. -/
theorem rademacherTraceProbability_eventProb_rectOpNorm2Le_signed_sampleResidualIncrement_diff_ge_one_sub_sum_two_mul_exp_neg_sq_div_of_finiteUnitBallCover
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ)
    (samples samples' : ElementwiseTrace m n s)
    (net : ι → Fin m ⊕ Fin n → ℝ)
    (ρ η L : ℝ) (σ : ι → ℝ)
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hσ : ∀ a : ι, 0 < σ a)
    (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hcoarse :
      ∀ ω : RademacherTrace s,
        finiteOpNorm2Le
          (fun b c : Fin m ⊕ Fin n =>
            ∑ t : Fin s,
              rademacherSignVector ω t *
                rectSelfAdjointDilation
                  (fun i j =>
                    elementwiseSampleResidualIncrement s A (samples t) i j -
                      elementwiseSampleResidualIncrement s A (samples' t) i j)
                  b c)
          L)
    (hvar :
      ∀ a : ι,
        (∑ t : Fin s,
          finiteQuadraticForm
            (fun b c : Fin m ⊕ Fin n =>
              rectSelfAdjointDilation
                (fun i j =>
                  elementwiseSampleResidualIncrement s A (samples t) i j -
                    elementwiseSampleResidualIncrement s A (samples' t) i j)
                b c)
            (net a) ^ 2) ≤ σ a ^ 2) :
    1 - (∑ a : ι, 2 * Real.exp (-(η ^ 2 / (2 * σ a ^ 2)))) ≤
      (rademacherTraceProbability s).eventProb
        {ω | rectOpNorm2Le
          (fun i j =>
            ∑ t : Fin s,
              rademacherSignVector ω t *
                (elementwiseSampleResidualIncrement s A (samples t) i j -
                  elementwiseSampleResidualIncrement s A (samples' t) i j))
          (η + L * (2 * ρ + ρ ^ 2))} := by
  classical
  let P := rademacherTraceProbability s
  let D : RademacherTrace s → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun ω b c =>
      ∑ t : Fin s,
        rademacherSignVector ω t *
          rectSelfAdjointDilation
            (fun i j =>
              elementwiseSampleResidualIncrement s A (samples t) i j -
                elementwiseSampleResidualIncrement s A (samples' t) i j)
            b c
  let R : RademacherTrace s → Fin m → Fin n → ℝ :=
    fun ω i j =>
      ∑ t : Fin s,
        rademacherSignVector ω t *
          (elementwiseSampleResidualIncrement s A (samples t) i j -
            elementwiseSampleResidualIncrement s A (samples' t) i j)
  let Etest : Set (RademacherTrace s) :=
    {ω | ∀ a : ι, |finiteQuadraticForm (D ω) (net a)| ≤ η}
  let Eop : Set (RademacherTrace s) :=
    {ω | rectOpNorm2Le (R ω) (η + L * (2 * ρ + ρ ^ 2))}
  have htest :
      1 - (∑ a : ι, 2 * Real.exp (-(η ^ 2 / (2 * σ a ^ 2)))) ≤
        P.eventProb Etest := by
    simpa [P, Etest, D] using
      sqMagTraceProbability_eventProb_forall_abs_finiteQuadraticForm_rademacher_signed_rectSelfAdjointDilation_sampleResidualIncrement_diff_le_ge_one_sub_sum_two_mul_exp_neg_sq_div
        (A := A) samples samples' (z := net) (T := fun _a : ι => η)
        (σ := σ) (by intro _; exact hη) hσ hvar
  have hsubset : Etest ⊆ Eop := by
    intro ω hω
    have hnet :
        ∀ a : ι, finiteQuadraticForm (D ω) (net a) ≤ η := by
      intro a
      exact (le_abs_self (finiteQuadraticForm (D ω) (net a))).trans (hω a)
    have hloewner :
        finiteLoewnerLe (D ω)
          (fun b c : Fin m ⊕ Fin n =>
            (η + L * (2 * ρ + ρ ^ 2)) * finiteIdMatrix b c) := by
      exact
        finiteLoewnerLe_of_finite_unit_ball_cover_quadraticForm
          (D ω) net hcover hnet (hcoarse ω) hL hρ
    have hD_eq :
        D ω = rectSelfAdjointDilation (R ω) := by
      ext b c
      cases b <;> cases c <;> simp [D, R, rectSelfAdjointDilation]
    have hC_nonneg : 0 ≤ η + L * (2 * ρ + ρ ^ 2) := by
      have hshape : 0 ≤ 2 * ρ + ρ ^ 2 := by nlinarith [hρ, sq_nonneg ρ]
      exact add_nonneg (le_of_lt hη) (mul_nonneg hL hshape)
    have hloewnerR :
        finiteLoewnerLe (rectSelfAdjointDilation (R ω))
          (fun b c : Fin m ⊕ Fin n =>
            (η + L * (2 * ρ + ρ ^ 2)) * finiteIdMatrix b c) := by
      simpa [hD_eq] using hloewner
    exact
      rectOpNorm2Le_of_selfAdjointDilation_loewnerLe_scalar_id
        (R ω) hC_nonneg hloewnerR
  exact htest.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Event that the exact truncated Algorithm 1 sketch is close to the
    original matrix.  This is the event shape used by the
    Drineas--Zouzias-style source-aligned variant: the sketch is built from
    `elementwiseTruncate tau A`, but the residual is measured against `A`. -/
def algorithm1ExactTruncatedSpectralEvent {Ω : Type*} {m n steps : ℕ}
    (tau : ℝ) (s : ℕ) (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) : Set Ω :=
  {ω | rectOpNorm2Le (elementwiseTruncatedTraceResidual tau s A (X ω)) ε}

/-- Event that the self-adjoint dilation of the exact Algorithm 1 residual
    satisfies a square vector-action operator bound.  This is the natural
    interface for future matrix Bernstein/Khintchine theorems, which are often
    stated for self-adjoint matrices. -/
def algorithm1ExactDilationEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω | finiteOpNorm2Le
      (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω))) ε}

/-- Event that the self-adjoint dilation of the exact Algorithm 1 residual is
    one-sided Loewner-bounded by `ε I`.  This is the natural output shape of
    largest-eigenvalue matrix concentration; for self-adjoint dilations it is
    already enough to imply the rectangular residual operator bound. -/
def algorithm1ExactDilationUpperEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω |
    finiteLoewnerLe
      (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω)))
      (fun a b => ε * finiteIdMatrix a b)}

/-- Scaled eigenvalue event produced by the current trace-MGF tail layer:
    every Hermitian eigenvalue of `theta * D(A - Atilde)` has absolute value
    below `T`.  The deterministic theorem below converts this event into the
    rectangular spectral event at radius `T / theta` when `theta > 0`. -/
noncomputable def algorithm1ScaledDilationAbsEigenvalueEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (theta T : ℝ) : Set Ω :=
  {ω |
    ∀ a : Fin m ⊕ Fin n,
      |finiteHermitianEigenvalues
        (fun b c : Fin m ⊕ Fin n =>
          theta *
            rectSelfAdjointDilation
              (elementwiseTraceResidual s A (X ω)) b c)
        (by
          intro b c
          exact congrArg (fun x => theta * x)
            (rectSelfAdjointDilation_symmetric
              (elementwiseTraceResidual s A (X ω)) b c))
        a| < T}

/-- Eigenvalue form of the one-sided self-adjoint-dilation upper event:
    every Hermitian eigenvalue of `ε I - D(A - Atilde)` is nonnegative.  This
    is only a deterministic restatement of the Loewner event; it is useful as a
    target shape for future largest-eigenvalue concentration work. -/
noncomputable def algorithm1ExactDilationEigenUpperEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω |
    ∀ a : Fin m ⊕ Fin n,
      0 ≤ finiteScalarUpperDiffEigenvalues
        (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω)))
        (rectSelfAdjointDilation_symmetric
          (elementwiseTraceResidual s A (X ω)))
        ε a}

/-- Single-eigenvalue component of the dilation eigenvalue upper event.  A
    union-bound argument over these events gives the full eigenvalue event. -/
noncomputable def algorithm1ExactDilationEigenUpperIndexEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ)
    (a : Fin m ⊕ Fin n) : Set Ω :=
  {ω |
    0 ≤ finiteScalarUpperDiffEigenvalues
      (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω)))
      (rectSelfAdjointDilation_symmetric
        (elementwiseTraceResidual s A (X ω)))
      ε a}

/-- Event that the square of the self-adjoint dilation of the exact residual
    is Loewner-bounded by `ε^2 I`.  This is a convenient target shape for
    future matrix-concentration/moment arguments; the theorem below converts it
    to the dilation operator event. -/
def algorithm1ExactDilationSquareEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω |
    finiteLoewnerLe
      (finiteMatMul
        (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω)))
        (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω))))
      (fun a b => ε ^ 2 * finiteIdMatrix a b)}

/-- Event that the exact Algorithm 1 residual satisfies a rectangular
    Frobenius-norm bound. This is weaker than the CACM equation (2) spectral
    target as a theorem shape, but it gives a fully deterministic bridge to the
    repository's rectangular vector-action operator event. -/
noncomputable def algorithm1ExactFrobEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω | frobNormRect (elementwiseTraceResidual s A (X ω)) ≤ ε}

/-- Event that every entry of the exact Algorithm 1 residual is bounded by
    `τ` in absolute value.  This is a scalar-entry layer used by union-bound
    arguments; it is weaker than a matrix Bernstein/Khintchine spectral event. -/
def algorithm1ExactEntrywiseEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (τ : ℝ) :
    Set Ω :=
  {ω | ∀ i j, |elementwiseTraceResidual s A (X ω) i j| ≤ τ}

/-- Event that the floating-point Algorithm 1 residual satisfies the exact
    spectral budget plus the Frobenius norm of an entrywise perturbation
    budget. -/
noncomputable def algorithm1FlSpectralEvent {Ω : Type*} (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (ε : ℝ)
    (B : Fin m → Fin n → ℝ) : Set Ω :=
  {ω | rectOpNorm2Le (fl_elementwiseTraceResidual fp s A (X ω))
      (ε + frobNormRect B)}

/-- Event that the exact residual using a supplied exact probability table
    satisfies a rectangular operator bound. -/
noncomputable def algorithm1ExactSpectralEventWithProb {Ω : Type*}
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) : Set Ω :=
  {ω | rectOpNorm2Le (elementwiseTraceResidualWithProb s A p (X ω)) ε}

/-- Floating-point event for Algorithm 1 when the sampler uses a supplied exact
    probability table. The displayed radius has separate additive budgets for
    changing from the canonical squared-magnitude law to `p` and for
    floating-point arithmetic while using `p` exactly. -/
noncomputable def algorithm1FlSpectralEventWithProb {Ω : Type*}
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (ε : ℝ)
    (C B : Fin m → Fin n → ℝ) : Set Ω :=
  {ω | rectOpNorm2Le (fl_elementwiseTraceResidualWithProb fp s A p (X ω))
      (ε + frobNormRect C + frobNormRect B)}

/-- Floating-point event for the truncated Algorithm 1 sketch against the
    original matrix. -/
noncomputable def algorithm1FlTruncatedSpectralEvent {Ω : Type*}
    (fp : FPModel) {m n steps : ℕ} (tau : ℝ) (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (B : Fin m → Fin n → ℝ) : Set Ω :=
  {ω | rectOpNorm2Le (fl_elementwiseTruncatedTraceResidual fp tau s A (X ω))
      (ε + frobNormRect B)}

/-- Floating-point event for the truncated Algorithm 1 sketch when the sampler
    uses a supplied exact probability table for the
    truncated matrix. -/
noncomputable def algorithm1FlTruncatedSpectralEventWithProb {Ω : Type*}
    (fp : FPModel) {m n steps : ℕ} (tau : ℝ) (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (ε : ℝ)
    (C B : Fin m → Fin n → ℝ) : Set Ω :=
  {ω |
    rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidualWithProb fp tau s A p (X ω))
      (ε + frobNormRect C + frobNormRect B)}

-- ============================================================
-- Deterministic floating-point transfer
-- ============================================================
















































































































































































































/-- For the source-aligned square truncated variant, a half-budget spectral
    residual event for the truncated matrix implies an `eps`-budget residual
    event against the original matrix. -/
theorem algorithm1ExactSpectralEvent_truncated_half_subset_original
    {Ω : Type*} {n steps : ℕ} (s : ℕ) (A : Fin n → Fin n → ℝ)
    (X : Ω → ElementwiseTrace n n steps) {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 0 < n) :
    algorithm1ExactSpectralEvent s
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A) X (eps / 2) ⊆
      algorithm1ExactTruncatedSpectralEvent (eps / (2 * (n : ℝ))) s A X eps := by
  intro ω h
  exact elementwiseTruncatedTraceResidual_square_rectOpNorm2Le_of_half
    s A (X ω) heps hn h

/-- Probability transfer for the source-aligned square truncated variant.  This
    does not prove the matrix-Bernstein residual event for the truncated matrix;
    it records the deterministic truncation step needed once that event is
    proved. -/
theorem probability_algorithm1_exact_truncated_spectral_of_sampled_half
    {Ω : Type*} [Fintype Ω] {n steps : ℕ} (s : ℕ)
    (A : Fin n → Fin n → ℝ) (X : Ω → ElementwiseTrace n n steps)
    (Pr : FiniteProbability Ω) (ρ : ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 0 < n)
    (hProb :
      ρ ≤ Pr.eventProb
        (algorithm1ExactSpectralEvent s
          (elementwiseTruncate (eps / (2 * (n : ℝ))) A) X (eps / 2))) :
    ρ ≤ Pr.eventProb
      (algorithm1ExactTruncatedSpectralEvent
        (eps / (2 * (n : ℝ))) s A X eps) := by
  exact hProb.trans
    (Pr.eventProb_mono
      (algorithm1ExactSpectralEvent_truncated_half_subset_original
        s A X heps hn))

/-- Floating-point event transfer for the source-aligned square truncated
    variant.  A half-budget exact event for the truncated matrix transfers to
    an `eps + ||B||_F` floating-point event against the original matrix, provided
    the rounded truncated sketch has the advertised entrywise perturbation
    budget. -/
theorem algorithm1ExactSpectralEvent_truncated_half_subset_fl_original
    (fp : FPModel) {Ω : Type*} {n steps : ℕ} (s : ℕ)
    (A : Fin n → Fin n → ℝ) (X : Ω → ElementwiseTrace n n steps)
    {eps : ℝ} (B : Fin n → Fin n → ℝ)
    (heps : 0 ≤ eps) (hn : 0 < n)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hPoint :
      ∀ ω i j,
        |fl_elementwiseTraceSketch fp s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) (X ω) i j -
          elementwiseTraceSketch s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) (X ω) i j| ≤ B i j) :
    algorithm1ExactSpectralEvent s
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A) X (eps / 2) ⊆
      algorithm1FlTruncatedSpectralEvent fp (eps / (2 * (n : ℝ))) s A X eps B := by
  intro ω h
  have hTruncFrob :
      frobNormRect
        (fun i j =>
          A i j - elementwiseTruncate (eps / (2 * (n : ℝ))) A i j) ≤
        eps / 2 :=
    elementwiseTruncate_square_error_frobNormRect_le_half A heps hn
  have hfl :=
    fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
      fp (eps / (2 * (n : ℝ))) s A (X ω) B hB_nonneg h (hPoint ω) hTruncFrob
  change rectOpNorm2Le
    (fl_elementwiseTruncatedTraceResidual fp (eps / (2 * (n : ℝ))) s A (X ω))
    (eps + frobNormRect B)
  convert hfl using 1
  ring

/-- Probability transfer to the floating-point source-aligned truncated event. -/
theorem probability_algorithm1_fl_truncated_spectral_of_sampled_half
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {n steps : ℕ} (s : ℕ)
    (A : Fin n → Fin n → ℝ) (X : Ω → ElementwiseTrace n n steps)
    (Pr : FiniteProbability Ω) (ρ : ℝ) {eps : ℝ}
    (B : Fin n → Fin n → ℝ)
    (heps : 0 ≤ eps) (hn : 0 < n)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hPoint :
      ∀ ω i j,
        |fl_elementwiseTraceSketch fp s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) (X ω) i j -
          elementwiseTraceSketch s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hProb :
      ρ ≤ Pr.eventProb
        (algorithm1ExactSpectralEvent s
          (elementwiseTruncate (eps / (2 * (n : ℝ))) A) X (eps / 2))) :
    ρ ≤ Pr.eventProb
      (algorithm1FlTruncatedSpectralEvent fp
        (eps / (2 * (n : ℝ))) s A X eps B) := by
  exact hProb.trans
    (Pr.eventProb_mono
      (algorithm1ExactSpectralEvent_truncated_half_subset_fl_original
        fp s A X B heps hn hB_nonneg hPoint))

/-- Rectangular half-budget truncation transfer for Algorithm 1.

If the sampled residual of `elementwiseTruncate (eps/(2*sqrt(mn))) A` is
bounded by `eps/2`, then the exact truncated residual against `A` is bounded
by `eps`. -/
theorem algorithm1ExactSpectralEvent_truncated_rect_half_subset_original
    {Ω : Type*} {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) {eps : ℝ}
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ)) :
    algorithm1ExactSpectralEvent s
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
        X (eps / 2) ⊆
      algorithm1ExactTruncatedSpectralEvent
        (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A X eps := by
  intro ω h
  have hTrunc :
      frobNormRect
        (fun i j =>
          A i j -
            elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j) ≤
        eps / 2 :=
    elementwiseTruncate_rect_error_frobNormRect_le_half A heps hmn
  have hmain :=
    elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
      (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A (X ω)
      (beta := eps / 2) (alpha := eps / 2) h hTrunc
  change rectOpNorm2Le
    (elementwiseTruncatedTraceResidual
      (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A (X ω)) eps
  convert hmain using 1
  ring

/-- Probability transfer for the rectangular source-aligned truncated variant. -/
theorem probability_algorithm1_exact_truncated_rect_spectral_of_sampled_half
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ : ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hProb :
      ρ ≤ Pr.eventProb
        (algorithm1ExactSpectralEvent s
          (elementwiseTruncate
            (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
          X (eps / 2))) :
    ρ ≤ Pr.eventProb
      (algorithm1ExactTruncatedSpectralEvent
        (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A X eps) := by
  exact hProb.trans
    (Pr.eventProb_mono
      (algorithm1ExactSpectralEvent_truncated_rect_half_subset_original
        s A X heps hmn))

/-- Rectangular floating-point half-budget truncation transfer for Algorithm 1.

The exact sampled residual event at radius `eps/2` transfers to the rounded
truncated residual event at radius `eps + ||B||_F`, provided the rounded sketch
has the advertised entrywise perturbation budget. -/
theorem algorithm1ExactSpectralEvent_truncated_rect_half_subset_fl_original
    (fp : FPModel) {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    {eps : ℝ} (B : Fin m → Fin n → ℝ)
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hPoint :
      ∀ ω i j,
        |fl_elementwiseTraceSketch fp s
            (elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
            (fun _ _ => 0) (X ω) i j -
          elementwiseTraceSketch s
            (elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
            (fun _ _ => 0) (X ω) i j| ≤ B i j) :
    algorithm1ExactSpectralEvent s
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
        X (eps / 2) ⊆
      algorithm1FlTruncatedSpectralEvent fp
        (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A X eps B := by
  intro ω h
  have hTrunc :
      frobNormRect
        (fun i j =>
          A i j -
            elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j) ≤
        eps / 2 :=
    elementwiseTruncate_rect_error_frobNormRect_le_half A heps hmn
  have hfl :=
    fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
      fp (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A (X ω)
      (beta := eps / 2) (alpha := eps / 2)
      B hB_nonneg h (hPoint ω) hTrunc
  change rectOpNorm2Le
    (fl_elementwiseTruncatedTraceResidual fp
      (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A (X ω))
    (eps + frobNormRect B)
  convert hfl using 1
  ring

/-- Probability transfer to the rectangular floating-point source-aligned
truncated event. -/
theorem probability_algorithm1_fl_truncated_rect_spectral_of_sampled_half
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ : ℝ) {eps : ℝ}
    (B : Fin m → Fin n → ℝ)
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hPoint :
      ∀ ω i j,
        |fl_elementwiseTraceSketch fp s
            (elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
            (fun _ _ => 0) (X ω) i j -
          elementwiseTraceSketch s
            (elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
            (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hProb :
      ρ ≤ Pr.eventProb
        (algorithm1ExactSpectralEvent s
          (elementwiseTruncate
            (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
          X (eps / 2))) :
    ρ ≤ Pr.eventProb
      (algorithm1FlTruncatedSpectralEvent fp
        (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A X eps B) := by
  exact hProb.trans
    (Pr.eventProb_mono
      (algorithm1ExactSpectralEvent_truncated_rect_half_subset_fl_original
        fp s A X B heps hmn hB_nonneg hPoint))




































































































-- ============================================================
-- Exact Frobenius residual concentration under the product trace law
-- ============================================================
































































































































































































































































































































































































































































































































































-- ============================================================
-- Probabilistic transfer
-- ============================================================

/-- A Frobenius residual event implies the corresponding rectangular
    vector-action operator-2 residual event. This deterministic bridge is useful
    for weaker exact concentration theorems and as a sanity layer before a true
    matrix Bernstein/Khintchine proof. -/
theorem algorithm1ExactFrobEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) :
    algorithm1ExactFrobEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X ε := by
  intro ω hFrob
  exact rectOpNorm2Le_of_frobNormRect_le
    (elementwiseTraceResidual s A (X ω)) hFrob

/-- A simultaneous entrywise residual bound implies an exact rectangular
    operator-2 event with the Frobenius norm of the constant entry budget.

This is a deterministic union-bound support bridge, not a spectral
concentration theorem. -/
theorem algorithm1ExactEntrywiseEvent_subset_exactSpectralEvent_const
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    algorithm1ExactEntrywiseEvent s A X τ ⊆
      algorithm1ExactSpectralEvent s A X
        (frobNormRect (fun _i : Fin m => fun _j : Fin n => τ)) := by
  intro ω hEntry
  apply rectOpNorm2Le_of_frobNormRect_le
  apply frobNormRect_le_of_entry_abs_le
  · intro i j
    exact hτ
  · intro i j
    exact hEntry i j

/-- Probability transfer from an exact Frobenius residual event to the
    repository's exact rectangular operator event. This is not the CACM
    equation (2) matrix-concentration theorem; it is a deterministic
    Frobenius-to-operator consequence for whatever exact Frobenius event has
    already been proved. -/
theorem probability_algorithm1_exact_spectral_of_frob
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ)
    (hFrobProb : ρ ≤ Pr.eventProb (algorithm1ExactFrobEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans hFrobProb
    (Pr.eventProb_mono
      (algorithm1ExactFrobEvent_subset_exactSpectralEvent s A X ε))

/-- Probability transfer from a simultaneous entrywise residual event to the
    exact rectangular operator event with constant-entry Frobenius budget. -/
theorem probability_algorithm1_exact_spectral_of_entrywise_const
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ τ : ℝ) (hτ : 0 ≤ τ)
    (hEntryProb :
      ρ ≤ Pr.eventProb (algorithm1ExactEntrywiseEvent s A X τ)) :
    ρ ≤ Pr.eventProb
      (algorithm1ExactSpectralEvent s A X
        (frobNormRect (fun _i : Fin m => fun _j : Fin n => τ))) := by
  exact le_trans hEntryProb
    (Pr.eventProb_mono
      (algorithm1ExactEntrywiseEvent_subset_exactSpectralEvent_const
        s A X τ hτ))

/-- A self-adjoint dilation residual event implies the rectangular
    vector-action residual event. This is the deterministic bridge needed to
    use future square matrix concentration theorems for CACM equation (2). -/
theorem algorithm1ExactDilationEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) :
    algorithm1ExactDilationEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X ε := by
  intro ω hDilation
  exact rectOpNorm2Le_of_selfAdjointDilation
    (elementwiseTraceResidual s A (X ω)) hDilation

/-- A one-sided dilation Loewner event implies the rectangular spectral event.
    This is the event-level adapter for a future largest-eigenvalue matrix
    concentration theorem stated as `D(M) <= ε I`. -/
theorem algorithm1ExactDilationUpperEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (hε : 0 ≤ ε) :
    algorithm1ExactDilationUpperEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X ε := by
  intro ω hUpper
  exact rectOpNorm2Le_of_selfAdjointDilation_loewnerLe_scalar_id
    (elementwiseTraceResidual s A (X ω)) hε hUpper

/-- Monotonicity of the exact Algorithm 1 spectral event in the radius. -/
theorem algorithm1ExactSpectralEvent_mono
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    {ε η : ℝ} (hεη : ε ≤ η) :
    algorithm1ExactSpectralEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X η := by
  intro ω hω
  exact rectOpNorm2Le_mono hεη hω

/-- Deterministic bridge from the scaled Hermitian-eigenvalue tail event to
    the rectangular Algorithm 1 spectral event.  It is the first conversion
    step after the trace-MGF corollary: `|lambda(theta D(R))| < T` implies
    `D(R) <= (T / theta) I`, and self-adjoint dilation Loewner control gives
    the rectangular operator bound. -/
theorem algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    {theta T : ℝ} (htheta : 0 < theta) (hTtheta : 0 ≤ T / theta) :
    algorithm1ScaledDilationAbsEigenvalueEvent s A X theta T ⊆
      algorithm1ExactSpectralEvent s A X (T / theta) := by
  intro ω hScaled
  let D : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω))
  let Mscaled : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun b c => theta * D b c
  have hsymScaled : IsSymmetricFiniteMatrix Mscaled := by
    intro b c
    exact congrArg (fun x => theta * x)
      (rectSelfAdjointDilation_symmetric
        (elementwiseTraceResidual s A (X ω)) b c)
  have hEigUpper :
      ∀ a : Fin m ⊕ Fin n,
        finiteHermitianEigenvalues Mscaled hsymScaled a ≤ T := by
    intro a
    have hlt := hScaled a
    have hle_abs :
        finiteHermitianEigenvalues Mscaled hsymScaled a ≤
          |finiteHermitianEigenvalues Mscaled hsymScaled a| :=
      le_abs_self _
    exact le_of_lt (lt_of_le_of_lt hle_abs hlt)
  have hUpperScaled :
      finiteLoewnerLe Mscaled (fun a b => T * finiteIdMatrix a b) :=
    finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le
      Mscaled hsymScaled hEigUpper
  have hUpper :
      finiteLoewnerLe D (fun a b => (T / theta) * finiteIdMatrix a b) := by
    exact finiteLoewnerLe_of_smul_left_le_smul_id D htheta
      (by simpa [Mscaled, D] using hUpperScaled)
  exact rectOpNorm2Le_of_selfAdjointDilation_loewnerLe_scalar_id
    (elementwiseTraceResidual s A (X ω)) hTtheta (by simpa [D] using hUpper)

/-- Explicit high-probability spectral-event form obtained from the scaled
eigenvalue tail.

The radius is still the unoptimized matrix-Bernstein parameter expression
`log (2 B / δ) / theta`.  This theorem closes the deterministic conversion
from the trace-MGF eigenvalue event to the repository's rectangular
`algorithm1ExactSpectralEvent`; the remaining CACM equation (2) work is the
source-constant `theta` optimization. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_scaled_radius_supportRadius
    {m n s : ℕ} {theta δ : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 < theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta)) := by
  classical
  intro L beta V B
  let P := sqMagTraceProbability (steps := s) A hden
  let T : ℝ := Real.log ((2 * B) / δ)
  have hTtheta : 0 ≤ T / theta := by
    have hmn_pos_nat : 0 < m + n := by
      exact_mod_cast hdim
    have hmn_ge_one_nat : 1 ≤ m + n := Nat.succ_le_of_lt hmn_pos_nat
    have hmn_ge_one : (1 : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
      have hcast : (1 : ℝ) ≤ (m + n : ℕ) := by
        exact_mod_cast hmn_ge_one_nat
      simpa [Nat.cast_add] using hcast
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    have hbeta_nonneg : 0 ≤ beta := by
      dsimp [beta]
      exact div_nonneg hnum (sq_nonneg L)
    have hV_nonneg : 0 ≤ V := by
      dsimp [V]
      have hmax_nonneg : 0 ≤ max (m : ℝ) (n : ℝ) :=
        le_trans (Nat.cast_nonneg m) (le_max_left (m : ℝ) (n : ℝ))
      have hfrac_nonneg :
          0 ≤ frobNormSqRect A / (s : ℝ) ^ 2 :=
        div_nonneg (frobNormSqRect_nonneg A) (sq_nonneg (s : ℝ))
      exact mul_nonneg hmax_nonneg hfrac_nonneg
    have hexponent_nonneg : 0 ≤ (s : ℝ) * (beta * V) := by
      positivity
    have hexp_ge_one : 1 ≤ Real.exp ((s : ℝ) * (beta * V)) :=
      Real.one_le_exp_iff.mpr hexponent_nonneg
    have hB_ge_one : 1 ≤ B := by
      dsimp [B]
      nlinarith [hmn_ge_one, hexp_ge_one]
    have harg_ge_one : 1 ≤ (2 * B) / δ := by
      have hδ_le_2B : δ ≤ 2 * B := by
        nlinarith [hδ_le_one, hB_ge_one]
      exact (le_div_iff₀ hδ).mpr
        (by simpa using hδ_le_2B : (1 : ℝ) * δ ≤ 2 * B)
    have hlog_nonneg : 0 ≤ Real.log ((2 * B) / δ) :=
      Real.log_nonneg harg_ge_one
    exact div_nonneg hlog_nonneg (le_of_lt htheta)
  have hscaled :
      1 - δ ≤ P.eventProb
        (algorithm1ScaledDilationAbsEigenvalueEvent s A
          (fun samples : ElementwiseTrace m n s => samples) theta T) := by
    simpa [P, T, L, beta, V, B,
      algorithm1ScaledDilationAbsEigenvalueEvent] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_literalTraceResidual_lt_ge_one_sub_delta_supportRadius
        (m := m) (n := n) (s := s) (theta := theta) (δ := δ)
        hs A hden (le_of_lt htheta) hdim hδ
  have hsubset :
      algorithm1ScaledDilationAbsEigenvalueEvent s A
          (fun samples : ElementwiseTrace m n s => samples) theta T ⊆
        algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) (T / theta) :=
    algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent
      s A (fun samples : ElementwiseTrace m n s => samples)
      htheta hTtheta
  exact hscaled.trans (P.eventProb_mono hsubset)

/-- Bennett-optimized literal Algorithm 1 support-radius theorem.

This is the nontruncated, literal-law analogue of the truncated Bennett
wrapper.  It removes the free trace-MGF parameter by choosing
`theta = log (1 + L*r/W) / L`, where `L` is the exact reciprocal-entry support
radius and `W = s*V` is the summed variance proxy.  The theorem is
nonconditional, but its budget visibly depends on the literal support radius;
it is therefore not the source-uniform CACM equation-(2) rate when tiny
nonzero entries are present. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bennett_radius_supportRadius
    {m n s : ℕ} {δ r : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let L : ℝ := elementwiseLiteralResidualSupportRadius s A
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W))) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  let L : ℝ := elementwiseLiteralResidualSupportRadius s A
  let V : ℝ := max (m : ℝ) (n : ℝ) *
    (frobNormSqRect A / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  let theta : ℝ := Real.log (1 + L * r / W) / L
  let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
  let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
  let P := sqMagTraceProbability (steps := s) A hden
  have hbudget' :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) := by
    simpa [L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect A := by
    simpa [sqMagProbDen] using hden
  have hFrob_pos : 0 < frobNormRect A := by
    have hne : frobNormRect A ≠ 0 := by
      intro hzero
      have hsq := frobNormRect_sq A
      have hzero_sq : frobNormRect A ^ 2 = 0 := by simp [hzero]
      have hzero_frob : frobNormSqRect A = 0 := by
        rw [← hsq, hzero_sq]
      exact (ne_of_gt hdenA) hzero_frob
    exact lt_of_le_of_ne (frobNormRect_nonneg A) (Ne.symm hne)
  have hL_pos : 0 < L := by
    have hfirst :
        0 < (1 / (s : ℝ)) * frobNormRect A :=
      mul_pos (one_div_pos.mpr hs) hFrob_pos
    have hsecond :
        0 ≤ elementwiseLiteralContributionRadius s A :=
      elementwiseLiteralContributionRadius_nonneg hs A
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect A +
            elementwiseLiteralContributionRadius s A :=
      add_pos_of_pos_of_nonneg hfirst hsecond
    simpa [L, elementwiseLiteralResidualSupportRadius] using hsum
  have hmax_pos : 0 < max (m : ℝ) (n : ℝ) := by
    by_contra hnot
    have hmax_le : max (m : ℝ) (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hm_le : (m : ℝ) ≤ 0 :=
      le_trans (le_max_left (m : ℝ) (n : ℝ)) hmax_le
    have hn_le : (n : ℝ) ≤ 0 :=
      le_trans (le_max_right (m : ℝ) (n : ℝ)) hmax_le
    nlinarith [hdim, hm_le, hn_le]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect A / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hmax_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have htheta_pos : 0 < theta := by
    have hquot : 0 < L * r / W := by positivity
    have harg : 1 < 1 + L * r / W := by linarith
    dsimp [theta]
    exact div_pos (Real.log_pos harg) hL_pos
  have hradius_core :
      (Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta) /
          theta ≤ r := by
    simpa [theta, beta] using
      real_bernstein_exact_radius_le_of_log_le
        hL_pos hW_pos hr hbudget'
  have hlog_radius :
      Real.log ((2 * B) / δ) / theta ≤ r := by
    have hq_pos : 0 < (2 * ((m : ℝ) + (n : ℝ))) / δ :=
      div_pos (mul_pos (by norm_num) hdim) hδ
    have hexp_ne : Real.exp ((s : ℝ) * (beta * V)) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    have hrewrite :
        (2 * B) / δ =
          ((2 * ((m : ℝ) + (n : ℝ))) / δ) *
            Real.exp ((s : ℝ) * (beta * V)) := by
      dsimp [B]
      field_simp [hδ.ne']
    have hlog :
        Real.log ((2 * B) / δ) =
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
            W * beta := by
      calc
        Real.log ((2 * B) / δ)
            = Real.log
                (((2 * ((m : ℝ) + (n : ℝ))) / δ) *
                  Real.exp ((s : ℝ) * (beta * V))) := by
                rw [hrewrite]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
              Real.log (Real.exp ((s : ℝ) * (beta * V))) := by
                rw [Real.log_mul (ne_of_gt hq_pos) hexp_ne]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta := by
                rw [Real.log_exp]
                dsimp [W]
                ring
    simpa [hlog] using hradius_core
  have hbase :
      1 - δ ≤
        P.eventProb
          (algorithm1ExactSpectralEvent s A
            (fun samples : ElementwiseTrace m n s => samples)
            (Real.log ((2 * B) / δ) / theta)) := by
    simpa [P, L, V, B, beta, theta] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_scaled_radius_supportRadius
        (m := m) (n := n) (s := s) (theta := theta) (δ := δ)
        hs A hden htheta_pos hdim hδ hδ_le_one
  have hsubset :
      algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta) ⊆
        algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) r :=
    algorithm1ExactSpectralEvent_mono s A
      (fun samples : ElementwiseTrace m n s => samples) hlog_radius
  exact hbase.trans (P.eventProb_mono hsubset)

/-- Literal Algorithm 1 support-radius theorem in Bernstein-denominator form.

This corollary replaces the exact Bennett-transform budget by the fully proved
scalar denominator `2W + (2/3)Lr`.  The support scale `L` is still the exact
literal reciprocal-entry radius, so the result is nonconditional and
nonvacuous without hiding the tiny-entry dependence. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_supportRadius
    {m n s : ℕ} {δ r : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let L : ℝ := elementwiseLiteralResidualSupportRadius s A
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r)) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  let L : ℝ := elementwiseLiteralResidualSupportRadius s A
  let V : ℝ := max (m : ℝ) (n : ℝ) *
    (frobNormSqRect A / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  have hbudget' :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) := by
    simpa [L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect A := by
    simpa [sqMagProbDen] using hden
  have hFrob_pos : 0 < frobNormRect A := by
    have hne : frobNormRect A ≠ 0 := by
      intro hzero
      have hsq := frobNormRect_sq A
      have hzero_sq : frobNormRect A ^ 2 = 0 := by simp [hzero]
      have hzero_frob : frobNormSqRect A = 0 := by
        rw [← hsq, hzero_sq]
      exact (ne_of_gt hdenA) hzero_frob
    exact lt_of_le_of_ne (frobNormRect_nonneg A) (Ne.symm hne)
  have hL_pos : 0 < L := by
    have hfirst :
        0 < (1 / (s : ℝ)) * frobNormRect A :=
      mul_pos (one_div_pos.mpr hs) hFrob_pos
    have hsecond :
        0 ≤ elementwiseLiteralContributionRadius s A :=
      elementwiseLiteralContributionRadius_nonneg hs A
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect A +
            elementwiseLiteralContributionRadius s A :=
      add_pos_of_pos_of_nonneg hfirst hsecond
    simpa [L, elementwiseLiteralResidualSupportRadius] using hsum
  have hmax_pos : 0 < max (m : ℝ) (n : ℝ) := by
    by_contra hnot
    have hmax_le : max (m : ℝ) (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hm_le : (m : ℝ) ≤ 0 :=
      le_trans (le_max_left (m : ℝ) (n : ℝ)) hmax_le
    have hn_le : (n : ℝ) ≤ 0 :=
      le_trans (le_max_right (m : ℝ) (n : ℝ)) hmax_le
    nlinarith [hdim, hm_le, hn_le]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect A / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hmax_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have hbennett :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) :=
    real_bennett_budget_of_quadratic_denominator_two_add_two_thirds
      hL_pos hW_pos hr hbudget'
  exact
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bennett_radius_supportRadius
      (m := m) (n := n) (s := s) (δ := δ) (r := r)
      hs A hden hdim hδ hδ_le_one hr
      (by simpa [L, V, W] using hbennett)

/-- Budget adapter from a simple nonzero-entry floor to the exact literal
reciprocal-entry support radius used by the Bernstein-denominator theorem.

The floor budget is stronger but easier to read: it replaces
`elementwiseLiteralResidualSupportRadius s A` by the upper bound
`s^{-1}||A||_F + mn ||A||_F^2/(s alpha)`. -/
theorem algorithm1LiteralBernsteinDenominatorBudget_of_entry_floor
    {m n s : ℕ} {δ r alpha : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hr : 0 < r)
    (halpha : 0 < alpha)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|)
    (hbudget :
      let Lfloor : ℝ :=
        (1 / (s : ℝ)) * frobNormRect A +
          ((m : ℝ) * (n : ℝ)) *
            (frobNormSqRect A / ((s : ℝ) * alpha))
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * Lfloor * r)) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    let W : ℝ := (s : ℝ) * V
    Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
      r ^ 2 / (2 * W + (2 / 3) * L * r) := by
  classical
  let L : ℝ := elementwiseLiteralResidualSupportRadius s A
  let Lfloor : ℝ :=
    (1 / (s : ℝ)) * frobNormRect A +
      ((m : ℝ) * (n : ℝ)) *
        (frobNormSqRect A / ((s : ℝ) * alpha))
  let V : ℝ := max (m : ℝ) (n : ℝ) *
    (frobNormSqRect A / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  have hbudget_floor :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * Lfloor * r) := by
    simpa [Lfloor, V, W] using hbudget
  have hL_le : L ≤ Lfloor := by
    simpa [L, Lfloor] using
      elementwiseLiteralResidualSupportRadius_le_of_entry_abs_ge
        halpha hs A hentry
  have hL_nonneg : 0 ≤ L := by
    simpa [L] using elementwiseLiteralResidualSupportRadius_nonneg hs A
  have hdenA : 0 < frobNormSqRect A := by
    simpa [sqMagProbDen] using hden
  have hmax_pos : 0 < max (m : ℝ) (n : ℝ) := by
    by_contra hnot
    have hmax_le : max (m : ℝ) (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hm_le : (m : ℝ) ≤ 0 :=
      le_trans (le_max_left (m : ℝ) (n : ℝ)) hmax_le
    have hn_le : (n : ℝ) ≤ 0 :=
      le_trans (le_max_right (m : ℝ) (n : ℝ)) hmax_le
    nlinarith [hdim, hm_le, hn_le]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect A / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hmax_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have hden_actual_pos : 0 < 2 * W + (2 / 3) * L * r := by
    nlinarith [hW_pos, hL_nonneg, hr]
  have hden_le :
      2 * W + (2 / 3) * L * r ≤
        2 * W + (2 / 3) * Lfloor * r := by
    have hcoef_nonneg : 0 ≤ (2 / 3 : ℝ) * r := by positivity
    have hmul := mul_le_mul_of_nonneg_right hL_le hcoef_nonneg
    nlinarith [hmul]
  have hdiv :
      r ^ 2 / (2 * W + (2 / 3) * Lfloor * r) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) :=
    div_le_div_of_nonneg_left (sq_nonneg r) hden_actual_pos hden_le
  exact hbudget_floor.trans
    (by simpa [L, Lfloor, V, W] using hdiv)

/-- Literal Algorithm 1 exact spectral theorem with the reciprocal-entry
support radius replaced by a readable nonzero-entry floor.

This is still a literal-law theorem.  It is nonconditional and exact, but it is
not source-uniform: the displayed budget depends on the entry floor `alpha`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bernstein_denominator_entry_floor
    {m n s : ℕ} {δ r alpha : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (halpha : 0 < alpha)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|)
    (hbudget :
      let Lfloor : ℝ :=
        (1 / (s : ℝ)) * frobNormRect A +
          ((m : ℝ) * (n : ℝ)) *
            (frobNormSqRect A / ((s : ℝ) * alpha))
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * Lfloor * r)) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  have hbudget_actual :
      let L : ℝ := elementwiseLiteralResidualSupportRadius s A
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) :=
    algorithm1LiteralBernsteinDenominatorBudget_of_entry_floor
      hs A hden hdim hr halpha hentry hbudget
  exact
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_supportRadius
      (m := m) (n := n) (s := s) (δ := δ) (r := r)
      hs A hden hdim hδ hδ_le_one hr hbudget_actual

theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius
    {m n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 < theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta)) := by
  classical
  intro Ahat L beta V B
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let T : ℝ := Real.log ((2 * B) / δ)
  have hTtheta : 0 ≤ T / theta := by
    have hmn_pos_nat : 0 < m + n := by
      exact_mod_cast hdim
    have hmn_ge_one_nat : 1 ≤ m + n := Nat.succ_le_of_lt hmn_pos_nat
    have hmn_ge_one : (1 : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
      have hcast : (1 : ℝ) ≤ (m + n : ℕ) := by
        exact_mod_cast hmn_ge_one_nat
      simpa [Nat.cast_add] using hcast
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    have hbeta_nonneg : 0 ≤ beta := by
      dsimp [beta]
      exact div_nonneg hnum (sq_nonneg L)
    have hV_nonneg : 0 ≤ V := by
      dsimp [V]
      positivity
    have hexponent_nonneg : 0 ≤ (s : ℝ) * (beta * V) := by
      positivity
    have hexp_ge_one : 1 ≤ Real.exp ((s : ℝ) * (beta * V)) :=
      Real.one_le_exp_iff.mpr hexponent_nonneg
    have hB_ge_one : 1 ≤ B := by
      dsimp [B]
      nlinarith [hmn_ge_one, hexp_ge_one]
    have harg_ge_one : 1 ≤ (2 * B) / δ := by
      have hδ_le_2B : δ ≤ 2 * B := by
        nlinarith [hδ_le_one, hB_ge_one]
      exact (le_div_iff₀ hδ).mpr
        (by simpa using hδ_le_2B : (1 : ℝ) * δ ≤ 2 * B)
    have hlog_nonneg : 0 ≤ Real.log ((2 * B) / δ) :=
      Real.log_nonneg harg_ge_one
    exact div_nonneg hlog_nonneg (le_of_lt htheta)
  have hscaled :
      1 - δ ≤ P.eventProb
        (algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) theta T) := by
    simpa [P, T, Ahat, L, beta, V, B,
      algorithm1ScaledDilationAbsEigenvalueEvent] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden (le_of_lt htheta) hdim hδ
  have hsubset :
      algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) theta T ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) (T / theta) :=
    algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent
      s Ahat (fun samples : ElementwiseTrace m n s => samples)
      htheta hTtheta
  exact hscaled.trans (P.eventProb_mono hsubset)

/-- Bennett-optimized high-probability spectral-event form for the truncated
Algorithm 1 route.

This corollary chooses
`theta = log (1 + L * r / W) / L`, where `W = s * V`, and uses the exact
scalar Bennett transform to replace the unoptimized radius
`log (2B/delta) / theta` by a requested radius `r`.  It is still a truncated
exact-arithmetic theorem; the CACM equation (2) row also needs the source
sample-complexity simplification, truncation transfer back to the original
matrix at the final constants, and the downstream floating-point spectral
transfer. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius
    {m n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ := Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau))
      let V : ℝ :=
        2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W))) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ := Real.sqrt 2 *
    ((1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau))
  let V : ℝ :=
    2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
  let W : ℝ := (s : ℝ) * V
  let theta : ℝ := Real.log (1 + L * r / W) / L
  let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
  let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hbudget' :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hparen :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hparen
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos (by norm_num) (mul_pos hmn hfrac)
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have htheta_pos : 0 < theta := by
    have hquot : 0 < L * r / W := by positivity
    have harg : 1 < 1 + L * r / W := by linarith
    dsimp [theta]
    exact div_pos (Real.log_pos harg) hL_pos
  have hradius_core :
      (Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta) /
          theta ≤ r := by
    simpa [theta, beta] using
      real_bernstein_exact_radius_le_of_log_le
        hL_pos hW_pos hr hbudget'
  have hlog_radius :
      Real.log ((2 * B) / δ) / theta ≤ r := by
    have hq_pos : 0 < (2 * ((m : ℝ) + (n : ℝ))) / δ :=
      div_pos (mul_pos (by norm_num) hdim) hδ
    have hexp_ne : Real.exp ((s : ℝ) * (beta * V)) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    have hrewrite :
        (2 * B) / δ =
          ((2 * ((m : ℝ) + (n : ℝ))) / δ) *
            Real.exp ((s : ℝ) * (beta * V)) := by
      dsimp [B]
      field_simp [hδ.ne']
    have hlog :
        Real.log ((2 * B) / δ) =
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
            W * beta := by
      calc
        Real.log ((2 * B) / δ)
            = Real.log
                (((2 * ((m : ℝ) + (n : ℝ))) / δ) *
                  Real.exp ((s : ℝ) * (beta * V))) := by
                rw [hrewrite]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
              Real.log (Real.exp ((s : ℝ) * (beta * V))) := by
                rw [Real.log_mul (ne_of_gt hq_pos) hexp_ne]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta := by
                rw [Real.log_exp]
                dsimp [W]
                ring
    simpa [hlog] using hradius_core
  have hbase :
      1 - δ ≤
        P.eventProb
          (algorithm1ExactSpectralEvent s Ahat
            (fun samples : ElementwiseTrace m n s => samples)
            (Real.log ((2 * B) / δ) / theta)) := by
    simpa [P, Ahat, L, V, B, beta, theta] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden htheta_pos hdim hδ hδ_le_one
  have hsubset :
      algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta) ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) r :=
    algorithm1ExactSpectralEvent_mono s Ahat
      (fun samples : ElementwiseTrace m n s => samples) hlog_radius
  exact hbase.trans (P.eventProb_mono hsubset)

/-- Rectangular source-sharp high-probability spectral-event form obtained
from the scaled eigenvalue tail.

This is the rectangular companion of the square source-sharp wrapper.  It uses
the variance scale `max(m,n) * ||Ahat||_F^2 / s^2` from the rectangular
trace-MGF skeleton and keeps the generic retained-entry support radius with
the `sqrt 2` dilation factor. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_rect
    {m n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 < theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta)) := by
  classical
  intro Ahat L beta V B
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let T : ℝ := Real.log ((2 * B) / δ)
  have hTtheta : 0 ≤ T / theta := by
    have hmn_pos_nat : 0 < m + n := by
      exact_mod_cast hdim
    have hmn_ge_one_nat : 1 ≤ m + n := Nat.succ_le_of_lt hmn_pos_nat
    have hmn_ge_one : (1 : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
      have hcast : (1 : ℝ) ≤ (m + n : ℕ) := by
        exact_mod_cast hmn_ge_one_nat
      simpa [Nat.cast_add] using hcast
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    have hbeta_nonneg : 0 ≤ beta := by
      dsimp [beta]
      exact div_nonneg hnum (sq_nonneg L)
    have hV_nonneg : 0 ≤ V := by
      dsimp [V]
      positivity
    have hexponent_nonneg : 0 ≤ (s : ℝ) * (beta * V) := by
      positivity
    have hexp_ge_one : 1 ≤ Real.exp ((s : ℝ) * (beta * V)) :=
      Real.one_le_exp_iff.mpr hexponent_nonneg
    have hB_ge_one : 1 ≤ B := by
      dsimp [B]
      nlinarith [hmn_ge_one, hexp_ge_one]
    have harg_ge_one : 1 ≤ (2 * B) / δ := by
      have hδ_le_2B : δ ≤ 2 * B := by
        nlinarith [hδ_le_one, hB_ge_one]
      exact (le_div_iff₀ hδ).mpr
        (by simpa using hδ_le_2B : (1 : ℝ) * δ ≤ 2 * B)
    have hlog_nonneg : 0 ≤ Real.log ((2 * B) / δ) :=
      Real.log_nonneg harg_ge_one
    exact div_nonneg hlog_nonneg (le_of_lt htheta)
  have hscaled :
      1 - δ ≤ P.eventProb
        (algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) theta T) := by
    simpa [P, T, Ahat, L, beta, V, B,
      algorithm1ScaledDilationAbsEigenvalueEvent] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_rect
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden (le_of_lt htheta) hdim hδ
  have hsubset :
      algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) theta T ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) (T / theta) :=
    algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent
      s Ahat (fun samples : ElementwiseTrace m n s => samples)
      htheta hTtheta
  exact hscaled.trans (P.eventProb_mono hsubset)

/-- Rectangular source-sharp Bennett-optimized high-probability spectral-event
form for the truncated Algorithm 1 route. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_rect
    {m n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ := Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau))
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect Ahat / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W))) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ := Real.sqrt 2 *
    ((1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau))
  let V : ℝ := max (m : ℝ) (n : ℝ) *
    (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  let theta : ℝ := Real.log (1 + L * r / W) / L
  let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
  let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hbudget' :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hsum
  have hM_pos : 0 < max (m : ℝ) (n : ℝ) := by
    have hm_le : (m : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_left _ _
    have hn_le : (n : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_right _ _
    nlinarith [hdim, hm_le, hn_le]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hM_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have htheta_pos : 0 < theta := by
    have hquot : 0 < L * r / W := by positivity
    have harg : 1 < 1 + L * r / W := by linarith
    dsimp [theta]
    exact div_pos (Real.log_pos harg) hL_pos
  have hradius_core :
      (Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta) /
          theta ≤ r := by
    simpa [theta, beta] using
      real_bernstein_exact_radius_le_of_log_le
        hL_pos hW_pos hr hbudget'
  have hlog_radius :
      Real.log ((2 * B) / δ) / theta ≤ r := by
    have hq_pos : 0 < (2 * ((m : ℝ) + (n : ℝ))) / δ :=
      div_pos (mul_pos (by norm_num) hdim) hδ
    have hexp_ne : Real.exp ((s : ℝ) * (beta * V)) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    have hrewrite :
        (2 * B) / δ =
          ((2 * ((m : ℝ) + (n : ℝ))) / δ) *
            Real.exp ((s : ℝ) * (beta * V)) := by
      dsimp [B]
      field_simp [hδ.ne']
    have hlog :
        Real.log ((2 * B) / δ) =
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
            W * beta := by
      calc
        Real.log ((2 * B) / δ)
            = Real.log
                (((2 * ((m : ℝ) + (n : ℝ))) / δ) *
                  Real.exp ((s : ℝ) * (beta * V))) := by
                rw [hrewrite]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
              Real.log (Real.exp ((s : ℝ) * (beta * V))) := by
                rw [Real.log_mul (ne_of_gt hq_pos) hexp_ne]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta := by
                rw [Real.log_exp]
                dsimp [W]
                ring
    simpa [hlog] using hradius_core
  have hbase :
      1 - δ ≤
        P.eventProb
          (algorithm1ExactSpectralEvent s Ahat
            (fun samples : ElementwiseTrace m n s => samples)
            (Real.log ((2 * B) / δ) / theta)) := by
    simpa [P, Ahat, L, V, B, beta, theta] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_rect
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden htheta_pos hdim hδ hδ_le_one
  have hsubset :
      algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta) ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) r :=
    algorithm1ExactSpectralEvent_mono s Ahat
      (fun samples : ElementwiseTrace m n s => samples) hlog_radius
  exact hbase.trans (P.eventProb_mono hsubset)

/-- Rectangular source-sharp Bernstein-denominator corollary for the truncated
Algorithm 1 route.

This removes the raw Bennett-transform hypothesis using the proved scalar
bound `(1+x) log(1+x)-x >= x^2/(2+(2/3)x)`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_sharp_rect
    {m n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ := Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau))
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect Ahat / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r)) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ := Real.sqrt 2 *
    ((1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau))
  let V : ℝ := max (m : ℝ) (n : ℝ) *
    (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  have hbudget' :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hsum
  have hM_pos : 0 < max (m : ℝ) (n : ℝ) := by
    have hm_le : (m : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_left _ _
    have hn_le : (n : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_right _ _
    nlinarith [hdim, hm_le, hn_le]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hM_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have hbennett :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) :=
    real_bennett_budget_of_quadratic_denominator_two_add_two_thirds
      hL_pos hW_pos hr hbudget'
  simpa [Ahat] using
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_rect
      (m := m) (n := n) (s := s) (tau := tau) (δ := δ) (r := r)
      htau hs A hden hdim hδ hδ_le_one hr
      (by simpa [Ahat, L, V, W] using hbennett)

set_option maxHeartbeats 800000

/-- Rectangular source-sample-budget corollary for the truncated Algorithm 1
route.

With `tau = eps/(2*sqrt(mn))`, the explicit budget
`4*(2M+(4 sqrt(2)/3)R)*||A||_F^2*log(2(m+n)/delta) <= s*eps^2`, where
`M=max(m,n)` and `R=sqrt(mn)`, implies the source-sharp rectangular
Bernstein-denominator event at radius `eps/2`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_rect
    {m n s : ℕ} {eps δ : ℝ} (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) (eps / 2)) := by
  classical
  let M : ℝ := max (m : ℝ) (n : ℝ)
  let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
  let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let r : ℝ := eps / 2
  let L : ℝ := Real.sqrt 2 *
    ((1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau))
  let V : ℝ := M * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  let q : ℝ := Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ)
  intro tau' Ahat'
  have hR_pos : 0 < R := by
    dsimp [R]
    exact Real.sqrt_pos.mpr hmn
  have htau_pos : 0 < tau := by
    dsimp [tau, R]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hdim : 0 < (m : ℝ) + (n : ℝ) := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [hmn, hm_nonneg, hn_nonneg]
  have hM_pos : 0 < M := by
    have hm_le : (m : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_left _ _
    have hn_le : (n : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_right _ _
    dsimp [M]
    nlinarith [hdim, hm_le, hn_le]
  have hC_pos : 0 < C := by
    dsimp [C]
    have hterm_nonneg :
        0 ≤ ((4 * Real.sqrt 2) / 3) * R := by
      positivity
    nlinarith
  have hFhatSq_pos : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, tau, sqMagProbDen] using hden
  have hFhat_pos : 0 < frobNormRect Ahat := by
    have hne : frobNormRect Ahat ≠ 0 := by
      intro hzero
      have hsq_zero : frobNormSqRect Ahat = 0 := by
        rw [← frobNormRect_sq Ahat, hzero]
        norm_num
      linarith
    exact lt_of_le_of_ne (frobNormRect_nonneg Ahat) (Ne.symm hne)
  have hFsq_pos : 0 < frobNormSqRect A := by
    exact lt_of_lt_of_le hFhatSq_pos
      (by simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A)
  have hFhatSq_le_Fsq : frobNormSqRect Ahat ≤ frobNormSqRect A := by
    simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A
  have htau_le_Fhat : tau ≤ frobNormRect Ahat := by
    simpa [Ahat, tau] using
      elementwiseTruncate_tau_le_frobNormRect_of_sqMagProbDen_pos
        (tau := tau) A (by simpa [Ahat, tau] using hden)
  have heps_le_two_R_Fhat :
      eps ≤ 2 * R * frobNormRect Ahat := by
    have hmul :=
      mul_le_mul_of_nonneg_left htau_le_Fhat
        (by positivity : 0 ≤ 2 * R)
    dsimp [tau] at hmul
    field_simp [hR_pos.ne'] at hmul
    nlinarith
  have heps_mul_Fhat_le :
      eps * frobNormRect Ahat ≤
        2 * R * frobNormSqRect Ahat := by
    have hmul :=
      mul_le_mul_of_nonneg_right heps_le_two_R_Fhat
        (le_of_lt hFhat_pos)
    calc
      eps * frobNormRect Ahat
          ≤ 2 * R * frobNormRect Ahat * frobNormRect Ahat := hmul
      _ = 2 * R * frobNormSqRect Ahat := by
          rw [← frobNormRect_sq Ahat]
          ring
  have hD_bound :
      2 * W + (2 / 3 : ℝ) * L * r ≤
        C * frobNormSqRect A / (s : ℝ) := by
    have hcoef_le :
        (6 * M + 4 * Real.sqrt 2 * R) * frobNormSqRect Ahat ≤
          (6 * M + 4 * Real.sqrt 2 * R) * frobNormSqRect A := by
      have hcoef_nonneg : 0 ≤ 6 * M + 4 * Real.sqrt 2 * R := by
        positivity
      exact mul_le_mul_of_nonneg_left hFhatSq_le_Fsq hcoef_nonneg
    dsimp [W, V, L, r, tau, C, M, R]
    field_simp [hs.ne', hR_pos.ne']
    nlinarith [heps_mul_Fhat_le, hcoef_le, Real.sqrt_nonneg 2]
  have hD_pos : 0 < 2 * W + (2 / 3 : ℝ) * L * r := by
    have hL_pos : 0 < L := by
      have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
        mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
      have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
        div_pos hFhatSq_pos (mul_pos hs htau_pos)
      have hsum :
          0 <
            (1 / (s : ℝ)) * frobNormRect Ahat +
              frobNormSqRect Ahat / ((s : ℝ) * tau) :=
        add_pos_of_nonneg_of_pos hfirst hsecond
      exact mul_pos hsqrt hsum
    have hV_pos : 0 < V := by
      have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
      have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
        div_pos hFhatSq_pos hs_sq
      dsimp [V]
      exact mul_pos hM_pos hfrac
    have hW_pos : 0 < W := by
      dsimp [W]
      exact mul_pos hs hV_pos
    positivity
  have hq_le_sample :
      q ≤ ((s : ℝ) * eps ^ 2) /
          (4 * C * frobNormSqRect A) := by
    have hden_sample : 0 < 4 * C * frobNormSqRect A := by
      positivity
    exact (le_div_iff₀ hden_sample).mpr (by
      have hsample_comm :
          q * (4 * C * frobNormSqRect A) ≤ (s : ℝ) * eps ^ 2 := by
        simpa [q, M, R, C, mul_assoc, mul_left_comm, mul_comm] using hsample
      simpa [mul_assoc, mul_left_comm, mul_comm] using hsample_comm)
  have hsample_factor_nonneg :
      0 ≤ ((s : ℝ) * eps ^ 2) /
          (4 * C * frobNormSqRect A) := by
    positivity
  have hqD_le : q * (2 * W + (2 / 3 : ℝ) * L * r) ≤ r ^ 2 := by
    have h1 :
        q * (2 * W + (2 / 3 : ℝ) * L * r) ≤
          (((s : ℝ) * eps ^ 2) /
            (4 * C * frobNormSqRect A)) *
            (2 * W + (2 / 3 : ℝ) * L * r) :=
      mul_le_mul_of_nonneg_right hq_le_sample (le_of_lt hD_pos)
    have h2 :
        (((s : ℝ) * eps ^ 2) /
            (4 * C * frobNormSqRect A)) *
            (2 * W + (2 / 3 : ℝ) * L * r) ≤
          (((s : ℝ) * eps ^ 2) /
            (4 * C * frobNormSqRect A)) *
            (C * frobNormSqRect A / (s : ℝ)) :=
      mul_le_mul_of_nonneg_left hD_bound hsample_factor_nonneg
    have h3 :
        (((s : ℝ) * eps ^ 2) /
            (4 * C * frobNormSqRect A)) *
            (C * frobNormSqRect A / (s : ℝ)) =
          r ^ 2 := by
      dsimp [r]
      field_simp [hs.ne', hC_pos.ne', (ne_of_gt hFsq_pos)]
      ring
    exact h1.trans (h2.trans_eq h3)
  have hbudget :
      q ≤ r ^ 2 / (2 * W + (2 / 3 : ℝ) * L * r) :=
    (le_div_iff₀ hD_pos).mpr hqD_le
  simpa [tau, Ahat, tau', Ahat', r, L, V, W, q, M, R, C] using
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_sharp_rect
      (m := m) (n := n) (s := s) (tau := tau) (δ := δ) (r := r)
      htau_pos hs A (by simpa [Ahat, tau] using hden) hdim hδ hδ_le_one hr
      (by simpa [Ahat, L, V, W, q, M] using hbudget)

/-- Exact rectangular source-budget Algorithm 1 theorem after deterministic
truncation transfer.

This theorem controls the exact truncated sketch against the original
rectangular input `A` at radius `eps`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_rect
    {m n s : ℕ} {eps δ : ℝ} (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace m n s => samples) eps) := by
  classical
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  intro tau' Ahat'
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hProb :
      1 - δ ≤ P.eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) (eps / 2)) := by
    simpa [P, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_rect
        (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden hδ hδ_le_one heps hsample
  have hmain :=
    probability_algorithm1_exact_truncated_rect_spectral_of_sampled_half
      (s := s) (A := A)
      (X := fun samples : ElementwiseTrace m n s => samples)
      (Pr := P) (ρ := 1 - δ) (eps := eps)
      (le_of_lt heps) hmn hProb
  simpa [P, tau, Ahat, tau', Ahat'] using hmain

/-- Source-sharp square-matrix high-probability spectral-event form obtained
from the scaled eigenvalue tail.

This is the square-matrix companion to
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius`.
It uses the Drineas--Zouzias variance scale
`V = n * ||Ahat||_F^2 / s^2` and the no-`sqrt 2` support radius supplied by
the source-sharp trace-MGF skeleton. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_square
    {n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 < theta)
    (hdim : 0 < (n : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau)
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    let B : ℝ := ((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples)
          (Real.log ((2 * B) / δ) / theta)) := by
  classical
  intro Ahat L beta V B
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let T : ℝ := Real.log ((2 * B) / δ)
  have hTtheta : 0 ≤ T / theta := by
    have hnn_pos_nat : 0 < n + n := by
      exact_mod_cast hdim
    have hnn_ge_one_nat : 1 ≤ n + n := Nat.succ_le_of_lt hnn_pos_nat
    have hnn_ge_one : (1 : ℝ) ≤ (n : ℝ) + (n : ℝ) := by
      have hcast : (1 : ℝ) ≤ (n + n : ℕ) := by
        exact_mod_cast hnn_ge_one_nat
      simpa [Nat.cast_add] using hcast
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    have hbeta_nonneg : 0 ≤ beta := by
      dsimp [beta]
      exact div_nonneg hnum (sq_nonneg L)
    have hV_nonneg : 0 ≤ V := by
      dsimp [V]
      positivity
    have hexponent_nonneg : 0 ≤ (s : ℝ) * (beta * V) := by
      positivity
    have hexp_ge_one : 1 ≤ Real.exp ((s : ℝ) * (beta * V)) :=
      Real.one_le_exp_iff.mpr hexponent_nonneg
    have hB_ge_one : 1 ≤ B := by
      dsimp [B]
      nlinarith [hnn_ge_one, hexp_ge_one]
    have harg_ge_one : 1 ≤ (2 * B) / δ := by
      have hδ_le_2B : δ ≤ 2 * B := by
        nlinarith [hδ_le_one, hB_ge_one]
      exact (le_div_iff₀ hδ).mpr
        (by simpa using hδ_le_2B : (1 : ℝ) * δ ≤ 2 * B)
    have hlog_nonneg : 0 ≤ Real.log ((2 * B) / δ) :=
      Real.log_nonneg harg_ge_one
    exact div_nonneg hlog_nonneg (le_of_lt htheta)
  have hscaled :
      1 - δ ≤ P.eventProb
        (algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) theta T) := by
    simpa [P, T, Ahat, L, beta, V, B,
      algorithm1ScaledDilationAbsEigenvalueEvent] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_square
        (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden (le_of_lt htheta) hdim hδ
  have hsubset :
      algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) theta T ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) (T / theta) :=
    algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent
      s Ahat (fun samples : ElementwiseTrace n n s => samples)
      htheta hTtheta
  exact hscaled.trans (P.eventProb_mono hsubset)

/-- Source-sharp Bennett-optimized high-probability spectral-event form for the
square truncated Algorithm 1 route.

This theorem closes the next source-sharp dependency after the two-sided
eigenvalue skeleton: under the explicit scalar Bennett budget with
`L = s^{-1} ||Ahat||_F + ||Ahat||_F^2/(s tau)` and
`W = s * n * ||Ahat||_F^2 / s^2`, the exact truncated sketch is within any
requested spectral radius `r` with probability at least `1 - delta`.  The
remaining Algorithm 1 equation (2) work is to simplify this budget to the
Drineas--Zouzias/CACM sample-complexity constants and then transfer the result
through truncation and floating-point perturbation. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square
    {n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hdim : 0 < (n : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ :=
        (1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau)
      let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W))) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  let theta : ℝ := Real.log (1 + L * r / W) / L
  let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
  let B : ℝ := ((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hbudget' :
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    simpa [L] using hsum
  have hn_pos : 0 < (n : ℝ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [hdim, hn_nonneg]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hn_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have htheta_pos : 0 < theta := by
    have hquot : 0 < L * r / W := by positivity
    have harg : 1 < 1 + L * r / W := by linarith
    dsimp [theta]
    exact div_pos (Real.log_pos harg) hL_pos
  have hradius_core :
      (Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) + W * beta) /
          theta ≤ r := by
    simpa [theta, beta] using
      real_bernstein_exact_radius_le_of_log_le
        hL_pos hW_pos hr hbudget'
  have hlog_radius :
      Real.log ((2 * B) / δ) / theta ≤ r := by
    have hq_pos : 0 < (2 * ((n : ℝ) + (n : ℝ))) / δ :=
      div_pos (mul_pos (by norm_num) hdim) hδ
    have hexp_ne : Real.exp ((s : ℝ) * (beta * V)) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    have hrewrite :
        (2 * B) / δ =
          ((2 * ((n : ℝ) + (n : ℝ))) / δ) *
            Real.exp ((s : ℝ) * (beta * V)) := by
      dsimp [B]
      field_simp [hδ.ne']
    have hlog :
        Real.log ((2 * B) / δ) =
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) +
            W * beta := by
      calc
        Real.log ((2 * B) / δ)
            = Real.log
                (((2 * ((n : ℝ) + (n : ℝ))) / δ) *
                  Real.exp ((s : ℝ) * (beta * V))) := by
                rw [hrewrite]
        _ = Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) +
              Real.log (Real.exp ((s : ℝ) * (beta * V))) := by
                rw [Real.log_mul (ne_of_gt hq_pos) hexp_ne]
        _ = Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) + W * beta := by
                rw [Real.log_exp]
                dsimp [W]
                ring
    simpa [hlog] using hradius_core
  have hbase :
      1 - δ ≤
        P.eventProb
          (algorithm1ExactSpectralEvent s Ahat
            (fun samples : ElementwiseTrace n n s => samples)
            (Real.log ((2 * B) / δ) / theta)) := by
    simpa [P, Ahat, L, V, B, beta, theta] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_square
        (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden htheta_pos hdim hδ hδ_le_one
  have hsubset :
      algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples)
          (Real.log ((2 * B) / δ) / theta) ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) r :=
    algorithm1ExactSpectralEvent_mono s Ahat
      (fun samples : ElementwiseTrace n n s => samples) hlog_radius
  exact hbase.trans (P.eventProb_mono hsubset)

/-- Conservative Bernstein-denominator corollary for the source-sharp square
Algorithm 1 route.

This theorem composes the source-sharp Bennett-radius theorem with the fully
proved scalar inequality
`(1+x) log(1+x) - x >= x^2/(2+x)`.  Its denominator
`2W + Lr` is weaker than the source-sharp Bernstein denominator
`2W + (2/3)Lr`; the latter is kept as the active final-constant bottleneck.
Nevertheless this corollary removes the raw Bennett-transform hypothesis for
a completely formalized fallback high-probability statement. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_sharp_square
    {n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hdim : 0 < (n : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ :=
        (1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau)
      let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + L * r)) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  have hbudget' :
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + L * r) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    simpa [L] using hsum
  have hn_pos : 0 < (n : ℝ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [hdim, hn_nonneg]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hn_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have hbennett :
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) :=
    real_bennett_budget_of_quadratic_denominator_two_add
      hL_pos hW_pos hr hbudget'
  simpa [Ahat] using
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square
      (n := n) (s := s) (tau := tau) (δ := δ) (r := r)
      htau hs A hden hdim hδ hδ_le_one hr
      (by simpa [Ahat, L, V, W] using hbennett)

/-- Source-sharp Bernstein-denominator corollary for the square Algorithm 1
route.

This theorem uses the fully proved scalar Bennett lower bound
`(1+x) log(1+x)-x >= x^2/(2+(2/3)x)`.  Thus the paper-style denominator
condition `q <= r^2/(2W+(2/3)Lr)` is enough to obtain the source-sharp
truncated spectral event at radius `r`.  The remaining CACM equation (2)
work is now the final sample-size algebra for the Drineas--Zouzias constants,
followed by truncation and floating-point transfer. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_sharp_square
    {n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hdim : 0 < (n : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ :=
        (1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau)
      let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r)) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  have hbudget' :
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    simpa [L] using hsum
  have hn_pos : 0 < (n : ℝ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [hdim, hn_nonneg]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hn_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have hbennett :
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) :=
    real_bennett_budget_of_quadratic_denominator_two_add_two_thirds
      hL_pos hW_pos hr hbudget'
  simpa [Ahat] using
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square
      (n := n) (s := s) (tau := tau) (δ := δ) (r := r)
      htau hs A hden hdim hδ hδ_le_one hr
      (by simpa [Ahat, L, V, W] using hbennett)

/-- Source sample-budget corollary for the square truncated Algorithm 1 route.

With the Drineas--Zouzias truncation threshold `tau = eps/(2n)`, the explicit
sample-budget condition
`14*n*||A||_F^2*log(2(2n)/delta) <= s*eps^2` implies the source-sharp
Bernstein-denominator budget at radius `eps/2`.  The conclusion is still the
truncated exact spectral event; the final paper row additionally needs the
deterministic truncation transfer back to `A` and then the FP perturbation
transfer. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square
    {n s : ℕ} {eps δ : ℝ} (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) (eps / 2)) := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  let r : ℝ := eps / 2
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  let q : ℝ := Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ)
  intro tau' Ahat'
  have htau_pos : 0 < tau := by
    dsimp [tau]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hdim : 0 < (n : ℝ) + (n : ℝ) := by nlinarith
  have hFhatSq_pos : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, tau, sqMagProbDen] using hden
  have hFhat_pos : 0 < frobNormRect Ahat := by
    have hne : frobNormRect Ahat ≠ 0 := by
      intro hzero
      have hsq_zero : frobNormSqRect Ahat = 0 := by
        rw [← frobNormRect_sq Ahat, hzero]
        norm_num
      linarith
    exact lt_of_le_of_ne (frobNormRect_nonneg Ahat) (Ne.symm hne)
  have hFsq_pos : 0 < frobNormSqRect A := by
    exact lt_of_lt_of_le hFhatSq_pos
      (by simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A)
  have hFhatSq_le_Fsq : frobNormSqRect Ahat ≤ frobNormSqRect A := by
    simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A
  have htau_le_Fhat : tau ≤ frobNormRect Ahat := by
    simpa [Ahat, tau] using
      elementwiseTruncate_tau_le_frobNormRect_of_sqMagProbDen_pos
        (tau := tau) A (by simpa [Ahat, tau] using hden)
  have heps_le_two_n_Fhat :
      eps ≤ 2 * (n : ℝ) * frobNormRect Ahat := by
    have hmul :=
      mul_le_mul_of_nonneg_left htau_le_Fhat
        (by positivity : 0 ≤ 2 * (n : ℝ))
    dsimp [tau] at hmul
    field_simp [hn.ne'] at hmul
    nlinarith
  have heps_mul_Fhat_le :
      eps * frobNormRect Ahat ≤
        2 * (n : ℝ) * frobNormSqRect Ahat := by
    have hmul :=
      mul_le_mul_of_nonneg_right heps_le_two_n_Fhat
        (le_of_lt hFhat_pos)
    calc
      eps * frobNormRect Ahat
          ≤ 2 * (n : ℝ) * frobNormRect Ahat * frobNormRect Ahat := hmul
      _ = 2 * (n : ℝ) * frobNormSqRect Ahat := by
          rw [← frobNormRect_sq Ahat]
          ring
  have hD_bound :
      2 * W + (2 / 3 : ℝ) * L * r ≤
        ((7 / 2 : ℝ) * (n : ℝ) * frobNormSqRect A) / (s : ℝ) := by
    dsimp [W, V, L, r, tau]
    field_simp [hs.ne', hn.ne', htau_pos.ne']
    nlinarith [heps_mul_Fhat_le, hFhatSq_le_Fsq]
  have hD_pos : 0 < 2 * W + (2 / 3 : ℝ) * L * r := by
    have hL_pos : 0 < L := by
      have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
        mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
      have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
        div_pos hFhatSq_pos (mul_pos hs htau_pos)
      exact add_pos_of_nonneg_of_pos hfirst hsecond
    have hV_pos : 0 < V := by
      have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
      have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
        div_pos hFhatSq_pos hs_sq
      dsimp [V]
      exact mul_pos hn hfrac
    have hW_pos : 0 < W := by
      dsimp [W]
      exact mul_pos hs hV_pos
    positivity
  have hq_le_sample :
      q ≤ ((s : ℝ) * eps ^ 2) /
          (14 * (n : ℝ) * frobNormSqRect A) := by
    have hden_sample : 0 < 14 * (n : ℝ) * frobNormSqRect A := by
      positivity
    exact (le_div_iff₀ hden_sample).mpr (by
      dsimp [q]
      nlinarith [hsample])
  have hsample_factor_nonneg :
      0 ≤ ((s : ℝ) * eps ^ 2) /
          (14 * (n : ℝ) * frobNormSqRect A) := by
    positivity
  have hqD_le : q * (2 * W + (2 / 3 : ℝ) * L * r) ≤ r ^ 2 := by
    have h1 :
        q * (2 * W + (2 / 3 : ℝ) * L * r) ≤
          (((s : ℝ) * eps ^ 2) /
            (14 * (n : ℝ) * frobNormSqRect A)) *
            (2 * W + (2 / 3 : ℝ) * L * r) :=
      mul_le_mul_of_nonneg_right hq_le_sample (le_of_lt hD_pos)
    have h2 :
        (((s : ℝ) * eps ^ 2) /
            (14 * (n : ℝ) * frobNormSqRect A)) *
            (2 * W + (2 / 3 : ℝ) * L * r) ≤
          (((s : ℝ) * eps ^ 2) /
            (14 * (n : ℝ) * frobNormSqRect A)) *
            (((7 / 2 : ℝ) * (n : ℝ) * frobNormSqRect A) / (s : ℝ)) :=
      mul_le_mul_of_nonneg_left hD_bound hsample_factor_nonneg
    have h3 :
        (((s : ℝ) * eps ^ 2) /
            (14 * (n : ℝ) * frobNormSqRect A)) *
            (((7 / 2 : ℝ) * (n : ℝ) * frobNormSqRect A) / (s : ℝ)) =
          r ^ 2 := by
      dsimp [r]
      field_simp [hs.ne', hn.ne', (ne_of_gt hFsq_pos)]
      ring
    exact h1.trans (h2.trans_eq h3)
  have hbudget :
      q ≤ r ^ 2 / (2 * W + (2 / 3 : ℝ) * L * r) :=
    (le_div_iff₀ hD_pos).mpr hqD_le
  simpa [tau, Ahat, r, L, V, W, q] using
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_sharp_square
      (n := n) (s := s) (tau := tau) (δ := δ) (r := r)
      htau_pos hs A (by simpa [Ahat, tau] using hden) hdim hδ hδ_le_one hr
      (by simpa [Ahat, L, V, W, q] using hbudget)

/-- Exact source-budget Algorithm 1 theorem after the deterministic truncation
transfer.

The previous theorem controls the sampled residual of the truncated matrix at
radius `eps/2`.  This corollary adds the already-formalized deterministic
truncation error, giving an exact-arithmetic event against the original matrix
at radius `eps`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square
    {n s : ℕ} {eps δ : ℝ} (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps) := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  intro tau' Ahat'
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hn_nat : 0 < n := by exact_mod_cast hn
  have hProb :
      1 - δ ≤ P.eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) (eps / 2)) := by
    simpa [P, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square
        (n := n) (s := s) (eps := eps) (δ := δ)
        hn hs A hden hδ hδ_le_one heps hsample
  exact
    probability_algorithm1_exact_truncated_spectral_of_sampled_half
      (s := s) (A := A)
      (X := fun samples : ElementwiseTrace n n s => samples)
      (Pr := P) (ρ := 1 - δ) (eps := eps)
      (le_of_lt heps) hn_nat hProb

















































/-- Floating-point literal Algorithm 1 spectral event with the exact
input-dependent support-radius concentration bound and the local gamma sketch
budget.

This theorem contains no generic perturbation-budget hypothesis.  The exact
probability law is the literal squared-magnitude trace law for `A`; the
floating-point budget is the concrete matrix
`sqMagTraceErrorBudget fp s s A 0`, obtained on the probability-one support
where all sampled denominators are nonzero. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_literal_scaled_radius_gamma_supportRadius
    (fp : FPModel) {m n s : ℕ} {theta δ : ℝ}
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 < theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    let TraceB : ℝ := ((m : ℝ) + (n : ℝ)) *
      Real.exp ((s : ℝ) * (beta * V))
    let eps : ℝ := Real.log ((2 * TraceB) / δ) / theta
    let Bmat : Fin m → Fin n → ℝ :=
      fun i j => sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1FlSpectralEvent fp s A
          (fun samples : ElementwiseTrace m n s => samples) eps Bmat) := by
  classical
  intro L beta V TraceB eps Bmat
  let P := sqMagTraceProbability (steps := s) A hden
  let Exact : Set (ElementwiseTrace m n s) :=
    algorithm1ExactSpectralEvent s A
      (fun samples : ElementwiseTrace m n s => samples) eps
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb A samples}
  let Fl : Set (ElementwiseTrace m n s) :=
    algorithm1FlSpectralEvent fp s A
      (fun samples : ElementwiseTrace m n s => samples) eps Bmat
  have hExactProb : 1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact, L, beta, V, TraceB, eps] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_scaled_radius_supportRadius
        (m := m) (n := n) (s := s) (theta := theta) (δ := δ)
        hs A hden htheta hdim hδ hδ_le_one
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb A hden
  have hInter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Exact Good δ 0
      hExactProb (by simp [hGoodProb])
  have hInter' : 1 - δ ≤ P.eventProb (Exact ∩ Good) := by
    simpa using hInter
  have hsubset : Exact ∩ Good ⊆ Fl := by
    intro samples hsamp
    rcases hsamp with ⟨hExact, hGood⟩
    have hB_nonneg : ∀ i j, 0 ≤ Bmat i j := by
      intro i j
      exact sqMagTraceErrorBudget_nonneg fp s s A (fun _ _ => 0) i j
        hgamma hgamma1
    have hPoint :
        ∀ i j,
          |fl_elementwiseTraceSketch fp s A
              (fun _ _ => 0) samples i j -
            elementwiseTraceSketch s A
              (fun _ _ => 0) samples i j| ≤ Bmat i j := by
      intro i j
      have hgood_pos : elementwiseTracePositiveProb A samples := by
        simpa [Good] using hGood
      simpa [Bmat] using
        fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
          fp s A samples hs.ne' hgamma hgamma1 hgood_pos i j
    have hfl :=
      fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
        fp s A samples Bmat hExact hB_nonneg hPoint
    simpa [Fl, algorithm1FlSpectralEvent] using hfl
  exact hInter'.trans (P.eventProb_mono hsubset)

/-- Floating-point source-budget Algorithm 1 theorem after deterministic
truncation and a stated entrywise FP perturbation budget.

The probability part is fully inherited from the exact source-budget theorem.
The only extra hypothesis is the explicit entrywise bound comparing the rounded
truncated sketch to the exact truncated sketch; this is the standard local FP
stability interface used elsewhere in the Algorithm 1 development. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square
    (fp : FPModel) {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (B : Fin n → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hPoint :
      ∀ (samples : ElementwiseTrace n n s) i j,
        |fl_elementwiseTraceSketch fp s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) samples i j -
          elementwiseTraceSketch s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) samples i j| ≤ B i j) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1FlTruncatedSpectralEvent fp tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps B) := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  intro tau' Ahat'
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hn_nat : 0 < n := by exact_mod_cast hn
  have hProb :
      1 - δ ≤ P.eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) (eps / 2)) := by
    simpa [P, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square
        (n := n) (s := s) (eps := eps) (δ := δ)
        hn hs A hden hδ hδ_le_one heps hsample
  exact
    probability_algorithm1_fl_truncated_spectral_of_sampled_half
      (fp := fp) (s := s) (A := A)
      (X := fun samples : ElementwiseTrace n n s => samples)
      (Pr := P) (ρ := 1 - δ) (eps := eps) (B := B)
      (le_of_lt heps) hn_nat hB_nonneg hPoint hProb

/-- Floating-point source-budget Algorithm 1 theorem with the entrywise
perturbation budget derived from the local gamma/hit-count stability library.

The exact event is intersected with the sampler's probability-one positive
support event.  On that support, every actually sampled denominator is nonzero,
so the deterministic local FP theorem supplies the budget
`sqMagTraceErrorBudget fp s s Ahat 0` with no separate `hPoint` hypothesis. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_square
    (fp : FPModel) {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let B : Fin n → Fin n → ℝ :=
      fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1FlTruncatedSpectralEvent fp tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps B) := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  let B : Fin n → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
  intro tau' Ahat' B'
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Exact : Set (ElementwiseTrace n n s) :=
    algorithm1ExactSpectralEvent s Ahat
      (fun samples : ElementwiseTrace n n s => samples) (eps / 2)
  let Good : Set (ElementwiseTrace n n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let Fl : Set (ElementwiseTrace n n s) :=
    algorithm1FlTruncatedSpectralEvent fp tau s A
      (fun samples : ElementwiseTrace n n s => samples) eps B
  have hn_nat : 0 < n := by exact_mod_cast hn
  have hExactProb : 1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square
        (n := n) (s := s) (eps := eps) (δ := δ)
        hn hs A hden hδ hδ_le_one heps hsample
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hInter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Exact Good δ 0
      hExactProb (by simp [hGoodProb])
  have hInter' : 1 - δ ≤ P.eventProb (Exact ∩ Good) := by
    simpa using hInter
  have hsubset : Exact ∩ Good ⊆ Fl := by
    intro samples hsamp
    rcases hsamp with ⟨hExact, hGood⟩
    have hB_nonneg : ∀ i j, 0 ≤ B i j := by
      intro i j
      exact sqMagTraceErrorBudget_nonneg fp s s Ahat (fun _ _ => 0) i j
        hgamma hgamma1
    have hPoint :
        ∀ i j,
          |fl_elementwiseTraceSketch fp s (elementwiseTruncate tau A)
              (fun _ _ => 0) samples i j -
            elementwiseTraceSketch s (elementwiseTruncate tau A)
              (fun _ _ => 0) samples i j| ≤ B i j := by
      intro i j
      have hgood_pos : elementwiseTracePositiveProb Ahat samples := by
        simpa [Good] using hGood
      simpa [Ahat, B] using
        fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
          fp s Ahat samples hs.ne' hgamma hgamma1 hgood_pos i j
    have hTruncFrob :
        frobNormRect
          (fun i j =>
            A i j - elementwiseTruncate (eps / (2 * (n : ℝ))) A i j) ≤
          eps / 2 :=
      elementwiseTruncate_square_error_frobNormRect_le_half A (le_of_lt heps) hn_nat
    have hfl :=
      fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
        fp tau s A samples (beta := eps / 2) (alpha := eps / 2)
        B hB_nonneg
        (by simpa [Ahat] using hExact)
        hPoint
        (by simpa [tau] using hTruncFrob)
    change rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
      (eps + frobNormRect B)
    convert hfl using 1
    ring
  exact hInter'.trans
    (by
      simpa [P, Exact, Good, Fl, tau, Ahat, B] using
        P.eventProb_mono hsubset)

/-- Rectangular floating-point source-budget Algorithm 1 theorem with the
entrywise perturbation budget derived from the local gamma/hit-count stability
library.

The sampling law is exact by convention.  The non-probability computation
charged here is the rounded zero-initialized truncated sketch update, packaged
as `sqMagTraceErrorBudget fp s s Ahat 0` on the sampler's probability-one
positive support. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_rect
    (fp : FPModel) {m n s : ℕ} {eps δ : ℝ}
    (hmn : 0 < (m : ℝ) * (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let B : Fin m → Fin n → ℝ :=
      fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1FlTruncatedSpectralEvent fp tau s A
          (fun samples : ElementwiseTrace m n s => samples) eps B) := by
  classical
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let B : Fin m → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
  intro tau' Ahat' B'
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Exact : Set (ElementwiseTrace m n s) :=
    algorithm1ExactSpectralEvent s Ahat
      (fun samples : ElementwiseTrace m n s => samples) (eps / 2)
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let Fl : Set (ElementwiseTrace m n s) :=
    algorithm1FlTruncatedSpectralEvent fp tau s A
      (fun samples : ElementwiseTrace m n s => samples) eps B
  have hExactProb : 1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_rect
        (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden hδ hδ_le_one heps hsample
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hInter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Exact Good δ 0
      hExactProb (by simp [hGoodProb])
  have hInter' : 1 - δ ≤ P.eventProb (Exact ∩ Good) := by
    simpa using hInter
  have hsubset : Exact ∩ Good ⊆ Fl := by
    intro samples hsamp
    rcases hsamp with ⟨hExact, hGood⟩
    have hB_nonneg : ∀ i j, 0 ≤ B i j := by
      intro i j
      exact sqMagTraceErrorBudget_nonneg fp s s Ahat (fun _ _ => 0) i j
        hgamma hgamma1
    have hPoint :
        ∀ i j,
          |fl_elementwiseTraceSketch fp s (elementwiseTruncate tau A)
              (fun _ _ => 0) samples i j -
            elementwiseTraceSketch s (elementwiseTruncate tau A)
              (fun _ _ => 0) samples i j| ≤ B i j := by
      intro i j
      have hgood_pos : elementwiseTracePositiveProb Ahat samples := by
        simpa [Good] using hGood
      simpa [Ahat, B] using
        fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
          fp s Ahat samples hs.ne' hgamma hgamma1 hgood_pos i j
    have hTruncFrob :
        frobNormRect
          (fun i j =>
            A i j -
              elementwiseTruncate
                (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j) ≤
          eps / 2 :=
      elementwiseTruncate_rect_error_frobNormRect_le_half A (le_of_lt heps) hmn
    have hfl :=
      fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
        fp tau s A samples (beta := eps / 2) (alpha := eps / 2)
        B hB_nonneg
        (by simpa [Ahat] using hExact)
        hPoint
        (by simpa [tau] using hTruncFrob)
    change rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
      (eps + frobNormRect B)
    convert hfl using 1
    ring
  exact hInter'.trans
    (by
      simpa [P, Exact, Good, Fl, tau, Ahat, B, tau', Ahat', B'] using
        P.eventProb_mono hsubset)






















































































































































































































/-- Literal Algorithm 1 floating-point spectral event with a scalar radius
expanded from the concrete local gamma budget.

The exact probability law is the squared-magnitude trace law for the exact
input.  The only floating-point term is the deterministic contribution of the
rounded sketch computation:
`sqrt(m*n) * (s * elementwiseLiteralContributionRadius s A) * gamma fp (s+1)`.
This is the implementation-facing scalar version of the literal support-radius
theorem above. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_scaled_radius_gamma_supportRadius
    (fp : FPModel) {m n s : ℕ} {theta δ : ℝ}
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 < theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    let TraceB : ℝ := ((m : ℝ) + (n : ℝ)) *
      Real.exp ((s : ℝ) * (beta * V))
    let eps : ℝ := Real.log ((2 * TraceB) / δ) / theta
    let fpRad : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ)) *
      (((s : ℝ) * elementwiseLiteralContributionRadius s A) *
        gamma fp (s + 1))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (eps + fpRad)} := by
  classical
  intro L beta V TraceB eps fpRad
  let P := sqMagTraceProbability (steps := s) A hden
  let Bmat : Fin m → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j
  have hProb :
      1 - δ ≤
        P.eventProb
          (algorithm1FlSpectralEvent fp s A
            (fun samples : ElementwiseTrace m n s => samples) eps Bmat) := by
    simpa [P, Bmat, L, beta, V, TraceB, eps] using
      sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_literal_scaled_radius_gamma_supportRadius
        (fp := fp) (m := m) (n := n) (s := s)
        (theta := theta) (δ := δ)
        hs A hden htheta hdim hδ hδ_le_one hgamma hgamma1
  have hB :
      frobNormRect Bmat ≤ fpRad := by
    simpa [Bmat, fpRad] using
      frobNormRect_sqMagTraceErrorBudget_zero_init_le_literalContributionRadius
        fp hs A hgamma hgamma1
  have hsubset :
      algorithm1FlSpectralEvent fp s A
          (fun samples : ElementwiseTrace m n s => samples) eps Bmat ⊆
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (eps + fpRad)} := by
    intro samples h
    exact rectOpNorm2Le_mono (by linarith) h
  exact hProb.trans (P.eventProb_mono hsubset)

/-- Final literal Algorithm 1 FP support-radius theorem with no free
trace-MGF parameter.

The exact probability law is the literal squared-magnitude product law.  The
sample-size/radius hypothesis is the visible Bernstein denominator involving
the exact reciprocal-entry support radius `L` and summed variance proxy `W`.
All floating-point arithmetic in the rounded sketch is charged by the
displayed scalar `fpRad`; probability construction remains exact by project
convention. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_ge_one_sub_delta_bernstein_denominator_gamma_supportRadius
    (fp : FPModel) {m n s : ℕ} {δ r : ℝ}
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1))
    (hbudget :
      let L : ℝ := elementwiseLiteralResidualSupportRadius s A
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r)) :
    let fpRad : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ)) *
      (((s : ℝ) * elementwiseLiteralContributionRadius s A) *
        gamma fp (s + 1))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (r + fpRad)} := by
  classical
  intro fpRad
  let P := sqMagTraceProbability (steps := s) A hden
  let Exact : Set (ElementwiseTrace m n s) :=
    algorithm1ExactSpectralEvent s A
      (fun samples : ElementwiseTrace m n s => samples) r
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb A samples}
  let Bmat : Fin m → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j
  have hExactProb : 1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_supportRadius
        (m := m) (n := n) (s := s) (δ := δ) (r := r)
        hs A hden hdim hδ hδ_le_one hr hbudget
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb A hden
  have hInter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Exact Good δ 0
      hExactProb (by simp [hGoodProb])
  have hInter' : 1 - δ ≤ P.eventProb (Exact ∩ Good) := by
    simpa using hInter
  have hBnorm : frobNormRect Bmat ≤ fpRad := by
    simpa [Bmat, fpRad] using
      frobNormRect_sqMagTraceErrorBudget_zero_init_le_literalContributionRadius
        fp hs A hgamma hgamma1
  have hsubset :
      Exact ∩ Good ⊆
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (r + fpRad)} := by
    intro samples hsamp
    rcases hsamp with ⟨hExact, hGood⟩
    have hB_nonneg : ∀ i j, 0 ≤ Bmat i j := by
      intro i j
      exact sqMagTraceErrorBudget_nonneg fp s s A (fun _ _ => 0) i j
        hgamma hgamma1
    have hPoint :
        ∀ i j,
          |fl_elementwiseTraceSketch fp s A
              (fun _ _ => 0) samples i j -
            elementwiseTraceSketch s A
              (fun _ _ => 0) samples i j| ≤ Bmat i j := by
      intro i j
      have hgood_pos : elementwiseTracePositiveProb A samples := by
        simpa [Good] using hGood
      simpa [Bmat] using
        fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
          fp s A samples hs.ne' hgamma hgamma1 hgood_pos i j
    have hfl :=
      fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
        fp s A samples Bmat hExact hB_nonneg hPoint
    exact rectOpNorm2Le_mono (by linarith) hfl
  exact hInter'.trans (P.eventProb_mono hsubset)

/-- Literal Algorithm 1 FP support-radius theorem with an explicit
nonzero-entry floor.

The exact sampling law is still the literal squared-magnitude law.  The
probability budget uses the readable support radius
`s^{-1}||A||_F + mn||A||_F^2/(s alpha)`, and the rounded-sketch arithmetic is
charged by
`sqrt(mn) * mn * (||A||_F^2/alpha) * gamma_{s+1}`. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_ge_one_sub_delta_bernstein_denominator_gamma_entry_floor
    (fp : FPModel) {m n s : ℕ} {δ r alpha : ℝ}
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (halpha : 0 < alpha)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1))
    (hbudget :
      let Lfloor : ℝ :=
        (1 / (s : ℝ)) * frobNormRect A +
          ((m : ℝ) * (n : ℝ)) *
            (frobNormSqRect A / ((s : ℝ) * alpha))
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * Lfloor * r)) :
    let fpRad : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ)) *
      ((((m : ℝ) * (n : ℝ)) * (frobNormSqRect A / alpha)) *
        gamma fp (s + 1))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (r + fpRad)} := by
  classical
  intro fpRad
  let P := sqMagTraceProbability (steps := s) A hden
  let fpRadActual : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ)) *
    (((s : ℝ) * elementwiseLiteralContributionRadius s A) *
      gamma fp (s + 1))
  have hbudget_actual :
      let L : ℝ := elementwiseLiteralResidualSupportRadius s A
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) :=
    algorithm1LiteralBernsteinDenominatorBudget_of_entry_floor
      hs A hden hdim hr halpha hentry hbudget
  have hProb :
      1 - δ ≤
        P.eventProb
          {samples : ElementwiseTrace m n s |
            rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
              (r + fpRadActual)} := by
    simpa [P, fpRadActual] using
      sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_ge_one_sub_delta_bernstein_denominator_gamma_supportRadius
        (fp := fp) (m := m) (n := n) (s := s) (δ := δ) (r := r)
        hs A hden hdim hδ hδ_le_one hr hgamma hgamma1 hbudget_actual
  have hscaled :
      (s : ℝ) * elementwiseLiteralContributionRadius s A ≤
        ((m : ℝ) * (n : ℝ)) * (frobNormSqRect A / alpha) :=
    smul_elementwiseLiteralContributionRadius_le_of_entry_abs_ge
      halpha hs A hentry
  have hinner :
      ((s : ℝ) * elementwiseLiteralContributionRadius s A) *
          gamma fp (s + 1) ≤
        (((m : ℝ) * (n : ℝ)) * (frobNormSqRect A / alpha)) *
          gamma fp (s + 1) :=
    mul_le_mul_of_nonneg_right hscaled (gamma_nonneg fp hgamma1)
  have hfpRad : fpRadActual ≤ fpRad := by
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((m : ℝ) * (n : ℝ)) := Real.sqrt_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hinner hsqrt_nonneg
    simpa [fpRadActual, fpRad, mul_assoc] using hmul
  have hsubset :
      {samples : ElementwiseTrace m n s |
        rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
          (r + fpRadActual)} ⊆
      {samples : ElementwiseTrace m n s |
        rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
          (r + fpRad)} := by
    intro samples hsamp
    exact rectOpNorm2Le_mono (by linarith) hsamp
  exact hProb.trans (P.eventProb_mono hsubset)











































































































/-- Literal Algorithm 1 exact spectral event at the source `n log n` sample
budget, for inputs where the Drineas--Zouzias threshold would not remove any
nonzero entry.

The probability law in the conclusion is the literal squared-magnitude law
`p_ij = A_ij^2 / ||A||_F^2`; no truncated matrix appears in the statement.
The explicit no-small-entry hypothesis is what allows the already-formalized
source-sharp truncated matrix-Bernstein theorem to specialize back to the
literal Algorithm 1 sampler. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_square
    {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hentry :
      ∀ i j, A i j ≠ 0 → eps / (2 * (n : ℝ)) ≤ |A i j|)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace n n s => samples) eps) := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  have htrunc : elementwiseTruncate tau A = A :=
    elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge
      (tau := tau) A (by simpa [tau] using hentry)
  have hden_trunc : 0 < sqMagProbDen (elementwiseTruncate tau A) := by
    simpa [htrunc] using hden
  have hprob :
      let tau' : ℝ := eps / (2 * (n : ℝ))
      let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau' A
      1 - δ ≤
        (sqMagTraceProbability (steps := s) Ahat hden_trunc).eventProb
          (algorithm1ExactTruncatedSpectralEvent tau' s A
            (fun samples : ElementwiseTrace n n s => samples) eps) :=
    sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square
      (n := n) (s := s) (eps := eps) (δ := δ)
      hn hs A hden_trunc hδ hδ_le_one heps hsample
  let P := sqMagTraceProbability (steps := s) A hden
  have hprob' :
      1 - δ ≤ P.eventProb
        (algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps) := by
    simpa [P, tau, htrunc, sqMagTraceProbability, sqMagSampleProbability]
      using hprob
  have hsubset :
      algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps ⊆
        algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace n n s => samples) eps := by
    intro samples hsamp
    change rectOpNorm2Le (elementwiseTraceResidual s A samples) eps
    change rectOpNorm2Le
      (elementwiseTruncatedTraceResidual tau s A samples) eps at hsamp
    convert hsamp using 1
    ext i j
    simp [elementwiseTraceResidual, elementwiseTruncatedTraceResidual, htrunc]
  exact hprob'.trans (P.eventProb_mono hsubset)















































































































/-- Floating-point Algorithm 1 equation (2) corollary with the internal budget
matrix expanded to an explicit scalar radius depending on the truncated input.

The probability and sample-size hypotheses are exactly those of the
source-budget gamma-square theorem.  The conclusion no longer contains a
budget matrix: the FP additive term is
`n * (||Ahat||_F^2 / tau) * gamma fp (s+1)`. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_square
    (fp : FPModel) {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (n : ℝ) *
                ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  let B : Fin n → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
  let P := sqMagTraceProbability (steps := s) Ahat hden
  intro tau' Ahat'
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have hProb :
      1 - δ ≤
        P.eventProb
          (algorithm1FlTruncatedSpectralEvent fp tau s A
            (fun samples : ElementwiseTrace n n s => samples) eps B) := by
    simpa [P, tau, Ahat, B] using
      sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_square
        (fp := fp) (n := n) (s := s) (eps := eps) (δ := δ)
        hn hs A hden hδ hδ_le_one heps hsample hgamma hgamma1
  have hB :
      frobNormRect B ≤
        (n : ℝ) * ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) := by
    simpa [B, Ahat] using
      frobNormRect_sqMagTraceErrorBudget_zero_init_truncated_le_const_square
        fp htau hs A hgamma1
  have hsubset :
      algorithm1FlTruncatedSpectralEvent fp tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps B ⊆
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (n : ℝ) *
                ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
    intro samples h
    exact rectOpNorm2Le_mono (by linarith) h
  exact hProb.trans (P.eventProb_mono hsubset)

/-- Source-only floating-point Algorithm 1 equation (2) corollary.

This is the PDF-facing version of the previous theorem.  For the Drineas--
Zouzias threshold `tau = eps/(2n)`, hard-thresholding gives
`||Ahat||_F <= ||A||_F`, so the additive FP term is bounded explicitly by
`2*n^2*||A||_F^2*gamma fp (s+1)/eps`. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_square
    (fp : FPModel) {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  intro tau' Ahat'
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have hProb :
      1 - δ ≤
        P.eventProb
          {samples : ElementwiseTrace n n s |
            rectOpNorm2Le
              (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
              (eps +
                (n : ℝ) *
                  ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
    simpa [P, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_square
        (fp := fp) (n := n) (s := s) (eps := eps) (δ := δ)
        hn hs A hden hδ hδ_le_one heps hsample hgamma hgamma1
  have hFhat_le : frobNormSqRect Ahat ≤ frobNormSqRect A := by
    simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A
  have hgamma_nonneg : 0 ≤ gamma fp (s + 1) :=
    gamma_nonneg fp hgamma1
  have hterm_le :
      (n : ℝ) * ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) ≤
        (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
          gamma fp (s + 1) := by
    have hdiv :
        frobNormSqRect Ahat / tau ≤ frobNormSqRect A / tau :=
      div_le_div_of_nonneg_right hFhat_le (le_of_lt htau)
    have hmul_gamma :
        (frobNormSqRect Ahat / tau) * gamma fp (s + 1) ≤
          (frobNormSqRect A / tau) * gamma fp (s + 1) :=
      mul_le_mul_of_nonneg_right hdiv hgamma_nonneg
    have hmul_n :
        (n : ℝ) * ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) ≤
          (n : ℝ) * ((frobNormSqRect A / tau) * gamma fp (s + 1)) :=
      mul_le_mul_of_nonneg_left hmul_gamma (by positivity)
    have hrewrite :
        (n : ℝ) * ((frobNormSqRect A / tau) * gamma fp (s + 1)) =
          (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
            gamma fp (s + 1) := by
      dsimp [tau]
      field_simp [hn.ne', heps.ne']
    exact hmul_n.trans_eq hrewrite
  have hsubset :
      {samples : ElementwiseTrace n n s |
        rectOpNorm2Le
          (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
          (eps +
            (n : ℝ) *
              ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} ⊆
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
    intro samples h
    exact rectOpNorm2Le_mono (by linarith) h
  exact hProb.trans (P.eventProb_mono hsubset)



























































/-- Rectangular floating-point Algorithm 1 corollary with the internal budget
matrix expanded to a scalar radius depending on the truncated input. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_rect
    (fp : FPModel) {m n s : ℕ} {eps δ : ℝ}
    (hmn : 0 < (m : ℝ) * (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              Real.sqrt ((m : ℝ) * (n : ℝ)) *
                ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
  classical
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let B : Fin m → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
  let P := sqMagTraceProbability (steps := s) Ahat hden
  intro tau' Ahat'
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have hProb :
      1 - δ ≤
        P.eventProb
          (algorithm1FlTruncatedSpectralEvent fp tau s A
            (fun samples : ElementwiseTrace m n s => samples) eps B) := by
    simpa [P, tau, Ahat, B] using
      sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_rect
        (fp := fp) (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden hδ hδ_le_one heps hsample hgamma hgamma1
  have hB :
      frobNormRect B ≤
        Real.sqrt ((m : ℝ) * (n : ℝ)) *
          ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) := by
    simpa [B, Ahat] using
      frobNormRect_sqMagTraceErrorBudget_zero_init_truncated_le_const_rect
        fp htau hs A hgamma1
  have hsubset :
      algorithm1FlTruncatedSpectralEvent fp tau s A
          (fun samples : ElementwiseTrace m n s => samples) eps B ⊆
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              Real.sqrt ((m : ℝ) * (n : ℝ)) *
                ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
    intro samples h
    exact rectOpNorm2Le_mono (by linarith) h
  exact hProb.trans (P.eventProb_mono hsubset)

/-- Source-only rectangular floating-point Algorithm 1 corollary.

For `tau = eps/(2*sqrt(mn))`, hard-thresholding gives
`||Ahat||_F <= ||A||_F`, so the additive FP term is bounded explicitly by
`2*m*n*||A||_F^2*gamma fp (s+1)/eps`. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_rect
    (fp : FPModel) {m n s : ℕ} {eps δ : ℝ}
    (hmn : 0 < (m : ℝ) * (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
  classical
  let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
  let tau : ℝ := eps / (2 * R)
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  intro tau' Ahat'
  have hR_pos : 0 < R := by
    dsimp [R]
    exact Real.sqrt_pos.mpr hmn
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have hProb :
      1 - δ ≤
        P.eventProb
          {samples : ElementwiseTrace m n s |
            rectOpNorm2Le
              (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
              (eps +
                Real.sqrt ((m : ℝ) * (n : ℝ)) *
                  ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
    simpa [P, tau, Ahat, R] using
      sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_rect
        (fp := fp) (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden hδ hδ_le_one heps hsample hgamma hgamma1
  have hFhat_le : frobNormSqRect Ahat ≤ frobNormSqRect A := by
    simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A
  have hgamma_nonneg : 0 ≤ gamma fp (s + 1) :=
    gamma_nonneg fp hgamma1
  have hterm_le :
      Real.sqrt ((m : ℝ) * (n : ℝ)) *
          ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) ≤
        (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
          gamma fp (s + 1) := by
    have hdiv :
        frobNormSqRect Ahat / tau ≤ frobNormSqRect A / tau :=
      div_le_div_of_nonneg_right hFhat_le (le_of_lt htau)
    have hmul_gamma :
        (frobNormSqRect Ahat / tau) * gamma fp (s + 1) ≤
          (frobNormSqRect A / tau) * gamma fp (s + 1) :=
      mul_le_mul_of_nonneg_right hdiv hgamma_nonneg
    have hmul_R :
        Real.sqrt ((m : ℝ) * (n : ℝ)) *
            ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) ≤
          Real.sqrt ((m : ℝ) * (n : ℝ)) *
            ((frobNormSqRect A / tau) * gamma fp (s + 1)) :=
      mul_le_mul_of_nonneg_left hmul_gamma (le_of_lt hR_pos)
    have hrewrite :
        Real.sqrt ((m : ℝ) * (n : ℝ)) *
            ((frobNormSqRect A / tau) * gamma fp (s + 1)) =
          (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
            gamma fp (s + 1) := by
      have hR_sq :
          (Real.sqrt ((m : ℝ) * (n : ℝ))) ^ 2 = (m : ℝ) * (n : ℝ) :=
        Real.sq_sqrt (le_of_lt hmn)
      dsimp [tau, R]
      field_simp [hR_pos.ne', heps.ne']
      rw [hR_sq]
    exact hmul_R.trans_eq hrewrite
  have hsubset :
      {samples : ElementwiseTrace m n s |
        rectOpNorm2Le
          (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
          (eps +
            Real.sqrt ((m : ℝ) * (n : ℝ)) *
              ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} ⊆
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
    intro samples h
    exact rectOpNorm2Le_mono (by linarith) h
  exact hProb.trans (P.eventProb_mono hsubset)

/-- Literal rectangular Algorithm 1 exact spectral event at the rectangular
source sample budget, for inputs where the rectangular source threshold would
not remove any nonzero entry.

The probability law in the conclusion is the literal squared-magnitude law
`p_ij = A_ij^2 / ||A||_F^2`; no truncated matrix appears in the statement.
The explicit no-small-entry hypothesis proves that the rectangular
hard-thresholding parameter `eps/(2*sqrt(m*n))` acts as the identity on `A`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_rect
    {m n s : ℕ} {eps δ : ℝ}
    (hmn : 0 < (m : ℝ) * (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hentry :
      ∀ i j, A i j ≠ 0 →
        eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ))) ≤ |A i j|)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) eps) := by
  classical
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  have htrunc : elementwiseTruncate tau A = A :=
    elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge
      (tau := tau) A (by simpa [tau] using hentry)
  have hden_trunc : 0 < sqMagProbDen (elementwiseTruncate tau A) := by
    simpa [htrunc] using hden
  let P := sqMagTraceProbability (steps := s) A hden
  have hprob :
      1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (elementwiseTruncate tau A) hden_trunc).eventProb
          (algorithm1ExactTruncatedSpectralEvent tau s A
            (fun samples : ElementwiseTrace m n s => samples) eps) := by
    simpa [tau] using
      sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_rect
        (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden_trunc hδ hδ_le_one heps hsample
  have hP_eq :
      sqMagTraceProbability (steps := s)
        (elementwiseTruncate tau A) hden_trunc = P := by
    ext samples
    simp [P, sqMagTraceProbability, htrunc]
  have hprob' :
      1 - δ ≤ P.eventProb
        (algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace m n s => samples) eps) := by
    simpa [hP_eq] using hprob
  have hsubset :
      algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace m n s => samples) eps ⊆
        algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) eps := by
    intro samples hsamp
    change rectOpNorm2Le (elementwiseTraceResidual s A samples) eps
    change rectOpNorm2Le
      (elementwiseTruncatedTraceResidual tau s A samples) eps at hsamp
    convert hsamp using 1
    ext i j
    simp [elementwiseTraceResidual, elementwiseTruncatedTraceResidual, htrunc]
  exact hprob'.trans (P.eventProb_mono hsubset)

/-- Literal rectangular Algorithm 1 floating-point spectral event at the
rectangular source sample budget, for inputs where the rectangular source
threshold would not remove any nonzero entry.

The exact law is the literal squared-magnitude product law for `A`.  The
non-probability computation charged here is the rounded sampled-entry
rescaling, sketch accumulation, and residual formation; the FP additive radius
is the rectangular source-only gamma term
`2*m*n*||A||_F^2*gamma fp (s+1)/eps`. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_source_sample_budget_no_small_entries_rect
    (fp : FPModel) {m n s : ℕ} {eps δ : ℝ}
    (hmn : 0 < (m : ℝ) * (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hentry :
      ∀ i j, A i j ≠ 0 →
        eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ))) ≤ |A i j|)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (eps +
              (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
  classical
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  have htrunc : elementwiseTruncate tau A = A :=
    elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge
      (tau := tau) A (by simpa [tau] using hentry)
  have hden_trunc : 0 < sqMagProbDen (elementwiseTruncate tau A) := by
    simpa [htrunc] using hden
  let P := sqMagTraceProbability (steps := s) A hden
  let Radius : ℝ :=
    eps + (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
      gamma fp (s + 1)
  have hprob :
      1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (elementwiseTruncate tau A) hden_trunc).eventProb
          {samples : ElementwiseTrace m n s |
            rectOpNorm2Le
              (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
              Radius} := by
    simpa [tau, Radius] using
      sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_rect
        (fp := fp) (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden_trunc hδ hδ_le_one heps hsample hgamma hgamma1
  have hP_eq :
      sqMagTraceProbability (steps := s)
        (elementwiseTruncate tau A) hden_trunc = P := by
    ext samples
    simp [P, sqMagTraceProbability, htrunc]
  have hprob' :
      1 - δ ≤ P.eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            Radius} := by
    simpa [hP_eq] using hprob
  have hsubset :
      {samples : ElementwiseTrace m n s |
        rectOpNorm2Le
          (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
          Radius} ⊆
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            Radius} := by
    intro samples hsamp
    change rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples) Radius
    change rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidual fp tau s A samples) Radius at hsamp
    convert hsamp using 1
    ext i j
    simp [fl_elementwiseTraceResidual, fl_elementwiseTruncatedTraceResidual,
      htrunc]
  exact hprob'.trans (P.eventProb_mono hsubset)

/-- Literal Algorithm 1 floating-point spectral event at the source `n log n`
sample budget, for inputs where the source threshold would not remove any
nonzero entry.

This is the source-rate counterpart to the Frobenius/Markov literal corollary.
The probability law in the statement is the literal squared-magnitude law
`p_ij = A_ij^2 / ||A||_F^2`.  The extra no-small-entry condition makes the
Drineas--Zouzias threshold `eps/(2n)` an identity operation on `A`; it also
exposes the necessary denominator control for the floating-point update. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_source_sample_budget_no_small_entries_square
    (fp : FPModel) {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hentry :
      ∀ i j, A i j ≠ 0 → eps / (2 * (n : ℝ)) ≤ |A i j|)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (eps +
              (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  have htrunc : elementwiseTruncate tau A = A :=
    elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge
      (tau := tau) A (by simpa [tau] using hentry)
  have hden_trunc : 0 < sqMagProbDen (elementwiseTruncate tau A) := by
    simpa [htrunc] using hden
  let P := sqMagTraceProbability (steps := s) A hden
  let Radius : ℝ :=
    eps + (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
      gamma fp (s + 1)
  have hprob :
      let tau' : ℝ := eps / (2 * (n : ℝ))
      let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau' A
      1 - δ ≤
        (sqMagTraceProbability (steps := s) Ahat hden_trunc).eventProb
          {samples : ElementwiseTrace n n s |
            rectOpNorm2Le
              (fl_elementwiseTruncatedTraceResidual fp tau' s A samples)
              Radius} :=
    sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_square
      (fp := fp) (n := n) (s := s) (eps := eps) (δ := δ)
      hn hs A hden_trunc hδ hδ_le_one heps hsample hgamma hgamma1
  have hprob' :
      1 - δ ≤ P.eventProb
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            Radius} := by
    simpa [P, tau, htrunc, Radius, sqMagTraceProbability, sqMagSampleProbability]
      using hprob
  have hsubset :
      {samples : ElementwiseTrace n n s |
        rectOpNorm2Le
          (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
          Radius} ⊆
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            Radius} := by
    intro samples hsamp
    change rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples) Radius
    change rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidual fp tau s A samples) Radius at hsamp
    convert hsamp using 1
    ext i j
    simp [fl_elementwiseTraceResidual, fl_elementwiseTruncatedTraceResidual,
      htrunc]
  exact hprob'.trans (P.eventProb_mono hsubset)

/-- If every self-adjoint dilation increment of the truncated residual is
    Loewner-bounded above by `L I`, then the full truncated residual dilation is
    Loewner-bounded above by `(s * L) I`.

This is a deterministic accumulation lemma for bounded-increment hypotheses.
It is intentionally weaker than a matrix Bernstein theorem: it proves a
probability-one bound at the accumulated worst-case scale, not a concentration
bound at the variance scale. -/
theorem truncatedDilationIncrementLoewnerBoundedEvent_subset_exactDilationUpperEvent_sum_bound
    {m n s : ℕ} (tau : ℝ) (A : Fin m → Fin n → ℝ)
    (L : ℝ) (hs : (s : ℝ) ≠ 0) :
    truncatedDilationIncrementLoewnerBoundedEvent tau A L ⊆
      algorithm1ExactDilationUpperEvent s (elementwiseTruncate tau A)
        (fun samples : ElementwiseTrace m n s => samples) ((s : ℝ) * L) := by
  intro samples hBound z
  rw [finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
    (elementwiseTruncate tau A) samples hs z]
  calc
    (∑ t : Fin s,
        finiteQuadraticForm
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) (samples t))) z)
        ≤ ∑ _t : Fin s,
            finiteQuadraticForm
              (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) z := by
          apply Finset.sum_le_sum
          intro t _
          exact (hBound t).1 z
    _ = finiteQuadraticForm
          (fun a b : Fin m ⊕ Fin n => ((s : ℝ) * L) * finiteIdMatrix a b) z := by
          simp_rw [finiteQuadraticForm_smul_finiteIdMatrix]
          simp [mul_assoc]

/-- Under the truncated squared-magnitude product law, the exact truncated
    residual satisfies the accumulated one-sided dilation bound with
    probability one.

This theorem consumes the already-proved probability-one bounded-increment
side condition.  It is a weak deterministic consequence and is not advertised
as the CACM equation (2) matrix-concentration theorem. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactDilationUpperEvent_truncated_sum_bound_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (algorithm1ExactDilationUpperEvent s (elementwiseTruncate tau A)
        (fun samples : ElementwiseTrace m n s => samples)
        ((s : ℝ) *
          (Real.sqrt 2 *
            ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
              frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  let Bound : Set (ElementwiseTrace m n s) :=
    truncatedDilationIncrementLoewnerBoundedEvent tau A L
  let Upper : Set (ElementwiseTrace m n s) :=
    algorithm1ExactDilationUpperEvent s Ahat
      (fun samples : ElementwiseTrace m n s => samples) ((s : ℝ) * L)
  have hBoundProb : P.eventProb Bound = 1 := by
    simpa [P, Ahat, L, Bound] using
      sqMagTraceProbability_eventProb_truncatedDilationIncrementLoewnerBoundedEvent_eq_one
        htau hs A hden
  have hsubset : Bound ⊆ Upper := by
    simpa [Ahat, L, Bound, Upper] using
      truncatedDilationIncrementLoewnerBoundedEvent_subset_exactDilationUpperEvent_sum_bound
        tau A L (ne_of_gt hs)
  have hmono : P.eventProb Bound ≤ P.eventProb Upper :=
    P.eventProb_mono hsubset
  have hge : 1 ≤ P.eventProb Upper := by
    linarith
  have hle : P.eventProb Upper ≤ 1 := P.eventProb_le_one Upper
  have hUpper : P.eventProb Upper = 1 := le_antisymm hle hge
  simpa [P, Ahat, L, Upper] using hUpper

/-- Probability-one rectangular spectral consequence of the accumulated
    truncated bounded-increment dilation bound.

This is still only a worst-case accumulated bound.  It helps audit the
bounded-increment layer, but it does not replace the missing
matrix-Bernstein/trace-MGF proof for CACM equation (2). -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncated_sum_bound_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (algorithm1ExactSpectralEvent s (elementwiseTruncate tau A)
        (fun samples : ElementwiseTrace m n s => samples)
        ((s : ℝ) *
          (Real.sqrt 2 *
            ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
              frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  let Upper : Set (ElementwiseTrace m n s) :=
    algorithm1ExactDilationUpperEvent s Ahat
      (fun samples : ElementwiseTrace m n s => samples) ((s : ℝ) * L)
  let Spectral : Set (ElementwiseTrace m n s) :=
    algorithm1ExactSpectralEvent s Ahat
      (fun samples : ElementwiseTrace m n s => samples) ((s : ℝ) * L)
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
  have hε : 0 ≤ (s : ℝ) * L := mul_nonneg (le_of_lt hs) hL_nonneg
  have hUpperProb : P.eventProb Upper = 1 := by
    simpa [P, Ahat, L, Upper] using
      sqMagTraceProbability_eventProb_algorithm1ExactDilationUpperEvent_truncated_sum_bound_eq_one
        htau hs A hden
  have hsubset : Upper ⊆ Spectral := by
    simpa [Ahat, L, Upper, Spectral] using
      algorithm1ExactDilationUpperEvent_subset_exactSpectralEvent
        s Ahat (fun samples : ElementwiseTrace m n s => samples) ((s : ℝ) * L) hε
  have hmono : P.eventProb Upper ≤ P.eventProb Spectral :=
    P.eventProb_mono hsubset
  have hge : 1 ≤ P.eventProb Spectral := by
    linarith
  have hle : P.eventProb Spectral ≤ 1 := P.eventProb_le_one Spectral
  have hSpectral : P.eventProb Spectral = 1 := le_antisymm hle hge
  simpa [P, Ahat, L, Spectral] using hSpectral

/-- The eigenvalue upper event is exactly strong enough to produce the
    one-sided dilation Loewner event.  This is a deterministic vocabulary
    adapter, not a probability or concentration theorem. -/
theorem algorithm1ExactDilationEigenUpperEvent_subset_exactDilationUpperEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) :
    algorithm1ExactDilationEigenUpperEvent s A X ε ⊆
      algorithm1ExactDilationUpperEvent s A X ε := by
  intro ω hEigen
  exact
    (finiteLoewnerLe_smul_id_iff_finiteScalarUpperDiffEigenvalues_nonneg
      (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω)))
      (rectSelfAdjointDilation_symmetric
        (elementwiseTraceResidual s A (X ω)))
      ε).mpr hEigen

/-- An eigenvalue form of the one-sided dilation event implies the rectangular
    spectral event.  The probability of this eigenvalue event remains the
    missing matrix-concentration step. -/
theorem algorithm1ExactDilationEigenUpperEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (hε : 0 ≤ ε) :
    algorithm1ExactDilationEigenUpperEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X ε := by
  exact Set.Subset.trans
    (algorithm1ExactDilationEigenUpperEvent_subset_exactDilationUpperEvent
      s A X ε)
    (algorithm1ExactDilationUpperEvent_subset_exactSpectralEvent
      s A X ε hε)

/-- A squared dilation Loewner event implies the dilation operator event.
    This is a deterministic spectral-event adapter, not a concentration
    theorem. -/
theorem algorithm1ExactDilationSquareEvent_subset_exactDilationEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (hε : 0 ≤ ε) :
    algorithm1ExactDilationSquareEvent s A X ε ⊆
      algorithm1ExactDilationEvent s A X ε := by
  intro ω hSq
  exact rectSelfAdjointDilation_opNorm2Le_of_square_loewnerLe_scalar_id
    (elementwiseTraceResidual s A (X ω)) hε hSq

/-- A squared dilation Loewner event implies the rectangular spectral event.
    This is the event-level bridge for any future theorem proving the squared
    Loewner event with high probability. -/
theorem algorithm1ExactDilationSquareEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (hε : 0 ≤ ε) :
    algorithm1ExactDilationSquareEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X ε := by
  intro ω hSq
  exact rectOpNorm2Le_of_selfAdjointDilation_square_loewnerLe_scalar_id
    (elementwiseTraceResidual s A (X ω)) hε hSq

/-- Probability transfer from a self-adjoint dilation residual event to the
    exact rectangular operator event. It does not prove the dilation
    concentration theorem; it only connects a future matrix-concentration
    theorem to the repository's rectangular Algorithm 1 target. -/
theorem probability_algorithm1_exact_spectral_of_dilation
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ)
    (hDilationProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans hDilationProb
    (Pr.eventProb_mono
      (algorithm1ExactDilationEvent_subset_exactSpectralEvent s A X ε))

/-- Probability transfer from a one-sided self-adjoint-dilation Loewner event to
    the exact rectangular operator event.  It does not prove the
    largest-eigenvalue concentration theorem; it records the deterministic
    adapter needed once that probability bound is available. -/
theorem probability_algorithm1_exact_spectral_of_dilation_upper
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (hDilationUpperProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationUpperEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans hDilationUpperProb
    (Pr.eventProb_mono
      (algorithm1ExactDilationUpperEvent_subset_exactSpectralEvent
        s A X ε hε))

/-- Probability transfer from the eigenvalue form of the one-sided
    self-adjoint-dilation event to the exact rectangular operator event.  The
    theorem deliberately assumes only the probability of the eigenvalue event;
    proving that probability from matrix concentration remains separate. -/
theorem probability_algorithm1_exact_spectral_of_dilation_eigen_upper
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (hDilationEigenProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationEigenUpperEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans hDilationEigenProb
    (Pr.eventProb_mono
      (algorithm1ExactDilationEigenUpperEvent_subset_exactSpectralEvent
        s A X ε hε))

/-- Union-bound transfer from single-eigenvalue scalar events to the full
    dilation eigenvalue upper event.  This does not prove the scalar
    eigenvalue probabilities; it only combines them once supplied. -/
theorem probability_algorithm1_exact_dilation_eigen_upper_of_index_bounds
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ε : ℝ)
    (δ : (Fin m ⊕ Fin n) → ℝ)
    (hIndex :
      ∀ a : Fin m ⊕ Fin n,
        1 - δ a ≤
          Pr.eventProb
            (algorithm1ExactDilationEigenUpperIndexEvent s A X ε a)) :
    1 - ∑ a : Fin m ⊕ Fin n, δ a ≤
      Pr.eventProb (algorithm1ExactDilationEigenUpperEvent s A X ε) := by
  classical
  simpa [algorithm1ExactDilationEigenUpperEvent,
    algorithm1ExactDilationEigenUpperIndexEvent] using
    (Pr.eventProb_forall_ge_one_sub_sum
      (fun a : Fin m ⊕ Fin n =>
        algorithm1ExactDilationEigenUpperIndexEvent s A X ε a)
      δ hIndex)

/-- Union-bound transfer from single-eigenvalue scalar events all the way to
    the exact rectangular spectral event.  The scalar eigenvalue probability
    estimates remain separate concentration obligations. -/
theorem probability_algorithm1_exact_spectral_of_dilation_eigen_upper_index_bounds
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ε : ℝ) (hε : 0 ≤ ε)
    (δ : (Fin m ⊕ Fin n) → ℝ)
    (hIndex :
      ∀ a : Fin m ⊕ Fin n,
        1 - δ a ≤
          Pr.eventProb
            (algorithm1ExactDilationEigenUpperIndexEvent s A X ε a)) :
    1 - ∑ a : Fin m ⊕ Fin n, δ a ≤
      Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans
    (probability_algorithm1_exact_dilation_eigen_upper_of_index_bounds
      s A X Pr ε δ hIndex)
    (Pr.eventProb_mono
      (algorithm1ExactDilationEigenUpperEvent_subset_exactSpectralEvent
        s A X ε hε))

/-- Probability transfer from a squared dilation Loewner event to the exact
    rectangular operator event.  It keeps the future concentration theorem's
    target explicit: the probability of the squared Loewner event must still be
    proved separately. -/
theorem probability_algorithm1_exact_spectral_of_dilation_square
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (hDilationSqProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationSquareEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans hDilationSqProb
    (Pr.eventProb_mono
      (algorithm1ExactDilationSquareEvent_subset_exactSpectralEvent
        s A X ε hε))





























































/-- Event inclusion form of the deterministic spectral transfer. -/
theorem algorithm1ExactSpectralEvent_subset_flSpectralEvent
    (fp : FPModel) {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j) :
    algorithm1ExactSpectralEvent s A X ε ⊆
      algorithm1FlSpectralEvent fp s A X ε B := by
  intro ω hExact
  exact fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
    fp s A (X ω) B hExact hB_nonneg (hEntry ω)

/-- Probability transfer for Algorithm 1 spectral residuals.

If an exact spectral event has probability at least `ρ`, then the corresponding
floating-point spectral event has probability at least `ρ`, provided the
entrywise perturbation budget holds for every outcome.  The theorem transfers
probability mass; it does not prove the exact spectral concentration event. -/
theorem probability_algorithm1_fl_spectral_of_exact_spectral
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hExactProb :
      ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact le_trans hExactProb
    (Pr.eventProb_mono
      (algorithm1ExactSpectralEvent_subset_flSpectralEvent
        fp s A X ε B hB_nonneg hEntry))

/-- Probability transfer from a self-adjoint dilation residual event all the
    way to the floating-point rectangular operator event.  This is the
    composition point for a future matrix Bernstein/Khintchine theorem stated
    on the dilation. -/
theorem probability_algorithm1_fl_spectral_of_exact_dilation
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hDilationProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr ρ ε B hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_dilation
      s A X Pr ρ ε hDilationProb)

/-- Probability transfer from a one-sided self-adjoint-dilation Loewner event
    all the way to the floating-point rectangular operator event.  This is a
    deterministic FP transfer from a future largest-eigenvalue tail theorem, not
    the tail theorem itself. -/
theorem probability_algorithm1_fl_spectral_of_exact_dilation_upper
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hDilationUpperProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationUpperEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr ρ ε B hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_dilation_upper
      s A X Pr ρ ε hε hDilationUpperProb)

/-- Floating-point probability transfer from an eigenvalue form of the
    one-sided self-adjoint-dilation event.  This theorem is an adapter from a
    future largest-eigenvalue tail bound to the existing FP residual event; it
    does not prove the tail bound itself. -/
theorem probability_algorithm1_fl_spectral_of_exact_dilation_eigen_upper
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hDilationEigenProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationEigenUpperEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr ρ ε B hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_dilation_eigen_upper
      s A X Pr ρ ε hε hDilationEigenProb)

/-- Floating-point probability transfer from supplied single-eigenvalue scalar
    probability bounds.  This combines the finite union-bound adapter, the
    eigenvalue-to-spectral event adapter, and the existing FP perturbation
    transfer; it does not prove the scalar eigenvalue concentration bounds. -/
theorem probability_algorithm1_fl_spectral_of_exact_dilation_eigen_upper_index_bounds
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ε : ℝ) (hε : 0 ≤ ε)
    (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (δ : (Fin m ⊕ Fin n) → ℝ)
    (hIndex :
      ∀ a : Fin m ⊕ Fin n,
        1 - δ a ≤
          Pr.eventProb
            (algorithm1ExactDilationEigenUpperIndexEvent s A X ε a)) :
    1 - ∑ a : Fin m ⊕ Fin n, δ a ≤
      Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr (1 - ∑ a : Fin m ⊕ Fin n, δ a) ε B
    hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_dilation_eigen_upper_index_bounds
      s A X Pr ε hε δ hIndex)

/-- Probability transfer from a squared dilation Loewner event all the way to
    the floating-point rectangular operator event.  The concentration theorem
    for the squared Loewner event remains a separate obligation. -/
theorem probability_algorithm1_fl_spectral_of_exact_dilation_square
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hDilationSqProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationSquareEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr ρ ε B hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_dilation_square
      s A X Pr ρ ε hε hDilationSqProb)

/-- Probability transfer from an exact Frobenius residual event all the way to
    the floating-point rectangular operator event.

This is a bridge theorem: it closes no concentration claim by itself. It says
that a proved exact Frobenius residual event, combined with an entrywise
floating-point perturbation budget, gives the corresponding floating-point
operator-2 event. -/
theorem probability_algorithm1_fl_spectral_of_exact_frob
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hFrobProb :
      ρ ≤ Pr.eventProb (algorithm1ExactFrobEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr ρ ε B hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_frob s A X Pr ρ ε hFrobProb)


















































































































































end NumStability
