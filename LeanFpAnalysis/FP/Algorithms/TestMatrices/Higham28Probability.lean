/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import LeanFpAnalysis.FP.Algorithms.TestMatrices.Higham28Exact
import LeanFpAnalysis.FP.Algorithms.TestMatrices.Higham28Stewart
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Polynomial.Roots

namespace LeanFpAnalysis.FP

/-! # Higham Chapter 28: precise probability statement surfaces

The chapter's two precise probabilistic prose claims are instantiated here on
standard product Gaussian and product uniform measures.  These declarations
make the remaining probability dependencies exact without assuming either
limit/almost-sure conclusion.
-/

open MeasureTheory Filter ProbabilityTheory

local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

noncomputable def realGinibreMeasure (n : ℕ) : Measure (RSqMat n) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1))

noncomputable def realEigenvalueCount (n : ℕ) (A : RSqMat n) : ℕ :=
  (Matrix.charpoly A).roots.card

noncomputable def expectedRealEigenvalueCount (n : ℕ) : ℝ :=
  ∫ A : RSqMat n, (realEigenvalueCount n A : ℝ) ∂realGinibreMeasure n

/-- Precise standard-limit formulation of the real-Ginibre prose on p. 517. -/
def RealGinibreExpectedCountLimit : Prop :=
  Tendsto (fun n : ℕ => expectedRealEigenvalueCount n / Real.sqrt n)
    atTop (nhds (Real.sqrt (2 / Real.pi)))

noncomputable def uniformUnitIntervalMatrixMeasure (n : ℕ) : Measure (RSqMat n) :=
  Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)))

def strictlyPositiveMatrixSet (n : ℕ) : Set (RSqMat n) :=
  {A | ∀ i j, 0 < A i j}

def HasPositiveDominantEigenvalue {n : ℕ} (A : RSqMat n) : Prop :=
  ∃ r : ℝ, 0 < r ∧ (Matrix.charpoly A).IsRoot r ∧
    ∀ z : ℂ, ((Matrix.charpoly A).map Complex.ofRealHom).IsRoot z → ‖z‖ ≤ r

def positiveDominantEigenvalueSet (n : ℕ) : Set (RSqMat n) :=
  {A | HasPositiveDominantEigenvalue A}

/-- Precise almost-sure formulation of the iid-uniform Perron prose on p. 517. -/
def UniformPositivePerronAlmostSure : Prop :=
  ∀ n : ℕ, 0 < n →
    uniformUnitIntervalMatrixMeasure n
      (strictlyPositiveMatrixSet n ∩ positiveDominantEigenvalueSet n) = 1

/-! ## Explicit-domain probability transfers and compatibility predicates -/

/-- The standard real-Ginibre product law is normalized.  This is the
nonvacuity check for the probability space used by the expectation transfer
below; no random-matrix spectral claim is hidden in it. -/
theorem realGinibreMeasure_univ (n : ℕ) :
    realGinibreMeasure n Set.univ = 1 := by
  unfold realGinibreMeasure
  calc
    (Measure.pi (fun _ : Fin n =>
        Measure.pi (fun _ : Fin n => gaussianReal 0 1))) Set.univ =
        ∏ i : Fin n,
          Measure.pi (fun _ : Fin n => gaussianReal 0 1) Set.univ :=
      MeasureTheory.Measure.pi_univ _
    _ = 1 := by simp

/-- Higham, 2nd ed., pp. 516-517: explicit-domain transfer of the real
Ginibre expected-real-root limit.  `a` is the coefficient sequence delivered
by the cited finite-`n` expectation calculation; the two premises are the
genuine upstream finite formula and its Gamma/Stirling estimate. -/
theorem realGinibreExpectedCountLimit_of_coefficient_formula
    (a : ℕ → ℝ)
    (hfinite : ∀ n, expectedRealEigenvalueCount n = a n)
    (hestimate : Tendsto (fun n : ℕ => a n / Real.sqrt n)
      atTop (nhds (Real.sqrt (2 / Real.pi)))) :
    RealGinibreExpectedCountLimit := by
  unfold RealGinibreExpectedCountLimit
  convert hestimate using 1
  funext n
  rw [hfinite]

/-- The standard iid restricted-volume matrix law is normalized. -/
theorem uniformUnitIntervalMatrixMeasure_univ (n : ℕ) :
    uniformUnitIntervalMatrixMeasure n Set.univ = 1 := by
  unfold uniformUnitIntervalMatrixMeasure
  calc
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n =>
        volume.restrict (Set.Icc (0 : ℝ) 1)))) Set.univ =
        ∏ i : Fin n, Measure.pi (fun _ : Fin n =>
          volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ :=
      MeasureTheory.Measure.pi_univ _
    _ = 1 := by simp [MeasureTheory.Measure.pi_univ]

/-- The strict-positivity event is genuinely inhabited in every dimension;
the all-ones matrix is a concrete witness. -/
theorem strictlyPositiveMatrixSet_nonempty (n : ℕ) :
    (strictlyPositiveMatrixSet n).Nonempty := by
  refine ⟨fun _ _ => 1, ?_⟩
  simp [strictlyPositiveMatrixSet]

/-- Higham, 2nd ed., p. 517: explicit-domain transfer from the two missing
foundations, namely boundary-nullness of the product law and the deterministic
Perron theorem for entrywise-positive matrices.  Neither premise restates the
almost-sure intersection conclusion. -/
theorem uniformPositivePerronAlmostSure_of_boundary_null_of_perron
    (hpositive : ∀ n : ℕ, 0 < n →
      uniformUnitIntervalMatrixMeasure n (strictlyPositiveMatrixSet n) = 1)
    (hperron : ∀ {n : ℕ} (A : RSqMat n),
      A ∈ strictlyPositiveMatrixSet n → HasPositiveDominantEigenvalue A) :
    UniformPositivePerronAlmostSure := by
  intro n hn
  have hset : strictlyPositiveMatrixSet n ∩ positiveDominantEigenvalueSet n =
      strictlyPositiveMatrixSet n := by
    ext A
    constructor
    · exact fun h => h.1
    · intro hA
      exact ⟨hA, hperron A hA⟩
  rw [hset, hpositive n hn]

/-- An ambient-matrix compatibility predicate for a normalized orthogonally
supported, left-invariant law.  This is useful as a transfer surface, but is
not Mathlib's group-level `Measure.IsHaarMeasure` endpoint and does not by
itself prove Stewart's Theorem 28.1.  The exact source push-forward and exact
group-level endpoint are `stewartOrthogonalGroupLaw` and
`StewartTheorem28_1HaarConclusion`. -/
def IsNormalizedOrthogonalHaarLaw (n : ℕ) (mu : Measure (RSqMat n)) : Prop :=
  mu Set.univ = 1 ∧
    mu {Q | IsOrthogonal n Q} = 1 ∧
    ∀ (U : RSqMat n), IsOrthogonal n U →
      ∀ s : Set (RSqMat n), MeasurableSet s →
        mu ((fun Q => U * Q) ⁻¹' s) = mu s

/-- Constructor for the ambient compatibility predicate from its three
fields.  This is a packaging lemma only: callers must still produce
normalization, orthogonal support, and left invariance, and the theorem does
not identify Stewart's Gaussian push-forward with group Haar measure. -/
theorem stewartLaw_isNormalizedOrthogonalHaarLaw
    {n : ℕ} (mu : Measure (RSqMat n))
    (hmass : mu Set.univ = 1)
    (hsupport : mu {Q | IsOrthogonal n Q} = 1)
    (hinvariant : ∀ (U : RSqMat n), IsOrthogonal n U →
      ∀ s : Set (RSqMat n), MeasurableSet s →
        mu ((fun Q => U * Q) ⁻¹' s) = mu s) :
    IsNormalizedOrthogonalHaarLaw n mu :=
  ⟨hmass, hsupport, hinvariant⟩

/-- The ambient compatibility predicate is inhabited in dimension zero: the
matrix space is a singleton, so the Dirac law at the identity has all three
fields.  This is not a nonvacuity witness for Stewart's positive-dimensional
Gaussian producer or its Haar conclusion. -/
theorem diracIdentity_isNormalizedOrthogonalHaarLaw_zero :
    IsNormalizedOrthogonalHaarLaw 0
      (Measure.dirac (1 : RSqMat 0)) := by
  refine ⟨by simp, ?_, ?_⟩
  · have horth : ∀ Q : RSqMat 0, IsOrthogonal 0 Q := by
      intro Q
      rw [Subsingleton.elim Q (1 : RSqMat 0)]
      exact IsOrthogonal.id 0
    have hset : {Q : RSqMat 0 | IsOrthogonal 0 Q} = Set.univ := by
      ext Q
      simp [horth Q]
    rw [hset]
    simp
  · intro U hU s hs
    have hpre : (fun Q : RSqMat 0 => U * Q) ⁻¹' s = s := by
      ext Q
      have hmul : U * Q = Q := Subsingleton.elim _ _
      change U * Q ∈ s ↔ Q ∈ s
      rw [hmul]
    rw [hpre]

end LeanFpAnalysis.FP
