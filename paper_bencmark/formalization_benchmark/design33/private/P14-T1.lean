import NumStability.Algorithms.Summation.Recursive.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Private admission skeleton only. Never give this file or its declaration names to
either measured formalizer. The paper PDF and neutral task packet are their
only target statement sources.
-/

namespace HighamBenchCandidate

open scoped BigOperators
open NumStability

/-- The positive exponential evaluations and recursive sum in the basic
log-sum-exp algorithm. The paper's no-overflow/no-underflow relative model is
represented by an FPModel for arithmetic and one error for each exponential. -/
structure P14BasicSumRun {n : ℕ} (x : Fin n → ℝ) (u : ℝ) where
  fp : FPModel
  unit_eq : fp.u = u
  expError : Fin n → ℝ
  expError_le : ∀ i, |expError i| ≤ u

noncomputable def p14ComputedExp {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : P14BasicSumRun x u) (i : Fin n) : ℝ :=
  Real.exp (x i) * (1 + run.expError i)

noncomputable def p14ExactSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, Real.exp (x i)

noncomputable def p14ComputedSum {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : P14BasicSumRun x u) : ℝ :=
  fl_recursiveSum run.fp n (p14ComputedExp run)

noncomputable def p14SumError {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : P14BasicSumRun x u) : ℝ :=
  p14ComputedSum run - p14ExactSum x

noncomputable def p14FiniteEnvelope (n : ℕ) (u s : ℝ) : ℝ :=
  (u + ((n : ℝ) * u / (1 - (n : ℝ) * u)) * (1 + u)) * s

noncomputable def p14QuadraticRemainder (n : ℕ) (s u : ℝ) : ℝ :=
  ((n : ℝ) * (n + 1 : ℝ) * s * u ^ 2) / (1 - (n : ℝ) * u)

/-- Source: Blanchard--Higham--Higham, equation (3.3), together with the
explicit positive-sum and exponential/recursive-sum steps that yield it.
The exact finite envelope is a strengthening of the printed first-order
coefficient; the displayed remainder certifies its O(u²) content. -/
theorem target
    {n : ℕ} (hn : 0 < n) {ι : Type*} {l : Filter ι} [l.NeBot]
    (x : Fin n → ℝ) (u : ι → ℝ)
    (run : ∀ t, P14BasicSumRun x (u t))
    (hu : Filter.Tendsto u l (nhds 0)) :
    let s := p14ExactSum x
    0 < s ∧
    (∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i)) ∧
    (∀ᶠ t in l,
      |(∑ i, p14ComputedExp (run t) i) - p14ComputedSum (run t)| ≤
        ((n - 1 : ℕ) : ℝ) * u t /
          (1 - ((n - 1 : ℕ) : ℝ) * u t) *
            ∑ i, |p14ComputedExp (run t) i|) ∧
    (∀ᶠ t in l,
      |p14SumError (run t)| ≤ p14FiniteEnvelope n (u t) s) ∧
    (∀ᶠ t in l,
      p14FiniteEnvelope n (u t) s =
        (n + 1 : ℝ) * u t * s + p14QuadraticRemainder n s (u t)) ∧
    (fun t => p14QuadraticRemainder n s (u t)) =O[l]
      (fun t => (u t) ^ 2) ∧
    ∀ t, p14ComputedSum (run t) = s + p14SumError (run t) := by
  sorry

end HighamBenchCandidate
