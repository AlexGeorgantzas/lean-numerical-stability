import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# HighamBench P14 definitions

Paper-scoped definitions for Blanchard, Higham, and Higham's analysis of the
log-sum-exp and softmax functions.
-/

namespace HighamBench

open scoped BigOperators

/-- The P14-local rounded-addition model used by softmax summation. -/
structure P14StandardAddModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add :
    ∀ x y : ℝ, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)

/-- P14's accumulated-error number `γₙ = n*u/(1-n*u)`. -/
noncomputable def p14Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

/-- Positivity condition for the denominator of `p14Gamma`. -/
def P14GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

/-- P14-local left-to-right recursive summation. -/
noncomputable def p14RecursiveSum (flAdd : ℝ → ℝ → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then
        v ⟨0, by simp⟩
      else
        flAdd
          (p14RecursiveSum flAdd n (fun i => v i.castSucc))
          (v (Fin.last n))

/-- The positive exponential sum appearing in log-sum-exp and softmax. -/
noncomputable def p14ExpSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, Real.exp (x i)

/-- The exact softmax component `exp(x_j) / sum_i exp(x_i)`. -/
noncomputable def p14Softmax {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.exp (x j) / p14ExpSum x

/-- A finite certificate for a computed basic softmax component.  The
exponentials `wHat` are recursively summed, and `deltaDiv` records the final
relative division error. -/
noncomputable def p14ComputedSoftmax {n : ℕ}
    (fp : P14StandardAddModel) (wHat : Fin n → ℝ) (deltaDiv : ℝ)
    (j : Fin n) : ℝ :=
  (wHat j / p14RecursiveSum fp.fl_add n wHat) * (1 + deltaDiv)

/-- Exact finite radius for the denominator error in the basic softmax
algorithm.  Its first-order value is `(n+1)u` when the exponential error is
bounded by `u`. -/
noncomputable def p14DenominatorRadius
    (u : ℝ) (n : ℕ) (epsilonExp : ℝ) : ℝ :=
  epsilonExp + p14Gamma u n * (1 + epsilonExp)

/-- Exact finite radius for the combined numerator exponential and final
division errors. -/
noncomputable def p14NumeratorRadius
    (epsilonExp epsilonDiv : ℝ) : ℝ :=
  epsilonExp + epsilonDiv + epsilonExp * epsilonDiv

end HighamBench
