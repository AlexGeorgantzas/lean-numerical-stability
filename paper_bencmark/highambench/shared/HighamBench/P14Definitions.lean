import HighamBench.Core

/-!
# HighamBench P14 definitions

Paper-scoped definitions for Blanchard, Higham, and Higham's analysis of the
log-sum-exp and softmax functions.
-/

namespace HighamBench

open scoped BigOperators

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
    (fp : StandardAddModel) (wHat : Fin n → ℝ) (deltaDiv : ℝ)
    (j : Fin n) : ℝ :=
  (wHat j / recursiveSum fp.fl_add n wHat) * (1 + deltaDiv)

/-- Exact finite radius for the denominator error in the basic softmax
algorithm.  Its first-order value is `(n+1)u` when the exponential error is
bounded by `u`. -/
noncomputable def p14DenominatorRadius
    (u : ℝ) (n : ℕ) (epsilonExp : ℝ) : ℝ :=
  epsilonExp + gamma u n * (1 + epsilonExp)

/-- Exact finite radius for the combined numerator exponential and final
division errors. -/
noncomputable def p14NumeratorRadius
    (epsilonExp epsilonDiv : ℝ) : ℝ :=
  epsilonExp + epsilonDiv + epsilonExp * epsilonDiv

end HighamBench
