import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas

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

/-! ## Basic positive exponential-sum execution -/

/-- A real-valued execution certificate for lines 1--5 of Algorithm 3.1.
The relative equations are exactly the paper's no-overflow/no-underflow model:
each exponential is evaluated with relative error at most `u`, then the
computed exponentials are accumulated from left to right. -/
structure P14BasicSumExecution {n : ℕ} (x : Fin n → ℝ) (u : ℝ) where
  fp : StandardAddModel
  unit_eq : fp.u = u
  expError : Fin n → ℝ
  expError_le : ∀ i, |expError i| ≤ u

/-- The computed exponential `wHat_i` in equation (3.1). -/
noncomputable def p14ComputedExp {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : P14BasicSumExecution x u) (i : Fin n) : ℝ :=
  Real.exp (x i) * (1 + run.expError i)

/-- The paper's `sTilde`: the exact sum of the computed exponentials. -/
noncomputable def p14ExactComputedExpSum {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : P14BasicSumExecution x u) : ℝ :=
  ∑ i, p14ComputedExp run i

/-- The paper's `sHat`: the recursively computed sum in Algorithm 3.1. -/
noncomputable def p14RecursiveComputedExpSum {n : ℕ}
    {x : Fin n → ℝ} {u : ℝ} (run : P14BasicSumExecution x u) : ℝ :=
  recursiveSum run.fp.fl_add n (p14ComputedExp run)

/-- The additive error `Delta s` from equation (3.3). -/
noncomputable def p14BasicSumDelta {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : P14BasicSumExecution x u) : ℝ :=
  p14RecursiveComputedExpSum run - p14ExpSum x

/-- Exact finite envelope whose first-order term is the paper's loose
`(n+1)u*s` bound. The `gamma_n` summation radius deliberately retains the
paper's final weakening rather than replacing equation (3.3) by the tighter
`gamma_(n-1)` addition-only estimate. -/
noncomputable def p14BasicSumFiniteEnvelope
    (n : ℕ) (u exactSum : ℝ) : ℝ :=
  (u + gamma u n * (1 + u)) * exactSum

/-- The explicit second-and-higher-order part of the finite envelope. -/
noncomputable def p14BasicSumQuadraticRemainder
    (n : ℕ) (exactSum u : ℝ) : ℝ :=
  ((n : ℝ) * (n + 1 : ℝ) * exactSum * u ^ 2) /
    (1 - (n : ℝ) * u)

end HighamBench
