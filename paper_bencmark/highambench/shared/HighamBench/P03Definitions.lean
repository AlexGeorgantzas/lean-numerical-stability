import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

/-!
# HighamBench P03 definitions

Condition-neutral finite matrix/vector notation for the Carson--Higham
three-precision iterative-refinement tasks.  The arithmetic contracts used by
the targets are supplied explicitly as hypotheses; this file contains no
evaluated-library import.
-/

namespace HighamBench

open scoped BigOperators

/-- Finite real matrix-vector multiplication used in the P03 paper model. -/
noncomputable def p03MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, A i j * x j

/-- Finite real matrix multiplication used in the P03 paper model. -/
noncomputable def p03MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  ∑ j : Fin n, A i j * B j k

/-- Componentwise absolute value of a P03 vector. -/
noncomputable def p03VecAbs {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |x i|

/-- The inverse-action contract for the nonnegative M-matrix inverse `M₁`
used in the proof of P03 Theorem 5.1. -/
def P03ResolventInverse {n : ℕ}
    (M P : Fin n → Fin n → ℝ) : Prop :=
  (∀ i k : Fin n, 0 ≤ M i k) ∧
    ∀ (z : Fin n → ℝ) (i : Fin n),
      p03MatVec M (fun k => z k - p03MatVec P z k) i = z i

end HighamBench
