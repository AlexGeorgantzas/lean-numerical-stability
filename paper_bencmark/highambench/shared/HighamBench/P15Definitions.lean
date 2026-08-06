import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed

/-!
# HighamBench P15 definitions

Paper-scoped finite matrix notation for Higham and Mary's analysis of block
low-rank LU factorization and triangular solves.
-/

namespace HighamBench

open scoped BigOperators Matrix.Norms.Frobenius

/-- A finite square real matrix in the P15 model. -/
abbrev P15Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A finite real vector in the P15 model. -/
abbrev P15Vector (n : ℕ) := Fin n → ℝ

/-- Exact finite matrix multiplication. -/
noncomputable def p15MatMul {n : ℕ} (A B : P15Matrix n) : P15Matrix n :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Exact finite matrix-vector multiplication. -/
noncomputable def p15MatVec {n : ℕ} (A : P15Matrix n)
    (x : P15Vector n) : P15Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Frobenius norm used throughout P15. -/
noncomputable def p15FrobNorm {n : ℕ} (A : P15Matrix n) : ℝ :=
  ‖A‖

/-- Euclidean vector norm used for the right-hand-side estimate in Theorem 4.5. -/
noncomputable def p15VecNorm {n : ℕ} (x : P15Vector n) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Exact matrix perturbation obtained by composing a perturbed factorization
with perturbed forward and backward substitutions. -/
noncomputable def p15ComposedMatrixError {n : ℕ}
    (factorError lowerError upperError L U : P15Matrix n) : P15Matrix n :=
  factorError + p15MatMul lowerError U +
    p15MatMul L upperError + p15MatMul lowerError upperError

/-- Exact right-hand-side perturbation obtained by composing the two
triangular solves. -/
noncomputable def p15ComposedRhsError {n : ℕ}
    (rhsLower rhsUpper : P15Vector n)
    (L lowerError : P15Matrix n) : P15Vector n :=
  rhsLower + p15MatVec L rhsUpper + p15MatVec lowerError rhsUpper

end HighamBench
