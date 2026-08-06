import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed

/-!
# HighamBench P16 definitions

Paper-scoped finite-dimensional notation for the modular backward-error
analysis of GMRES and restarted GMRES.
-/

namespace HighamBench

open scoped BigOperators Matrix.Norms.Frobenius

/-- A finite square real matrix in the P16 model. -/
abbrev P16Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A finite real vector in the P16 model. -/
abbrev P16Vector (n : ℕ) := Fin n → ℝ

/-- Exact finite matrix-vector multiplication. -/
noncomputable def p16MatVec {n : ℕ} (A : P16Matrix n)
    (x : P16Vector n) : P16Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Frobenius norm used in the paper's normwise backward error. -/
noncomputable def p16FrobNorm {n : ℕ} (A : P16Matrix n) : ℝ :=
  ‖A‖

/-- Euclidean vector norm. -/
noncomputable def p16VecNorm {n : ℕ} (x : P16Vector n) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Exact residual `b - A x`. -/
noncomputable def p16Residual {n : ℕ} (A : P16Matrix n)
    (b x : P16Vector n) : P16Vector n :=
  b - p16MatVec A x

/-- Frobenius condition-number factor represented by a matrix and a supplied
inverse. The T3 target needs only its exact nonnegativity. -/
noncomputable def p16ConditionNumberF {n : ℕ}
    (A Ainv : P16Matrix n) : ℝ :=
  p16FrobNorm A * p16FrobNorm Ainv

/-- The mixed-precision contraction factor from Theorem 6.3. -/
noncomputable def p16MixedContraction {n : ℕ}
    (c uLow : ℝ) (A Ainv : P16Matrix n) : ℝ :=
  c * uLow * p16ConditionNumberF A Ainv

/-- High-precision backward-error floor from Theorem 6.3. -/
noncomputable def p16BackwardFloor (c uHigh : ℝ) : ℝ :=
  c * uHigh

/-- High-precision forward-error floor from Theorem 6.3. -/
noncomputable def p16ForwardFloor {n : ℕ}
    (c uHigh : ℝ) (A Ainv : P16Matrix n) : ℝ :=
  c * uHigh * p16ConditionNumberF A Ainv

end HighamBench
