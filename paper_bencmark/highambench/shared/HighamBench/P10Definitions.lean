import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed

open scoped BigOperators Matrix.Norms.Frobenius

namespace HighamBench

/-- A square real matrix in the native finite `Matrix` representation. -/
abbrev P10Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Finite square matrix multiplication. -/
noncomputable def p10MatMul (n : ℕ) (A B : P10Matrix n) : P10Matrix n :=
  A * B

/-- The Frobenius norm, written explicitly to keep the public statement lightweight. -/
noncomputable def p10FrobNorm {n : ℕ} (A : P10Matrix n) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)

/-- Exact computed product with inherited input perturbations and a local product error. -/
noncomputable def p10PerturbedProduct (n : ℕ)
    (A dA B dB E : P10Matrix n) : P10Matrix n :=
  p10MatMul n (A + dA) (B + dB) + E

/-- The exact local, inherited-left, inherited-right, and cross-term error expansion. -/
noncomputable def p10ProductErrorExpansion (n : ℕ)
    (A dA B dB E : P10Matrix n) : P10Matrix n :=
  E + (p10MatMul n A dB +
    (p10MatMul n dA B + p10MatMul n dA dB))

/-- The one-level amplification factor in the Sylvester recurrence on printed page 86. -/
noncomputable def p10SylvesterGrowth {n : ℕ}
    (A B : P10Matrix n) (sep : ℝ) : ℝ :=
  4 + 2 * (p10FrobNorm A + p10FrobNorm B) / sep

/-- The one-level forcing term in the Sylvester recurrence on printed page 86. -/
noncomputable def p10SylvesterForcing {n : ℕ}
    (A B C R : P10Matrix n) (sep epsilon mu : ℝ) : ℝ :=
  epsilon / sep *
    (3 * p10FrobNorm C +
      2 * mu * (p10FrobNorm A + p10FrobNorm B) * p10FrobNorm R)

end HighamBench
