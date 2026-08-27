import Mathlib.Analysis.Matrix.Normed

open scoped BigOperators Matrix.Norms.Frobenius

namespace HighamBench

/-- Square real matrices used for the finite P11 certificates. -/
abbrev P11Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Matrix multiplication in the P11 setting. -/
noncomputable def p11MatMul (n : ℕ) (A B : P11Matrix n) : P11Matrix n :=
  A * B

/-- Matrix transpose in the P11 setting. -/
def p11Transpose {n : ℕ} (A : P11Matrix n) : P11Matrix n :=
  A.transpose

/-- The identity matrix. -/
def p11Identity (n : ℕ) : P11Matrix n :=
  1

/-- Explicit Frobenius norm for the condition-neutral public statements. -/
noncomputable def p11FrobNorm {n : ℕ} (A : P11Matrix n) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)

/-- Explicit Euclidean norm for a finite real vector. -/
noncomputable def p11VecNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Matrix-vector multiplication. -/
noncomputable def p11MatVec {n : ℕ} (A : P11Matrix n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  A.mulVec x

/-- The loss-of-orthogonality matrix appearing in Theorem 1(7). -/
noncomputable def p11OrthogonalityDefect {n : ℕ}
    (Q : P11Matrix n) : P11Matrix n :=
  p11Identity n - p11MatMul n (p11Transpose Q) Q

/-- The normal-equations residual in Theorem 1(5). -/
noncomputable def p11NormalEquationResidual {n : ℕ}
    (A R : P11Matrix n) : P11Matrix n :=
  p11MatMul n (p11Transpose R) R -
    p11MatMul n (p11Transpose A) A

/-- The exact inner residual in the appendix derivation of Theorem 1(7). -/
noncomputable def p11DefectCore {n : ℕ}
    (A dA R : P11Matrix n) : P11Matrix n :=
  p11NormalEquationResidual A R -
    p11MatMul n (p11Transpose A) dA -
    p11MatMul n (p11Transpose dA) A -
    p11MatMul n (p11Transpose dA) dA

end HighamBench
