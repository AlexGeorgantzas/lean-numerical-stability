import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- The finite square matrix product used in P05's LU and Cholesky bounds. -/
noncomputable def p05MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- Matrix transpose in P05's finite-index notation. -/
noncomputable def p05Transpose {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A j i

/-- The componentwise absolute product `|A||B|` used by both factorization
backward-error bounds in P05. -/
noncomputable def p05AbsMatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, |A i k| * |B k j|

/-- The three source families across which the proof of P05 Lemma 4.1
distributes its scalar residual: `c`, the computed result, and the products. -/
noncomputable def p05CoefficientSource {k : ℕ}
    (computed c : ℝ) (products : Fin k → ℝ) :
    Option (Option (Fin k)) → ℝ
  | none => c
  | some none => computed
  | some (some i) => products i

end HighamBench
