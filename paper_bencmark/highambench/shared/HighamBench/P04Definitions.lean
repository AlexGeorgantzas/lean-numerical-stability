import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

namespace HighamBench

open scoped BigOperators

/-- P04's paper-local accumulated-error number `γₙ = n*u/(1-n*u)`. -/
noncomputable def p04Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

/-- Positivity condition for the denominator of `p04Gamma`. -/
def P04GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

/-- The mixed-precision block-FMA coefficient occurring in P04 equations
(3.4)--(3.6). -/
noncomputable def p04BlockFmaCoeff
    (uFma u : ℝ) (q n : ℕ) : ℝ :=
  p04Gamma uFma q + p04Gamma u n + p04Gamma uFma q * p04Gamma u n

/-- The factorization-stage coefficient in P04 equations (4.4) and (4.7). -/
noncomputable def p04FactorizationCoeff
    (uLow uFma u : ℝ) (q n b : ℕ) : ℝ :=
  2 * uLow + uLow ^ 2 +
    max
      (p04Gamma uFma (q - 1) + p04Gamma u (n - b + 1) +
        p04Gamma uFma (q - 1) * p04Gamma u (n - b + 1))
      (p04Gamma u b) * (1 + uLow) ^ 2

/-- Square matrix multiplication in the paper's finite-index notation. -/
noncomputable def p04MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- Matrix-vector multiplication in the paper's finite-index notation. -/
noncomputable def p04MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, A i j * x j

end HighamBench
