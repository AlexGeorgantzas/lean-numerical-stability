import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- Square matrix-vector multiplication in the notation used for P08. -/
noncomputable def p08MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Square matrix multiplication in the notation used for P08. -/
noncomputable def p08MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Identity matrix for the paper-scoped matrix powers. -/
noncomputable def p08IdMatrix (n : ℕ) : Fin n → Fin n → ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Matrix powers used in the finite recurrence certificate for Lemma 4.3. -/
noncomputable def p08MatPow {n : ℕ}
    (B : Fin n → Fin n → ℝ) : ℕ → Fin n → Fin n → ℝ
  | 0 => p08IdMatrix n
  | k + 1 => p08MatMul B (p08MatPow B k)

/-- Componentwise absolute matrix action, `(abs A) (abs x)`. -/
noncomputable def p08AbsAction {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, |A i j| * |x j|

/-- The expanded componentwise action `(abs A) (abs Ainv) (abs q)`. -/
noncomputable def p08AbsProductAction {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) (q : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, |A i j| * p08AbsAction Ainv q j

/-- Recursive affine envelope used to expose the induction in P08 Lemma 4.3. -/
noncomputable def p08AffineEnvelope {n : ℕ}
    (B : Fin n → Fin n → ℝ) (s v : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => v
  | k + 1 => fun i ↦ p08MatVec B (p08AffineEnvelope B s v k) i + s i

end HighamBench
