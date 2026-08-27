import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Real.Sqrt

namespace HighamBench

open scoped BigOperators

/-- Real matrix-vector action used for the paper's real-equivalent FFT analysis. -/
noncomputable def p09MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Transpose in the paper-scoped real matrix notation. -/
def p09Transpose {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ A j i

/-- Scalar multiplication of a paper-scoped real matrix. -/
def p09ScaleMatrix {n : ℕ}
    (s : ℝ) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ s * A i j

/-- A candidate `Ainv` is a left inverse of `A`. -/
def p09IsLeftInverse {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, ∑ k : Fin n, Ainv i k * A k j = if i = j then 1 else 0

/-- A candidate `Ainv` is a right inverse of `A`. -/
def p09IsRightInverse {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, ∑ k : Fin n, A i k * Ainv k j = if i = j then 1 else 0

/-- Orthogonality of the normalized real-equivalent Fourier action. -/
def p09Orthogonal {n : ℕ} (Q : Fin n → Fin n → ℝ) : Prop :=
  p09IsLeftInverse Q (p09Transpose Q) ∧
    p09IsRightInverse Q (p09Transpose Q)

/-- Squared Euclidean norm of a finite real vector. -/
noncomputable def p09VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, x i ^ 2

/-- Euclidean norm of a finite real vector. -/
noncomputable def p09VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p09VecNorm2Sq x)

/-- Root-mean-square value used throughout the paper. -/
noncomputable def p09Rms {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  p09VecNorm2 x / Real.sqrt (n : ℝ)

/-- Maximum absolute coordinate of a finite real vector. -/
noncomputable def p09Max {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖x‖

/-- Coordinatewise sum of a finite family of error vectors. -/
noncomputable def p09VectorSum {m n : ℕ}
    (term : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j ↦ ∑ i : Fin m, term i j

end HighamBench
