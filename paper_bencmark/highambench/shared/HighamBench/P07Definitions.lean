import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- Euclidean norm in the finite real-vector notation used by P07. -/
noncomputable def p07VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Rectangular matrix-vector multiplication. -/
noncomputable def p07MatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Product of two compatible finite rectangular matrices. -/
noncomputable def p07RectMatMul {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ) :
    Fin m → Fin p → ℝ :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Homogeneous rectangular operator-2 upper-bound certificate. -/
def p07RectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x, p07VecNorm2 (p07MatVec A x) ≤ c * p07VecNorm2 x

/-- Homogeneous lower singular-value certificate. -/
def p07RectLowerBound {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x, c * p07VecNorm2 x ≤ p07VecNorm2 (p07MatVec A x)

/-- A rectangular matrix acts isometrically on Euclidean vectors. -/
def p07Isometry {m n : ℕ} (Q : Fin m → Fin n → ℝ) : Prop :=
  ∀ x, p07VecNorm2 (p07MatVec Q x) = p07VecNorm2 x

/-- Paired lower/upper singular-value certificate used to express the
condition-number identity in P07 Lemma 2.1 without choosing singular values. -/
def p07ConditionCertificate {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (lower upper : ℝ) : Prop :=
  p07RectLowerBound A lower ∧ p07RectOpNorm2Le A upper

/-- Exact error matrix expanded in the proof of P07 Theorem 3.5. -/
noncomputable def p07BackwardError {m n : ℕ}
    (Y ΔY : Fin m → Fin n → ℝ)
    (R ΔR : Fin n → Fin n → ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j ↦
    (p07RectMatMul Y R i j - A i j) +
      (p07RectMatMul ΔY R i j +
        (p07RectMatMul Y ΔR i j + p07RectMatMul ΔY ΔR i j))

end HighamBench
