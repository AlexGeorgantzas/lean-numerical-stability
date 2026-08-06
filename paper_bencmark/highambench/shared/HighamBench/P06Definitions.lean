import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- Euclidean norm in the finite real-vector notation used by P06. -/
noncomputable def p06VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Rectangular Frobenius norm in P06's finite matrix notation. -/
noncomputable def p06FrobNorm {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)

/-- Rectangular matrix-vector multiplication. -/
noncomputable def p06MatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- The homogeneous rectangular operator-2 upper-bound predicate. -/
def p06RectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (L : ℝ) : Prop :=
  ∀ x, p06VecNorm2 (p06MatVec A x) ≤ L * p06VecNorm2 x

/-- Euclidean norm on an arbitrary finite index type, needed for a dilation. -/
noncomputable def p06FiniteVecNorm2 {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- Matrix-vector multiplication on an arbitrary finite index type. -/
noncomputable def p06FiniteMatVec {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i ↦ ∑ j, A i j * x j

/-- Quadratic form on an arbitrary finite real matrix. -/
noncomputable def p06FiniteQuadraticForm {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, x i * p06FiniteMatVec A x i

/-- Identity matrix on an arbitrary finite decidable index type. -/
noncomputable def p06FiniteId {ι : Type*} [DecidableEq ι] : ι → ι → ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Quadratic-form (Loewner) order used to express the largest-eigenvalue
threshold in P06 equation (3.4) without introducing eigenvalue machinery. -/
def p06FiniteLoewnerLe {ι : Type*} [Fintype ι]
    (A B : ι → ι → ℝ) : Prop :=
  ∀ x, p06FiniteQuadraticForm A x ≤ p06FiniteQuadraticForm B x

/-- P06 equation (3.3): the symmetric dilation `[[0,M],[Mᵀ,0]]`. -/
noncomputable def p06SelfAdjointDilation {m n : ℕ}
    (M : Fin m → Fin n → ℝ) :
    (Fin m ⊕ Fin n) → (Fin m ⊕ Fin n) → ℝ :=
  fun a b ↦
    match a, b with
    | Sum.inl i, Sum.inr j => M i j
    | Sum.inr j, Sum.inl i => M i j
    | _, _ => 0

/-- The exact state obtained after the first `r` unperturbed transformations.
The recurrence represents `P_(r-1) ⋯ P_0 b`. -/
noncomputable def p06ExactState {m : ℕ}
    (P : ℕ → Fin m → Fin m → ℝ) (b : Fin m → ℝ) :
    ℕ → Fin m → ℝ
  | 0 => b
  | r + 1 => p06MatVec (P r) (p06ExactState P b r)

/-- The coefficient of the terms containing exactly one local perturbation.
This is the recursive form of the insertion sum in P06 equations (4.8)--(4.9). -/
noncomputable def p06FirstOrderState {m : ℕ}
    (P E : ℕ → Fin m → Fin m → ℝ) (b : Fin m → ℝ) :
    ℕ → Fin m → ℝ
  | 0 => fun _ ↦ 0
  | r + 1 => fun i ↦
      p06MatVec (P r) (p06FirstOrderState P E b r) i +
        p06MatVec (E r) (p06ExactState P b r) i

/-- The sum of all terms containing at least two local perturbations, after
factoring out `t²` from transformations `P_r + t E_r`. -/
noncomputable def p06HigherOrderState {m : ℕ}
    (t : ℝ) (P E : ℕ → Fin m → Fin m → ℝ)
    (b : Fin m → ℝ) : ℕ → Fin m → ℝ
  | 0 => fun _ ↦ 0
  | r + 1 => fun i ↦
      p06MatVec (P r) (p06HigherOrderState t P E b r) i +
        p06MatVec (E r) (p06FirstOrderState P E b r) i +
        t * p06MatVec (E r) (p06HigherOrderState t P E b r) i

/-- State obtained from the fully perturbed sequence `P_r + t E_r`. -/
noncomputable def p06PerturbedState {m : ℕ}
    (t : ℝ) (P E : ℕ → Fin m → Fin m → ℝ)
    (b : Fin m → ℝ) : ℕ → Fin m → ℝ
  | 0 => b
  | r + 1 =>
      p06MatVec (fun i j ↦ P r i j + t * E r i j)
        (p06PerturbedState t P E b r)

end HighamBench
