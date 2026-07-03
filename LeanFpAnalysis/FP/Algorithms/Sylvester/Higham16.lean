-- Algorithms/Sylvester/Higham16.lean
--
-- Source-facing Chapter 16 surfaces for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed.  This file complements the older square
-- Frobenius-norm Sylvester infrastructure in `SylvesterSpec`,
-- `SylvesterBackward`, and `SylvesterPerturbation`.

import LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterPerturbation
import LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterBackward

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- Rectangular source equations
-- ============================================================

/-- On square matrices, the rectangular product agrees with the repository's
    legacy square `matMul`. -/
theorem matMulRect_square_eq_matMul (n : Nat) (A B : Fin n -> Fin n -> Real) :
    matMulRect n n n A B = matMul n A B := by
  rfl

/-- Higham, 2nd ed., Chapter 16, equation (16.1):
    rectangular Sylvester operator `X |-> AX - XB`. -/
noncomputable def sylvesterOpRect (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (X : RMatFn m n) : RMatFn m n :=
  fun i j => matMulRect m m n A X i j - matMulRect m n n X B i j

/-- The square source-facing Sylvester operator is the existing legacy square
    operator used by the proved Chapter 16 infrastructure. -/
theorem sylvesterOpRect_square_eq_sylvesterOp (n : Nat)
    (A B X : Fin n -> Fin n -> Real) :
    sylvesterOpRect n n A B X = sylvesterOp n A B X := by
  rfl

/-- Higham, 2nd ed., Chapter 16, equation (16.1):
    the rectangular Sylvester equation predicate `AX - XB = C`. -/
def IsSylvesterSolutionRect (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X : RMatFn m n) : Prop :=
  forall i j, sylvesterOpRect m n A B X i j = C i j

/-- Higham, 2nd ed., Chapter 16, equations (16.9), (16.11), and (16.29):
    rectangular residual `C - (AY - YB)` for an approximate Sylvester solution. -/
noncomputable def sylvesterResidualRect (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Yhat : RMatFn m n) : RMatFn m n :=
  fun i j => C i j - sylvesterOpRect m n A B Yhat i j

/-- Rectangular residual expanded:
    `R_ij = C_ij - (AY)_ij + (YB)_ij`. -/
theorem sylvesterResidualRect_eq (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Yhat : RMatFn m n) :
    sylvesterResidualRect m n A B C Yhat =
    fun i j => C i j - matMulRect m m n A Yhat i j +
      matMulRect m n n Yhat B i j := by
  ext i j
  unfold sylvesterResidualRect sylvesterOpRect
  ring

-- ============================================================
-- Lyapunov specialization from Chapter 16.3
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.3:
    the Lyapunov equation is the Sylvester equation with `B = -A^T`. -/
theorem lyapunov_solution_iff_sylvester_special (n : Nat)
    (A C X : Fin n -> Fin n -> Real) :
    (forall i j, lyapunovOp n A X i j = C i j) <->
      (forall i j,
        sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j) := by
  constructor
  case mp =>
    intro h i j
    have hij := h i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  case mpr =>
    intro h i j
    have hij := h i j
    rw [(lyapunovOp_eq_sylvesterOp n A X).symm] at hij
    exact hij

/-- Higham, 2nd ed., Chapter 16.3:
    positive separation for `sep(A,-A^T)` gives uniqueness for the Lyapunov
    equation. -/
theorem lyapunov_unique_solution_of_sep (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (C X1 X2 : Fin n -> Fin n -> Real)
    (hX1 : forall i j, lyapunovOp n A X1 i j = C i j)
    (hX2 : forall i j, lyapunovOp n A X2 i j = C i j) :
    forall i j, X1 i j = X2 i j :=
  sep_implies_unique_solution n A (fun i j => -matTranspose A i j) sigma hSep
    C X1 X2
    ((lyapunov_solution_iff_sylvester_special n A C X1).mp hX1)
    ((lyapunov_solution_iff_sylvester_special n A C X2).mp hX2)

/-- If `X` solves a Lyapunov equation with a symmetric right-hand side, then
    `X^T` solves the same Lyapunov equation. -/
theorem lyapunov_transpose_solution_of_symmetric_rhs (n : Nat)
    (A C X : Fin n -> Fin n -> Real)
    (hC : IsSymmetric n C)
    (hX : forall i j, lyapunovOp n A X i j = C i j) :
    forall i j, lyapunovOp n A (matTranspose X) i j = C i j := by
  intro i j
  have hji := hX j i
  unfold lyapunovOp matMul matTranspose at hji
  unfold lyapunovOp matMul matTranspose
  calc
    (Finset.sum Finset.univ (fun k : Fin n => A i k * X j k)) +
        (Finset.sum Finset.univ (fun k : Fin n => X k i * A j k))
        = (Finset.sum Finset.univ (fun k : Fin n => X j k * A i k)) +
            (Finset.sum Finset.univ (fun k : Fin n => A j k * X k i)) := by
          have hleft :
              Finset.sum Finset.univ (fun k : Fin n => A i k * X j k) =
                Finset.sum Finset.univ (fun k : Fin n => X j k * A i k) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
          have hright :
              Finset.sum Finset.univ (fun k : Fin n => X k i * A j k) =
                Finset.sum Finset.univ (fun k : Fin n => A j k * X k i) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
          rw [hleft, hright]
    _ = (Finset.sum Finset.univ (fun k : Fin n => A j k * X k i)) +
          (Finset.sum Finset.univ (fun k : Fin n => X j k * A i k)) := by
          ring
    _ = C j i := hji
    _ = C i j := hC j i

/-- Higham, 2nd ed., Chapter 16.3:
    for a symmetric right-hand side, positive `sep(A,-A^T)` makes any
    Lyapunov solution symmetric, hence the solution is unique in the symmetric
    class. -/
theorem lyapunov_solution_symmetric_of_symmetric_rhs (n : Nat)
    (A C X : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hC : IsSymmetric n C)
    (hX : forall i j, lyapunovOp n A X i j = C i j) :
    IsSymmetric n X := by
  have hXT : forall i j, lyapunovOp n A (matTranspose X) i j = C i j :=
    lyapunov_transpose_solution_of_symmetric_rhs n A C X hC hX
  have huniq :=
    lyapunov_unique_solution_of_sep n A sigma hSep C X (matTranspose X) hX hXT
  intro i j
  exact huniq i j

-- ============================================================
-- Generalized equations from Chapter 16.5
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.5, equation (16.30):
    residual for the generalized Sylvester form `A X B + C X D = E`. -/
noncomputable def generalizedSylvesterAXB_CXD_residual (m n : Nat)
    (A C : RMatFn m m) (B D : RMatFn n n) (E X : RMatFn m n) : RMatFn m n :=
  fun i j =>
    matMulRect m n n (matMulRect m m n A X) B i j +
      matMulRect m n n (matMulRect m m n C X) D i j - E i j

/-- Higham, 2nd ed., Chapter 16.5, equation (16.31):
    coupled generalized Sylvester equation predicate
    `AX - YB = C` and `DX - YE = F`. -/
def IsGeneralizedSylvesterPairSolution (m n : Nat)
    (A D : RMatFn m m) (B E : RMatFn n n)
    (C F0 X Y : RMatFn m n) : Prop :=
  And
    (forall i j, matMulRect m m n A X i j - matMulRect m n n Y B i j = C i j)
    (forall i j, matMulRect m m n D X i j - matMulRect m n n Y E i j = F0 i j)

/-- Higham, 2nd ed., Chapter 16.5, equation (16.32):
    residual for the algebraic Riccati form `AX + XB - XFX + G = 0`. -/
noncomputable def riccatiResidual (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (F : RMatFn n m)
    (G X : RMatFn m n) : RMatFn m n :=
  fun i j =>
    matMulRect m m n A X i j +
      matMulRect m n n X B i j -
      matMulRect m m n (matMulRect m n m X F) X i j +
      G i j

end LeanFpAnalysis.FP
