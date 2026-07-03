-- Algorithms/Sylvester/Higham16.lean
--
-- Source-facing Chapter 16 surfaces for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed.  This file complements the older square
-- Frobenius-norm Sylvester infrastructure in `SylvesterSpec`,
-- `SylvesterBackward`, and `SylvesterPerturbation`.

import LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterPerturbation
import LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterBackward
import Mathlib.LinearAlgebra.Matrix.Vec

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
-- Vec/Kronecker formulation from Chapter 16.1
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2):
    the product-index coefficient matrix
    `I_n kron A - B^T kron I_m` for vectorized rectangular Sylvester systems.
    The product index follows Mathlib's column-stacking `Matrix.vec` convention:
    `(j,i)` denotes entry `(i,j)`. -/
noncomputable def sylvesterVecCoeff (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) :
    Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real :=
  Matrix.kronecker (1 : Matrix (Fin n) (Fin n) Real) A -
    Matrix.kronecker (Matrix.transpose B) (1 : Matrix (Fin m) (Fin m) Real)

/-- Higham, 2nd ed., Chapter 16.1, prose following equation (16.2):
    `vec(A X B) = (B^T kron A) vec(X)` for finite matrices. -/
theorem vec_triple_product_rect (m k n p : Nat)
    (A : Matrix (Fin m) (Fin k) Real)
    (X : Matrix (Fin k) (Fin n) Real)
    (B : Matrix (Fin n) (Fin p) Real) :
    Matrix.vec (A * X * B) =
      Matrix.mulVec (Matrix.kronecker (Matrix.transpose B) A) (Matrix.vec X) := by
  simpa [Matrix.kronecker] using
    (Matrix.kronecker_mulVec_vec A X (Matrix.transpose B)).symm

/-- Left multiplication by `A` in vectorized form, the `I_n kron A` half of
    equation (16.2). -/
theorem vec_left_mul_rect (m k n : Nat)
    (A : Matrix (Fin m) (Fin k) Real)
    (X : Matrix (Fin k) (Fin n) Real) :
    Matrix.vec (A * X) =
      Matrix.mulVec
        (Matrix.kronecker (1 : Matrix (Fin n) (Fin n) Real) A)
        (Matrix.vec X) := by
  simpa [Matrix.kronecker] using Matrix.vec_mul_eq_mulVec A X

/-- Right multiplication by `B` in vectorized form, the `B^T kron I_m` half of
    equation (16.2). -/
theorem vec_right_mul_rect (m n p : Nat)
    (X : Matrix (Fin m) (Fin n) Real)
    (B : Matrix (Fin n) (Fin p) Real) :
    Matrix.vec (X * B) =
      Matrix.mulVec
        (Matrix.kronecker (Matrix.transpose B)
          (1 : Matrix (Fin m) (Fin m) Real))
        (Matrix.vec X) := by
  simpa [Matrix.kronecker] using
    (Matrix.kronecker_mulVec_vec (1 : Matrix (Fin m) (Fin m) Real)
      X (Matrix.transpose B)).symm

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2):
    applying `I_n kron A - B^T kron I_m` to `vec(X)` gives
    `vec(AX - XB)`. -/
theorem sylvesterVecCoeff_mulVec_vec (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (X : RMatFn m n) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) =
      Matrix.vec (sylvesterOpRect m n A B X) := by
  ext p
  have hleft := congrFun (vec_left_mul_rect m m n A X) p
  have hright := congrFun (vec_right_mul_rect m n n X B) p
  unfold sylvesterVecCoeff
  simp only [Pi.sub_apply, Matrix.sub_mulVec, hleft.symm, hright.symm]
  simp [sylvesterOpRect, matMulRect, Matrix.vec, Matrix.mul_apply]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2):
    the vectorized linear system is equivalent to the rectangular Sylvester
    equation. -/
theorem sylvester_vec_system_iff_solution (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X : RMatFn m n) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) = Matrix.vec C <->
      IsSylvesterSolutionRect m n A B C X := by
  constructor
  case mp =>
    intro h i j
    have hp := congrFun h (j, i)
    rw [sylvesterVecCoeff_mulVec_vec] at hp
    exact hp
  case mpr =>
    intro h
    rw [sylvesterVecCoeff_mulVec_vec]
    ext p
    exact h p.2 p.1

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), diagonal case:
    if `A` and `B` are diagonal in the chosen bases, the vec/Kronecker
    Sylvester coefficient is diagonal with entries `a_i - b_j`.
    This is the algebraic finite-index core of the general eigenvalue
    difference formula. -/
theorem sylvesterVecCoeff_diagonal (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b) =
      Matrix.diagonal (fun p : Prod (Fin n) (Fin m) => a p.2 - b p.1) := by
  ext p q
  by_cases h1 : p.1 = q.1
  case pos =>
    by_cases h2 : p.2 = q.2
    case pos =>
      cases p
      cases q
      simp_all [sylvesterVecCoeff, Matrix.kronecker, Matrix.diagonal]
    case neg =>
      have hpq : Not (p = q) := by
        intro hpq
        exact h2 (congrArg Prod.snd hpq)
      simp [sylvesterVecCoeff, Matrix.kronecker, Matrix.diagonal, h1, h2, hpq]
  case neg =>
    have h1' : Not (q.1 = p.1) := by
      intro h
      exact h1 h.symm
    have hpq : Not (p = q) := by
      intro hpq
      exact h1 (congrArg Prod.fst hpq)
    by_cases h2 : p.2 = q.2
    case pos =>
      simp [sylvesterVecCoeff, Matrix.kronecker, Matrix.diagonal, h1, h1', h2, hpq]
    case neg =>
      simp [sylvesterVecCoeff, Matrix.kronecker, Matrix.diagonal, h1, h1', h2, hpq]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), diagonal case:
    determinant of the diagonal-basis vec/Kronecker coefficient. -/
theorem sylvesterVecCoeff_diagonal_det (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    (sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b)).det =
      Finset.prod Finset.univ (fun p : Prod (Fin n) (Fin m) => a p.2 - b p.1) := by
  rw [sylvesterVecCoeff_diagonal, Matrix.det_diagonal]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), diagonal case:
    the diagonal-basis vec/Kronecker coefficient is nonsingular exactly when
    no diagonal entry of `A` equals a diagonal entry of `B`. -/
theorem sylvesterVecCoeff_diagonal_det_ne_zero_iff (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    Not ((sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b)).det = 0) <->
      forall i j, Not (a i - b j = 0) := by
  rw [sylvesterVecCoeff_diagonal_det]
  constructor
  case mp =>
    intro h i j
    have hall := Finset.prod_ne_zero_iff.mp h
    exact hall (j, i) (by simp)
  case mpr =>
    intro h
    exact Finset.prod_ne_zero_iff.mpr (by
      intro p _hp
      exact h p.2 p.1)

-- ============================================================
-- Exact Schur-coordinate algebra from Chapter 16.1
-- ============================================================

private theorem rectMatMul_left_right_sub {m n p q : Nat}
    (A : Fin m -> Fin n -> Real) (B C : Fin n -> Fin p -> Real)
    (D : Fin p -> Fin q -> Real) :
    rectMatMul A (rectMatMul (fun i j => B i j - C i j) D) =
      fun i j => rectMatMul A (rectMatMul B D) i j -
        rectMatMul A (rectMatMul C D) i j := by
  ext i j
  unfold rectMatMul
  rw [(Finset.sum_sub_distrib (s := Finset.univ)
    (f := fun k : Fin n => A i k * Finset.sum Finset.univ (fun k1 : Fin p =>
      B k k1 * D k1 j))
    (g := fun k : Fin n => A i k * Finset.sum Finset.univ (fun k1 : Fin p =>
      C k k1 * D k1 j))).symm]
  apply Finset.sum_congr rfl
  intro k _
  rw [(mul_sub (A i k)
    (Finset.sum Finset.univ (fun k1 : Fin p => B k k1 * D k1 j))
    (Finset.sum Finset.univ (fun k1 : Fin p => C k k1 * D k1 j))).symm]
  apply congrArg (fun z => A i k * z)
  rw [(Finset.sum_sub_distrib (s := Finset.univ)
    (f := fun k1 : Fin p => B k k1 * D k1 j)
    (g := fun k1 : Fin p => C k k1 * D k1 j)).symm]
  apply Finset.sum_congr rfl
  intro k1 _
  ring

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5):
    exact Sylvester-operator algebra in supplied Schur coordinates.  If
    `A = U R U^T`, `B = V S V^T`, and `U,V` are orthogonal, then
    substituting `X = U Y V^T` transforms `AX - XB` into
    `U (RY - YS) V^T`.  This conditional wrapper does not assert existence
    of Schur decompositions or any triangular/quasi-triangular structure. -/
theorem sylvester_schur_transform_identity (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V))) :
    sylvesterOpRect m n A B (rectMatMul U (rectMatMul Y (matTranspose V))) =
      rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) := by
  subst A
  subst B
  have hUtU : rectMatMul (matTranspose U) U = idMatrix m := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.left_inv i j
  have hVtV : rectMatMul (matTranspose V) V = idMatrix n := by
    ext i j
    simpa [rectMatMul, idMatrix] using hV.left_inv i j
  have hleft :
      rectMatMul (rectMatMul U (rectMatMul R (matTranspose U)))
          (rectMatMul U (rectMatMul Y (matTranspose V))) =
        rectMatMul U (rectMatMul (rectMatMul R Y) (matTranspose V)) := by
    calc
      rectMatMul (rectMatMul U (rectMatMul R (matTranspose U)))
          (rectMatMul U (rectMatMul Y (matTranspose V)))
          = rectMatMul U (rectMatMul (rectMatMul R (matTranspose U))
              (rectMatMul U (rectMatMul Y (matTranspose V)))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul R
              (rectMatMul (matTranspose U) (rectMatMul U (rectMatMul Y (matTranspose V))))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul R
              (rectMatMul (rectMatMul (matTranspose U) U) (rectMatMul Y (matTranspose V)))) := by
              exact congrArg (fun Z => rectMatMul U (rectMatMul R Z))
                (rectMatMul_assoc (matTranspose U) U (rectMatMul Y (matTranspose V))).symm
      _ = rectMatMul U (rectMatMul R
              (rectMatMul (idMatrix m) (rectMatMul Y (matTranspose V)))) := by
              rw [hUtU]
      _ = rectMatMul U (rectMatMul R (rectMatMul Y (matTranspose V))) := by
              rw [rectMatMul_id_left]
      _ = rectMatMul U (rectMatMul (rectMatMul R Y) (matTranspose V)) := by
              exact congrArg (rectMatMul U) (rectMatMul_assoc R Y (matTranspose V)).symm
  have hright :
      rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
          (rectMatMul V (rectMatMul S (matTranspose V))) =
        rectMatMul U (rectMatMul (rectMatMul Y S) (matTranspose V)) := by
    calc
      rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
          (rectMatMul V (rectMatMul S (matTranspose V)))
          = rectMatMul U (rectMatMul (rectMatMul Y (matTranspose V))
              (rectMatMul V (rectMatMul S (matTranspose V)))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul Y
              (rectMatMul (matTranspose V) (rectMatMul V (rectMatMul S (matTranspose V))))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul Y
              (rectMatMul (rectMatMul (matTranspose V) V) (rectMatMul S (matTranspose V)))) := by
              exact congrArg (fun Z => rectMatMul U (rectMatMul Y Z))
                (rectMatMul_assoc (matTranspose V) V (rectMatMul S (matTranspose V))).symm
      _ = rectMatMul U (rectMatMul Y
              (rectMatMul (idMatrix n) (rectMatMul S (matTranspose V)))) := by
              rw [hVtV]
      _ = rectMatMul U (rectMatMul Y (rectMatMul S (matTranspose V))) := by
              rw [rectMatMul_id_left]
      _ = rectMatMul U (rectMatMul (rectMatMul Y S) (matTranspose V)) := by
              exact congrArg (rectMatMul U) (rectMatMul_assoc Y S (matTranspose V)).symm
  have hcombine :
      rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) =
        fun i j => rectMatMul U (rectMatMul (rectMatMul R Y) (matTranspose V)) i j -
          rectMatMul U (rectMatMul (rectMatMul Y S) (matTranspose V)) i j := by
    simpa [sylvesterOpRect, matMulRect_eq_rectMatMul] using
      (rectMatMul_left_right_sub U (rectMatMul R Y) (rectMatMul Y S) (matTranspose V))
  unfold sylvesterOpRect
  simp only [matMulRect_eq_rectMatMul]
  rw [hleft, hright]
  exact hcombine.symm

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
-- A posteriori source wrapper from Chapter 16.4
-- ============================================================

/-- Higham, 2nd ed., Chapter 16, equation (16.28), relative source form:
    divide the existing Frobenius residual-error bound by the norm of the
    exact solution. -/
theorem sylvester_relative_aposteriori_bound (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSep : SepLowerBound n A B sigma)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X :=
  div_le_div_of_nonneg_right
    (sylvester_aposteriori_bound n A B C X Xhat sigma hSigma hSep hExact hE_ne)
    (le_of_lt hX_pos)

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

/-- Higham, 2nd ed., Chapter 16.5, equation (16.30):
    source equation predicate for `A X B + C X D = E`. -/
def IsGeneralizedSylvesterAXB_CXD_Solution (m n : Nat)
    (A C : RMatFn m m) (B D : RMatFn n n) (E X : RMatFn m n) : Prop :=
  forall i j,
    matMulRect m n n (matMulRect m m n A X) B i j +
      matMulRect m n n (matMulRect m m n C X) D i j = E i j

/-- The residual for equation (16.30) is zero exactly when the generalized
    Sylvester equation holds. -/
theorem generalizedSylvesterAXB_CXD_residual_zero_iff_solution (m n : Nat)
    (A C : RMatFn m m) (B D : RMatFn n n) (E X : RMatFn m n) :
    (forall i j, generalizedSylvesterAXB_CXD_residual m n A C B D E X i j = 0) <->
      IsGeneralizedSylvesterAXB_CXD_Solution m n A C B D E X := by
  constructor
  case mp =>
    intro h i j
    have hij := h i j
    unfold generalizedSylvesterAXB_CXD_residual at hij
    linarith
  case mpr =>
    intro h i j
    have hij := h i j
    unfold IsGeneralizedSylvesterAXB_CXD_Solution at h
    unfold generalizedSylvesterAXB_CXD_residual
    linarith

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

/-- Higham, 2nd ed., Chapter 16.5, equation (16.32):
    source equation predicate for `A X + X B - X F X + G = 0`. -/
def IsRiccatiSolution (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (F : RMatFn n m)
    (G X : RMatFn m n) : Prop :=
  forall i j,
    matMulRect m m n A X i j +
      matMulRect m n n X B i j -
      matMulRect m m n (matMulRect m n m X F) X i j +
      G i j = 0

/-- The residual for equation (16.32) is zero exactly when the Riccati source
    equation holds. -/
theorem riccatiResidual_zero_iff_solution (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (F : RMatFn n m)
    (G X : RMatFn m n) :
    (forall i j, riccatiResidual m n A B F G X i j = 0) <->
      IsRiccatiSolution m n A B F G X := by
  constructor
  case mp =>
    intro h i j
    exact h i j
  case mpr =>
    intro h i j
    exact h i j

end LeanFpAnalysis.FP
