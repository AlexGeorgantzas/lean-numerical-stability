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

/-- Higham, 2nd ed., Chapter 16, equation (16.22):
    vectorized/Kronecker form of the full perturbation identity, including the
    second-order terms. -/
theorem sylvester_perturbation_equation_vec (n : Nat)
    (A B C X dA dB dC dX : Fin n -> Fin n -> Real)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hPerturbed : forall i j, sylvesterOp n
      (fun i' j' => A i' j' + dA i' j')
      (fun i' j' => B i' j' + dB i' j')
      (fun i' j' => X i' j' + dX i' j') i j = C i j + dC i j) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) (Matrix.vec dX) =
      Matrix.vec (fun i j =>
        dC i j - matMul n dA X i j + matMul n X dB i j -
          matMul n dA dX i j + matMul n dX dB i j) := by
  rw [sylvesterVecCoeff_mulVec_vec]
  ext p
  simpa [sylvesterOpRect] using
    sylvester_perturbation_equation n A B C X dA dB dC dX
      hExact hPerturbed p.2 p.1

/-- Higham, 2nd ed., Chapter 16, equation (16.22), first-order form:
    after dropping second-order perturbation products, the vec/Kronecker
    coefficient sends `vec(dX)` to the vectorized first-order right-hand side. -/
theorem sylvester_perturbation_first_order_vec (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) (Matrix.vec dX) =
      Matrix.vec (fun i j =>
        dC i j - matMul n dA X i j + matMul n X dB i j) := by
  rw [sylvesterVecCoeff_mulVec_vec]
  ext p
  simpa [sylvesterOpRect] using
    sylvester_perturbation_first_order n A B X dA dB dC dX hLin p.2 p.1

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

private theorem rectMatMul_schur_coords_cancel {m n : Nat}
    (U : RMatFn m m) (V : RMatFn n n) (M : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V) :
    rectMatMul (matTranspose U)
      (rectMatMul (rectMatMul U (rectMatMul M (matTranspose V))) V) = M := by
  have hUtU : rectMatMul (matTranspose U) U = idMatrix m := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.left_inv i j
  have hVtV : rectMatMul (matTranspose V) V = idMatrix n := by
    ext i j
    simpa [rectMatMul, idMatrix] using hV.left_inv i j
  calc
    rectMatMul (matTranspose U)
        (rectMatMul (rectMatMul U (rectMatMul M (matTranspose V))) V)
        = rectMatMul (rectMatMul (matTranspose U)
            (rectMatMul U (rectMatMul M (matTranspose V)))) V := by
            exact (rectMatMul_assoc (matTranspose U)
              (rectMatMul U (rectMatMul M (matTranspose V))) V).symm
    _ = rectMatMul (rectMatMul (rectMatMul (matTranspose U) U)
            (rectMatMul M (matTranspose V))) V := by
            exact congrArg (fun Z => rectMatMul Z V)
              (rectMatMul_assoc (matTranspose U) U (rectMatMul M (matTranspose V))).symm
    _ = rectMatMul (rectMatMul (idMatrix m) (rectMatMul M (matTranspose V))) V := by
            rw [hUtU]
    _ = rectMatMul (rectMatMul M (matTranspose V)) V := by
            rw [rectMatMul_id_left]
    _ = rectMatMul M (rectMatMul (matTranspose V) V) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul M (idMatrix n) := by
            rw [hVtV]
    _ = M := by
            rw [rectMatMul_id_right]

private theorem rectMatMul_schur_coords_expand {m n : Nat}
    (U : RMatFn m m) (V : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V) :
    rectMatMul U
      (rectMatMul (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V)) = C := by
  have hUUt : rectMatMul U (matTranspose U) = idMatrix m := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.right_inv i j
  have hVVt : rectMatMul V (matTranspose V) = idMatrix n := by
    ext i j
    simpa [rectMatMul, idMatrix] using hV.right_inv i j
  calc
    rectMatMul U
        (rectMatMul (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V))
        = rectMatMul (rectMatMul U
            (rectMatMul (matTranspose U) (rectMatMul C V))) (matTranspose V) := by
            exact (rectMatMul_assoc U
              (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V)).symm
    _ = rectMatMul (rectMatMul (rectMatMul U (matTranspose U))
            (rectMatMul C V)) (matTranspose V) := by
            exact congrArg (fun Z => rectMatMul Z (matTranspose V))
              (rectMatMul_assoc U (matTranspose U) (rectMatMul C V)).symm
    _ = rectMatMul (rectMatMul (idMatrix m) (rectMatMul C V)) (matTranspose V) := by
            rw [hUUt]
    _ = rectMatMul (rectMatMul C V) (matTranspose V) := by
            rw [rectMatMul_id_left]
    _ = rectMatMul C (rectMatMul V (matTranspose V)) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul C (idMatrix n) := by
            rw [hVVt]
    _ = C := by
            rw [rectMatMul_id_right]

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5):
    equation-level Schur-coordinate form.  Under supplied orthogonal
    factorizations `A = U R U^T` and `B = V S V^T`, the substitution
    `X = U Y V^T` solves `AX - XB = C` exactly when `Y` solves
    `RY - YS = U^T C V`. -/
theorem sylvester_schur_transform_solution_iff (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V))) :
    IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul Y (matTranspose V))) <->
      IsSylvesterSolutionRect m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) Y := by
  constructor
  case mp =>
    intro h
    have htrans := sylvester_schur_transform_identity m n U R A V S B Y hU hV hA hB
    have hUMVt :
        rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) = C := by
      rw [htrans.symm]
      ext i j
      exact h i j
    have hM :
        sylvesterOpRect m n R S Y =
          rectMatMul (matTranspose U) (rectMatMul C V) := by
      calc
        sylvesterOpRect m n R S Y =
            rectMatMul (matTranspose U)
              (rectMatMul (rectMatMul U
                (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V))) V) := by
                exact (rectMatMul_schur_coords_cancel U V
                  (sylvesterOpRect m n R S Y) hU hV).symm
        _ = rectMatMul (matTranspose U) (rectMatMul C V) := by
                rw [hUMVt]
    intro i j
    exact congrFun (congrFun hM i) j
  case mpr =>
    intro h
    have hM :
        sylvesterOpRect m n R S Y =
          rectMatMul (matTranspose U) (rectMatMul C V) := by
      ext i j
      exact h i j
    have hUMVt :
        rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) = C := by
      rw [hM]
      exact rectMatMul_schur_coords_expand U V C hU hV
    have htrans := sylvester_schur_transform_identity m n U R A V S B Y hU hV hA hB
    have hsol :
        sylvesterOpRect m n A B (rectMatMul U (rectMatMul Y (matTranspose V))) = C := by
      rw [htrans]
      exact hUMVt
    intro i j
    exact congrFun (congrFun hsol i) j

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
-- Separation infimum from Chapter 16.4
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    feasible Frobenius ratios for `sep(A,B)`.  The nonzero condition is
    represented by `frobNormSq X` to match the existing square infrastructure. -/
def sylvesterSepRatios (n : Nat) (A B : Fin n -> Fin n -> Real) : Set Real :=
  {rho | exists X : Fin n -> Fin n -> Real,
    Not (frobNormSq X = 0) /\
      rho = frobNorm (sylvesterOp n A B X) / frobNorm X}

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    `sep(A,B)` modeled as the infimum of the nonzero Frobenius ratios.
    This records the exact source object without asserting that the infimum is
    attained by a minimizing matrix. -/
noncomputable def sylvesterSepInf (n : Nat) (A B : Fin n -> Fin n -> Real) : Real :=
  sInf (sylvesterSepRatios n A B)

/-- The exact `sep(A,B)` ratio set is bounded below by zero. -/
theorem sylvesterSepRatios_bddBelow (n : Nat) (A B : Fin n -> Fin n -> Real) :
    BddBelow (sylvesterSepRatios n A B) := by
  refine Exists.intro 0 ?_
  intro rho hrho
  cases hrho with
  | intro X hrest =>
      cases hrest with
      | intro _hX hrho_eq =>
          rw [hrho_eq]
          exact div_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

/-- The exact infimum model of `sep(A,B)` from equation (16.26) is
    nonnegative, since every feasible Frobenius ratio is nonnegative. -/
theorem sylvesterSepInf_nonneg (n : Nat) (A B : Fin n -> Fin n -> Real) :
    0 <= sylvesterSepInf n A B := by
  unfold sylvesterSepInf
  apply Real.sInf_nonneg
  intro rho hrho
  rcases hrho with ⟨X, _hX, hrho_eq⟩
  rw [hrho_eq]
  exact div_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

/-- Every nonzero Frobenius ratio is above the infimum model of `sep(A,B)`. -/
theorem sylvesterSepInf_le_ratio (n : Nat) (A B X : Fin n -> Fin n -> Real)
    (hX : Not (frobNormSq X = 0)) :
    sylvesterSepInf n A B <= frobNorm (sylvesterOp n A B X) / frobNorm X := by
  unfold sylvesterSepInf
  exact csInf_le (sylvesterSepRatios_bddBelow n A B)
    (Exists.intro X (And.intro hX rfl))

/-- A positive `SepLowerBound` certificate is below the exact infimum model,
    whenever the feasible ratio set is nonempty. -/
theorem SepLowerBound_le_sylvesterSepInf_of_nonempty (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma)
    (hne : (sylvesterSepRatios n A B).Nonempty) :
    sigma <= sylvesterSepInf n A B := by
  unfold sylvesterSepInf
  apply le_csInf hne
  intro rho hrho
  cases hrho with
  | intro X hrest =>
      cases hrest with
      | intro hX hrho_eq =>
          rw [hrho_eq]
          have hXsq_pos : 0 < frobNormSq X :=
            lt_of_le_of_ne (frobNormSq_nonneg X) (Ne.symm hX)
          have hXnorm_pos : 0 < frobNorm X := by
            have hs : 0 < frobNorm X ^ 2 := by
              rw [frobNorm_sq]
              exact hXsq_pos
            have hne_norm : Not (frobNorm X = 0) := sq_pos_iff.mp hs
            exact lt_of_le_of_ne (frobNorm_nonneg X) (Ne.symm hne_norm)
          have hsq := hSep.2 X hX
          have hsq_norms : (sigma * frobNorm X) ^ 2 <=
              frobNorm (sylvesterOp n A B X) ^ 2 := by
            rw [mul_pow, frobNorm_sq, frobNorm_sq]
            exact hsq
          have hleft_nonneg : 0 <= sigma * frobNorm X :=
            mul_nonneg (le_of_lt hSep.1) (frobNorm_nonneg X)
          have hright_nonneg : 0 <= frobNorm (sylvesterOp n A B X) :=
            frobNorm_nonneg _
          have hnorm_le :
              sigma * frobNorm X <= frobNorm (sylvesterOp n A B X) := by
            nlinarith [sq_nonneg
              (frobNorm (sylvesterOp n A B X) - sigma * frobNorm X)]
          have hXnorm_ne : Not (frobNorm X = 0) := ne_of_gt hXnorm_pos
          calc
            sigma = sigma * frobNorm X / frobNorm X := by
              field_simp [hXnorm_ne]
            _ <= frobNorm (sylvesterOp n A B X) / frobNorm X := by
              exact div_le_div_of_nonneg_right hnorm_le (le_of_lt hXnorm_pos)

/-- Any positive number below the exact infimum model of `sep(A,B)` is a valid
    `SepLowerBound` certificate for the existing perturbation infrastructure. -/
theorem SepLowerBound_of_pos_le_sylvesterSepInf (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    SepLowerBound n A B sigma := by
  refine And.intro hsigma ?_
  intro X hX
  have hXsq_pos : 0 < frobNormSq X :=
    lt_of_le_of_ne (frobNormSq_nonneg X) (Ne.symm hX)
  have hXnorm_pos : 0 < frobNorm X := by
    have hs : 0 < frobNorm X ^ 2 := by
      rw [frobNorm_sq]
      exact hXsq_pos
    have hne_norm : Not (frobNorm X = 0) := sq_pos_iff.mp hs
    exact lt_of_le_of_ne (frobNorm_nonneg X) (Ne.symm hne_norm)
  have hratio :
      sigma <= frobNorm (sylvesterOp n A B X) / frobNorm X :=
    le_trans hle (sylvesterSepInf_le_ratio n A B X hX)
  have hnorm_le :
      sigma * frobNorm X <= frobNorm (sylvesterOp n A B X) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hratio (le_of_lt hXnorm_pos)
    have hXnorm_ne : Not (frobNorm X = 0) := ne_of_gt hXnorm_pos
    have hcancel :
        frobNorm (sylvesterOp n A B X) / frobNorm X * frobNorm X =
          frobNorm (sylvesterOp n A B X) := by
      field_simp [hXnorm_ne]
    simpa [hcancel] using hmul
  have hleft_nonneg : 0 <= sigma * frobNorm X :=
    mul_nonneg (le_of_lt hsigma) (frobNorm_nonneg X)
  have hright_nonneg : 0 <= frobNorm (sylvesterOp n A B X) :=
    frobNorm_nonneg _
  have hsq_norms : (sigma * frobNorm X) ^ 2 <=
      frobNorm (sylvesterOp n A B X) ^ 2 := by
    nlinarith [sq_nonneg
      (frobNorm (sylvesterOp n A B X) - sigma * frobNorm X)]
  rw [mul_pow, frobNorm_sq, frobNorm_sq] at hsq_norms
  exact hsq_norms

/-- For a nonempty feasible ratio set, the existing positive lower-bound
    predicate is equivalent to being a positive lower bound of the exact
    infimum model.  This is an infimum bridge, not an attained-minimum claim. -/
theorem SepLowerBound_iff_pos_le_sylvesterSepInf_of_nonempty (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hne : (sylvesterSepRatios n A B).Nonempty) :
    SepLowerBound n A B sigma <->
      0 < sigma /\ sigma <= sylvesterSepInf n A B := by
  constructor
  · intro hSep
    exact And.intro hSep.1
      (SepLowerBound_le_sylvesterSepInf_of_nonempty n A B sigma hSep hne)
  · intro h
    exact SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma h.1 h.2

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
