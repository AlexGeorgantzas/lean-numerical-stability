-- Algorithms/StationaryIteration.lean
--
-- Higham Chapter 17: Error analysis of stationary iterative methods.
--
-- Covers §17.2 (forward error analysis) and §17.3 (backward/residual error
-- analysis) for iterations of the form  Mx_{k+1} = Nx_k + b  where A = M − N.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Analysis.HighamChapter7
import LeanFpAnalysis.FP.Algorithms.MatrixPowers

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §17.2  Splitting specification and iteration matrices
-- ============================================================

/-- A splitting A = M − N with M invertible. -/
structure SplittingSpec (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ) : Prop where
  splitting : ∀ i j, A i j = M i j - N i j
  inv_left : IsLeftInverse n M M_inv
  inv_right : IsRightInverse n M M_inv

/-- Iteration matrix G = M⁻¹N. -/
noncomputable def iterMatrix (n : ℕ) (M_inv N : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ := matMul n M_inv N

/-- Dual iteration matrix H = NM⁻¹. -/
noncomputable def dualIterMatrix (n : ℕ) (N M_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ := matMul n N M_inv

/-- Row/column diagonal scaling of a square matrix, `D_left A D_right`.
    This is the matrix part of Higham's scaled system
    `A x = b -> D1 A D2 (D2^{-1} x) = D1 b`. -/
noncomputable def stationaryRowColumnScale (n : ℕ)
    (dLeft dRight : Fin n → ℝ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  matMul n (diagMatrix dLeft) (matMul n A (diagMatrix dRight))

/-- Inverse candidate for a row/column-scaled splitting matrix:
    `(D1 M D2)^{-1} = D2^{-1} M^{-1} D1^{-1}`. -/
noncomputable def stationaryScaledInverse (n : ℕ)
    (dLeftInv dRightInv : Fin n → ℝ) (M_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  matMul n (diagMatrix dRightInv) (matMul n M_inv (diagMatrix dLeftInv))

/-- A diagonal matrix times its reciprocal diagonal is the identity. -/
theorem diagMatrix_mul_diagMatrix_eq_id (n : ℕ) (d e : Fin n → ℝ)
    (h : ∀ i, d i * e i = 1) :
    matMul n (diagMatrix d) (diagMatrix e) = idMatrix n := by
  ext i j
  rw [matMul_diagMatrix_left]
  by_cases hij : i = j
  · subst j
    simp [diagMatrix, idMatrix, h i]
  · simp [diagMatrix, idMatrix, hij]

/-- Entrywise form of the row/column diagonal scaling used for stationary
    iteration. -/
theorem stationaryRowColumnScale_apply (n : ℕ)
    (dLeft dRight : Fin n → ℝ) (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    stationaryRowColumnScale n dLeft dRight A i j =
      dLeft i * A i j * dRight j := by
  unfold stationaryRowColumnScale
  rw [matMul_diagMatrix_left]
  rw [matMul_diagMatrix_right]
  ring

/-- Higham, 2nd ed., Chapter 17, Section 17.2, p. 327, scale-independence
    passage: a diagonal row/column scaling preserves the splitting structure
    when `A`, `M`, and `N` are scaled in corresponding positions. -/
theorem stationaryRowColumnScale_splittingSpec (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ) (hS : SplittingSpec n A M N M_inv)
    (dLeft dLeftInv dRight dRightInv : Fin n → ℝ)
    (hdLeft : ∀ i, dLeftInv i * dLeft i = 1)
    (hdRight : ∀ i, dRightInv i * dRight i = 1) :
    SplittingSpec n
      (stationaryRowColumnScale n dLeft dRight A)
      (stationaryRowColumnScale n dLeft dRight M)
      (stationaryRowColumnScale n dLeft dRight N)
      (stationaryScaledInverse n dLeftInv dRightInv M_inv) where
  splitting := by
    intro i j
    repeat rw [stationaryRowColumnScale_apply]
    rw [hS.splitting i j]
    ring
  inv_left := by
    have hDLeft :
        matMul n (diagMatrix dLeftInv) (diagMatrix dLeft) = idMatrix n :=
      diagMatrix_mul_diagMatrix_eq_id n dLeftInv dLeft hdLeft
    have hDRight :
        matMul n (diagMatrix dRightInv) (diagMatrix dRight) = idMatrix n :=
      diagMatrix_mul_diagMatrix_eq_id n dRightInv dRight hdRight
    have hMLeft : matMul n M_inv M = idMatrix n := by
      ext i j
      exact hS.inv_left i j
    have hLeftMat :
        matMul n (stationaryScaledInverse n dLeftInv dRightInv M_inv)
          (stationaryRowColumnScale n dLeft dRight M) = idMatrix n := by
      unfold stationaryScaledInverse stationaryRowColumnScale
      calc
        matMul n (matMul n (diagMatrix dRightInv)
              (matMul n M_inv (diagMatrix dLeftInv)))
            (matMul n (diagMatrix dLeft) (matMul n M (diagMatrix dRight)))
            =
          matMul n (diagMatrix dRightInv)
            (matMul n M_inv
              (matMul n (diagMatrix dLeftInv)
                (matMul n (diagMatrix dLeft)
                  (matMul n M (diagMatrix dRight))))) := by
              rw [matMul_assoc]
              rw [matMul_assoc]
        _ =
          matMul n (diagMatrix dRightInv)
            (matMul n M_inv (matMul n M (diagMatrix dRight))) := by
              rw [← matMul_assoc n (diagMatrix dLeftInv) (diagMatrix dLeft)
                (matMul n M (diagMatrix dRight))]
              rw [hDLeft, matMul_id_left]
        _ =
          matMul n (diagMatrix dRightInv)
            (matMul n (matMul n M_inv M) (diagMatrix dRight)) := by
              rw [matMul_assoc]
        _ = matMul n (diagMatrix dRightInv) (diagMatrix dRight) := by
              rw [hMLeft, matMul_id_left]
        _ = idMatrix n := hDRight
    intro i j
    have hentry := congrArg (fun T : Fin n → Fin n → ℝ => T i j) hLeftMat
    simpa [matMul, idMatrix] using hentry
  inv_right := by
    have hDLeft :
        matMul n (diagMatrix dLeft) (diagMatrix dLeftInv) = idMatrix n :=
      diagMatrix_mul_diagMatrix_eq_id n dLeft dLeftInv
        (fun i => by rw [mul_comm]; exact hdLeft i)
    have hDRight :
        matMul n (diagMatrix dRight) (diagMatrix dRightInv) = idMatrix n :=
      diagMatrix_mul_diagMatrix_eq_id n dRight dRightInv
        (fun i => by rw [mul_comm]; exact hdRight i)
    have hMRight : matMul n M M_inv = idMatrix n := by
      ext i j
      exact hS.inv_right i j
    have hRightMat :
        matMul n (stationaryRowColumnScale n dLeft dRight M)
          (stationaryScaledInverse n dLeftInv dRightInv M_inv) = idMatrix n := by
      unfold stationaryScaledInverse stationaryRowColumnScale
      calc
        matMul n (matMul n (diagMatrix dLeft)
              (matMul n M (diagMatrix dRight)))
            (matMul n (diagMatrix dRightInv)
              (matMul n M_inv (diagMatrix dLeftInv)))
            =
          matMul n (diagMatrix dLeft)
            (matMul n M
              (matMul n (diagMatrix dRight)
                (matMul n (diagMatrix dRightInv)
                  (matMul n M_inv (diagMatrix dLeftInv))))) := by
              rw [matMul_assoc]
              rw [matMul_assoc]
        _ =
          matMul n (diagMatrix dLeft)
            (matMul n M (matMul n M_inv (diagMatrix dLeftInv))) := by
              rw [← matMul_assoc n (diagMatrix dRight) (diagMatrix dRightInv)
                (matMul n M_inv (diagMatrix dLeftInv))]
              rw [hDRight, matMul_id_left]
        _ =
          matMul n (diagMatrix dLeft)
            (matMul n (matMul n M M_inv) (diagMatrix dLeftInv)) := by
              rw [matMul_assoc]
        _ = matMul n (diagMatrix dLeft) (diagMatrix dLeftInv) := by
              rw [hMRight, matMul_id_left]
        _ = idMatrix n := hDLeft
    intro i j
    have hentry := congrArg (fun T : Fin n → Fin n → ℝ => T i j) hRightMat
    simpa [matMul, idMatrix] using hentry

/-- Higham, 2nd ed., Chapter 17, Section 17.2, p. 327, scale-independence
    passage: after row/column diagonal scaling, the new iteration matrix is
    similar to the old one by the column scaling matrix. This is the algebraic
    certificate behind the statement that the eigenvalues of `M^{-1}N` are
    unchanged. -/
theorem stationaryScaledIterMatrix_similarity (n : ℕ)
    (M_inv N : Fin n → Fin n → ℝ)
    (dLeft dLeftInv dRight dRightInv : Fin n → ℝ)
    (hdLeft : ∀ i, dLeftInv i * dLeft i = 1)
    (_hdRight : ∀ i, dRightInv i * dRight i = 1) :
    iterMatrix n
      (stationaryScaledInverse n dLeftInv dRightInv M_inv)
      (stationaryRowColumnScale n dLeft dRight N) =
      matMul n (diagMatrix dRightInv)
        (matMul n (iterMatrix n M_inv N) (diagMatrix dRight)) := by
  have hDLeft :
      matMul n (diagMatrix dLeftInv) (diagMatrix dLeft) = idMatrix n :=
    diagMatrix_mul_diagMatrix_eq_id n dLeftInv dLeft hdLeft
  unfold iterMatrix stationaryScaledInverse stationaryRowColumnScale
  calc
    matMul n (matMul n (diagMatrix dRightInv)
          (matMul n M_inv (diagMatrix dLeftInv)))
        (matMul n (diagMatrix dLeft) (matMul n N (diagMatrix dRight)))
        =
      matMul n (diagMatrix dRightInv)
        (matMul n M_inv
          (matMul n (diagMatrix dLeftInv)
            (matMul n (diagMatrix dLeft) (matMul n N (diagMatrix dRight))))) := by
          rw [matMul_assoc]
          rw [matMul_assoc]
    _ =
      matMul n (diagMatrix dRightInv)
        (matMul n M_inv (matMul n N (diagMatrix dRight))) := by
          rw [← matMul_assoc n (diagMatrix dLeftInv) (diagMatrix dLeft)
            (matMul n N (diagMatrix dRight))]
          rw [hDLeft, matMul_id_left]
    _ =
      matMul n (diagMatrix dRightInv)
        (matMul n (matMul n M_inv N) (diagMatrix dRight)) := by
          rw [matMul_assoc]

/-- Higham, 2nd ed., Chapter 17, Section 17.2, p. 327, scale-independence
    passage: the scaled iteration matrix has the same characteristic polynomial
    as the original `M^{-1}N`, so the eigenvalue data encoded by the
    characteristic polynomial is unchanged. -/
theorem stationaryScaledIterMatrix_charpoly_eq (n : ℕ)
    (M_inv N : Fin n → Fin n → ℝ)
    (dLeft dLeftInv dRight dRightInv : Fin n → ℝ)
    (hdLeft : ∀ i, dLeftInv i * dLeft i = 1)
    (hdRight : ∀ i, dRightInv i * dRight i = 1) :
    Matrix.charpoly
      (iterMatrix n
        (stationaryScaledInverse n dLeftInv dRightInv M_inv)
        (stationaryRowColumnScale n dLeft dRight N) :
        Matrix (Fin n) (Fin n) ℝ) =
      Matrix.charpoly (iterMatrix n M_inv N : Matrix (Fin n) (Fin n) ℝ) := by
  let G : Fin n → Fin n → ℝ := iterMatrix n M_inv N
  let D : Fin n → Fin n → ℝ := diagMatrix dRight
  let Dinv : Fin n → Fin n → ℝ := diagMatrix dRightInv
  have hDRight : matMul n D Dinv = idMatrix n :=
    diagMatrix_mul_diagMatrix_eq_id n dRight dRightInv
      (fun i => by rw [mul_comm]; exact hdRight i)
  have hsim :
      iterMatrix n
        (stationaryScaledInverse n dLeftInv dRightInv M_inv)
        (stationaryRowColumnScale n dLeft dRight N) =
        matMul n Dinv (matMul n G D) := by
    simpa [G, D, Dinv] using
      stationaryScaledIterMatrix_similarity n M_inv N dLeft dLeftInv dRight
        dRightInv hdLeft hdRight
  have hcomm :
      Matrix.charpoly (matMul n Dinv (matMul n G D) : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.charpoly (matMul n (matMul n G D) Dinv :
          Matrix (Fin n) (Fin n) ℝ) := by
    simpa [matMul, Matrix.mul_apply] using
      (Matrix.charpoly_mul_comm
        (A := (Dinv : Matrix (Fin n) (Fin n) ℝ))
        (B := (matMul n G D : Matrix (Fin n) (Fin n) ℝ)))
  have hcollapse : matMul n (matMul n G D) Dinv = G := by
    rw [matMul_assoc, hDRight, matMul_id_right]
  calc
    Matrix.charpoly
      (iterMatrix n
        (stationaryScaledInverse n dLeftInv dRightInv M_inv)
        (stationaryRowColumnScale n dLeft dRight N) :
        Matrix (Fin n) (Fin n) ℝ)
        = Matrix.charpoly (matMul n Dinv (matMul n G D) :
            Matrix (Fin n) (Fin n) ℝ) := by rw [hsim]
    _ = Matrix.charpoly (matMul n (matMul n G D) Dinv :
            Matrix (Fin n) (Fin n) ℝ) := hcomm
    _ = Matrix.charpoly (iterMatrix n M_inv N : Matrix (Fin n) (Fin n) ℝ) := by
          rw [hcollapse]

-- ============================================================
-- AG = HA identity
-- ============================================================

/-- **AG = HA**: Since A = M − N, both sides equal N − NM⁻¹N. -/
theorem AG_eq_HA (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv) :
    matMul n A (iterMatrix n M_inv N) =
    matMul n (dualIterMatrix n N M_inv) A := by
  ext i j
  show ∑ k : Fin n, A i k * (∑ l : Fin n, M_inv k l * N l j) =
       ∑ k : Fin n, (∑ l : Fin n, N i l * M_inv l k) * A k j
  -- Expand A = M - N on both sides
  simp_rw [hS.splitting]
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  -- Show first terms both = N_{ij}
  have h1 : ∑ k : Fin n, M i k * ∑ l : Fin n, M_inv k l * N l j = N i j := by
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    simp_rw [show ∀ x x_1 : Fin n, M i x_1 * (M_inv x_1 x * N x j) =
        M i x_1 * M_inv x_1 x * N x j from fun _ _ => by ring]
    simp_rw [← Finset.sum_mul]
    conv_lhs => arg 2; ext l; rw [hS.inv_right i l]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  have h2 : ∑ k : Fin n, (∑ l : Fin n, N i l * M_inv l k) * M k j = N i j := by
    simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    simp_rw [show ∀ x x_1 : Fin n, N i x * M_inv x x_1 * M x_1 j =
        N i x * (M_inv x x_1 * M x_1 j) from fun _ _ => by ring]
    simp_rw [← Finset.mul_sum]
    conv_lhs => arg 2; ext l; rw [hS.inv_left l j]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  -- Show second terms match: ∑ N*(M⁻¹N) = ∑ (NM⁻¹)*N
  have h3 : ∑ k : Fin n, N i k * ∑ l : Fin n, M_inv k l * N l j =
      ∑ k : Fin n, (∑ l : Fin n, N i l * M_inv l k) * N k j := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    simp_rw [show ∀ k l : Fin n, N i k * (M_inv k l * N l j) =
        N i k * M_inv k l * N l j from fun _ _ => by ring]
    rw [Finset.sum_comm]
  linarith

/-- **AG^k = H^kA** for all k, by induction. -/
theorem A_matPow_G_eq_matPow_H_A (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv) (k : ℕ) :
    matMul n A (matPow n (iterMatrix n M_inv N) k) =
    matMul n (matPow n (dualIterMatrix n N M_inv) k) A := by
  induction k with
  | zero =>
    simp only [matPow]; rw [matMul_id_right, matMul_id_left]
  | succ k ih =>
    show matMul n A (matMul n (iterMatrix n M_inv N)
      (matPow n (iterMatrix n M_inv N) k)) =
      matMul n (matMul n (dualIterMatrix n N M_inv)
      (matPow n (dualIterMatrix n N M_inv) k)) A
    rw [← matMul_assoc n A, AG_eq_HA n A M N M_inv hS,
        matMul_assoc n _ A, ih, ← matMul_assoc]

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.4):
    an exact solution of `Ax = b` is a fixed point of the stationary
    affine map `x ↦ Gx + M⁻¹b`, where `G = M⁻¹N`. -/
theorem stationary_solution_fixed_point (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i) :
    ∀ i, x i =
      matMulVec n (iterMatrix n M_inv N) x i + matMulVec n M_inv b i := by
  have hMx : ∀ l, matMulVec n M x l = matMulVec n N x l + b l := by
    intro l
    unfold matMulVec
    have : ∑ j : Fin n, M l j * x j - ∑ j : Fin n, N l j * x j = b l := by
      rw [← Finset.sum_sub_distrib]
      convert hAx l using 1
      congr 1
      ext j
      rw [hS.splitting l j]
      ring
    linarith
  have hApplyLeft : matMulVec n M_inv (matMulVec n M x) = x := by
    ext i
    calc
      matMulVec n M_inv (matMulVec n M x) i
          = matMulVec n (matMul n M_inv M) x i := by
              rw [matMulVec_matMul]
      _ = matMulVec n (idMatrix n) x i := by
          unfold matMulVec matMul idMatrix
          apply Finset.sum_congr rfl
          intro j _hj
          exact congrArg (fun t : ℝ => t * x j) (hS.inv_left i j)
      _ = x i := by
          simp [matMulVec, idMatrix]
  intro i
  calc
    x i = matMulVec n M_inv (matMulVec n M x) i := by
      exact (congrFun hApplyLeft i).symm
    _ = matMulVec n M_inv (fun l => matMulVec n N x l + b l) i := by
      congr 1
      ext l
      exact hMx l
    _ = matMulVec n M_inv (matMulVec n N x) i +
        matMulVec n M_inv b i := by
      simpa using congrFun (matMulVec_add_right n M_inv (matMulVec n N x) b) i
    _ = matMulVec n (iterMatrix n M_inv N) x i + matMulVec n M_inv b i := by
      simp [iterMatrix, matMulVec_matMul]

/-- Finite unrolling of an affine fixed point `x = Gx + c`. -/
theorem affine_fixed_point_unroll (n : ℕ)
    (G : Fin n → Fin n → ℝ) (c x : Fin n → ℝ)
    (hfix : ∀ i, x i = matMulVec n G x i + c i) :
    ∀ m i, x i =
      matMulVec n (matPow n G m) x i +
      ∑ k ∈ Finset.range m, matMulVec n (matPow n G k) c i := by
  intro m
  induction m with
  | zero =>
      intro i
      simp [matPow, matMulVec, idMatrix]
  | succ m ih =>
      intro i
      have htail :
          matMulVec n (matPow n G m) x i =
            matMulVec n (matPow n G (m + 1)) x i +
              matMulVec n (matPow n G m) c i := by
        have hx :
            x = fun j => matMulVec n G x j + c j := by
          ext j
          exact hfix j
        calc
          matMulVec n (matPow n G m) x i
              = matMulVec n (matPow n G m)
                  (fun j => matMulVec n G x j + c j) i := by
                  exact congrArg (fun y => matMulVec n (matPow n G m) y i) hx
          _ = matMulVec n (matPow n G m) (matMulVec n G x) i +
                matMulVec n (matPow n G m) c i := by
                  simpa using
                    congrFun
                      (matMulVec_add_right n (matPow n G m)
                        (matMulVec n G x) c) i
          _ = matMulVec n (matPow n G (m + 1)) x i +
                matMulVec n (matPow n G m) c i := by
                  congr 1
                  rw [← matMulVec_matMul n (matPow n G m) G x i]
                  rw [← matPow_succ_right n G m]
      calc
        x i = matMulVec n (matPow n G m) x i +
            ∑ k ∈ Finset.range m, matMulVec n (matPow n G k) c i := ih i
        _ = (matMulVec n (matPow n G (m + 1)) x i +
              matMulVec n (matPow n G m) c i) +
            ∑ k ∈ Finset.range m, matMulVec n (matPow n G k) c i := by
              rw [htail]
        _ = matMulVec n (matPow n G (m + 1)) x i +
            ∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n G k) c i := by
              rw [Finset.sum_range_succ]
              ring

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.4):
    finite-sum identity for an exact stationary solution, obtained by
    unrolling the affine fixed-point equation. -/
theorem stationary_solution_finite_sum (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (m : ℕ) :
    ∀ i, x i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1)) x i +
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n (iterMatrix n M_inv N) k)
          (matMulVec n M_inv b) i := by
  intro i
  exact affine_fixed_point_unroll n (iterMatrix n M_inv N)
    (matMulVec n M_inv b) x
    (stationary_solution_fixed_point n A M N M_inv hS b x hAx)
    (m + 1) i

/-- Matrix-vector multiplication distributes over a finite sum in the vector
    argument. -/
theorem matMulVec_finset_sum_right {α : Type*} [DecidableEq α] (n : ℕ)
    (A : Fin n → Fin n → ℝ) (s : Finset α) (v : α → Fin n → ℝ) :
    matMulVec n A (fun i => ∑ a ∈ s, v a i) =
      fun i => ∑ a ∈ s, matMulVec n A (v a) i := by
  classical
  induction s using Finset.induction with
  | empty =>
      ext i
      simp [matMulVec]
  | insert a s ha ih =>
      ext i
      simp [ha, matMulVec_add_right, ih]

/-- Finite unrolling of an affine recurrence with a time-varying source term. -/
theorem affine_recurrence_unroll (n : ℕ)
    (G : Fin n → Fin n → ℝ) (d : ℕ → Fin n → ℝ)
    (y : ℕ → Fin n → ℝ)
    (hstep : ∀ k i, y (k + 1) i = matMulVec n G (y k) i + d k i) :
    ∀ m i, y (m + 1) i =
      matMulVec n (matPow n G (m + 1)) (y 0) i +
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n G k) (d (m - k)) i := by
  intro m
  induction m with
  | zero =>
      intro i
      rw [Finset.sum_range_one, matPow_one]
      simpa [matPow_zero, matMulVec, idMatrix] using hstep 0 i
  | succ m ih =>
      intro i
      have hy :
          y (m + 1) =
            fun j => matMulVec n (matPow n G (m + 1)) (y 0) j +
              ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G k) (d (m - k)) j := by
        ext j
        exact ih j
      have hlead :
          matMulVec n G
              (matMulVec n (matPow n G (m + 1)) (y 0)) i =
            matMulVec n (matPow n G ((m + 1) + 1)) (y 0) i := by
        rw [← matMulVec_matMul n G (matPow n G (m + 1)) (y 0) i]
        rw [← matPow_succ n G (m + 1)]
      have hsum :
          matMulVec n G
              (fun j => ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G k) (d (m - k)) j) i =
            ∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n G (k + 1)) (d (m - k)) i := by
        calc
          matMulVec n G
              (fun j => ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G k) (d (m - k)) j) i
              = ∑ k ∈ Finset.range (m + 1),
                  matMulVec n G
                    (matMulVec n (matPow n G k) (d (m - k))) i := by
                  simpa using
                    congrFun
                      (matMulVec_finset_sum_right n G (Finset.range (m + 1))
                        (fun k => matMulVec n (matPow n G k) (d (m - k)))) i
          _ = ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G (k + 1)) (d (m - k)) i := by
              apply Finset.sum_congr rfl
              intro k _hk
              rw [← matMulVec_matMul n G (matPow n G k) (d (m - k)) i]
              rw [← matPow_succ n G k]
      have hfull :
          (∑ k ∈ Finset.range ((m + 1) + 1),
            matMulVec n (matPow n G k) (d ((m + 1) - k)) i) =
            d (m + 1) i +
            ∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n G (k + 1)) (d (m - k)) i := by
        have hzero :
            matMulVec n (matPow n G 0) (d ((m + 1) - 0)) i =
              d (m + 1) i := by
          simp [matPow_zero, matMulVec, idMatrix]
        have htail :
            (∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n G (k + 1))
                (d ((m + 1) - (k + 1))) i) =
              ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G (k + 1)) (d (m - k)) i := by
          apply Finset.sum_congr rfl
          intro k _hk
          simp [Nat.succ_sub_succ_eq_sub]
        rw [Finset.sum_range_succ']
        rw [hzero, htail]
        ring
      calc
        y ((m + 1) + 1) i =
            matMulVec n G (y (m + 1)) i + d (m + 1) i := hstep (m + 1) i
        _ = matMulVec n G
              (fun j => matMulVec n (matPow n G (m + 1)) (y 0) j +
                ∑ k ∈ Finset.range (m + 1),
                  matMulVec n (matPow n G k) (d (m - k)) j) i +
            d (m + 1) i := by
              rw [hy]
        _ = (matMulVec n G
                (matMulVec n (matPow n G (m + 1)) (y 0)) i +
              matMulVec n G
                (fun j => ∑ k ∈ Finset.range (m + 1),
                  matMulVec n (matPow n G k) (d (m - k)) j) i) +
            d (m + 1) i := by
              rw [congrFun
                (matMulVec_add_right n G
                  (matMulVec n (matPow n G (m + 1)) (y 0))
                  (fun j => ∑ k ∈ Finset.range (m + 1),
                    matMulVec n (matPow n G k) (d (m - k)) j)) i]
        _ = (matMulVec n (matPow n G ((m + 1) + 1)) (y 0) i +
              ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G (k + 1)) (d (m - k)) i) +
            d (m + 1) i := by
              rw [hlead, hsum]
        _ = matMulVec n (matPow n G ((m + 1) + 1)) (y 0) i +
            ∑ k ∈ Finset.range ((m + 1) + 1),
              matMulVec n (matPow n G k) (d ((m + 1) - k)) i := by
              rw [hfull]
              ring

-- ============================================================
-- §17.2  Computed iteration and one-step error
-- ============================================================

/-- Computed stationary iteration with local errors, using the repository's
    legacy sign convention `M xhat_{k+1} = N xhat_k + b + xi_k`. -/
structure ComputedIteration (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ)) : Prop where
  step : ∀ k i, ∑ j : Fin n, M i j * x_hat (k + 1) j =
         ∑ j : Fin n, N i j * x_hat k j + b i + ξ k i

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.1):
    source-sign form of the computed stationary iteration,
    `M xhat_{k+1} = N xhat_k + b - xi_k`. -/
structure SourceComputedIteration (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ)) : Prop where
  step : ∀ k i, ∑ j : Fin n, M i j * x_hat (k + 1) j =
         ∑ j : Fin n, N i j * x_hat k j + b i - ξ k i

/-- The source-sign convention in Higham's equation (17.1) is the legacy
    `ComputedIteration` convention with the local error term negated. -/
theorem computedIteration_of_sourceComputedIteration (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ) :
    ComputedIteration n M N b x_hat (fun k i => -ξ k i) := by
  constructor
  intro k i
  simpa [sub_eq_add_neg] using hIter.step k i

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.1):
    applying `M⁻¹` to the source-sign computed iteration gives the affine
    step `xhat_{k+1} = G xhat_k + M⁻¹(b - xi_k)`. -/
theorem sourceComputedIteration_step_affine (n : ℕ)
    (M N M_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x_hat ξ : ℕ → Fin n → ℝ)
    (hLeft : IsLeftInverse n M M_inv)
    (hIter : SourceComputedIteration n M N b x_hat ξ) :
    ∀ k i, x_hat (k + 1) i =
      matMulVec n (iterMatrix n M_inv N) (x_hat k) i +
      matMulVec n M_inv (fun j => b j - ξ k j) i := by
  intro k i
  have hApplyLeft :
      matMulVec n M_inv (matMulVec n M (x_hat (k + 1))) =
        x_hat (k + 1) := by
    ext r
    calc
      matMulVec n M_inv (matMulVec n M (x_hat (k + 1))) r
          = matMulVec n (matMul n M_inv M) (x_hat (k + 1)) r := by
              rw [matMulVec_matMul]
      _ = matMulVec n (idMatrix n) (x_hat (k + 1)) r := by
          unfold matMulVec matMul idMatrix
          apply Finset.sum_congr rfl
          intro j _hj
          exact congrArg (fun t : ℝ => t * x_hat (k + 1) j) (hLeft r j)
      _ = x_hat (k + 1) r := by
          simp [matMulVec, idMatrix]
  calc
    x_hat (k + 1) i =
        matMulVec n M_inv (matMulVec n M (x_hat (k + 1))) i := by
          exact (congrFun hApplyLeft i).symm
    _ = matMulVec n M_inv
          (fun l => matMulVec n N (x_hat k) l + (b l - ξ k l)) i := by
          congr 1
          ext l
          have h := hIter.step k l
          dsimp [matMulVec] at h ⊢
          linarith
    _ = matMulVec n M_inv (matMulVec n N (x_hat k)) i +
        matMulVec n M_inv (fun l => b l - ξ k l) i := by
          simpa using
            congrFun
              (matMulVec_add_right n M_inv (matMulVec n N (x_hat k))
                (fun l => b l - ξ k l)) i
    _ = matMulVec n (iterMatrix n M_inv N) (x_hat k) i +
        matMulVec n M_inv (fun l => b l - ξ k l) i := by
          simp [iterMatrix, matMulVec_matMul]

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.3):
    finite-sum closed form for the source-sign computed stationary iteration. -/
theorem sourceComputedIteration_finite_sum (n : ℕ)
    (M N M_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x_hat ξ : ℕ → Fin n → ℝ)
    (hLeft : IsLeftInverse n M M_inv)
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (m : ℕ) :
    ∀ i, x_hat (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1)) (x_hat 0) i +
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n (iterMatrix n M_inv N) k)
          (matMulVec n M_inv (fun j => b j - ξ (m - k) j)) i := by
  intro i
  exact affine_recurrence_unroll n (iterMatrix n M_inv N)
    (fun k => matMulVec n M_inv (fun j => b j - ξ k j))
    x_hat
    (sourceComputedIteration_step_affine n M N M_inv b x_hat ξ hLeft hIter)
    m i

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.21):
    exact stationary iterates for a consistent singular system satisfy the
    same finite affine unrolling
    `x_{m+1} = G^{m+1} x_0 + sum_{k=0}^m G^k M⁻¹ b`.

    The proof uses only the nonsingularity of `M`, not nonsingularity of `A`,
    which is precisely why the identity remains valid at the start of the
    singular-system analysis. -/
theorem singular_stationary_iterate_finite_sum (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b : Fin n → ℝ) (x_seq : ℕ → Fin n → ℝ)
    (hIter : SourceComputedIteration n M N b x_seq (fun _ _ => 0))
    (m : ℕ) :
    ∀ i, x_seq (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1)) (x_seq 0) i +
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n (iterMatrix n M_inv N) k)
          (matMulVec n M_inv b) i := by
  intro i
  have h := sourceComputedIteration_finite_sum n M N M_inv b x_seq
    (fun _ _ => 0) hS.inv_left hIter m i
  simpa using h

/-- Applying a Neumann partial sum to a vector is the same as summing the
    displayed matrix-power actions. -/
theorem matMulVec_neumannSum_range (n : ℕ)
    (G : Fin n → Fin n → ℝ) (m : ℕ) (v : Fin n → ℝ) :
    ∀ i, matMulVec n (neumannSum n G m) v i =
      ∑ k ∈ Finset.range (m + 1), matMulVec n (matPow n G k) v i := by
  induction m with
  | zero =>
      intro i
      rw [Finset.sum_range_one]
      simp [neumannSum_zero, matPow_zero, matMulVec_id]
  | succ m ih =>
      intro i
      rw [neumannSum_succ]
      rw [congrFun (matMulVec_add_left n (neumannSum n G m)
        (matPow n G (m + 1)) v) i]
      rw [ih i]
      exact (Finset.sum_range_succ
        (fun k => matMulVec n (matPow n G k) v i) (m + 1)).symm

/-- Higham, 2nd ed., Chapter 17, Section 17.4, printed page 333:
    for a consistent system `Ax = b`, the source term in the singular-system
    exact iteration satisfies `M⁻¹ b = (I - G)x`. -/
theorem singular_consistent_source_term_eq_I_sub_G (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i) :
    matMulVec n M_inv b =
      matMulVec n (matSub_id n (iterMatrix n M_inv N)) x := by
  ext i
  have hfix := stationary_solution_fixed_point n A M N M_inv hS b x hAx i
  have hsub :
      matMulVec n (matSub_id n (iterMatrix n M_inv N)) x i =
        x i - matMulVec n (iterMatrix n M_inv N) x i := by
    unfold matMulVec matSub_id
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    have hid : ∑ j : Fin n, idMatrix n i j * x j = x i := by
      have h := congrFun (matMulVec_id n x) i
      simpa [matMulVec] using h
    rw [hid]
  rw [hsub]
  linarith

/-- Higham, 2nd ed., Chapter 17, Section 17.4, printed page 333:
    the consistent-system source term in (17.21) telescopes as
    `sum_{k=0}^m G^k M⁻¹ b = (I - G^(m+1))x`. -/
theorem singular_consistent_second_term_telescope (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (m : ℕ) :
    ∀ i, (∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n (iterMatrix n M_inv N) k)
          (matMulVec n M_inv b) i) =
      x i - matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1)) x i := by
  intro i
  let G := iterMatrix n M_inv N
  have hsource :
      matMulVec n M_inv b = matMulVec n (matSub_id n G) x := by
    simpa [G] using singular_consistent_source_term_eq_I_sub_G n A M N M_inv hS b x hAx
  have hsum := matMulVec_neumannSum_range n G m (matMulVec n M_inv b) i
  have htel :
      matMulVec n (neumannSum n G m) (matMulVec n (matSub_id n G) x) i =
        x i - matMulVec n (matPow n G (m + 1)) x i := by
    calc
      matMulVec n (neumannSum n G m) (matMulVec n (matSub_id n G) x) i
          = matMulVec n (matMul n (neumannSum n G m) (matSub_id n G)) x i := by
              rw [matMulVec_matMul]
      _ = matMulVec n (fun a b => idMatrix n a b - matPow n G (m + 1) a b) x i := by
              rw [neumann_telescope_right n G m]
      _ = x i - matMulVec n (matPow n G (m + 1)) x i := by
              unfold matMulVec
              simp_rw [sub_mul, Finset.sum_sub_distrib]
              have hid : ∑ j : Fin n, idMatrix n i j * x j = x i := by
                have h := congrFun (matMulVec_id n x) i
                simpa [matMulVec] using h
              rw [hid]
  calc
    (∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n (iterMatrix n M_inv N) k)
          (matMulVec n M_inv b) i)
        = matMulVec n (neumannSum n G m) (matMulVec n M_inv b) i := by
            simpa [G] using hsum.symm
    _ = matMulVec n (neumannSum n G m) (matMulVec n (matSub_id n G) x) i := by
            rw [hsource]
    _ = x i - matMulVec n (matPow n G (m + 1)) x i := htel
    _ = x i - matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1)) x i := by
            rfl

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equations (17.21)-(17.26):
    before taking the semiconvergent/Drazin limit, a consistent exact singular
    iteration splits into a propagated initial term plus the telescoped
    consistent solution contribution. -/
theorem singular_stationary_iterate_consistent_split (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_seq : ℕ → Fin n → ℝ)
    (hIter : SourceComputedIteration n M N b x_seq (fun _ _ => 0))
    (m : ℕ) :
    ∀ i, x_seq (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1)) (x_seq 0) i +
        (x i - matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1)) x i) := by
  intro i
  have hiter := singular_stationary_iterate_finite_sum n A M N M_inv hS b x_seq hIter m i
  have htel := singular_consistent_second_term_telescope n A M N M_inv hS b x hAx m i
  rw [hiter, htel]

/-- One-step error: x_i − x̂_{k+1,i} = ∑_j G_{ij}(x_j − x̂_{k,j}) − ∑_j M⁻¹_{ij} ξ_{k,j}. -/
theorem one_step_error (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) :
    ∀ k i, x i - x_hat (k + 1) i =
      ∑ j : Fin n, (iterMatrix n M_inv N) i j * (x j - x_hat k j) -
      ∑ j : Fin n, M_inv i j * ξ k j := by
  intro k i
  have hstep := hIter.step k
  -- Mx = Nx + b
  have hMx : ∀ l, ∑ j : Fin n, M l j * x j =
      ∑ j : Fin n, N l j * x j + b l := by
    intro l
    have : ∑ j : Fin n, M l j * x j - ∑ j : Fin n, N l j * x j = b l := by
      rw [← Finset.sum_sub_distrib]
      convert hAx l using 1; congr 1; ext j; rw [hS.splitting l j]; ring
    linarith
  -- M(x - x̂_{k+1})_l = N(x - x̂_k)_l - ξ_{k,l}
  have hMdiff : ∀ l, ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j) =
      ∑ j : Fin n, N l j * (x j - x_hat k j) - ξ k l := by
    intro l
    have h1 : ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j) =
        ∑ j, M l j * x j - ∑ j, M l j * x_hat (k + 1) j := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
    have h2 : ∑ j : Fin n, N l j * (x j - x_hat k j) =
        ∑ j, N l j * x j - ∑ j, N l j * x_hat k j := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
    rw [h1, h2]; linarith [hstep l, hMx l]
  -- Apply M⁻¹
  have h_start : x i - x_hat (k + 1) i =
      ∑ l : Fin n, M_inv i l * ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j) := by
    symm
    calc ∑ l : Fin n, M_inv i l * ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j)
        = ∑ j : Fin n, (∑ l : Fin n, M_inv i l * M l j) *
            (x j - x_hat (k + 1) j) := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          congr 1; ext j; congr 1; ext l; ring
      _ = ∑ j : Fin n, (if i = j then 1 else 0) * (x j - x_hat (k + 1) j) := by
          congr 1; ext j; congr 1; exact hS.inv_left i j
      _ = x i - x_hat (k + 1) i := by
          simp [Finset.sum_ite_eq, Finset.mem_univ]
  rw [h_start]
  -- Replace M·diff with N·diff - ξ
  conv_lhs => arg 2; ext l; rw [hMdiff l]
  -- LHS: ∑_l M⁻¹_{il} * (∑_j N_{lj} (x_j - x̂_{k,j}) - ξ_{k,l})
  -- RHS: ∑_j G_{ij}(x_j-x̂_{k,j}) - ∑_j M⁻¹_{ij}ξ_{k,j}
  -- Both sides equal ∑_l ∑_j M⁻¹_{il}N_{lj}d_j - ∑_l M⁻¹_{il}ξ_l
  -- Transform LHS
  simp_rw [show ∀ l : Fin n, M_inv i l *
      (∑ j : Fin n, N l j * (x j - x_hat k j) - ξ k l) =
      ∑ j : Fin n, M_inv i l * (N l j * (x j - x_hat k j)) -
      M_inv i l * ξ k l from fun l => by rw [mul_sub, Finset.mul_sum]]
  rw [Finset.sum_sub_distrib]
  congr 1
  -- ∑_l ∑_j M⁻¹_{il}*(N_{lj}*d_j) = ∑_j G_{ij}*d_j
  rw [Finset.sum_comm]
  congr 1; ext j
  simp_rw [show ∀ l : Fin n, M_inv i l * (N l j * (x j - x_hat k j)) =
      M_inv i l * N l j * (x j - x_hat k j) from fun l => by ring]
  rw [← Finset.sum_mul]; rfl

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.1):
    one-step error recurrence for the source-sign local error convention. -/
theorem one_step_error_source (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ) :
    ∀ k i, x i - x_hat (k + 1) i =
      ∑ j : Fin n, (iterMatrix n M_inv N) i j * (x j - x_hat k j) +
      ∑ j : Fin n, M_inv i j * ξ k j := by
  intro k i
  have hOld := one_step_error n A M N M_inv hS b x hAx x_hat
    (fun k i => -ξ k i)
    (computedIteration_of_sourceComputedIteration n M N b x_hat ξ hIter) k i
  calc
    x i - x_hat (k + 1) i =
        ∑ j : Fin n, (iterMatrix n M_inv N) i j * (x j - x_hat k j) -
        ∑ j : Fin n, M_inv i j * (-ξ k j) := hOld
    _ = ∑ j : Fin n, (iterMatrix n M_inv N) i j * (x j - x_hat k j) +
        ∑ j : Fin n, M_inv i j * ξ k j := by
        rw [sub_eq_add_neg]
        congr 1
        simp_rw [mul_neg]
        rw [Finset.sum_neg_distrib, neg_neg]

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.5):
    finite-sum forward-error recurrence for the source-sign computed
    stationary iteration. -/
theorem sourceComputedIteration_error_finite_sum (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (m : ℕ) :
    ∀ i, x i - x_hat (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i +
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n (iterMatrix n M_inv N) k)
          (matMulVec n M_inv (ξ (m - k))) i := by
  intro i
  exact affine_recurrence_unroll n (iterMatrix n M_inv N)
    (fun k => matMulVec n M_inv (ξ k))
    (fun k j => x j - x_hat k j)
    (by
      intro k j
      simpa [matMulVec] using
        one_step_error_source n A M N M_inv hS b x hAx x_hat ξ hIter k j)
    m i

/-- A vector splits into its `E` component plus its `(I - E)` component. -/
theorem matMulVec_add_complement_apply (n : ℕ)
    (E : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    ∀ i, matMulVec n E v i + matMulVec n (matSub_id n E) v i = v i := by
  intro i
  unfold matMulVec matSub_id
  calc
    (∑ j : Fin n, E i j * v j) +
        ∑ j : Fin n, (idMatrix n i j - E i j) * v j =
      ∑ j : Fin n, idMatrix n i j * v j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
    _ = v i := by
        have h := congrFun (matMulVec_id n v) i
        simpa [matMulVec] using h

/-- If a vector is fixed by `G`, it is fixed by every finite power of `G`. -/
theorem matPow_fixed_of_matMulVec_fixed (n : ℕ)
    (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hfixed : ∀ i, matMulVec n G v i = v i) :
    ∀ k i, matMulVec n (matPow n G k) v i = v i := by
  intro k
  induction k with
  | zero =>
      intro i
      simpa [matPow_zero] using congrFun (matMulVec_id n v) i
  | succ k ih =>
      intro i
      calc
        matMulVec n (matPow n G (k + 1)) v i =
            matMulVec n G (matMulVec n (matPow n G k) v) i := by
              rw [matPow_succ, matMulVec_matMul]
        _ = matMulVec n G v i := by
              congr 1
              ext j
              exact ih j
        _ = v i := hfixed i

/-- Matrix-level version of `matPow_fixed_of_matMulVec_fixed`: if multiplying a
    matrix `C` on the left by `G` leaves it fixed, then every finite power of
    `G` leaves `C` fixed. -/
theorem matPow_mul_fixed_of_matMul_fixed (n : ℕ)
    (G C : Fin n → Fin n → ℝ) (hfixed : matMul n G C = C) :
    ∀ k, matMul n (matPow n G k) C = C := by
  intro k
  induction k with
  | zero =>
      simpa [matPow_zero] using matMul_id_left n C
  | succ k ih =>
      calc
        matMul n (matPow n G (k + 1)) C =
            matMul n (matMul n G (matPow n G k)) C := by
              rw [matPow_succ]
        _ = matMul n G (matMul n (matPow n G k) C) := by
              rw [matMul_assoc]
        _ = matMul n G C := by
              rw [ih]
        _ = C := hfixed

/-- If a matrix `E` commutes with `G`, then it commutes with every finite
    power of `G`. -/
theorem matPow_comm_of_matMul_comm (n : ℕ)
    (G E : Fin n → Fin n → ℝ)
    (hcomm : matMul n G E = matMul n E G) :
    ∀ k, matMul n (matPow n G k) E = matMul n E (matPow n G k) := by
  intro k
  induction k with
  | zero =>
      calc
        matMul n (matPow n G 0) E = E := by
          rw [matPow_zero, matMul_id_left]
        _ = matMul n E (matPow n G 0) := by
          rw [matPow_zero, matMul_id_right]
  | succ k ih =>
      calc
        matMul n (matPow n G (k + 1)) E =
            matMul n (matMul n G (matPow n G k)) E := by
              rw [matPow_succ]
        _ = matMul n G (matMul n (matPow n G k) E) := by
              rw [matMul_assoc]
        _ = matMul n G (matMul n E (matPow n G k)) := by
              rw [ih]
        _ = matMul n (matMul n G E) (matPow n G k) := by
              rw [← matMul_assoc]
        _ = matMul n (matMul n E G) (matPow n G k) := by
              rw [hcomm]
        _ = matMul n E (matMul n G (matPow n G k)) := by
              rw [matMul_assoc]
        _ = matMul n E (matPow n G (k + 1)) := by
              rw [matPow_succ]

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equations (17.22)-(17.25):
    index-one Drazin inverse certificate for the matrix `A = I - G`.

    The fields record the standard algebraic identities used by the source's
    semiconvergent singular-system projector route: commutation, the reflexive
    inverse law `DAD = D`, and the index-one identity `A^2D = A`. -/
structure IndexOneDrazinInverse (n : ℕ)
    (A D : Fin n → Fin n → ℝ) : Prop where
  comm : matMul n A D = matMul n D A
  reflexive : matMul n D (matMul n A D) = D
  index_one : matMul n (matMul n A A) D = A

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.27):
    the Drazin range projector `E = (I - G)(I - G)^D` used to split the
    singular-system error into range and fixed/null components. -/
noncomputable def stationaryDrazinRangeProjector (n : ℕ)
    (G D : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n (matSub_id n G) D

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equations (17.25)-(17.27):
    the fixed/null projector `I - E = I - (I - G)(I - G)^D`, corresponding to
    the limiting fixed-space component in the semiconvergent analysis. -/
noncomputable def stationaryDrazinFixedProjector (n : ℕ)
    (G D : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matSub_id n (stationaryDrazinRangeProjector n G D)

/-- Multiplying two complements expands as
    `(I - A)(I - E) = I - E - A + AE`. -/
private theorem matMul_matSub_id_matSub_id (n : ℕ)
    (A E : Fin n → Fin n → ℝ) :
    matMul n (matSub_id n A) (matSub_id n E) =
      fun i j => idMatrix n i j - E i j - A i j + matMul n A E i j := by
  ext i j
  unfold matMul matSub_id
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  have hII :
      ∑ k : Fin n, idMatrix n i k * idMatrix n k j = idMatrix n i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_left n (idMatrix n))
    simpa [matMul] using h
  have hIE :
      ∑ k : Fin n, idMatrix n i k * E k j = E i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_left n E)
    simpa [matMul] using h
  have hAI :
      ∑ k : Fin n, A i k * idMatrix n k j = A i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_right n A)
    simpa [matMul] using h
  rw [hII, hIE, hAI]
  ring

/-- Left multiplication by a complement expands as `(I-A)B = B - AB`. -/
private theorem matMul_matSub_id_left (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    matMul n (matSub_id n A) B =
      fun i j => B i j - matMul n A B i j := by
  ext i j
  unfold matMul matSub_id
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  have hIB :
      ∑ k : Fin n, idMatrix n i k * B k j = B i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_left n B)
    simpa [matMul] using h
  rw [hIB]

/-- Right multiplication by a complement expands as `B(I-A) = B - BA`. -/
private theorem matMul_matSub_id_right (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    matMul n B (matSub_id n A) =
      fun i j => B i j - matMul n B A i j := by
  ext i j
  unfold matMul matSub_id
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hBI :
      ∑ k : Fin n, B i k * idMatrix n k j = B i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_right n B)
    simpa [matMul] using h
  rw [hBI]

/-- The Drazin range projector `E = (I - G)D` is idempotent under the
    index-one Drazin inverse identities. -/
theorem stationaryDrazinRangeProjector_idempotent (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n (stationaryDrazinRangeProjector n G D)
      (stationaryDrazinRangeProjector n G D) =
    stationaryDrazinRangeProjector n G D := by
  unfold stationaryDrazinRangeProjector
  rw [matMul_assoc]
  exact congrArg (fun T : Fin n → Fin n → ℝ => matMul n (matSub_id n G) T)
    hD.reflexive

/-- The Drazin range projector `E = (I-G)D` absorbs `I-G` on the left:
    `(I-G)E = I-G`. -/
theorem stationaryDrazinRangeProjector_matSub_id_mul_left (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n (matSub_id n G) (stationaryDrazinRangeProjector n G D) =
      matSub_id n G := by
  unfold stationaryDrazinRangeProjector
  rw [← matMul_assoc]
  exact hD.index_one

/-- The Drazin range projector `E = (I-G)D` also absorbs `I-G` on the right:
    `E(I-G) = I-G`. -/
theorem stationaryDrazinRangeProjector_matSub_id_mul_right (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n (stationaryDrazinRangeProjector n G D) (matSub_id n G) =
      matSub_id n G := by
  let A := matSub_id n G
  change matMul n (matMul n A D) A = A
  calc
    matMul n (matMul n A D) A = matMul n A (matMul n D A) := by
      rw [matMul_assoc]
    _ = matMul n A (matMul n A D) := by
      rw [← hD.comm]
    _ = matMul n (matMul n A A) D := by
      rw [← matMul_assoc]
    _ = A := hD.index_one

/-- The Drazin range projector commutes with the stationary iteration matrix
    `G`. -/
theorem stationaryDrazinRangeProjector_commutes_with_G (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n G (stationaryDrazinRangeProjector n G D) =
      matMul n (stationaryDrazinRangeProjector n G D) G := by
  let A := matSub_id n G
  let E := stationaryDrazinRangeProjector n G D
  have hG : matSub_id n A = G := by
    ext i j
    dsimp [A, matSub_id, idMatrix]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  have hAE : matMul n A E = A := by
    simpa [A, E] using
      stationaryDrazinRangeProjector_matSub_id_mul_left n G D hD
  have hEA : matMul n E A = A := by
    simpa [A, E] using
      stationaryDrazinRangeProjector_matSub_id_mul_right n G D hD
  calc
    matMul n G (stationaryDrazinRangeProjector n G D) =
      matMul n (matSub_id n A) E := by
        rw [hG]
    _ = (fun i j => E i j - matMul n A E i j) :=
        matMul_matSub_id_left n A E
    _ = (fun i j => E i j - A i j) := by
        rw [hAE]
    _ = (fun i j => E i j - matMul n E A i j) := by
        rw [hEA]
    _ = matMul n E (matSub_id n A) := by
        exact (matMul_matSub_id_right n A E).symm
    _ = matMul n (stationaryDrazinRangeProjector n G D) G := by
        rw [hG]

/-- The Drazin range projector commutes with every finite power of `G`. -/
theorem stationaryDrazinRangeProjector_commutes_with_matPow (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ k, matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D) =
      matMul n (stationaryDrazinRangeProjector n G D) (matPow n G k) := by
  exact matPow_comm_of_matMul_comm n G
    (stationaryDrazinRangeProjector n G D)
    (stationaryDrazinRangeProjector_commutes_with_G n G D hD)

/-- Sandwiching a powered range component by the Drazin range projector leaves
    it unchanged: `E G^k E = G^k E`. -/
theorem stationaryDrazinRangeProjector_matPow_sandwich (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ k,
      matMul n (stationaryDrazinRangeProjector n G D)
        (matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D)) =
      matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D) := by
  intro k
  let E := stationaryDrazinRangeProjector n G D
  have hEid : matMul n E E = E := by
    simpa [E] using stationaryDrazinRangeProjector_idempotent n G D hD
  have hcomm :
      matMul n (matPow n G k) E = matMul n E (matPow n G k) := by
    simpa [E] using stationaryDrazinRangeProjector_commutes_with_matPow n G D hD k
  calc
    matMul n (stationaryDrazinRangeProjector n G D)
        (matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D)) =
      matMul n E (matMul n (matPow n G k) E) := rfl
    _ = matMul n (matMul n E (matPow n G k)) E := by
        rw [matMul_assoc]
    _ = matMul n (matMul n (matPow n G k) E) E := by
        rw [← hcomm]
    _ = matMul n (matPow n G k) (matMul n E E) := by
        rw [matMul_assoc]
    _ = matMul n (matPow n G k) E := by
        rw [hEid]

/-- The Drazin range and fixed projectors are complementary on the right:
    `E(I-E) = 0`. -/
theorem stationaryDrazinRangeProjector_mul_fixedProjector_eq_zero (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n (stationaryDrazinRangeProjector n G D)
      (stationaryDrazinFixedProjector n G D) = fun _ _ => 0 := by
  let E := stationaryDrazinRangeProjector n G D
  have hEid : matMul n E E = E := by
    simpa [E] using stationaryDrazinRangeProjector_idempotent n G D hD
  ext i j
  have hEI : (∑ k : Fin n, E i k * idMatrix n k j) = E i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_right n E)
    simpa [matMul] using h
  have hEE : (∑ k : Fin n, E i k * E k j) = E i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j) hEid
    simpa [matMul] using h
  dsimp [stationaryDrazinFixedProjector, E, matMul, matSub_id]
  calc
    (∑ k : Fin n,
        stationaryDrazinRangeProjector n G D i k *
          (idMatrix n k j - stationaryDrazinRangeProjector n G D k j)) =
      ∑ k : Fin n,
        (E i k * idMatrix n k j - E i k * E k j) := by
        apply Finset.sum_congr rfl
        intro k _hk
        ring
    _ = (∑ k : Fin n, E i k * idMatrix n k j) -
        ∑ k : Fin n, E i k * E k j := by
        rw [← Finset.sum_sub_distrib]
    _ = 0 := by
        rw [hEI, hEE]
        ring

/-- The Drazin range and fixed projectors are complementary on the left:
    `(I-E)E = 0`. -/
theorem stationaryDrazinFixedProjector_mul_rangeProjector_eq_zero (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n (stationaryDrazinFixedProjector n G D)
      (stationaryDrazinRangeProjector n G D) = fun _ _ => 0 := by
  let E := stationaryDrazinRangeProjector n G D
  have hEid : matMul n E E = E := by
    simpa [E] using stationaryDrazinRangeProjector_idempotent n G D hD
  ext i j
  have hIE : (∑ k : Fin n, idMatrix n i k * E k j) = E i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_left n E)
    simpa [matMul] using h
  have hEE : (∑ k : Fin n, E i k * E k j) = E i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j) hEid
    simpa [matMul] using h
  dsimp [stationaryDrazinFixedProjector, E, matMul, matSub_id]
  calc
    (∑ k : Fin n,
        (idMatrix n i k - stationaryDrazinRangeProjector n G D i k) *
          stationaryDrazinRangeProjector n G D k j) =
      ∑ k : Fin n,
        (idMatrix n i k * E k j - E i k * E k j) := by
        apply Finset.sum_congr rfl
        intro k _hk
        ring
    _ = (∑ k : Fin n, idMatrix n i k * E k j) -
        ∑ k : Fin n, E i k * E k j := by
        rw [← Finset.sum_sub_distrib]
    _ = 0 := by
        rw [hIE, hEE]
        ring

/-- The complementary Drazin fixed/null projector `I-E` is idempotent. -/
theorem stationaryDrazinFixedProjector_idempotent (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n (stationaryDrazinFixedProjector n G D)
      (stationaryDrazinFixedProjector n G D) =
    stationaryDrazinFixedProjector n G D := by
  let E := stationaryDrazinRangeProjector n G D
  have hEid : matMul n E E = E := by
    simpa [E] using stationaryDrazinRangeProjector_idempotent n G D hD
  calc
    matMul n (stationaryDrazinFixedProjector n G D)
        (stationaryDrazinFixedProjector n G D) =
      matMul n (matSub_id n E) (matSub_id n E) := rfl
    _ = (fun i j => idMatrix n i j - E i j - E i j + matMul n E E i j) :=
        matMul_matSub_id_matSub_id n E E
    _ = stationaryDrazinFixedProjector n G D := by
        ext i j
        rw [hEid]
        unfold stationaryDrazinFixedProjector matSub_id
        ring

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equations (17.25)-(17.27):
    the Drazin fixed/null projector `I - (I - G)D` is fixed by the stationary
    iteration matrix `G`.  This is the algebraic projector fact needed by the
    finite singular error split. -/
theorem stationaryDrazinFixedProjector_fixed_by_G (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n G (stationaryDrazinFixedProjector n G D) =
      stationaryDrazinFixedProjector n G D := by
  let A := matSub_id n G
  let E := stationaryDrazinRangeProjector n G D
  have hG : matSub_id n A = G := by
    ext i j
    dsimp [A, matSub_id, idMatrix]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  have hAE : matMul n A E = A := by
    dsimp [A, E, stationaryDrazinRangeProjector]
    rw [← matMul_assoc]
    exact hD.index_one
  calc
    matMul n G (stationaryDrazinFixedProjector n G D)
        = matMul n G (matSub_id n E) := rfl
    _ = matMul n (matSub_id n A) (matSub_id n E) := by
            rw [hG]
    _ = (fun i j => idMatrix n i j - E i j - A i j + matMul n A E i j) :=
            matMul_matSub_id_matSub_id n A E
    _ = matSub_id n E := by
            ext i j
            rw [hAE]
            unfold matSub_id
            ring
    _ = stationaryDrazinFixedProjector n G D := rfl

/-- Every finite power of `G` fixes the Drazin fixed/null projector.  This is
    the finite-power algebraic side of the limiting projector identity used in
    Higham's semiconvergent singular-system analysis. -/
theorem stationaryDrazinFixedProjector_matPow_fixed (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ k, matMul n (matPow n G k) (stationaryDrazinFixedProjector n G D) =
      stationaryDrazinFixedProjector n G D := by
  exact matPow_mul_fixed_of_matMul_fixed n G
    (stationaryDrazinFixedProjector n G D)
    (stationaryDrazinFixedProjector_fixed_by_G n G D hD)

/-- Vector-action form of `stationaryDrazinFixedProjector_fixed_by_G`. -/
theorem stationaryDrazinFixedProjector_matMulVec_fixed (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D)
    (v : Fin n → ℝ) :
    ∀ i, matMulVec n G
        (matMulVec n (stationaryDrazinFixedProjector n G D) v) i =
      matMulVec n (stationaryDrazinFixedProjector n G D) v i := by
  intro i
  calc
    matMulVec n G (matMulVec n (stationaryDrazinFixedProjector n G D) v) i
        = matMulVec n
            (matMul n G (stationaryDrazinFixedProjector n G D)) v i := by
            rw [← matMulVec_matMul]
    _ = matMulVec n (stationaryDrazinFixedProjector n G D) v i := by
            rw [stationaryDrazinFixedProjector_fixed_by_G n G D hD]

/-- The Drazin range projector supplies the fixed-null hypothesis required by
    the finite singular error split: `G` fixes `(I - E)M^{-1}xi_t`. -/
theorem stationaryDrazinRangeProjector_null_component_fixed (n : ℕ)
    (G D M_inv : Fin n → Fin n → ℝ) (xi : ℕ → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ t i,
      matMulVec n G
        (matMulVec n (matSub_id n (stationaryDrazinRangeProjector n G D))
          (matMulVec n M_inv (xi t))) i =
      matMulVec n (matSub_id n (stationaryDrazinRangeProjector n G D))
        (matMulVec n M_inv (xi t)) i := by
  intro t i
  simpa [stationaryDrazinFixedProjector] using
    stationaryDrazinFixedProjector_matMulVec_fixed n G D hD
      (matMulVec n M_inv (xi t)) i

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.28):
    the finite source term `S_m = sum_{k=0}^m G^k E M⁻¹ ξ_{m-k}` used in
    the singular-system forward-error analysis. -/
noncomputable def singularErrorSourceTerm (n : ℕ)
    (G E M_inv : Fin n → Fin n → ℝ) (ξ : ℕ → Fin n → ℝ) (m : ℕ) :
    Fin n → ℝ :=
  fun i => ∑ k ∈ Finset.range (m + 1),
    matMulVec n (matPow n G k)
      (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.27), finite
    algebraic core: once the `(I - E)M⁻¹ξ_t` component is in the fixed
    subspace of `G`, the finite error recurrence splits into the propagated
    initial error, the `S_m` range term, and the accumulated fixed/null
    component.  The Drazin/projector construction that proves the fixed-space
    hypothesis is intentionally left as an explicit later dependency. -/
theorem singular_error_split_finite (n : ℕ)
    (A M N M_inv E : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (hNull : ∀ t i,
      matMulVec n (iterMatrix n M_inv N)
        (matMulVec n (matSub_id n E) (matMulVec n M_inv (ξ t))) i =
      matMulVec n (matSub_id n E) (matMulVec n M_inv (ξ t)) i)
    (m : ℕ) :
    ∀ i, x i - x_hat (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i +
      singularErrorSourceTerm n (iterMatrix n M_inv N) E M_inv ξ m i +
      matMulVec n (matSub_id n E)
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i := by
  intro i
  let G := iterMatrix n M_inv N
  let C := matSub_id n E
  change x i - x_hat (m + 1) i =
      matMulVec n (matPow n G (m + 1)) (fun j => x j - x_hat 0 j) i +
      singularErrorSourceTerm n G E M_inv ξ m i +
      matMulVec n C
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i
  have hbase := sourceComputedIteration_error_finite_sum
    n A M N M_inv hS b x hAx x_hat ξ hIter m i
  have hsumSplit :
      (∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n G k)
          (matMulVec n M_inv (ξ (m - k))) i) =
      singularErrorSourceTerm n G E M_inv ξ m i +
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n C (matMulVec n M_inv (ξ (m - k))) i := by
    calc
      (∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n G k)
          (matMulVec n M_inv (ξ (m - k))) i)
          =
        ∑ k ∈ Finset.range (m + 1),
          (matMulVec n (matPow n G k)
              (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i +
            matMulVec n C (matMulVec n M_inv (ξ (m - k))) i) := by
            apply Finset.sum_congr rfl
            intro k _hk
            let v := matMulVec n M_inv (ξ (m - k))
            have hsplit :
                v = fun j => matMulVec n E v j + matMulVec n C v j := by
              ext j
              exact (matMulVec_add_complement_apply n E v j).symm
            have hfixedOne :
                ∀ r, matMulVec n G (matMulVec n C v) r =
                  matMulVec n C v r := by
              intro r
              simpa [G, C, v] using hNull (m - k) r
            have hfixedPow :
                matMulVec n (matPow n G k) (matMulVec n C v) i =
                  matMulVec n C v i :=
              matPow_fixed_of_matMulVec_fixed n G (matMulVec n C v)
                hfixedOne k i
            calc
              matMulVec n (matPow n G k)
                  (matMulVec n M_inv (ξ (m - k))) i =
                matMulVec n (matPow n G k) v i := by rfl
              _ = matMulVec n (matPow n G k)
                    (fun j => matMulVec n E v j + matMulVec n C v j) i := by
                    exact congrArg
                      (fun w => matMulVec n (matPow n G k) w i) hsplit
              _ = matMulVec n (matPow n G k) (matMulVec n E v) i +
                    matMulVec n (matPow n G k) (matMulVec n C v) i := by
                    simpa using congrFun
                      (matMulVec_add_right n (matPow n G k)
                        (matMulVec n E v) (matMulVec n C v)) i
              _ = matMulVec n (matPow n G k) (matMulVec n E v) i +
                    matMulVec n C v i := by
                    rw [hfixedPow]
              _ = matMulVec n (matPow n G k)
                    (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i +
                    matMulVec n C (matMulVec n M_inv (ξ (m - k))) i := by rfl
      _ =
        (∑ k ∈ Finset.range (m + 1),
          matMulVec n (matPow n G k)
            (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i) +
        ∑ k ∈ Finset.range (m + 1),
          matMulVec n C (matMulVec n M_inv (ξ (m - k))) i := by
          rw [Finset.sum_add_distrib]
      _ = singularErrorSourceTerm n G E M_inv ξ m i +
          ∑ k ∈ Finset.range (m + 1),
            matMulVec n C (matMulVec n M_inv (ξ (m - k))) i := by
          rfl
  have hsumC :
      (∑ k ∈ Finset.range (m + 1),
        matMulVec n C (matMulVec n M_inv (ξ (m - k))) i) =
      matMulVec n C
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i := by
    have hM :
        matMulVec n M_inv
            (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j) =
          fun r => ∑ k ∈ Finset.range (m + 1),
            matMulVec n M_inv (ξ (m - k)) r := by
      simpa using
        matMulVec_finset_sum_right n M_inv (Finset.range (m + 1))
          (fun k => ξ (m - k))
    have hC :
        matMulVec n C
            (fun r => ∑ k ∈ Finset.range (m + 1),
              matMulVec n M_inv (ξ (m - k)) r) =
          fun r => ∑ k ∈ Finset.range (m + 1),
            matMulVec n C (matMulVec n M_inv (ξ (m - k))) r := by
      simpa using
        matMulVec_finset_sum_right n C (Finset.range (m + 1))
          (fun k => matMulVec n M_inv (ξ (m - k)))
    calc
      (∑ k ∈ Finset.range (m + 1),
        matMulVec n C (matMulVec n M_inv (ξ (m - k))) i) =
        matMulVec n C
          (fun r => ∑ k ∈ Finset.range (m + 1),
            matMulVec n M_inv (ξ (m - k)) r) i := by
            simpa using (congrFun hC i).symm
      _ = matMulVec n C
          (matMulVec n M_inv
            (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i := by
            rw [← hM]
  calc
    x i - x_hat (m + 1) i =
      matMulVec n (matPow n G (m + 1)) (fun j => x j - x_hat 0 j) i +
        ∑ k ∈ Finset.range (m + 1),
          matMulVec n (matPow n G k)
            (matMulVec n M_inv (ξ (m - k))) i := by
        simpa [G] using hbase
    _ = matMulVec n (matPow n G (m + 1)) (fun j => x j - x_hat 0 j) i +
        (singularErrorSourceTerm n G E M_inv ξ m i +
          ∑ k ∈ Finset.range (m + 1),
            matMulVec n C (matMulVec n M_inv (ξ (m - k))) i) := by
        rw [hsumSplit]
    _ = matMulVec n (matPow n G (m + 1)) (fun j => x j - x_hat 0 j) i +
        singularErrorSourceTerm n G E M_inv ξ m i +
        matMulVec n C
          (matMulVec n M_inv
            (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i := by
        rw [hsumC]
        ring

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equations (17.24), (17.27),
    and (17.28): finite singular-system error split with the source Drazin
    projector `E = (I - G)(I - G)^D`.

    Compared with `singular_error_split_finite`, this wrapper no longer asks
    for the fixed-null hypothesis separately: it is supplied by the
    index-one Drazin inverse certificate for `I - G`.  The limiting
    semiconvergence and infinite-sum bounds remain separate obligations. -/
theorem singular_error_split_finite_of_indexOneDrazin_projector (n : ℕ)
    (A M N M_inv D : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (hD : IndexOneDrazinInverse n (matSub_id n (iterMatrix n M_inv N)) D)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (xi : ℕ → Fin n → ℝ)
    (hIter : SourceComputedIteration n M N b x_hat xi)
    (m : ℕ) :
    ∀ i, x i - x_hat (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i +
      singularErrorSourceTerm n (iterMatrix n M_inv N)
        (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D)
        M_inv xi m i +
      matMulVec n
        (stationaryDrazinFixedProjector n (iterMatrix n M_inv N) D)
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), xi (m - k) j)) i := by
  intro i
  have hNull :
      ∀ t r,
        matMulVec n (iterMatrix n M_inv N)
          (matMulVec n
            (matSub_id n
              (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D))
            (matMulVec n M_inv (xi t))) r =
        matMulVec n
          (matSub_id n
            (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D))
          (matMulVec n M_inv (xi t)) r := by
    intro t r
    exact stationaryDrazinRangeProjector_null_component_fixed
      n (iterMatrix n M_inv N) D M_inv xi hD t r
  have hsplit := singular_error_split_finite n A M N M_inv
    (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D)
    hS b x hAx x_hat xi hIter hNull m i
  simpa [stationaryDrazinFixedProjector] using hsplit

/-- The componentwise source vector `( |M| + |N| ) |x|` appearing in Higham,
    2nd ed., Chapter 17, equations (17.10), (17.29), and (17.32). -/
noncomputable def stationaryLocalErrorSourceVector (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, (|M i j| + |N i j|) * |x j|

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29):
    finite normwise coefficient `sum ||G^k E M⁻¹||_∞` for the singular
    source term `S_m`. -/
noncomputable def singularErrorSourceNormSum (n : ℕ)
    (G E M_inv : Fin n → Fin n → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    infNorm (matMul n (matMul n (matPow n G k) E) M_inv)

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29):
    finite componentwise right-hand side
    `c_n u (1+theta_x) sum |G^k E M⁻¹| (|M|+|N|)|x|`
    for the singular source term `S_m`. -/
noncomputable def singularErrorSourceComponentBound (n : ℕ)
    (G E M_inv M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (cn_u theta_x : ℝ) (m : ℕ) : Fin n → ℝ :=
  fun i => cn_u * (1 + theta_x) *
    ∑ k ∈ Finset.range (m + 1),
      matMulVec n
        (absMatrix n (matMul n (matMul n (matPow n G k) E) M_inv))
        (stationaryLocalErrorSourceVector n M N x) i

/-- The action defining `S_m` is the matrix product
    `(G^k E M⁻¹) ξ_{m-k}` term by term. -/
private theorem singularErrorSourceTerm_term_eq (n : ℕ)
    (G E M_inv : Fin n → Fin n → ℝ) (ξ : ℕ → Fin n → ℝ)
    (m k : ℕ) :
    matMulVec n (matPow n G k)
        (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) =
      matMulVec n (matMul n (matMul n (matPow n G k) E) M_inv)
        (ξ (m - k)) := by
  ext i
  calc
    matMulVec n (matPow n G k)
        (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i =
      matMulVec n (matMul n (matPow n G k) E)
        (matMulVec n M_inv (ξ (m - k))) i := by
        rw [← matMulVec_matMul]
    _ = matMulVec n (matMul n (matMul n (matPow n G k) E) M_inv)
        (ξ (m - k)) i := by
        rw [← matMulVec_matMul]

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), finite
    normwise surface: a uniform local-error norm bound `||ξ_t||∞ ≤ μ` bounds
    `||S_m||∞` by `μ sum ||G^k E M⁻¹||∞`.  The source's displayed
    `c_n u(1+gamma_x)(||M||∞+||N||∞)||x||∞` is obtained by instantiating `μ`
    with the normwise local-error estimate. -/
theorem singularErrorSourceTerm_norm_bound (n : ℕ) (hn : 0 < n)
    (G E M_inv : Fin n → Fin n → ℝ) (ξ : ℕ → Fin n → ℝ)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hξ : ∀ t : ℕ, infNormVec (ξ t) ≤ μ) (m : ℕ) :
    infNormVec (singularErrorSourceTerm n G E M_inv ξ m) ≤
      μ * singularErrorSourceNormSum n G E M_inv m := by
  apply infNormVec_le_of_abs_le
  · intro i
    calc
      |singularErrorSourceTerm n G E M_inv ξ m i|
          = |∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n G k)
                (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| := by
              rfl
      _ ≤ ∑ k ∈ Finset.range (m + 1),
            |matMulVec n (matPow n G k)
              (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (m + 1),
            infNorm (matMul n (matMul n (matPow n G k) E) M_inv) * μ := by
            apply Finset.sum_le_sum
            intro k _hk
            let P := matMul n (matMul n (matPow n G k) E) M_inv
            have hterm :=
              congrFun (singularErrorSourceTerm_term_eq n G E M_inv ξ m k) i
            calc
              |matMulVec n (matPow n G k)
                  (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i|
                  = |matMulVec n P (ξ (m - k)) i| := by
                    rw [hterm]
              _ ≤ infNormVec (matMulVec n P (ξ (m - k))) :=
                    abs_le_infNormVec _ i
              _ ≤ infNorm P * infNormVec (ξ (m - k)) :=
                    infNormVec_matMulVec_le hn P (ξ (m - k))
              _ ≤ infNorm P * μ := by
                    exact mul_le_mul_of_nonneg_left (hξ (m - k)) (infNorm_nonneg P)
      _ = μ * singularErrorSourceNormSum n G E M_inv m := by
            unfold singularErrorSourceNormSum
            rw [← Finset.sum_mul]
            ring
  · unfold singularErrorSourceNormSum
    exact mul_nonneg hμ
      (Finset.sum_nonneg (fun k _hk => infNorm_nonneg _))

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), finite
    componentwise surface: if the local errors satisfy the already-simplified
    componentwise source bound, then the singular source term `S_m` is bounded
    by `c_n u(1+theta_x) sum |G^k E M⁻¹|(|M|+|N|)|x|`. -/
theorem singularErrorSourceTerm_componentwise_bound (n : ℕ)
    (G E M_inv M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (ξ : ℕ → Fin n → ℝ) (cn_u theta_x : ℝ)
    (hξ : ∀ (t : ℕ) (j : Fin n),
      |ξ t j| ≤ cn_u * (1 + theta_x) *
        stationaryLocalErrorSourceVector n M N x j)
    (m : ℕ) :
    ∀ i, |singularErrorSourceTerm n G E M_inv ξ m i| ≤
      singularErrorSourceComponentBound n G E M_inv M N x cn_u theta_x m i := by
  intro i
  let coeff := cn_u * (1 + theta_x)
  calc
    |singularErrorSourceTerm n G E M_inv ξ m i|
        = |∑ k ∈ Finset.range (m + 1),
            matMulVec n (matPow n G k)
              (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| := by
            rfl
    _ ≤ ∑ k ∈ Finset.range (m + 1),
          |matMulVec n (matPow n G k)
            (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1),
          coeff *
            matMulVec n
              (absMatrix n (matMul n (matMul n (matPow n G k) E) M_inv))
              (stationaryLocalErrorSourceVector n M N x) i := by
          apply Finset.sum_le_sum
          intro k _hk
          let P := matMul n (matMul n (matPow n G k) E) M_inv
          have hterm :=
            congrFun (singularErrorSourceTerm_term_eq n G E M_inv ξ m k) i
          calc
            |matMulVec n (matPow n G k)
                (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i|
                = |matMulVec n P (ξ (m - k)) i| := by
                  rw [hterm]
            _ ≤ ∑ j : Fin n, |P i j| * |ξ (m - k) j| :=
                  abs_matMulVec_le n P (ξ (m - k)) i
            _ ≤ ∑ j : Fin n, |P i j| *
                  (coeff * stationaryLocalErrorSourceVector n M N x j) := by
                  apply Finset.sum_le_sum
                  intro j _hj
                  exact mul_le_mul_of_nonneg_left
                    (by simpa [coeff] using hξ (m - k) j) (abs_nonneg _)
            _ = coeff *
                  matMulVec n (absMatrix n P)
                    (stationaryLocalErrorSourceVector n M N x) i := by
                  unfold matMulVec absMatrix
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl (fun j _hj => by ring)
    _ = singularErrorSourceComponentBound n G E M_inv M N x cn_u theta_x m i := by
          unfold singularErrorSourceComponentBound
          rw [← Finset.mul_sum]

-- ============================================================
-- §17.2  Componentwise forward bound (eq 17.6)
-- ============================================================

/-- **Eq. 17.6 (Componentwise forward bound)**: triangle inequality bound on
    |∑_j G^{m+1}_{ij} e_{0,j} + ∑_{k=0}^m ∑_j G^k_{ij} w_{m-k,j}|. -/
theorem componentwise_forward_bound (n : ℕ)
    (G : Fin n → Fin n → ℝ) (e₀ : Fin n → ℝ) (m : ℕ)
    (w : ℕ → (Fin n → ℝ)) (μ : ℕ → (Fin n → ℝ))
    (hw : ∀ k i, |w k i| ≤ μ k i)
    (_hμ : ∀ k i, 0 ≤ μ k i) :
    ∀ i, |∑ j : Fin n, matPow n G (m + 1) i j * e₀ j +
      ∑ k ∈ Finset.range (m + 1),
        ∑ j : Fin n, matPow n G k i j * w (m - k) j| ≤
      ∑ j : Fin n, |matPow n G (m + 1) i j| * |e₀ j| +
      ∑ k ∈ Finset.range (m + 1),
        ∑ j : Fin n, |matPow n G k i j| * μ (m - k) j := by
  intro i
  calc |∑ j : Fin n, matPow n G (m + 1) i j * e₀ j +
        ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, matPow n G k i j * w (m - k) j|
      ≤ |∑ j : Fin n, matPow n G (m + 1) i j * e₀ j| +
        |∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, matPow n G k i j * w (m - k) j| := abs_add_le _ _
    _ ≤ (∑ j : Fin n, |matPow n G (m + 1) i j * e₀ j|) +
        ∑ k ∈ Finset.range (m + 1),
          |∑ j : Fin n, matPow n G k i j * w (m - k) j| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ (Finset.univ : Finset (Fin n)))
          (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ j : Fin n, |matPow n G (m + 1) i j| * |e₀ j|) +
        ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, |matPow n G k i j * w (m - k) j| := by
        gcongr with j _
        · exact le_of_eq (abs_mul _ _)
        · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ j : Fin n, |matPow n G (m + 1) i j| * |e₀ j|) +
        ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, |matPow n G k i j| * μ (m - k) j := by
        gcongr with k _ j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hw _ _) (abs_nonneg _)

-- ============================================================
-- §17.2  Iterate-growth constants (eqs 17.7, 17.9)
-- ============================================================

/-- Higham, 2nd ed., Chapter 17, equation (17.7):
    candidate values for the normwise iterate-growth constant
    `gamma_x = sup_k ||xhat_k||_inf / ||x||_inf`. -/
def NormwiseIterateGrowthValues (n : ℕ)
    (x : Fin n → ℝ) (x_hat : ℕ → Fin n → ℝ) : Set ℝ :=
  {rho | ∃ k : ℕ, rho = infNormVec (x_hat k) / infNormVec x}

/-- Higham, 2nd ed., Chapter 17, equation (17.7):
    normwise iterate-growth constant as the supremum of the source ratios. -/
noncomputable def normwiseIterateGrowth (n : ℕ)
    (x : Fin n → ℝ) (x_hat : ℕ → Fin n → ℝ) : ℝ :=
  sSup (NormwiseIterateGrowthValues n x x_hat)

/-- Predicate form of the bound supplied by the source `gamma_x` definition. -/
def NormwiseIterateGrowthBound (n : ℕ)
    (x : Fin n → ℝ) (x_hat : ℕ → Fin n → ℝ) (gamma_x : ℝ) : Prop :=
  ∀ k : ℕ, infNormVec (x_hat k) ≤ gamma_x * infNormVec x

/-- Each displayed ratio is bounded by the supremum model of `gamma_x`, provided
    the ratio set is bounded above. -/
theorem normwiseIterateGrowth_ratio_le (n : ℕ)
    (x : Fin n → ℝ) (x_hat : ℕ → Fin n → ℝ)
    (hBdd : BddAbove (NormwiseIterateGrowthValues n x x_hat)) (k : ℕ) :
    infNormVec (x_hat k) / infNormVec x ≤
      normwiseIterateGrowth n x x_hat := by
  unfold normwiseIterateGrowth
  exact le_csSup hBdd ⟨k, rfl⟩

/-- The supremum model of `gamma_x` supplies the normwise iterate-growth bound
    used in the finite and q-bound forward-error wrappers when `x` is nonzero in
    infinity norm. -/
theorem normwiseIterateGrowthBound_of_sSup (n : ℕ)
    (x : Fin n → ℝ) (x_hat : ℕ → Fin n → ℝ)
    (hx : 0 < infNormVec x)
    (hBdd : BddAbove (NormwiseIterateGrowthValues n x x_hat)) :
    NormwiseIterateGrowthBound n x x_hat
      (normwiseIterateGrowth n x x_hat) := by
  intro k
  have hratio :=
    normwiseIterateGrowth_ratio_le n x x_hat hBdd k
  have hmul := mul_le_mul_of_nonneg_right hratio (le_of_lt hx)
  have hx_ne : infNormVec x ≠ 0 := ne_of_gt hx
  simpa [NormwiseIterateGrowthBound, div_mul_cancel₀, hx_ne] using hmul

/-- Higham, 2nd ed., Chapter 17, equation (17.9):
    candidate values for the componentwise iterate-growth constant
    `theta_x = sup_k max_i |xhat_k i| / |x i|`, restricted to nonzero
    components of `x`.  The source notes that zero components require a separate
    compatibility condition. -/
def ComponentwiseIterateGrowthValues (n : ℕ)
    (x : Fin n → ℝ) (x_hat : ℕ → Fin n → ℝ) : Set ℝ :=
  {rho | ∃ (k : ℕ) (i : Fin n), x i ≠ 0 ∧ rho = |x_hat k i| / |x i|}

/-- Higham, 2nd ed., Chapter 17, equation (17.9):
    componentwise iterate-growth constant as the supremum of the nonzero-entry
    source ratios. -/
noncomputable def componentwiseIterateGrowth (n : ℕ)
    (x : Fin n → ℝ) (x_hat : ℕ → Fin n → ℝ) : ℝ :=
  sSup (ComponentwiseIterateGrowthValues n x x_hat)

/-- Predicate form of the componentwise bound supplied by the source
    `theta_x` definition. -/
def ComponentwiseIterateGrowthBound (n : ℕ)
    (x : Fin n → ℝ) (x_hat : ℕ → Fin n → ℝ) (theta_x : ℝ) : Prop :=
  ∀ (k : ℕ) (i : Fin n), |x_hat k i| ≤ theta_x * |x i|

/-- Each nonzero-entry displayed ratio is bounded by the supremum model of
    `theta_x`, provided the ratio set is bounded above. -/
theorem componentwiseIterateGrowth_ratio_le (n : ℕ)
    (x : Fin n → ℝ) (x_hat : ℕ → Fin n → ℝ)
    (hBdd : BddAbove (ComponentwiseIterateGrowthValues n x x_hat))
    (k : ℕ) (i : Fin n) (hx : x i ≠ 0) :
    |x_hat k i| / |x i| ≤ componentwiseIterateGrowth n x x_hat := by
  unfold componentwiseIterateGrowth
  exact le_csSup hBdd ⟨k, i, hx, rfl⟩

/-- The supremum model of `theta_x` supplies the componentwise iterate-growth
    bound used by the local-error simplification, assuming computed iterates are
    also zero wherever the exact solution has a zero component. -/
theorem componentwiseIterateGrowthBound_of_sSup (n : ℕ)
    (x : Fin n → ℝ) (x_hat : ℕ → Fin n → ℝ)
    (hzero : ∀ (k : ℕ) (i : Fin n), x i = 0 → x_hat k i = 0)
    (hBdd : BddAbove (ComponentwiseIterateGrowthValues n x x_hat)) :
    ComponentwiseIterateGrowthBound n x x_hat
      (componentwiseIterateGrowth n x x_hat) := by
  intro k i
  by_cases hx : x i = 0
  · simp [hx, hzero k i hx]
  · have hratio :=
      componentwiseIterateGrowth_ratio_le n x x_hat hBdd k i hx
    have hden_pos : 0 < |x i| := abs_pos.mpr hx
    have hmul := mul_le_mul_of_nonneg_right hratio (le_of_lt hden_pos)
    have hden_ne : |x i| ≠ 0 := ne_of_gt hden_pos
    simpa [ComponentwiseIterateGrowthBound, div_mul_cancel₀, hden_ne] using hmul

-- ============================================================
-- §17.2  Local error bound and simplification (eqs 17.2, 17.10)
-- ============================================================

/-- Eq. 17.2: local rounding error bound. -/
def LocalErrorBound (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : ℕ → (Fin n → ℝ))
    (ξ : ℕ → (Fin n → ℝ)) (cn_u : ℝ) : Prop :=
  ∀ k i, |ξ k i| ≤ cn_u * (∑ j : Fin n, |M i j| * |x_hat (k + 1) j| +
                              ∑ j : Fin n, |N i j| * |x_hat k j| + |b i|)

/-- **Eq. 17.10**: |ξ_k,i| ≤ c_n u(1+θ_x) ∑_j (|M_{ij}|+|N_{ij}|)|x_j|. -/
theorem local_error_simplified (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (cn_u θ_x : ℝ) (hcn : 0 ≤ cn_u) (_hθ : 0 ≤ θ_x)
    (hx_bound : ∀ k i, |x_hat k i| ≤ θ_x * |x i|)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u) :
    ∀ k i, |ξ k i| ≤ cn_u * (1 + θ_x) *
      ∑ j : Fin n, (|M i j| + |N i j|) * |x j| := by
  intro k i
  have hL := hLocal k i
  have hb : |b i| ≤ ∑ j : Fin n, (|M i j| + |N i j|) * |x j| := by
    calc |b i| = |∑ j, (M i j - N i j) * x j| := by rw [hAx]
      _ ≤ ∑ j, |(M i j - N i j) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |M i j - N i j| * |x j| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, (|M i j| + |N i j|) * |x j| := by
          gcongr with j _
          calc |M i j - N i j| = |M i j + (-(N i j))| := by ring_nf
            _ ≤ |M i j| + |-(N i j)| := abs_add_le _ _
            _ = |M i j| + |N i j| := by rw [abs_neg]
  have hM_bound : ∑ j : Fin n, |M i j| * |x_hat (k + 1) j| ≤
      θ_x * ∑ j : Fin n, |M i j| * |x j| :=
    calc ∑ j, |M i j| * |x_hat (k + 1) j|
        ≤ ∑ j, |M i j| * (θ_x * |x j|) := by
          gcongr with j _; exact hx_bound _ _
      _ = θ_x * ∑ j, |M i j| * |x j| := by
          rw [Finset.mul_sum]; congr 1; ext j; ring
  have hN_bound : ∑ j : Fin n, |N i j| * |x_hat k j| ≤
      θ_x * ∑ j : Fin n, |N i j| * |x j| :=
    calc ∑ j, |N i j| * |x_hat k j|
        ≤ ∑ j, |N i j| * (θ_x * |x j|) := by
          gcongr with j _; exact hx_bound _ _
      _ = θ_x * ∑ j, |N i j| * |x j| := by
          rw [Finset.mul_sum]; congr 1; ext j; ring
  have hSum : ∑ j : Fin n, |M i j| * |x_hat (k + 1) j| +
      ∑ j : Fin n, |N i j| * |x_hat k j| + |b i| ≤
      (1 + θ_x) * ∑ j : Fin n, (|M i j| + |N i j|) * |x j| := by
    have split_sum : ∑ j : Fin n, (|M i j| + |N i j|) * |x j| =
        ∑ j : Fin n, |M i j| * |x j| + ∑ j : Fin n, |N i j| * |x j| := by
      rw [← Finset.sum_add_distrib]; congr 1; ext j; ring
    rw [split_sum]; nlinarith
  calc |ξ k i|
      ≤ cn_u * (∑ j, |M i j| * |x_hat (k + 1) j| +
                ∑ j, |N i j| * |x_hat k j| + |b i|) := hL
    _ ≤ cn_u * ((1 + θ_x) * ∑ j, (|M i j| + |N i j|) * |x j|) := by
        apply mul_le_mul_of_nonneg_left hSum hcn
    _ = cn_u * (1 + θ_x) * ∑ j, (|M i j| + |N i j|) * |x j| := by ring

/-- Higham, 2nd ed., Chapter 17, equations (17.2), (17.7), and (17.29):
    normwise simplification of the local-error model using the iterate-growth
    bound `||xhat_k||_∞ <= gamma_x ||x||_∞`. -/
theorem local_error_normwise_simplified (n : ℕ)
    (M N : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (cn_u gamma_x : ℝ) (hcn : 0 ≤ cn_u) (hgamma : 0 ≤ gamma_x)
    (hx_bound : NormwiseIterateGrowthBound n x x_hat gamma_x)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u) :
    ∀ k, infNormVec (ξ k) ≤
      cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x := by
  intro k
  apply infNormVec_le_of_abs_le
  · intro i
    have hL := hLocal k i
    have hMrow :
        ∑ j : Fin n, |M i j| * |x_hat (k + 1) j| ≤
          infNorm M * (gamma_x * infNormVec x) := by
      calc
        ∑ j : Fin n, |M i j| * |x_hat (k + 1) j|
            ≤ ∑ j : Fin n, |M i j| * infNormVec (x_hat (k + 1)) := by
              apply Finset.sum_le_sum
              intro j _hj
              exact mul_le_mul_of_nonneg_left
                (abs_le_infNormVec (x_hat (k + 1)) j) (abs_nonneg _)
        _ = (∑ j : Fin n, |M i j|) * infNormVec (x_hat (k + 1)) := by
              rw [Finset.sum_mul]
        _ ≤ infNorm M * infNormVec (x_hat (k + 1)) := by
              exact mul_le_mul_of_nonneg_right
                (row_sum_le_infNorm M i) (infNormVec_nonneg _)
        _ ≤ infNorm M * (gamma_x * infNormVec x) := by
              exact mul_le_mul_of_nonneg_left
                (hx_bound (k + 1)) (infNorm_nonneg M)
    have hNrow :
        ∑ j : Fin n, |N i j| * |x_hat k j| ≤
          infNorm N * (gamma_x * infNormVec x) := by
      calc
        ∑ j : Fin n, |N i j| * |x_hat k j|
            ≤ ∑ j : Fin n, |N i j| * infNormVec (x_hat k) := by
              apply Finset.sum_le_sum
              intro j _hj
              exact mul_le_mul_of_nonneg_left
                (abs_le_infNormVec (x_hat k) j) (abs_nonneg _)
        _ = (∑ j : Fin n, |N i j|) * infNormVec (x_hat k) := by
              rw [Finset.sum_mul]
        _ ≤ infNorm N * infNormVec (x_hat k) := by
              exact mul_le_mul_of_nonneg_right
                (row_sum_le_infNorm N i) (infNormVec_nonneg _)
        _ ≤ infNorm N * (gamma_x * infNormVec x) := by
              exact mul_le_mul_of_nonneg_left
                (hx_bound k) (infNorm_nonneg N)
    have hMexact :
        ∑ j : Fin n, |M i j| * |x j| ≤ infNorm M * infNormVec x := by
      calc
        ∑ j : Fin n, |M i j| * |x j|
            ≤ ∑ j : Fin n, |M i j| * infNormVec x := by
              apply Finset.sum_le_sum
              intro j _hj
              exact mul_le_mul_of_nonneg_left (abs_le_infNormVec x j) (abs_nonneg _)
        _ = (∑ j : Fin n, |M i j|) * infNormVec x := by
              rw [Finset.sum_mul]
        _ ≤ infNorm M * infNormVec x := by
              exact mul_le_mul_of_nonneg_right
                (row_sum_le_infNorm M i) (infNormVec_nonneg x)
    have hNexact :
        ∑ j : Fin n, |N i j| * |x j| ≤ infNorm N * infNormVec x := by
      calc
        ∑ j : Fin n, |N i j| * |x j|
            ≤ ∑ j : Fin n, |N i j| * infNormVec x := by
              apply Finset.sum_le_sum
              intro j _hj
              exact mul_le_mul_of_nonneg_left (abs_le_infNormVec x j) (abs_nonneg _)
        _ = (∑ j : Fin n, |N i j|) * infNormVec x := by
              rw [Finset.sum_mul]
        _ ≤ infNorm N * infNormVec x := by
              exact mul_le_mul_of_nonneg_right
                (row_sum_le_infNorm N i) (infNormVec_nonneg x)
    have hb :
        |b i| ≤ (infNorm M + infNorm N) * infNormVec x := by
      calc
        |b i| = |∑ j : Fin n, (M i j - N i j) * x j| := by
            rw [hAx]
        _ ≤ ∑ j : Fin n, |(M i j - N i j) * x j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |M i j - N i j| * |x j| := by
            apply Finset.sum_congr rfl
            intro j _hj
            exact abs_mul _ _
        _ ≤ ∑ j : Fin n, (|M i j| + |N i j|) * |x j| := by
            apply Finset.sum_le_sum
            intro j _hj
            exact mul_le_mul_of_nonneg_right
              (by
                calc
                  |M i j - N i j| = |M i j + (-N i j)| := by ring_nf
                  _ ≤ |M i j| + |(-N i j)| := abs_add_le _ _
                  _ = |M i j| + |N i j| := by rw [abs_neg])
              (abs_nonneg _)
        _ = ∑ j : Fin n, |M i j| * |x j| +
              ∑ j : Fin n, |N i j| * |x j| := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
        _ ≤ infNorm M * infNormVec x + infNorm N * infNormVec x := by
            exact add_le_add hMexact hNexact
        _ = (infNorm M + infNorm N) * infNormVec x := by ring
    have hinside :
        ∑ j : Fin n, |M i j| * |x_hat (k + 1) j| +
          ∑ j : Fin n, |N i j| * |x_hat k j| + |b i| ≤
        (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x := by
      nlinarith [hMrow, hNrow, hb, hgamma,
        infNorm_nonneg M, infNorm_nonneg N, infNormVec_nonneg x]
    calc
      |ξ k i| ≤ cn_u *
          (∑ j : Fin n, |M i j| * |x_hat (k + 1) j| +
            ∑ j : Fin n, |N i j| * |x_hat k j| + |b i|) := hL
      _ ≤ cn_u * ((1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x) := by
          exact mul_le_mul_of_nonneg_left hinside hcn
      _ = cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x := by
          ring
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hcn (by linarith))
        (add_nonneg (infNorm_nonneg M) (infNorm_nonneg N)))
      (infNormVec_nonneg x)

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), normwise
    surface instantiated from the source local-error model (17.2) and
    `gamma_x` iterate-growth hypothesis (17.7). -/
theorem singularErrorSourceTerm_norm_bound_of_local_error (n : ℕ) (hn : 0 < n)
    (G E M_inv M N : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i)
    (x_hat ξ : ℕ → Fin n → ℝ) (cn_u gamma_x : ℝ)
    (hcn : 0 ≤ cn_u) (hgamma : 0 ≤ gamma_x)
    (hx_bound : NormwiseIterateGrowthBound n x x_hat gamma_x)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u)
    (m : ℕ) :
    infNormVec (singularErrorSourceTerm n G E M_inv ξ m) ≤
      cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x *
        singularErrorSourceNormSum n G E M_inv m := by
  let μ := cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x
  have hμ : 0 ≤ μ := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hcn (by linarith))
        (add_nonneg (infNorm_nonneg M) (infNorm_nonneg N)))
      (infNormVec_nonneg x)
  have hξ :
      ∀ t : ℕ, infNormVec (ξ t) ≤ μ := by
    simpa [μ] using
      local_error_normwise_simplified n M N b x hAx x_hat ξ
        cn_u gamma_x hcn hgamma hx_bound hLocal
  simpa [μ] using
    singularErrorSourceTerm_norm_bound n hn G E M_inv ξ μ hμ hξ m

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), instantiated
    componentwise surface: the displayed bound for `S_m` follows from the
    source local-error model (17.2), the exact equation `Mx-Nx=b`, and the
    componentwise iterate-growth hypothesis from (17.9). -/
theorem singularErrorSourceTerm_componentwise_bound_of_local_error (n : ℕ)
    (G E M_inv M N : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i)
    (x_hat ξ : ℕ → Fin n → ℝ) (cn_u theta_x : ℝ)
    (hcn : 0 ≤ cn_u) (hθ : 0 ≤ theta_x)
    (hx_bound : ComponentwiseIterateGrowthBound n x x_hat theta_x)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u)
    (m : ℕ) :
    ∀ i, |singularErrorSourceTerm n G E M_inv ξ m i| ≤
      singularErrorSourceComponentBound n G E M_inv M N x cn_u theta_x m i := by
  have hξ :
      ∀ (t : ℕ) (j : Fin n),
        |ξ t j| ≤ cn_u * (1 + theta_x) *
          stationaryLocalErrorSourceVector n M N x j := by
    intro t j
    simpa [stationaryLocalErrorSourceVector] using
      local_error_simplified n M N b x hAx x_hat ξ cn_u theta_x
        hcn hθ hx_bound hLocal t j
  exact singularErrorSourceTerm_componentwise_bound
    n G E M_inv M N x ξ cn_u theta_x hξ m

-- ============================================================
-- §17.2  c(A) constant and main bound (eqs 17.12–17.13)
-- ============================================================

/-- Partial sum bound (eq 17.12): ∑_{k=0}^m |G^k M⁻¹|_{ij} ≤ cA · |A⁻¹_{ij}|. -/
def PartialSumBound (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ)
    (cA : ℝ) (m : ℕ) : Prop :=
  ∀ i j, ∑ k ∈ Finset.range (m + 1),
    ∑ l : Fin n, |matPow n G k i l| * |M_inv l j| ≤ cA * |A_inv i j|

-- ============================================================
-- §17.2.1  Jacobi specialization
-- ============================================================

/-- **Eq. 17.16 (Jacobi)**: |M| + |N| = |A| for M = diag(A), N = diag(A) − A. -/
theorem jacobi_splitting_abs (n : ℕ) (A : Fin n → Fin n → ℝ)
    (M N : Fin n → Fin n → ℝ)
    (hM : ∀ i j, M i j = if i = j then A i i else 0)
    (hN : ∀ i j, N i j = M i j - A i j) :
    ∀ i j, |M i j| + |N i j| = |A i j| := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hM i i, if_pos rfl, hN i i, hM i i, if_pos rfl, sub_self, abs_zero, add_zero]
  · rw [hM i j, if_neg hij, hN i j, hM i j, if_neg hij, zero_sub, abs_zero, zero_add, abs_neg]

-- ============================================================
-- §17.2.2  SOR specialization
-- ============================================================

/-- **Eq. 17.17 (SOR)**: |M| + |N| ≤ f(ω)|A| where f(ω) = (1+|1−ω|)/ω. -/
theorem sor_splitting_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (ω : ℝ) (hω_pos : 0 < ω)
    (D L U : Fin n → Fin n → ℝ)
    (hDecomp : ∀ i j, A i j = D i j + L i j + U i j)
    (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, j.val ≥ i.val → L i j = 0)
    (hU : ∀ i j, j.val ≤ i.val → U i j = 0)
    (M_sor N_sor : Fin n → Fin n → ℝ)
    (hM : ∀ i j, M_sor i j = (1 / ω) * (D i j + ω * L i j))
    (hN : ∀ i j, N_sor i j = (1 / ω) * ((1 - ω) * D i j - ω * U i j)) :
    ∀ i j, |M_sor i j| + |N_sor i j| ≤ ((1 + |1 - ω|) / ω) * |A i j| := by
  have hω_ne : ω ≠ 0 := ne_of_gt hω_pos
  have hfω : 1 ≤ (1 + |1 - ω|) / ω := by
    rw [le_div_iff₀ hω_pos]
    by_cases h : ω ≤ 1
    · have : |1 - ω| = 1 - ω := abs_of_nonneg (by linarith)
      nlinarith
    · push_neg at h
      have h1 : (1 : ℝ) - ω < 0 := by linarith
      have : |1 - ω| = -(1 - ω) := abs_of_neg h1
      linarith
  intro i j
  by_cases hij : i = j
  · -- Diagonal case: L_{ii} = U_{ii} = 0
    have hLii := hL i i (le_refl _)
    have hUii := hU i i (le_refl _)
    have hAii : A i i = D i i := by
      have := hDecomp i i; rw [hLii, hUii] at this; linarith
    subst hij
    have hMval : M_sor i i = D i i / ω := by
      rw [hM, hLii, mul_zero, add_zero]; field_simp
    have hNval : N_sor i i = (1 - ω) * D i i / ω := by
      rw [hN, hUii, mul_zero, sub_zero]; field_simp
    rw [hMval, hNval, ← hAii]
    rw [abs_div, abs_div, abs_mul, ← add_div, abs_of_pos hω_pos, div_mul_eq_mul_div]
    ring_nf; rfl
  · -- Off-diagonal: D_{ij} = 0
    have hDij := hD i j hij
    have hMval : M_sor i j = L i j := by
      rw [hM, hDij, zero_add]; field_simp
    have hNval : N_sor i j = -(U i j) := by
      rw [hN, hDij, mul_zero, zero_sub]; field_simp
    rw [hMval, hNval, abs_neg]
    have hAij : A i j = L i j + U i j := by
      have := hDecomp i j; rw [hDij] at this; linarith
    by_cases hlj : j.val < i.val
    · have hUij := hU i j (le_of_lt hlj)
      rw [hUij, abs_zero, add_zero, hAij, hUij, add_zero]
      exact le_mul_of_one_le_left (abs_nonneg _) hfω
    · push_neg at hlj
      have hji : i.val < j.val := by
        rcases hlj.eq_or_lt with heq | hlt
        · exact absurd (Fin.ext heq.symm) (Ne.symm hij)
        · exact hlt
      have hLij := hL i j (le_of_lt hji)
      rw [hLij, abs_zero, zero_add, hAij, hLij, zero_add]
      exact le_mul_of_one_le_left (abs_nonneg _) hfω

-- ============================================================
-- §17.3  Backward error — residual identity and sigma bound
-- ============================================================

/-- The residual r_k = b − Ax̂_k equals A(x − x̂_k). -/
theorem residual_eq_A_error (n : ℕ) (A : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : Fin n → ℝ) :
    ∀ i, b i - ∑ j : Fin n, A i j * x_hat j =
      ∑ j : Fin n, A i j * (x j - x_hat j) := by
  intro i
  rw [← hAx i, ← Finset.sum_sub_distrib]
  congr 1; ext j; ring

/-- Geometric series partial sum bound: ∑_{k=0}^m q^k ≤ 1/(1-q) for 0 ≤ q < 1. -/
private theorem geom_partial_sum_le (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), q ^ k ≤ 1 / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  rw [le_div_iff₀ hq1']
  calc (∑ k ∈ Finset.range (m + 1), q ^ k) * (1 - q)
      = ∑ k ∈ Finset.range (m + 1), (q ^ k - q ^ (k + 1)) := by
        rw [Finset.sum_mul]; congr 1; ext k; ring
    _ = 1 - q ^ (m + 1) := by
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ]; linarith
    _ ≤ 1 := by linarith [pow_nonneg hq (m + 1)]

/-- **σ bound** (§17.3): ∑_{k=0}^m ‖H^k(I−H)‖∞ ≤ ‖I−H‖∞/(1−q) when ‖H‖∞ ≤ q < 1. -/
theorem sigma_bound (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hH : infNorm H ≤ q) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      infNorm (matMul n (matPow n H k) (matSub_id n H)) ≤
    infNorm (matSub_id n H) / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  calc ∑ k ∈ Finset.range (m + 1),
        infNorm (matMul n (matPow n H k) (matSub_id n H))
      ≤ ∑ k ∈ Finset.range (m + 1),
        (q ^ k * infNorm (matSub_id n H)) := by
        gcongr with k _
        calc infNorm (matMul n (matPow n H k) (matSub_id n H))
            ≤ infNorm (matPow n H k) * infNorm (matSub_id n H) :=
              infNorm_matMul_le hn _ _
          _ ≤ q ^ k * infNorm (matSub_id n H) := by
              apply mul_le_mul_of_nonneg_right _ (infNorm_nonneg _)
              exact (infNorm_matPow_le hn H k).trans (pow_le_pow_left₀ (infNorm_nonneg H) hH k)
    _ = (∑ k ∈ Finset.range (m + 1), q ^ k) * infNorm (matSub_id n H) := by
        rw [Finset.sum_mul]
    _ ≤ (1 / (1 - q)) * infNorm (matSub_id n H) := by
        apply mul_le_mul_of_nonneg_right (geom_partial_sum_le q hq hq1 m) (infNorm_nonneg _)
    _ = infNorm (matSub_id n H) / (1 - q) := by
        rw [one_div, mul_comm, div_eq_mul_inv]

/-- Finite source-sigma matrix from Higham, 2nd ed., Chapter 17, Section 17.3:
    the partial matrix `sum_{k=0}^m |H^k(I-H)|` underlying the infinite
    sigma in the paragraph before equation (17.20). -/
noncomputable def finiteResidualSigmaMatrix (n : ℕ)
    (H : Fin n → Fin n → ℝ) (m : ℕ) : Fin n → Fin n → ℝ :=
  fun i j =>
    ∑ k ∈ Finset.range (m + 1),
      |matMul n (matPow n H k) (matSub_id n H) i j|

/-- Finite source-sigma scalar `||sum_{k=0}^m |H^k(I-H)||_infty`. -/
noncomputable def finiteResidualSigma (n : ℕ)
    (H : Fin n → Fin n → ℝ) (m : ℕ) : ℝ :=
  infNorm (finiteResidualSigmaMatrix n H m)

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20):
    entrywise `tsum` matrix for the source residual sigma
    `sum_{k >= 0} |H^k(I-H)|`.  Convergence is intentionally not hidden in the
    definition; use the `HasSum` wrapper below when a concrete convergence
    certificate is available. -/
noncomputable def residualSigmaTsumMatrix (n : ℕ)
    (H : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    ∑' k : ℕ, |matMul n (matPow n H k) (matSub_id n H) i j|

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20):
    scalar infinity-norm version of the entrywise `tsum` residual sigma. -/
noncomputable def residualSigmaTsum (n : ℕ)
    (H : Fin n → Fin n → ℝ) : ℝ :=
  infNorm (residualSigmaTsumMatrix n H)

/-- Entrywise unfolding of the literal `tsum` residual-sigma matrix. -/
theorem residualSigmaTsumMatrix_apply (n : ℕ)
    (H : Fin n → Fin n → ℝ) (i j : Fin n) :
    residualSigmaTsumMatrix n H i j =
      ∑' k : ℕ, |matMul n (matPow n H k) (matSub_id n H) i j| := by
  rfl

/-- If each entrywise source residual-sigma series has sum `S i j`, then the
    `tsum` matrix is exactly `S`. -/
theorem residualSigmaTsumMatrix_eq_of_hasSum (n : ℕ)
    (H S : Fin n → Fin n → ℝ)
    (hsum : ∀ i j,
      HasSum (fun k : ℕ => |matMul n (matPow n H k) (matSub_id n H) i j|)
        (S i j)) :
    residualSigmaTsumMatrix n H = S := by
  ext i j
  unfold residualSigmaTsumMatrix
  exact (hsum i j).tsum_eq

/-- Norm-level form of `residualSigmaTsumMatrix_eq_of_hasSum`. -/
theorem residualSigmaTsum_eq_infNorm_of_hasSum (n : ℕ)
    (H S : Fin n → Fin n → ℝ)
    (hsum : ∀ i j,
      HasSum (fun k : ℕ => |matMul n (matPow n H k) (matSub_id n H) i j|)
        (S i j)) :
    residualSigmaTsum n H = infNorm S := by
  unfold residualSigmaTsum
  rw [residualSigmaTsumMatrix_eq_of_hasSum n H S hsum]

/-- A row-sum certificate bounds the literal `tsum` residual sigma. -/
theorem residualSigmaTsum_le_of_row_sum_le (n : ℕ)
    (H : Fin n → Fin n → ℝ) {sigma : ℝ}
    (hrows : ∀ i : Fin n,
      ∑ j : Fin n, |residualSigmaTsumMatrix n H i j| ≤ sigma)
    (hsigma : 0 ≤ sigma) :
    residualSigmaTsum n H ≤ sigma := by
  unfold residualSigmaTsum
  exact infNorm_le_of_row_sum_le (residualSigmaTsumMatrix n H) hrows hsigma

/-- Higham, 2nd ed., Chapter 17, Section 17.3:
    candidate finite partial norms for the source residual sigma.  This is the
    `sSup`-based wrapper around the finite matrices `sum_{k=0}^m |H^k(I-H)|`;
    it does not assert a separate `tsum` representation. -/
def ResidualSigmaValues (n : ℕ) (H : Fin n → Fin n → ℝ) : Set ℝ :=
  {sigma | ∃ m : ℕ, sigma = finiteResidualSigma n H m}

/-- Higham, 2nd ed., Chapter 17, Section 17.3:
    supremum of the finite source-sigma partial norms. -/
noncomputable def residualSigmaSup (n : ℕ)
    (H : Fin n → Fin n → ℝ) : ℝ :=
  sSup (ResidualSigmaValues n H)

/-- A uniform finite-partial bound also bounds the supremum model of the source
    residual sigma. -/
theorem residualSigmaSup_le_of_finiteResidualSigma_le (n : ℕ)
    (H : Fin n → Fin n → ℝ) (sigma : ℝ)
    (hbound : ∀ m : ℕ, finiteResidualSigma n H m ≤ sigma) :
    residualSigmaSup n H ≤ sigma := by
  unfold residualSigmaSup
  apply csSup_le
  · exact ⟨finiteResidualSigma n H 0, ⟨0, rfl⟩⟩
  · intro y hy
    rcases hy with ⟨m, rfl⟩
    exact hbound m

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20):
    finite maximum `max_i |1 - lambda_i| / (1 - |lambda_i|)` appearing in the
    diagonalizable bound for the source residual sigma. -/
noncomputable def diagonalResidualRatioMax (n : ℕ)
    (J : Fin n → Fin n → ℝ) (hn : 0 < n) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin n))
    (by exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
    (fun i => |1 - J i i| / (1 - |J i i|))

/-- Each eigenvalue ratio in Higham (17.20) is bounded by the displayed finite
    maximum. -/
theorem diagonalResidualRatio_le_max (n : ℕ)
    (J : Fin n → Fin n → ℝ) (hn : 0 < n) (i : Fin n) :
    |1 - J i i| / (1 - |J i i|) ≤ diagonalResidualRatioMax n J hn := by
  unfold diagonalResidualRatioMax
  exact Finset.le_sup' (fun i => |1 - J i i| / (1 - |J i i|)) (Finset.mem_univ i)

/-- The finite maximum in Higham (17.20) is nonnegative when all diagonal
    eigenvalue moduli are strictly below one. -/
theorem diagonalResidualRatioMax_nonneg (n : ℕ)
    (J : Fin n → Fin n → ℝ) (hn : 0 < n)
    (hLam : ∀ i : Fin n, |J i i| < 1) :
    0 ≤ diagonalResidualRatioMax n J hn := by
  let i0 : Fin n := ⟨0, hn⟩
  have hden : 0 ≤ 1 - |J i0 i0| := by
    linarith [hLam i0]
  have hratio : 0 ≤ |1 - J i0 i0| / (1 - |J i0 i0|) :=
    div_nonneg (abs_nonneg _) hden
  exact hratio.trans (diagonalResidualRatio_le_max n J hn i0)

private theorem residual_geometric_partial_le_ratio (lam : ℝ)
    (hLam : |lam| < 1) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), |lam| ^ k * |1 - lam| ≤
      |1 - lam| / (1 - |lam|) := by
  have hden : 0 < 1 - |lam| := by linarith
  calc
    ∑ k ∈ Finset.range (m + 1), |lam| ^ k * |1 - lam|
        = (∑ k ∈ Finset.range (m + 1), |lam| ^ k) * |1 - lam| := by
            rw [Finset.sum_mul]
    _ ≤ (1 / (1 - |lam|)) * |1 - lam| := by
            exact mul_le_mul_of_nonneg_right
              (geom_partial_sum_le |lam| (abs_nonneg lam) hLam m) (abs_nonneg _)
    _ = |1 - lam| / (1 - |lam|) := by
            rw [one_div, div_eq_mul_inv]
            ring

private theorem residual_term_entry_abs_le_of_real_diagonalization (n : ℕ)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (k : ℕ) (i j : Fin n) :
    |matMul n (matPow n H k) (matSub_id n H) i j| ≤
      ∑ a : Fin n, |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j| := by
  have hterm :
      matMul n (matPow n H k) (matSub_id n H) i j =
        matPow n H k i j - matPow n H (k + 1) i j := by
    unfold matMul matSub_id
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    have hid :
        (∑ l : Fin n, matPow n H k i l * idMatrix n l j) =
          matPow n H k i j := by
      unfold idMatrix
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hmul :
        (∑ l : Fin n, matPow n H k i l * H l j) =
          matPow n H (k + 1) i j := by
      rw [matPow_succ_right n H k]
      rfl
    rw [hid, hmul]
  have hpow_entry :
      ∀ p (r c : Fin n),
        matPow n H p r c =
          ∑ a : Fin n, X r a * (J a a ^ p * X_inv a c) := by
    intro p r c
    have hpow := congrFun
      (congrFun (matPow_similarity n H X X_inv J hXr hXl hsim p) r) c
    rw [hpow]
    unfold matMul
    apply Finset.sum_congr rfl
    intro a _ha
    congr 1
    have hinner :
        (∑ b : Fin n, matPow n J p a b * X_inv b c) =
          J a a ^ p * X_inv a c := by
      rw [Finset.sum_eq_single a]
      · rw [matPow_diagonal n J hdiag p a a, if_pos rfl]
      · intro b _hb hba
        rw [matPow_diagonal n J hdiag p a b, if_neg (Ne.symm hba), zero_mul]
      · intro hnot
        exact absurd (Finset.mem_univ a) hnot
    exact hinner
  have hsource :
      matMul n (matPow n H k) (matSub_id n H) i j =
        ∑ a : Fin n, X i a * (J a a ^ k * (1 - J a a) * X_inv a j) := by
    rw [hterm, hpow_entry k i j, hpow_entry (k + 1) i j]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [pow_succ]
    ring
  rw [hsource]
  calc
    |∑ a : Fin n, X i a * (J a a ^ k * (1 - J a a) * X_inv a j)|
        ≤ ∑ a : Fin n, |X i a * (J a a ^ k * (1 - J a a) * X_inv a j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : Fin n,
          |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j| := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [abs_mul, abs_mul, abs_mul, abs_pow]
          ring

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), finite
    diagonalization-certificate form: if `H = X J X^{-1}` with diagonal `J`
    and `|lambda_i| < 1`, then every finite source-sigma partial matrix is
    bounded by `kappa_infty(X) * max_i |1-lambda_i|/(1-|lambda_i|)`.

    The theorem takes the displayed maximum as an explicit scalar upper bound
    `sigmaDiag`; the literal infinite-series sigma is still a later wrapper. -/
theorem finiteResidualSigma_le_diagonalizable_bound (n : ℕ) (_hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (sigmaDiag : ℝ) (hsigma : 0 ≤ sigmaDiag)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (hratio : ∀ i : Fin n, |1 - J i i| / (1 - |J i i|) ≤ sigmaDiag)
    (m : ℕ) :
    finiteResidualSigma n H m ≤ (infNorm X * infNorm X_inv) * sigmaDiag := by
  unfold finiteResidualSigma
  apply infNorm_le_of_row_sum_le
  · intro i
    have hrowEntry_nonneg :
        ∀ j : Fin n, 0 ≤ finiteResidualSigmaMatrix n H m i j := by
      intro j
      unfold finiteResidualSigmaMatrix
      exact Finset.sum_nonneg (fun k _hk => abs_nonneg _)
    calc
      ∑ j : Fin n, |finiteResidualSigmaMatrix n H m i j|
          = ∑ j : Fin n, finiteResidualSigmaMatrix n H m i j := by
              apply Finset.sum_congr rfl
              intro j _hj
              exact abs_of_nonneg (hrowEntry_nonneg j)
      _ = ∑ j : Fin n, ∑ k ∈ Finset.range (m + 1),
            |matMul n (matPow n H k) (matSub_id n H) i j| := by
              rfl
      _ ≤ ∑ j : Fin n, ∑ a : Fin n,
            |X i a| * sigmaDiag * |X_inv a j| := by
              apply Finset.sum_le_sum
              intro j _hj
              calc
                ∑ k ∈ Finset.range (m + 1),
                    |matMul n (matPow n H k) (matSub_id n H) i j|
                    ≤ ∑ k ∈ Finset.range (m + 1), ∑ a : Fin n,
                        |X i a| * (|J a a| ^ k * |1 - J a a|) *
                          |X_inv a j| := by
                        apply Finset.sum_le_sum
                        intro k _hk
                        exact residual_term_entry_abs_le_of_real_diagonalization
                          n H X X_inv J hXr hXl hsim hdiag k i j
                _ = ∑ a : Fin n, ∑ k ∈ Finset.range (m + 1),
                        |X i a| * (|J a a| ^ k * |1 - J a a|) *
                          |X_inv a j| := by
                        rw [Finset.sum_comm]
                _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := by
                        apply Finset.sum_le_sum
                        intro a _ha
                        have hgeom :
                            ∑ k ∈ Finset.range (m + 1),
                              |J a a| ^ k * |1 - J a a| ≤ sigmaDiag :=
                            (residual_geometric_partial_le_ratio (J a a)
                            (hLam a) m).trans (hratio a)
                        calc
                          ∑ k ∈ Finset.range (m + 1),
                              |X i a| * (|J a a| ^ k * |1 - J a a|) *
                                |X_inv a j|
                              = |X i a| *
                                  (∑ k ∈ Finset.range (m + 1),
                                    |J a a| ^ k * |1 - J a a|) *
                                  |X_inv a j| := by
                                  rw [Finset.mul_sum, Finset.sum_mul]
                          _ ≤ |X i a| * sigmaDiag * |X_inv a j| := by
                                  exact mul_le_mul_of_nonneg_right
                                    (mul_le_mul_of_nonneg_left hgeom (abs_nonneg _))
                                    (abs_nonneg _)
      _ = ∑ a : Fin n, |X i a| * sigmaDiag * (∑ j : Fin n, |X_inv a j|) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a _ha
              rw [← Finset.mul_sum]
      _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * infNorm X_inv := by
              apply Finset.sum_le_sum
              intro a _ha
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X_inv a)
                (mul_nonneg (abs_nonneg _) hsigma)
      _ = sigmaDiag * infNorm X_inv * (∑ a : Fin n, |X i a|) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _ha
              ring
      _ ≤ sigmaDiag * infNorm X_inv * infNorm X := by
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X i)
                (mul_nonneg hsigma (infNorm_nonneg _))
      _ = (infNorm X * infNorm X_inv) * sigmaDiag := by
              ring
  · exact mul_nonneg (mul_nonneg (infNorm_nonneg X) (infNorm_nonneg X_inv)) hsigma

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), finite
    maximum form: if `H = X J X^{-1}` with diagonal `J` and `|lambda_i| < 1`,
    then every finite source-sigma partial norm is bounded by
    `kappa_infty(X)` times the displayed maximum eigenvalue ratio. -/
theorem finiteResidualSigma_le_diagonalizable_max_bound (n : ℕ) (hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (m : ℕ) :
    finiteResidualSigma n H m ≤
      (infNorm X * infNorm X_inv) * diagonalResidualRatioMax n J hn := by
  exact finiteResidualSigma_le_diagonalizable_bound n hn H X X_inv J
    hXr hXl hsim hdiag (diagonalResidualRatioMax n J hn)
    (diagonalResidualRatioMax_nonneg n J hn hLam) hLam
    (diagonalResidualRatio_le_max n J hn) m

private theorem residualSigmaTsum_entry_le_of_real_diagonalization (n : ℕ)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (sigmaDiag : ℝ)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (hratio : ∀ i : Fin n, |1 - J i i| / (1 - |J i i|) ≤ sigmaDiag)
    (i j : Fin n) :
    residualSigmaTsumMatrix n H i j ≤
      ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := by
  let f : ℕ → ℝ :=
    fun k => |matMul n (matPow n H k) (matSub_id n H) i j|
  let g : ℕ → ℝ :=
    fun k => ∑ a : Fin n,
      |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j|
  have hfg : ∀ k : ℕ, f k ≤ g k := by
    intro k
    simpa [f, g] using
      residual_term_entry_abs_le_of_real_diagonalization
        n H X X_inv J hXr hXl hsim hdiag k i j
  have hg_a : ∀ a : Fin n,
      Summable (fun k : ℕ =>
        |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j|) := by
    intro a
    have hgeom : Summable (fun k : ℕ => |J a a| ^ k) :=
      summable_geometric_of_lt_one (abs_nonneg _) (hLam a)
    have hscaled :
        Summable (fun k : ℕ => |J a a| ^ k * |1 - J a a|) :=
      Summable.mul_right _ hgeom
    have hleft :
        Summable (fun k : ℕ =>
          |X i a| * (|J a a| ^ k * |1 - J a a|)) :=
      Summable.mul_left _ hscaled
    exact Summable.mul_right _ hleft
  have hg : Summable g := by
    dsimp [g]
    simpa using
      (summable_sum (s := Finset.univ)
        (fun a _ha => hg_a a))
  have hf : Summable f :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hfg hg
  have hle_tsum : (∑' k : ℕ, f k) ≤ ∑' k : ℕ, g k :=
    Summable.tsum_le_tsum hfg hf hg
  have hg_tsum_eq :
      (∑' k : ℕ, g k) =
        ∑ a : Fin n, ∑' k : ℕ,
          |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j| := by
    dsimp [g]
    simpa using
      (Summable.tsum_finsetSum (s := Finset.univ)
        (fun a _ha => hg_a a))
  have hg_tsum_le :
      (∑' k : ℕ, g k) ≤
        ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := by
    rw [hg_tsum_eq]
    apply Finset.sum_le_sum
    intro a _ha
    have hgeom_tsum :
        (∑' k : ℕ, |J a a| ^ k * |1 - J a a|) =
          |1 - J a a| / (1 - |J a a|) := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one (abs_nonneg _) (hLam a)]
      rw [div_eq_mul_inv, mul_comm]
    have hweighted_tsum :
        (∑' k : ℕ,
          |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j|) =
          |X i a| * (|1 - J a a| / (1 - |J a a|)) * |X_inv a j| := by
      rw [tsum_mul_right, tsum_mul_left, hgeom_tsum]
    rw [hweighted_tsum]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hratio a) (abs_nonneg _))
      (abs_nonneg _)
  calc
    residualSigmaTsumMatrix n H i j = ∑' k : ℕ, f k := by rfl
    _ ≤ ∑' k : ℕ, g k := hle_tsum
    _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := hg_tsum_le

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), literal
    `tsum` diagonalization-certificate form: if `H = X J X^{-1}` with diagonal
    `J` and `|lambda_i| < 1`, then the entrywise infinite source residual sigma
    is bounded by `kappa_infty(X) * sigmaDiag`. -/
theorem residualSigmaTsum_le_diagonalizable_bound (n : ℕ) (_hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (sigmaDiag : ℝ) (hsigma : 0 ≤ sigmaDiag)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (hratio : ∀ i : Fin n, |1 - J i i| / (1 - |J i i|) ≤ sigmaDiag) :
    residualSigmaTsum n H ≤ (infNorm X * infNorm X_inv) * sigmaDiag := by
  apply residualSigmaTsum_le_of_row_sum_le
  · intro i
    have hentry_nonneg :
        ∀ j : Fin n, 0 ≤ residualSigmaTsumMatrix n H i j := by
      intro j
      unfold residualSigmaTsumMatrix
      exact tsum_nonneg (fun k => abs_nonneg _)
    calc
      ∑ j : Fin n, |residualSigmaTsumMatrix n H i j|
          = ∑ j : Fin n, residualSigmaTsumMatrix n H i j := by
              apply Finset.sum_congr rfl
              intro j _hj
              exact abs_of_nonneg (hentry_nonneg j)
      _ ≤ ∑ j : Fin n, ∑ a : Fin n,
            |X i a| * sigmaDiag * |X_inv a j| := by
              apply Finset.sum_le_sum
              intro j _hj
              exact residualSigmaTsum_entry_le_of_real_diagonalization
                n H X X_inv J hXr hXl hsim hdiag sigmaDiag
                hLam hratio i j
      _ = ∑ a : Fin n, |X i a| * sigmaDiag *
            (∑ j : Fin n, |X_inv a j|) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a _ha
              rw [← Finset.mul_sum]
      _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * infNorm X_inv := by
              apply Finset.sum_le_sum
              intro a _ha
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X_inv a)
                (mul_nonneg (abs_nonneg _) hsigma)
      _ = sigmaDiag * infNorm X_inv * (∑ a : Fin n, |X i a|) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _ha
              ring
      _ ≤ sigmaDiag * infNorm X_inv * infNorm X := by
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X i)
                (mul_nonneg hsigma (infNorm_nonneg _))
      _ = (infNorm X * infNorm X_inv) * sigmaDiag := by
              ring
  · exact mul_nonneg (mul_nonneg (infNorm_nonneg X) (infNorm_nonneg X_inv)) hsigma

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), literal
    `tsum` maximum form: the entrywise infinite source residual sigma is bounded
    by `kappa_infty(X)` times the displayed maximum eigenvalue ratio. -/
theorem residualSigmaTsum_le_diagonalizable_max_bound_direct (n : ℕ) (hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hLam : ∀ i : Fin n, |J i i| < 1) :
    residualSigmaTsum n H ≤
      (infNorm X * infNorm X_inv) * diagonalResidualRatioMax n J hn := by
  exact residualSigmaTsum_le_diagonalizable_bound n hn H X X_inv J
    hXr hXl hsim hdiag (diagonalResidualRatioMax n J hn)
    (diagonalResidualRatioMax_nonneg n J hn hLam) hLam
    (diagonalResidualRatio_le_max n J hn)

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), supremum
    wrapper: the supremum of all finite source-sigma partial norms is bounded by
    `kappa_infty(X)` times the displayed maximum eigenvalue ratio.  This is a
    source-facing infinite-sigma envelope, not a proof that an entrywise infinite
    matrix series has been constructed as a `tsum`. -/
theorem residualSigmaSup_le_diagonalizable_max_bound (n : ℕ) (hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hLam : ∀ i : Fin n, |J i i| < 1) :
    residualSigmaSup n H ≤
      (infNorm X * infNorm X_inv) * diagonalResidualRatioMax n J hn := by
  apply residualSigmaSup_le_of_finiteResidualSigma_le
  intro m
  exact finiteResidualSigma_le_diagonalizable_max_bound n hn H X X_inv J
    hXr hXl hsim hdiag hLam m

-- ============================================================
-- §17.3  Residual recurrence: r_{k+1} = Hr_k − (I−H)ξ_k
-- ============================================================

/-- AM⁻¹ = I − H: since A = M − N, AM⁻¹ = MM⁻¹ − NM⁻¹ = I − H. -/
theorem A_matMul_Minv_eq_sub (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv) :
    matMul n A M_inv = matSub_id n (dualIterMatrix n N M_inv) := by
  ext i j
  show ∑ k, A i k * M_inv k j = idMatrix n i j - ∑ k, N i k * M_inv k j
  simp_rw [hS.splitting, sub_mul, Finset.sum_sub_distrib]
  have hMM := hS.inv_right i j; unfold idMatrix at *; linarith

/-- **One-step residual recurrence** (eq 17.18 base case): r_{k+1} = Hr_k − (I−H)ξ_k.
    Obtained by left-multiplying e_{k+1} = Ge_k − M⁻¹ξ_k by A
    and using AG = HA, AM⁻¹ = I − H. -/
theorem one_step_residual (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) :
    ∀ k i, (b i - ∑ j, A i j * x_hat (k + 1) j) =
      matMulVec n (dualIterMatrix n N M_inv)
        (fun j => b j - ∑ l, A j l * x_hat k l) i -
      matMulVec n (matSub_id n (dualIterMatrix n N M_inv)) (ξ k) i := by
  intro k i
  -- r_{k+1,i} = ∑_j A_{ij}(x_j − x̂_{k+1,j})
  rw [residual_eq_A_error n A b x hAx (x_hat (k + 1)) i]
  -- Substitute one_step_error
  have hstep := one_step_error n A M N M_inv hS b x hAx x_hat ξ hIter k
  conv_lhs => arg 2; ext j; rw [hstep j, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · -- A·(G·e_k) = H·r_k  via  A(Gd) = (AG)d = (HA)d = H(Ad) = H·r_k
    show matMulVec n A (matMulVec n (iterMatrix n M_inv N)
        (fun l => x l - x_hat k l)) i =
      matMulVec n (dualIterMatrix n N M_inv)
        (fun j => b j - ∑ l, A j l * x_hat k l) i
    rw [← matMulVec_matMul, AG_eq_HA n A M N M_inv hS, matMulVec_matMul]
    suffices h : matMulVec n A (fun l => x l - x_hat k l) =
        fun j => b j - ∑ l, A j l * x_hat k l by rw [h]
    ext j; exact (residual_eq_A_error n A b x hAx (x_hat k) j).symm
  · -- A·(M⁻¹·ξ_k) = (I−H)·ξ_k  via  AM⁻¹ = I − H
    show matMulVec n A (matMulVec n M_inv (ξ k)) i =
      matMulVec n (matSub_id n (dualIterMatrix n N M_inv)) (ξ k) i
    rw [← matMulVec_matMul, A_matMul_Minv_eq_sub n A M N M_inv hS]

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.18):
    finite-sum residual recurrence
    `r_{m+1} = H^(m+1) r_0 - sum_{k=0}^m H^k (I-H) ξ_{m-k}`. -/
theorem residual_finite_sum (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ)
    (m : ℕ) :
    ∀ i, b i - ∑ j : Fin n, A i j * x_hat (m + 1) j =
      matMulVec n (matPow n (dualIterMatrix n N M_inv) (m + 1))
        (fun j => b j - ∑ l : Fin n, A j l * x_hat 0 l) i -
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n (dualIterMatrix n N M_inv) k)
          (matMulVec n (matSub_id n (dualIterMatrix n N M_inv))
            (ξ (m - k))) i := by
  intro i
  let H := dualIterMatrix n N M_inv
  let C := matSub_id n H
  let R : ℕ → Fin n → ℝ :=
    fun k j => b j - ∑ l : Fin n, A j l * x_hat k l
  have hsource :
      (∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n H k)
          (fun j => -matMulVec n C (ξ (m - k)) j) i) =
      - ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n H k)
          (matMulVec n C (ξ (m - k))) i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    unfold matMulVec
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hunroll := affine_recurrence_unroll n H
    (fun k j => -matMulVec n C (ξ k) j)
    R
    (by
      intro k j
      have hres := one_step_residual n A M N M_inv hS b x hAx x_hat ξ hIter k j
      simpa [R, H, C, sub_eq_add_neg] using hres)
    m i
  rw [hsource] at hunroll
  simpa [R, H, C, sub_eq_add_neg] using hunroll

/-- Finite sigma-form residual bound following from the closed residual
    recurrence: the propagated initial residual plus the finite sum of
    `||H^k(I-H)||∞ * ||ξ_{m-k}||∞` controls `||r_{m+1}||∞`. -/
theorem normwise_residual_sigma_finite_bound (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ)
    (m : ℕ) :
    infNormVec (fun i => b i - ∑ j : Fin n, A i j * x_hat (m + 1) j) ≤
      infNorm (matPow n (dualIterMatrix n N M_inv) (m + 1)) *
        infNormVec (fun i => b i - ∑ j : Fin n, A i j * x_hat 0 j) +
      ∑ k ∈ Finset.range (m + 1),
        infNorm (matMul n (matPow n (dualIterMatrix n N M_inv) k)
          (matSub_id n (dualIterMatrix n N M_inv))) *
        infNormVec (ξ (m - k)) := by
  let H := dualIterMatrix n N M_inv
  let C := matSub_id n H
  let r0 : Fin n → ℝ :=
    fun i => b i - ∑ j : Fin n, A i j * x_hat 0 j
  apply infNormVec_le_of_abs_le
  · intro i
    have hres := residual_finite_sum n A M N M_inv hS b x hAx x_hat ξ hIter m i
    have hlead :
        |matMulVec n (matPow n H (m + 1)) r0 i| ≤
          infNorm (matPow n H (m + 1)) * infNormVec r0 := by
      exact (abs_le_infNormVec (matMulVec n (matPow n H (m + 1)) r0) i).trans
        (infNormVec_matMulVec_le hn (matPow n H (m + 1)) r0)
    have hsum :
        |∑ k ∈ Finset.range (m + 1),
          matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i| ≤
        ∑ k ∈ Finset.range (m + 1),
          infNorm (matMul n (matPow n H k) C) * infNormVec (ξ (m - k)) := by
      calc
        |∑ k ∈ Finset.range (m + 1),
          matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i|
            ≤ ∑ k ∈ Finset.range (m + 1),
                |matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range (m + 1),
              infNorm (matMul n (matPow n H k) C) * infNormVec (ξ (m - k)) := by
            apply Finset.sum_le_sum
            intro k _hk
            calc
              |matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i|
                  = |matMulVec n (matMul n (matPow n H k) C)
                      (ξ (m - k)) i| := by
                    rw [matMulVec_matMul n (matPow n H k) C (ξ (m - k)) i]
              _ ≤ infNormVec
                    (matMulVec n (matMul n (matPow n H k) C) (ξ (m - k))) :=
                  abs_le_infNormVec _ i
              _ ≤ infNorm (matMul n (matPow n H k) C) *
                    infNormVec (ξ (m - k)) :=
                  infNormVec_matMulVec_le hn _ _
    calc
      |b i - ∑ j : Fin n, A i j * x_hat (m + 1) j|
          = |matMulVec n (matPow n H (m + 1)) r0 i -
              ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i| := by
              rw [hres]
      _ ≤ |matMulVec n (matPow n H (m + 1)) r0 i| +
            |∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i| :=
          (abs_add_le _ _).trans (by rw [abs_neg])
      _ ≤ infNorm (matPow n H (m + 1)) * infNormVec r0 +
            ∑ k ∈ Finset.range (m + 1),
              infNorm (matMul n (matPow n H k) C) *
                infNormVec (ξ (m - k)) :=
          add_le_add hlead hsum
  · exact add_nonneg
      (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))
      (Finset.sum_nonneg (fun k _hk =>
        mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _)))

-- ============================================================
-- §17.2  Normwise one-step bound and forward bound (eqs 17.5, 17.8)
-- ============================================================

/-- Normwise one-step error bound from `one_step_error`:
    ‖e_{k+1}‖∞ ≤ ‖G‖∞·‖e_k‖∞ + ‖M⁻¹‖∞·‖ξ_k‖∞. -/
theorem normwise_one_step_bound (n : ℕ) (_hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) (k : ℕ) :
    infNormVec (fun i => x i - x_hat (k + 1) i) ≤
      infNorm (iterMatrix n M_inv N) *
        infNormVec (fun i => x i - x_hat k i) +
      infNorm M_inv * infNormVec (ξ k) := by
  have hstep := one_step_error n A M N M_inv hS b x hAx x_hat ξ hIter k
  -- Suffices to show for each component i
  suffices h : ∀ i : Fin n, |x i - x_hat (k + 1) i| ≤
      infNorm (iterMatrix n M_inv N) *
        infNormVec (fun i => x i - x_hat k i) +
      infNorm M_inv * infNormVec (ξ k) by
    apply infNormVec_le_of_abs_le
    · exact h
    · exact add_nonneg
        (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))
        (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))
  intro i; rw [hstep i]
  -- |∑ G_{ij}(x_j - x̂_{k,j}) - ∑ M⁻¹_{ij}ξ_{k,j}| ≤ ‖G‖·‖e_k‖ + ‖M⁻¹‖·‖ξ_k‖
  -- Step 1: triangle inequality
  set a := ∑ j, iterMatrix n M_inv N i j * (x j - x_hat k j) with ha_def
  set b := ∑ j, M_inv i j * ξ k j with hb_def
  have htri : |a - b| ≤ |a| + |b| :=
    (abs_add_le a (-b)).trans (by rw [abs_neg])
  -- Step 2: bound each absolute sum
  have ha_bound : |a| ≤ ∑ j, |iterMatrix n M_inv N i j| * |x j - x_hat k j| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun j _ => le_of_eq (abs_mul _ _)))
  have hb_bound : |b| ≤ ∑ j, |M_inv i j| * |ξ k j| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun j _ => le_of_eq (abs_mul _ _)))
  -- Step 3: bound sums using infNormVec
  have ha2 : ∑ j : Fin n, |iterMatrix n M_inv N i j| * |x j - x_hat k j| ≤
      (∑ j, |iterMatrix n M_inv N i j|) *
        infNormVec (fun i => x i - x_hat k i) := by
    rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro j _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact abs_le_infNormVec (fun i => x i - x_hat k i) j
  have hb2 : ∑ j : Fin n, |M_inv i j| * |ξ k j| ≤
      (∑ j, |M_inv i j|) * infNormVec (ξ k) := by
    rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro j _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact abs_le_infNormVec (ξ k) j
  -- Combine
  calc |a - b| ≤ |a| + |b| := htri
    _ ≤ (∑ j, |iterMatrix n M_inv N i j|) *
          infNormVec (fun i => x i - x_hat k i) +
        (∑ j, |M_inv i j|) * infNormVec (ξ k) := by
        linarith [ha_bound.trans ha2, hb_bound.trans hb2]
    _ ≤ infNorm (iterMatrix n M_inv N) *
          infNormVec (fun i => x i - x_hat k i) +
        infNorm M_inv * infNormVec (ξ k) := by
        apply add_le_add <;>
          exact mul_le_mul_of_nonneg_right (row_sum_le_infNorm _ i)
            (infNormVec_nonneg _)

/-- **Eq. 17.8 (Normwise forward bound)**: ‖e_{m+1}‖∞ ≤ q^{m+1}·‖e₀‖∞ + μ·‖M⁻¹‖∞/(1−q)
    where q ≥ ‖G‖∞ and μ ≥ ‖ξ_k‖∞ for all k.  Proved by induction
    from `normwise_one_step_bound` using geometric contraction. -/
theorem normwise_forward_bound (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hG : infNorm (iterMatrix n M_inv N) ≤ q)
    (μ : ℝ) (hμ : 0 ≤ μ) (hξ_bound : ∀ k, infNormVec (ξ k) ≤ μ)
    (m : ℕ) :
    infNormVec (fun i => x i - x_hat (m + 1) i) ≤
      q ^ (m + 1) * infNormVec (fun i => x i - x_hat 0 i) +
      μ * infNorm M_inv / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  have hMn : 0 ≤ infNorm M_inv := infNorm_nonneg _
  have he₀ := infNormVec_nonneg (fun i => x i - x_hat 0 i)
  induction m with
  | zero =>
    have hone := normwise_one_step_bound n hn A M N M_inv hS b x hAx x_hat ξ hIter 0
    calc infNormVec (fun i => x i - x_hat 1 i)
        ≤ infNorm (iterMatrix n M_inv N) *
            infNormVec (fun i => x i - x_hat 0 i) +
          infNorm M_inv * infNormVec (ξ 0) := hone
      _ ≤ q * infNormVec (fun i => x i - x_hat 0 i) +
          infNorm M_inv * μ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hG (infNormVec_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hξ_bound 0) hMn
      _ = q ^ 1 * infNormVec (fun i => x i - x_hat 0 i) +
          μ * infNorm M_inv := by rw [pow_one]; ring
      _ ≤ q ^ 1 * infNormVec (fun i => x i - x_hat 0 i) +
          μ * infNorm M_inv / (1 - q) := by
          have hnn : 0 ≤ μ * infNorm M_inv := mul_nonneg hμ hMn
          have hdiv : μ * infNorm M_inv ≤ μ * infNorm M_inv / (1 - q) := by
            rw [le_div_iff₀ hq1']; nlinarith
          linarith
  | succ m ih =>
    have hone := normwise_one_step_bound n hn A M N M_inv hS b x hAx x_hat ξ hIter (m + 1)
    calc infNormVec (fun i => x i - x_hat (m + 2) i)
        ≤ infNorm (iterMatrix n M_inv N) *
            infNormVec (fun i => x i - x_hat (m + 1) i) +
          infNorm M_inv * infNormVec (ξ (m + 1)) := hone
      _ ≤ q * (q ^ (m + 1) * infNormVec (fun i => x i - x_hat 0 i) +
            μ * infNorm M_inv / (1 - q)) +
          infNorm M_inv * μ := by
          apply add_le_add
          · exact le_trans (mul_le_mul_of_nonneg_right hG (infNormVec_nonneg _))
              (mul_le_mul_of_nonneg_left ih hq)
          · exact mul_le_mul_of_nonneg_left (hξ_bound _) hMn
      _ = q ^ (m + 2) * infNormVec (fun i => x i - x_hat 0 i) +
          (q * (μ * infNorm M_inv / (1 - q)) + μ * infNorm M_inv) := by ring
      _ = q ^ (m + 2) * infNormVec (fun i => x i - x_hat 0 i) +
          μ * infNorm M_inv / (1 - q) := by
          congr 1
          field_simp
          ring

-- ============================================================
-- §17.2  Main forward bound (eq 17.13)
-- ============================================================

/-- **Eq. 17.13 (Main componentwise forward bound)**: Composes the componentwise
    forward bound (eq 17.6) with local error simplification (eq 17.10) and the
    partial-sum bound c(A) (eq 17.12).  Given as hypotheses rather than
    re-deriving; this is a straightforward composition. -/
theorem main_forward_bound (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (M N : Fin n → Fin n → ℝ)
    (cn_u θ_x cA : ℝ) (hcn : 0 ≤ cn_u) (_hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x) (m : ℕ)
    (hPartial : PartialSumBound n G M_inv A_inv cA m) :
    ∀ i, ∑ k ∈ Finset.range (m + 1),
      ∑ j : Fin n, (∑ l : Fin n, |matPow n G k i l| * |M_inv l j|) *
        (cn_u * (1 + θ_x) * ∑ p : Fin n, (|M j p| + |N j p|) * |x p|) ≤
      cn_u * (1 + θ_x) * cA *
        ∑ j : Fin n, |A_inv i j| *
          ∑ p : Fin n, (|M j p| + |N j p|) * |x p| := by
  intro i
  have hcoeff : 0 ≤ cn_u * (1 + θ_x) := mul_nonneg hcn (by linarith)
  calc ∑ k ∈ Finset.range (m + 1),
      ∑ j : Fin n, (∑ l, |matPow n G k i l| * |M_inv l j|) *
        (cn_u * (1 + θ_x) * ∑ p, (|M j p| + |N j p|) * |x p|)
      = cn_u * (1 + θ_x) * ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, (∑ l, |matPow n G k i l| * |M_inv l j|) *
            ∑ p, (|M j p| + |N j p|) * |x p| := by
        rw [Finset.mul_sum]; congr 1; ext k
        rw [Finset.mul_sum]; congr 1; ext j; ring
    _ ≤ cn_u * (1 + θ_x) * (cA * ∑ j : Fin n, |A_inv i j| *
          ∑ p, (|M j p| + |N j p|) * |x p|) := by
        apply mul_le_mul_of_nonneg_left _ hcoeff
        rw [Finset.sum_comm]; rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro j _
        rw [← Finset.sum_mul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hPartial i j) (Finset.sum_nonneg (fun p _ =>
          mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)))
    _ = cn_u * (1 + θ_x) * cA *
          ∑ j, |A_inv i j| * ∑ p, (|M j p| + |N j p|) * |x p| := by ring

/-- Finite correction term obtained from the local-error bound in Higham,
    2nd ed., Chapter 17, equations (17.11) and (17.13).  This is the
    finite, certified counterpart of the infinite-series correction term. -/
noncomputable def finiteForwardCorrection (n : ℕ)
    (G M_inv M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (cn_u θ_x : ℝ) (m : ℕ) : Fin n → ℝ :=
  fun i => ∑ k ∈ Finset.range (m + 1),
    ∑ j : Fin n, (∑ l : Fin n, |matPow n G k i l| * |M_inv l j|) *
      (cn_u * (1 + θ_x) * ∑ p : Fin n, (|M j p| + |N j p|) * |x p|)

/-- Vector form of the source factor
    `|A^{-1}| (|M| + |N|) |x|` in Higham, 2nd ed., Chapter 17,
    equations (17.13) and (17.15). -/
noncomputable def mainForwardBoundVector (n : ℕ)
    (A_inv M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, |A_inv i j| *
    ∑ p : Fin n, (|M j p| + |N j p|) * |x p|

/-- The vector `|A^{-1}| (|M| + |N|) |x|` is componentwise nonnegative. -/
theorem mainForwardBoundVector_nonneg (n : ℕ)
    (A_inv M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    ∀ i, 0 ≤ mainForwardBoundVector n A_inv M N x i := by
  intro i
  unfold mainForwardBoundVector
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (abs_nonneg _)
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)

/-- The finite Chapter 17 correction term is componentwise nonnegative under
    the standard nonnegativity hypotheses on `c_n u` and `θ_x`. -/
theorem finiteForwardCorrection_nonneg (n : ℕ)
    (G M_inv M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (cn_u θ_x : ℝ) (hcn : 0 ≤ cn_u) (hθ : 0 ≤ θ_x) (m : ℕ) :
    ∀ i, 0 ≤ finiteForwardCorrection n G M_inv M N x cn_u θ_x m i := by
  have hcoeff : 0 ≤ cn_u * (1 + θ_x) := mul_nonneg hcn (by linarith)
  intro i
  unfold finiteForwardCorrection
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg
  · apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · apply mul_nonneg hcoeff
    apply Finset.sum_nonneg
    intro p _
    exact mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)

/-- Finite, componentwise version of the `(17.13)` correction estimate:
    the finite correction term is bounded by the `c(A)`-weighted source vector. -/
theorem finiteForwardCorrection_le_mainForwardBoundVector (n : ℕ)
    (G M_inv A_inv M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (cn_u θ_x cA : ℝ) (hcn : 0 ≤ cn_u) (hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x)
    (m : ℕ) (hPartial : PartialSumBound n G M_inv A_inv cA m) :
    ∀ i, finiteForwardCorrection n G M_inv M N x cn_u θ_x m i ≤
      cn_u * (1 + θ_x) * cA * mainForwardBoundVector n A_inv M N x i := by
  intro i
  simpa [finiteForwardCorrection, mainForwardBoundVector] using
    main_forward_bound n G M_inv A_inv x M N cn_u θ_x cA hcn hcA hθ m hPartial i

/-- Infinity-norm form of the finite `(17.13)` correction estimate. -/
theorem finiteForwardCorrection_norm_bound (n : ℕ)
    (G M_inv A_inv M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (cn_u θ_x cA : ℝ) (hcn : 0 ≤ cn_u) (hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x)
    (m : ℕ) (hPartial : PartialSumBound n G M_inv A_inv cA m) :
    infNormVec (finiteForwardCorrection n G M_inv M N x cn_u θ_x m) ≤
      cn_u * (1 + θ_x) * cA * infNormVec (mainForwardBoundVector n A_inv M N x) := by
  have hcoeff : 0 ≤ cn_u * (1 + θ_x) * cA := by
    exact mul_nonneg (mul_nonneg hcn (by linarith)) hcA
  have hcorr_nonneg :=
    finiteForwardCorrection_nonneg n G M_inv M N x cn_u θ_x hcn hθ m
  have hbound_nonneg := mainForwardBoundVector_nonneg n A_inv M N x
  have hcomp :=
    finiteForwardCorrection_le_mainForwardBoundVector n G M_inv A_inv M N x
      cn_u θ_x cA hcn hcA hθ m hPartial
  apply infNormVec_le_of_abs_le
  · intro i
    have hbound_abs :
        |mainForwardBoundVector n A_inv M N x i| =
          mainForwardBoundVector n A_inv M N x i :=
      abs_of_nonneg (hbound_nonneg i)
    have hbound_le_norm :
        mainForwardBoundVector n A_inv M N x i ≤
          infNormVec (mainForwardBoundVector n A_inv M N x) := by
      simpa [hbound_abs] using
        abs_le_infNormVec (mainForwardBoundVector n A_inv M N x) i
    calc
      |finiteForwardCorrection n G M_inv M N x cn_u θ_x m i|
          = finiteForwardCorrection n G M_inv M N x cn_u θ_x m i :=
            abs_of_nonneg (hcorr_nonneg i)
      _ ≤ cn_u * (1 + θ_x) * cA * mainForwardBoundVector n A_inv M N x i :=
            hcomp i
      _ ≤ cn_u * (1 + θ_x) * cA *
          infNormVec (mainForwardBoundVector n A_inv M N x) :=
            mul_le_mul_of_nonneg_left hbound_le_norm hcoeff
  · exact mul_nonneg hcoeff (infNormVec_nonneg _)

/-- Finite normwise form corresponding to Higham, 2nd ed., Chapter 17,
    equation (17.15): taking the infinity norm of the propagated initial
    error plus the finite, `c(A)`-certified correction term. -/
theorem finite_norm_form_forward_bound (n : ℕ)
    (G M_inv A_inv M N : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (cn_u θ_x cA : ℝ) (hcn : 0 ≤ cn_u) (hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x)
    (m : ℕ) (hPartial : PartialSumBound n G M_inv A_inv cA m) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M N x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cA * infNormVec (mainForwardBoundVector n A_inv M N x) := by
  have hcorrNorm :=
    finiteForwardCorrection_norm_bound n G M_inv A_inv M N x cn_u θ_x cA
      hcn hcA hθ m hPartial
  have hcorr_abs :
      ∀ i, |finiteForwardCorrection n G M_inv M N x cn_u θ_x m i| ≤
        cn_u * (1 + θ_x) * cA * infNormVec (mainForwardBoundVector n A_inv M N x) := by
    intro i
    exact le_trans
      (abs_le_infNormVec (finiteForwardCorrection n G M_inv M N x cn_u θ_x m) i)
      hcorrNorm
  apply infNormVec_le_of_abs_le
  · intro i
    calc
      |matMulVec n (matPow n G (m + 1)) e₀ i +
          finiteForwardCorrection n G M_inv M N x cn_u θ_x m i|
          ≤ |matMulVec n (matPow n G (m + 1)) e₀ i| +
              |finiteForwardCorrection n G M_inv M N x cn_u θ_x m i| :=
            abs_add_le _ _
      _ ≤ infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
          cn_u * (1 + θ_x) * cA * infNormVec (mainForwardBoundVector n A_inv M N x) :=
            add_le_add (abs_le_infNormVec (matMulVec n (matPow n G (m + 1)) e₀) i)
              (hcorr_abs i)
  · exact add_nonneg (infNormVec_nonneg _)
      (mul_nonneg
        (mul_nonneg (mul_nonneg hcn (by linarith)) hcA)
        (infNormVec_nonneg _))

/-- Jacobi-specialized source vector `|A^{-1}| |A| |x|` appearing in
    Higham, 2nd ed., Chapter 17, equation (17.16). -/
noncomputable def jacobiForwardBoundVector (n : ℕ)
    (A_inv A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, |A_inv i j| * ∑ p : Fin n, |A j p| * |x p|

/-- Under the Jacobi splitting, the general `(17.13)` source vector
    `|A^{-1}|(|M|+|N|)|x|` becomes `|A^{-1}||A||x|`. -/
theorem mainForwardBoundVector_eq_jacobiForwardBoundVector (n : ℕ)
    (A_inv A M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hM : ∀ i j, M i j = if i = j then A i i else 0)
    (hN : ∀ i j, N i j = M i j - A i j) :
    mainForwardBoundVector n A_inv M N x =
      jacobiForwardBoundVector n A_inv A x := by
  have hJac := jacobi_splitting_abs n A M N hM hN
  funext i
  unfold mainForwardBoundVector jacobiForwardBoundVector
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [hJac j p]

/-- Finite/certificate Jacobi specialization of the norm-form forward bound,
    corresponding to the finite-horizon counterpart of equation (17.16). -/
theorem finite_norm_form_jacobi_forward_bound (n : ℕ)
    (A G M_inv A_inv M N : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (cn_u θ_x cA : ℝ) (hcn : 0 ≤ cn_u) (hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x)
    (hM : ∀ i j, M i j = if i = j then A i i else 0)
    (hN : ∀ i j, N i j = M i j - A i j)
    (m : ℕ) (hPartial : PartialSumBound n G M_inv A_inv cA m) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M N x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cA * infNormVec (jacobiForwardBoundVector n A_inv A x) := by
  have hmain :=
    finite_norm_form_forward_bound n G M_inv A_inv M N e₀ x cn_u θ_x cA
      hcn hcA hθ m hPartial
  have hvec := mainForwardBoundVector_eq_jacobiForwardBoundVector n A_inv A M N x hM hN
  simpa [hvec] using hmain

/-- Higham, 2nd ed., Chapter 17, equation (17.17):
    SOR multiplier `f(omega) = (1 + |1 - omega|) / omega`. -/
noncomputable def sorForwardFactor (ω : ℝ) : ℝ :=
  (1 + |1 - ω|) / ω

/-- The SOR forward-error multiplier is nonnegative for positive relaxation
    parameter. -/
theorem sorForwardFactor_nonneg (ω : ℝ) (hω_pos : 0 < ω) :
    0 ≤ sorForwardFactor ω := by
  unfold sorForwardFactor
  have hnum : 0 ≤ 1 + |1 - ω| := by
    linarith [abs_nonneg (1 - ω)]
  exact div_nonneg hnum (le_of_lt hω_pos)

/-- The Jacobi right-hand vector `|A^{-1}||A||x|` is componentwise
    nonnegative. -/
theorem jacobiForwardBoundVector_nonneg (n : ℕ)
    (A_inv A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    ∀ i, 0 ≤ jacobiForwardBoundVector n A_inv A x i := by
  intro i
  unfold jacobiForwardBoundVector
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (abs_nonneg _)
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Higham, 2nd ed., Chapter 17, equation (17.17), lifted to the
    source-vector level: the general vector `|A^{-1}|(|M|+|N|)|x|` is bounded by
    `f(omega)|A^{-1}||A||x|` for the SOR splitting. -/
theorem mainForwardBoundVector_le_sorForwardBoundVector (n : ℕ)
    (A_inv A D L U M_sor N_sor : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (ω : ℝ) (hω_pos : 0 < ω)
    (hDecomp : ∀ i j, A i j = D i j + L i j + U i j)
    (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, j.val ≥ i.val → L i j = 0)
    (hU : ∀ i j, j.val ≤ i.val → U i j = 0)
    (hM : ∀ i j, M_sor i j = (1 / ω) * (D i j + ω * L i j))
    (hN : ∀ i j, N_sor i j = (1 / ω) * ((1 - ω) * D i j - ω * U i j)) :
    ∀ i, mainForwardBoundVector n A_inv M_sor N_sor x i ≤
      sorForwardFactor ω * jacobiForwardBoundVector n A_inv A x i := by
  let f := sorForwardFactor ω
  have hsor :
      ∀ i j, |M_sor i j| + |N_sor i j| ≤ f * |A i j| := by
    intro i j
    simpa [f, sorForwardFactor] using
      sor_splitting_bound n A ω hω_pos D L U hDecomp hD hL hU M_sor N_sor hM hN i j
  intro i
  unfold mainForwardBoundVector jacobiForwardBoundVector
  change (∑ j : Fin n, |A_inv i j| *
      ∑ p : Fin n, (|M_sor j p| + |N_sor j p|) * |x p|) ≤
    f * (∑ j : Fin n, |A_inv i j| * ∑ p : Fin n, |A j p| * |x p|)
  calc
    ∑ j : Fin n, |A_inv i j| *
        ∑ p : Fin n, (|M_sor j p| + |N_sor j p|) * |x p|
        ≤ ∑ j : Fin n, |A_inv i j| *
            ∑ p : Fin n, (f * |A j p|) * |x p| := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply Finset.sum_le_sum
          intro p _
          exact mul_le_mul_of_nonneg_right (hsor j p) (abs_nonneg _)
    _ = f * (∑ j : Fin n, |A_inv i j| * ∑ p : Fin n, |A j p| * |x p|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          calc
            |A_inv i j| * (∑ p : Fin n, (f * |A j p|) * |x p|)
                = |A_inv i j| * (f * ∑ p : Fin n, |A j p| * |x p|) := by
                  congr 1
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro p _
                  ring
            _ = f * (|A_inv i j| * ∑ p : Fin n, |A j p| * |x p|) := by ring

/-- Infinity-norm version of the SOR source-vector comparison from (17.17). -/
theorem mainForwardBoundVector_norm_le_sorForwardBoundVector (n : ℕ)
    (A_inv A D L U M_sor N_sor : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (ω : ℝ) (hω_pos : 0 < ω)
    (hDecomp : ∀ i j, A i j = D i j + L i j + U i j)
    (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, j.val ≥ i.val → L i j = 0)
    (hU : ∀ i j, j.val ≤ i.val → U i j = 0)
    (hM : ∀ i j, M_sor i j = (1 / ω) * (D i j + ω * L i j))
    (hN : ∀ i j, N_sor i j = (1 / ω) * ((1 - ω) * D i j - ω * U i j)) :
    infNormVec (mainForwardBoundVector n A_inv M_sor N_sor x) ≤
      sorForwardFactor ω * infNormVec (jacobiForwardBoundVector n A_inv A x) := by
  have hf : 0 ≤ sorForwardFactor ω := sorForwardFactor_nonneg ω hω_pos
  have hmain_nonneg := mainForwardBoundVector_nonneg n A_inv M_sor N_sor x
  have hjac_nonneg := jacobiForwardBoundVector_nonneg n A_inv A x
  have hcomp :=
    mainForwardBoundVector_le_sorForwardBoundVector n A_inv A D L U M_sor N_sor x
      ω hω_pos hDecomp hD hL hU hM hN
  apply infNormVec_le_of_abs_le
  · intro i
    have hjac_abs :
        |jacobiForwardBoundVector n A_inv A x i| =
          jacobiForwardBoundVector n A_inv A x i :=
      abs_of_nonneg (hjac_nonneg i)
    have hjac_le_norm :
        jacobiForwardBoundVector n A_inv A x i ≤
          infNormVec (jacobiForwardBoundVector n A_inv A x) := by
      simpa [hjac_abs] using
        abs_le_infNormVec (jacobiForwardBoundVector n A_inv A x) i
    calc
      |mainForwardBoundVector n A_inv M_sor N_sor x i|
          = mainForwardBoundVector n A_inv M_sor N_sor x i :=
            abs_of_nonneg (hmain_nonneg i)
      _ ≤ sorForwardFactor ω * jacobiForwardBoundVector n A_inv A x i :=
            hcomp i
      _ ≤ sorForwardFactor ω * infNormVec (jacobiForwardBoundVector n A_inv A x) :=
            mul_le_mul_of_nonneg_left hjac_le_norm hf
  · exact mul_nonneg hf (infNormVec_nonneg _)

/-- Finite/certificate SOR specialization of Higham, 2nd ed., Chapter 17,
    equations (17.15)-(17.17): the finite norm-form forward bound with the
    SOR multiplier `f(omega)` and right-hand vector `|A^{-1}||A||x|`. -/
theorem finite_norm_form_sor_forward_bound (n : ℕ)
    (A G M_inv A_inv D L U M_sor N_sor : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (ω cn_u θ_x cA : ℝ) (hω_pos : 0 < ω)
    (hcn : 0 ≤ cn_u) (hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x)
    (hDecomp : ∀ i j, A i j = D i j + L i j + U i j)
    (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, j.val ≥ i.val → L i j = 0)
    (hU : ∀ i j, j.val ≤ i.val → U i j = 0)
    (hM : ∀ i j, M_sor i j = (1 / ω) * (D i j + ω * L i j))
    (hN : ∀ i j, N_sor i j = (1 / ω) * ((1 - ω) * D i j - ω * U i j))
    (m : ℕ) (hPartial : PartialSumBound n G M_inv A_inv cA m) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M_sor N_sor x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cA *
          (sorForwardFactor ω * infNormVec (jacobiForwardBoundVector n A_inv A x)) := by
  have hmain :=
    finite_norm_form_forward_bound n G M_inv A_inv M_sor N_sor e₀ x cn_u θ_x cA
      hcn hcA hθ m hPartial
  have hvec :=
    mainForwardBoundVector_norm_le_sorForwardBoundVector n A_inv A D L U M_sor N_sor x
      ω hω_pos hDecomp hD hL hU hM hN
  have hcoeff : 0 ≤ cn_u * (1 + θ_x) * cA := by
    exact mul_nonneg (mul_nonneg hcn (by linarith)) hcA
  exact hmain.trans
    (add_le_add_right (mul_le_mul_of_nonneg_left hvec hcoeff)
      (infNormVec (matMulVec n (matPow n G (m + 1)) e₀)))

/-- Higham, 2nd ed., Chapter 17, Section 17.2.2:
    for Gauss-Seidel, viewed as SOR with `omega = 1`, the SOR multiplier is 1. -/
theorem sorForwardFactor_one : sorForwardFactor 1 = 1 := by
  unfold sorForwardFactor
  simp

/-- Finite/certificate Gauss-Seidel specialization of Higham, 2nd ed.,
    Chapter 17, Section 17.2.2: Gauss-Seidel is SOR with `omega = 1`, so the
    finite norm-form forward bound has the same visible right-hand factor as
    the Jacobi finite norm-form bound. -/
theorem finite_norm_form_gaussSeidel_forward_bound (n : ℕ)
    (A G M_inv A_inv D L U M_gs N_gs : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (cn_u θ_x cA : ℝ) (hcn : 0 ≤ cn_u) (hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x)
    (hDecomp : ∀ i j, A i j = D i j + L i j + U i j)
    (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, j.val ≥ i.val → L i j = 0)
    (hU : ∀ i j, j.val ≤ i.val → U i j = 0)
    (hM : ∀ i j, M_gs i j = D i j + L i j)
    (hN : ∀ i j, N_gs i j = -U i j)
    (m : ℕ) (hPartial : PartialSumBound n G M_inv A_inv cA m) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M_gs N_gs x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cA *
          infNormVec (jacobiForwardBoundVector n A_inv A x) := by
  have hM_sor :
      ∀ i j, M_gs i j = (1 / (1 : ℝ)) * (D i j + (1 : ℝ) * L i j) := by
    intro i j
    rw [hM i j]
    ring
  have hN_sor :
      ∀ i j, N_gs i j = (1 / (1 : ℝ)) * (((1 : ℝ) - 1) * D i j - (1 : ℝ) * U i j) := by
    intro i j
    rw [hN i j]
    ring
  have hsor :=
    finite_norm_form_sor_forward_bound n A G M_inv A_inv D L U M_gs N_gs e₀ x
      1 cn_u θ_x cA (by norm_num) hcn hcA hθ hDecomp hD hL hU hM_sor hN_sor
      m hPartial
  simpa [sorForwardFactor_one] using hsor

-- ============================================================
-- §17.3  Normwise residual bound (eq 17.19)
-- ============================================================

/-- Normwise one-step residual bound from `one_step_residual`:
    ‖r_{k+1}‖∞ ≤ ‖H‖∞·‖r_k‖∞ + ‖I−H‖∞·‖ξ_k‖∞. -/
theorem normwise_one_step_residual_bound (n : ℕ) (_hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) (k : ℕ) :
    infNormVec (fun i => b i - ∑ j, A i j * x_hat (k + 1) j) ≤
      infNorm (dualIterMatrix n N M_inv) *
        infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) +
      infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
        infNormVec (ξ k) := by
  have hres := one_step_residual n A M N M_inv hS b x hAx x_hat ξ hIter
  suffices h : ∀ i : Fin n, |b i - ∑ j, A i j * x_hat (k + 1) j| ≤
      infNorm (dualIterMatrix n N M_inv) *
        infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) +
      infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
        infNormVec (ξ k) by
    apply infNormVec_le_of_abs_le
    · exact h
    · exact add_nonneg
        (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))
        (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))
  intro i; rw [hres k i]
  -- |Hr_k - (I-H)ξ_k| ≤ |Hr_k| + |(I-H)ξ_k| ≤ ‖H‖·‖r_k‖ + ‖I-H‖·‖ξ_k‖
  set a := matMulVec n (dualIterMatrix n N M_inv)
      (fun j => b j - ∑ l, A j l * x_hat k l) i
  set c := matMulVec n (matSub_id n (dualIterMatrix n N M_inv)) (ξ k) i
  have htri : |a - c| ≤ |a| + |c| := (abs_add_le a (-c)).trans (by rw [abs_neg])
  have ha : |a| ≤ infNorm (dualIterMatrix n N M_inv) *
      infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) := by
    change |∑ j : Fin n, dualIterMatrix n N M_inv i j *
        (b j - ∑ l, A j l * x_hat k l)| ≤ _
    calc |∑ j, dualIterMatrix n N M_inv i j *
            (b j - ∑ l, A j l * x_hat k l)|
        ≤ ∑ j, |dualIterMatrix n N M_inv i j *
            (b j - ∑ l, A j l * x_hat k l)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |dualIterMatrix n N M_inv i j| *
            |b j - ∑ l, A j l * x_hat k l| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, |dualIterMatrix n N M_inv i j| *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact abs_le_infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) j
      _ = (∑ j, |dualIterMatrix n N M_inv i j|) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) := by
          rw [Finset.sum_mul]
      _ ≤ infNorm (dualIterMatrix n N M_inv) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) :=
          mul_le_mul_of_nonneg_right (row_sum_le_infNorm _ i)
            (infNormVec_nonneg _)
  have hc : |c| ≤ infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
      infNormVec (ξ k) := by
    change |∑ j : Fin n, matSub_id n (dualIterMatrix n N M_inv) i j *
        ξ k j| ≤ _
    calc |∑ j, matSub_id n (dualIterMatrix n N M_inv) i j * ξ k j|
        ≤ ∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j * ξ k j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j| * |ξ k j| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j| *
            infNormVec (ξ k) := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact abs_le_infNormVec (ξ k) j
      _ = (∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j|) *
            infNormVec (ξ k) := by rw [Finset.sum_mul]
      _ ≤ infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
            infNormVec (ξ k) :=
          mul_le_mul_of_nonneg_right (row_sum_le_infNorm _ i)
            (infNormVec_nonneg _)
  linarith

/-- **Eq. 17.19 (Normwise residual bound)**: ‖r_{m+1}‖∞ ≤ q^{m+1}·‖r₀‖∞ + μ·‖I−H‖∞/(1−q)
    where q ≥ ‖H‖∞ and μ ≥ ‖ξ_k‖∞ for all k.  Derived by induction
    from `normwise_one_step_residual_bound` using geometric contraction. -/
theorem normwise_residual_bound (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hH : infNorm (dualIterMatrix n N M_inv) ≤ q)
    (μ : ℝ) (hμ : 0 ≤ μ) (hξ_bound : ∀ k, infNormVec (ξ k) ≤ μ)
    (m : ℕ) :
    infNormVec (fun i => b i - ∑ j, A i j * x_hat (m + 1) j) ≤
      q ^ (m + 1) * infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
      μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  have hImH := infNorm_nonneg (matSub_id n (dualIterMatrix n N M_inv))
  induction m with
  | zero =>
    have hone := normwise_one_step_residual_bound n hn A M N M_inv hS b x hAx
        x_hat ξ hIter 0
    calc infNormVec (fun i => b i - ∑ j, A i j * x_hat 1 j)
        ≤ infNorm (dualIterMatrix n N M_inv) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
            infNormVec (ξ 0) := hone
      _ ≤ q * infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          infNorm (matSub_id n (dualIterMatrix n N M_inv)) * μ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hH (infNormVec_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hξ_bound 0) hImH
      _ = q ^ 1 * infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) := by
          rw [pow_one]; ring
      _ ≤ q ^ 1 * infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) /
            (1 - q) := by
          have hnn : 0 ≤ μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) :=
            mul_nonneg hμ hImH
          have hdiv : μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) ≤
              μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) /
                (1 - q) := by
            rw [le_div_iff₀ hq1']; nlinarith
          linarith
  | succ m ih =>
    have hone := normwise_one_step_residual_bound n hn A M N M_inv hS b x hAx
        x_hat ξ hIter (m + 1)
    calc infNormVec (fun i => b i - ∑ j, A i j * x_hat (m + 2) j)
        ≤ infNorm (dualIterMatrix n N M_inv) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat (m + 1) j) +
          infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
            infNormVec (ξ (m + 1)) := hone
      _ ≤ q * (q ^ (m + 1) *
              infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
            μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) /
              (1 - q)) +
          infNorm (matSub_id n (dualIterMatrix n N M_inv)) * μ := by
          apply add_le_add
          · exact le_trans (mul_le_mul_of_nonneg_right hH (infNormVec_nonneg _))
              (mul_le_mul_of_nonneg_left ih hq)
          · exact mul_le_mul_of_nonneg_left (hξ_bound _) hImH
      _ = q ^ (m + 2) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          (q * (μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) /
            (1 - q)) +
           μ * infNorm (matSub_id n (dualIterMatrix n N M_inv))) := by
          ring
      _ = q ^ (m + 2) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) /
            (1 - q) := by
          congr 1; field_simp; ring

-- ============================================================
-- §17.5  Stopping tests (eqs. 17.33a-c)
-- ============================================================

/-- Higham, 2nd ed., Chapter 17, Section 17.5, equation (17.33a):
    a small residual relative to the right-hand side is equivalent to an
    exact solve for a right-hand-side perturbation with the same norm budget. -/
theorem stopping_test_rhs_backward_subordinate
    {n : ℕ} (_hn : 0 < n) {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    {A : CMatrix n n} {y b : CVec n} {ε : ℝ} (_hε : 0 ≤ ε) :
    (ν (fun i => b i - complexMatrixVecMul A y i) ≤ ε * ν b) ↔
    (∃ Δb : CVec n,
      ν Δb ≤ ε * ν b ∧
      complexMatrixVecMul A y = fun i => b i + Δb i) := by
  constructor
  · intro h
    let r : CVec n := fun i => b i - complexMatrixVecMul A y i
    let Δb : CVec n := complexVecSMul (-1 : ℂ) r
    refine ⟨Δb, ?_, ?_⟩
    · calc
        ν Δb = ν r := by
          dsimp [Δb]
          rw [hν.smul (-1 : ℂ) r]
          norm_num
        _ ≤ ε * ν b := by simpa [r] using h
    · ext i
      dsimp [Δb, r, complexVecSMul]
      ring
  · intro h
    obtain ⟨Δb, hΔb, hExact⟩ := h
    have hr :
        (fun i => b i - complexMatrixVecMul A y i) =
          complexVecSMul (-1 : ℂ) Δb := by
      ext i
      have hi := congrFun hExact i
      rw [hi]
      simp [complexVecSMul]
    calc
      ν (fun i => b i - complexMatrixVecMul A y i)
          = ν (complexVecSMul (-1 : ℂ) Δb) := by rw [hr]
      _ = ν Δb := by
        rw [hν.smul (-1 : ℂ) Δb]
        norm_num
      _ ≤ ε * ν b := hΔb

/-- Higham, 2nd ed., Chapter 17, Section 17.5, equation (17.33b):
    a small residual relative to `‖A‖‖y‖` is equivalent to an exact solve for
    a matrix perturbation with the same subordinate-norm budget. -/
theorem stopping_test_matrix_backward_subordinate
    {n : ℕ} (hn : 0 < n) {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    {A E : CMatrix n n} {y b : CVec n} {e ε : ℝ}
    (hε : 0 ≤ ε)
    (hE : IsMixedSubordinateMatrixNormValue ν ν E e) :
    (ν (fun i => b i - complexMatrixVecMul A y i) ≤ ε * (e * ν y)) ↔
    (∃ ΔA : CMatrix n n,
      MixedSubordinateMatrixBound ν ν ΔA (ε * e) ∧
      complexMatrixVecMul (fun i j => A i j + ΔA i j) y = b) := by
  have hzeroν : ν (0 : CVec n) = 0 := (hν.eq_zero_iff (0 : CVec n)).2 rfl
  constructor
  · intro h
    have hBound :
        ν (fun i => b i - complexMatrixVecMul A y i) ≤
          ε * (e * ν y + ν (0 : CVec n)) := by
      simpa [hzeroν] using h
    obtain ⟨ΔA, Δb, hΔA, hΔb, hExact⟩ :=
      theorem7_1_subordinate_sufficient
        (n := n) (ν := ν) (A := A) (E := E) (y := y) (b := b)
        (f := 0) (e := e) (ε := ε) hn hν hε hE hBound
    have hΔb_norm_zero : ν Δb = 0 := by
      apply le_antisymm
      · calc
          ν Δb ≤ ε * ν (0 : CVec n) := hΔb
          _ = 0 := by rw [hzeroν, mul_zero]
      · exact hν.nonneg Δb
    have hΔb_zero : Δb = 0 := (hν.eq_zero_iff Δb).1 hΔb_norm_zero
    refine ⟨ΔA, hΔA, ?_⟩
    ext i
    have hi := congrFun hExact i
    rw [hΔb_zero] at hi
    simpa using hi
  · intro h
    obtain ⟨ΔA, hΔA, hExact⟩ := h
    have hΔb : ν (0 : CVec n) ≤ ε * ν (0 : CVec n) := by
      rw [hzeroν, mul_zero]
    have hPerturbed :
        complexMatrixVecMul (fun i j => A i j + ΔA i j) y =
          fun i => b i + (0 : CVec n) i := by
      ext i
      simpa using congrFun hExact i
    have hBound :
        ν (fun i => b i - complexMatrixVecMul A y i) ≤
          ε * (e * ν y + ν (0 : CVec n)) :=
      theorem7_1_subordinate_necessary
        (n := n) (ν := ν) (A := A) (E := E) (ΔA := ΔA)
        (y := y) (b := b) (f := 0) (Δb := 0) (e := e) (ε := ε)
        hn hν hε hE hΔA hΔb hPerturbed
    simpa [hzeroν] using hBound

/-- Higham, 2nd ed., Chapter 17, Section 17.5, equation (17.33c):
    the mixed stopping test is exactly the Chapter 7 normwise backward-error
    equivalence specialized with the right-hand-side budget `f = b`. -/
theorem stopping_test_mixed_backward_subordinate
    {n : ℕ} (hn : 0 < n) {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    {A E : CMatrix n n} {y b : CVec n} {e ε : ℝ}
    (hε : 0 ≤ ε)
    (hE : IsMixedSubordinateMatrixNormValue ν ν E e) :
    (ν (fun i => b i - complexMatrixVecMul A y i) ≤
      ε * (e * ν y + ν b)) ↔
    (∃ ΔA : CMatrix n n, ∃ Δb : CVec n,
      MixedSubordinateMatrixBound ν ν ΔA (ε * e) ∧
      ν Δb ≤ ε * ν b ∧
      complexMatrixVecMul (fun i j => A i j + ΔA i j) y =
        fun i => b i + Δb i) := by
  exact theorem7_1_subordinate
    (n := n) (ν := ν) (A := A) (E := E) (y := y) (b := b)
    (f := b) (e := e) (ε := ε) hn hν hε hE

/-- Higham, 2nd ed., Chapter 17, Section 17.5, after equation (17.33):
    componentwise absolute-value version of (17.33a), perturbing the right-hand
    side only. -/
theorem stopping_test_rhs_backward_componentwise
    {n : ℕ} (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    {ε : ℝ} (_hε : 0 ≤ ε) :
    (∀ i : Fin n, |residualVec n A y b i| ≤ ε * |b i|) ↔
    (∃ Δb : Fin n → ℝ,
      (∀ i : Fin n, |Δb i| ≤ ε * |b i|) ∧
      (∀ i : Fin n, ∑ j : Fin n, A i j * y j = b i + Δb i)) := by
  constructor
  · intro h
    let Δb : Fin n → ℝ := fun i => ∑ j : Fin n, A i j * y j - b i
    refine ⟨Δb, ?_, ?_⟩
    · intro i
      have hres : Δb i = -residualVec n A y b i := by
        simp [Δb, residualVec]
      calc
        |Δb i| = |residualVec n A y b i| := by rw [hres, abs_neg]
        _ ≤ ε * |b i| := h i
    · intro i
      simp [Δb]
  · intro h
    obtain ⟨Δb, hΔb, hExact⟩ := h
    intro i
    have hi := hExact i
    have hres : residualVec n A y b i = -Δb i := by
      simp [residualVec, hi]
    calc
      |residualVec n A y b i| = |Δb i| := by rw [hres, abs_neg]
      _ ≤ ε * |b i| := hΔb i

/-- Higham, 2nd ed., Chapter 17, Section 17.5, after equation (17.33):
    componentwise absolute-value version of (17.33b), perturbing the matrix
    only.  This is the Oettli-Prager theorem with zero right-hand-side budget. -/
theorem stopping_test_matrix_backward_componentwise
    {n : ℕ} (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∀ i : Fin n,
      |residualVec n A y b i| ≤ ε * (∑ j : Fin n, |A i j| * |y j|)) ↔
    (∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA i j| ≤ ε * |A i j|) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i)) := by
  have hE : ∀ i j : Fin n, 0 ≤ absMatrix n A i j := by
    intro i j
    exact abs_nonneg (A i j)
  have hf : ∀ i : Fin n, 0 ≤ (0 : Fin n → ℝ) i := by
    intro i
    exact le_rfl
  constructor
  · intro h
    have hBound :
        ∀ i : Fin n, |residualVec n A y b i| ≤
          ε * (∑ j : Fin n, absMatrix n A i j * |y j| + (0 : Fin n → ℝ) i) := by
      intro i
      simpa [absMatrix] using h i
    obtain ⟨ΔA, Δb, hΔA, hΔb, hExact⟩ :=
      oettli_prager_sufficient n A y b (absMatrix n A) (fun _ => 0) ε hε hE hf hBound
    have hΔb_zero : Δb = 0 := by
      ext i
      have hzero : |Δb i| = 0 := by
        apply le_antisymm
        · simpa using hΔb i
        · exact abs_nonneg (Δb i)
      exact abs_eq_zero.mp hzero
    refine ⟨ΔA, ?_, ?_⟩
    · intro i j
      simpa [absMatrix] using hΔA i j
    · intro i
      have hi := hExact i
      rw [hΔb_zero] at hi
      simpa using hi
  · intro h
    obtain ⟨ΔA, hΔA, hExact⟩ := h
    have hΔA' : ∀ i j : Fin n, |ΔA i j| ≤ ε * absMatrix n A i j := by
      intro i j
      simpa [absMatrix] using hΔA i j
    have hΔb' : ∀ i : Fin n, |(0 : Fin n → ℝ) i| ≤ ε * (0 : Fin n → ℝ) i := by
      intro i
      simp
    have hExact' :
        ∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * y j =
          b i + (0 : Fin n → ℝ) i := by
      intro i
      simpa using hExact i
    have hBound :=
      oettli_prager_necessary n A y b ΔA (fun _ => 0)
        (absMatrix n A) (fun _ => 0) ε hε hΔA' hΔb' hE hf hExact'
    intro i
    simpa [absMatrix] using hBound i

/-- Higham, 2nd ed., Chapter 17, Section 17.5, after equation (17.33):
    componentwise absolute-value version of (17.33c), perturbing both the matrix
    and right-hand side. -/
theorem stopping_test_mixed_backward_componentwise
    {n : ℕ} (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∀ i : Fin n,
      |residualVec n A y b i| ≤
        ε * (∑ j : Fin n, |A i j| * |y j| + |b i|)) ↔
    (∃ ΔA : Fin n → Fin n → ℝ, ∃ Δb : Fin n → ℝ,
      (∀ i j : Fin n, |ΔA i j| ≤ ε * |A i j|) ∧
      (∀ i : Fin n, |Δb i| ≤ ε * |b i|) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)) := by
  have hE : ∀ i j : Fin n, 0 ≤ absMatrix n A i j := by
    intro i j
    exact abs_nonneg (A i j)
  have hf : ∀ i : Fin n, 0 ≤ absVec n b i := by
    intro i
    exact abs_nonneg (b i)
  simpa [absMatrix, absVec] using
    (oettli_prager n A y b (absMatrix n A) (absVec n b) ε hε hE hf)

end LeanFpAnalysis.FP
