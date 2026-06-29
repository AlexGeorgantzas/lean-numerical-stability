-- Algorithms/Underdetermined/UnderdeterminedSolve.lean
--
-- Error analysis of solution methods for underdetermined systems
-- (Higham §21.3).
--
-- Q method (Theorem 21.4): backward stable; currently represented by
-- an abstract Gram-system predicate while the rectangular QR bridge is open.
-- The full source theorem requires rectangular QR.
--
-- SNE method: solves RᵀRy = b via Cholesky-like approach. The
-- backward error is proved by composing with existing Cholesky
-- solve results. The forward error (eq. 21.11) follows from
-- normwise_perturbation_bound (Theorem 7.2).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Analysis.PerturbationTheory
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySolve
import LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve
import LeanFpAnalysis.FP.Algorithms.Underdetermined.UnderdeterminedSpec

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §21.1  QR block algebra for the Q method and SNE setup
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.1):
    source-facing wrapper for multiplying by the tall QR block `[R; 0]`
    appearing in `Aᵀ = Q [R; 0]`. -/
theorem higham21_eq21_1_qr_transpose_block_mulVec {m k : ℕ}
    (R : Fin m → Fin m → ℝ) (x : Fin m → ℝ) :
    rectMatMulVec (lsQRTallBlock (k := k) R) x =
      Fin.append (rectMatMulVec R x) (0 : Fin k → ℝ) :=
  lsQRTallBlock_mulVec R x

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.2):
    source-facing wrapper for the block-transpose coordinate identity
    `[Rᵀ 0] [y₁; y₂] = Rᵀ y₁`.  This is the algebraic step behind reducing
    `b = A x` to the triangular equation for the first coordinate block after
    applying the orthogonal factor from (21.1). -/
theorem higham21_eq21_2_qr_block_transpose_coordinates {m k : ℕ}
    (R : Fin m → Fin m → ℝ) (y1 : Fin m → ℝ) (y2 : Fin k → ℝ) :
    (fun j : Fin m =>
      ∑ i : Fin (m + k), lsQRTallBlock (k := k) R i j *
        Fin.append y1 y2 i) =
      fun j : Fin m => ∑ i : Fin m, R i j * y1 i :=
  lsQRTallBlock_transpose_mulVec_append R y1 y2

/-- Orthogonal-coordinate transpose action for a rectangular panel.  If
    `M = Q B`, then `Mᵀ (Q y) = Bᵀ y`. -/
theorem higham21_matMulRectLeft_transpose_action_orthogonal {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (B : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) (hQ : IsOrthogonal m Q) :
    rectMatMulVec (finiteTranspose (matMulRectLeft Q B))
        (matMulVec m Q y) =
      fun j : Fin n => ∑ i : Fin m, B i j * y i := by
  ext j
  unfold rectMatMulVec finiteTranspose matMulRectLeft matMulVec
  calc
    ∑ i : Fin m, (∑ k : Fin m, Q i k * B k j) *
        (∑ l : Fin m, Q i l * y l)
        = ∑ i : Fin m, ∑ k : Fin m, ∑ l : Fin m,
            (Q i k * B k j) * (Q i l * y l) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
    _ = ∑ k : Fin m, ∑ l : Fin m, ∑ i : Fin m,
          (Q i k * B k j) * (Q i l * y l) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_comm]
    _ = ∑ k : Fin m, ∑ l : Fin m,
          (∑ i : Fin m, Q i k * Q i l) * (B k j * y l) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ∑ k : Fin m, ∑ l : Fin m,
          (if k = l then 1 else 0) * (B k j * y l) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            rw [hQ.col_orthonormal k l]
    _ = ∑ k : Fin m, B k j * y k := by
            simp [Finset.mem_univ]

/-- Multiplying by an orthogonal matrix recovers a vector from its transposed
    coordinates. -/
theorem higham21_matMulVec_orthogonal_mul_transpose {n : ℕ}
    {Q : Fin n → Fin n → ℝ} (hQ : IsOrthogonal n Q)
    (x : Fin n → ℝ) :
    matMulVec n Q (matMulVec n (matTranspose Q) x) = x := by
  ext i
  calc
    matMulVec n Q (matMulVec n (matTranspose Q) x) i
        = matMulVec n (matMul n Q (matTranspose Q)) x i := by
            exact (matMulVec_matMul n Q (matTranspose Q) x i).symm
    _ = matMulVec n (idMatrix n) x i := by
            have hmat : matMul n Q (matTranspose Q) = idMatrix n := by
              ext a b
              exact hQ.right_inv a b
            rw [hmat]
    _ = x i := by
            exact congrFun (matMulVec_id n x) i

/-- Reconstruct a vector over `Fin (p + q)` from its left and right
    `Fin.append` coordinate blocks. -/
theorem higham21_finAppend_left_right {p q : ℕ}
    (y : Fin (p + q) → ℝ) :
    Fin.append
        (fun i : Fin p => y (Fin.castAdd q i))
        (fun i : Fin q => y (Fin.natAdd p i)) =
      y := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (p + q) =>
      Fin.append
          (fun i : Fin p => y (Fin.castAdd q i))
          (fun i : Fin q => y (Fin.natAdd p i)) i = y i)
    ?left ?right i
  · intro i
    simp [Fin.append_left]
  · intro i
    simp [Fin.append_right]

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equations (21.1)-(21.3):
    exact QR-coordinate handoff for the underdetermined system.  If
    `Aᵀ = Q [R;0]`, represented here by
    `A = (Q [R;0])ᵀ`, then applying `A` to `Q[y₁;y₂]` gives the
    triangular coordinate equation `Rᵀ y₁`. -/
theorem higham21_qr_transpose_system_eq {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (y1 : Fin m → ℝ) (y2 : Fin k → ℝ) :
    rectMatMulVec
        (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
        (matMulVec (m + k) Q (Fin.append y1 y2)) =
      fun j : Fin m => ∑ i : Fin m, R i j * y1 i := by
  have hcols :=
    higham21_matMulRectLeft_transpose_action_orthogonal
      Q (lsQRTallBlock (k := k) R) (Fin.append y1 y2) hQ
  ext j
  calc
    rectMatMulVec
        (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
        (matMulVec (m + k) Q (Fin.append y1 y2)) j
        = (fun j : Fin m =>
            ∑ i : Fin (m + k), lsQRTallBlock (k := k) R i j *
              Fin.append y1 y2 i) j := by
            exact congrFun hcols j
    _ = (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) j := by
            exact congrFun (lsQRTallBlock_transpose_mulVec_append R y1 y2) j

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    source-facing algebraic wrapper for the minimum-norm coordinate choice
    in the Q method.  Among coordinate vectors with the same first block,
    setting the free second block to zero gives no larger Euclidean norm.
    This is the norm-minimization step only; the full orthogonal `Q` handoff
    and triangular solve formula remain separate selected targets. -/
theorem higham21_eq21_3_free_coordinate_zero_min_norm {m k : ℕ}
    (y1 : Fin m → ℝ) (y2 : Fin k → ℝ) :
    vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) ≤
      vecNorm2 (Fin.append y1 y2) := by
  have hzero :
      vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) = vecNorm2 y1 := by
    unfold vecNorm2
    rw [lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  calc
    vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) = vecNorm2 y1 := hzero
    _ ≤ vecNorm2 (Fin.append y1 y2) := lsVecNorm2_left_le_append y1 y2

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    source-facing lift of the free-coordinate norm-minimization step through
    the orthogonal factor `Q`.  Since orthogonal multiplication preserves the
    Euclidean norm, the vector `Q [y₁; 0]` has no larger norm than
    `Q [y₁; y₂]` for the same first coordinate block. -/
theorem higham21_eq21_3_q_factor_zero_free_block_min_norm {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (y1 : Fin m → ℝ) (y2 : Fin k → ℝ) :
    vecNorm2 (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) ≤
      vecNorm2 (matMulVec (m + k) Q (Fin.append y1 y2)) := by
  rw [vecNorm2_orthogonal Q (Fin.append y1 (0 : Fin k → ℝ)) hQ,
    vecNorm2_orthogonal Q (Fin.append y1 y2) hQ]
  exact higham21_eq21_3_free_coordinate_zero_min_norm y1 y2

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equations (21.1)-(21.3):
    exact Q-method minimum-norm handoff.  Under the supplied exact QR
    factorization `Aᵀ = Q [R;0]`, if `y₁` is the unique solution of the
    triangular coordinate equation `Rᵀ y₁ = b`, then the Q-method vector
    `Q [y₁;0]` is the minimum 2-norm solution of `A x = b`.

    This proves the QR-coordinate/minimum-norm algebra; the existence and
    triangular nonsingularity route for `R` remain separate selected targets. -/
theorem higham21_eq21_3_q_method_min_norm_of_qr_unique {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b)
    (huniq :
      ∀ z1 : Fin m → ℝ,
        (fun j : Fin m => ∑ i : Fin m, R i j * z1 i) = b → z1 = y1) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) := by
  constructor
  · rw [higham21_qr_transpose_system_eq Q hQ R y1 (0 : Fin k → ℝ), hy1]
  · intro z hz
    let y : Fin (m + k) → ℝ := matMulVec (m + k) (matTranspose Q) z
    let z1 : Fin m → ℝ := fun i => y (Fin.castAdd k i)
    let z2 : Fin k → ℝ := fun i => y (Fin.natAdd m i)
    have hy_append : Fin.append z1 z2 = y := by
      simpa [z1, z2] using higham21_finAppend_left_right (p := m) (q := k) y
    have hz_recover :
        matMulVec (m + k) Q (Fin.append z1 z2) = z := by
      rw [hy_append]
      exact higham21_matMulVec_orthogonal_mul_transpose hQ z
    have hz1_solve :
        (fun j : Fin m => ∑ i : Fin m, R i j * z1 i) = b := by
      have hAw :=
        higham21_qr_transpose_system_eq Q hQ R z1 z2
      rw [← hAw, hz_recover, hz]
    have hz1_eq : z1 = y1 := huniq z1 hz1_solve
    calc
      vecNorm2 (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)))
          = vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) := by
              exact vecNorm2_orthogonal Q (Fin.append y1 (0 : Fin k → ℝ)) hQ
      _ ≤ vecNorm2 (Fin.append z1 z2) := by
              simpa [hz1_eq] using
                higham21_eq21_3_free_coordinate_zero_min_norm y1 z2
      _ = vecNorm2 (matMulVec (m + k) Q (Fin.append z1 z2)) := by
              exact (vecNorm2_orthogonal Q (Fin.append z1 z2) hQ).symm
      _ = vecNorm2 z := by
              rw [hz_recover]

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    uniqueness of the triangular coordinate equation `Rᵀ y₁ = b` from a
    supplied inverse of `Rᵀ`. -/
theorem higham21_eq21_3_transpose_triangular_solution_unique_of_inverse {m : ℕ}
    (R RTinv : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hInv : IsInverse m (matTranspose R) RTinv)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    ∀ z1 : Fin m → ℝ,
      (fun j : Fin m => ∑ i : Fin m, R i j * z1 i) = b → z1 = y1 := by
  intro z1 hz1
  have hy1_mv : rectMatMulVec (matTranspose R) y1 = b := by
    ext j
    exact congrFun hy1 j
  have hz1_mv : rectMatMulVec (matTranspose R) z1 = b := by
    ext j
    exact congrFun hz1 j
  calc
    z1 = rectMatMulVec RTinv (rectMatMulVec (matTranspose R) z1) := by
          exact (rectMatMulVec_left_inverse_of_IsLeftInverse hInv.1 z1).symm
    _ = rectMatMulVec RTinv b := by rw [hz1_mv]
    _ = rectMatMulVec RTinv (rectMatMulVec (matTranspose R) y1) := by rw [hy1_mv]
    _ = y1 := rectMatMulVec_left_inverse_of_IsLeftInverse hInv.1 y1

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    exact Q-method minimum-norm handoff with the triangular solve uniqueness
    instantiated from an inverse of `Rᵀ`. -/
theorem higham21_eq21_3_q_method_min_norm_of_qr_inverse {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R RTinv : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hInv : IsInverse m (matTranspose R) RTinv)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) :=
  higham21_eq21_3_q_method_min_norm_of_qr_unique Q hQ R b y1 hy1
    (higham21_eq21_3_transpose_triangular_solution_unique_of_inverse
      R RTinv b y1 hInv hy1)

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    determinant-facing exact Q-method minimum-norm handoff, using the
    repository nonsingular inverse for `Rᵀ`. -/
theorem higham21_eq21_3_q_method_min_norm_of_qr_det_ne_zero {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hdetT : Matrix.det (matTranspose R : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) :=
  higham21_eq21_3_q_method_min_norm_of_qr_inverse
    Q hQ R (nonsingInv m (matTranspose R)) b y1
    (isInverse_nonsingInv_of_det_ne_zero m (matTranspose R) hdetT)
    hy1

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    determinant-facing exact Q-method minimum-norm handoff from nonsingularity
    of the triangular factor `R` itself.  This is a thin source-facing bridge
    from the usual triangular-factor determinant condition to the transposed
    coordinate solve `Rᵀ y₁ = b`. -/
theorem higham21_eq21_3_q_method_min_norm_of_qr_R_det_ne_zero {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hdet : Matrix.det (R : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) := by
  have hdetT : Matrix.det (matTranspose R : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    change Matrix.det (Matrix.transpose (R : Matrix (Fin m) (Fin m) ℝ)) ≠ 0
    simpa [Matrix.det_transpose] using hdet
  exact higham21_eq21_3_q_method_min_norm_of_qr_det_ne_zero Q hQ R b y1 hdetT hy1

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    exact Q-method minimum-norm handoff from the usual triangular-factor
    nonsingularity condition: `R` is upper triangular with nonzero diagonal. -/
theorem higham21_eq21_3_q_method_min_norm_of_qr_upper_diag_ne_zero {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hupper : IsUpperTrapezoidal m m R)
    (hdiag : ∀ i : Fin m, R i i ≠ 0)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) := by
  have hdet : Matrix.det (R : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    det_ne_zero_of_upper_triangular_diag_ne_zero m R hupper hdiag
  exact higham21_eq21_3_q_method_min_norm_of_qr_R_det_ne_zero Q hQ R b y1 hdet hy1

-- ============================================================
-- §21.2  Lemma 21.2 projector/norm bridge
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-facing alias for the projector mixture reused from the Chapter 20
    Kielbasinski--Schwetlick construction.  This is the constructed
    perturbation block, not the full minimum-norm symmetrization theorem. -/
noncomputable abbrev undetLemma21_2SymmetrizedPerturbation {m n : ℕ}
    (s : Fin m → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  lsLemma20_6Perturbation s DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the Frobenius-squared norm bound for the projector mixture used to replace
    two perturbation blocks by one. -/
theorem higham21_lemma21_2_symmetrized_perturbation_frobNormSq_le {m n : ℕ}
    (s : Fin m → ℝ) (hsq : vecNorm2Sq s ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormSqRect (undetLemma21_2SymmetrizedPerturbation s DeltaA1 DeltaA2) ≤
      frobNormSqRect DeltaA1 + frobNormSqRect DeltaA2 :=
  lsLemma20_6Perturbation_frobNormSqRect_le s hsq DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Frobenius-norm form of the printed bound
    `||Delta A||_F <= (||Delta A_1||_F^2 + ||Delta A_2||_F^2)^(1/2)` for the
    projector mixture. -/
theorem higham21_lemma21_2_symmetrized_perturbation_frob_bound {m n : ℕ}
    (s : Fin m → ℝ) (hsq : vecNorm2Sq s ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormRect (undetLemma21_2SymmetrizedPerturbation s DeltaA1 DeltaA2) ≤
      Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) :=
  lsLemma20_6Perturbation_norm_bound_two_frob s hsq DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-2 norm form of the printed bound for the projector mixture.  If
    the two original perturbation blocks have operator-2 bounds `alpha` and
    `beta`, then the constructed perturbation has bound
    `(alpha^2 + beta^2)^(1/2)`. -/
theorem higham21_lemma21_2_symmetrized_perturbation_op_bound {m n : ℕ}
    (s : Fin m → ℝ) (hsq : vecNorm2Sq s ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    rectOpNorm2Le (undetLemma21_2SymmetrizedPerturbation s DeltaA1 DeltaA2)
      (Real.sqrt (alpha ^ 2 + beta ^ 2)) :=
  lsLemma20_6Perturbation_norm_bound_two_operator
    s hsq DeltaA1 DeltaA2 halpha hbeta hDeltaA1 hDeltaA2

-- ============================================================
-- §21.3  Row-wise backward error for underdetermined systems
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    a row-wise backward-error witness for an underdetermined system.

    The computed vector `x_hat` is the exact minimum 2-norm solution of the
    row-wise perturbed rectangular system `(A + ΔA) x = b`, and each row
    perturbation is bounded relative to the corresponding row of `A` in the
    Euclidean norm. -/
structure UndetRowwiseBackwardErrorFeasible (m n : ℕ)
    (A ΔA : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    (eta : ℝ) : Prop where
  /-- The row-wise error factor is nonnegative. -/
  eta_nonneg : 0 ≤ eta
  /-- `x_hat` is the minimum 2-norm solution of the perturbed system. -/
  min_norm :
    RectMinNormSolution m n (fun i j => A i j + ΔA i j) b x_hat
  /-- Each row perturbation is bounded by `eta` times the original row norm. -/
  row_bound : ∀ i : Fin m, rectRowNorm2 ΔA i ≤ eta * rectRowNorm2 A i

/-- Existence form of the Chapter 21 row-wise backward-error predicate. -/
def UndetRowwiseBackwardErrorBounded (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    (eta : ℝ) : Prop :=
  ∃ ΔA : Fin m → Fin n → ℝ,
    UndetRowwiseBackwardErrorFeasible m n A ΔA b x_hat eta

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    source-facing constructor for a row-wise backward-error certificate.
    This packages the definition used by Theorem 21.4; it does not by itself
    prove that a particular QR implementation supplies such a witness. -/
theorem higham21_rowwise_backward_error_bound_witness
    (m n : ℕ)
    (A ΔA : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    (eta : ℝ)
    (heta : 0 ≤ eta)
    (hmin :
      RectMinNormSolution m n (fun i j => A i j + ΔA i j) b x_hat)
    (hrow : ∀ i : Fin m, rectRowNorm2 ΔA i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat eta :=
  ⟨ΔA, ⟨heta, hmin, hrow⟩⟩

-- ============================================================
-- §21.2  Theorem 21.3: normwise backward-error model
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    feasibility predicate for the normwise Frobenius backward error
    `eta_F(y)` of an approximate minimum 2-norm underdetermined solution.

    This reuses the Chapter 20 weighted Frobenius perturbation cost
    `||[DeltaA, theta Delta b]||_F`; the Ch21-specific change is that `y`
    must be a minimum 2-norm solution of the perturbed rectangular system. -/
def UndetNormwiseBackwardErrorFeasible {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) : Prop :=
  RectMinNormSolution m n
    (fun i j => A i j + DeltaA i j)
    (fun i => b i + Deltab i) y

/-- Attainable weighted Frobenius costs in the Chapter 21 Theorem 21.3
    normwise backward-error definition. -/
noncomputable def undetNormwiseBackwardErrorValuesF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : Set ℝ :=
  {eta | ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
    UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
      eta = lsNormwiseBackwardErrorCostF theta DeltaA Deltab}

/-- Infimum model of Higham Chapter 21 Theorem 21.3's normwise backward
    error `eta_F(y)`.  The source writes a minimum and gives the Sun-Sun
    closed formula; those attainment and singular-value formula rows remain
    separate selected targets. -/
noncomputable def undetNormwiseBackwardErrorEtaF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  sInf (undetNormwiseBackwardErrorValuesF theta A b y)

/-- The Chapter 21 attainable-cost set is bounded below by zero. -/
theorem undetNormwiseBackwardErrorValuesF.bddBelow {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    BddBelow (undetNormwiseBackwardErrorValuesF theta A b y) := by
  refine ⟨0, ?_⟩
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, _hfeas, rfl⟩
  exact lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab

/-- The Chapter 21 normwise backward-error infimum model is nonnegative. -/
theorem undetNormwiseBackwardErrorEtaF_nonneg {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    0 ≤ undetNormwiseBackwardErrorEtaF theta A b y := by
  unfold undetNormwiseBackwardErrorEtaF
  apply Real.sInf_nonneg
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, _hfeas, rfl⟩
  exact lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab

/-- Any feasible Chapter 21 normwise perturbation gives an upper bound on
    the infimum model `eta_F(y)`. -/
theorem undetNormwiseBackwardErrorEtaF_le_costF_of_feasible
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hfeas :
      UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    undetNormwiseBackwardErrorEtaF theta A b y ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  unfold undetNormwiseBackwardErrorEtaF
  exact csInf_le (undetNormwiseBackwardErrorValuesF.bddBelow theta A b y)
    ⟨DeltaA, Deltab, hfeas, rfl⟩

/-- Zero is an attainable Chapter 21 normwise backward-error cost when `y`
    is already a minimum 2-norm solution of the original data. -/
theorem undetNormwiseBackwardErrorValuesF.zero_mem_of_rectMinNormSolution
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (hmin : RectMinNormSolution m n A b y) :
    (0 : ℝ) ∈ undetNormwiseBackwardErrorValuesF theta A b y := by
  rw [← lsNormwiseBackwardErrorCostF_zero (m := m) (n := n) theta]
  refine ⟨(0 : Fin m → Fin n → ℝ), (0 : Fin m → ℝ), ?_, rfl⟩
  simpa [UndetNormwiseBackwardErrorFeasible] using hmin

/-- If `y` is already a minimum 2-norm solution of the original data, then
    the Chapter 21 infimum model gives zero backward error. -/
theorem undetNormwiseBackwardErrorEtaF_eq_zero_of_rectMinNormSolution
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (hmin : RectMinNormSolution m n A b y) :
    undetNormwiseBackwardErrorEtaF theta A b y = 0 := by
  apply le_antisymm
  · unfold undetNormwiseBackwardErrorEtaF
    exact csInf_le (undetNormwiseBackwardErrorValuesF.bddBelow theta A b y)
      (undetNormwiseBackwardErrorValuesF.zero_mem_of_rectMinNormSolution
        theta A b y hmin)
  · exact undetNormwiseBackwardErrorEtaF_nonneg theta A b y

/-- In the Chapter 21 Theorem 21.3 weighted Frobenius model, perturbing only
    the right-hand side by `-b` has cost `theta * ||b||_2`, for nonnegative
    source weight `theta`. -/
theorem undetNormwiseBackwardErrorCostF_zero_deltaA_neg_deltab
    {m n : ℕ} (theta : ℝ) (htheta : 0 ≤ theta) (b : Fin m → ℝ) :
    lsNormwiseBackwardErrorCostF (m := m) (n := n) theta
      (0 : Fin m → Fin n → ℝ) (fun i => -b i) = theta * vecNorm2 b := by
  have hleft : 0 ≤ lsNormwiseBackwardErrorCostF theta
      (0 : Fin m → Fin n → ℝ) (fun i => -b i) :=
    lsNormwiseBackwardErrorCostF_nonneg theta
      (0 : Fin m → Fin n → ℝ) (fun i => -b i)
  have hright : 0 ≤ theta * vecNorm2 b :=
    mul_nonneg htheta (vecNorm2_nonneg b)
  apply (sq_eq_sq₀ hleft hright).mp
  rw [lsNormwiseBackwardErrorCostF_sq]
  rw [show frobNormSqRect (0 : Fin m → Fin n → ℝ) = 0 by
    simp [frobNormSqRect]]
  have hneg : vecNorm2Sq (fun i : Fin m => -b i) = vecNorm2Sq b := by
    unfold vecNorm2Sq
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hneg]
  rw [show (theta * vecNorm2 b) ^ 2 = theta ^ 2 * vecNorm2 b ^ 2 by ring]
  rw [vecNorm2_sq]
  ring

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    the source zero-vector candidate `y = 0` has attainable cost
    `theta * ||b||_2` in the underdetermined normwise backward-error model. -/
theorem undetNormwiseBackwardErrorValuesF.theta_vecNorm_mem_zero
    {m n : ℕ} (theta : ℝ) (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    theta * vecNorm2 b ∈
      undetNormwiseBackwardErrorValuesF theta A b (0 : Fin n → ℝ) := by
  refine ⟨(0 : Fin m → Fin n → ℝ), (fun i => -b i), ?_, ?_⟩
  · unfold UndetNormwiseBackwardErrorFeasible
    constructor
    · ext i
      simp [rectMatMulVec]
    · intro z _hz
      change vecNorm2 (fun _ : Fin n => 0) ≤ vecNorm2 z
      rw [vecNorm2_zero]
      exact vecNorm2_nonneg z
  · exact (undetNormwiseBackwardErrorCostF_zero_deltaA_neg_deltab
      theta htheta b).symm

/-- Any feasible perturbation for the Chapter 21 zero-vector candidate must
    pay at least the weighted right-hand-side cost `theta * ||b||_2`. -/
theorem undetNormwiseBackwardErrorCostF_ge_theta_vecNorm_of_zero_feasible
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hfeas :
      UndetNormwiseBackwardErrorFeasible A b (0 : Fin n → ℝ) DeltaA Deltab) :
    theta * vecNorm2 b ≤ lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  have hDeltab : Deltab = fun i : Fin m => -b i := by
    ext i
    have hi := congrFun hfeas.system_eq i
    have hzero : (0 : ℝ) = b i + Deltab i := by
      simpa [rectMatMulVec] using hi
    linarith
  have hweighted : theta * vecNorm2 Deltab ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
    lsNormwiseBackwardErrorCostF_weighted_deltab_le htheta DeltaA Deltab
  simpa [hDeltab, vecNorm2_neg] using hweighted

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    zero-vector branch of the Sun--Sun normwise Frobenius backward-error
    formula, `eta_F(0) = theta * ||b||_2`, stated for nonnegative `theta`.
    The nonzero singular-value formula remains a separate selected target. -/
theorem higham21_thm21_3_etaF_zero
    {m n : ℕ} (theta : ℝ) (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    undetNormwiseBackwardErrorEtaF theta A b (0 : Fin n → ℝ) =
      theta * vecNorm2 b := by
  apply le_antisymm
  · unfold undetNormwiseBackwardErrorEtaF
    exact csInf_le
      (undetNormwiseBackwardErrorValuesF.bddBelow theta A b (0 : Fin n → ℝ))
      (undetNormwiseBackwardErrorValuesF.theta_vecNorm_mem_zero theta htheta A b)
  · unfold undetNormwiseBackwardErrorEtaF
    apply le_csInf
    · exact ⟨theta * vecNorm2 b,
        undetNormwiseBackwardErrorValuesF.theta_vecNorm_mem_zero theta htheta A b⟩
    · intro eta heta
      rcases heta with ⟨DeltaA, Deltab, hfeas, rfl⟩
      exact undetNormwiseBackwardErrorCostF_ge_theta_vecNorm_of_zero_feasible
        htheta A b DeltaA Deltab hfeas

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    residual for an approximate underdetermined solution, using the source
    sign convention `r = b - A y`. -/
noncomputable def undetResidualHigham {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    Fin m → ℝ :=
  fun i => b i - rectMatMulVec A y i

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    source-facing model of `I - y y^+` in the nonzero-`y` branch.  This reuses
    the Chapter 20 rank-one complement-projector infrastructure. -/
noncomputable abbrev undetApproxComplementProjector {n : ℕ}
    (y : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  lsResidualComplementProjector y

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    source matrix `A(I - y y^+)` appearing in the nonzero Sun--Sun formula. -/
noncomputable def undetNormwiseBackwardErrorFormulaMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  rectMatMul A (undetApproxComplementProjector y)

/-- Entry expansion of the Chapter 21 source matrix `A(I - y y^+)`. -/
theorem undetNormwiseBackwardErrorFormulaMatrix_apply {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (i : Fin m) (j : Fin n) :
    undetNormwiseBackwardErrorFormulaMatrix A y i j =
      ∑ k : Fin n, A i k *
        (idMatrix n k j - y k * y j / vecNorm2Sq y) := by
  rfl

/-- Applying the Chapter 21 source matrix `A(I - y y^+)` is the same as first
    projecting with `I - y y^+`, then applying `A`. -/
theorem undetNormwiseBackwardErrorFormulaMatrix_mulVec_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y x : Fin n → ℝ) :
    rectMatMulVec (undetNormwiseBackwardErrorFormulaMatrix A y) x =
      rectMatMulVec A (rectMatMulVec (undetApproxComplementProjector y) x) := by
  rw [undetNormwiseBackwardErrorFormulaMatrix, rectMatMulVec_rectMatMul]

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    the source matrix `A(I - y y^+)` annihilates the nonzero candidate
    direction `y`. -/
theorem higham21_thm21_3_formulaMatrix_mulVec_candidate_eq_zero
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ)
    (hysq : vecNorm2Sq y ≠ 0) :
    rectMatMulVec (undetNormwiseBackwardErrorFormulaMatrix A y) y = 0 := by
  have hcomp : rectMatMulVec (undetApproxComplementProjector y) y = 0 := by
    simpa [undetApproxComplementProjector, rectMatMulVec, matMulVec] using
      (lsResidualComplementProjector_mulVec_residual y hysq)
  rw [undetNormwiseBackwardErrorFormulaMatrix_mulVec_eq A y y, hcomp]
  ext i
  simp [rectMatMulVec]

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    scalar right-hand side of the nonzero Sun--Sun formula, parameterized by
    the smallest singular value of `A(I - y y^+)`.  Proving that this equals
    `eta_F(y)` remains the open singular-value branch. -/
noncomputable def undetNormwiseBackwardErrorNonzeroFormulaRHS {m n : ℕ}
    (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (sigma : ℝ) : ℝ :=
  Real.sqrt
    (theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) *
        (vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y) +
      sigma ^ 2)

/-- Radicand nonnegativity for the scalar right-hand side in the nonzero
    branch of Higham Chapter 21, Theorem 21.3.  This is only scalar formula
    bookkeeping; it does not assert the Sun--Sun equality with `eta_F(y)`. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_radicand_nonneg
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (sigma : ℝ) :
    0 ≤
      theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) *
          (vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y) +
        sigma ^ 2 := by
  have htheta_sq : 0 ≤ theta ^ 2 := sq_nonneg theta
  have hy_sq : 0 ≤ vecNorm2Sq y := vecNorm2Sq_nonneg y
  have hnum : 0 ≤ theta ^ 2 * vecNorm2Sq y := mul_nonneg htheta_sq hy_sq
  have hden : 0 ≤ 1 + theta ^ 2 * vecNorm2Sq y := by
    exact add_nonneg zero_le_one hnum
  have hleft :
      0 ≤ theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) :=
    div_nonneg hnum hden
  have hres :
      0 ≤ vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y :=
    div_nonneg (vecNorm2Sq_nonneg _) hy_sq
  exact add_nonneg (mul_nonneg hleft hres) (sq_nonneg sigma)

/-- The scalar right-hand side in the nonzero branch of Higham Chapter 21,
    Theorem 21.3 is nonnegative. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_nonneg
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (sigma : ℝ) :
    0 ≤ undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  unfold undetNormwiseBackwardErrorNonzeroFormulaRHS
  exact Real.sqrt_nonneg _

/-- Squared form of the scalar right-hand side in the nonzero branch of
    Higham Chapter 21, Theorem 21.3.  This prepares the later lower/upper
    bound route against the Sun--Sun formula but does not close it. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_sq
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (sigma : ℝ) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma ^ 2 =
      theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) *
          (vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y) +
        sigma ^ 2 := by
  unfold undetNormwiseBackwardErrorNonzeroFormulaRHS
  exact Real.sq_sqrt
    (undetNormwiseBackwardErrorNonzeroFormulaRHS_radicand_nonneg
      theta A b y sigma)

/-- Positive singular-value branch of the scalar right-hand side in Higham
    Chapter 21, Theorem 21.3: a positive supplied singular-value parameter
    makes the displayed formula positive. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_pos_of_sigma_pos
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  unfold undetNormwiseBackwardErrorNonzeroFormulaRHS
  apply Real.sqrt_pos.2
  have hsigma_sq_pos : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have hleft :
      0 ≤ theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) *
          (vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y) := by
    have htheta_sq : 0 ≤ theta ^ 2 := sq_nonneg theta
    have hy_sq : 0 ≤ vecNorm2Sq y := vecNorm2Sq_nonneg y
    have hnum : 0 ≤ theta ^ 2 * vecNorm2Sq y := mul_nonneg htheta_sq hy_sq
    have hden : 0 ≤ 1 + theta ^ 2 * vecNorm2Sq y :=
      add_nonneg zero_le_one hnum
    have hleft_factor :
        0 ≤ theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) :=
      div_nonneg hnum hden
    have hres :
        0 ≤ vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y :=
      div_nonneg (vecNorm2Sq_nonneg _) hy_sq
    exact mul_nonneg hleft_factor hres
  exact add_pos_of_nonneg_of_pos hleft hsigma_sq_pos

/-- Lower-bound handoff for the nonzero branch of Higham Chapter 21,
    Theorem 21.3: once every feasible perturbation has cost at least the
    displayed nonzero RHS, the RHS is below the infimum model `eta_F(y)`.
    The singular-vector proof of that pointwise lower bound remains open. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_forall_feasible_cost_ge
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (y : Fin n → ℝ) (sigma : ℝ)
    (hnonempty : (undetNormwiseBackwardErrorValuesF theta A b y).Nonempty)
    (hlower :
      ∀ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab →
          undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma ≤
            lsNormwiseBackwardErrorCostF theta DeltaA Deltab) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma ≤
      undetNormwiseBackwardErrorEtaF theta A b y := by
  unfold undetNormwiseBackwardErrorEtaF
  apply le_csInf hnonempty
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, hfeas, heta_eq⟩
  rw [heta_eq]
  exact hlower DeltaA Deltab hfeas

/-- Upper-bound handoff for the nonzero branch of Higham Chapter 21,
    Theorem 21.3: an attaining feasible perturbation gives
    `eta_F(y) <=` the displayed nonzero RHS. -/
theorem undetNormwiseBackwardErrorEtaF_le_nonzeroFormulaRHS_of_exists_feasible_cost_eq
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (y : Fin n → ℝ) (sigma : ℝ)
    (hatt :
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
            undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma) :
    undetNormwiseBackwardErrorEtaF theta A b y ≤
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  rcases hatt with ⟨DeltaA, Deltab, hfeas, hcost⟩
  calc
    undetNormwiseBackwardErrorEtaF theta A b y ≤
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
      undetNormwiseBackwardErrorEtaF_le_costF_of_feasible
        theta A b y DeltaA Deltab hfeas
    _ = undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := hcost

/-- Inequality-form upper-bound handoff for the nonzero branch of Higham
    Chapter 21, Theorem 21.3: it is enough to exhibit a feasible perturbation
    whose weighted cost is bounded by the displayed nonzero RHS. -/
theorem undetNormwiseBackwardErrorEtaF_le_nonzeroFormulaRHS_of_exists_feasible_cost_le
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (y : Fin n → ℝ) (sigma : ℝ)
    (hupper :
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab ≤
            undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma) :
    undetNormwiseBackwardErrorEtaF theta A b y ≤
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  rcases hupper with ⟨DeltaA, Deltab, hfeas, hcost⟩
  exact
    (undetNormwiseBackwardErrorEtaF_le_costF_of_feasible
      theta A b y DeltaA Deltab hfeas).trans hcost

/-- Certificate form of the open nonzero equality in Higham Chapter 21,
    Theorem 21.3.  It isolates the two remaining obligations for the
    Sun--Sun proof: a pointwise lower bound for all feasible perturbations
    and one feasible perturbation attaining the displayed nonzero RHS. -/
theorem undetNormwiseBackwardErrorEtaF_eq_nonzeroFormulaRHS_of_formula_certificate
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (y : Fin n → ℝ) (sigma : ℝ)
    (hnonempty : (undetNormwiseBackwardErrorValuesF theta A b y).Nonempty)
    (hlower :
      ∀ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab →
          undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma ≤
            lsNormwiseBackwardErrorCostF theta DeltaA Deltab)
    (hatt :
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
            undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma) :
    undetNormwiseBackwardErrorEtaF theta A b y =
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  exact le_antisymm
    (undetNormwiseBackwardErrorEtaF_le_nonzeroFormulaRHS_of_exists_feasible_cost_eq
      theta A b y sigma hatt)
    (undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_forall_feasible_cost_ge
      theta A b y sigma hnonempty hlower)

-- ============================================================
-- §21.3  Theorem 21.4: Q method backward stability
-- ============================================================

/-- **Theorem 21.4** (Higham): The Q method for underdetermined systems
    is row-wise backward stable.

    The Q method solves Rᵀy₁ = b and forms x = Q[y₁; 0]ᵀ using
    the QR factorization Aᵀ = Q[R; 0]. The computed x̂ is the
    minimum 2-norm solution to (A + ΔA)x = b, where:

    ‖ΔA‖_F ≤ mγ_{cn}‖A‖_F  (normwise)
    |ΔA| ≤ mnγ_{cn}|A|G, ‖G‖_F = 1  (componentwise)

    Note: b is not perturbed (unlike the least-squares QR result in
    Theorem 20.3).

    Recorded as an abstract predicate until the rectangular QR factorization
    bridge and Lemma 21.2 symmetrization route are fully formalized. -/
structure QMethodBackwardStable (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (b y_hat : Fin m → ℝ)
    (c_bound : ℝ) : Prop where
  /-- c_bound is nonneg. -/
  bound_nonneg : 0 ≤ c_bound
  /-- The computed ŷ satisfies perturbed normal equations
      (AAᵀ + ΔG)ŷ = b with bounded ΔG.
      This captures the Q method's backward stability projected
      to the m×m Gram system AAᵀ. -/
  result : ∃ (ΔG : Fin m → Fin m → ℝ),
    (∀ i, matMulVec m (fun a b => AAT a b + ΔG a b) y_hat i = b i) ∧
    frobNorm ΔG ≤ c_bound

-- ============================================================
-- §21.3  SNE method backward error
-- ============================================================

/-- **SNE method backward error for underdetermined systems** (Higham §21.3).

    The SNE method solves RᵀRy = b where Aᵀ = Q[R; 0], then forms
    x = Aᵀy. The solve RᵀRy = b is equivalent to Cholesky-solving
    the m×m system AAᵀy = b (since AAᵀ = RᵀR for the exact R).

    The backward error of the Cholesky solve gives:
    (RᵀR + ΔC)ŷ = b where |ΔC| ≤ (γ(m+1) + 2γ(m) + γ(m)²)·|R̂ᵀ||R̂|

    This is a direct application of `cholesky_solve_backward_error_expanded`
    from CholeskySolve.lean with n := m (the Gram matrix is m×m). -/
theorem sne_backward_error (fp : FPModel) (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (hR_diag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m AAT R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1)) :
    let R_hatT := fun i j : Fin m => R_hat j i
    let y_hat := fl_forwardSub fp m R_hatT b
    let x_hat := fl_backSub fp m R_hat y_hat
    ∃ ΔC : Fin m → Fin m → ℝ,
      (∀ i j, |ΔC i j| ≤
        (gamma fp (m + 1) + 2 * gamma fp m + gamma fp m ^ 2) *
          ∑ k : Fin m, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * x_hat j = b i) :=
  cholesky_solve_backward_error_expanded fp m AAT R_hat b hR_diag hChol hm1

-- ============================================================
-- §21.3  Forward error bound (eq. 21.11)
-- ============================================================

/-- **Forward error for underdetermined system solve** (Higham §21.3, eq. 21.11).

    For both the Q method and SNE method, the forward error satisfies:
    ‖x̂ − x‖₂/‖x‖₂ ≤ mnγ'_{cn} · cond₂(A) + O(u²)

    where cond₂(A) = ‖|A⁺||A|‖₂. Note this bound is independent
    of the row scaling of A.

    We prove the componentwise form: given backward error in the
    m×m Gram system, the forward error is bounded by
    |ŷ − y| ≤ |(AAᵀ)⁻¹| · |ΔG · ŷ|.

    This reuses `normwise_perturbation_bound` (Theorem 7.2) from
    PerturbationTheory.lean, noting that Δb = 0 for the Q method
    (the right-hand side b is not perturbed). -/
theorem underdetermined_forward_error (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔG : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, matMulVec m (fun a c => AAT a c + ΔG a c) y_hat i = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔG j k| * |y_hat k| := by
  -- Since Δb = 0, the bound from Theorem 7.2 simplifies to
  -- |ŷ − y| ≤ |(AAᵀ)⁻¹| · (|ΔG|·|ŷ| + 0)
  -- We apply normwise_perturbation_bound with Δb := 0.
  let Δb : Fin m → ℝ := fun _ => 0
  have hPerturbed' : ∀ i, ∑ j, (AAT i j + ΔG i j) * y_hat j = b i + Δb i := by
    intro i; simp [Δb]; exact hPerturbed i
  have hExact' : ∀ i, ∑ j, AAT i j * y j = b i := fun i => hExact i
  have hBound := normwise_perturbation_bound m AAT AAT_inv y y_hat b ΔG Δb
    hInv.1 hExact' hPerturbed'
  intro i
  rw [abs_sub_comm]
  have h := hBound i
  -- Simplify: |Δb_j| = 0, so ∑|ΔG|·|ŷ| + |Δb| = ∑|ΔG|·|ŷ| + 0
  calc |y i - y_hat i|
      ≤ ∑ j, |AAT_inv i j| * (∑ k, |ΔG j k| * |y_hat k| + |Δb j|) := h
    _ = ∑ j, |AAT_inv i j| * (∑ k, |ΔG j k| * |y_hat k| + 0) := by
        simp [Δb]
    _ = ∑ j, |AAT_inv i j| * ∑ k, |ΔG j k| * |y_hat k| := by
        apply Finset.sum_congr rfl; intro j _; ring_nf

/-- **SNE method is NOT backward stable** (Higham §21.3, remark).

    Unlike the Q method (Theorem 21.4), the SNE method does not
    guarantee that x̂ is the minimum 2-norm solution to a nearby
    system. The SNE only guarantees a small residual in the normal
    equations RᵀRŷ ≈ b.

    However, both methods achieve the same forward error bound (eq. 21.11):
    ‖x̂−x‖₂/‖x‖₂ ≤ mnγ'_{cn} · cond₂(A) + O(u²)

    This means the forward error from SNE is as good as from Q method,
    even though the backward error characterization is weaker. -/
theorem sne_forward_error_matches_q_method
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔC : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * y_hat j = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔC j k| * |y_hat k| := by
  -- Same proof as underdetermined_forward_error: apply Theorem 7.2 with Δb = 0
  have hPert' : ∀ i, matMulVec m (fun a c => AAT a c + ΔC a c) y_hat i = b i :=
    fun i => hPerturbed i
  exact underdetermined_forward_error m AAT AAT_inv hInv b y y_hat hExact ΔC hPert'

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.11):
    source-facing wrapper for the currently formalized Gram-system forward
    perturbation consequence.  This is not the full printed asymptotic
    `mn * gamma * cond_2(A) + O(u^2)` bound; it is the exact componentwise
    perturbation inequality used as a dependency for that row. -/
theorem higham21_eq21_11_gram_forward_error
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔG : Fin m → Fin m → ℝ)
    (hPerturbed :
      ∀ i, matMulVec m (fun a c => AAT a c + ΔG a c) y_hat i = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔG j k| * |y_hat k| :=
  underdetermined_forward_error m AAT AAT_inv hInv b y y_hat hExact ΔG hPerturbed

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    source-facing wrapper for the proved statement that the SNE Gram-system
    perturbation route has the same componentwise forward-error consequence as
    the Q-method Gram-system route.  The full source statement still requires
    instantiating the QR/SNE computed-object bounds. -/
theorem higham21_sne_gram_forward_error_matches_q_method
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔC : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * y_hat j = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔC j k| * |y_hat k| :=
  sne_forward_error_matches_q_method m AAT AAT_inv hInv b y y_hat hExact ΔC
    hPerturbed

end LeanFpAnalysis.FP
