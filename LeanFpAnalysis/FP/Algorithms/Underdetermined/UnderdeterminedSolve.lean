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
import LeanFpAnalysis.FP.Analysis.HighamChapter7
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySolve
import LeanFpAnalysis.FP.Algorithms.QR.Higham19
import LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt
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

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equations (21.1) and (21.5):
    the Gram matrix of `(Q B)ᵀ` is the right Gram matrix of `B` when `Q` is
    orthogonal.  This is the algebraic cancellation behind deriving the SNE
    matrix from the QR representation `Aᵀ = Q B`. -/
theorem higham21_rectGram_finiteTranspose_matMulRectLeft_orthogonal {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (B : Fin m → Fin n → ℝ)
    (hQ : IsOrthogonal m Q) :
    rectGram (finiteTranspose (matMulRectLeft Q B)) =
      fun i j : Fin n => ∑ r : Fin m, B r i * B r j := by
  ext i j
  unfold rectGram finiteTranspose matMulRectLeft
  calc
    ∑ row : Fin m, (∑ a : Fin m, Q row a * B a i) *
        (∑ b : Fin m, Q row b * B b j)
        = ∑ row : Fin m, ∑ a : Fin m, ∑ b : Fin m,
            (Q row a * B a i) * (Q row b * B b j) := by
            apply Finset.sum_congr rfl
            intro row _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
    _ = ∑ a : Fin m, ∑ b : Fin m, ∑ row : Fin m,
          (Q row a * Q row b) * (B a i * B b j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro row _
            ring
    _ = ∑ a : Fin m, ∑ b : Fin m,
          (∑ row : Fin m, Q row a * Q row b) * (B a i * B b j) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_mul]
    _ = ∑ a : Fin m, ∑ b : Fin m,
          (if a = b then 1 else 0) * (B a i * B b j) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [hQ.col_orthonormal a b]
    _ = ∑ a : Fin m, B a i * B a j := by
            simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.5):
    the right Gram matrix of the tall block `[R;0]` is `RᵀR`. -/
theorem higham21_eq21_5_tall_block_right_gram {m k : ℕ}
    (R : Fin m → Fin m → ℝ) :
    (fun i j : Fin m =>
        ∑ row : Fin (m + k),
          lsQRTallBlock (k := k) R row i * lsQRTallBlock (k := k) R row j) =
      fun i j : Fin m => ∑ row : Fin m, R row i * R row j := by
  ext i j
  unfold lsQRTallBlock
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.5):
    if `Aᵀ = Q [R;0]` with `Q` orthogonal, then the SNE matrix
    `A Aᵀ` is `RᵀR`.  The theorem is stated for the exact rectangular matrix
    represented in this development as `A = (Q [R;0])ᵀ`. -/
theorem higham21_eq21_5_qr_sne_gram_eq {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ) :
    rectGram (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))) =
      fun i j : Fin m => ∑ row : Fin m, R row i * R row j := by
  calc
    rectGram (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
        = (fun i j : Fin m =>
            ∑ row : Fin (m + k),
              lsQRTallBlock (k := k) R row i *
                lsQRTallBlock (k := k) R row j) := by
            exact
              higham21_rectGram_finiteTranspose_matMulRectLeft_orthogonal
                Q (lsQRTallBlock (k := k) R) hQ
    _ = fun i j : Fin m => ∑ row : Fin m, R row i * R row j :=
            higham21_eq21_5_tall_block_right_gram (k := k) R

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.5):
    QR-specialized SNE formation step.  Under `Aᵀ = Q[R;0]`, a vector `y`
    solving `RᵀR y = b`, followed by `x = Aᵀ y`, solves `A x = b`. -/
theorem higham21_eq21_5_sne_rect_transpose_solution_of_qr {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R SNE : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (x : Fin (m + k) → ℝ)
    (hSNE : ∀ i j : Fin m, SNE i j = ∑ row : Fin m, R row i * R row j)
    (hy : ∀ i : Fin m, matMulVec m SNE y i = b i)
    (hx :
      x = rectTransposeMulVec
        (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))) y) :
    rectMatMulVec
        (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))) x =
      b := by
  let A : Fin m → Fin (m + k) → ℝ :=
    finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))
  have hgram := higham21_eq21_5_qr_sne_gram_eq Q hQ R
  have hSNEgram : ∀ i j : Fin m, SNE i j = rectGram A i j := by
    intro i j
    calc
      SNE i j = ∑ row : Fin m, R row i * R row j := hSNE i j
      _ = rectGram A i j := by
          exact (congrFun (congrFun hgram i) j).symm
  exact higham21_eq21_5_sne_rect_transpose_solution A SNE b y x hSNEgram hy hx

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.5):
    QR-specialized SNE minimum-norm handoff.  Under `Aᵀ = Q[R;0]`, solving
    `RᵀR y = b` and forming `x = Aᵀ y` gives the minimum 2-norm solution of
    the exact underdetermined system. -/
theorem higham21_eq21_5_sne_rect_transpose_min_norm_of_qr {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R SNE : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hSNE : ∀ i j : Fin m, SNE i j = ∑ row : Fin m, R row i * R row j)
    (hy : ∀ i : Fin m, matMulVec m SNE y i = b i) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (rectTransposeMulVec
        (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))) y) := by
  let A : Fin m → Fin (m + k) → ℝ :=
    finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))
  exact higham21_eq21_4_rect_transpose_min_norm_of_solves A b y
    (higham21_eq21_5_sne_rect_transpose_solution_of_qr
      Q hQ R SNE b y (rectTransposeMulVec A y) hSNE hy rfl)

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
    source-facing right-projector mixture for the Kielbasinski--Schwetlick
    construction.  The projector acts on the solution vector `x`, as in the
    printed formula `DeltaA = DeltaA1 P + DeltaA2 (I - P)`.  This is the
    constructed perturbation block, not the full minimum-norm symmetrization
    theorem. -/
noncomputable abbrev undetLemma21_2SymmetrizedPerturbation {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  finiteTranspose
    (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1))

/-- Nonzero vectors have nonzero squared Euclidean norm.  This local helper lets
    the Chapter 21 Lemma 21.2 wrapper branch on the source proof's `x = 0`
    case while feeding the existing nonzero beta/projector route. -/
theorem higham21_vecNorm2Sq_ne_zero_of_ne_zero {n : ℕ}
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    vecNorm2Sq x ≠ 0 := by
  intro hsq
  apply hx
  ext i
  have hall :
      ∀ j : Fin n, j ∈ (Finset.univ : Finset (Fin n)) →
        x j ^ 2 = 0 := by
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun j : Fin n => x j ^ 2)
        (by intro j _; exact sq_nonneg (x j))).mp
        (by simpa [vecNorm2Sq] using hsq)
  have hxi2 : x i ^ 2 = 0 := hall i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hxi2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-case perturbation.  The proof takes `DeltaA = DeltaA2` when the
    candidate solution `x` is zero; otherwise it uses the right-projector
    mixture already represented by `undetLemma21_2SymmetrizedPerturbation`. -/
noncomputable def undetLemma21_2SinglePerturbation {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  if x = 0 then DeltaA2 else undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the transposed Chapter 20 construction is exactly the right-projector
    mixture `DeltaA1 P + DeltaA2 (I - P)` used in the proof. -/
theorem higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j =
      matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j +
        matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j := by
  have hmix :=
    lsLemma20_6Perturbation_eq_projector_mixture
      x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1) j i
  have hrightQ :
      matMulRectLeft (lsLemma20_6ProjectorComplement x) (finiteTranspose DeltaA2) j i =
        matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j := by
    unfold matMulRectLeft matMulRectRight finiteTranspose
    apply Finset.sum_congr rfl
    intro k _
    rw [lsLemma20_6ProjectorComplement_symmetric x j k]
    ring
  have hrightP :
      matMulRectLeft (lsLemma20_6Projector x) (finiteTranspose DeltaA1) j i =
        matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j := by
    unfold matMulRectLeft matMulRectRight finiteTranspose
    apply Finset.sum_congr rfl
    intro k _
    rw [lsLemma20_6Projector_symmetric x j k]
    ring
  calc
    undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j =
        lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1) j i := rfl
    _ = matMulRectLeft (lsLemma20_6ProjectorComplement x) (finiteTranspose DeltaA2) j i +
          matMulRectLeft (lsLemma20_6Projector x) (finiteTranspose DeltaA1) j i := hmix
    _ = matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j +
          matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j := by
          rw [hrightQ, hrightP]
    _ = matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j +
          matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j := by
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the two source perturbation slots are the same matrix, then the
    source-case single perturbation collapses back to that matrix. -/
theorem higham21_lemma21_2_single_perturbation_same {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA : Fin m → Fin n → ℝ) :
    undetLemma21_2SinglePerturbation x DeltaA DeltaA = DeltaA := by
  by_cases hx : x = 0
  · simp [undetLemma21_2SinglePerturbation, hx]
  · ext i j
    calc
      undetLemma21_2SinglePerturbation x DeltaA DeltaA i j =
          undetLemma21_2SymmetrizedPerturbation x DeltaA DeltaA i j := by
            simp [undetLemma21_2SinglePerturbation, hx]
      _ =
          matMulRectRight DeltaA (lsLemma20_6Projector x) i j +
            matMulRectRight DeltaA (lsLemma20_6ProjectorComplement x) i j :=
            higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture
              x DeltaA DeltaA i j
      _ =
          matMulRectRight DeltaA
            (fun a b => lsLemma20_6Projector x a b +
              lsLemma20_6ProjectorComplement x a b) i j := by
            unfold matMulRectRight
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = matMulRectRight DeltaA (idMatrix n) i j := by
            unfold matMulRectRight
            apply Finset.sum_congr rfl
            intro k _
            simpa using
              congrArg (fun t : ℝ => DeltaA i k * t)
                (lsLemma20_6Projector_add_complement x k j)
      _ = DeltaA i j := by
            have h := congrFun (congrFun (rectMatMul_id_right DeltaA) i) j
            simpa [rectMatMul, matMulRectRight] using h

private theorem higham21_rectMatMulVec_matMulRectRight {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (matMulRectRight A V) x =
      rectMatMulVec A (matMulVec n V x) := by
  simpa [matMulRectRight, rectMatMul, rectMatMulVec, matMulVec] using
    (rectMatMulVec_rectMatMul A V x)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    for the source-oriented construction
    `DeltaA = DeltaA1 P + DeltaA2 (I-P)`, multiplying by the projector source
    vector `x` recovers the first perturbation action `DeltaA1 x`.  This is the
    algebraic step behind `(A + DeltaA)x = (A + DeltaA1)x = b`. -/
theorem higham21_lemma21_2_symmetrized_perturbation_mulVec_self_eq {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    rectMatMulVec (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) x =
      rectMatMulVec DeltaA1 x := by
  let P : Fin n → Fin n → ℝ := lsLemma20_6Projector x
  let Q : Fin n → Fin n → ℝ := lsLemma20_6ProjectorComplement x
  have hP : matMulVec n P x = x := by
    ext j
    simpa [P, matMulVec] using lsLemma20_6Projector_apply_self x hsq j
  have hQ : matMulVec n Q x = 0 := by
    simpa [Q] using lsLemma20_6ProjectorComplement_mulVec_self x hsq
  ext i
  calc
    rectMatMulVec (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) x i =
        rectMatMulVec
          (fun i j => matMulRectRight DeltaA1 P i j + matMulRectRight DeltaA2 Q i j) x i := by
          unfold rectMatMulVec
          apply Finset.sum_congr rfl
          intro j _
          rw [higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture]
    _ = rectMatMulVec (matMulRectRight DeltaA1 P) x i +
          rectMatMulVec (matMulRectRight DeltaA2 Q) x i := by
          unfold rectMatMulVec
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = rectMatMulVec DeltaA1 (matMulVec n P x) i +
          rectMatMulVec DeltaA2 (matMulVec n Q x) i := by
          rw [congrFun (higham21_rectMatMulVec_matMulRectRight DeltaA1 P x) i,
            congrFun (higham21_rectMatMulVec_matMulRectRight DeltaA2 Q x) i]
    _ = rectMatMulVec DeltaA1 x i := by
          rw [hP, hQ]
          simp [rectMatMulVec]

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    system-action form of the previous identity.  The constructed perturbation
    has the same action on `x` as `DeltaA1`, so replacing `DeltaA1` by the
    symmetrized perturbation preserves the equation tested at `x`. -/
theorem higham21_lemma21_2_symmetrized_system_mulVec_self_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    rectMatMulVec
        (fun i j => A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) x =
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x := by
  have hDelta :=
    higham21_lemma21_2_symmetrized_perturbation_mulVec_self_eq
      x hsq DeltaA1 DeltaA2
  ext i
  have hDelta_i := congrFun hDelta i
  unfold rectMatMulVec at hDelta_i ⊢
  calc
    (∑ j : Fin n,
        (A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) * x j)
        = (∑ j : Fin n, A i j * x j) +
            (∑ j : Fin n, undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j * x j) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (∑ j : Fin n, A i j * x j) + (∑ j : Fin n, DeltaA1 i j * x j) := by
          rw [hDelta_i]
    _ = ∑ j : Fin n, (A i j + DeltaA1 i j) * x j := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the first perturbed system `(A + DeltaA1)x = b` holds, then the
    source-oriented symmetrized perturbation also satisfies `(A + DeltaA)x = b`
    at the same vector `x`. -/
theorem higham21_lemma21_2_symmetrized_system_mulVec_self_of_deltaA1 {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b) :
    rectMatMulVec
        (fun i j => A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) x =
      b := by
  rw [higham21_lemma21_2_symmetrized_system_mulVec_self_eq A x hsq DeltaA1 DeltaA2]
  exact hDeltaA1

/-- A zero right-hand side has the zero vector as a minimum 2-norm solution of
    any rectangular system. -/
theorem rectMinNormSolution_zero_of_rhs_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hb : b = 0) :
    RectMinNormSolution m n A b (0 : Fin n → ℝ) := by
  constructor
  · rw [hb]
    ext i
    simp [rectMatMulVec]
  · intro z _hz
    have hzero : vecNorm2 (0 : Fin n → ℝ) = 0 := by
      simpa using (vecNorm2_zero (n := n))
    rw [hzero]
    exact vecNorm2_nonneg z

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    zero-vector branch of the Kielbasinski--Schwetlick proof.  If the printed
    candidate `x` is zero, the source proof takes the single perturbation to be
    `DeltaA2`; the first perturbed equation then forces `b = 0`, so the zero
    vector is the minimum 2-norm solution for the `A + DeltaA2` system.

    This is only the `x = 0` branch.  The nonzero branch uses the projector
    mixture and beta argument below. -/
theorem higham21_lemma21_2_zero_branch_min_norm_of_deltaA2 {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hx : x = 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b) :
    RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x := by
  subst x
  have hb : b = 0 := by
    rw [← hDeltaA1]
    ext i
    simp [rectMatMulVec]
  exact rectMinNormSolution_zero_of_rhs_zero
    (fun i j => A i j + DeltaA2 i j) b hb

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the scalar `beta = 1 + x^T H^T y / x^T x`, where
    `H = DeltaA1 - DeltaA2`, used to rescale the dual vector in the proof. -/
noncomputable def undetLemma21_2Beta {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) : ℝ :=
  1 + (∑ j : Fin n,
    x j * rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y j) /
      vecNorm2Sq x

private theorem higham21_lemma21_2_symmetrized_perturbation_eq_deltaA2_add_H_projector
    {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j =
      DeltaA2 i j +
        matMulRectRight (fun i j => DeltaA1 i j - DeltaA2 i j)
          (lsLemma20_6Projector x) i j := by
  have hmix :=
    higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture
      x DeltaA1 DeltaA2 i j
  have hid :
      (∑ k : Fin n, DeltaA2 i k * idMatrix n k j) = DeltaA2 i j := by
    have h := congrFun (congrFun (rectMatMul_id_right DeltaA2) i) j
    simpa [rectMatMul] using h
  rw [hmix]
  unfold matMulRectRight lsLemma20_6ProjectorComplement
  calc
    (∑ k : Fin n, DeltaA1 i k * lsLemma20_6Projector x k j) +
        ∑ k : Fin n, DeltaA2 i k * (idMatrix n k j - lsLemma20_6Projector x k j)
        = ∑ k : Fin n,
            (DeltaA2 i k * idMatrix n k j +
              (DeltaA1 i k - DeltaA2 i k) * lsLemma20_6Projector x k j) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = (∑ k : Fin n, DeltaA2 i k * idMatrix n k j) +
            ∑ k : Fin n,
              (DeltaA1 i k - DeltaA2 i k) * lsLemma20_6Projector x k j := by
          rw [Finset.sum_add_distrib]
    _ = DeltaA2 i j +
          ∑ k : Fin n,
            (DeltaA1 i k - DeltaA2 i k) * lsLemma20_6Projector x k j := by
          rw [hid]

private theorem higham21_matMulRectRight_projector_transpose_mulVec {m n : ℕ}
    (x : Fin n → ℝ) (H : Fin m → Fin n → ℝ) (y : Fin m → ℝ)
    (j : Fin n) :
    rectMatMulVec (finiteTranspose (matMulRectRight H (lsLemma20_6Projector x))) y j =
      ((∑ k : Fin n, x k * rectMatMulVec (finiteTranspose H) y k) /
          vecNorm2Sq x) * x j := by
  unfold rectMatMulVec finiteTranspose matMulRectRight lsLemma20_6Projector
  calc
    (∑ i : Fin m, (∑ k : Fin n, H i k * (x k * x j / vecNorm2Sq x)) * y i)
        = ∑ i : Fin m, ∑ k : Fin n,
            (H i k * y i) * (x k * x j / vecNorm2Sq x) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ k : Fin n, ∑ i : Fin m,
            (H i k * y i) * (x k * x j / vecNorm2Sq x) := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n,
          (∑ i : Fin m, H i k * y i) * (x k * x j / vecNorm2Sq x) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
    _ = ∑ k : Fin n,
          (x k * (∑ i : Fin m, H i k * y i) / vecNorm2Sq x) * x j := by
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ((∑ k : Fin n, x k * (∑ i : Fin m, H i k * y i)) /
          vecNorm2Sq x) * x j := by
          rw [← Finset.sum_mul]
          congr 1
          rw [← Finset.sum_div]
    _ = ((∑ k : Fin n, x k * rectMatMulVec (finiteTranspose H) y k) /
          vecNorm2Sq x) * x j := by
          rfl

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    transposed-system action of the source-oriented projector construction.
    If `x = (A + DeltaA2)^T y`, then
    `(A + DeltaA)^T y = beta x`, where
    `DeltaA = DeltaA1 P + DeltaA2 (I-P)` and
    `beta = 1 + x^T (DeltaA1 - DeltaA2)^T y / x^T x`.

    This is the algebraic step before the source proof shows `beta ≠ 0` and
    sets the new dual vector to `beta^{-1} y`; it does not prove positivity of
    `beta` or the final minimum-norm symmetrization theorem. -/
theorem higham21_lemma21_2_symmetrized_transpose_mulVec_eq_beta_smul {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x) :
    rectMatMulVec
        (finiteTranspose
          (fun i j => A i j +
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)) y =
      fun j : Fin n => undetLemma21_2Beta x DeltaA1 DeltaA2 y * x j := by
  let H : Fin m → Fin n → ℝ := fun i j => DeltaA1 i j - DeltaA2 i j
  ext j
  have hDeltaA2_j := congrFun hDeltaA2 j
  have hcorr :=
    higham21_matMulRectRight_projector_transpose_mulVec x H y j
  unfold rectMatMulVec finiteTranspose at hDeltaA2_j ⊢
  calc
    (∑ i : Fin m,
        (A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) * y i)
        = (∑ i : Fin m, (A i j + DeltaA2 i j) * y i) +
            ∑ i : Fin m, matMulRectRight H (lsLemma20_6Projector x) i j * y i := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [higham21_lemma21_2_symmetrized_perturbation_eq_deltaA2_add_H_projector]
          ring
    _ = x j +
          ((∑ k : Fin n, x k * rectMatMulVec (finiteTranspose H) y k) /
            vecNorm2Sq x) * x j := by
          rw [hDeltaA2_j]
          rw [← hcorr]
          rfl
    _ = undetLemma21_2Beta x DeltaA1 DeltaA2 y * x j := by
          unfold undetLemma21_2Beta H
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    conditional rescaling step after the source proof's beta algebra.
    If the source-oriented perturbation preserves the first perturbed system,
    `(A + DeltaA2)^T y = x`, and the beta scalar is nonzero, then the same
    constructed perturbation makes `x` a minimum 2-norm solution of the single
    perturbed rectangular system.

    This is intentionally conditional on `beta ≠ 0`; the source proof's
    perturbation-smallness argument that ensures this condition remains a
    separate open dependency. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_beta_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hbeta : undetLemma21_2Beta x DeltaA1 DeltaA2 y ≠ 0) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let M : Fin m → Fin n → ℝ :=
    fun i j => A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j
  let beta : ℝ := undetLemma21_2Beta x DeltaA1 DeltaA2 y
  let ytilde : Fin m → ℝ := fun i => beta⁻¹ * y i
  have hfirst : rectMatMulVec M x = b := by
    simpa [M] using
      higham21_lemma21_2_symmetrized_system_mulVec_self_of_deltaA1
        A x hsq DeltaA1 DeltaA2 b hDeltaA1
  have haction :
      rectMatMulVec (finiteTranspose M) y = fun j : Fin n => beta * x j := by
    simpa [M, beta] using
      higham21_lemma21_2_symmetrized_transpose_mulVec_eq_beta_smul
        A x DeltaA1 DeltaA2 y hDeltaA2
  have hytilde_eq : rectTransposeMulVec M ytilde = x := by
    ext j
    have hsmul_j :=
      congrFun (rectMatMulVec_smul (finiteTranspose M) beta⁻¹ y) j
    have haction_j := congrFun haction j
    calc
      rectTransposeMulVec M ytilde j =
          rectMatMulVec (finiteTranspose M) ytilde j := by
            rfl
      _ = beta⁻¹ * rectMatMulVec (finiteTranspose M) y j := by
            change rectMatMulVec (finiteTranspose M) (fun i : Fin m => beta⁻¹ * y i) j =
              beta⁻¹ * rectMatMulVec (finiteTranspose M) y j
            exact hsmul_j
      _ = beta⁻¹ * (beta * x j) := by rw [haction_j]
      _ = x j := by
            rw [← mul_assoc, inv_mul_cancel₀ hbeta, one_mul]
  have hsolve : rectMatMulVec M (rectTransposeMulVec M ytilde) = b := by
    rw [hytilde_eq]
    exact hfirst
  have hmin :=
    higham21_eq21_4_rect_transpose_min_norm_of_solves M b ytilde hsolve
  rwa [hytilde_eq] at hmin

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar smallness adapter for a common bound.  If both perturbation
    products are bounded by `rho`, then `3 * rho < 1` implies the printed
    `3 * max ... < 1` hypothesis. -/
theorem higham21_lemma21_2_three_max_lt_one_of_common_bound
    (a b rho : ℝ)
    (ha : a ≤ rho)
    (hb : b ≤ rho)
    (hrho : 3 * rho < 1) :
    3 * max a b < 1 := by
  have hmax_le : max a b ≤ rho := max_le ha hb
  nlinarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar endpoint of the source proof's beta-positivity estimate.
    Once the matrix perturbation argument has produced the displayed lower
    bound `beta >= 1 - (a + b)/(1 - b)`, the source smallness condition
    `3 * max a b < 1` implies `beta > 0`.

    This is only the final real-arithmetic step; it does not prove the
    pseudoinverse perturbation lower bound that supplies `hbound`. -/
theorem higham21_lemma21_2_scalar_beta_pos_of_bound
    (a b beta : ℝ)
    (hsmall : 3 * max a b < 1)
    (hbound : 1 - (a + b) / (1 - b) ≤ beta) :
    0 < beta := by
  have ha_le : a ≤ max a b := le_max_left a b
  have hb_le : b ≤ max a b := le_max_right a b
  have hden_pos : 0 < 1 - b := by
    nlinarith [hb_le, hsmall]
  have hnum_lt_den : a + b < 1 - b := by
    nlinarith [ha_le, hb_le, hsmall]
  have hfrac_lt_one : (a + b) / (1 - b) < 1 := by
    rw [div_lt_iff₀ hden_pos]
    simpa using hnum_lt_den
  linarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    nonzero form of the scalar beta-positivity endpoint. -/
theorem higham21_lemma21_2_scalar_beta_ne_zero_of_bound
    (a b beta : ℝ)
    (hsmall : 3 * max a b < 1)
    (hbound : 1 - (a + b) / (1 - b) ≤ beta) :
    beta ≠ 0 :=
  ne_of_gt (higham21_lemma21_2_scalar_beta_pos_of_bound a b beta hsmall hbound)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    inner-product route to the source proof's displayed beta lower bound.
    If the numerator `x^T (DeltaA1 - DeltaA2)^T y` is bounded in absolute
    value by `gamma * x^T x`, then
    `beta >= 1 - gamma`.

    This is an algebraic handoff for the still-open pseudoinverse perturbation
    estimate, which must provide the absolute inner-product bound. -/
theorem higham21_lemma21_2_beta_lower_bound_of_abs_inner_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    (gamma : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hinner :
      |∑ j : Fin n,
        x j *
          rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
            y j| ≤
        gamma * vecNorm2Sq x) :
    1 - gamma ≤ undetLemma21_2Beta x DeltaA1 DeltaA2 y := by
  let numer : ℝ :=
    ∑ j : Fin n,
      x j *
        rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          y j
  let denom : ℝ := vecNorm2Sq x
  have hden_pos : 0 < denom := by
    exact lt_of_le_of_ne (by simpa [denom] using vecNorm2Sq_nonneg x)
      (by simpa [denom] using hsq.symm)
  have hden_ne : denom ≠ 0 := ne_of_gt hden_pos
  have hinner' : |numer| ≤ gamma * denom := by
    simpa [numer, denom] using hinner
  have hnum_lower : -(gamma * denom) ≤ numer := (abs_le.mp hinner').1
  have hdiv_lower :
      (-(gamma * denom)) / denom ≤ numer / denom :=
    div_le_div_of_nonneg_right hnum_lower (le_of_lt hden_pos)
  have hleft : (-(gamma * denom)) / denom = -gamma := by
    field_simp [hden_ne]
  have hratio_lower : -gamma ≤ numer / denom := by
    simpa [hleft] using hdiv_lower
  have hfinal : 1 - gamma ≤ 1 + numer / denom := by
    linarith
  simpa [undetLemma21_2Beta, numer, denom] using hfinal

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from the source proof's scalar beta lower bound.
    If the matrix perturbation argument supplies
    `1 - (rho1 + rho2)/(1 - rho2) <= beta`, then the source smallness condition
    `3 * max rho1 rho2 < 1` gives `beta ≠ 0`, so the conditional rescaling
    theorem applies.

    This isolates the remaining matrix work to proving the displayed lower
    bound from pseudoinverse perturbation estimates. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_beta_lower_bound {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hbound :
      1 - (rho1 + rho2) / (1 - rho2) ≤
        undetLemma21_2Beta x DeltaA1 DeltaA2 y) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_beta_ne_zero
    A x DeltaA1 DeltaA2 b y hsq hDeltaA1 hDeltaA2
    (higham21_lemma21_2_scalar_beta_ne_zero_of_bound
      rho1 rho2 (undetLemma21_2Beta x DeltaA1 DeltaA2 y) hsmall hbound)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from the beta numerator bound.  This replaces the
    previous displayed beta lower-bound hypothesis by the equivalent local
    obligation that the absolute beta numerator is bounded by
    `((rho1 + rho2)/(1 - rho2)) * x^T x`.

    The pseudoinverse perturbation estimate needed to prove this absolute
    numerator bound remains open. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_abs_inner_fraction_bound {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hinner :
      |∑ j : Fin n,
        x j *
          rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
            y j| ≤
        ((rho1 + rho2) / (1 - rho2)) * vecNorm2Sq x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_beta_lower_bound
    A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall
    (higham21_lemma21_2_beta_lower_bound_of_abs_inner_bound
      x DeltaA1 DeltaA2 y ((rho1 + rho2) / (1 - rho2)) hsq hinner)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    vector-action route to the beta numerator bound.  If
    `(DeltaA1 - DeltaA2)^T y` has Euclidean norm at most `gamma * ||x||_2`,
    then Cauchy--Schwarz gives
    `|x^T (DeltaA1 - DeltaA2)^T y| <= gamma * x^T x`.

    The remaining source perturbation work is to supply this vector-action
    bound from pseudoinverse estimates. -/
theorem higham21_lemma21_2_beta_abs_inner_bound_of_transpose_action_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    (gamma : ℝ)
    (haction :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        gamma * vecNorm2 x) :
    |∑ j : Fin n,
      x j *
        rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          y j| ≤
      gamma * vecNorm2Sq x := by
  let z : Fin n → ℝ :=
    rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y
  calc
    |∑ j : Fin n, x j * z j|
        ≤ vecNorm2 x * vecNorm2 z :=
            abs_vecInnerProduct_le_vecNorm2_mul x z
    _ ≤ vecNorm2 x * (gamma * vecNorm2 x) :=
            mul_le_mul_of_nonneg_left (by simpa [z] using haction)
              (vecNorm2_nonneg x)
    _ = gamma * vecNorm2Sq x := by
            rw [← vecNorm2_sq x]
            ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from a vector-action perturbation bound on the beta
    numerator.  This is one step closer to the source pseudoinverse proof than
    the raw scalar lower-bound hypothesis, but it is still conditional on the
    vector-action estimate. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (haction :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_abs_inner_fraction_bound
    A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall
    (higham21_lemma21_2_beta_abs_inner_bound_of_transpose_action_bound
      x DeltaA1 DeltaA2 y ((rho1 + rho2) / (1 - rho2)) haction)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator/vector route to the beta vector-action bound.  An operator-2
    bound for `(DeltaA1 - DeltaA2)^T`, together with a bound on the auxiliary
    dual vector `y` in terms of `x`, gives the vector-action estimate needed by
    the beta handoff.

    The source pseudoinverse perturbation argument is still responsible for
    proving the operator and dual-vector bounds used here. -/
theorem higham21_lemma21_2_transpose_action_bound_of_op_bound_and_dual_norm
    {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    {alpha eta gamma : ℝ}
    (halpha : 0 ≤ alpha)
    (hprod : alpha * eta ≤ gamma)
    (hOp :
      rectOpNorm2Le
        (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) alpha)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    vecNorm2
        (rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
      gamma * vecNorm2 x := by
  calc
    vecNorm2
        (rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y)
        ≤ alpha * vecNorm2 y := hOp y
    _ ≤ alpha * (eta * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left hy halpha
    _ = (alpha * eta) * vecNorm2 x := by ring
    _ ≤ gamma * vecNorm2 x :=
        mul_le_mul_of_nonneg_right hprod (vecNorm2_nonneg x)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from operator and dual-vector norm bounds for the beta
    vector-action estimate.  This isolates the remaining source-specific work
    to proving those bounds from pseudoinverse perturbation theory. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_op_bound_and_dual_norm {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hprod : alpha * eta ≤ (rho1 + rho2) / (1 - rho2))
    (hOp :
      rectOpNorm2Le
        (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) alpha)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound
    A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall
    (higham21_lemma21_2_transpose_action_bound_of_op_bound_and_dual_norm
      x DeltaA1 DeltaA2 y halpha hprod hOp hy)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-2 triangle step for the remaining beta obligation.  Separate
    operator bounds on `DeltaA1` and `DeltaA2` give an operator bound for
    `(DeltaA1 - DeltaA2)^T`. -/
theorem higham21_lemma21_2_transpose_sub_op_bound_of_separate_op_bounds {m n : ℕ}
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {alpha beta : ℝ}
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    rectOpNorm2Le
      (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
      (alpha + beta) :=
  rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
    (fun i j => DeltaA1 i j - DeltaA2 i j)
    (add_nonneg halpha hbeta)
    (rectOpNorm2Le_sub DeltaA1 DeltaA2 hDeltaA1 hDeltaA2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from separate perturbation operator bounds and a
    dual-vector norm bound.  This leaves the source-specific pseudoinverse
    perturbation work to prove the dual-vector estimate and the final product
    budget. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_norm
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (hprod : (alpha + beta) * eta ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_op_bound_and_dual_norm
    A x DeltaA1 DeltaA2 b y rho1 rho2 (alpha + beta) eta hsq hDeltaA1
    hDeltaA2 hsmall (add_nonneg halpha hbeta) hprod
    (higham21_lemma21_2_transpose_sub_op_bound_of_separate_op_bounds
      DeltaA1 DeltaA2 halpha hbeta hDeltaA1Op hDeltaA2Op)
    hy

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar product-budget bridge for the operator/dual-vector route.  If the
    two perturbation operator bounds are no larger than `rho1` and `rho2`, and
    the dual-vector factor is bounded by `(1 - rho2)^{-1}`, then the product
    budget required by the beta handoff follows. -/
theorem higham21_lemma21_2_product_budget_of_separate_bounds_and_dual_factor
    (rho1 rho2 alpha beta eta : ℝ)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹) :
    (alpha + beta) * eta ≤ (rho1 + rho2) / (1 - rho2) := by
  have hrho2_le : rho2 ≤ max rho1 rho2 := le_max_right rho1 rho2
  have hden_pos : 0 < 1 - rho2 := by
    nlinarith [hrho2_le, hsmall]
  have hsum_le : alpha + beta ≤ rho1 + rho2 :=
    add_le_add halpha_le hbeta_le
  have hsum_rhs_nonneg : 0 ≤ rho1 + rho2 :=
    le_trans (add_nonneg halpha hbeta) hsum_le
  have hprod :
      (alpha + beta) * eta ≤ (rho1 + rho2) * (1 - rho2)⁻¹ :=
    mul_le_mul hsum_le heta_le heta hsum_rhs_nonneg
  simpa [div_eq_mul_inv] using hprod

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from separate perturbation operator bounds and a
    source-shaped dual-vector factor estimate.  The remaining source-specific
    work is to prove `||y||₂ <= eta ||x||₂` with
    `eta <= (1 - rho2)^{-1}` from the pseudoinverse perturbation argument. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_factor
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_norm
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1 hDeltaA2
    hsmall halpha hbeta
    (higham21_lemma21_2_product_budget_of_separate_bounds_and_dual_factor
      rho1 rho2 alpha beta eta hsmall halpha hbeta heta halpha_le hbeta_le
      heta_le)
    hDeltaA1Op hDeltaA2Op hy

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    algebraic action of the perturbed pseudoinverse transpose used in the
    source proof.  Applying `Bᵀ` to `Bplusᵀ x` is the transposed action of the
    domain projection `Bplus B` on `x`. -/
theorem higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
    {m n : ℕ}
    (B : Fin m → Fin n → ℝ) (Bplus : Fin n → Fin m → ℝ)
    (x : Fin n → ℝ) :
    rectMatMulVec (finiteTranspose B) (rectMatMulVec (finiteTranspose Bplus) x) =
      rectMatMulVec (finiteTranspose (rectMatMul Bplus B)) x := by
  ext j
  unfold rectMatMulVec finiteTranspose rectMatMul
  calc
    ∑ i : Fin m, B i j * (∑ k : Fin n, Bplus k i * x k)
        = ∑ i : Fin m, ∑ k : Fin n, B i j * (Bplus k i * x k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ i : Fin m, B i j * (Bplus k i * x k) := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin n, (∑ i : Fin m, Bplus k i * B i j) * x k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the perturbed pseudoinverse domain projection is symmetric and fixes
    `x`, then the source proof's choice `y = Bplusᵀ x` solves
    `Bᵀ y = x`. -/
theorem higham21_lemma21_2_perturbed_pseudoinverse_transpose_solves_of_domain_projection
    {m n : ℕ}
    (B : Fin m → Fin n → ℝ) (Bplus : Fin n → Fin m → ℝ)
    (x : Fin n → ℝ)
    (hDomainSym : IsSymmetricFiniteMatrix (rectMatMul Bplus B))
    (hDomainX : rectMatMulVec (rectMatMul Bplus B) x = x) :
    rectMatMulVec (finiteTranspose B) (rectMatMulVec (finiteTranspose Bplus) x) =
      x := by
  rw [higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection]
  have htranspose :
      finiteTranspose (rectMatMul Bplus B) = rectMatMul Bplus B := by
    ext i j
    exact hDomainSym j i
  rw [htranspose, hDomainX]

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a perturbation-pseudoinverse operator bound gives the dual-vector estimate
    for the source proof's choice `y = Bplusᵀ x`. -/
theorem higham21_lemma21_2_dual_vector_bound_of_perturbed_pseudoinverse_op_bound
    {m n : ℕ}
    (Bplus : Fin n → Fin m → ℝ) (x : Fin n → ℝ)
    {eta : ℝ}
    (heta : 0 ≤ eta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    vecNorm2 (rectMatMulVec (finiteTranspose Bplus) x) ≤ eta * vecNorm2 x :=
  (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Bplus heta hBplusOp) x

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped product-bound bridge.  A direct operator bound for
    `Bplus * (DeltaA1 - DeltaA2)` gives the vector-action estimate for
    `(DeltaA1 - DeltaA2)ᵀ (Bplusᵀ x)` used in the beta numerator. -/
theorem higham21_lemma21_2_transpose_action_bound_of_pseudoinverse_product_bound
    {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    {gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (hProduct :
      rectOpNorm2Le
        (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
        gamma) :
    vecNorm2
        (rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          (rectMatMulVec (finiteTranspose Bplus) x)) ≤
      gamma * vecNorm2 x := by
  have haction :
      rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          (rectMatMulVec (finiteTranspose Bplus) x) =
        rectMatMulVec
          (finiteTranspose
            (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j)))
          x :=
    higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
      (fun i j => DeltaA1 i j - DeltaA2 i j) Bplus x
  rw [haction]
  exact
    (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
      hgamma hProduct) x

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete operator-product estimate used in the beta lower-bound route.
    Separate operator-2 bounds for `DeltaA1`, `DeltaA2`, and the perturbed
    pseudoinverse candidate `Bplus` imply an operator bound for the source
    product `Bplus * (DeltaA1 - DeltaA2)`.

    This is the product-bound estimate only; the source perturbation theorem
    must still supply the perturbed-pseudoinverse operator bound. -/
theorem higham21_lemma21_2_pseudoinverse_product_bound_of_separate_op_bounds
    {m n : ℕ}
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    {alpha beta eta : ℝ}
    (heta : 0 ≤ eta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    rectOpNorm2Le
      (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
      (eta * (alpha + beta)) :=
  rectOpNorm2Le_rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j)
    heta hBplusOp (rectOpNorm2Le_sub DeltaA1 DeltaA2 hDeltaA1 hDeltaA2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from a source-shaped product bound on
    `Bplus * (DeltaA1 - DeltaA2)`.  The remaining perturbation proof is to
    instantiate this product bound for `Bplus = (A + DeltaA2)^+` from the
    source smallness hypotheses. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_pseudoinverse_product_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    (rho1 rho2 gamma : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDomainSym :
      IsSymmetricFiniteMatrix
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)))
    (hDomainX :
      rectMatMulVec
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hgamma : 0 ≤ gamma)
    (hgamma_le : gamma ≤ (rho1 + rho2) / (1 - rho2))
    (hProduct :
      rectOpNorm2Le
        (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
        gamma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let y : Fin m → ℝ := rectMatMulVec (finiteTranspose Bplus) x
  have hDeltaA2 :
      rectMatMulVec (finiteTranspose B) y = x := by
    simpa [B, y] using
      higham21_lemma21_2_perturbed_pseudoinverse_transpose_solves_of_domain_projection
        B Bplus x (by simpa [B] using hDomainSym) (by simpa [B] using hDomainX)
  have hActionGamma :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        gamma * vecNorm2 x := by
    simpa [y] using
      higham21_lemma21_2_transpose_action_bound_of_pseudoinverse_product_bound
        x DeltaA1 DeltaA2 Bplus hgamma hProduct
  have hAction :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x :=
    le_trans hActionGamma
      (mul_le_mul_of_nonneg_right hgamma_le (vecNorm2_nonneg x))
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound
      A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall hAction

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse specialization of the source-shaped product
    handoff.  Under Gram nonsingularity for `B = A + DeltaA2`, the printed
    hypothesis `x = Bᵀ y` supplies the domain-projection condition, so the
    remaining source perturbation work is reduced to the product bound
    on `B⁺ (DeltaA1 - DeltaA2)`. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 gamma : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hgamma : 0 ≤ gamma)
    (hgamma_le : gamma ≤ (rho1 + rho2) / (1 - rho2))
    (hProduct :
      rectOpNorm2Le
        (rectMatMul
          (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
          (fun i j => DeltaA1 i j - DeltaA2 i j))
        gamma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let Bplus : Fin n → Fin m → ℝ := undetAplusOfGramNonsingInv B
  have hdetB : Matrix.det (rectGram B : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    simpa [B] using hdet
  have hMP : RectMoorePenrosePseudoinverse m n B Bplus :=
    higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero B hdetB
  have hxRange :
      x = rectMatMulVec Bplus (matMulVec m (rectGram B) y) := by
    calc
      x = rectTransposeMulVec B y := by
        simpa [B] using hxTranspose
      _ = rectMatMulVec Bplus (matMulVec m (rectGram B) y) := by
        simpa [Bplus] using
          higham21_lemma21_2_gram_pseudoinverse_range_of_transpose B hdetB y
  have hDomainX : rectMatMulVec (rectMatMul Bplus B) x = x := by
    rw [hxRange]
    simpa [Bplus] using
      higham21_lemma21_2_gram_pseudoinverse_domain_projection_apply_range
        B hdetB (matMulVec m (rectGram B) y)
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_pseudoinverse_product_bound
      A x DeltaA1 DeltaA2 b Bplus rho1 rho2 gamma hsq hDeltaA1
      (by simpa [B, Bplus] using hMP.domain_projection_symmetric)
      (by simpa [B, Bplus] using hDomainX) hsmall hgamma hgamma_le
      (by simpa [B, Bplus] using hProduct)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-facing product-bound specialization of the symmetrized minimum-norm
    handoff.  If the perturbed Gram pseudoinverse exists, the printed transpose
    representation `x = (A + DeltaA2)^T y` holds, and the separate operator
    bounds plus the perturbed-pseudoinverse operator bound imply the source
    product budget, then the constructed single perturbation makes `x` the
    minimum 2-norm solution.

    This removes the raw product-bound hypothesis from the concrete Gram route;
    it remains conditional on the perturbed-Gram nonsingularity and
    perturbed-pseudoinverse operator estimate. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_budget
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hbudget : eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let Bplus : Fin n → Fin m → ℝ :=
    undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j)
  have hgamma : 0 ≤ eta * (alpha + beta) :=
    mul_nonneg heta (add_nonneg halpha hbeta)
  have hProduct :
      rectOpNorm2Le
        (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
        (eta * (alpha + beta)) := by
    exact
      higham21_lemma21_2_pseudoinverse_product_bound_of_separate_op_bounds
        DeltaA1 DeltaA2 Bplus heta hDeltaA1Op hDeltaA2Op
        (by simpa [Bplus] using hBplusOp)
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_bound
      A x DeltaA1 DeltaA2 b y rho1 rho2 (eta * (alpha + beta))
      hsq hDeltaA1 hdet hxTranspose hsmall hgamma hbudget
      (by simpa [Bplus] using hProduct)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-factor budget for the concrete perturbed-pseudoinverse route.
    The printed estimates `alpha <= rho1`, `beta <= rho2`, and
    `eta <= (1 - rho2)^{-1}` imply the product budget in the orientation used
    by the concrete Gram-pseudoinverse handoff. -/
theorem higham21_lemma21_2_product_budget_of_source_factor_bounds
    (rho1 rho2 alpha beta eta : ℝ)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹) :
    eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2) := by
  have hbudget :
      (alpha + beta) * eta ≤ (rho1 + rho2) / (1 - rho2) :=
    higham21_lemma21_2_product_budget_of_separate_bounds_and_dual_factor
      rho1 rho2 alpha beta eta hsmall halpha hbeta heta halpha_le
      hbeta_le heta_le
  simpa [mul_comm] using hbudget

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the Gram perturbation
    `(A + DeltaA2)(A + DeltaA2)^T - A A^T` used to reduce perturbed
    Gram nonsingularity to the Chapter 7 `I + A^{-1} DeltaA` route. -/
noncomputable def undetGramPerturbation {m n : ℕ}
    (A DeltaA2 : Fin m → Fin n → ℝ) : Fin m → Fin m → ℝ :=
  fun i j =>
    rectGram (fun i j => A i j + DeltaA2 i j) i j - rectGram A i j

/-- Componentwise budget for the Chapter 21 Gram perturbation induced by a
    rectangular data perturbation bound `|DeltaA2| <= eps * E`. -/
noncomputable def undetGramPerturbationComponentBudget {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) (eps : ℝ) : Fin m → Fin m → ℝ :=
  fun i j => ∑ k : Fin n,
    (|A i k| * E j k + E i k * |A j k| + eps * E i k * E j k)

/-- Row-norm source budget for the Chapter 21 Gram perturbation induced by a
    rectangular componentwise data-perturbation budget.  This replaces each
    entry of `A` and `E` in the componentwise Gram budget by its row 2-norm. -/
noncomputable def undetGramPerturbationRowNormBudget {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) (eps : ℝ) : Fin m → Fin m → ℝ :=
  fun i j =>
    (n : ℝ) *
      (rectRowNorm2 A i * rectRowNorm2 E j +
        rectRowNorm2 E i * rectRowNorm2 A j +
        eps * rectRowNorm2 E i * rectRowNorm2 E j)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a row 2-norm is bounded by an operator-2 certificate for the transpose. -/
theorem higham21_rectRowNorm2_le_of_transpose_rectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) {c : ℝ}
    (hAt : rectOpNorm2Le (finiteTranspose A) c) :
    rectRowNorm2 A i ≤ c := by
  have htest := hAt (finiteBasisVec i)
  have hrow :
      rectMatMulVec (finiteTranspose A) (finiteBasisVec i) =
        fun j : Fin n => A i j := by
    ext j
    simp [rectMatMulVec, finiteTranspose, finiteBasisVec]
  simpa [rectRowNorm2, hrow, vecNorm2_finiteBasisVec] using htest

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a uniform operator-2 bound on a rectangular matrix bounds every row
    2-norm, by applying the transpose operator certificate to a coordinate
    vector. -/
theorem higham21_rectRowNorm2_le_of_rectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) {c : ℝ}
    (hc : 0 ≤ c) (hA : rectOpNorm2Le A c) :
    rectRowNorm2 A i ≤ c :=
  higham21_rectRowNorm2_le_of_transpose_rectOpNorm2Le A i
    (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le A hc hA)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scaling a rectangular data majorant by a nonnegative perturbation size
    scales its operator-2 certificate. -/
theorem higham21_rectOpNorm2Le_const_mul_of_nonneg {m n : ℕ}
    (E : Fin m → Fin n → ℝ) {eps e : ℝ}
    (heps : 0 ≤ eps) (hE : rectOpNorm2Le E e) :
    rectOpNorm2Le (fun i j => eps * E i j) (eps * e) := by
  intro x
  have hscale :
      rectMatMulVec (fun i j => eps * E i j) x =
        fun i => eps * rectMatMulVec E x i := by
    ext i
    unfold rectMatMulVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    vecNorm2 (rectMatMulVec (fun i j => eps * E i j) x)
        = eps * vecNorm2 (rectMatMulVec E x) := by
          rw [hscale, vecNorm2_smul, abs_of_nonneg heps]
    _ ≤ eps * (e * vecNorm2 x) :=
          mul_le_mul_of_nonneg_left (hE x) heps
    _ = eps * e * vecNorm2 x := by ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a componentwise data perturbation bound `|DeltaA| <= eps * E` gives an
    operator-2 certificate for `DeltaA` from an operator-2 certificate for
    `E`. -/
theorem higham21_rectOpNorm2Le_of_componentwise_data_bound {m n : ℕ}
    (DeltaA E : Fin m → Fin n → ℝ) {eps e : ℝ}
    (heps : 0 ≤ eps)
    (hDeltaComponent : ∀ i k, |DeltaA i k| ≤ eps * E i k)
    (hE : rectOpNorm2Le E e) :
    rectOpNorm2Le DeltaA (eps * e) :=
  rectOpNorm2Le_of_abs_entry_le
    (A := DeltaA) (B := fun i j => eps * E i j)
    hDeltaComponent
    (higham21_rectOpNorm2Le_const_mul_of_nonneg E heps hE)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the dimension factor in the conservative source scalar bound has the
    expected quadratic form. -/
theorem higham21_sqrt_nat_cast_mul_self (m : ℕ) :
    Real.sqrt ((m : ℝ) * (m : ℝ)) = (m : ℝ) := by
  rw [← sq]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (by exact_mod_cast Nat.zero_le m)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    quadratic source-size scalar bound for the conservative Chapter 7 factor. -/
theorem higham21_lemma21_2_source_factor_le_of_quadratic_bound
    (m : ℕ) (rho2 tau omega : ℝ)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹) :
    tau *
        (Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * omega)) ≤
      (1 - rho2)⁻¹ := by
  calc
    tau *
        (Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * omega))
        = 2 * (m : ℝ) ^ 2 * tau * omega := by
          rw [higham21_sqrt_nat_cast_mul_self m]
          ring
    _ ≤ (1 - rho2)⁻¹ := hSourceFactor_le

/-- Expansion of the Chapter 21 Gram perturbation
    `(A + DeltaA2)(A + DeltaA2)^T - AA^T`. -/
theorem undetGramPerturbation_eq_sum {m n : ℕ}
    (A DeltaA2 : Fin m → Fin n → ℝ) (i j : Fin m) :
    undetGramPerturbation A DeltaA2 i j =
      ∑ k : Fin n,
        (A i k * DeltaA2 j k + DeltaA2 i k * A j k +
          DeltaA2 i k * DeltaA2 j k) := by
  unfold undetGramPerturbation rectGram
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The componentwise Gram budget is nonnegative when the rectangular
    perturbation majorant is nonnegative. -/
theorem undetGramPerturbationComponentBudget_nonneg {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hE : ∀ i k, 0 ≤ E i k) :
    ∀ i j : Fin m, 0 ≤ undetGramPerturbationComponentBudget A E eps i j := by
  intro i j
  unfold undetGramPerturbationComponentBudget
  apply Finset.sum_nonneg
  intro k _
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (abs_nonneg _) (hE j k))
      (mul_nonneg (hE i k) (abs_nonneg _)))
    (mul_nonneg (mul_nonneg heps (hE i k)) (hE j k))

/-- The row-norm source Gram budget is nonnegative when the rectangular
    perturbation majorant and scalar perturbation size are nonnegative. -/
theorem undetGramPerturbationRowNormBudget_nonneg {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) :
    ∀ i j : Fin m, 0 ≤ undetGramPerturbationRowNormBudget A E eps i j := by
  intro i j
  unfold undetGramPerturbationRowNormBudget
  exact mul_nonneg (by exact_mod_cast Nat.zero_le n)
    (add_nonneg
      (add_nonneg
        (mul_nonneg (rectRowNorm2_nonneg A i) (rectRowNorm2_nonneg E j))
        (mul_nonneg (rectRowNorm2_nonneg E i) (rectRowNorm2_nonneg A j)))
      (mul_nonneg
        (mul_nonneg heps (rectRowNorm2_nonneg E i))
        (rectRowNorm2_nonneg E j)))

/-- The induced componentwise Gram perturbation budget is bounded by the
    row-norm source Gram budget. -/
theorem undetGramPerturbationComponentBudget_le_rowNormBudget {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hE : ∀ i k, 0 ≤ E i k) :
    ∀ i j : Fin m,
      undetGramPerturbationComponentBudget A E eps i j ≤
        undetGramPerturbationRowNormBudget A E eps i j := by
  intro i j
  let C : ℝ :=
    rectRowNorm2 A i * rectRowNorm2 E j +
      rectRowNorm2 E i * rectRowNorm2 A j +
      eps * rectRowNorm2 E i * rectRowNorm2 E j
  have hsum :
      (∑ k : Fin n,
        (|A i k| * E j k + E i k * |A j k| + eps * E i k * E j k)) ≤
        ∑ _k : Fin n, C := by
    apply Finset.sum_le_sum
    intro k _
    have hAi : |A i k| ≤ rectRowNorm2 A i := by
      simpa [rectRowNorm2] using abs_coord_le_vecNorm2 (fun q : Fin n => A i q) k
    have hAj : |A j k| ≤ rectRowNorm2 A j := by
      simpa [rectRowNorm2] using abs_coord_le_vecNorm2 (fun q : Fin n => A j q) k
    have hEi : E i k ≤ rectRowNorm2 E i := by
      simpa [rectRowNorm2, abs_of_nonneg (hE i k)] using
        abs_coord_le_vecNorm2 (fun q : Fin n => E i q) k
    have hEj : E j k ≤ rectRowNorm2 E j := by
      simpa [rectRowNorm2, abs_of_nonneg (hE j k)] using
        abs_coord_le_vecNorm2 (fun q : Fin n => E j q) k
    have hterm1 :
        |A i k| * E j k ≤ rectRowNorm2 A i * rectRowNorm2 E j :=
      mul_le_mul hAi hEj (hE j k) (rectRowNorm2_nonneg A i)
    have hterm2 :
        E i k * |A j k| ≤ rectRowNorm2 E i * rectRowNorm2 A j :=
      mul_le_mul hEi hAj (abs_nonneg _) (rectRowNorm2_nonneg E i)
    have hterm3_raw :
        E i k * E j k ≤ rectRowNorm2 E i * rectRowNorm2 E j :=
      mul_le_mul hEi hEj (hE j k) (rectRowNorm2_nonneg E i)
    have hterm3 :
        eps * E i k * E j k ≤
          eps * rectRowNorm2 E i * rectRowNorm2 E j := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hterm3_raw heps
    simpa [C, add_assoc] using add_le_add (add_le_add hterm1 hterm2) hterm3
  calc
    undetGramPerturbationComponentBudget A E eps i j
        = ∑ k : Fin n,
            (|A i k| * E j k + E i k * |A j k| + eps * E i k * E j k) := by
          rfl
    _ ≤ ∑ _k : Fin n, C := hsum
    _ = undetGramPerturbationRowNormBudget A E eps i j := by
          simp [undetGramPerturbationRowNormBudget, C]
          ring

/-- A componentwise rectangular perturbation bound induces a componentwise
    bound on the Chapter 21 Gram perturbation. -/
theorem undetGramPerturbation_abs_le_componentBudget {m n : ℕ}
    (A DeltaA2 E : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps)
    (hE : ∀ i k, 0 ≤ E i k)
    (hDeltaA2 : ∀ i k, |DeltaA2 i k| ≤ eps * E i k) :
    ∀ i j : Fin m,
      |undetGramPerturbation A DeltaA2 i j| ≤
        eps * undetGramPerturbationComponentBudget A E eps i j := by
  intro i j
  rw [undetGramPerturbation_eq_sum]
  unfold undetGramPerturbationComponentBudget
  calc
    |∑ k : Fin n,
        (A i k * DeltaA2 j k + DeltaA2 i k * A j k +
          DeltaA2 i k * DeltaA2 j k)|
        ≤ ∑ k : Fin n,
            |A i k * DeltaA2 j k + DeltaA2 i k * A j k +
              DeltaA2 i k * DeltaA2 j k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n,
          eps * (|A i k| * E j k + E i k * |A j k| +
            eps * E i k * E j k) := by
        apply Finset.sum_le_sum
        intro k _
        have hterm1 :
            |A i k * DeltaA2 j k| ≤ eps * (|A i k| * E j k) := by
          calc
            |A i k * DeltaA2 j k| = |A i k| * |DeltaA2 j k| := by
              rw [abs_mul]
            _ ≤ |A i k| * (eps * E j k) :=
              mul_le_mul_of_nonneg_left (hDeltaA2 j k) (abs_nonneg _)
            _ = eps * (|A i k| * E j k) := by ring
        have hterm2 :
            |DeltaA2 i k * A j k| ≤ eps * (E i k * |A j k|) := by
          calc
            |DeltaA2 i k * A j k| = |DeltaA2 i k| * |A j k| := by
              rw [abs_mul]
            _ ≤ (eps * E i k) * |A j k| :=
              mul_le_mul_of_nonneg_right (hDeltaA2 i k) (abs_nonneg _)
            _ = eps * (E i k * |A j k|) := by ring
        have hterm3 :
            |DeltaA2 i k * DeltaA2 j k| ≤
              eps * (eps * E i k * E j k) := by
          have hleft_nonneg : 0 ≤ eps * E i k := mul_nonneg heps (hE i k)
          calc
            |DeltaA2 i k * DeltaA2 j k| =
                |DeltaA2 i k| * |DeltaA2 j k| := by
              rw [abs_mul]
            _ ≤ (eps * E i k) * (eps * E j k) :=
              mul_le_mul (hDeltaA2 i k) (hDeltaA2 j k)
                (abs_nonneg _) hleft_nonneg
            _ = eps * (eps * E i k * E j k) := by ring
        calc
          |A i k * DeltaA2 j k + DeltaA2 i k * A j k +
              DeltaA2 i k * DeltaA2 j k|
              ≤ |A i k * DeltaA2 j k| +
                  |DeltaA2 i k * A j k| +
                  |DeltaA2 i k * DeltaA2 j k| := by
                exact abs_add_three _ _ _
          _ ≤ eps * (|A i k| * E j k) +
                eps * (E i k * |A j k|) +
                eps * (eps * E i k * E j k) := by
              nlinarith [hterm1, hterm2, hterm3]
          _ = eps * (|A i k| * E j k + E i k * |A j k| +
                eps * E i k * E j k) := by ring
    _ = eps * (∑ k : Fin n,
          (|A i k| * E j k + E i k * |A j k| +
            eps * E i k * E j k)) := by
        rw [Finset.mul_sum]

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Chapter 7 inverse-perturbation handoff for the remaining perturbed Gram
    nonsingularity obligation.  If `AA^T` has a left inverse and the relative
    Gram perturbation `AAT_inv * ((A + DeltaA2)(A + DeltaA2)^T - AA^T)` is a
    strict absolute infinity-norm contraction, then the perturbed Gram matrix
    is nonsingular.

    This is not the full source smallness proof; it replaces the raw
    determinant certificate by the repository's existing Neumann-style
    perturbation condition. -/
theorem higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    Matrix.det
        (rectGram (fun i j => A i j + DeltaA2 i j) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let G : Fin m → Fin m → ℝ := rectGram A
  let DeltaG : Fin m → Fin m → ℝ := undetGramPerturbation A DeltaA2
  let GpertInv : Fin m → Fin m → ℝ :=
    ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG
  have hRight :
      IsRightInverse m (fun i j => G i j + DeltaG i j) GpertInv :=
    problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound
      m hm G AAT_inv DeltaG c hc_nn hc_lt
      (by simpa [G] using hLeft)
      (by simpa [DeltaG] using hbound)
  have hdetAdd :
      Matrix.det
          ((fun i j => G i j + DeltaG i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    exact
      Matrix.det_ne_zero_of_right_inverse
        (A := ((fun i j => G i j + DeltaG i j) :
          Matrix (Fin m) (Fin m) ℝ))
        (B := (GpertInv : Matrix (Fin m) (Fin m) ℝ))
        (by
          ext i j
          rw [Matrix.mul_apply, Matrix.one_apply]
          exact hRight i j)
  have hmatrix :
      ((fun i j => G i j + DeltaG i j) :
        Matrix (Fin m) (Fin m) ℝ) =
        (rectGram B : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j
    simp [G, DeltaG, undetGramPerturbation, B]
  rw [hmatrix] at hdetAdd
  simpa [B] using hdetAdd

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the Chapter 7 inverse perturbation candidate is a certified right inverse
    for the perturbed Gram matrix under the same absolute left-product
    contraction used for nonsingularity above. -/
theorem higham21_lemma21_2_perturbed_gram_ch7_candidate_right_inverse_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    IsRightInverse m
      (rectGram (fun i j => A i j + DeltaA2 i j))
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2)) := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let G : Fin m → Fin m → ℝ := rectGram A
  let DeltaG : Fin m → Fin m → ℝ := undetGramPerturbation A DeltaA2
  have hRight :
      IsRightInverse m (fun i j => G i j + DeltaG i j)
        (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) :=
    problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound
      m hm G AAT_inv DeltaG c hc_nn hc_lt
      (by simpa [G] using hLeft)
      (by simpa [DeltaG] using hbound)
  intro i j
  simpa [G, DeltaG, undetGramPerturbation, B] using hRight i j

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    under the Chapter 7 contraction certificate, the repository
    `nonsingInv` chosen for `(A + DeltaA2)(A + DeltaA2)^T` agrees with the
    explicit inverse-perturbation candidate. -/
theorem higham21_lemma21_2_perturbed_gram_nonsingInv_eq_ch7_candidate_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    undetGramNonsingInv (fun i j => A i j + DeltaA2 i j) =
      ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2) := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  have hRight :
      IsRightInverse m (rectGram B)
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2)) := by
    simpa [B] using
      higham21_lemma21_2_perturbed_gram_ch7_candidate_right_inverse_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c hc_nn hc_lt hLeft hbound
  unfold undetGramNonsingInv
  simpa [B] using
    nonsingInv_eq_of_isRightInverse (rectGram B)
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2))
      hRight

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a concrete operator-2 certificate for the perturbed Gram inverse follows
    from the explicit Chapter 7 candidate and the Frobenius operator bound. -/
theorem higham21_lemma21_2_gram_nonsingInv_rectOpNorm2Le_frob_candidate_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    rectOpNorm2Le
      (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
      (frobNorm
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2))) := by
  rw [
    higham21_lemma21_2_perturbed_gram_nonsingInv_eq_ch7_candidate_of_abs_left_product_bound
      hm A DeltaA2 AAT_inv c hc_nn hc_lt hLeft hbound]
  exact
    rectOpNorm2Le_of_opNorm2Le_square
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2))
      (opNorm2Le_of_frobNorm_self
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2)))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    square-matrix norm bridge used to convert the Chapter 7 infinity-norm
    estimate for the explicit perturbed inverse candidate into a conservative
    Frobenius/operator-2 certificate. -/
theorem higham21_frobNorm_le_sqrt_card_sq_mul_infNorm {n : ℕ}
    (M : Fin n → Fin n → ℝ) :
    frobNorm M ≤ Real.sqrt ((n : ℝ) * (n : ℝ)) * infNorm M := by
  rw [← frobNormRect_eq_frobNorm M]
  exact
    frobNormRect_le_sqrt_mul_nat_of_entry_abs_le M (infNorm_nonneg M)
      (fun i j => ch7_abs_entry_le_infNorm M i j)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    conservative Frobenius bound for the explicit Chapter 7 perturbed inverse
    candidate, obtained by composing the local Frobenius/infinity bridge with
    the Chapter 7 inverse-candidate infinity-norm estimate. -/
theorem higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_abs_left_product_bound
    {m : ℕ}
    (hm : 0 < m)
    (AAT_inv DeltaG : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv DeltaG))
        c) :
    frobNorm (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) ≤
      Real.sqrt ((m : ℝ) * (m : ℝ)) *
        (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) := by
  let Gcand : Fin m → Fin m → ℝ :=
    ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG
  have hInf :
      infNorm Gcand ≤ ((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv := by
    simpa [Gcand] using
      problem7_11_perturbed_inverse_candidate_infNorm_bound_of_abs_left_product_bound
        m hm AAT_inv DeltaG c hc_nn hc_lt hbound
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) :=
    Real.sqrt_nonneg _
  calc
    frobNorm Gcand
        ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) * infNorm Gcand :=
          higham21_frobNorm_le_sqrt_card_sq_mul_infNorm Gcand
    _ ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) :=
          mul_le_mul_of_nonneg_left hInf hsqrt_nonneg

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar half-radius adapter for the conservative Chapter 7 inverse-candidate
    factor. -/
theorem higham21_one_div_one_sub_le_two_of_nonneg_le_half
    {c : ℝ}
    (_hc_nn : 0 ≤ c)
    (hc_half : c ≤ (1 / 2 : ℝ)) :
    1 / (1 - c) ≤ 2 := by
  have hden_pos : 0 < 1 - c := by nlinarith
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    conservative Frobenius bound for the explicit Chapter 7 perturbed inverse
    candidate under the sufficient half-radius first-product condition. -/
theorem higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_half_radius
    {m : ℕ}
    (hm : 0 < m)
    (AAT_inv DeltaG : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_half : c ≤ (1 / 2 : ℝ))
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv DeltaG))
        c) :
    frobNorm (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) ≤
      Real.sqrt ((m : ℝ) * (m : ℝ)) *
        (((m : ℝ) * 2) * infNorm AAT_inv) := by
  have hc_lt : c < 1 := by nlinarith
  have hbase :
      frobNorm (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) :=
    higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_abs_left_product_bound
      hm AAT_inv DeltaG c hc_nn hc_lt hbound
  have hfactor :
      1 / (1 - c) ≤ 2 :=
    higham21_one_div_one_sub_le_two_of_nonneg_le_half hc_nn hc_half
  have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hinner :
      (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) ≤
        (((m : ℝ) * 2) * infNorm AAT_inv) := by
    exact
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor hm_nonneg)
        (infNorm_nonneg AAT_inv)
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) :=
    Real.sqrt_nonneg _
  exact hbase.trans (mul_le_mul_of_nonneg_left hinner hsqrt_nonneg)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a componentwise Gram-perturbation estimate implies the Chapter 7 absolute
    left-product contraction certificate used for perturbed Gram
    nonsingularity. -/
theorem higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
    {m n : ℕ}
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (eps : ℝ)
    (heps : 0 ≤ eps)
    (hE : ∀ i j, 0 ≤ E i j)
    (hDeltaG :
      ∀ i j,
        |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j) :
    infNormBound m
      (absMatrix m
        (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
      (eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E)) := by
  simpa [infNormBound] using
    ch7_abs_left_product_infNorm_le_of_componentwise_bound
      m AAT_inv (undetGramPerturbation A DeltaA2) E eps heps hE hDeltaG

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise source-shaped route to perturbed Gram nonsingularity.  If the
    relative Gram perturbation is small in the Chapter 7 first-product
    sensitivity bound, then `(A + DeltaA2)(A + DeltaA2)^T` is nonsingular. -/
theorem higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_gram_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (eps : ℝ)
    (heps : 0 ≤ eps)
    (hsmall :
      eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E) < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hE : ∀ i j, 0 ≤ E i j)
    (hDeltaG :
      ∀ i j,
        |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j) :
    Matrix.det
        (rectGram (fun i j => A i j + DeltaA2 i j) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
  higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
    hm A DeltaA2 AAT_inv
    (eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E))
    (mul_nonneg heps
      (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv E)))
    hsmall hLeft
    (higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
      A DeltaA2 AAT_inv E eps heps hE hDeltaG)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise rectangular-perturbation route to perturbed Gram
    nonsingularity.  A bound `|DeltaA2| <= eps * E` induces a componentwise
    Gram perturbation budget, which is then passed to the Chapter 7
    first-product smallness condition. -/
theorem higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps : ℝ)
    (heps : 0 ≤ eps)
    (hsmall :
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hE : ∀ i k, 0 ≤ E i k)
    (hDeltaA2 : ∀ i k, |DeltaA2 i k| ≤ eps * E i k) :
    Matrix.det
        (rectGram (fun i j => A i j + DeltaA2 i j) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
  higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_gram_bound
    hm A DeltaA2 AAT_inv (undetGramPerturbationComponentBudget A E eps)
    eps heps hsmall hLeft
    (undetGramPerturbationComponentBudget_nonneg A E heps hE)
    (undetGramPerturbation_abs_le_componentBudget A DeltaA2 E heps hE hDeltaA2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    monotonicity of the Chapter 7 first-product infinity-norm sensitivity in
    the nonnegative componentwise perturbation budget. -/
theorem higham21_ch7_first_product_infNorm_le_of_componentwise_le
    {m : ℕ}
    (A_inv E F : Fin m → Fin m → ℝ)
    (hE_nonneg : ∀ i j, 0 ≤ E i j)
    (hEF : ∀ i j, E i j ≤ F i j) :
    infNorm (ch7InverseFirstProductSensitivity m A_inv E) ≤
      infNorm (ch7InverseFirstProductSensitivity m A_inv F) := by
  let PE : Fin m → Fin m → ℝ := ch7InverseFirstProductSensitivity m A_inv E
  let PF : Fin m → Fin m → ℝ := ch7InverseFirstProductSensitivity m A_inv F
  have hF_nonneg : ∀ i j, 0 ≤ F i j := by
    intro i j
    exact (hE_nonneg i j).trans (hEF i j)
  have hPE_nonneg : ∀ i j, 0 ≤ PE i j := by
    intro i j
    exact ch7InverseFirstProductSensitivity_nonneg m A_inv E hE_nonneg i j
  have hPF_nonneg : ∀ i j, 0 ≤ PF i j := by
    intro i j
    exact ch7InverseFirstProductSensitivity_nonneg m A_inv F hF_nonneg i j
  have hPE_le_PF : ∀ i j, PE i j ≤ PF i j := by
    intro i j
    simpa [PE, PF, ch7InverseFirstProductSensitivity] using
      ch7_matMul_le_of_nonneg_left m (absMatrix m A_inv) E F
        (fun i j => abs_nonneg (A_inv i j)) hEF i j
  refine infNorm_le_of_row_sum_le PE ?_ (infNorm_nonneg PF)
  intro i
  calc
    ∑ j : Fin m, |PE i j| = ∑ j : Fin m, PE i j := by
      apply Finset.sum_congr rfl
      intro j _
      exact abs_of_nonneg (hPE_nonneg i j)
    _ ≤ ∑ j : Fin m, PF i j := by
      exact Finset.sum_le_sum fun j _ => hPE_le_PF i j
    _ = ∑ j : Fin m, |PF i j| := by
      apply Finset.sum_congr rfl
      intro j _
      exact (abs_of_nonneg (hPF_nonneg i j)).symm
    _ ≤ infNorm PF :=
      row_sum_le_infNorm PF i

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-budget handoff for the Chapter 7 first-product radius condition.
    If the induced Gram perturbation budget is componentwise bounded by a
    nonnegative source Gram budget, then a radius condition for the source
    budget implies the radius condition for the induced budget. -/
theorem higham21_lemma21_2_gram_first_product_radius_of_componentwise_budget_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (EGram : Fin m → Fin m → ℝ)
    (eps rhoG : ℝ)
    (heps : 0 ≤ eps)
    (hrhoG : 0 ≤ rhoG)
    (hE : ∀ i k, 0 ≤ E i k)
    (hBudget_le :
      ∀ i j, undetGramPerturbationComponentBudget A E eps i j ≤ EGram i j)
    (hSourceRadius :
      rhoG * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram) ≤
        (1 / 2 : ℝ)) :
    rhoG *
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps)) ≤
      (1 / 2 : ℝ) := by
  have hBudget_nonneg :
      ∀ i j, 0 ≤ undetGramPerturbationComponentBudget A E eps i j :=
    undetGramPerturbationComponentBudget_nonneg A E heps hE
  have hsens_le :
      infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps)) ≤
        infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram) :=
    higham21_ch7_first_product_infNorm_le_of_componentwise_le
      AAT_inv (undetGramPerturbationComponentBudget A E eps) EGram
      hBudget_nonneg hBudget_le
  exact (mul_le_mul_of_nonneg_left hsens_le hrhoG).trans hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    perturbed Gram-pseudoinverse operator-bound reduction.  Bounds for `A`,
    the second perturbation `DeltaA2`, and the inverse candidate for
    `(A + DeltaA2)(A + DeltaA2)^T` imply the operator bound for the concrete
    table `(A + DeltaA2)^T ((A + DeltaA2)(A + DeltaA2)^T)^{-1}`.

    This does not prove the source perturbation estimate for the Gram inverse;
    it exposes that estimate as the remaining matrix-analysis obligation. -/
theorem higham21_lemma21_2_perturbed_pseudoinverse_op_bound_of_matrix_and_gram_inverse_bounds
    {m n : ℕ}
    (A DeltaA2 : Fin m → Fin n → ℝ)
    {sigma beta eta : ℝ}
    (hsigma : 0 ≤ sigma)
    (hbeta : 0 ≤ beta)
    (hA : rectOpNorm2Le A sigma)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta)
    (hGramInv :
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    rectOpNorm2Le
      (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
      ((sigma + beta) * eta) := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  have hB : rectOpNorm2Le B (sigma + beta) := by
    simpa [B] using rectOpNorm2Le_add A DeltaA2 hA hDeltaA2
  exact
    rectOpNorm2Le_undetAplusOfGramNonsingInv_of_bounds
      B (add_nonneg hsigma hbeta) hB (by simpa [B] using hGramInv)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse handoff with the scalar product budget derived
    from source-shaped perturbation and pseudoinverse-factor bounds.  The
    remaining matrix perturbation work is still the perturbed Gram
    nonsingularity and the perturbed-pseudoinverse operator estimate. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_source_factors
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_budget
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1
    hdet hxTranspose hsmall halpha hbeta heta
    (higham21_lemma21_2_product_budget_of_source_factor_bounds
      rho1 rho2 alpha beta eta hsmall halpha hbeta heta halpha_le
      hbeta_le heta_le)
    hDeltaA1Op hDeltaA2Op hBplusOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    case-split minimum-norm handoff for the source proof.  If `x = 0`, the
    single perturbation is `DeltaA2`; otherwise the existing projector/beta
    argument applies to the symmetrized perturbation.  The nonzero branch is
    still conditional on the perturbed-Gram nonsingularity and pseudoinverse
    operator estimate that remain the active source-facing gap. -/
theorem higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_product_budget
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hbudget : eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    have hnonzero :
        RectMinNormSolution m n
          (fun i j => A i j +
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
          b x :=
      higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_budget
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1
        hdet hxTranspose hsmall halpha hbeta heta hbudget hDeltaA1Op
        hDeltaA2Op hBplusOp
    simpa [undetLemma21_2SinglePerturbation, hx] using hnonzero

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    case-split handoff using source-shaped factor bounds instead of an explicit
    scalar product-budget certificate.  The theorem still exposes the genuine
    nonzero-branch matrix perturbation obligations. -/
theorem higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_source_factors
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    have hnonzero :
        RectMinNormSolution m n
          (fun i j => A i j +
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
          b x :=
      higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_source_factors
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1
        hdet hxTranspose hsmall halpha hbeta heta halpha_le hbeta_le
        heta_le hDeltaA1Op hDeltaA2Op hBplusOp
    simpa [undetLemma21_2SinglePerturbation, hx] using hnonzero

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped case split whose nonzero-branch certificates are only
    required when `x != 0`.  This records that the `x = 0` branch needs only the
    first perturbed equation, while the projector/beta branch still needs the
    perturbed-Gram and pseudoinverse product-budget certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_certificates
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet : x ≠ 0 →
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (heta : x ≠ 0 → 0 ≤ eta)
    (hbudget : x ≠ 0 →
      eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : x ≠ 0 →
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · exact
      higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_product_budget
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hDeltaA1
        (hdet hx) (hxTranspose hx) (hsmall hx) (halpha hx) (hbeta hx)
        (heta hx) (hbudget hx) (hDeltaA1Op hx) (hDeltaA2Op hx)
        (hBplusOp hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor case split.  The zero branch has no perturbation
    certificates; the nonzero branch derives the scalar product budget from
    source-shaped factor bounds and still exposes only the genuine matrix
    perturbation obligations. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_source_factors
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet : x ≠ 0 →
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (heta_le : x ≠ 0 → eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : x ≠ 0 →
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · exact
      higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_source_factors
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hDeltaA1
        (hdet hx) (hxTranspose hx) (hsmall hx) (halpha hx) (hbeta hx)
        (heta hx) (halpha_le hx) (hbeta_le hx) (heta_le hx)
        (hDeltaA1Op hx) (hDeltaA2Op hx) (hBplusOp hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with the concrete perturbed-pseudoinverse
    operator certificate derived from a perturbed-matrix bound and a Gram-inverse
    bound.  The zero branch still needs only the first perturbed equation; the
    nonzero branch now exposes perturbed Gram nonsingularity and the concrete
    Gram-inverse operator estimate as the remaining matrix-analysis obligations. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet : x ≠ 0 →
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_source_factors
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta ((sigma + beta) * eta)
    hDeltaA1 hdet hxTranspose hsmall halpha hbeta
    (fun hx => mul_nonneg (add_nonneg (hsigma hx) (hbeta hx)) (heta hx))
    halpha_le hbeta_le hGramFactor_le hDeltaA1Op hDeltaA2Op
    (fun hx =>
      higham21_lemma21_2_perturbed_pseudoinverse_op_bound_of_matrix_and_gram_inverse_bounds
        A DeltaA2 (hsigma hx) (hbeta hx) (hAOp hx) (hDeltaA2Op hx)
        (hGramInvOp hx))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    nonzero-branch handoff with perturbed Gram nonsingularity discharged by
    the Chapter 7 absolute infinity-norm contraction condition on the relative
    Gram perturbation.  The remaining explicit matrix-analysis obligation is
    the operator-2 bound for the concrete perturbed Gram inverse. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eta c : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramSmallNonneg : x ≠ 0 → 0 ≤ c)
    (hGramSmallLt : x ≠ 0 → c < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramPerturbBound : x ≠ 0 →
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma eta
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c (hGramSmallNonneg hx) (hGramSmallLt hx)
        (hGramLeftInv hx) (hGramPerturbBound hx))
    hxTranspose hsmall halpha hbeta hsigma heta halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op hGramInvOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with both perturbed Gram nonsingularity and
    the concrete Gram-inverse operator certificate derived from the Chapter 7
    absolute left-product contraction.  The remaining source-side obligation is
    the scalar factor bound for the explicit Chapter 7 inverse candidate. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma c : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramSmallNonneg : x ≠ 0 → 0 ≤ c)
    (hGramSmallLt : x ≠ 0 → c < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramPerturbBound : x ≠ 0 →
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 →
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma
    (frobNorm
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2)))
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c (hGramSmallNonneg hx) (hGramSmallLt hx)
        (hGramLeftInv hx) (hGramPerturbBound hx))
    hxTranspose hsmall halpha hbeta hsigma
    (fun _ =>
      frobNorm_nonneg
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2)))
    halpha_le hbeta_le hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op
    (fun hx =>
      higham21_lemma21_2_gram_nonsingInv_rectOpNorm2Le_frob_candidate_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c (hGramSmallNonneg hx) (hGramSmallLt hx)
        (hGramLeftInv hx) (hGramPerturbBound hx))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise Gram-perturbation version of the concrete Chapter 7
    candidate/Frobenius handoff.  The componentwise estimate supplies the
    absolute left-product contraction used by the previous theorem. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_gram_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E) < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramE : x ≠ 0 → ∀ i j, 0 ≤ E i j)
    (hGramPerturbComponent : x ≠ 0 →
      ∀ i j, |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 →
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_abs_left_product_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv rho1 rho2 alpha beta sigma
    (eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E))
    hDeltaA1
    (fun hx =>
      mul_nonneg (hGramEpsNonneg hx)
        (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv E)))
    hGramSmallLt hGramLeftInv
    (fun hx =>
      higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
        A DeltaA2 AAT_inv E eps (hGramEpsNonneg hx) (hGramE hx)
        (hGramPerturbComponent hx))
    hxTranspose hsmall halpha hbeta hsigma halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation version of the concrete Chapter 7
    candidate/Frobenius handoff.  A componentwise rectangular bound on
    `DeltaA2` induces the Gram perturbation budget used by the componentwise
    theorem above. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 →
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_gram_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv
    (undetGramPerturbationComponentBudget A E eps)
    rho1 rho2 alpha beta sigma eps hDeltaA1 hDataEpsNonneg
    hGramSmallLt hGramLeftInv
    (fun hx =>
      undetGramPerturbationComponentBudget_nonneg A E
        (hDataEpsNonneg hx) (hDataE hx))
    (fun hx =>
      undetGramPerturbation_abs_le_componentBudget A DeltaA2 E
        (hDataEpsNonneg hx) (hDataE hx) (hDeltaA2Component hx))
    hxTranspose hsmall halpha hbeta hsigma halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with the Chapter 7 candidate factor
    replaced by a concrete conservative bound from the inverse-candidate
    infinity-norm estimate.  The remaining explicit source obligation is the
    smallness of the induced first product. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hConservativeFactor_le : x ≠ 0 →
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) *
                (1 /
                  (1 -
                    eps *
                      infNorm
                        (ch7InverseFirstProductSensitivity m AAT_inv
                          (undetGramPerturbationComponentBudget A E eps)))))
              * infNorm AAT_inv)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let EGram : Fin m → Fin m → ℝ :=
    undetGramPerturbationComponentBudget A E eps
  let c : ℝ :=
    eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram)
  refine
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E
      rho1 rho2 alpha beta sigma eps hDeltaA1 hDataEpsNonneg
      hGramSmallLt hGramLeftInv hDataE hDeltaA2Component hxTranspose
      hsmall halpha hbeta hsigma halpha_le hbeta_le ?_ hAOp
      hDeltaA1Op hDeltaA2Op
  intro hx
  have hGramBound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c := by
    simpa [c, EGram] using
      higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
        A DeltaA2 AAT_inv EGram eps (hDataEpsNonneg hx)
        (by
          simpa [EGram] using
            undetGramPerturbationComponentBudget_nonneg A E
              (hDataEpsNonneg hx) (hDataE hx))
        (by
          simpa [EGram] using
            undetGramPerturbation_abs_le_componentBudget A DeltaA2 E
              (hDataEpsNonneg hx) (hDataE hx) (hDeltaA2Component hx))
  have hCand :
      frobNorm
          (ch7Problem711PerturbedInverseCandidate m AAT_inv
            (undetGramPerturbation A DeltaA2)) ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) :=
    higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_abs_left_product_bound
      hm AAT_inv (undetGramPerturbation A DeltaA2) c
      (by
        dsimp [c, EGram]
        exact mul_nonneg (hDataEpsNonneg hx)
          (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps))))
      (by simpa [c, EGram] using hGramSmallLt hx) hGramBound
  have hscaled :
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) *
                (1 /
                  (1 -
                    eps *
                      infNorm
                        (ch7InverseFirstProductSensitivity m AAT_inv
                          (undetGramPerturbationComponentBudget A E eps)))))
              * infNorm AAT_inv)) := by
    simpa [c, EGram] using
      mul_le_mul_of_nonneg_left hCand (add_nonneg (hsigma hx) (hbeta hx))
  exact hscaled.trans (hConservativeFactor_le hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with a sufficient half-radius
    first-product condition.  This replaces the explicit `1 / (1 - c)` factor
    in the previous conservative handoff by the simpler source-facing bound
    using the constant `2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_half_radius_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallHalf : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hConservativeFactor_le : x ≠ 0 →
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let EGram : Fin m → Fin m → ℝ :=
    undetGramPerturbationComponentBudget A E eps
  let c : ℝ :=
    eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram)
  refine
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
      hDeltaA1 hDataEpsNonneg ?_ hGramLeftInv hDataE
      hDeltaA2Component hxTranspose hsmall halpha hbeta hsigma
      halpha_le hbeta_le ?_ hAOp hDeltaA1Op hDeltaA2Op
  · intro hx
    have hhalf : c ≤ (1 / 2 : ℝ) := by
      simpa [c, EGram] using hGramSmallHalf hx
    nlinarith
  · intro hx
    have hc_nn : 0 ≤ c := by
      dsimp [c, EGram]
      exact mul_nonneg (hDataEpsNonneg hx)
        (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv
          (undetGramPerturbationComponentBudget A E eps)))
    have hfactor :
        1 / (1 - c) ≤ 2 :=
      higham21_one_div_one_sub_le_two_of_nonneg_le_half hc_nn
        (by simpa [c, EGram] using hGramSmallHalf hx)
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    have hinner :
        (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) ≤
          (((m : ℝ) * 2) * infNorm AAT_inv) := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactor hm_nonneg)
          (infNorm_nonneg AAT_inv)
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) :=
      Real.sqrt_nonneg _
    have hsqrt :
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) ≤
          Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv) :=
      mul_le_mul_of_nonneg_left hinner hsqrt_nonneg
    have hscaled :
        (sigma + beta) *
            (Real.sqrt ((m : ℝ) * (m : ℝ)) *
              (((m : ℝ) *
                  (1 /
                    (1 -
                      eps *
                        infNorm
                          (ch7InverseFirstProductSensitivity m AAT_inv
                            (undetGramPerturbationComponentBudget A E eps)))))
                * infNorm AAT_inv)) ≤
          (sigma + beta) *
            (Real.sqrt ((m : ℝ) * (m : ℝ)) *
              (((m : ℝ) * 2) * infNorm AAT_inv)) := by
      simpa [c, EGram] using
        mul_le_mul_of_nonneg_left hsqrt (add_nonneg (hsigma hx) (hbeta hx))
    exact hscaled.trans (hConservativeFactor_le hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with a source-radius smallness
    condition.  The half-radius first-product condition is discharged from
    `eps <= rhoG` and `rhoG * || |AAT_inv| EGram ||_inf <= 1/2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramSmallRadius : x ≠ 0 →
      rhoG *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hConservativeFactor_le : x ≠ 0 →
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  refine
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_half_radius_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
      hDeltaA1 hDataEpsNonneg ?_ hGramLeftInv hDataE
      hDeltaA2Component hxTranspose hsmall halpha hbeta hsigma
      halpha_le hbeta_le hConservativeFactor_le hAOp hDeltaA1Op
      hDeltaA2Op
  intro hx
  have hsens_nonneg :
      0 ≤
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps)) :=
    infNorm_nonneg _
  exact
    (mul_le_mul_of_nonneg_right (hDataEpsLeRho hx) hsens_nonneg).trans
      (hGramSmallRadius hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-factor adapter for the conservative Chapter 7 candidate
    bound.  A bound on `sigma + beta` and a bound on `||AAT_inv||_inf`
    imply the concrete conservative factor inequality consumed by the
    rectangular data handoff. -/
theorem higham21_lemma21_2_conservative_ch7_factor_le_of_source_bounds
    {m : ℕ}
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho2 sigma beta tau omega : ℝ)
    (hsigma : 0 ≤ sigma)
    (hbeta : 0 ≤ beta)
    (hSigmaBeta_le : sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹) :
    (sigma + beta) *
        (Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
      (1 - rho2)⁻¹ := by
  have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hm2_nonneg : 0 ≤ (m : ℝ) * 2 :=
    mul_nonneg hm_nonneg (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) :=
    Real.sqrt_nonneg _
  have hinv_nonneg : 0 ≤ infNorm AAT_inv :=
    infNorm_nonneg AAT_inv
  have hconcrete_nonneg :
      0 ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * infNorm AAT_inv) :=
    mul_nonneg hsqrt_nonneg (mul_nonneg hm2_nonneg hinv_nonneg)
  have htau_nonneg : 0 ≤ tau :=
    (add_nonneg hsigma hbeta).trans hSigmaBeta_le
  have hstep_left :
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) :=
    mul_le_mul_of_nonneg_right hSigmaBeta_le hconcrete_nonneg
  have hinner :
      ((m : ℝ) * 2) * infNorm AAT_inv ≤ ((m : ℝ) * 2) * omega :=
    mul_le_mul_of_nonneg_left hAATInv_le hm2_nonneg
  have hsize :
      Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * infNorm AAT_inv) ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * omega) :=
    mul_le_mul_of_nonneg_left hinner hsqrt_nonneg
  have hstep_right :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) :=
    mul_le_mul_of_nonneg_left hsize htau_nonneg
  exact (hstep_left.trans hstep_right).trans hSourceFactor_le

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with separated source-size scalar
    bounds.  The remaining scalar source obligation is the simplified factor
    involving an upper bound for `sigma + beta` and `||AAT_inv||_inf`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramSmallRadius : x ≠ 0 →
      rhoG *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps rhoG
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho hGramSmallRadius hGramLeftInv
    hDataE hDeltaA2Component hxTranspose hsmall halpha hbeta hsigma
    halpha_le hbeta_le
    (fun hx =>
      higham21_lemma21_2_conservative_ch7_factor_le_of_source_bounds
        AAT_inv rho2 sigma beta tau omega (hsigma hx) (hbeta hx)
        (hSigmaBeta_le hx) hAATInv_le hSourceFactor_le)
    hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with separated source-size scalar
    bounds and a source Gram-budget radius certificate.  This wrapper replaces
    the exact induced Gram first-product radius by a larger componentwise source
    Gram budget. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_budget_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (EGram : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramBudget_le : x ≠ 0 →
      ∀ i j, undetGramPerturbationComponentBudget A E eps i j ≤ EGram i j)
    (hGramSourceRadius : x ≠ 0 →
      rhoG * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps rhoG
    tau omega hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    (fun hx =>
      higham21_lemma21_2_gram_first_product_radius_of_componentwise_budget_bound
        A AAT_inv E EGram eps rhoG (hDataEpsNonneg hx)
        ((hDataEpsNonneg hx).trans (hDataEpsLeRho hx)) (hDataE hx)
        (hGramBudget_le hx) (hGramSourceRadius hx))
    hGramLeftInv hDataE hDeltaA2Component hxTranspose hsmall halpha hbeta
    hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le hSourceFactor_le
    hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget specialization of the conservative rectangular
    data-perturbation handoff.  The induced Gram budget is bounded internally
    by `undetGramPerturbationRowNormBudget`, leaving only a radius condition for
    that row-norm source budget. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_row_norm_budget_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramRowNormRadius : x ≠ 0 →
      rhoG *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationRowNormBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_budget_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E
    (undetGramPerturbationRowNormBudget A E eps)
    rho1 rho2 alpha beta sigma eps rhoG tau omega
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    (fun hx =>
      undetGramPerturbationComponentBudget_le_rowNormBudget A E
        (hDataEpsNonneg hx) (hDataE hx))
    hGramRowNormRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha hbeta hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le
    hSourceFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    sufficient row-budget radius certificate from separated infinity-norm
    bounds.  This turns the Chapter 7 first-product smallness condition for
    the row-norm Gram budget into the scalar source obligations
    `‖AAT_inv‖∞ <= omega`, `‖rowBudget‖∞ <= gamma`, and
    `rhoG * (omega * gamma) <= 1/2`. -/
theorem higham21_lemma21_2_row_norm_first_product_radius_of_infNorm_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps rhoG omega gamma : ℝ)
    (hrhoG : 0 ≤ rhoG)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hRowBudget_le :
      infNorm (undetGramPerturbationRowNormBudget A E eps) ≤ gamma)
    (homega : 0 ≤ omega)
    (hRadius : rhoG * (omega * gamma) ≤ (1 / 2 : ℝ)) :
    rhoG *
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationRowNormBudget A E eps)) ≤
      (1 / 2 : ℝ) := by
  let G : Fin m → Fin m → ℝ := undetGramPerturbationRowNormBudget A E eps
  change rhoG * infNorm (matMul m (absMatrix m AAT_inv) G) ≤ (1 / 2 : ℝ)
  have hprod :
      infNorm (matMul m (absMatrix m AAT_inv) G) ≤ omega * gamma := by
    have hsub : infNorm (matMul m (absMatrix m AAT_inv) G) ≤
        infNorm (absMatrix m AAT_inv) * infNorm G :=
      infNorm_matMul_le hm (absMatrix m AAT_inv) G
    have habs : infNorm (absMatrix m AAT_inv) = infNorm AAT_inv :=
      infNorm_absMatrix hm AAT_inv
    have hmul : infNorm (absMatrix m AAT_inv) * infNorm G ≤ omega * gamma := by
      rw [habs]
      exact mul_le_mul hAATInv_le hRowBudget_le (infNorm_nonneg G) homega
    exact hsub.trans hmul
  exact (mul_le_mul_of_nonneg_left hprod hrhoG).trans hRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm Gram budget infinity-norm bound from uniform row-norm bounds on
    the data matrix and perturbation majorant. -/
theorem undetGramPerturbationRowNormBudget_infNorm_le_of_row_norm_bounds
    {m n : ℕ}
    (A E : Fin m → Fin n → ℝ)
    {eps a e : ℝ}
    (heps : 0 ≤ eps)
    (hArow : ∀ i : Fin m, rectRowNorm2 A i ≤ a)
    (hErow : ∀ i : Fin m, rectRowNorm2 E i ≤ e)
    (ha : 0 ≤ a)
    (he : 0 ≤ e) :
    infNorm (undetGramPerturbationRowNormBudget A E eps) ≤
      (m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)) := by
  let C : ℝ := (n : ℝ) * (a * e + e * a + eps * e * e)
  have hinner_nonneg : 0 ≤ a * e + e * a + eps * e * e := by
    exact add_nonneg
      (add_nonneg (mul_nonneg ha he) (mul_nonneg he ha))
      (mul_nonneg (mul_nonneg heps he) he)
  have hC_nonneg : 0 ≤ C :=
    mul_nonneg (by exact_mod_cast Nat.zero_le n) hinner_nonneg
  have hbound_entry :
      ∀ i j : Fin m, undetGramPerturbationRowNormBudget A E eps i j ≤ C := by
    intro i j
    have hAE :
        rectRowNorm2 A i * rectRowNorm2 E j ≤ a * e :=
      mul_le_mul (hArow i) (hErow j) (rectRowNorm2_nonneg E j) ha
    have hEA :
        rectRowNorm2 E i * rectRowNorm2 A j ≤ e * a :=
      mul_le_mul (hErow i) (hArow j) (rectRowNorm2_nonneg A j) he
    have hEE :
        eps * rectRowNorm2 E i * rectRowNorm2 E j ≤ eps * e * e := by
      have hEprod :
          rectRowNorm2 E i * rectRowNorm2 E j ≤ e * e :=
        mul_le_mul (hErow i) (hErow j) (rectRowNorm2_nonneg E j) he
      calc
        eps * rectRowNorm2 E i * rectRowNorm2 E j
            = eps * (rectRowNorm2 E i * rectRowNorm2 E j) := by ring
        _ ≤ eps * (e * e) := mul_le_mul_of_nonneg_left hEprod heps
        _ = eps * e * e := by ring
    have hsum :
        rectRowNorm2 A i * rectRowNorm2 E j +
            rectRowNorm2 E i * rectRowNorm2 A j +
            eps * rectRowNorm2 E i * rectRowNorm2 E j ≤
          a * e + e * a + eps * e * e :=
      add_le_add (add_le_add hAE hEA) hEE
    unfold undetGramPerturbationRowNormBudget C
    exact mul_le_mul_of_nonneg_left hsum (by exact_mod_cast Nat.zero_le n)
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin m, |undetGramPerturbationRowNormBudget A E eps i j|
          = ∑ j : Fin m, undetGramPerturbationRowNormBudget A E eps i j := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_of_nonneg
              (undetGramPerturbationRowNormBudget_nonneg A E heps i j)
      _ ≤ ∑ _j : Fin m, C := by
            apply Finset.sum_le_sum
            intro j _
            exact hbound_entry i j
      _ = (m : ℝ) * C := by
            simp [C]
      _ = (m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)) := rfl
  · exact mul_nonneg (by exact_mod_cast Nat.zero_le m) hC_nonneg

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-sized row-norm radius certificate from uniform row-norm bounds on
    `A` and `E`. -/
theorem higham21_lemma21_2_row_norm_first_product_radius_of_row_norm_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps rhoG omega a e : ℝ)
    (heps : 0 ≤ eps)
    (hrhoG : 0 ≤ rhoG)
    (hArow : ∀ i : Fin m, rectRowNorm2 A i ≤ a)
    (hErow : ∀ i : Fin m, rectRowNorm2 E i ≤ e)
    (ha : 0 ≤ a)
    (he : 0 ≤ e)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hRadius :
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))) ≤
        (1 / 2 : ℝ)) :
    rhoG *
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationRowNormBudget A E eps)) ≤
      (1 / 2 : ℝ) := by
  have homega : 0 ≤ omega :=
    (infNorm_nonneg AAT_inv).trans hAATInv_le
  exact
    higham21_lemma21_2_row_norm_first_product_radius_of_infNorm_bounds
      hm A AAT_inv E eps rhoG omega
      ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))
      hrhoG hAATInv_le
      (undetGramPerturbationRowNormBudget_infNorm_le_of_row_norm_bounds
        A E heps hArow hErow ha he)
      homega hRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget handoff with the Chapter 7 radius condition reduced
    to separated infinity-norm scalar bounds. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_infNorm_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega gamma : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hRowBudget_le : x ≠ 0 →
      infNorm (undetGramPerturbationRowNormBudget A E eps) ≤ gamma)
    (hRowRadius : x ≠ 0 → rhoG * (omega * gamma) ≤ (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  have homega : 0 ≤ omega :=
    (infNorm_nonneg AAT_inv).trans hAATInv_le
  exact
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_row_norm_budget_bounds_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
      rhoG tau omega hDeltaA1 hDataEpsNonneg hDataEpsLeRho
      (fun hx =>
        higham21_lemma21_2_row_norm_first_product_radius_of_infNorm_bounds
          hm A AAT_inv E eps rhoG omega gamma (hrhoG hx) hAATInv_le
          (hRowBudget_le hx) homega (hRowRadius hx))
      hGramLeftInv hDataE hDeltaA2Component hxTranspose hsmall halpha hbeta
      hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le hSourceFactor_le
      hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget handoff with the row-budget infinity norm discharged
    from uniform row-norm bounds on `A` and `E`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega a e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hArow : x ≠ 0 → ∀ i : Fin m, rectRowNorm2 A i ≤ a)
    (hErow : x ≠ 0 → ∀ i : Fin m, rectRowNorm2 E i ≤ e)
    (ha : x ≠ 0 → 0 ≤ a)
    (he : x ≠ 0 → 0 ≤ e)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_infNorm_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
    rhoG tau omega
    ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG
    (fun hx =>
      undetGramPerturbationRowNormBudget_infNorm_le_of_row_norm_bounds
        A E (hDataEpsNonneg hx) (hArow hx) (hErow hx) (ha hx) (he hx))
    hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose hsmall
    halpha hbeta hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le
    hSourceFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget handoff with the row-norm bounds on `A` and `E`
    discharged from operator-2 certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_op_norm_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
    rhoG tau omega sigma e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG
    (fun hx i =>
      higham21_rectRowNorm2_le_of_rectOpNorm2Le A i (hsigma hx) (hAOp hx))
    (fun hx i =>
      higham21_rectRowNorm2_le_of_rectOpNorm2Le E i (he hx) (hEOp hx))
    hsigma he hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha hbeta hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le
    hSourceFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-norm row-budget handoff with the `DeltaA2` operator certificate
    discharged from the componentwise data perturbation bound and an
    operator-2 certificate for `E`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_op_norm_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha (eps * e) sigma
    eps rhoG tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG
    hEOp he hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha
    (fun hx => mul_nonneg (hDataEpsNonneg hx) (he hx))
    hsigma halpha_le hEpsE_le hSigmaEpsE_le hAATInv_le hSourceFactor_le
    hAOp hDeltaA1Op
    (fun hx =>
      higham21_rectOpNorm2Le_of_componentwise_data_bound DeltaA2 E
        (hDataEpsNonneg hx) (hDeltaA2Component hx) (hEOp hx))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with the conservative source scalar factor
    supplied in the simpler quadratic dimension form. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_quadratic_source_factor
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha sigma eps rhoG
    tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp he
    hEpsE_le hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha hsigma halpha_le hSigmaEpsE_le hAATInv_le
    (higham21_lemma21_2_source_factor_le_of_quadratic_bound
      m rho2 tau omega hSourceFactor_le)
    hAOp hDeltaA1Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with both perturbation operator certificates
    discharged from componentwise data bounds against the same majorant `E`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_op_bounds_quadratic_source_factor
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_quadratic_source_factor
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 (eps * e) sigma eps
    rhoG tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp
    he hEpsE_le_rho2 hRowRadius hGramLeftInv hDataE hDeltaA2Component
    hxTranspose hsmall
    (fun hx => mul_nonneg (hDataEpsNonneg hx) (he hx))
    hsigma hEpsE_le_rho1 hSigmaEpsE_le hAATInv_le hSourceFactor_le hAOp
    (fun hx =>
      higham21_rectOpNorm2Le_of_componentwise_data_bound DeltaA1 E
        (hDataEpsNonneg hx) (hDeltaA1Component hx) (hEOp hx))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar row-radius adapter.  The source-sized envelope
    `sigma + eps * e <= tau` bounds the row-budget expression
    `sigma*e + e*sigma + eps*e*e` by `2*e*tau`. -/
theorem higham21_lemma21_2_row_radius_of_source_size_bound
    (m n : ℕ) {sigma eps e tau omega rhoG : ℝ}
    (heps : 0 ≤ eps)
    (he : 0 ≤ e)
    (homega : 0 ≤ omega)
    (hrhoG : 0 ≤ rhoG)
    (hSigmaEpsE_le : sigma + eps * e ≤ tau)
    (hSourceRadius :
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (2 * e * tau)))) ≤
        (1 / 2 : ℝ)) :
    rhoG *
        (omega *
          ((m : ℝ) *
            ((n : ℝ) *
              (sigma * e + e * sigma + eps * e * e)))) ≤
      (1 / 2 : ℝ) := by
  have heps_e_nonneg : 0 ≤ eps * e := mul_nonneg heps he
  have hsigma_le_tau : sigma ≤ tau :=
    (le_add_of_nonneg_right heps_e_nonneg).trans hSigmaEpsE_le
  have hsum : sigma + (sigma + eps * e) ≤ tau + tau :=
    add_le_add hsigma_le_tau hSigmaEpsE_le
  have hrow_term :
      sigma * e + e * sigma + eps * e * e ≤ 2 * e * tau := by
    calc
      sigma * e + e * sigma + eps * e * e
          = e * (sigma + (sigma + eps * e)) := by ring
      _ ≤ e * (tau + tau) := mul_le_mul_of_nonneg_left hsum he
      _ = 2 * e * tau := by ring
  have hn :
      (n : ℝ) * (sigma * e + e * sigma + eps * e * e) ≤
        (n : ℝ) * (2 * e * tau) :=
    mul_le_mul_of_nonneg_left hrow_term (by exact_mod_cast Nat.zero_le n)
  have hm :
      (m : ℝ) *
          ((n : ℝ) * (sigma * e + e * sigma + eps * e * e)) ≤
        (m : ℝ) * ((n : ℝ) * (2 * e * tau)) :=
    mul_le_mul_of_nonneg_left hn (by exact_mod_cast Nat.zero_le m)
  have homega_mul :
      omega *
          ((m : ℝ) *
            ((n : ℝ) *
              (sigma * e + e * sigma + eps * e * e))) ≤
        omega * ((m : ℝ) * ((n : ℝ) * (2 * e * tau))) :=
    mul_le_mul_of_nonneg_left hm homega
  exact (mul_le_mul_of_nonneg_left homega_mul hrhoG).trans hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-size scalar adapter.  Separate source bounds for the unperturbed
    matrix size and the data perturbation size imply the combined
    `sigma + eps * e <= tau` envelope used by the row-radius handoff. -/
theorem higham21_lemma21_2_source_size_bound_of_separate_bounds
    {sigma eps e tauA tauE tau : ℝ}
    (hSigma_le : sigma ≤ tauA)
    (hEpsE_le : eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau) :
    sigma + eps * e ≤ tau := by
  exact (add_le_add hSigma_le hEpsE_le).trans hSourceSize

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar row-radius adapter from the flat source product form to the nested
    product shape consumed by the Chapter 7 first-product handoff. -/
theorem higham21_lemma21_2_row_radius_of_flat_source_product
    (m n : ℕ) {e tau omega rhoG : ℝ}
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ)) :
    rhoG *
        (omega *
          ((m : ℝ) * ((n : ℝ) * (2 * e * tau)))) ≤
      (1 / 2 : ℝ) := by
  have hshape :
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (2 * e * tau)))) =
        2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG := by
    ring
  simpa [hshape] using hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with the row-radius scalar obligation
    reduced to the source-sized envelope `2*e*tau`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) * (2 * e * tau)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  have homega : 0 ≤ omega :=
    (infNorm_nonneg AAT_inv).trans hAATInv_le
  exact
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_op_bounds_quadratic_source_factor
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
      tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp he
      hEpsE_le_rho1 hEpsE_le_rho2
      (fun hx =>
        higham21_lemma21_2_row_radius_of_source_size_bound m n
          (hDataEpsNonneg hx) (he hx) homega (hrhoG hx) (hSigmaEpsE_le hx)
          (hRowRadius hx))
      hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
      hsmall hsigma hSigmaEpsE_le hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with separated source-size bounds and a
    flat source-radius product.  This wrapper removes the combined
    `sigma + eps * e <= tau` and nested row-radius certificates from the public
    surface used by the guarded nonzero branch. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_separated_source_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp he
    hEpsE_le_rho1 hEpsE_le_rho2
    (fun hx =>
      higham21_lemma21_2_row_radius_of_flat_source_product m n
        (hFlatSourceRadius hx))
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hsigma
    (fun hx =>
      higham21_lemma21_2_source_size_bound_of_separate_bounds
        (hSigma_le hx) (hEpsE_le_tauE hx) hSourceSize)
    hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from one common perturbation-radius bound to the two
    separate radius inequalities used by the source-factor handoff. -/
theorem higham21_lemma21_2_epsE_le_radii_of_le_min
    {eps e rho1 rho2 : ℝ}
    (hEpsE_le_min : eps * e ≤ min rho1 rho2) :
    eps * e ≤ rho1 ∧ eps * e ≤ rho2 :=
  le_min_iff.mp hEpsE_le_min

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a common perturbation-radius bound.
    This replaces the duplicate `eps * e <= rho1` and `eps * e <= rho2`
    obligations by the single source-shaped inequality
    `eps * e <= min rho1 rho2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_radius_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_separated_source_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      (higham21_lemma21_2_epsE_le_radii_of_le_min
        (hEpsE_le_min hx)).1)
    (fun hx =>
      (higham21_lemma21_2_epsE_le_radii_of_le_min
        (hEpsE_le_min hx)).2)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from a source perturbation-size cap to the common
    `min rho1 rho2` radius bound. -/
theorem higham21_lemma21_2_epsE_le_min_of_source_radius
    {eps e rho rho1 rho2 : ℝ}
    (hEpsE_le_rho : eps * e ≤ rho)
    (hrho_le_min : rho ≤ min rho1 rho2) :
    eps * e ≤ min rho1 rho2 :=
  hEpsE_le_rho.trans hrho_le_min

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a separate source perturbation-size cap.
    This replaces the direct `eps * e <= min rho1 rho2` obligation by
    `eps * e <= rho` together with `rho <= min rho1 rho2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho : x ≠ 0 → eps * e ≤ rho)
    (hrho_le_min : rho ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      higham21_lemma21_2_epsE_le_min_of_source_radius
        (hEpsE_le_rho hx) hrho_le_min)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-radius adapter from the branch bound `eps <= rhoG` and a
    source product cap `rhoG * e <= rho`. -/
theorem higham21_lemma21_2_epsE_le_source_radius_of_eps_le_rhoG
    {eps rhoG e rho : ℝ}
    (hEps_le_rhoG : eps ≤ rhoG)
    (he : 0 ≤ e)
    (hRhoGE_le_rho : rhoG * e ≤ rho) :
    eps * e ≤ rho :=
  (mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_rho

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a source product cap for the
    perturbation-size radius.  This replaces `eps * e <= rho` by the branch
    bound `eps <= rhoG`, nonnegativity of `e`, and `rhoG * e <= rho`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_product_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_min : rho ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 sigma eps
    rhoG tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      higham21_lemma21_2_epsE_le_source_radius_of_eps_le_rhoG
        (hDataEpsLeRho hx) (he hx) (hRhoGE_le_rho hx))
    hrho_le_min hFlatSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall hsigma
    hSigma_le hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from separate source radius comparisons to the common
    `min rho1 rho2` comparison. -/
theorem higham21_lemma21_2_source_radius_le_min_of_bounds
    {rho rho1 rho2 : ℝ}
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2) :
    rho ≤ min rho1 rho2 :=
  le_min hrho_le_rho1 hrho_le_rho2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with separate source comparisons from the
    perturbation cap `rho` to the two Lemma 21.2 smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_split_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_product_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 sigma eps
    rhoG tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he hRhoGE_le_rho
    (higham21_lemma21_2_source_radius_le_min_of_bounds
      hrho_le_rho1 hrho_le_rho2)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from branch-wise `rhoG * e` bounds to the common
    `eps * e <= min rho1 rho2` radius condition. -/
theorem higham21_lemma21_2_epsE_le_min_of_eps_le_rhoG_product_bounds
    {eps rhoG e rho1 rho2 : ℝ}
    (hEps_le_rhoG : eps ≤ rhoG)
    (he : 0 ≤ e)
    (hRhoGE_le_rho1 : rhoG * e ≤ rho1)
    (hRhoGE_le_rho2 : rhoG * e ≤ rho2) :
    eps * e ≤ min rho1 rho2 :=
  le_min
    ((mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_rho1)
    ((mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_rho2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from one common `rhoG * e` product-radius bound to the two
    branch-wise product bounds used by the nonzero-branch source handoff. -/
theorem higham21_lemma21_2_rhoGE_le_radii_of_le_min
    {rhoG e rho1 rho2 : ℝ}
    (hRhoGE_le_min : rhoG * e ≤ min rho1 rho2) :
    rhoG * e ≤ rho1 ∧ rhoG * e ≤ rho2 :=
  le_min_iff.mp hRhoGE_le_min

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    branch-wise perturbation-radius bounds imply the common min-radius bound. -/
theorem higham21_lemma21_2_epsE_le_min_of_branch_bounds
    {eps e rho1 rho2 : ℝ}
    (hEpsE_le_rho1 : eps * e ≤ rho1)
    (hEpsE_le_rho2 : eps * e ≤ rho2) :
    eps * e ≤ min rho1 rho2 :=
  le_min hEpsE_le_rho1 hEpsE_le_rho2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-size adapter from the branch perturbation bound
    `eps <= rhoG` and a product-size cap `rhoG * e <= tauE`. -/
theorem higham21_lemma21_2_epsE_le_tauE_of_eps_le_rhoG_product_bound
    {eps rhoG e tauE : ℝ}
    (hEps_le_rhoG : eps ≤ rhoG)
    (he : 0 ≤ e)
    (hRhoGE_le_tauE : rhoG * e ≤ tauE) :
    eps * e ≤ tauE :=
  (mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_tauE

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar nonnegativity adapter for a source radius majorant. -/
theorem higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
    {eps rhoG : ℝ}
    (hEps_nonneg : 0 ≤ eps)
    (hEps_le_rhoG : eps ≤ rhoG) :
    0 ≤ rhoG :=
  hEps_nonneg.trans hEps_le_rhoG

/-- A nonzero finite vector can exist only over a nonempty `Fin` domain. -/
theorem higham21_nonempty_fin_of_vec_ne_zero {n : ℕ}
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    Nonempty (Fin n) := by
  cases n with
  | zero =>
      exfalso
      exact hx (by funext i; exact Fin.elim0 i)
  | succ n =>
      exact ⟨⟨0, Nat.succ_pos n⟩⟩

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-envelope nonnegativity adapter for the nonzero branch. -/
theorem higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
    {m n : ℕ}
    {x : Fin n → ℝ}
    (E : Fin m → Fin n → ℝ)
    {e : ℝ}
    (hx : x ≠ 0)
    (hEOp : rectOpNorm2Le E e) :
    0 ≤ e := by
  letI : Nonempty (Fin n) := higham21_nonempty_fin_of_vec_ne_zero hx
  exact rectOpNorm2Le_radius_nonneg E hEOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with branch-wise source product bounds
    against the two Lemma 21.2 smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_rhoG_product_radius_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_rho1 : x ≠ 0 → rhoG * e ≤ rho1)
    (hRhoGE_le_rho2 : x ≠ 0 → rhoG * e ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      higham21_lemma21_2_epsE_le_min_of_eps_le_rhoG_product_bounds
        (hDataEpsLeRho hx) (he hx)
        (hRhoGE_le_rho1 hx) (hRhoGE_le_rho2 hx))
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a common `rhoG * e` product-radius
    bound.  This replaces the two branch-wise product-radius obligations by the
    single source-shaped inequality `rhoG * e <= min rho1 rho2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_rhoG_product_radius_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      (higham21_lemma21_2_rhoGE_le_radii_of_le_min
        (hRhoGE_le_min hx)).1)
    (fun hx =>
      (higham21_lemma21_2_rhoGE_le_radii_of_le_min
        (hRhoGE_le_min hx)).2)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common product-radius handoff with the data-perturbation source-size
    obligation also expressed as a `rhoG * e` product bound. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_and_size_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he hRhoGE_le_min hFlatSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    (fun hx =>
      higham21_lemma21_2_epsE_le_tauE_of_eps_le_rhoG_product_bound
        (hDataEpsLeRho hx) (he hx) (hRhoGE_le_tauE hx))
    hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common `rhoG * e` product-radius and product-size handoff with the
    unperturbed matrix operator envelope written directly as the source-size
    quantity `tauA`.  This is the same dependency chain as the preceding
    wrapper with `sigma = tauA`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (htauA : x ≠ 0 → 0 ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_and_size_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 tauA eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall htauA (fun _ => le_rfl) hSourceSize hAATInv_le
    hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    `tauA` operator-envelope handoff with nonnegativity of the radius majorant
    derived from the source perturbation bounds `0 <= eps` and `eps <= rhoG`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_eps_nonneg
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (htauA : x ≠ 0 → 0 ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    (fun hx =>
      higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
        (hDataEpsNonneg hx) (hDataEpsLeRho hx))
    hEOp he hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall htauA hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    `tauA` operator-envelope handoff with both radius nonnegativity side
    conditions derived from the source perturbation and operator certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_operator_envelopes
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (htauA : x ≠ 0 → 0 ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_eps_nonneg
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hEOp
    (fun hx =>
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        E hx (hEOp hx))
    hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall htauA
    hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator-envelope handoff for the current nonzero branch.  The
    nonnegativity of both operator radii is derived from the `A` and `E`
    operator-envelope certificates on the active branch. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_operator_envelopes
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hEOp hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose hsmall
    (fun hx =>
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        A hx (hAOp hx))
    hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator-envelope handoff with the perturbation-size contribution
    written directly as `rhoG * e`, removing the auxiliary `tauE` envelope. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA (rhoG * e) tau omega e hDeltaA1 hDataEpsNonneg
    hDataEpsLeRho hEOp hRhoGE_le_min (fun _ => le_rfl)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hSourceSize hAATInv_le
    hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/product-size handoff with the common product-radius
    condition derived from a source cap `rhoG * e <= rho` and separate
    comparisons of `rho` with the two smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_split_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    (fun hx =>
      (hRhoGE_le_rho hx).trans
        (higham21_lemma21_2_source_radius_le_min_of_bounds
          hrho_le_rho1 hrho_le_rho2))
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hSourceSize hAATInv_le
    hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter deriving the flat source-radius product from a source
    perturbation cap `rhoG * e <= rho`. -/
theorem higham21_lemma21_2_flat_source_radius_of_product_cap
    (m n : ℕ) {rhoG e rho tau omega : ℝ}
    (htau : 0 ≤ tau)
    (homega : 0 ≤ omega)
    (hRhoGE_le_rho : rhoG * e ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * rho ≤
        (1 / 2 : ℝ)) :
    2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
      (1 / 2 : ℝ) := by
  have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hfactor_nonneg :
      0 ≤ 2 * (m : ℝ) * (n : ℝ) * tau * omega := by
    have h2m : 0 ≤ (2 : ℝ) * (m : ℝ) :=
      mul_nonneg (by norm_num) hm_nonneg
    have h2mn : 0 ≤ (2 : ℝ) * (m : ℝ) * (n : ℝ) :=
      mul_nonneg h2m hn_nonneg
    have h2mnt : 0 ≤ (2 : ℝ) * (m : ℝ) * (n : ℝ) * tau :=
      mul_nonneg h2mn htau
    exact mul_nonneg h2mnt homega
  have hmul :
      (2 * (m : ℝ) * (n : ℝ) * tau * omega) *
          (rhoG * e) ≤
        (2 * (m : ℝ) * (n : ℝ) * tau * omega) * rho :=
    mul_le_mul_of_nonneg_left hRhoGE_le_rho hfactor_nonneg
  have hleft :
      (2 * (m : ℝ) * (n : ℝ) * tau * omega) *
          (rhoG * e) =
        2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG := by
    ring
  have hright :
      (2 * (m : ℝ) * (n : ℝ) * tau * omega) * rho =
        2 * (m : ℝ) * (n : ℝ) * tau * omega * rho := by
    ring
  have hflat :
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        2 * (m : ℝ) * (n : ℝ) * tau * omega * rho := by
    simpa [hleft, hright] using hmul
  exact hflat.trans hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter deriving the flat source-radius product from the common
    product-radius bound `rhoG * e <= min rho1 rho2`. -/
theorem higham21_lemma21_2_flat_source_radius_of_common_product_radius
    (m n : ℕ) {rhoG e rho1 rho2 tau omega : ℝ}
    (htau : 0 ≤ tau)
    (homega : 0 ≤ omega)
    (hRhoGE_le_min : rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * min rho1 rho2 ≤
        (1 / 2 : ℝ)) :
    2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
      (1 / 2 : ℝ) :=
  higham21_lemma21_2_flat_source_radius_of_product_cap
    (rho := min rho1 rho2) m n htau homega hRhoGE_le_min hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the source smallness condition bounds the second perturbation radius away
    from one. -/
theorem higham21_lemma21_2_rho2_lt_one_of_three_max_lt_one
    {rho1 rho2 : ℝ}
    (hsmall : 3 * max rho1 rho2 < 1) :
    rho2 < 1 := by
  have hrho2_le : rho2 ≤ max rho1 rho2 := le_max_right rho1 rho2
  nlinarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the second source radius is nonnegative and below one, then the
    reciprocal factor `(1 - rho2)^{-1}` is at least one. -/
theorem higham21_lemma21_2_one_le_inv_one_sub_of_nonneg_lt_one
    {rho2 : ℝ}
    (hrho2_nonneg : 0 ≤ rho2)
    (hrho2_lt_one : rho2 < 1) :
    1 ≤ (1 - rho2)⁻¹ := by
  have hden_pos : 0 < 1 - rho2 := by linarith
  have hden_le_one : 1 - rho2 ≤ 1 := by linarith
  exact (one_le_inv₀ hden_pos).2 hden_le_one

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    unit source-factor bound implies the inverse-factor bound once
    `0 <= rho2` and the source smallness condition are known. -/
theorem higham21_lemma21_2_source_factor_le_inv_of_unit_bound
    (m : ℕ) {rho1 rho2 tau omega : ℝ}
    (hrho2_nonneg : 0 ≤ rho2)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hSourceFactor_le_one :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ 1) :
    2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹ :=
  hSourceFactor_le_one.trans
    (higham21_lemma21_2_one_le_inv_one_sub_of_nonneg_lt_one hrho2_nonneg
      (higham21_lemma21_2_rho2_lt_one_of_three_max_lt_one hsmall))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a min-radius source-factor bound implies the unit source-factor bound under
    the source smallness condition. -/
theorem higham21_lemma21_2_source_factor_le_one_of_min_radius_bound
    (m : ℕ) {rho1 rho2 tau omega : ℝ}
    (hsmall : 3 * max rho1 rho2 < 1)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ min rho1 rho2) :
    2 * (m : ℝ) ^ 2 * tau * omega ≤ 1 := by
  have hmax_lt_one : max rho1 rho2 < 1 := by nlinarith
  have hmin_le_max : min rho1 rho2 ≤ max rho1 rho2 :=
    (min_le_left rho1 rho2).trans (le_max_left rho1 rho2)
  exact le_of_lt
    (lt_of_le_of_lt (hSourceFactor_le_min.trans hmin_le_max) hmax_lt_one)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from a source-factor cap to the min-radius source-factor
    bound. -/
theorem higham21_lemma21_2_source_factor_le_min_of_cap
    (m : ℕ) {rho rho1 rho2 tau omega : ℝ}
    (hSourceFactor_le_rho :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2) :
    2 * (m : ℝ) ^ 2 * tau * omega ≤ min rho1 rho2 :=
  hSourceFactor_le_rho.trans
    (higham21_lemma21_2_source_radius_le_min_of_bounds
      hrho_le_rho1 hrho_le_rho2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from a min-radius cap comparison to the two branch
    comparisons. -/
theorem higham21_lemma21_2_source_cap_le_radii_of_le_min
    {rho rho1 rho2 : ℝ}
    (hrho_le_min : rho ≤ min rho1 rho2) :
    rho ≤ rho1 ∧ rho ≤ rho2 :=
  ⟨hrho_le_min.trans (min_le_left rho1 rho2),
    hrho_le_min.trans (min_le_right rho1 rho2)⟩

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the source-size envelope implies nonnegativity of `tau` on the nonzero
    branch once the operator radii and data perturbation radius are available. -/
theorem higham21_lemma21_2_tau_nonneg_of_source_size
    {m n : ℕ}
    (A E : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    {eps rhoG tauA tau e : ℝ}
    (hx : x ≠ 0)
    (hDataEpsNonneg : 0 ≤ eps)
    (hDataEpsLeRho : eps ≤ rhoG)
    (hEOp : rectOpNorm2Le E e)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAOp : rectOpNorm2Le A tauA) :
    0 ≤ tau := by
  have htauA : 0 ≤ tauA :=
    higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero A hx hAOp
  have he : 0 ≤ e :=
    higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero E hx hEOp
  have hrhoG : 0 ≤ rhoG :=
    higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
      hDataEpsNonneg hDataEpsLeRho
  exact (add_nonneg htauA (mul_nonneg hrhoG he)).trans hSourceSize

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    nonnegativity of an inverse-norm majorant follows from the infinity-norm
    certificate. -/
theorem higham21_lemma21_2_omega_nonneg_of_infNorm_bound
    {m : ℕ}
    (AAT_inv : Fin m → Fin m → ℝ)
    {omega : ℝ}
    (hAATInv_le : infNorm AAT_inv ≤ omega) :
    0 ≤ omega :=
  (infNorm_nonneg AAT_inv).trans hAATInv_le

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    in the nonzero branch, the common product-radius bound makes `rho2`
    nonnegative because `rhoG` and the operator envelope radius `e` are
    nonnegative. -/
theorem higham21_lemma21_2_rho2_nonneg_of_common_product_radius
    {m n : ℕ}
    (E : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    {eps rhoG e rho1 rho2 : ℝ}
    (hx : x ≠ 0)
    (hDataEpsNonneg : 0 ≤ eps)
    (hDataEpsLeRho : eps ≤ rhoG)
    (hEOp : rectOpNorm2Le E e)
    (hRhoGE_le_min : rhoG * e ≤ min rho1 rho2) :
    0 ≤ rho2 := by
  have hrhoG : 0 ≤ rhoG :=
    higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
      hDataEpsNonneg hDataEpsLeRho
  have he : 0 ≤ e :=
    higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero E hx hEOp
  have hprod_nonneg : 0 ≤ rhoG * e := mul_nonneg hrhoG he
  exact hprod_nonneg.trans (hRhoGE_le_min.trans (min_le_right rho1 rho2))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/product-size handoff with the flat source-radius product
    derived from the same source perturbation cap used for the smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (htau : 0 ≤ tau)
    (homega : 0 ≤ omega)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_split_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    hRhoGE_le_rho hrho_le_rho1 hrho_le_rho2
    (fun hx =>
      higham21_lemma21_2_flat_source_radius_of_product_cap
        m n htau homega (hRhoGE_le_rho hx) hSourceRadius)
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    flat source-radius handoff with nonnegativity of `tau` and `omega`
    derived from the active source-size and inverse-norm certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_product_bound_of_source_nonneg
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_split_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    hRhoGE_le_rho hrho_le_rho1 hrho_le_rho2
    (fun hx =>
      higham21_lemma21_2_flat_source_radius_of_product_cap
        m n
        (higham21_lemma21_2_tau_nonneg_of_source_size A E hx
          (hDataEpsNonneg hx) (hDataEpsLeRho hx) (hEOp hx)
          hSourceSize (hAOp hx))
        (higham21_lemma21_2_omega_nonneg_of_infNorm_bound
          AAT_inv hAATInv_le)
        (hRhoGE_le_rho hx) hSourceRadius)
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/product-size handoff with the flat source-radius product
    derived directly from the common `rhoG * e <= min rho1 rho2` product
    radius, avoiding an auxiliary source cap `rho`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_common_radius_product_bound_of_source_nonneg
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    hRhoGE_le_min
    (fun hx =>
      higham21_lemma21_2_flat_source_radius_of_common_product_radius
        m n
        (higham21_lemma21_2_tau_nonneg_of_source_size A E hx
          (hDataEpsNonneg hx) (hDataEpsLeRho hx) (hEOp hx)
          hSourceSize (hAOp hx))
        (higham21_lemma21_2_omega_nonneg_of_infNorm_bound
          AAT_inv hAATInv_le)
        (hRhoGE_le_min hx) hSourceRadius)
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/common-radius handoff with the source-size envelope
    specialized to the exact quantity `tauA + rhoG * e`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + rhoG * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * (tauA + rhoG * e) * omega ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_common_radius_product_bound_of_source_nonneg
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA (tauA + rhoG * e) omega e hDeltaA1 hDataEpsNonneg
    hDataEpsLeRho hEOp hRhoGE_le_min hSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall le_rfl
    hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with the inverse source-factor condition
    discharged from a unit source-factor bound in the nonzero branch.  The
    zero branch still uses only the first perturbed equation, as in the printed
    proof's separate `x = 0` case. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_unit_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + rhoG * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_one : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + rhoG * e) * omega ≤ 1)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · exact
      higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_product_bound
        hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG tauA omega e
        hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp hRhoGE_le_min
        hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
        hxTranspose hsmall hAATInv_le
        (higham21_lemma21_2_source_factor_le_inv_of_unit_bound m
          (higham21_lemma21_2_rho2_nonneg_of_common_product_radius E hx
            (hDataEpsNonneg hx) (hDataEpsLeRho hx) (hEOp hx)
            (hRhoGE_le_min hx))
          (hsmall hx) (hSourceFactor_le_one hx))
        hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with the source factor supplied in the
    min-radius form.  The source smallness condition converts that min-radius
    bound to the unit source-factor condition consumed by the nonzero branch. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + rhoG * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + rhoG * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_unit_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG tauA omega e
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp hRhoGE_le_min hSourceRadius
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose hsmall
    hAATInv_le
    (fun hx =>
      higham21_lemma21_2_source_factor_le_one_of_min_radius_bound m
        (hsmall hx) (hSourceFactor_le_min hx))
    hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff specialized to the printed perturbation
    size `eps`, eliminating the auxiliary `rhoG` radius when the source bounds
    are already stated directly in terms of `eps * e`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps eps tauA omega e
    hDeltaA1 hDataEpsNonneg (fun _ => le_rfl) hEOp hEpsE_le_min
    hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
    hxTranspose hsmall hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with the printed smallness condition
    supplied by a common cap on the two perturbation-product radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rho eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le : rho1 ≤ rho)
    (hrho2_le : rho2 ≤ rho)
    (hrho_small : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min hSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    (fun _ =>
      higham21_lemma21_2_three_max_lt_one_of_common_bound
        rho1 rho2 rho hrho1_le hrho2_le hrho_small)
    hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with global scalar, operator-envelope,
    inverse, componentwise-data, and min-radius source-factor assumptions.
    The only remaining branch-dependent assumption is the nonzero-branch
    transpose representation of `x`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall eps tauA omega e
    hDeltaA1 (fun _ => hDataEpsNonneg) (fun _ => hEOp)
    (fun _ => hEpsE_le_min) hSourceRadius (fun _ => hGramLeftInv)
    (fun _ => hDataE) (fun _ => hDeltaA1Component)
    (fun _ => hDeltaA2Component) hxTranspose hrho1_le_small
    hrho2_le_small hrhoSmall hAATInv_le (fun _ => hSourceFactor_le_min)
    (fun _ => hAOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    global min-factor handoff with the printed smallness shape
    `3 * max rho1 rho2 < 1`, avoiding an auxiliary common-smallness radius. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_min_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_global_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 (max rho1 rho2)
    eps tauA omega e hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min
    hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
    hxTranspose (le_max_left rho1 rho2) (le_max_right rho1 rho2) hsmall
    hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    printed-smallness/global min-factor handoff with the scalar source-radius
    condition supplied against `max rho1 rho2`.  In the nonzero branch,
    `min rho1 rho2 <= max rho1 rho2` and nonnegativity of the source
    coefficient convert this to the min-radius condition consumed downstream. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_min_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadiusMax :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · let coeff : ℝ :=
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega
    have htauA : 0 ≤ tauA :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero A hx hAOp
    have he : 0 ≤ e :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero E hx hEOp
    have homega : 0 ≤ omega :=
      higham21_lemma21_2_omega_nonneg_of_infNorm_bound AAT_inv
        hAATInv_le
    have hcoeff_nonneg : 0 ≤ coeff := by
      have htwo : 0 ≤ (2 : ℝ) := by norm_num
      have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hsize : 0 ≤ tauA + eps * e :=
        add_nonneg htauA (mul_nonneg hDataEpsNonneg he)
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg htwo hm_nonneg) hn_nonneg)
          hsize)
        homega
    have hmin_le_max : min rho1 rho2 ≤ max rho1 rho2 :=
      (min_le_left rho1 rho2).trans (le_max_left rho1 rho2)
    have hSourceRadius :
        2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
            min rho1 rho2 ≤
          (1 / 2 : ℝ) := by
      change coeff * min rho1 rho2 ≤ (1 / 2 : ℝ)
      exact
        (mul_le_mul_of_nonneg_left hmin_le_max hcoeff_nonneg).trans
          (by simpa [coeff] using hSourceRadiusMax)
    exact
      higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_min_factor_global_bounds
        hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
        hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min hSourceRadius
        hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
        hxTranspose hsmall hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    printed-smallness/max-radius handoff with the perturbation-radius and
    source-factor min-radius obligations supplied by one scalar max bound. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_combined_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactorMax :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        min rho1 rho2)
    (hSourceRadiusMax :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_min_factor_global_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp
    ((le_max_left (eps * e)
      (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega)).trans
      hRadiusFactorMax)
    hSourceRadiusMax hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hAATInv_le
    ((le_max_right (eps * e)
      (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega)).trans
      hRadiusFactorMax)
    hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common-radius version of the printed-smallness/max-radius combined-factor
    handoff.  This packages the two source radii by a single scalar majorant
    `rho`, matching the printed `max` smallness condition more closely while
    keeping the scalar radius and operator-envelope obligations explicit. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_common_radius_combined_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  have hRadiusFactorMin :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        min rho rho := by
    simpa using hRadiusFactor
  have hSourceRadiusMax :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max rho rho ≤
        (1 / 2 : ℝ) := by
    simpa using hSourceRadius
  have hsmallMax : 3 * max rho rho < 1 := by
    simpa using hsmall
  simpa [min_self, max_self] using
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_combined_factor_global_bounds
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho eps tauA omega e
      hDeltaA1 hDataEpsNonneg hEOp hRadiusFactorMin hSourceRadiusMax
      hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
      hxTranspose hsmallMax hAATInv_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    combined-factor handoff with the common radius instantiated by the
    concrete scalar
    `max (eps * e) (2*m^2*(tauA + eps*e)*omega)`.  This removes the auxiliary
    radius parameter from the previous wrapper while keeping the scalar
    smallness, source-radius, operator-envelope, and componentwise-data
    obligations explicit. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_common_radius_combined_factor_global_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E
    (max (eps * e)
      (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega))
    eps tauA omega e hDeltaA1 hDataEpsNonneg hEOp le_rfl
    hCombinedSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hCombinedSmall hAATInv_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with common-smallness and source-factor
    caps separated. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall rhoFactor eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_cap : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ rhoFactor)
    (hFactorCap_le_rho1 : rhoFactor ≤ rho1)
    (hFactorCap_le_rho2 : rhoFactor ≤ rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min hSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hrho1_le_small hrho2_le_small hrhoSmall hAATInv_le
    (fun hx =>
      higham21_lemma21_2_source_factor_le_min_of_cap m
        (hSourceFactor_le_cap hx) hFactorCap_le_rho1 hFactorCap_le_rho2)
    hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-factor-cap handoff with global scalar, operator-envelope, and
    componentwise data assumptions.  The only remaining branch-dependent
    assumption is the nonzero-branch transpose representation of `x`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall rhoFactor eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_cap :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ rhoFactor)
    (hFactorCap_le_rho1 : rhoFactor ≤ rho1)
    (hFactorCap_le_rho2 : rhoFactor ≤ rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall rhoFactor
    eps tauA omega e hDeltaA1 (fun _ => hDataEpsNonneg)
    (fun _ => hEOp) (fun _ => hEpsE_le_min) hSourceRadius
    (fun _ => hGramLeftInv) (fun _ => hDataE)
    (fun _ => hDeltaA1Component) (fun _ => hDeltaA2Component)
    hxTranspose hrho1_le_small hrho2_le_small hrhoSmall hAATInv_le
    (fun _ => hSourceFactor_le_cap) hFactorCap_le_rho1 hFactorCap_le_rho2
    (fun _ => hAOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    global source-factor-cap handoff with the cap comparison supplied as a
    single min-radius bound. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_min_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall rhoFactor eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_cap :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ rhoFactor)
    (hFactorCap_le_min : rhoFactor ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  rcases higham21_lemma21_2_source_cap_le_radii_of_le_min
      hFactorCap_le_min with
    ⟨hFactorCap_le_rho1, hFactorCap_le_rho2⟩
  exact
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_global_bounds
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall rhoFactor
      eps tauA omega e hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min
      hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
      hxTranspose hrho1_le_small hrho2_le_small hrhoSmall hAATInv_le
      hSourceFactor_le_cap hFactorCap_le_rho1 hFactorCap_le_rho2 hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size `eps`-specialized handoff with the source perturbation-radius
    condition supplied as separate bounds for the two perturbation radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_branch_radius_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp
    (fun hx =>
      higham21_lemma21_2_epsE_le_min_of_branch_bounds
        (hEpsE_le_rho1 hx) (hEpsE_le_rho2 hx))
    hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
    hxTranspose hsmall hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size `eps` handoff with both perturbation radii instantiated by the
    common conservative majorant `eps * e`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_self_radius_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          (eps * e) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * (eps * e) < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_radius : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ eps * e)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_branch_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E (eps * e) (eps * e) eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp (fun _ => le_rfl) (fun _ => le_rfl)
    (by simpa using hSourceRadius) hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose
    (fun hx =>
      higham21_lemma21_2_three_max_lt_one_of_common_bound
        (eps * e) (eps * e) (eps * e) le_rfl le_rfl (hsmall hx))
    hAATInv_le (fun hx => by simpa using hSourceFactor_le_radius hx) hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-style self-radius `eps` handoff with global scalar, operator-envelope,
    and componentwise data assumptions.  The only remaining branch-dependent
    assumption is the nonzero-branch transpose representation of `x`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          (eps * e) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * (eps * e) < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_radius :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ eps * e)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_self_radius_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E eps tauA omega e hDeltaA1
    (fun _ => hDataEpsNonneg) (fun _ => hEOp) hSourceRadius
    (fun _ => hGramLeftInv) (fun _ => hDataE) (fun _ => hDeltaA1Component)
    (fun _ => hDeltaA2Component) hxTranspose (fun _ => hsmall)
    hAATInv_le (fun _ => hSourceFactor_le_radius) (fun _ => hAOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with perturbed Gram nonsingularity discharged
    from a componentwise bound on the Gram perturbation.  The remaining
    nonzero-branch matrix-analysis obligation is the concrete operator-2 bound
    for the perturbed Gram inverse. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds_of_componentwise_gram_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eta eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E) < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramE : x ≠ 0 → ∀ i j, 0 ≤ E i j)
    (hGramPerturbComponent : x ≠ 0 →
      ∀ i j, |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma eta
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_gram_bound
        hm A DeltaA2 AAT_inv E eps (hGramEpsNonneg hx)
        (hGramSmallLt hx) (hGramLeftInv hx) (hGramE hx)
        (hGramPerturbComponent hx))
    hxTranspose hsmall halpha hbeta hsigma heta halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op hGramInvOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with perturbed Gram nonsingularity discharged
    from a componentwise bound on the rectangular perturbation `DeltaA2`.
    The only remaining nonzero-branch matrix-analysis obligation is the
    concrete operator-2 bound for the perturbed Gram inverse. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eta eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma eta
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_data_bound
        hm A DeltaA2 AAT_inv E eps (hDataEpsNonneg hx)
        (hGramSmallLt hx) (hGramLeftInv hx) (hDataE hx)
        (hDeltaA2Component hx))
    hxTranspose hsmall halpha hbeta hsigma heta halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op hGramInvOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped pseudoinverse handoff for the remaining beta argument.
    If `Bplus` is a perturbed pseudoinverse for `B = A + DeltaA2` whose
    domain projection fixes `x`, and `Bplus` has the source perturbation
    operator bound, then the existing separate-operator bridge proves the
    single-perturbation minimum-norm system.

    The still-open matrix perturbation work is to instantiate the projection
    and operator-bound hypotheses for the concrete `(A + DeltaA2)^+`. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_perturbed_pseudoinverse
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDomainSym :
      IsSymmetricFiniteMatrix
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)))
    (hDomainX :
      rectMatMulVec
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let y : Fin m → ℝ := rectMatMulVec (finiteTranspose Bplus) x
  have hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x := by
    simpa [y] using
      higham21_lemma21_2_perturbed_pseudoinverse_transpose_solves_of_domain_projection
        (fun i j => A i j + DeltaA2 i j) Bplus x hDomainSym hDomainX
  have hy : vecNorm2 y ≤ eta * vecNorm2 x := by
    simpa [y] using
      higham21_lemma21_2_dual_vector_bound_of_perturbed_pseudoinverse_op_bound
        Bplus x heta hBplusOp
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_factor
      A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1 hDeltaA2
      hsmall halpha hbeta heta halpha_le hbeta_le heta_le hDeltaA1Op hDeltaA2Op hy

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Moore--Penrose specialization of the perturbed-pseudoinverse beta handoff.
    A pseudoinverse certificate supplies the domain-projection symmetry needed
    by the source proof; the remaining open perturbation work is the projection
    fixing `x` and the operator bound for the concrete perturbed pseudoinverse. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_moore_penrose_pseudoinverse_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (fun i j => A i j + DeltaA2 i j) Bplus)
    (hDomainX :
      rectMatMulVec
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_perturbed_pseudoinverse
    A x DeltaA1 DeltaA2 b Bplus rho1 rho2 alpha beta eta hsq hDeltaA1
    hMP.domain_projection_symmetric hDomainX hsmall halpha hbeta heta
    halpha_le hbeta_le heta_le hDeltaA1Op hDeltaA2Op hBplusOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse specialization of the beta handoff for
    `B = A + DeltaA2`.  Under nonsingularity of `B Bᵀ`, the source table
    `Bᵀ(BBᵀ)⁻¹` supplies the Moore--Penrose certificate used by the previous
    wrapper. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hDomainX :
      rectMatMulVec
        (rectMatMul
          (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
          (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  have hMP : RectMoorePenrosePseudoinverse m n B (undetAplusOfGramNonsingInv B) :=
    higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero B (by
      simpa [B] using hdet)
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_moore_penrose_pseudoinverse_bound
      A x DeltaA1 DeltaA2 b (undetAplusOfGramNonsingInv B)
      rho1 rho2 alpha beta eta hsq hDeltaA1 hMP
      (by simpa [B] using hDomainX) hsmall halpha hbeta heta
      halpha_le hbeta_le heta_le hDeltaA1Op hDeltaA2Op
      (by simpa [B] using hBplusOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse range specialization of the beta handoff.
    Instead of assuming the domain projection fixes `x` directly, it suffices
    that `x` is explicitly represented as `(A + DeltaA2)^+ yB`. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_range
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (yB : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxRange :
      x =
        rectMatMulVec
          (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
          yB)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  refine
    higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_bound
      A x DeltaA1 DeltaA2 b rho1 rho2 alpha beta eta hsq hDeltaA1 hdet
      ?_ hsmall halpha hbeta heta halpha_le hbeta_le heta_le
      hDeltaA1Op hDeltaA2Op hBplusOp
  rw [hxRange]
  simpa [B] using
    higham21_lemma21_2_gram_pseudoinverse_domain_projection_apply_range
      B (by simpa [B] using hdet) yB

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped Gram-pseudoinverse range handoff.  The printed hypothesis
    `x = (A + DeltaA2)ᵀ y` supplies the concrete pseudoinverse-range
    representation needed by the beta/minimum-norm argument. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_transpose_range
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  refine
    higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_range
      A x DeltaA1 DeltaA2 b (matMulVec m (rectGram B) y)
      rho1 rho2 alpha beta eta hsq hDeltaA1 hdet ?_
      hsmall halpha hbeta heta halpha_le hbeta_le heta_le
      hDeltaA1Op hDeltaA2Op hBplusOp
  calc
    x = rectTransposeMulVec B y := by
      simpa [B] using hxTranspose
    _ =
        rectMatMulVec (undetAplusOfGramNonsingInv B)
          (matMulVec m (rectGram B) y) := by
      exact
        higham21_lemma21_2_gram_pseudoinverse_range_of_transpose
          B (by simpa [B] using hdet) y

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the Frobenius-squared norm bound for the projector mixture used to replace
    two perturbation blocks by one. -/
theorem higham21_lemma21_2_symmetrized_perturbation_frobNormSq_le {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormSqRect (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) ≤
      frobNormSqRect DeltaA1 + frobNormSqRect DeltaA2 := by
  have h :=
    lsLemma20_6Perturbation_frobNormSqRect_le
      x hsq (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)
  simpa [undetLemma21_2SymmetrizedPerturbation, frobNormSqRect_finiteTranspose, add_comm]
    using h

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Frobenius-norm form of the printed bound
    `||Delta A||_F <= (||Delta A_1||_F^2 + ||Delta A_2||_F^2)^(1/2)` for the
    projector mixture. -/
theorem higham21_lemma21_2_symmetrized_perturbation_frob_bound {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormRect (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) ≤
      Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) := by
  have h :=
    lsLemma20_6Perturbation_norm_bound_two_frob
      x hsq (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)
  simpa [undetLemma21_2SymmetrizedPerturbation, frobNormRect_finiteTranspose, add_comm]
    using h

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-2 norm form of the printed bound for the projector mixture.  If
    the two original perturbation blocks have operator-2 bounds `alpha` and
    `beta`, then the constructed perturbation has bound
    `(alpha^2 + beta^2)^(1/2)`. -/
theorem higham21_lemma21_2_symmetrized_perturbation_op_bound {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    rectOpNorm2Le (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2)
      (Real.sqrt (alpha ^ 2 + beta ^ 2)) := by
  have hDeltaA2T : rectOpNorm2Le (finiteTranspose DeltaA2) beta :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le DeltaA2 hbeta hDeltaA2
  have hDeltaA1T : rectOpNorm2Le (finiteTranspose DeltaA1) alpha :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le DeltaA1 halpha hDeltaA1
  have hbase :
      rectOpNorm2Le
        (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1))
        (Real.sqrt (beta ^ 2 + alpha ^ 2)) :=
    lsLemma20_6Perturbation_norm_bound_two_operator
      x hsq (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)
      hbeta halpha hDeltaA2T hDeltaA1T
  have htrans :
      rectOpNorm2Le
        (finiteTranspose
          (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)))
        (Real.sqrt (beta ^ 2 + alpha ^ 2)) :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1))
      (Real.sqrt_nonneg _) hbase
  have hrad : beta ^ 2 + alpha ^ 2 = alpha ^ 2 + beta ^ 2 := by ring
  simpa [undetLemma21_2SymmetrizedPerturbation, hrad] using htrans

private theorem higham21_right_nonneg_le_sqrt_sq_add_sq
    (a b : ℝ) (hb : 0 ≤ b) :
    b ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  have hb_sq : b ^ 2 ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg a]
  have hsqrt : Real.sqrt (b ^ 2) ≤ Real.sqrt (a ^ 2 + b ^ 2) :=
    Real.sqrt_le_sqrt hb_sq
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hb] using hsqrt

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    squared Frobenius-norm form of the printed perturbation bound for the
    source-case single perturbation.  In the zero branch the perturbation is
    `DeltaA2`; in the nonzero branch it is the projector mixture. -/
theorem higham21_lemma21_2_single_perturbation_frobNormSq_le {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormSqRect (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) ≤
      frobNormSqRect DeltaA1 + frobNormSqRect DeltaA2 := by
  by_cases hx : x = 0
  · have hD1 : 0 ≤ frobNormSqRect DeltaA1 := frobNormSqRect_nonneg DeltaA1
    have hbound :
        frobNormSqRect DeltaA2 ≤ frobNormSqRect DeltaA1 + frobNormSqRect DeltaA2 := by
      nlinarith
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_frobNormSq_le
        x hsq DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Frobenius-norm form of the printed perturbation bound for the source-case
    single perturbation. -/
theorem higham21_lemma21_2_single_perturbation_frob_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormRect (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) ≤
      Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) := by
  by_cases hx : x = 0
  · have hbound :
        frobNormRect DeltaA2 ≤
          Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) :=
      higham21_right_nonneg_le_sqrt_sq_add_sq
        (frobNormRect DeltaA1) (frobNormRect DeltaA2)
        (frobNormRect_nonneg DeltaA2)
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_frob_bound
        x hsq DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    squared row-wise 2-norm form of the printed perturbation bound for the
    projector mixture. -/
theorem higham21_lemma21_2_symmetrized_perturbation_rowNormSq_le {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) (i : Fin m) :
    vecNorm2Sq
        (fun j : Fin n =>
          undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) ≤
      vecNorm2Sq (fun j : Fin n => DeltaA1 i j) +
        vecNorm2Sq (fun j : Fin n => DeltaA2 i j) := by
  let C1 : Fin n → Fin 1 → ℝ := fun j _ => DeltaA2 i j
  let C2 : Fin n → Fin 1 → ℝ := fun j _ => DeltaA1 i j
  have hbase :=
    lsLemma20_6Perturbation_frobNormSqRect_le x hsq C1 C2
  have hleft :
      frobNormSqRect (lsLemma20_6Perturbation x C1 C2) =
        vecNorm2Sq
          (fun j : Fin n =>
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) := by
    simp [frobNormSqRect, vecNorm2Sq, C1, C2,
      undetLemma21_2SymmetrizedPerturbation, lsLemma20_6Perturbation,
      finiteTranspose, matMulRectLeft]
  have hC1 :
      frobNormSqRect C1 =
        vecNorm2Sq (fun j : Fin n => DeltaA2 i j) := by
    simp [frobNormSqRect, vecNorm2Sq, C1]
  have hC2 :
      frobNormSqRect C2 =
        vecNorm2Sq (fun j : Fin n => DeltaA1 i j) := by
    simp [frobNormSqRect, vecNorm2Sq, C2]
  calc
    vecNorm2Sq
        (fun j : Fin n =>
          undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
        = frobNormSqRect (lsLemma20_6Perturbation x C1 C2) := hleft.symm
    _ ≤ frobNormSqRect C1 + frobNormSqRect C2 := hbase
    _ = vecNorm2Sq (fun j : Fin n => DeltaA1 i j) +
        vecNorm2Sq (fun j : Fin n => DeltaA2 i j) := by
          rw [hC1, hC2]
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-wise 2-norm form of the printed perturbation bound for the projector
    mixture. -/
theorem higham21_lemma21_2_symmetrized_perturbation_row_bound {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) (i : Fin m) :
    rectRowNorm2 (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) i ≤
      Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 + rectRowNorm2 DeltaA2 i ^ 2) := by
  apply (sq_le_sq₀
    (rectRowNorm2_nonneg
      (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) i)
    (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  simpa [rectRowNorm2, vecNorm2_sq] using
    higham21_lemma21_2_symmetrized_perturbation_rowNormSq_le
      x hsq DeltaA1 DeltaA2 i

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-wise 2-norm form of the printed perturbation bound for the source-case
    single perturbation.  In the zero branch the perturbation is `DeltaA2`;
    in the nonzero branch it is the projector mixture. -/
theorem higham21_lemma21_2_single_perturbation_row_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) (i : Fin m) :
    rectRowNorm2 (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) i ≤
      Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 + rectRowNorm2 DeltaA2 i ^ 2) := by
  by_cases hx : x = 0
  · have hbound :
        rectRowNorm2 DeltaA2 i ≤
          Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 + rectRowNorm2 DeltaA2 i ^ 2) :=
      higham21_right_nonneg_le_sqrt_sq_add_sq
        (rectRowNorm2 DeltaA1 i) (rectRowNorm2 DeltaA2 i)
        (rectRowNorm2_nonneg DeltaA2 i)
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_row_bound
        x hsq DeltaA1 DeltaA2 i

private theorem higham21_sqrt_sq_add_sq_le_sqrt_two_mul
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha_le : a ≤ c) (hb_le : b ≤ c) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt 2 * c := by
  have ha_sq : a ^ 2 ≤ c ^ 2 := (sq_le_sq₀ ha hc).mpr ha_le
  have hb_sq : b ^ 2 ≤ c ^ 2 := (sq_le_sq₀ hb hc).mpr hb_le
  apply (sq_le_sq₀
    (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hc)).mp
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    entrywise row-relative perturbation bounds imply the row-2-norm bound used
    by the row-wise backward-error model. -/
theorem higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
    {m n : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaA : ∀ i k, |DeltaA i k| ≤ eta * |A i k|)
    (i : Fin m) :
    rectRowNorm2 DeltaA i ≤ eta * rectRowNorm2 A i := by
  calc
    rectRowNorm2 DeltaA i
        ≤ vecNorm2 (fun k : Fin n => eta * |A i k|) := by
          simpa [rectRowNorm2] using
            vecNorm2_le_of_abs_le
              (fun k : Fin n => DeltaA i k)
              (fun k : Fin n => eta * |A i k|)
              (fun k => hDeltaA i k)
    _ = eta * rectRowNorm2 A i := by
          rw [vecNorm2_smul, abs_of_nonneg heta, vecNorm2_abs]
          rfl

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common row-wise relative-bound corollary for the source-case single
    perturbation.  If both input perturbations are bounded row-by-row by
    `eta * ||A(i,:)||_2`, the constructed single perturbation is bounded
    row-by-row by `sqrt 2 * eta * ||A(i,:)||_2`. -/
theorem higham21_lemma21_2_single_perturbation_row_bound_of_common_row_bound
    {m n : ℕ}
    (x : Fin n → ℝ)
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaA1 : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2 : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i)
    (i : Fin m) :
    rectRowNorm2 (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) i ≤
      Real.sqrt 2 * eta * rectRowNorm2 A i := by
  have hrow :=
    higham21_lemma21_2_single_perturbation_row_bound
      x DeltaA1 DeltaA2 i
  have hcommon_nonneg : 0 ≤ eta * rectRowNorm2 A i :=
    mul_nonneg heta (rectRowNorm2_nonneg A i)
  have hsqrt :
      Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 +
          rectRowNorm2 DeltaA2 i ^ 2) ≤
        Real.sqrt 2 * (eta * rectRowNorm2 A i) :=
    higham21_sqrt_sq_add_sq_le_sqrt_two_mul
      (rectRowNorm2_nonneg DeltaA1 i)
      (rectRowNorm2_nonneg DeltaA2 i)
      hcommon_nonneg (hDeltaA1 i) (hDeltaA2 i)
  calc
    rectRowNorm2 (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) i
        ≤ Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 +
            rectRowNorm2 DeltaA2 i ^ 2) := hrow
    _ ≤ Real.sqrt 2 * (eta * rectRowNorm2 A i) := hsqrt
    _ = Real.sqrt 2 * eta * rectRowNorm2 A i := by ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-2 norm form of the printed perturbation bound for the source-case
    single perturbation. -/
theorem higham21_lemma21_2_single_perturbation_op_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    rectOpNorm2Le (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2)
      (Real.sqrt (alpha ^ 2 + beta ^ 2)) := by
  by_cases hx : x = 0
  · have hbeta_le : beta ≤ Real.sqrt (alpha ^ 2 + beta ^ 2) :=
      higham21_right_nonneg_le_sqrt_sq_add_sq alpha beta hbeta
    have hbound :
        rectOpNorm2Le DeltaA2 (Real.sqrt (alpha ^ 2 + beta ^ 2)) :=
      rectOpNorm2Le_mono hbeta_le hDeltaA2
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_op_bound
        x hsq DeltaA1 DeltaA2 halpha hbeta hDeltaA1 hDeltaA2

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

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    once the Lemma 21.2 single perturbation is known to make `x_hat` a
    minimum-norm solution, common row-wise relative bounds on the two source
    perturbations give a row-wise backward-error witness with factor
    `sqrt 2 * eta`. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
    {m n : ℕ}
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hmin :
      RectMinNormSolution m n
        (fun i j =>
          A i j + undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2 i j)
        b x_hat)
    (hDeltaA1 : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2 : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat (Real.sqrt 2 * eta) :=
  higham21_rowwise_backward_error_bound_witness m n A
    (undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2) b x_hat
    (Real.sqrt 2 * eta)
    (mul_nonneg (Real.sqrt_nonneg 2) heta)
    hmin
    (fun i => by
      simpa [mul_assoc] using
        higham21_lemma21_2_single_perturbation_row_bound_of_common_row_bound
          x_hat A DeltaA1 DeltaA2 heta hDeltaA1 hDeltaA2 i)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff with a common source radius
    `rho`.  This version matches the printed smallness/radius shape more
    directly than the self-radius wrapper while still leaving the QR/Q-method
    row-bound obligations explicit. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
    A DeltaA1 DeltaA2 b x_hat heta
    (higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_common_radius_combined_factor_global_bounds
      hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E rho eps tauA omega e
      hDeltaA1 hDataEpsNonneg hEOp hRadiusFactor hSourceRadius
      hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
      hxTranspose hsmall hAATInv_le hAOp)
    hDeltaA1Row hDeltaA2Row

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    common-radius row-wise handoff from entrywise row-relative perturbation
    bounds. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_entrywise_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Entry : ∀ i k, |DeltaA1 i k| ≤ eta * |A i k|)
    (hDeltaA2Entry : ∀ i k, |DeltaA2 i k| ≤ eta * |A i k|) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E rho eps tauA omega e eta
    hDeltaA1 hDataEpsNonneg hEOp hRadiusFactor hSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose hsmall
    hAATInv_le hAOp heta
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA1 heta hDeltaA1Entry i)
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA2 heta hDeltaA2Entry i)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    common-radius row-wise handoff specialized to the relative componentwise
    data majorant `E = |A|`. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_abs_data_source_operator_envelopes_exact_size_eps_common_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hAbsAOp : rectOpNorm2Le (fun i j => |A i j|) e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * |A i k|)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * |A i k|)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eps) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_entrywise_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv (fun i j => |A i j|)
    rho eps tauA omega e eps hDeltaA1 hDataEpsNonneg hAbsAOp
    hRadiusFactor hSourceRadius hGramLeftInv
    (fun i k => abs_nonneg (A i k))
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall hAATInv_le
    hAOp hDataEpsNonneg hDeltaA1Component hDeltaA2Component

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff.  The latest
    source-envelope version of Lemma 21.2 supplies the single perturbed
    minimum-norm system, and common row-wise source perturbation bounds then
    package it as the row-wise backward-error predicate used in Theorem 21.4. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
    A DeltaA1 DeltaA2 b x_hat heta
    (higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
      hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E eps tauA omega e
      hDeltaA1 hDataEpsNonneg hEOp hCombinedSourceRadius hGramLeftInv
      hDataE hDeltaA1Component hDeltaA2Component hxTranspose
      hCombinedSmall hAATInv_le hAOp)
    hDeltaA1Row hDeltaA2Row

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff from entrywise row-relative
    perturbation bounds.  This is a stronger sufficient condition for the
    row-wise hypotheses consumed by Theorem 21.4. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_entrywise_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Entry : ∀ i k, |DeltaA1 i k| ≤ eta * |A i k|)
    (hDeltaA2Entry : ∀ i k, |DeltaA2 i k| ≤ eta * |A i k|) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E eps tauA omega e eta
    hDeltaA1 hDataEpsNonneg hEOp hCombinedSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hCombinedSmall hAATInv_le hAOp heta
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA1 heta hDeltaA1Entry i)
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA2 heta hDeltaA2Entry i)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff specialized to the relative
    componentwise data majorant `E = |A|`.  The componentwise perturbation
    bounds then supply the row-wise hypotheses directly. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_abs_data_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hAbsAOp : rectOpNorm2Le (fun i j => |A i j|) e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * |A i k|)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * |A i k|)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eps) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_entrywise_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv (fun i j => |A i j|)
    eps tauA omega e eps hDeltaA1 hDataEpsNonneg hAbsAOp
    hCombinedSourceRadius hGramLeftInv
    (fun i k => abs_nonneg (A i k))
    hDeltaA1Component hDeltaA2Component hxTranspose hCombinedSmall
    hAATInv_le hAOp hDataEpsNonneg hDeltaA1Component hDeltaA2Component

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
    source-residual identity for any feasible perturbation in the
    underdetermined normwise backward-error model.  If `y` is an exact
    minimum-norm solution of `(A + DeltaA)y = b + Deltab`, then the source
    residual `b - A y` equals `DeltaA*y - Deltab`. -/
theorem UndetNormwiseBackwardErrorFeasible.source_residual_eq
    {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {y : Fin n → ℝ}
    {DeltaA : Fin m → Fin n → ℝ} {Deltab : Fin m → ℝ}
    (hfeas : UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    undetResidualHigham A b y =
      fun i => rectMatMulVec DeltaA y i - Deltab i := by
  ext i
  have hi := congrFun hfeas.system_eq i
  unfold undetResidualHigham rectMatMulVec at *
  simp_rw [add_mul] at hi
  rw [Finset.sum_add_distrib] at hi
  linarith

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    scalar residual lower-bound dependency for the nonzero Sun--Sun route.
    Any feasible perturbation pair has weighted cost at least the scalar
    `phi` branch formed from the source residual `b - A*y`.  The full
    nonzero formula still requires the singular-value term. -/
theorem UndetNormwiseBackwardErrorFeasible.phi_le_costF
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {y : Fin n → ℝ}
    {DeltaA : Fin m → Fin n → ℝ} {Deltab : Fin m → ℝ}
    (hy : y ≠ 0)
    (hfeas : UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    lsNormwiseBackwardErrorPhi theta (undetResidualHigham A b y) y ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
  lsNormwiseBackwardErrorPhi_le_costF_of_residual_eq_deltaA_y_sub_deltab
    htheta hy (undetResidualHigham A b y) DeltaA Deltab
    hfeas.source_residual_eq

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

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    in the degenerate `sigma = 0` specialization of the nonzero Sun--Sun
    scalar formula, the displayed right-hand side reduces to the residual
    scalar `phi` branch.  This does not assert the full singular-value
    equality with `eta_F(y)`. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_eq_phi_of_sigma_zero
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) {y : Fin n → ℝ}
    (hy : y ≠ 0) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y 0 =
      lsNormwiseBackwardErrorPhi theta (undetResidualHigham A b y) y := by
  apply (sq_eq_sq₀
    (undetNormwiseBackwardErrorNonzeroFormulaRHS_nonneg theta A b y 0)
    (lsNormwiseBackwardErrorPhi_nonneg theta (undetResidualHigham A b y) y)).mp
  rw [undetNormwiseBackwardErrorNonzeroFormulaRHS_sq]
  rw [lsNormwiseBackwardErrorPhi_eq_theta_mul_norm_div_sqrt_den htheta hy]
  have hy_sq_ne : vecNorm2Sq y ≠ 0 :=
    higham21_vecNorm2Sq_ne_zero_of_ne_zero hy
  have hden_pos : 0 < 1 + theta ^ 2 * vecNorm2Sq y :=
    lsNormwiseBackwardErrorMu_den_pos theta y
  rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hden_pos), vecNorm2_sq]
  field_simp [hy_sq_ne, ne_of_gt hden_pos]
  ring

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    lower-bound dependency for the `sigma = 0` specialization of the nonzero
    scalar formula.  Every feasible perturbation has cost at least this
    degenerate right-hand side, via the residual `phi` lower bound. -/
theorem UndetNormwiseBackwardErrorFeasible.nonzeroFormulaRHS_le_costF_of_sigma_zero
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {y : Fin n → ℝ}
    {DeltaA : Fin m → Fin n → ℝ} {Deltab : Fin m → ℝ}
    (hy : y ≠ 0)
    (hfeas : UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y 0 ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  rw [undetNormwiseBackwardErrorNonzeroFormulaRHS_eq_phi_of_sigma_zero
    htheta A b hy]
  exact hfeas.phi_le_costF htheta hy

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

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    lower-bound corollary for the `sigma = 0` specialization.  Combining the
    degenerate RHS-to-`phi` bridge with the feasible-cost lower bound shows
    that this scalar branch is below the `eta_F(y)` infimum whenever the
    attainable-cost set is nonempty.  The full singular-value lower route
    remains open. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_sigma_zero
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) {y : Fin n → ℝ}
    (hy : y ≠ 0)
    (hnonempty : (undetNormwiseBackwardErrorValuesF theta A b y).Nonempty) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y 0 ≤
      undetNormwiseBackwardErrorEtaF theta A b y :=
  undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_forall_feasible_cost_ge
    theta A b y 0 hnonempty
    (fun _DeltaA _Deltab hfeas =>
      hfeas.nonzeroFormulaRHS_le_costF_of_sigma_zero htheta hy)

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
  rcases hatt with ⟨DeltaA, Deltab, hfeas, hcost⟩
  have hnonempty : (undetNormwiseBackwardErrorValuesF theta A b y).Nonempty :=
    ⟨lsNormwiseBackwardErrorCostF theta DeltaA Deltab,
      DeltaA, Deltab, hfeas, rfl⟩
  exact le_antisymm
    (undetNormwiseBackwardErrorEtaF_le_nonzeroFormulaRHS_of_exists_feasible_cost_eq
      theta A b y sigma ⟨DeltaA, Deltab, hfeas, hcost⟩)
    (undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_forall_feasible_cost_ge
      theta A b y sigma hnonempty hlower)

/-- Inequality-form certificate for the open nonzero equality in Higham
    Chapter 21, Theorem 21.3.  A pointwise lower bound for every feasible
    perturbation and one feasible perturbation whose cost is no larger than the
    displayed nonzero RHS already force the infimum model to equal the RHS. -/
theorem undetNormwiseBackwardErrorEtaF_eq_nonzeroFormulaRHS_of_formula_upper_certificate
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (y : Fin n → ℝ) (sigma : ℝ)
    (hlower :
      ∀ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab →
          undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma ≤
            lsNormwiseBackwardErrorCostF theta DeltaA Deltab)
    (hupper :
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab ≤
            undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma) :
    undetNormwiseBackwardErrorEtaF theta A b y =
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  rcases hupper with ⟨DeltaA, Deltab, hfeas, hcost⟩
  have hnonempty : (undetNormwiseBackwardErrorValuesF theta A b y).Nonempty :=
    ⟨lsNormwiseBackwardErrorCostF theta DeltaA Deltab,
      DeltaA, Deltab, hfeas, rfl⟩
  exact le_antisymm
    (undetNormwiseBackwardErrorEtaF_le_nonzeroFormulaRHS_of_exists_feasible_cost_le
      theta A b y sigma ⟨DeltaA, Deltab, hfeas, hcost⟩)
    (undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_forall_feasible_cost_ge
      theta A b y sigma hnonempty hlower)

-- ============================================================
-- §21.3  Theorem 21.4: Q method backward stability
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    a columnwise Householder QR perturbation bound for `Aᵀ` is exactly a
    row-wise perturbation bound for the transposed perturbation of `A`. -/
theorem higham21_rectRowNorm2_eq_columnFrob_finiteTranspose {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    rectRowNorm2 A i = columnFrob (finiteTranspose A) i := by
  simp [rectRowNorm2, columnFrob_eq_vecNorm2, finiteTranspose]

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    transposing a Chapter 19 columnwise QR perturbation certificate turns its
    column bounds into the row-wise bounds used by the underdetermined-system
    backward-error definition. -/
theorem higham21_row_bounds_of_transposed_qr_column_bounds {m n : ℕ}
    (AT DeltaAT : Fin n → Fin m → ℝ) {eta : ℝ}
    (hcol : ∀ i : Fin m,
      columnFrob DeltaAT i ≤ eta * columnFrob AT i) :
    ∀ i : Fin m,
      rectRowNorm2 (finiteTranspose DeltaAT) i ≤
        eta * rectRowNorm2 (finiteTranspose AT) i := by
  intro i
  simpa [higham21_rectRowNorm2_eq_columnFrob_finiteTranspose] using hcol i

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    source-facing QR dependency for the Q method.  Applying Chapter 19,
    Theorem 19.4 to `Aᵀ` gives a perturbation `DeltaA0` of the original
    underdetermined matrix whose rows satisfy the printed row-wise QR bound.

    This is only the QR factorization perturbation used in the proof of
    Theorem 21.4; the triangular-solve and final `Q`-application perturbations
    remain separate obligations before the full Q-method theorem closes. -/
theorem higham21_theorem21_4_qr_transpose_row_perturbation_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ)
    (R_hat : Fin n → Fin m → ℝ)
    (eta : ℝ)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError n m
      (finiteTranspose A) Q R_hat eta) :
    ∃ DeltaA0 : Fin m → Fin n → ℝ,
      (∀ i j, A i j + DeltaA0 i j =
        matMulRect n n m Q R_hat j i) ∧
      (∀ i : Fin m,
        rectRowNorm2 DeltaA0 i ≤ eta * rectRowNorm2 A i) := by
  rcases hqr.result with ⟨DeltaAT, hrep, hcol⟩
  refine ⟨finiteTranspose DeltaAT, ?_, ?_⟩
  · intro i j
    simpa [finiteTranspose] using hrep j i
  · intro i
    have hrow :=
      higham21_row_bounds_of_transposed_qr_column_bounds
        (finiteTranspose A) DeltaAT hcol i
    simpa [finiteTranspose_finiteTranspose] using hrow

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    concrete Householder QR instantiation of the transposed row-perturbation
    dependency for `Aᵀ`.  The dimension hypotheses are the Chapter 19 tall-panel
    side conditions for the matrix `Aᵀ : ℝ^(n×m)`. -/
theorem higham21_theorem21_4_householder_qr_transpose_row_perturbation_bound
    {m n : ℕ} (fp : FPModel)
    (A : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hmn : m ≤ n)
    (hvalid :
      gammaValid fp (m * householderConstructApplyGammaIndex n)) :
    ∃ DeltaA0 : Fin m → Fin n → ℝ,
      (∀ i j, A i j + DeltaA0 i j =
        matMulRect n n m
          (fl_householderQRPanel_Q fp n m (finiteTranspose A))
          (fl_householderQRPanel_R fp n m (finiteTranspose A)) j i) ∧
      (∀ i : Fin m,
        rectRowNorm2 DeltaA0 i ≤
          H19.Theorem19_4.gamma_tilde fp n m * rectRowNorm2 A i) := by
  exact
    higham21_theorem21_4_qr_transpose_row_perturbation_bound A
      (fl_householderQRPanel_Q fp n m (finiteTranspose A))
      (fl_householderQRPanel_R fp n m (finiteTranspose A))
      (H19.Theorem19_4.gamma_tilde fp n m)
      (H19.Theorem19_4.householder_qr_backward_error
        fp n m (finiteTranspose A) hm hmn hvalid)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    triangular-solve dependency for the Q-method proof.  Applying the existing
    forward-substitution backward-error theorem to `R_hatᵀ` gives the printed
    perturbation form `(R_hat + DeltaR)ᵀ y_hat1 = b` with a componentwise
    `gamma_m` bound on `DeltaR`. -/
theorem higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
    (fp : FPModel) (m : ℕ)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      ∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i := by
  let L : Fin m → Fin m → ℝ := matTranspose R_hat
  have hLdiag : ∀ i : Fin m, L i i ≠ 0 := by
    intro i
    simpa [L, matTranspose] using hdiag i
  have hlower : ∀ i j : Fin m, i.val < j.val → L i j = 0 := by
    intro i j hij
    simpa [L, matTranspose] using hupper j i hij
  obtain ⟨DeltaL, hDeltaL, hsolve⟩ :=
    forwardSub_backward_error fp m L b hLdiag hlower hvalid
  let DeltaR : Fin m → Fin m → ℝ := matTranspose DeltaL
  refine ⟨DeltaR, ?_, ?_⟩
  · intro i j
    simpa [DeltaR, L, matTranspose] using hDeltaL j i
  · intro i
    simpa [DeltaR, L, matTranspose, matMulVec] using hsolve i

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    triangular perturbation nonsingularity for the rounded `R_hat^T` solve.
    If an upper-triangular factor has nonzero diagonal and the perturbation is
    entrywise relatively bounded by a factor below one, then the perturbed
    transpose factor remains nonsingular. -/
theorem higham21_theorem21_4_perturbed_transpose_factor_det_ne_zero_of_componentwise_bound
    {m : ℕ}
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    {eta : ℝ} (heta_lt : eta < 1)
    (hDelta : ∀ i j, |DeltaR i j| ≤ eta * |R_hat i j|) :
    Matrix.det
        (matTranspose (fun a b => R_hat a b + DeltaR a b) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  let Tpert : Fin m → Fin m → ℝ :=
    matTranspose (fun a b => R_hat a b + DeltaR a b)
  have hlowerPert : ∀ i j : Fin m, i.val < j.val → Tpert i j = 0 := by
    intro i j hij
    have hR : R_hat j i = 0 := hupper j i hij
    have hbound : |DeltaR j i| ≤ 0 := by
      simpa [hR] using hDelta j i
    have hDeltaZero : DeltaR j i = 0 := by
      exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg (DeltaR j i)))
    simp [Tpert, matTranspose, hR, hDeltaZero]
  have hdiagPert : ∀ i : Fin m, Tpert i i ≠ 0 := by
    intro i hzero
    have hsum : R_hat i i + DeltaR i i = 0 := by
      simpa [Tpert, matTranspose] using hzero
    have hDelta_eq : DeltaR i i = -R_hat i i := by
      linarith
    have habs_eq : |DeltaR i i| = |R_hat i i| := by
      rw [hDelta_eq, abs_neg]
    have hle : |R_hat i i| ≤ eta * |R_hat i i| := by
      simpa [habs_eq] using hDelta i i
    have hpos : 0 < |R_hat i i| := abs_pos.mpr (hdiag i)
    nlinarith
  have hdet :
      Matrix.det (Tpert : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    det_ne_zero_of_lower_triangular_diag_ne_zero m
      Tpert
      hlowerPert hdiagPert
  simpa [Tpert] using hdet

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    triangular-solve handoff into the exact Q-method minimum-norm theorem.
    The rounded solve of `R_hat^T y = b` supplies a perturbation `DeltaR`;
    if the perturbed transpose factor is nonsingular, then the formed
    Q-method vector is the exact minimum-norm solution for the corresponding
    perturbed QR-coordinate system.

    This is not the full row-wise backward-stability theorem: it isolates the
    remaining nonsingularity and row-wise perturbation obligations from the
    already proved triangular-solve backward-error certificate. -/
theorem higham21_theorem21_4_forwardSub_q_method_min_norm_handoff
    {m k : ℕ} (fp : FPModel)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      (Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 →
        RectMinNormSolution m (m + k)
          (finiteTranspose
            (matMulRectLeft Q
              (lsQRTallBlock (k := k) (fun a b => R_hat a b + DeltaR a b))))
          b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m (matTranspose R_hat) b)
              (0 : Fin k → ℝ)))) := by
  obtain ⟨DeltaR, hDeltaR, hsolve⟩ :=
    higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
      fp m R_hat b hdiag hupper hvalid
  refine ⟨DeltaR, hDeltaR, hsolve, ?_⟩
  intro hdetT
  let Rpert : Fin m → Fin m → ℝ := fun a b => R_hat a b + DeltaR a b
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  have hy1 : (fun j : Fin m => ∑ i : Fin m, Rpert i j * y1 i) = b := by
    ext j
    simpa [Rpert, y1, matMulVec, matTranspose] using hsolve j
  exact
    higham21_eq21_3_q_method_min_norm_of_qr_det_ne_zero
      Q hQ Rpert b y1 hdetT hy1

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-free triangular-solve handoff for the Q-method minimum-norm
    theorem.  The stronger guard `gammaValid fp (2*m)` makes `gamma_m < 1`,
    so the componentwise triangular perturbation preserves nonsingularity of
    the perturbed transpose factor. -/
theorem higham21_theorem21_4_forwardSub_q_method_min_norm_handoff_of_gammaValid2
    {m k : ℕ} (fp : FPModel)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      RectMinNormSolution m (m + k)
        (finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k) (fun a b => R_hat a b + DeltaR a b))))
        b
        (matMulVec (m + k) Q
          (Fin.append
            (fl_forwardSub fp m (matTranspose R_hat) b)
            (0 : Fin k → ℝ))) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hminCond⟩ :=
    higham21_theorem21_4_forwardSub_q_method_min_norm_handoff
      fp Q hQ R_hat b hdiag hupper hvalid
  have hdet :
      Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_theorem21_4_perturbed_transpose_factor_det_ne_zero_of_componentwise_bound
      R_hat DeltaR hdiag hupper (gamma_lt_one fp m hvalid2) hDeltaR
  exact ⟨DeltaR, hDeltaR, hsolve, hminCond hdet⟩

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    row-wise backward-error handoff after the triangular solve.  The theorem
    combines the forward-substitution perturbation certificate with the
    existing Lemma 21.2 row-wise witness surface.  The remaining source work is
    exactly the Q-method row-wise assembly: identify the single Lemma 21.2
    perturbation with the perturbed QR-coordinate system and prove the two
    source row bounds. -/
theorem higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (DeltaA1 DeltaA2 : Fin m → Fin (m + k) → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      (Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 →
        (fun i j =>
            A i j +
              undetLemma21_2SinglePerturbation
                (matMulVec (m + k) Q
                  (Fin.append
                    (fl_forwardSub fp m (matTranspose R_hat) b)
                    (0 : Fin k → ℝ)))
                DeltaA1 DeltaA2 i j) =
          finiteTranspose
            (matMulRectLeft Q
              (lsQRTallBlock (k := k)
                (fun a b => R_hat a b + DeltaR a b))) →
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m (matTranspose R_hat) b)
              (0 : Fin k → ℝ)))
          (Real.sqrt 2 * eta)) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hminCond⟩ :=
    higham21_theorem21_4_forwardSub_q_method_min_norm_handoff
      fp Q hQ R_hat b hdiag hupper hvalid
  refine ⟨DeltaR, hDeltaR, hsolve, ?_⟩
  intro hdet hsingle
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q
      (Fin.append
        (fl_forwardSub fp m (matTranspose R_hat) b)
        (0 : Fin k → ℝ))
  let A_qr : Fin m → Fin (m + k) → ℝ :=
    finiteTranspose
      (matMulRectLeft Q
        (lsQRTallBlock (k := k)
          (fun a b => R_hat a b + DeltaR a b)))
  have hminQR : RectMinNormSolution m (m + k) A_qr b x_hat := by
    simpa [A_qr, x_hat] using hminCond hdet
  have hsingle' :
      (fun i j =>
          A i j + undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2 i j)
        = A_qr := by
    simpa [A_qr, x_hat] using hsingle
  have hminSingle :
      RectMinNormSolution m (m + k)
        (fun i j =>
          A i j + undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2 i j)
        b x_hat := by
    rw [hsingle']
    exact hminQR
  simpa [x_hat] using
    higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
      A DeltaA1 DeltaA2 b x_hat heta hminSingle
      hDeltaA1Row hDeltaA2Row

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-free row-wise backward-error handoff after the triangular
    solve.  Compared with
    `higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff`, the
    stronger `gammaValid fp (2*m)` guard discharges the perturbed transpose
    factor nonsingularity side condition. -/
theorem higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff_of_gammaValid2
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m))
    (DeltaA1 DeltaA2 : Fin m → Fin (m + k) → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      ((fun i j =>
          A i j +
            undetLemma21_2SinglePerturbation
              (matMulVec (m + k) Q
                (Fin.append
                  (fl_forwardSub fp m (matTranspose R_hat) b)
                  (0 : Fin k → ℝ)))
              DeltaA1 DeltaA2 i j) =
        finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k)
              (fun a b => R_hat a b + DeltaR a b))) →
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m (matTranspose R_hat) b)
              (0 : Fin k → ℝ)))
          (Real.sqrt 2 * eta)) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hrowCond⟩ :=
    higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff
      fp A Q hQ R_hat b hdiag hupper hvalid DeltaA1 DeltaA2
      heta hDeltaA1Row hDeltaA2Row
  have hdet :
      Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_theorem21_4_perturbed_transpose_factor_det_ne_zero_of_componentwise_bound
      R_hat DeltaR hdiag hupper (gamma_lt_one fp m hvalid2) hDeltaR
  exact ⟨DeltaR, hDeltaR, hsolve, fun hsingle => hrowCond hdet hsingle⟩

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    algebraic difference form of the computed final `Q` action.  If
    `x_hat = (Q + DeltaQ)[y1;0]`, then its difference from the exact
    `Q[y1;0]` action is precisely `DeltaQ [y1;0]`. -/
theorem higham21_eq21_10_q_action_difference_eq_deltaQ
    {m k : ℕ}
    (Q DeltaQ : Fin (m + k) → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hx :
      x_hat =
        matMulVec (m + k) (fun i j => Q i j + DeltaQ i j)
          (Fin.append y1 (0 : Fin k → ℝ))) :
    (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) i) =
      matMulVec (m + k) DeltaQ (Fin.append y1 (0 : Fin k → ℝ)) := by
  ext i
  rw [hx]
  unfold matMulVec
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    the Frobenius perturbation bound for the computed final `Q` action implies
    a Euclidean vector-error bound for the formed solution. -/
theorem higham21_eq21_10_q_action_vec_error_bound
    {m k : ℕ}
    (Q DeltaQ : Fin (m + k) → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (eta : ℝ)
    (hx :
      x_hat =
        matMulVec (m + k) (fun i j => Q i j + DeltaQ i j)
          (Fin.append y1 (0 : Fin k → ℝ)))
    (hDeltaQ : frobNorm DeltaQ ≤ eta) :
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      eta * vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) := by
  let z : Fin (m + k) → ℝ := Fin.append y1 (0 : Fin k → ℝ)
  have hdiff :
      (fun i : Fin (m + k) =>
        x_hat i - matMulVec (m + k) Q z i) =
        matMulVec (m + k) DeltaQ z := by
    simpa [z] using
      higham21_eq21_10_q_action_difference_eq_deltaQ
        Q DeltaQ y1 x_hat hx
  calc
    vecNorm2 (fun i : Fin (m + k) =>
        x_hat i -
          matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) i)
        = vecNorm2 (matMulVec (m + k) DeltaQ z) := by
            simpa [z] using congrArg vecNorm2 hdiff
    _ ≤ frobNorm DeltaQ * vecNorm2 z :=
        vecNorm2_matMulVec_le_frobNorm_mul DeltaQ z
    _ ≤ eta * vecNorm2 z :=
        mul_le_mul_of_nonneg_right hDeltaQ (vecNorm2_nonneg z)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    source-shaped final `Q` action bound with the zero-padded coordinate vector
    reduced to the active block norm `‖y1‖₂`. -/
theorem higham21_eq21_10_q_action_vec_error_bound_left_block
    {m k : ℕ}
    (Q DeltaQ : Fin (m + k) → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (eta : ℝ)
    (hx :
      x_hat =
        matMulVec (m + k) (fun i j => Q i j + DeltaQ i j)
          (Fin.append y1 (0 : Fin k → ℝ)))
    (hDeltaQ : frobNorm DeltaQ ≤ eta) :
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      eta * vecNorm2 y1 := by
  have hbase :=
    higham21_eq21_10_q_action_vec_error_bound
      Q DeltaQ y1 x_hat eta hx hDeltaQ
  have hzero :
      vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) = vecNorm2 y1 := by
    unfold vecNorm2
    rw [lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  rwa [hzero] at hbase

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    consume the QR accumulated-`Q` perturbation certificate directly.  If the
    computed final action uses a rounded `Q_hat` that is certified as
    `Q + DeltaQ` with Frobenius radius `eta`, then the formed-solution error is
    bounded by `eta * ‖y1‖₂`. -/
theorem higham21_eq21_10_q_action_vec_error_bound_of_fixed_q_accum_error
    {m k : ℕ}
    (Q Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (eta : ℝ)
    (hQerr :
      HouseholderQRPanelQhatFixedAccumError (m + k) Q Q_hat eta)
    (hx :
      x_hat =
        matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))) :
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      eta * vecNorm2 y1 := by
  rcases hQerr.result with ⟨DeltaQ, hQhat_rep, hDeltaQ⟩
  have hQhat :
      Q_hat = fun i j => Q i j + DeltaQ i j := by
    ext i j
    exact hQhat_rep i j
  have hx' :
      x_hat =
        matMulVec (m + k) (fun i j => Q i j + DeltaQ i j)
          (Fin.append y1 (0 : Fin k → ℝ)) := by
    simpa [hQhat] using hx
  exact
    higham21_eq21_10_q_action_vec_error_bound_left_block
      Q DeltaQ y1 x_hat eta hx' hDeltaQ

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    concrete Householder QR panel specialization of the final `Q` action
    perturbation bridge.  Applied to the QR factorization of `Aᵀ`, the rounded
    accumulated panel `Q_hat` gives the source-shaped `‖y1‖₂` error bound with
    the existing Householder QR growth radius. -/
theorem higham21_eq21_10_q_action_vec_error_bound_of_householder_qr_panel_qhat
    {m k : ℕ}
    (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hvalid : gammaValid fp (11 * (m + k) + 23))
    (hx :
      x_hat =
        matMulVec (m + k)
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ))) :
    let eta : ℝ :=
      (((m + k : ℕ) : ℝ) * householderConstructApplyBound fp (m + k) *
        (1 + householderConstructApplyBound fp (m + k)) ^ (m + k) *
        Real.sqrt (((m + k : ℕ) : ℝ)))
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k)
          (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      eta * vecNorm2 y1 := by
  let eta : ℝ :=
    (((m + k : ℕ) : ℝ) * householderConstructApplyBound fp (m + k) *
      (1 + householderConstructApplyBound fp (m + k)) ^ (m + k) *
      Real.sqrt (((m + k : ℕ) : ℝ)))
  have hQerr :
      HouseholderQRPanelQhatFixedAccumError (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
        eta := by
    simpa [eta] using
      fl_householderQRPanel_Qhat_fixed_Q_growth_accum_error
        fp (m + k) m (m + k) (finiteTranspose A) (le_refl (m + k)) hvalid
  exact
    higham21_eq21_10_q_action_vec_error_bound_of_fixed_q_accum_error
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      y1 x_hat eta hQerr hx

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
