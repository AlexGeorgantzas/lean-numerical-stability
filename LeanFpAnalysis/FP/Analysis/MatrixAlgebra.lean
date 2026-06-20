-- Analysis/MatrixAlgebra.lean
--
-- Matrix algebra infrastructure: matrix multiplication, matrix power,
-- Neumann series, and constructive (I − M)⁻¹ for nonneg M with ‖M‖∞ < 1.
--
-- This provides the matrix inverse theory needed for iterative refinement
-- (Higham §11) and forward error analysis (§8.2).
--
-- This file is exact algebra, not floating-point algorithm code.
--
-- Exact algebra and norms use Mathlib as the source of truth.  When an object
-- already has a Mathlib-native type such as `Matrix (Fin m) (Fin n) ℝ`, use
-- Mathlib notation directly.  When existing algorithm code uses the legacy
-- function-shaped representation `Fin m → Fin n → ℝ`, use the compatibility
-- wrappers in this file (`frobNorm`, `infNorm`, etc.).  These wrappers should
-- be read as bridges to Mathlib, not as independent mathematical definitions.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace LeanFpAnalysis.FP

open scoped BigOperators NNReal Matrix.Norms.Frobenius

-- ============================================================
-- Public exact vector/matrix shape aliases
-- ============================================================

/-- Real vector indexed by `Fin n`. -/
abbrev RVec (n : ℕ) := Fin n → ℝ

/-- Rectangular real matrix using Mathlib's matrix type.  New exact
    matrix-facing APIs should prefer this shape when possible, especially for
    rectangular algorithms such as QR and least squares. -/
abbrev RMat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- Square real matrix using Mathlib's matrix type. -/
abbrev RSqMat (n : ℕ) := RMat n n

/-- Legacy function-shaped rectangular real matrix.  Existing algorithm code
    still uses this representation heavily; it is definitionally the same data
    as `RMat m n`, but Lean's norm instances are not the same unless we coerce
    through `Matrix.of`.  New code should use this shape only when it needs to
    interoperate with existing `fl_*` algorithms or square matrix infrastructure. -/
abbrev RMatFn (m n : ℕ) := Fin m → Fin n → ℝ

-- ============================================================
-- Matrix multiplication (exact, non-FP)
-- ============================================================

/-- **Matrix-matrix product**: (AB)_{ij} = ∑_k A_{ik} B_{kj}. -/
noncomputable def matMul (n : ℕ) (A B : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- **Identity matrix** on Fin n. -/
noncomputable def idMatrix (n : ℕ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then 1 else 0

-- ============================================================
-- Basic matMul properties
-- ============================================================

/-- Right multiplication by identity: A · I = A. -/
theorem matMul_id_right (n : ℕ) (A : Fin n → Fin n → ℝ) :
    matMul n A (idMatrix n) = A := by
  ext i j; unfold matMul idMatrix
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Left multiplication by identity: I · A = A. -/
theorem matMul_id_left (n : ℕ) (A : Fin n → Fin n → ℝ) :
    matMul n (idMatrix n) A = A := by
  ext i j; unfold matMul idMatrix
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- Matrix multiplication is associative. -/
theorem matMul_assoc (n : ℕ) (A B C : Fin n → Fin n → ℝ) :
    matMul n (matMul n A B) C = matMul n A (matMul n B C) := by
  ext i j; unfold matMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _; ring

/-- Left distributivity: (A + B)·C = A·C + B·C (pointwise). -/
theorem matMul_add_left (n : ℕ) (A B C : Fin n → Fin n → ℝ) :
    matMul n (fun a b => A a b + B a b) C =
    fun i j => matMul n A C i j + matMul n B C i j := by
  ext i j; unfold matMul; rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _; ring

/-- Right distributivity: A·(B + C) = A·B + A·C (pointwise). -/
theorem matMul_add_right (n : ℕ) (A B C : Fin n → Fin n → ℝ) :
    matMul n A (fun a b => B a b + C a b) =
    fun i j => matMul n A B i j + matMul n A C i j := by
  ext i j; unfold matMul; rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _; ring

/-- Matrix-vector product via matMul: (Av)_i = ∑_j A_{ij} v_j.
    This connects matMul to the existing matMulVec. -/
theorem matMul_vec_eq (n : ℕ) (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    (fun i => ∑ j : Fin n, A i j * v j) =
    (fun i => ∑ j : Fin n, matMul n A (fun k l => if k = l then v l else 0) i j) := by
  ext i; unfold matMul
  apply Finset.sum_congr rfl; intro j _
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Identity matrix times a vector is the vector (using idMatrix). -/
lemma idMatrix_mulVec (n : ℕ) (v : Fin n → ℝ) :
    (fun i => ∑ j : Fin n, idMatrix n i j * v j) = v := by
  ext i; unfold idMatrix; simp [Finset.mem_univ]

-- ============================================================
-- Matrix-vector operations and componentwise absolute values
-- ============================================================

/-- Matrix-vector product: (Av)_i = ∑_j A_ij v_j. -/
noncomputable def matMulVec (n : ℕ) (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j : Fin n, A i j * v j

/-- Componentwise absolute value of a vector. -/
noncomputable def absVec (n : ℕ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |v i|

/-- Componentwise absolute value of a matrix. -/
noncomputable def absMatrix (n : ℕ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => |A i j|

/-- Componentwise absolute value of a rectangular matrix. -/
noncomputable def absMatrixRect {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => |A i j|

/-- ∑ |f k * g k| = ∑ |f k| * |g k|.
    Eliminates the common `apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _` pattern. -/
lemma Finset.sum_abs_mul {n : ℕ} (f g : Fin n → ℝ) :
    ∑ k : Fin n, |f k * g k| = ∑ k : Fin n, |f k| * |g k| :=
  Finset.sum_congr rfl (fun k _ => abs_mul (f k) (g k))

-- ============================================================
-- Matrix inverse predicates
-- ============================================================

/-- T_inv is a left inverse of T: T_inv * T = I. -/
def IsLeftInverse (n : ℕ) (T T_inv : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, ∑ k : Fin n, T_inv i k * T k j = if i = j then 1 else 0

/-- T_inv is a right inverse of T: T * T_inv = I. -/
def IsRightInverse (n : ℕ) (T T_inv : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, ∑ k : Fin n, T i k * T_inv k j = if i = j then 1 else 0

/-- Full inverse: both left and right inverse. -/
def IsInverse (n : ℕ) (T T_inv : Fin n → Fin n → ℝ) : Prop :=
  IsLeftInverse n T T_inv ∧ IsRightInverse n T T_inv

/-- The Mathlib nonsingular inverse, exposed in the repository's legacy
    function-shaped matrix representation. -/
noncomputable def nonsingInv (n : ℕ) (T : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  letI : Inv (Matrix (Fin n) (Fin n) ℝ) := Matrix.inv
  fun i j =>
    (Inv.inv (α := Matrix (Fin n) (Fin n) ℝ)
      (T : Matrix (Fin n) (Fin n) ℝ)) i j

/-- A matrix with unit determinant has a left inverse in the repository's
    `IsLeftInverse` predicate. -/
theorem isLeftInverse_nonsingInv_of_det_isUnit (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hdet : IsUnit (Matrix.det (T : Matrix (Fin n) (Fin n) ℝ))) :
    IsLeftInverse n T (nonsingInv n T) := by
  intro i j
  have h :=
    congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
      (Matrix.nonsing_inv_mul (T : Matrix (Fin n) (Fin n) ℝ) hdet)
  letI : Inv (Matrix (Fin n) (Fin n) ℝ) := Matrix.inv
  change
    (∑ x : Fin n,
      (Inv.inv (α := Matrix (Fin n) (Fin n) ℝ)
        (T : Matrix (Fin n) (Fin n) ℝ)) i x * T x j) =
      (if i = j then 1 else 0)
  simpa [Matrix.mul_apply] using h

/-- A matrix with unit determinant has a right inverse in the repository's
    `IsRightInverse` predicate. -/
theorem isRightInverse_nonsingInv_of_det_isUnit (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hdet : IsUnit (Matrix.det (T : Matrix (Fin n) (Fin n) ℝ))) :
    IsRightInverse n T (nonsingInv n T) := by
  intro i j
  have h :=
    congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
      (Matrix.mul_nonsing_inv (T : Matrix (Fin n) (Fin n) ℝ) hdet)
  letI : Inv (Matrix (Fin n) (Fin n) ℝ) := Matrix.inv
  change
    (∑ x : Fin n,
      T i x *
        (Inv.inv (α := Matrix (Fin n) (Fin n) ℝ)
          (T : Matrix (Fin n) (Fin n) ℝ)) x j) =
      (if i = j then 1 else 0)
  simpa [Matrix.mul_apply] using h

/-- A matrix with unit determinant has a two-sided inverse in the repository's
    `IsInverse` predicate. -/
theorem isInverse_nonsingInv_of_det_isUnit (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hdet : IsUnit (Matrix.det (T : Matrix (Fin n) (Fin n) ℝ))) :
    IsInverse n T (nonsingInv n T) :=
  ⟨isLeftInverse_nonsingInv_of_det_isUnit n T hdet,
    isRightInverse_nonsingInv_of_det_isUnit n T hdet⟩

/-- A matrix with unit determinant has a local left-inverse witness. -/
theorem exists_isLeftInverse_of_det_isUnit (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hdet : IsUnit (Matrix.det (T : Matrix (Fin n) (Fin n) ℝ))) :
    ∃ T_inv : Fin n → Fin n → ℝ, IsLeftInverse n T T_inv :=
  ⟨nonsingInv n T, isLeftInverse_nonsingInv_of_det_isUnit n T hdet⟩

/-- Over `ℝ`, a nonzero determinant supplies a local left-inverse witness. -/
theorem exists_isLeftInverse_of_det_ne_zero (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ T_inv : Fin n → Fin n → ℝ, IsLeftInverse n T T_inv :=
  exists_isLeftInverse_of_det_isUnit n T (isUnit_iff_ne_zero.mpr hdet)

/-- A matrix with unit determinant has a local two-sided inverse witness. -/
theorem exists_isInverse_of_det_isUnit (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hdet : IsUnit (Matrix.det (T : Matrix (Fin n) (Fin n) ℝ))) :
    ∃ T_inv : Fin n → Fin n → ℝ, IsInverse n T T_inv :=
  ⟨nonsingInv n T, isInverse_nonsingInv_of_det_isUnit n T hdet⟩

/-- Over `ℝ`, a nonzero determinant supplies a local two-sided inverse
    witness. -/
theorem exists_isInverse_of_det_ne_zero (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ T_inv : Fin n → Fin n → ℝ, IsInverse n T T_inv :=
  exists_isInverse_of_det_isUnit n T (isUnit_iff_ne_zero.mpr hdet)

/-- Over `ℝ`, the repository nonsingular inverse is a two-sided inverse when
    the determinant is nonzero. -/
theorem isInverse_nonsingInv_of_det_ne_zero (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    IsInverse n T (nonsingInv n T) :=
  isInverse_nonsingInv_of_det_isUnit n T (isUnit_iff_ne_zero.mpr hdet)

/-- A finite upper-triangular real matrix with nonzero diagonal has nonzero
    determinant.  The triangular shape uses the repository convention
    `j.val < i.val -> T i j = 0`. -/
theorem det_ne_zero_of_upper_triangular_diag_ne_zero (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hupper : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hdiag : ∀ i : Fin n, T i i ≠ 0) :
    Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  classical
  have htri :
      Matrix.BlockTriangular
        (M := (T : Matrix (Fin n) (Fin n) ℝ)) id := by
    intro i j hij
    exact hupper i j (by simpa using hij)
  rw [Matrix.det_of_upperTriangular htri]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)

/-- A finite upper-triangular real matrix with nonzero determinant has nonzero
    diagonal entries.  The triangular shape uses the repository convention
    `j.val < i.val -> T i j = 0`. -/
theorem diag_ne_zero_of_upper_triangular_det_ne_zero (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hupper : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hdet : Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∀ i : Fin n, T i i ≠ 0 := by
  classical
  have htri :
      Matrix.BlockTriangular
        (M := (T : Matrix (Fin n) (Fin n) ℝ)) id := by
    intro i j hij
    exact hupper i j (by simpa using hij)
  rw [Matrix.det_of_upperTriangular htri] at hdet
  exact fun i => Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

/-- A finite lower-triangular real matrix with nonzero diagonal has nonzero
    determinant.  This is the transpose form of
    `det_ne_zero_of_upper_triangular_diag_ne_zero`. -/
theorem det_ne_zero_of_lower_triangular_diag_ne_zero (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hlower : ∀ i j : Fin n, i.val < j.val → T i j = 0)
    (hdiag : ∀ i : Fin n, T i i ≠ 0) :
    Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  classical
  rw [← Matrix.det_transpose]
  apply det_ne_zero_of_upper_triangular_diag_ne_zero n
    (fun i j : Fin n => T j i)
  · intro i j hji
    exact hlower j i (by simpa using hji)
  · intro i
    exact hdiag i

-- ============================================================
-- Matrix subtraction: I − M
-- ============================================================

/-- **(I − M)** defined componentwise. -/
noncomputable def matSub_id (n : ℕ) (M : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => idMatrix n i j - M i j

-- ============================================================
-- Matrix power M^k
-- ============================================================

/-- **Matrix power** M^k by recursion. -/
noncomputable def matPow (n : ℕ) (M : Fin n → Fin n → ℝ) : ℕ → (Fin n → Fin n → ℝ)
  | 0 => idMatrix n
  | k + 1 => matMul n M (matPow n M k)

/-- M^0 = I. -/
theorem matPow_zero (n : ℕ) (M : Fin n → Fin n → ℝ) :
    matPow n M 0 = idMatrix n := rfl

/-- M^(k+1) = M · M^k. -/
theorem matPow_succ (n : ℕ) (M : Fin n → Fin n → ℝ) (k : ℕ) :
    matPow n M (k + 1) = matMul n M (matPow n M k) := rfl

/-- M^1 = M. -/
theorem matPow_one (n : ℕ) (M : Fin n → Fin n → ℝ) :
    matPow n M 1 = M := by
  simp [matPow, matMul_id_right]

/-- M^(k+1) = M^k · M (right multiplication form). -/
theorem matPow_succ_right (n : ℕ) (M : Fin n → Fin n → ℝ) (k : ℕ) :
    matPow n M (k + 1) = matMul n (matPow n M k) M := by
  induction k with
  | zero => simp [matPow, matMul_id_left, matMul_id_right]
  | succ k ih =>
    -- M^{k+2} = M · M^{k+1} = M · (M^k · M) = (M · M^k) · M = M^{k+1} · M
    conv_lhs => rw [matPow_succ, ih, ← matMul_assoc, ← matPow_succ]

-- ============================================================
-- Finite products of varying square matrices
-- ============================================================

/-- Product of a finite sequence of square matrices, ordered left to right.

`matSeqProd n m X` represents `X 0 * X 1 * ... * X (m-1)`, with the
empty product equal to the identity. -/
noncomputable def matSeqProd (n : ℕ) : (m : ℕ) →
    (Fin m → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | 0, _ => idMatrix n
  | m + 1, X => matMul n (X 0) (matSeqProd n m (fun j => X j.succ))

/-- Product of a finite sequence of scalars, ordered to match `matSeqProd`. -/
noncomputable def scalarSeqProd : (m : ℕ) → (Fin m → ℝ) → ℝ
  | 0, _ => 1
  | m + 1, a => a 0 * scalarSeqProd m (fun j => a j.succ)

/-- Nonnegative scalar factors have a nonnegative sequence product. -/
theorem scalarSeqProd_nonneg (m : ℕ) (a : Fin m → ℝ)
    (ha : ∀ j, 0 ≤ a j) :
    0 ≤ scalarSeqProd m a := by
  induction m with
  | zero =>
      simp [scalarSeqProd]
  | succ m ih =>
      simp [scalarSeqProd]
      exact mul_nonneg (ha 0) (ih (fun j => a j.succ) (fun j => ha j.succ))

/-- If every scalar factor is at least one, so is its sequence product. -/
theorem one_le_scalarSeqProd (m : ℕ) (a : Fin m → ℝ)
    (ha : ∀ j, 1 ≤ a j) :
    1 ≤ scalarSeqProd m a := by
  induction m with
  | zero =>
      simp [scalarSeqProd]
  | succ m ih =>
      have ha0_nonneg : 0 ≤ a 0 := le_trans zero_le_one (ha 0)
      have htail_one :
          1 ≤ scalarSeqProd m (fun j => a j.succ) :=
        ih (fun j => a j.succ) (fun j => ha j.succ)
      have htail_nonneg : 0 ≤ scalarSeqProd m (fun j => a j.succ) :=
        le_trans zero_le_one htail_one
      calc
        1 = 1 * 1 := by ring
        _ ≤ a 0 * scalarSeqProd m (fun j => a j.succ) :=
            mul_le_mul (ha 0) htail_one zero_le_one ha0_nonneg
        _ = scalarSeqProd (m + 1) a := by simp [scalarSeqProd]

/-- A sequence product of entrywise nonnegative matrices is entrywise
nonnegative. -/
theorem matSeqProd_nonneg (n m : ℕ) (A : Fin m → Fin n → Fin n → ℝ)
    (hA : ∀ r i j, 0 ≤ A r i j) :
    ∀ i j, 0 ≤ matSeqProd n m A i j := by
  induction m with
  | zero =>
      intro i j
      unfold matSeqProd idMatrix
      split <;> norm_num
  | succ m ih =>
      intro i j
      change 0 ≤ matMul n (A 0) (matSeqProd n m (fun r => A r.succ)) i j
      unfold matMul
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (hA 0 i k)
          (ih (fun r => A r.succ) (fun r => hA r.succ) k j))

/-- Componentwise domination of a perturbed finite matrix product by the
corresponding product of absolute-value matrices.

This is the absolute-value half of Higham Lemma 3.8: if
`|ΔX_j| <= δ_j |X_j|` with `δ_j >= 0`, then the product of the perturbed
factors is componentwise bounded by
`prod_j (1 + δ_j) * prod_j |X_j|`. -/
theorem matSeqProd_abs_perturbed_le_scalar_abs (n m : ℕ)
    (X ΔX : Fin m → Fin n → Fin n → ℝ) (δ : Fin m → ℝ)
    (hδ : ∀ r, 0 ≤ δ r)
    (hΔ : ∀ r i j, |ΔX r i j| ≤ δ r * |X r i j|) :
    ∀ i j,
      |matSeqProd n m (fun r i j => X r i j + ΔX r i j) i j| ≤
        scalarSeqProd m (fun r => 1 + δ r) *
          matSeqProd n m (fun r => absMatrix n (X r)) i j := by
  induction m with
  | zero =>
      intro i j
      unfold matSeqProd scalarSeqProd idMatrix
      split <;> norm_num
  | succ m ih =>
      intro i j
      let tailPert : Fin m → Fin n → Fin n → ℝ :=
        fun r i j => X r.succ i j + ΔX r.succ i j
      let tailAbs : Fin m → Fin n → Fin n → ℝ :=
        fun r => absMatrix n (X r.succ)
      let tailScale : ℝ := scalarSeqProd m (fun r => 1 + δ r.succ)
      have htail :
          ∀ k j,
            |matSeqProd n m tailPert k j| ≤
              tailScale * matSeqProd n m tailAbs k j := by
        intro k j
        simpa [tailPert, tailAbs, tailScale] using
          ih (fun r => X r.succ) (fun r => ΔX r.succ) (fun r => δ r.succ)
            (fun r => hδ r.succ) (fun r => hΔ r.succ) k j
      have htail_nonneg :
          ∀ k j, 0 ≤ matSeqProd n m tailAbs k j :=
        matSeqProd_nonneg n m tailAbs (by
          intro r a b
          simp [tailAbs, absMatrix])
      have hscale_nonneg : 0 ≤ tailScale := by
        exact scalarSeqProd_nonneg m (fun r => 1 + δ r.succ)
          (fun r => by linarith [hδ r.succ])
      have hhead_abs :
          ∀ k, |X 0 i k + ΔX 0 i k| ≤ (1 + δ 0) * |X 0 i k| := by
        intro k
        calc
          |X 0 i k + ΔX 0 i k| ≤ |X 0 i k| + |ΔX 0 i k| :=
              abs_add_le (X 0 i k) (ΔX 0 i k)
          _ ≤ |X 0 i k| + δ 0 * |X 0 i k| := by
              linarith [hΔ 0 i k]
          _ = (1 + δ 0) * |X 0 i k| := by ring
      unfold matSeqProd matMul
      calc
        |∑ k : Fin n,
            (X 0 i k + ΔX 0 i k) * matSeqProd n m tailPert k j|
            ≤ ∑ k : Fin n,
                |(X 0 i k + ΔX 0 i k) * matSeqProd n m tailPert k j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n,
                |X 0 i k + ΔX 0 i k| * |matSeqProd n m tailPert k j| := by
              apply Finset.sum_congr rfl
              intro k _
              exact abs_mul (X 0 i k + ΔX 0 i k) (matSeqProd n m tailPert k j)
        _ ≤ ∑ k : Fin n,
                ((1 + δ 0) * |X 0 i k|) *
                  (tailScale * matSeqProd n m tailAbs k j) := by
              apply Finset.sum_le_sum
              intro k _
              calc
                |X 0 i k + ΔX 0 i k| * |matSeqProd n m tailPert k j|
                    ≤ ((1 + δ 0) * |X 0 i k|) *
                        |matSeqProd n m tailPert k j| := by
                      exact mul_le_mul_of_nonneg_right (hhead_abs k) (abs_nonneg _)
                _ ≤ ((1 + δ 0) * |X 0 i k|) *
                        (tailScale * matSeqProd n m tailAbs k j) := by
                      exact mul_le_mul_of_nonneg_left (htail k j)
                        (mul_nonneg (by linarith [hδ 0]) (abs_nonneg _))
        _ =
              (1 + δ 0) * tailScale *
                (∑ k : Fin n, absMatrix n (X 0) i k *
                  matSeqProd n m tailAbs k j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              simp [tailAbs, absMatrix]
              ring
        _ =
              scalarSeqProd (m + 1) (fun r => 1 + δ r) *
                matMul n (absMatrix n (X 0)) (matSeqProd n m tailAbs) i j := by
              change
                (1 + δ 0) * tailScale *
                    (∑ k : Fin n, absMatrix n (X 0) i k *
                      matSeqProd n m tailAbs k j) =
                  ((1 + δ 0) * tailScale) *
                    (∑ k : Fin n, absMatrix n (X 0) i k *
                      matSeqProd n m tailAbs k j)
              ring

/-- Higham Chapter 3, Lemma 3.8, finite-sequence componentwise form.

If each factor in a matrix product is perturbed componentwise as
`|ΔX_j| <= δ_j |X_j|` with `δ_j >= 0`, then the whole product satisfies

`|prod_j (X_j + ΔX_j) - prod_j X_j|`
`<= (prod_j (1 + δ_j) - 1) * prod_j |X_j|`

componentwise. -/
theorem matSeqProd_componentwise_perturbation_bound (n m : ℕ)
    (X ΔX : Fin m → Fin n → Fin n → ℝ) (δ : Fin m → ℝ)
    (hδ : ∀ r, 0 ≤ δ r)
    (hΔ : ∀ r i j, |ΔX r i j| ≤ δ r * |X r i j|) :
    ∀ i j,
      |matSeqProd n m (fun r i j => X r i j + ΔX r i j) i j -
        matSeqProd n m X i j| ≤
        (scalarSeqProd m (fun r => 1 + δ r) - 1) *
          matSeqProd n m (fun r => absMatrix n (X r)) i j := by
  induction m with
  | zero =>
      intro i j
      simp [matSeqProd, scalarSeqProd]
  | succ m ih =>
      intro i j
      let tailX : Fin m → Fin n → Fin n → ℝ := fun r => X r.succ
      let tailΔ : Fin m → Fin n → Fin n → ℝ := fun r => ΔX r.succ
      let tailPert : Fin m → Fin n → Fin n → ℝ :=
        fun r i j => X r.succ i j + ΔX r.succ i j
      let tailAbs : Fin m → Fin n → Fin n → ℝ :=
        fun r => absMatrix n (X r.succ)
      let tailScale : ℝ := scalarSeqProd m (fun r => 1 + δ r.succ)
      have htail_abs :
          ∀ k j,
            |matSeqProd n m tailPert k j| ≤
              tailScale * matSeqProd n m tailAbs k j := by
        intro k j
        simpa [tailPert, tailAbs, tailScale] using
          matSeqProd_abs_perturbed_le_scalar_abs n m tailX tailΔ
            (fun r => δ r.succ) (fun r => hδ r.succ)
            (fun r => hΔ r.succ) k j
      have htail_err :
          ∀ k j,
            |matSeqProd n m tailPert k j - matSeqProd n m tailX k j| ≤
              (tailScale - 1) * matSeqProd n m tailAbs k j := by
        intro k j
        simpa [tailX, tailΔ, tailPert, tailAbs, tailScale] using
          ih tailX tailΔ (fun r => δ r.succ) (fun r => hδ r.succ)
            (fun r => hΔ r.succ) k j
      have htail_nonneg :
          ∀ k j, 0 ≤ matSeqProd n m tailAbs k j :=
        matSeqProd_nonneg n m tailAbs (by
          intro r a b
          simp [tailAbs, absMatrix])
      have htailScale_one : 1 ≤ tailScale := by
        exact one_le_scalarSeqProd m (fun r => 1 + δ r.succ)
          (fun r => by linarith [hδ r.succ])
      have htailScale_nonneg : 0 ≤ tailScale := le_trans zero_le_one htailScale_one
      have htailScale_sub_nonneg : 0 ≤ tailScale - 1 := by linarith
      have hhead_abs :
          ∀ k, |X 0 i k + ΔX 0 i k| ≤ (1 + δ 0) * |X 0 i k| := by
        intro k
        calc
          |X 0 i k + ΔX 0 i k| ≤ |X 0 i k| + |ΔX 0 i k| :=
              abs_add_le (X 0 i k) (ΔX 0 i k)
          _ ≤ |X 0 i k| + δ 0 * |X 0 i k| := by
              linarith [hΔ 0 i k]
          _ = (1 + δ 0) * |X 0 i k| := by ring
      have hterm :
          ∀ k : Fin n,
            |(X 0 i k + ΔX 0 i k) * matSeqProd n m tailPert k j -
              X 0 i k * matSeqProd n m tailX k j| ≤
              |ΔX 0 i k| * |matSeqProd n m tailPert k j| +
                |X 0 i k| *
                  |matSeqProd n m tailPert k j -
                    matSeqProd n m tailX k j| := by
        intro k
        let x0 := X 0 i k
        let dx := ΔX 0 i k
        let pp := matSeqProd n m tailPert k j
        let pt := matSeqProd n m tailX k j
        change |(x0 + dx) * pp - x0 * pt| ≤
          |dx| * |pp| + |x0| * |pp - pt|
        have hrewrite : (x0 + dx) * pp - x0 * pt = dx * pp + x0 * (pp - pt) := by
          ring
        rw [hrewrite]
        calc
          |dx * pp + x0 * (pp - pt)| ≤ |dx * pp| + |x0 * (pp - pt)| :=
              abs_add_le _ _
          _ = |dx| * |pp| + |x0| * |pp - pt| := by
              rw [abs_mul, abs_mul]
      have hterm_raw :
          ∀ k : Fin n,
            |(fun r i j => X r i j + ΔX r i j) 0 i k *
                matSeqProd n m
                  (fun j => (fun r i j => X r i j + ΔX r i j) j.succ) k j -
              X 0 i k * matSeqProd n m (fun j => X j.succ) k j| ≤
              |ΔX 0 i k| * |matSeqProd n m tailPert k j| +
                |X 0 i k| *
                  |matSeqProd n m tailPert k j -
                    matSeqProd n m tailX k j| := by
        intro k
        simpa [tailPert, tailX] using hterm k
      calc
        |matSeqProd n (m + 1) (fun r i j => X r i j + ΔX r i j) i j -
            matSeqProd n (m + 1) X i j|
            ≤ ∑ k : Fin n,
                |(fun r i j => X r i j + ΔX r i j) 0 i k *
                    matSeqProd n m
                      (fun j => (fun r i j => X r i j + ΔX r i j) j.succ) k j -
                  X 0 i k * matSeqProd n m (fun j => X j.succ) k j| :=
              by
                simpa [matSeqProd, matMul, Finset.sum_sub_distrib] using
                  Finset.abs_sum_le_sum_abs
                    (s := (Finset.univ : Finset (Fin n)))
                    (f := fun k : Fin n =>
                      (fun r i j => X r i j + ΔX r i j) 0 i k *
                          matSeqProd n m
                            (fun j => (fun r i j => X r i j + ΔX r i j) j.succ) k j -
                        X 0 i k * matSeqProd n m (fun j => X j.succ) k j)
        _ ≤
              ∑ k : Fin n,
                |ΔX 0 i k| * |matSeqProd n m tailPert k j| +
              ∑ k : Fin n,
                |X 0 i k| *
                  |matSeqProd n m tailPert k j -
                    matSeqProd n m tailX k j| := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_le_sum
              intro k _
              exact hterm_raw k
        _ ≤
              ∑ k : Fin n,
                (δ 0 * |X 0 i k|) *
                  (tailScale * matSeqProd n m tailAbs k j) +
              ∑ k : Fin n,
                |X 0 i k| *
                  ((tailScale - 1) * matSeqProd n m tailAbs k j) := by
              apply add_le_add <;> apply Finset.sum_le_sum <;> intro k _
              · calc
                  |ΔX 0 i k| * |matSeqProd n m tailPert k j|
                      ≤ (δ 0 * |X 0 i k|) *
                          |matSeqProd n m tailPert k j| := by
                        exact mul_le_mul_of_nonneg_right (hΔ 0 i k) (abs_nonneg _)
                  _ ≤ (δ 0 * |X 0 i k|) *
                          (tailScale * matSeqProd n m tailAbs k j) := by
                        exact mul_le_mul_of_nonneg_left (htail_abs k j)
                          (mul_nonneg (hδ 0) (abs_nonneg _))
              · exact mul_le_mul_of_nonneg_left (htail_err k j) (abs_nonneg _)
        _ =
              (δ 0 * tailScale + (tailScale - 1)) *
                (∑ k : Fin n, absMatrix n (X 0) i k *
                  matSeqProd n m tailAbs k j) := by
              rw [Finset.mul_sum]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro k _
              simp [tailAbs, absMatrix]
              ring
        _ =
              (scalarSeqProd (m + 1) (fun r => 1 + δ r) - 1) *
                matSeqProd n (m + 1) (fun r => absMatrix n (X r)) i j := by
              change
                (δ 0 * tailScale + (tailScale - 1)) *
                    (∑ k : Fin n, absMatrix n (X 0) i k *
                      matSeqProd n m tailAbs k j) =
                  (((1 + δ 0) * tailScale) - 1) *
                    (∑ k : Fin n, absMatrix n (X 0) i k *
                      matSeqProd n m tailAbs k j)
              ring

/-- Higham Chapter 3, Lemma 3.6, perturbed finite-product size bound for an
abstract consistent matrix norm.

This is the auxiliary product-size estimate: if `N` is nonnegative,
submultiplicative, and subadditive, and `N (Delta X_j) <= delta_j * N X_j`,
then

`N (prod_j (X_j + Delta X_j)) <= prod_j (1 + delta_j) * prod_j N(X_j)`.

The assumptions package exactly the norm properties used in the source's
"consistent norm" induction. -/
theorem matSeqProd_norm_perturbed_le_scalar (n m : ℕ)
    (N : (Fin n → Fin n → ℝ) → ℝ)
    (hN_nonneg : ∀ A, 0 ≤ N A)
    (hN_id : N (idMatrix n) ≤ 1)
    (hN_add : ∀ A B,
      N (fun i j => A i j + B i j) ≤ N A + N B)
    (hN_mul : ∀ A B, N (matMul n A B) ≤ N A * N B)
    (X ΔX : Fin m → Fin n → Fin n → ℝ) (δ : Fin m → ℝ)
    (hδ : ∀ r, 0 ≤ δ r)
    (hΔ : ∀ r, N (ΔX r) ≤ δ r * N (X r)) :
    N (matSeqProd n m (fun r i j => X r i j + ΔX r i j)) ≤
      scalarSeqProd m (fun r => 1 + δ r) *
        scalarSeqProd m (fun r => N (X r)) := by
  induction m with
  | zero =>
      simp [matSeqProd, scalarSeqProd]
      exact hN_id
  | succ m ih =>
      let tailX : Fin m → Fin n → Fin n → ℝ := fun r => X r.succ
      let tailΔ : Fin m → Fin n → Fin n → ℝ := fun r => ΔX r.succ
      let tailPert : Fin m → Fin n → Fin n → ℝ :=
        fun r i j => X r.succ i j + ΔX r.succ i j
      let tailScale : ℝ := scalarSeqProd m (fun r => 1 + δ r.succ)
      let tailNorm : ℝ := scalarSeqProd m (fun r => N (X r.succ))
      have htail :
          N (matSeqProd n m tailPert) ≤ tailScale * tailNorm := by
        simpa [tailX, tailΔ, tailPert, tailScale, tailNorm] using
          ih tailX tailΔ (fun r => δ r.succ) (fun r => hδ r.succ)
            (fun r => hΔ r.succ)
      have htail_rhs_nonneg : 0 ≤ tailScale * tailNorm := by
        exact mul_nonneg
          (scalarSeqProd_nonneg m (fun r => 1 + δ r.succ)
            (fun r => by linarith [hδ r.succ]))
          (scalarSeqProd_nonneg m (fun r => N (X r.succ))
            (fun r => hN_nonneg (X r.succ)))
      have hhead :
          N (fun i j => X 0 i j + ΔX 0 i j) ≤ (1 + δ 0) * N (X 0) := by
        calc
          N (fun i j => X 0 i j + ΔX 0 i j)
              ≤ N (X 0) + N (ΔX 0) := hN_add (X 0) (ΔX 0)
          _ ≤ N (X 0) + δ 0 * N (X 0) := by
              linarith [hΔ 0]
          _ = (1 + δ 0) * N (X 0) := by ring
      have hhead_rhs_nonneg : 0 ≤ (1 + δ 0) * N (X 0) := by
        exact mul_nonneg (by linarith [hδ 0]) (hN_nonneg (X 0))
      calc
        N (matSeqProd n (m + 1) (fun r i j => X r i j + ΔX r i j))
            =
              N (matMul n
                (fun i j => X 0 i j + ΔX 0 i j)
                (matSeqProd n m tailPert)) := by
              rfl
        _ ≤
              N (fun i j => X 0 i j + ΔX 0 i j) *
                N (matSeqProd n m tailPert) :=
              hN_mul _ _
        _ ≤ ((1 + δ 0) * N (X 0)) * (tailScale * tailNorm) := by
              exact mul_le_mul hhead htail (hN_nonneg _) hhead_rhs_nonneg
        _ =
              scalarSeqProd (m + 1) (fun r => 1 + δ r) *
                scalarSeqProd (m + 1) (fun r => N (X r)) := by
              simp [scalarSeqProd, tailScale, tailNorm]
              ring

/-- Higham Chapter 3, Lemma 3.6, finite-sequence normwise form.

For any matrix norm `N` satisfying nonnegativity, subadditivity, and
submultiplicativity, component factor bounds
`N (Delta X_j) <= delta_j * N X_j` imply

`N (prod_j (X_j + Delta X_j) - prod_j X_j)`
`<= (prod_j (1 + delta_j) - 1) * prod_j N(X_j)`.

The theorem uses non-strict inequalities, which are the repository's usual
formal surface; the source's strict version follows by monotonic weakening in
applications with strict hypotheses. -/
theorem matSeqProd_normwise_perturbation_bound (n m : ℕ)
    (N : (Fin n → Fin n → ℝ) → ℝ)
    (hN_nonneg : ∀ A, 0 ≤ N A)
    (hN_zero : N (fun _ _ => 0) ≤ 0)
    (hN_id : N (idMatrix n) ≤ 1)
    (hN_add : ∀ A B,
      N (fun i j => A i j + B i j) ≤ N A + N B)
    (hN_mul : ∀ A B, N (matMul n A B) ≤ N A * N B)
    (X ΔX : Fin m → Fin n → Fin n → ℝ) (δ : Fin m → ℝ)
    (hδ : ∀ r, 0 ≤ δ r)
    (hΔ : ∀ r, N (ΔX r) ≤ δ r * N (X r)) :
    N (fun i j =>
      matSeqProd n m (fun r i j => X r i j + ΔX r i j) i j -
        matSeqProd n m X i j) ≤
      (scalarSeqProd m (fun r => 1 + δ r) - 1) *
        scalarSeqProd m (fun r => N (X r)) := by
  induction m with
  | zero =>
      simp [matSeqProd, scalarSeqProd]
      exact hN_zero
  | succ m ih =>
      let tailX : Fin m → Fin n → Fin n → ℝ := fun r => X r.succ
      let tailΔ : Fin m → Fin n → Fin n → ℝ := fun r => ΔX r.succ
      let tailPert : Fin m → Fin n → Fin n → ℝ :=
        fun r i j => X r.succ i j + ΔX r.succ i j
      let tailScale : ℝ := scalarSeqProd m (fun r => 1 + δ r.succ)
      let tailNorm : ℝ := scalarSeqProd m (fun r => N (X r.succ))
      have htail_size :
          N (matSeqProd n m tailPert) ≤ tailScale * tailNorm := by
        simpa [tailX, tailΔ, tailPert, tailScale, tailNorm] using
          matSeqProd_norm_perturbed_le_scalar n m N hN_nonneg hN_id hN_add hN_mul
            tailX tailΔ (fun r => δ r.succ) (fun r => hδ r.succ)
            (fun r => hΔ r.succ)
      have htail_err :
          N (fun i j => matSeqProd n m tailPert i j -
            matSeqProd n m tailX i j) ≤ (tailScale - 1) * tailNorm := by
        simpa [tailX, tailΔ, tailPert, tailScale, tailNorm] using
          ih tailX tailΔ (fun r => δ r.succ) (fun r => hδ r.succ)
            (fun r => hΔ r.succ)
      have htailScale_one : 1 ≤ tailScale := by
        exact one_le_scalarSeqProd m (fun r => 1 + δ r.succ)
          (fun r => by linarith [hδ r.succ])
      have htailScale_nonneg : 0 ≤ tailScale := le_trans zero_le_one htailScale_one
      have htailScale_sub_nonneg : 0 ≤ tailScale - 1 := by linarith
      have htailNorm_nonneg : 0 ≤ tailNorm := by
        exact scalarSeqProd_nonneg m (fun r => N (X r.succ))
          (fun r => hN_nonneg (X r.succ))
      have hdelta_head_nonneg : 0 ≤ δ 0 * N (X 0) := by
        exact mul_nonneg (hδ 0) (hN_nonneg (X 0))
      have hsplit :
          (fun i j =>
            matSeqProd n (m + 1) (fun r i j => X r i j + ΔX r i j) i j -
              matSeqProd n (m + 1) X i j) =
          (fun i j =>
            matMul n (ΔX 0) (matSeqProd n m tailPert) i j +
              matMul n (X 0)
                (fun a b => matSeqProd n m tailPert a b -
                  matSeqProd n m tailX a b) i j) := by
        ext i j
        change
          matMul n (fun i j => X 0 i j + ΔX 0 i j) (matSeqProd n m tailPert) i j -
              matMul n (X 0) (matSeqProd n m tailX) i j =
            matMul n (ΔX 0) (matSeqProd n m tailPert) i j +
              matMul n (X 0)
                (fun a b => matSeqProd n m tailPert a b -
                  matSeqProd n m tailX a b) i j
        unfold matMul
        rw [← Finset.sum_sub_distrib]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      calc
        N (fun i j =>
          matSeqProd n (m + 1) (fun r i j => X r i j + ΔX r i j) i j -
            matSeqProd n (m + 1) X i j)
            =
              N (fun i j =>
                matMul n (ΔX 0) (matSeqProd n m tailPert) i j +
                  matMul n (X 0)
                    (fun a b => matSeqProd n m tailPert a b -
                      matSeqProd n m tailX a b) i j) := by
              rw [hsplit]
        _ ≤
              N (matMul n (ΔX 0) (matSeqProd n m tailPert)) +
                N (matMul n (X 0)
                  (fun a b => matSeqProd n m tailPert a b -
                    matSeqProd n m tailX a b)) :=
              hN_add _ _
        _ ≤
              N (ΔX 0) * N (matSeqProd n m tailPert) +
                N (X 0) *
                  N (fun a b => matSeqProd n m tailPert a b -
                    matSeqProd n m tailX a b) := by
              exact add_le_add (hN_mul _ _) (hN_mul _ _)
        _ ≤
              (δ 0 * N (X 0)) * (tailScale * tailNorm) +
                N (X 0) * ((tailScale - 1) * tailNorm) := by
              apply add_le_add
              · calc
                  N (ΔX 0) * N (matSeqProd n m tailPert)
                      ≤ (δ 0 * N (X 0)) * N (matSeqProd n m tailPert) := by
                        exact mul_le_mul_of_nonneg_right (hΔ 0) (hN_nonneg _)
                  _ ≤ (δ 0 * N (X 0)) * (tailScale * tailNorm) := by
                        exact mul_le_mul_of_nonneg_left htail_size hdelta_head_nonneg
              · exact mul_le_mul_of_nonneg_left htail_err (hN_nonneg (X 0))
        _ =
              (scalarSeqProd (m + 1) (fun r => 1 + δ r) - 1) *
                scalarSeqProd (m + 1) (fun r => N (X r)) := by
              simp [scalarSeqProd, tailScale, tailNorm]
              ring

/-- Higham Chapter 3, Lemma 3.7, mixed-norm finite-sequence form.

This is the induction core behind the source's Frobenius/spectral variant:
the error is measured by `NF`, the unperturbed factors are measured by `NS`,
and the hypotheses expose exactly the mixed multiplication bounds needed for
the proof.  Instantiating `NF` with Frobenius norm and `NS` with an operator-2
certificate uses the norm inequality cited by the book from Problem 6.5. -/
theorem matSeqProd_mixed_normwise_perturbation_bound (n m : ℕ)
    (NF NS : (Fin n → Fin n → ℝ) → ℝ)
    (hF_zero : NF (fun _ _ => 0) ≤ 0)
    (hF_add : ∀ A B,
      NF (fun i j => A i j + B i j) ≤ NF A + NF B)
    (hF_mul_left : ∀ A B, NF (matMul n A B) ≤ NS A * NF B)
    (hF_mul_right : ∀ A B, NF (matMul n A B) ≤ NF A * NS B)
    (hS_nonneg : ∀ A, 0 ≤ NS A)
    (hS_id : NS (idMatrix n) ≤ 1)
    (hS_add : ∀ A B,
      NS (fun i j => A i j + B i j) ≤ NS A + NS B)
    (hS_mul : ∀ A B, NS (matMul n A B) ≤ NS A * NS B)
    (X ΔX : Fin m → Fin n → Fin n → ℝ) (δ : Fin m → ℝ)
    (hδ : ∀ r, 0 ≤ δ r)
    (hΔF : ∀ r, NF (ΔX r) ≤ δ r * NS (X r))
    (hΔS : ∀ r, NS (ΔX r) ≤ δ r * NS (X r)) :
    NF (fun i j =>
      matSeqProd n m (fun r i j => X r i j + ΔX r i j) i j -
        matSeqProd n m X i j) ≤
      (scalarSeqProd m (fun r => 1 + δ r) - 1) *
        scalarSeqProd m (fun r => NS (X r)) := by
  induction m with
  | zero =>
      simp [matSeqProd, scalarSeqProd]
      exact hF_zero
  | succ m ih =>
      let tailX : Fin m → Fin n → Fin n → ℝ := fun r => X r.succ
      let tailΔ : Fin m → Fin n → Fin n → ℝ := fun r => ΔX r.succ
      let tailPert : Fin m → Fin n → Fin n → ℝ :=
        fun r i j => X r.succ i j + ΔX r.succ i j
      let tailScale : ℝ := scalarSeqProd m (fun r => 1 + δ r.succ)
      let tailNorm : ℝ := scalarSeqProd m (fun r => NS (X r.succ))
      have htail_size :
          NS (matSeqProd n m tailPert) ≤ tailScale * tailNorm := by
        simpa [tailX, tailΔ, tailPert, tailScale, tailNorm] using
          matSeqProd_norm_perturbed_le_scalar n m NS hS_nonneg hS_id hS_add hS_mul
            tailX tailΔ (fun r => δ r.succ) (fun r => hδ r.succ)
            (fun r => hΔS r.succ)
      have htail_err :
          NF (fun i j => matSeqProd n m tailPert i j -
            matSeqProd n m tailX i j) ≤ (tailScale - 1) * tailNorm := by
        simpa [tailX, tailΔ, tailPert, tailScale, tailNorm] using
          ih tailX tailΔ (fun r => δ r.succ) (fun r => hδ r.succ)
            (fun r => hΔF r.succ) (fun r => hΔS r.succ)
      have htailScale_one : 1 ≤ tailScale := by
        exact one_le_scalarSeqProd m (fun r => 1 + δ r.succ)
          (fun r => by linarith [hδ r.succ])
      have htailScale_sub_nonneg : 0 ≤ tailScale - 1 := by linarith
      have htailNorm_nonneg : 0 ≤ tailNorm := by
        exact scalarSeqProd_nonneg m (fun r => NS (X r.succ))
          (fun r => hS_nonneg (X r.succ))
      have hdelta_head_nonneg : 0 ≤ δ 0 * NS (X 0) := by
        exact mul_nonneg (hδ 0) (hS_nonneg (X 0))
      have hsplit :
          (fun i j =>
            matSeqProd n (m + 1) (fun r i j => X r i j + ΔX r i j) i j -
              matSeqProd n (m + 1) X i j) =
          (fun i j =>
            matMul n (ΔX 0) (matSeqProd n m tailPert) i j +
              matMul n (X 0)
                (fun a b => matSeqProd n m tailPert a b -
                  matSeqProd n m tailX a b) i j) := by
        ext i j
        change
          matMul n (fun i j => X 0 i j + ΔX 0 i j) (matSeqProd n m tailPert) i j -
              matMul n (X 0) (matSeqProd n m tailX) i j =
            matMul n (ΔX 0) (matSeqProd n m tailPert) i j +
              matMul n (X 0)
                (fun a b => matSeqProd n m tailPert a b -
                  matSeqProd n m tailX a b) i j
        unfold matMul
        rw [← Finset.sum_sub_distrib]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      calc
        NF (fun i j =>
          matSeqProd n (m + 1) (fun r i j => X r i j + ΔX r i j) i j -
            matSeqProd n (m + 1) X i j)
            =
              NF (fun i j =>
                matMul n (ΔX 0) (matSeqProd n m tailPert) i j +
                  matMul n (X 0)
                    (fun a b => matSeqProd n m tailPert a b -
                      matSeqProd n m tailX a b) i j) := by
              rw [hsplit]
        _ ≤
              NF (matMul n (ΔX 0) (matSeqProd n m tailPert)) +
                NF (matMul n (X 0)
                  (fun a b => matSeqProd n m tailPert a b -
                    matSeqProd n m tailX a b)) :=
              hF_add _ _
        _ ≤
              NF (ΔX 0) * NS (matSeqProd n m tailPert) +
                NS (X 0) *
                  NF (fun a b => matSeqProd n m tailPert a b -
                    matSeqProd n m tailX a b) := by
              exact add_le_add (hF_mul_right _ _) (hF_mul_left _ _)
        _ ≤
              (δ 0 * NS (X 0)) * (tailScale * tailNorm) +
                NS (X 0) * ((tailScale - 1) * tailNorm) := by
              apply add_le_add
              · calc
                  NF (ΔX 0) * NS (matSeqProd n m tailPert)
                      ≤ (δ 0 * NS (X 0)) * NS (matSeqProd n m tailPert) := by
                        exact mul_le_mul_of_nonneg_right (hΔF 0) (hS_nonneg _)
                  _ ≤ (δ 0 * NS (X 0)) * (tailScale * tailNorm) := by
                        exact mul_le_mul_of_nonneg_left htail_size hdelta_head_nonneg
              · exact mul_le_mul_of_nonneg_left htail_err (hS_nonneg (X 0))
        _ =
              (scalarSeqProd (m + 1) (fun r => 1 + δ r) - 1) *
                scalarSeqProd (m + 1) (fun r => NS (X r)) := by
              simp [scalarSeqProd, tailScale, tailNorm]
              ring

-- ============================================================
-- Neumann partial sums: S_N = ∑_{k=0}^{N} M^k
-- ============================================================

/-- **Neumann partial sum**: S_N = ∑_{k=0}^{N} M^k. -/
noncomputable def neumannSum (n : ℕ) (M : Fin n → Fin n → ℝ) : ℕ → (Fin n → Fin n → ℝ)
  | 0 => idMatrix n
  | N + 1 => fun i j => neumannSum n M N i j + matPow n M (N + 1) i j

/-- S_0 = I. -/
theorem neumannSum_zero (n : ℕ) (M : Fin n → Fin n → ℝ) :
    neumannSum n M 0 = idMatrix n := rfl

/-- S_{N+1} = S_N + M^{N+1}. -/
theorem neumannSum_succ (n : ℕ) (M : Fin n → Fin n → ℝ) (N : ℕ) :
    neumannSum n M (N + 1) = fun i j => neumannSum n M N i j + matPow n M (N + 1) i j := rfl

-- ============================================================
-- Telescoping identity: (I − M) · S_N = I − M^{N+1}
-- ============================================================

/-- **M · S_N = S_N · M** (M commutes with its own partial sums).

    Actually we prove the useful direction: M · S_N = S_{N+1} − I. -/
theorem matMul_neumannSum (n : ℕ) (M : Fin n → Fin n → ℝ) (N : ℕ) :
    ∀ i j, ∑ k : Fin n, M i k * neumannSum n M N k j =
      neumannSum n M (N + 1) i j - idMatrix n i j := by
  induction N with
  | zero =>
    intro i j
    simp [neumannSum, matPow, matMul, idMatrix]
  | succ N ih =>
    intro i j
    simp only [neumannSum_succ]
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [ih i j]
    have hpow : ∑ k : Fin n, M i k * matPow n M (N + 1) k j =
        matPow n M (N + 2) i j := by
      simp only [matPow_succ, matMul]
    rw [hpow]; simp only [neumannSum_succ]; ring

/-- **Telescoping identity**: (I − M) · S_N = I − M^{N+1}.

    This is the key algebraic identity for the Neumann series. -/
theorem neumann_telescope (n : ℕ) (M : Fin n → Fin n → ℝ) (N : ℕ) :
    matMul n (matSub_id n M) (neumannSum n M N) =
      fun i j => idMatrix n i j - matPow n M (N + 1) i j := by
  ext i j; unfold matMul matSub_id
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  have hid : ∑ k : Fin n, idMatrix n i k * neumannSum n M N k j =
      neumannSum n M N i j := by
    unfold idMatrix; simp [Finset.sum_ite_eq, Finset.mem_univ]
  rw [hid, matMul_neumannSum n M N i j]
  simp [neumannSum_succ]; ring

/-- **Right telescoping**: S_N · (I − M) = I − M^{N+1}.

    The Neumann partial sum also commutes with (I − M) from the right. -/
theorem neumann_telescope_right (n : ℕ) (M : Fin n → Fin n → ℝ) (N : ℕ) :
    matMul n (neumannSum n M N) (matSub_id n M) =
      fun i j => idMatrix n i j - matPow n M (N + 1) i j := by
  induction N with
  | zero =>
    ext i j
    -- S_0 · (I-M) = I · (I-M) = I-M = I - M^1
    have hid := congr_fun (congr_fun (matMul_id_left n (matSub_id n M)) i) j
    unfold matMul at hid ⊢; simp only [neumannSum_zero]
    rw [hid]; unfold matSub_id; rw [matPow_one]
  | succ N ih =>
    ext i j; unfold matMul
    simp only [neumannSum_succ]
    simp_rw [add_mul, Finset.sum_add_distrib]
    -- First sum: S_N · (I − M) at (i,j) = I(i,j) − M^{N+1}(i,j)
    have h1 : ∑ k : Fin n, neumannSum n M N i k * matSub_id n M k j =
        idMatrix n i j - matPow n M (N + 1) i j := by
      have := congr_fun (congr_fun ih i) j; unfold matMul at this; exact this
    rw [h1]
    -- Second sum: M^{N+1} · (I − M) at (i,j) = M^{N+1}(i,j) − M^{N+2}(i,j)
    have h2 : ∑ k : Fin n, matPow n M (N + 1) i k * matSub_id n M k j =
        matPow n M (N + 1) i j - matPow n M (N + 2) i j := by
      unfold matSub_id
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      congr 1
      · unfold idMatrix; simp [Finset.sum_ite_eq', Finset.mem_univ]
      · simp only [matPow_succ_right, matMul]
    rw [h2]; ring

-- ============================================================
-- Infinity norm and 1-norm
-- ============================================================

/-- Compatibility name for Mathlib's finite-function sup norm:
    `‖v‖ = max_i |v_i|`, with value `0` for `Fin 0`. -/
noncomputable def infNormVec {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ‖v‖

/-- Compatibility name for Mathlib's `linfty` matrix operator norm:
    `‖A‖∞ = max_i ∑_j |A_ij|`, with value `0` for `Fin 0`. -/
noncomputable def infNorm {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  ‖(Matrix.of A : Matrix (Fin n) (Fin n) ℝ)‖

/-- Infinity norm of a matrix is nonneg. -/
lemma infNorm_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    0 ≤ infNorm A := by
  unfold infNorm
  rw [Matrix.linfty_opNorm_def]
  exact NNReal.coe_nonneg _

/-- Infinity norm of a vector is nonneg. -/
lemma infNormVec_nonneg {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ infNormVec v := by
  unfold infNormVec
  exact norm_nonneg _

/-- 1-norm of a matrix (max column sum): max_j ∑_i |A_ij|.
    This is the Mathlib `linfty` operator norm of the transpose. -/
noncomputable def oneNorm {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  infNorm (fun i j => A j i)

/-- 1-norm of a matrix is nonneg. -/
lemma oneNorm_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    0 ≤ oneNorm A := by
  unfold oneNorm
  exact infNorm_nonneg _

/-- 1-norm equals ∞-norm of the transpose. -/
theorem oneNorm_eq_infNorm_transpose {n : ℕ} (A : Fin n → Fin n → ℝ) :
    oneNorm A = infNorm (fun i j => A j i) := by
  rfl

/-- Each row sum of a matrix is bounded by its ∞-norm. -/
lemma row_sum_le_infNorm {n : ℕ} (A : Fin n → Fin n → ℝ)
    (i : Fin n) : ∑ j : Fin n, |A i j| ≤ infNorm A := by
  unfold infNorm
  rw [Matrix.linfty_opNorm_def]
  let f : Fin n → ℝ≥0 :=
    fun i => ∑ j : Fin n, ‖(Matrix.of A : Matrix (Fin n) (Fin n) ℝ) i j‖₊
  have hnn : f i ≤ Finset.univ.sup f :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin n))) (f := f) (Finset.mem_univ i)
  have h : (f i : ℝ) ≤ ((Finset.univ.sup f : ℝ≥0) : ℝ) := by
    exact_mod_cast hnn
  simpa [f, Real.norm_eq_abs, NNReal.coe_sum] using h

/-- A row-wise proof gives an ∞-norm bound. -/
lemma infNorm_le_of_row_sum_le {n : ℕ} (A : Fin n → Fin n → ℝ) {c : ℝ}
    (hrows : ∀ i : Fin n, ∑ j : Fin n, |A i j| ≤ c) (hc : 0 ≤ c) :
    infNorm A ≤ c := by
  unfold infNorm
  rw [Matrix.linfty_opNorm_def]
  let f : Fin n → ℝ≥0 :=
    fun i => ∑ j : Fin n, ‖(Matrix.of A : Matrix (Fin n) (Fin n) ℝ) i j‖₊
  have hrows_nn : ∀ i, f i ≤ Real.toNNReal c := by
    intro i
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal c hc]
    simpa [f, Real.norm_eq_abs, NNReal.coe_sum] using hrows i
  have hsup : Finset.univ.sup f ≤ Real.toNNReal c :=
    Finset.sup_le (fun i _ => hrows_nn i)
  have hreal : ((Finset.univ.sup f : ℝ≥0) : ℝ) ≤ c := by
    rw [← Real.coe_toNNReal c hc]
    exact_mod_cast hsup
  simpa [f] using hreal

/-- A nonsingular nonempty square matrix has positive repository infinity norm.

    This is a small determinant-to-norm bridge: if `‖A‖∞ = 0`, every row sum
    of absolute values is zero, hence every entry is zero, forcing a zero row
    and therefore zero determinant. -/
lemma infNorm_pos_of_det_ne_zero {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    0 < infNorm A := by
  refine lt_of_le_of_ne (infNorm_nonneg A) ?_
  intro hzero
  have hrow_zero : ∀ i : Fin n, ∑ j : Fin n, |A i j| = 0 := by
    intro i
    have hle : ∑ j : Fin n, |A i j| ≤ 0 := by
      simpa [hzero] using row_sum_le_infNorm A i
    have hnonneg : 0 ≤ ∑ j : Fin n, |A i j| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg (A i j))
    exact le_antisymm hle hnonneg
  have hentries : ∀ i j : Fin n, A i j = 0 := by
    intro i j
    have hterm :
        |A i j| = 0 := by
      have hterms :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => abs_nonneg (A i j))).mp (hrow_zero i)
      exact hterms j (Finset.mem_univ j)
    exact abs_eq_zero.mp hterm
  have hdet_zero :
      Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) = 0 := by
    exact Matrix.det_eq_zero_of_row_eq_zero (⟨0, hn⟩ : Fin n)
      (fun j => hentries ⟨0, hn⟩ j)
  exact hdet hdet_zero

/-- Each column sum is bounded by the 1-norm. -/
lemma col_sum_le_oneNorm {n : ℕ} (A : Fin n → Fin n → ℝ)
    (j : Fin n) : ∑ i : Fin n, |A i j| ≤ oneNorm A := by
  exact row_sum_le_infNorm (fun i j => A j i) j

/-- Each component of a vector is bounded by its ∞-norm. -/
lemma abs_le_infNormVec {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |v i| ≤ infNormVec v := by
  unfold infNormVec
  simpa using norm_le_pi_norm v i

/-- A componentwise bound gives a vector ∞-norm bound. -/
lemma infNormVec_le_of_abs_le {n : ℕ} (v : Fin n → ℝ) {c : ℝ}
    (h : ∀ i : Fin n, |v i| ≤ c) (hc : 0 ≤ c) :
    infNormVec v ≤ c := by
  unfold infNormVec
  rw [pi_norm_le_iff_of_nonneg hc]
  intro i
  simpa using h i

/-- A column-wise proof gives a 1-norm bound. -/
lemma oneNorm_le_of_col_sum_le {n : ℕ} (A : Fin n → Fin n → ℝ) {c : ℝ}
    (hcols : ∀ j : Fin n, ∑ i : Fin n, |A i j| ≤ c) (hc : 0 ≤ c) :
    oneNorm A ≤ c := by
  unfold oneNorm
  apply infNorm_le_of_row_sum_le
  · intro j
    exact hcols j
  · exact hc

/-- Rectangular infinity norm: maximum absolute row sum, with value `0` when
    there are no rows. -/
noncomputable def infNormRect {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ :=
  let f : Fin m → ℝ≥0 := fun i => ∑ j : Fin n, ‖A i j‖₊
  ((Finset.univ.sup f : ℝ≥0) : ℝ)

/-- Rectangular matrix infinity norm is nonnegative. -/
lemma infNormRect_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    0 ≤ infNormRect A := by
  unfold infNormRect
  exact NNReal.coe_nonneg _

/-- Rectangular 1-norm: maximum absolute column sum, with value `0` when
    there are no columns. -/
noncomputable def oneNormRect {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ :=
  infNormRect (fun j : Fin n => fun i : Fin m => A i j)

/-- Rectangular matrix 1-norm is nonnegative. -/
lemma oneNormRect_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    0 ≤ oneNormRect A := by
  unfold oneNormRect
  exact infNormRect_nonneg _

/-- Each rectangular row sum is bounded by the rectangular infinity norm. -/
lemma row_sum_le_infNormRect {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : ∑ j : Fin n, |A i j| ≤ infNormRect A := by
  unfold infNormRect
  let f : Fin m → ℝ≥0 := fun i => ∑ j : Fin n, ‖A i j‖₊
  have hnn : f i ≤ Finset.univ.sup f :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin m))) (f := f) (Finset.mem_univ i)
  have h : (f i : ℝ) ≤ ((Finset.univ.sup f : ℝ≥0) : ℝ) := by
    exact_mod_cast hnn
  simpa [f, Real.norm_eq_abs, NNReal.coe_sum] using h

/-- A rectangular row-wise proof gives an infinity-norm bound. -/
lemma infNormRect_le_of_row_sum_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {c : ℝ}
    (hrows : ∀ i : Fin m, ∑ j : Fin n, |A i j| ≤ c) (hc : 0 ≤ c) :
    infNormRect A ≤ c := by
  unfold infNormRect
  let f : Fin m → ℝ≥0 := fun i => ∑ j : Fin n, ‖A i j‖₊
  have hrows_nn : ∀ i, f i ≤ Real.toNNReal c := by
    intro i
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal c hc]
    simpa [f, Real.norm_eq_abs, NNReal.coe_sum] using hrows i
  have hsup : Finset.univ.sup f ≤ Real.toNNReal c :=
    Finset.sup_le (fun i _ => hrows_nn i)
  have hreal : ((Finset.univ.sup f : ℝ≥0) : ℝ) ≤ c := by
    rw [← Real.coe_toNNReal c hc]
    exact_mod_cast hsup
  simpa [f] using hreal

/-- Each rectangular column sum is bounded by the rectangular 1-norm. -/
lemma col_sum_le_oneNormRect {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (j : Fin n) : ∑ i : Fin m, |A i j| ≤ oneNormRect A := by
  exact row_sum_le_infNormRect (fun j : Fin n => fun i : Fin m => A i j) j

/-- A rectangular column-wise proof gives a 1-norm bound. -/
lemma oneNormRect_le_of_col_sum_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {c : ℝ}
    (hcols : ∀ j : Fin n, ∑ i : Fin m, |A i j| ≤ c) (hc : 0 ≤ c) :
    oneNormRect A ≤ c := by
  unfold oneNormRect
  apply infNormRect_le_of_row_sum_le
  · intro j
    exact hcols j
  · exact hc

-- ============================================================
-- Diagonal matrix infrastructure
-- ============================================================

/-- Diagonal matrix from a vector. -/
noncomputable def diagMatrix {n : ℕ} (d : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then d i else 0

/-- Right multiplication by a diagonal matrix: (A · diag(d))_ij = A_ij · d_j. -/
lemma matMul_diagMatrix_right {n : ℕ} (A : Fin n → Fin n → ℝ) (d : Fin n → ℝ) :
    ∀ i j, matMul n (A) (diagMatrix d) i j = A i j * d j := by
  intro i j
  simp only [matMul, diagMatrix]
  rw [show (∑ k : Fin n, A i k * (if k = j then d k else 0)) = A i j * d j from by
    conv_lhs =>
      arg 2; ext k
      rw [show A i k * (if k = j then d k else 0) =
          if k = j then A i k * d k else 0 from by split_ifs <;> simp]
    simp [Finset.sum_ite_eq']]

/-- Left multiplication by a diagonal matrix: (diag(d) · A)_ij = d_i · A_ij. -/
lemma matMul_diagMatrix_left {n : ℕ} (d : Fin n → ℝ) (A : Fin n → Fin n → ℝ) :
    ∀ i j, matMul n (diagMatrix d) A i j = d i * A i j := by
  intro i j
  simp only [matMul, diagMatrix]
  rw [show (∑ k : Fin n, (if i = k then d i else 0) * A k j) = d i * A i j from by
    conv_lhs =>
      arg 2; ext k
      rw [show (if i = k then d i else 0) * A k j =
          if i = k then d i * A k j else 0 from by split_ifs <;> simp]
    simp [Finset.sum_ite_eq]]

-- ============================================================
-- Absolute value of sums (sign propagation)
-- ============================================================

/-- Absolute value of sum equals sum of absolute values for nonneg terms. -/
theorem abs_sum_eq_sum_abs_of_nonneg_terms {n : ℕ}
    (f : Fin n → ℝ) (hf : ∀ k : Fin n, 0 ≤ f k) :
    |∑ k : Fin n, f k| = ∑ k : Fin n, |f k| := by
  rw [abs_of_nonneg (Finset.sum_nonneg (fun k _ => hf k))]
  apply Finset.sum_congr rfl; intro k _; rw [abs_of_nonneg (hf k)]

/-- Variant for nonpositive terms. -/
theorem abs_sum_eq_sum_abs_of_nonpos_terms {n : ℕ}
    (f : Fin n → ℝ) (hf : ∀ k : Fin n, f k ≤ 0) :
    |∑ k : Fin n, f k| = ∑ k : Fin n, |f k| := by
  rw [abs_of_nonpos (Finset.sum_nonpos (fun k _ => hf k)),
    show -(∑ k : Fin n, f k) = ∑ k : Fin n, -f k from by
      rw [Finset.sum_neg_distrib]]
  apply Finset.sum_congr rfl; intro k _; rw [abs_of_nonpos (hf k)]

-- ============================================================
-- L⁻¹ = U · A⁻¹ for LU factorizations
-- ============================================================

/-- **L⁻¹ = U · A⁻¹** when A = LU. From L⁻¹A = L⁻¹(LU) = (L⁻¹L)U = U,
    right-multiplying by A⁻¹ gives L⁻¹ = UA⁻¹. -/
lemma L_inv_eq_matMul_U_Ainv (n : ℕ)
    (A L U A_inv L_inv : Fin n → Fin n → ℝ)
    (hLU : ∀ i j, ∑ k : Fin n, L i k * U k j = A i j)
    (hLInv : IsLeftInverse n L L_inv)
    (hAInv : IsRightInverse n A A_inv) :
    ∀ k j, L_inv k j = ∑ l : Fin n, U k l * A_inv l j := by
  -- First: L⁻¹ · A = U
  have hLA : ∀ k' j', ∑ m : Fin n, L_inv k' m * A m j' = U k' j' := by
    intro k' j'
    calc ∑ m : Fin n, L_inv k' m * A m j'
        = ∑ m : Fin n, L_inv k' m * (∑ p : Fin n, L m p * U p j') := by
          apply Finset.sum_congr rfl; intro m _; rw [hLU]
      _ = ∑ p : Fin n, (∑ m : Fin n, L_inv k' m * L m p) * U p j' := by
          simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro m _; ring
      _ = ∑ p : Fin n, (if k' = p then 1 else 0) * U p j' := by
          apply Finset.sum_congr rfl; intro p _; rw [hLInv k' p]
      _ = U k' j' := by simp
  -- Derive: L⁻¹ = U · A⁻¹
  intro k j
  calc L_inv k j
      = ∑ m : Fin n, L_inv k m * (if m = j then 1 else 0) := by simp
    _ = ∑ m : Fin n, L_inv k m * (∑ l : Fin n, A m l * A_inv l j) := by
        apply Finset.sum_congr rfl; intro m _; rw [hAInv]
    _ = ∑ l : Fin n, (∑ m : Fin n, L_inv k m * A m l) * A_inv l j := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro l _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro m _; ring
    _ = ∑ l : Fin n, U k l * A_inv l j := by
        apply Finset.sum_congr rfl; intro l _; rw [hLA]

-- ============================================================
-- Matrix transpose
-- ============================================================

/-- **Matrix transpose**: (Aᵀ)_{ij} = A_{ji}. -/
noncomputable def matTranspose {n : ℕ} (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => A j i

/-- Transpose of transpose is the original. -/
theorem matTranspose_involutive {n : ℕ} (A : Fin n → Fin n → ℝ) :
    matTranspose (matTranspose A) = A := by
  ext i j; rfl

/-- Transpose distributes over multiplication: (AB)ᵀ = BᵀAᵀ. -/
theorem matTranspose_matMul {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    matTranspose (matMul n A B) = matMul n (matTranspose B) (matTranspose A) := by
  ext i j; unfold matTranspose matMul
  apply Finset.sum_congr rfl; intro k _; ring

/-- Transpose of identity is identity. -/
theorem matTranspose_id {n : ℕ} : matTranspose (idMatrix n) = idMatrix n := by
  ext i j; unfold matTranspose idMatrix
  simp [eq_comm]

-- ============================================================
-- Frobenius norm (squared and unsquared)
-- ============================================================

/-- **Squared Frobenius norm**: ‖A‖²_F = ∑_{ij} A_{ij}². -/
noncomputable def frobNormSq {m n : ℕ} (A : RMatFn m n) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2

/-- **Frobenius norm** as a Mathlib-backed compatibility wrapper for the
    library's function-shaped matrices.  The source of truth is Mathlib's
    Frobenius norm on `Matrix`, not a separate local norm definition. -/
noncomputable abbrev frobNorm {m n : ℕ} (A : RMatFn m n) : ℝ :=
  ‖(Matrix.of A : RMat m n)‖

/-- Squared Frobenius norm is nonneg. -/
lemma frobNormSq_nonneg {m n : ℕ} (A : RMatFn m n) :
    0 ≤ frobNormSq A := by
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact sq_nonneg _

/-- Mathlib's Frobenius norm agrees with the local squared-norm convenience. -/
lemma frobNorm_eq_sqrt_frobNormSq {m n : ℕ} (A : RMatFn m n) :
    frobNorm A = Real.sqrt (frobNormSq A) := by
  unfold frobNorm frobNormSq
  rw [Matrix.frobenius_norm_def]
  simp [Matrix.of_apply, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]

/-- Frobenius norm is nonneg. -/
lemma frobNorm_nonneg {m n : ℕ} (A : RMatFn m n) :
    0 ≤ frobNorm A := by
  exact norm_nonneg _

/-- Frobenius norm of a nonnegative constant `n × n` matrix. -/
theorem frobNorm_const {n : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    frobNorm (fun _i _j : Fin n => c) = (n : ℝ) * c := by
  rw [frobNorm_eq_sqrt_frobNormSq]
  unfold frobNormSq
  rw [Finset.sum_const, Finset.sum_const]
  simp
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hc]
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  rw [← mul_assoc, Real.mul_self_sqrt hn]

/-- ‖A‖²_F = ‖A‖_F². -/
lemma frobNorm_sq {m n : ℕ} (A : RMatFn m n) :
    frobNorm A ^ 2 = frobNormSq A := by
  rw [frobNorm_eq_sqrt_frobNormSq]
  rw [sq, Real.mul_self_sqrt (frobNormSq_nonneg A)]

/-- Every entry is bounded in absolute value by the Frobenius norm. -/
theorem abs_entry_le_frobNorm {m n : ℕ} (A : RMatFn m n)
    (i : Fin m) (j : Fin n) :
    |A i j| ≤ frobNorm A := by
  have hrow : A i j ^ 2 ≤ ∑ k : Fin n, A i k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j)
  have htotal :
      (∑ k : Fin n, A i k ^ 2) ≤
        ∑ r : Fin m, ∑ k : Fin n, A r k ^ 2 :=
    Finset.single_le_sum
      (fun r _ => Finset.sum_nonneg (fun k _ => sq_nonneg (A r k)))
      (Finset.mem_univ i)
  have hsq : |A i j| ^ 2 ≤ frobNorm A ^ 2 := by
    rw [frobNorm_sq]
    simpa [frobNormSq, sq_abs] using le_trans hrow htotal
  have habs := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg (abs_nonneg _), abs_of_nonneg (frobNorm_nonneg A)]
    using habs

/-- Frobenius norm monotonicity from entrywise absolute-value domination. -/
theorem frobNorm_le_of_entry_abs_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (h : ∀ i j, |A i j| ≤ B i j) :
    frobNorm A ≤ frobNorm B := by
  rw [frobNorm_eq_sqrt_frobNormSq A, frobNorm_eq_sqrt_frobNormSq B]
  apply Real.sqrt_le_sqrt
  unfold frobNormSq
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have habs : |A i j| ≤ |B i j| := by
    simpa [abs_of_nonneg (hB_nonneg i j)] using h i j
  exact (sq_le_sq).mpr habs

/-- ‖A‖_F = 0 iff A = 0. -/
theorem frobNorm_eq_zero_iff {m n : ℕ} (A : RMatFn m n) :
    frobNorm A = 0 ↔ ∀ i j, A i j = 0 := by
  rw [frobNorm_eq_sqrt_frobNormSq]
  rw [Real.sqrt_eq_zero (frobNormSq_nonneg A)]
  unfold frobNormSq
  constructor
  · intro h
    have h1 : ∀ i ∈ Finset.univ, ∑ j : Fin n, A i j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))).mp h
    intro i j
    have h2 : A i j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A i j))).mp
        (h1 i (Finset.mem_univ i)) j (Finset.mem_univ j)
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h2
  · intro h
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    rw [h i j]; ring

/-- Frobenius norm is invariant under transpose: ‖Aᵀ‖_F = ‖A‖_F. -/
theorem frobNormSq_transpose {n : ℕ} (A : Fin n → Fin n → ℝ) :
    frobNormSq (matTranspose A) = frobNormSq A := by
  unfold frobNormSq matTranspose
  rw [Finset.sum_comm]

/-- Frobenius norm is invariant under transpose. -/
theorem frobNorm_transpose {n : ℕ} (A : Fin n → Fin n → ℝ) :
    frobNorm (matTranspose A) = frobNorm A := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNorm_eq_sqrt_frobNormSq, frobNormSq_transpose]

/-- **Frobenius submultiplicativity** (squared form):
    ‖AB‖²_F ≤ ‖A‖²_F · ‖B‖²_F.

    Proof uses Cauchy-Schwarz for finite sums. -/
theorem frobNormSq_matMul_le {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    frobNormSq (matMul n A B) ≤ frobNormSq A * frobNormSq B := by
  unfold frobNormSq matMul
  -- By Cauchy-Schwarz: (∑_k A_ik B_kj)² ≤ (∑_k A_ik²)(∑_k B_kj²)
  -- Then sum over i,j and factor.
  calc ∑ i : Fin n, ∑ j : Fin n, (∑ k : Fin n, A i k * B k j) ^ 2
      ≤ ∑ i : Fin n, ∑ j : Fin n,
          (∑ k : Fin n, A i k ^ 2) * (∑ k : Fin n, B k j ^ 2) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => A i k) (fun k => B k j)
    _ = (∑ i : Fin n, ∑ k : Fin n, A i k ^ 2) *
        (∑ k : Fin n, ∑ j : Fin n, B k j ^ 2) := by
        have key : ∀ i : Fin n,
            ∑ j : Fin n, (∑ k : Fin n, A i k ^ 2) * (∑ k : Fin n, B k j ^ 2) =
            (∑ k : Fin n, A i k ^ 2) * ∑ j : Fin n, ∑ k : Fin n, B k j ^ 2 := by
          intro i; rw [Finset.mul_sum]
        simp_rw [key, ← Finset.sum_mul, Finset.sum_comm (f := fun k j => B k j ^ 2)]

/-- **Frobenius submultiplicativity** (unsquared form):
    ‖AB‖_F ≤ ‖A‖_F · ‖B‖_F. -/
theorem frobNorm_matMul_le {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    frobNorm (matMul n A B) ≤ frobNorm A * frobNorm B := by
  unfold matMul
  simpa [Matrix.mul_apply] using
    (Matrix.frobenius_norm_mul (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
      (Matrix.of B : Matrix (Fin n) (Fin n) ℝ))

/-- **Cauchy-Schwarz for Frobenius inner product**:
    (∑_ij A_ij B_ij)² ≤ ‖A‖²_F · ‖B‖²_F.

    Proved by applying `Finset.sum_mul_sq_le_sq_mul_sq` to the
    flattened sum over Fin n × Fin n. -/
theorem frobInnerProduct_sq_le {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, A i j * B i j) ^ 2 ≤
    frobNormSq A * frobNormSq B := by
  unfold frobNormSq
  -- Flatten: use Cauchy-Schwarz on Fin n × Fin n
  have cs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ ×ˢ (Finset.univ : Finset (Fin n)))
    (fun p : Fin n × Fin n => A p.1 p.2)
    (fun p : Fin n × Fin n => B p.1 p.2)
  -- Convert ∑ p ∈ univ ×ˢ univ to ∑ i, ∑ j via Fintype.sum_prod_type'
  simp only [Finset.univ_product_univ] at cs
  rw [Fintype.sum_prod_type' (fun i j => A i j * B i j),
      Fintype.sum_prod_type' (fun i j => A i j ^ 2),
      Fintype.sum_prod_type' (fun i j => B i j ^ 2)] at cs
  exact cs

/-- **Frobenius inner product bound**: ∑_ij A_ij B_ij ≤ ‖A‖_F · ‖B‖_F.
    Follows from Cauchy-Schwarz and ‖·‖_F = √(‖·‖²_F). -/
theorem frobInnerProduct_le {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, A i j * B i j ≤
      frobNorm A * frobNorm B := by
  -- From CS: (∑ AB)² ≤ ‖A‖²_F ‖B‖²_F = (‖A‖_F ‖B‖_F)²
  have hcs := frobInnerProduct_sq_le A B
  have hnn : 0 ≤ frobNorm A * frobNorm B :=
    mul_nonneg (frobNorm_nonneg A) (frobNorm_nonneg B)
  -- (∑ AB)² ≤ (‖A‖_F ‖B‖_F)² and ‖A‖_F ‖B‖_F ≥ 0 → ∑ AB ≤ ‖A‖_F ‖B‖_F
  rw [show frobNormSq A * frobNormSq B =
      (frobNorm A * frobNorm B) ^ 2 from by
    rw [show (frobNorm A * frobNorm B) ^ 2 =
          frobNorm A ^ 2 * frobNorm B ^ 2 from by ring,
        frobNorm_sq, frobNorm_sq]] at hcs
  nlinarith [sq_abs (∑ i : Fin n, ∑ j : Fin n, A i j * B i j)]

/-- **Frobenius triangle inequality** (squared form):
    ‖A + B‖²_F ≤ (‖A‖_F + ‖B‖_F)². -/
theorem frobNormSq_add_le {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    frobNormSq (fun i j => A i j + B i j) ≤
    (frobNorm A + frobNorm B) ^ 2 := by
  -- ‖A+B‖²_F = ‖A‖²_F + 2⟨A,B⟩ + ‖B‖²_F
  -- ≤ ‖A‖²_F + 2‖A‖_F‖B‖_F + ‖B‖²_F = (‖A‖_F + ‖B‖_F)²
  have hexp : frobNormSq (fun i j => A i j + B i j) =
      frobNormSq A + 2 * (∑ i : Fin n, ∑ j : Fin n, A i j * B i j) +
      frobNormSq B := by
    unfold frobNormSq
    simp_rw [show ∀ i j : Fin n, (A i j + B i j) ^ 2 =
        A i j ^ 2 + 2 * (A i j * B i j) + B i j ^ 2 from fun i j => by ring,
      Finset.sum_add_distrib]
    rw [show ∑ x : Fin n, ∑ x_1 : Fin n, 2 * (A x x_1 * B x x_1) =
        2 * ∑ x : Fin n, ∑ x_1 : Fin n, A x x_1 * B x x_1 from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]]
  rw [hexp, show (frobNorm A + frobNorm B) ^ 2 =
      frobNorm A ^ 2 + 2 * (frobNorm A * frobNorm B) + frobNorm B ^ 2 from by ring,
    frobNorm_sq, frobNorm_sq]
  linarith [frobInnerProduct_le A B]

/-- **Frobenius triangle inequality**: ‖A + B‖_F ≤ ‖A‖_F + ‖B‖_F. -/
theorem frobNorm_add_le {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    frobNorm (fun i j => A i j + B i j) ≤ frobNorm A + frobNorm B := by
  simpa using
    (norm_add_le (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
      (Matrix.of B : Matrix (Fin n) (Fin n) ℝ))

/-- Frobenius norm is invariant under negation: ‖-A‖²_F = ‖A‖²_F. -/
theorem frobNormSq_neg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    frobNormSq (fun i j => -A i j) = frobNormSq A := by
  unfold frobNormSq; congr 1; ext i; congr 1; ext j; ring

/-- Frobenius norm is invariant under negation: ‖-A‖_F = ‖A‖_F. -/
theorem frobNorm_neg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    frobNorm (fun i j => -A i j) = frobNorm A := by
  simpa using norm_neg (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)

/-- **Frobenius triangle inequality for subtraction**: ‖A - B‖_F ≤ ‖A‖_F + ‖B‖_F. -/
theorem frobNorm_sub_le {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    frobNorm (fun i j => A i j - B i j) ≤ frobNorm A + frobNorm B := by
  simpa [sub_eq_add_neg] using
    (norm_sub_le (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
      (Matrix.of B : Matrix (Fin n) (Fin n) ℝ))

-- ============================================================
-- Rectangular Frobenius norm infrastructure
-- ============================================================

/-- Permute a finite vector by an equivalence of its index type. -/
def vecPermute {n : ℕ} (σ : Fin n ≃ Fin n) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => x (σ i)

/-- Permute the rows of a rectangular matrix. -/
def rectPermuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => A (σ i) j

/-- Permute the columns of a rectangular matrix. -/
def rectPermuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => A i (π j)

/-- **Squared Frobenius norm for rectangular matrices**:
    ‖A‖²_F = ∑ᵢ∑ⱼ Aᵢⱼ² for A ∈ ℝ^{m×n}.

    The original `frobNormSq` is square-matrix specialized because much of
    the library's linear-system infrastructure is square. RandNLA sampling
    algorithms naturally act on rectangular data matrices, so we expose this
    rectangular variant for their probability weights and scaling factors. -/
noncomputable def frobNormSqRect {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2

/-- Squared rectangular Frobenius norm is nonnegative. -/
lemma frobNormSqRect_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    0 ≤ frobNormSqRect A := by
  unfold frobNormSqRect
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact sq_nonneg _

/-- For square matrices, the rectangular squared Frobenius norm agrees with
    the existing square-matrix definition. -/
theorem frobNormSqRect_eq_frobNormSq {n : ℕ} (A : Fin n → Fin n → ℝ) :
    frobNormSqRect A = frobNormSq A := rfl

/-- A rectangular matrix has zero squared Frobenius norm iff all entries are
    zero. -/
theorem frobNormSqRect_eq_zero_iff {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    frobNormSqRect A = 0 ↔ ∀ i j, A i j = 0 := by
  unfold frobNormSqRect
  constructor
  · intro h
    have hrow : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        ∑ j : Fin n, A i j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))).mp h
    intro i j
    have hterm : A i j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A i j))).mp
        (hrow i (Finset.mem_univ i)) j (Finset.mem_univ j)
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hterm
  · intro h
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    rw [h i j]; ring

/-- If one entry is nonzero, then the rectangular squared Frobenius norm is
    nonzero. -/
lemma frobNormSqRect_ne_zero_of_entry_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hAij : A i j ≠ 0) :
    frobNormSqRect A ≠ 0 := by
  intro hzero
  exact hAij ((frobNormSqRect_eq_zero_iff A).mp hzero i j)

/-- If one entry is nonzero, then the rectangular squared Frobenius norm is
    positive. -/
lemma frobNormSqRect_pos_of_entry_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hAij : A i j ≠ 0) :
    0 < frobNormSqRect A :=
  lt_of_le_of_ne (frobNormSqRect_nonneg A)
    (Ne.symm (frobNormSqRect_ne_zero_of_entry_ne_zero A i j hAij))

/-- Rectangular Frobenius norm:
    `‖A‖_F = sqrt (∑ᵢ∑ⱼ Aᵢⱼ²)` for `A : ℝ^{m×n}`. -/
noncomputable def frobNormRect {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ :=
  Real.sqrt (frobNormSqRect A)

/-- Rectangular Frobenius norm is nonnegative. -/
lemma frobNormRect_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    0 ≤ frobNormRect A :=
  Real.sqrt_nonneg _

/-- Row permutations preserve the squared rectangular Frobenius norm. -/
theorem frobNormSqRect_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) :
    frobNormSqRect (rectPermuteRows σ A) = frobNormSqRect A := by
  unfold frobNormSqRect rectPermuteRows
  exact
    Fintype.sum_equiv σ
      (fun i : Fin m => ∑ j : Fin n, A (σ i) j ^ 2)
      (fun i : Fin m => ∑ j : Fin n, A i j ^ 2)
      (fun _ => rfl)

/-- Column permutations preserve the squared rectangular Frobenius norm. -/
theorem frobNormSqRect_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) :
    frobNormSqRect (rectPermuteCols π A) = frobNormSqRect A := by
  unfold frobNormSqRect rectPermuteCols
  congr 1
  ext i
  exact
    Fintype.sum_equiv π
      (fun j : Fin n => A i (π j) ^ 2)
      (fun j : Fin n => A i j ^ 2)
      (fun _ => rfl)

/-- Row permutations preserve the rectangular Frobenius norm. -/
theorem frobNormRect_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) :
    frobNormRect (rectPermuteRows σ A) = frobNormRect A := by
  unfold frobNormRect
  rw [frobNormSqRect_permuteRows σ A]

/-- Column permutations preserve the rectangular Frobenius norm. -/
theorem frobNormRect_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) :
    frobNormRect (rectPermuteCols π A) = frobNormRect A := by
  unfold frobNormRect
  rw [frobNormSqRect_permuteCols π A]

/-- `‖A‖_F² = ∑ᵢ∑ⱼ Aᵢⱼ²` for rectangular matrices. -/
lemma frobNormRect_sq {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    frobNormRect A ^ 2 = frobNormSqRect A := by
  unfold frobNormRect
  rw [sq, Real.mul_self_sqrt (frobNormSqRect_nonneg A)]

/-- Every rectangular entry is bounded in absolute value by the rectangular
    Frobenius norm. -/
theorem abs_entry_le_frobNormRect {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    |A i j| ≤ frobNormRect A := by
  have hrow : A i j ^ 2 ≤ ∑ k : Fin n, A i k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j)
  have htotal :
      (∑ k : Fin n, A i k ^ 2) ≤
        ∑ r : Fin m, ∑ k : Fin n, A r k ^ 2 :=
    Finset.single_le_sum
      (fun r _ => Finset.sum_nonneg (fun k _ => sq_nonneg (A r k)))
      (Finset.mem_univ i)
  have hsq : |A i j| ^ 2 ≤ frobNormRect A ^ 2 := by
    rw [frobNormRect_sq]
    simpa [frobNormSqRect, sq_abs] using le_trans hrow htotal
  have habs := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg (abs_nonneg _),
    abs_of_nonneg (frobNormRect_nonneg A)] using habs

/-- For square matrices, the rectangular Frobenius norm agrees with the
    existing square-matrix definition. -/
theorem frobNormRect_eq_frobNorm {n : ℕ} (A : Fin n → Fin n → ℝ) :
    frobNormRect A = frobNorm A := by
  unfold frobNormRect
  rw [frobNorm_eq_sqrt_frobNormSq, frobNormSqRect_eq_frobNormSq]

/-- The rectangular Frobenius wrapper agrees with the repository's
    Mathlib-backed Frobenius norm wrapper for every rectangular shape. -/
theorem frobNormRect_eq_frobNormFn {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    frobNormRect A = frobNorm A := by
  unfold frobNormRect
  rw [frobNorm_eq_sqrt_frobNormSq]
  rfl

/-- Rectangular Frobenius monotonicity from entrywise absolute-value
    domination. -/
theorem frobNormRect_le_of_entry_abs_le {m n : ℕ}
    (A B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (h : ∀ i j, |A i j| ≤ B i j) :
    frobNormRect A ≤ frobNormRect B := by
  unfold frobNormRect
  apply Real.sqrt_le_sqrt
  unfold frobNormSqRect
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have habs : |A i j| ≤ |B i j| := by
    simpa [abs_of_nonneg (hB_nonneg i j)] using h i j
  exact (sq_le_sq).mpr habs

/-- Rectangular Frobenius norm bound from a uniform entrywise absolute-value
budget. -/
theorem frobNormRect_le_sqrt_mul_nat_of_entry_abs_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hentry : ∀ i j, |A i j| ≤ B) :
    frobNormRect A ≤ Real.sqrt ((m : ℝ) * (n : ℝ)) * B := by
  have hsq :
      frobNormSqRect A ≤ (m : ℝ) * (n : ℝ) * B ^ 2 := by
    unfold frobNormSqRect
    calc
      (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)
          = ∑ i : Fin m, ∑ j : Fin n, |A i j| ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              exact (sq_abs (A i j)).symm
      _ ≤ ∑ _i : Fin m, ∑ _j : Fin n, B ^ 2 := by
              apply Finset.sum_le_sum
              intro i _
              apply Finset.sum_le_sum
              intro j _
              nlinarith [abs_nonneg (A i j), hentry i j, hB]
      _ = (m : ℝ) * (n : ℝ) * B ^ 2 := by
              simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
              ring
  have hmn : 0 ≤ (m : ℝ) * (n : ℝ) :=
    mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
  calc
    frobNormRect A
        = Real.sqrt (frobNormSqRect A) := rfl
    _ ≤ Real.sqrt ((m : ℝ) * (n : ℝ) * B ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt ((m : ℝ) * (n : ℝ)) * B := by
        rw [show (m : ℝ) * (n : ℝ) * B ^ 2 =
            ((m : ℝ) * (n : ℝ)) * B ^ 2 by ring]
        rw [Real.sqrt_mul hmn (B ^ 2), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hB]

/-- Squared rectangular Frobenius norm is homogeneous under scalar
    multiplication. -/
lemma frobNormSqRect_smul {m n : ℕ} (a : ℝ)
    (A : Fin m → Fin n → ℝ) :
    frobNormSqRect (fun i j => a * A i j) =
      a ^ 2 * frobNormSqRect A := by
  unfold frobNormSqRect
  simp_rw [show ∀ i : Fin m, ∀ j : Fin n,
      (a * A i j) ^ 2 = a ^ 2 * A i j ^ 2 from fun i j => by ring]
  calc
    (∑ i : Fin m, ∑ j : Fin n, a ^ 2 * A i j ^ 2)
        = ∑ i : Fin m, a ^ 2 * ∑ j : Fin n, A i j ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = a ^ 2 * ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by
            rw [Finset.mul_sum]

/-- Rectangular Frobenius norm is homogeneous under scalar multiplication. -/
lemma frobNormRect_smul {m n : ℕ} (a : ℝ)
    (A : Fin m → Fin n → ℝ) :
    frobNormRect (fun i j => a * A i j) =
      |a| * frobNormRect A := by
  unfold frobNormRect
  rw [frobNormSqRect_smul]
  rw [Real.sqrt_mul (sq_nonneg a)]
  rw [Real.sqrt_sq_eq_abs]

/-- Taking componentwise absolute values preserves the squared rectangular
    Frobenius norm. -/
lemma frobNormSqRect_abs {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    frobNormSqRect (fun i j => |A i j|) = frobNormSqRect A := by
  unfold frobNormSqRect
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact sq_abs (A i j)

/-- Taking componentwise absolute values preserves the rectangular Frobenius
    norm. -/
lemma frobNormRect_abs {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    frobNormRect (fun i j => |A i j|) = frobNormRect A := by
  unfold frobNormRect
  rw [frobNormSqRect_abs]

/-- Rectangular Frobenius inner product Cauchy--Schwarz inequality. -/
theorem frobInnerProductRect_sq_le {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) :
    (∑ i : Fin m, ∑ j : Fin n, A i j * B i j) ^ 2 ≤
      frobNormSqRect A * frobNormSqRect B := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ ×ˢ (Finset.univ : Finset (Fin n)))
    (fun p : Fin m × Fin n => A p.1 p.2)
    (fun p : Fin m × Fin n => B p.1 p.2)
  simp only [Finset.univ_product_univ] at cs
  rw [Fintype.sum_prod_type' (fun i j => A i j * B i j),
      Fintype.sum_prod_type' (fun i j => A i j ^ 2),
      Fintype.sum_prod_type' (fun i j => B i j ^ 2)] at cs
  exact cs

/-- Rectangular Frobenius inner product is bounded by the product of
    rectangular Frobenius norms. -/
theorem frobInnerProductRect_le {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) :
    ∑ i : Fin m, ∑ j : Fin n, A i j * B i j ≤
      frobNormRect A * frobNormRect B := by
  have hcs := frobInnerProductRect_sq_le A B
  have hnn : 0 ≤ frobNormRect A * frobNormRect B :=
    mul_nonneg (frobNormRect_nonneg A) (frobNormRect_nonneg B)
  rw [show frobNormSqRect A * frobNormSqRect B =
      (frobNormRect A * frobNormRect B) ^ 2 from by
    rw [show (frobNormRect A * frobNormRect B) ^ 2 =
        frobNormRect A ^ 2 * frobNormRect B ^ 2 from by ring,
      frobNormRect_sq, frobNormRect_sq]] at hcs
  nlinarith [sq_abs (∑ i : Fin m, ∑ j : Fin n, A i j * B i j)]

/-- Squared rectangular Frobenius triangle inequality. -/
theorem frobNormSqRect_add_le {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) :
    frobNormSqRect (fun i j => A i j + B i j) ≤
      (frobNormRect A + frobNormRect B) ^ 2 := by
  have hexp : frobNormSqRect (fun i j => A i j + B i j) =
      frobNormSqRect A +
        2 * (∑ i : Fin m, ∑ j : Fin n, A i j * B i j) +
      frobNormSqRect B := by
    unfold frobNormSqRect
    simp_rw [show ∀ i : Fin m, ∀ j : Fin n, (A i j + B i j) ^ 2 =
        A i j ^ 2 + 2 * (A i j * B i j) + B i j ^ 2 from fun i j => by ring,
      Finset.sum_add_distrib]
    rw [show ∑ x : Fin m, ∑ x_1 : Fin n, 2 * (A x x_1 * B x x_1) =
        2 * ∑ x : Fin m, ∑ x_1 : Fin n, A x x_1 * B x x_1 from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]]
  rw [hexp, show (frobNormRect A + frobNormRect B) ^ 2 =
      frobNormRect A ^ 2 + 2 * (frobNormRect A * frobNormRect B) +
        frobNormRect B ^ 2 from by ring,
    frobNormRect_sq, frobNormRect_sq]
  linarith [frobInnerProductRect_le A B]

/-- Rectangular Frobenius triangle inequality. -/
theorem frobNormRect_add_le {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) :
    frobNormRect (fun i j => A i j + B i j) ≤
      frobNormRect A + frobNormRect B := by
  have hnn : 0 ≤ frobNormRect A + frobNormRect B :=
    add_nonneg (frobNormRect_nonneg A) (frobNormRect_nonneg B)
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt (frobNormSqRect_add_le A B)

/-- Negating every entry preserves the rectangular Frobenius norm. -/
lemma frobNormRect_neg {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    frobNormRect (fun i j => -A i j) = frobNormRect A := by
  simpa using (frobNormRect_smul (-1) A)

/-- Rectangular Frobenius triangle inequality for subtraction. -/
theorem frobNormRect_sub_le {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) :
    frobNormRect (fun i j => A i j - B i j) ≤
      frobNormRect A + frobNormRect B := by
  simpa [sub_eq_add_neg, frobNormRect_neg] using
    (frobNormRect_add_le A (fun i j => -B i j))

/-- Squared rectangular Frobenius norm of a matrix with a single nonzero
    entry, written with the fixed index on the left of the equality tests. -/
theorem frobNormSqRect_single_left {m n : ℕ}
    (i : Fin m) (j : Fin n) (x : ℝ) :
    frobNormSqRect (fun r c => if i = r ∧ j = c then x else 0) = x ^ 2 := by
  classical
  unfold frobNormSqRect
  rw [Finset.sum_eq_single i]
  · simp
  · intro r _ hr
    have hne : i ≠ r := by
      intro hir
      exact hr hir.symm
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ i))

/-- Rectangular Frobenius norm of a matrix with a single nonzero entry,
    written with the fixed index on the left of the equality tests. -/
theorem frobNormRect_single_left {m n : ℕ}
    (i : Fin m) (j : Fin n) (x : ℝ) :
    frobNormRect (fun r c => if i = r ∧ j = c then x else 0) = |x| := by
  unfold frobNormRect
  rw [frobNormSqRect_single_left, Real.sqrt_sq_eq_abs]

-- ============================================================
-- Vector 2-norm and operator-2-norm inequalities
-- ============================================================

/-- Squared Euclidean norm of a vector: `||x||₂² = ∑ᵢ xᵢ²`. -/
noncomputable def vecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, x i ^ 2

/-- Permutations preserve squared Euclidean vector norm. -/
theorem vecNorm2Sq_permute {n : ℕ} (σ : Fin n ≃ Fin n)
    (x : Fin n → ℝ) :
    vecNorm2Sq (vecPermute σ x) = vecNorm2Sq x := by
  unfold vecNorm2Sq vecPermute
  exact
    Fintype.sum_equiv σ
      (fun i : Fin n => x (σ i) ^ 2)
      (fun i : Fin n => x i ^ 2)
      (fun _ => rfl)

/-- Applying a vector permutation and then the inverse permutation gives the
    original vector. -/
theorem vecPermute_symm_vecPermute {n : ℕ} (σ : Fin n ≃ Fin n)
    (x : Fin n → ℝ) :
    vecPermute σ.symm (vecPermute σ x) = x := by
  ext i
  simp [vecPermute]

/-- Applying an inverse vector permutation and then the original permutation
    gives the original vector. -/
theorem vecPermute_vecPermute_symm {n : ℕ} (σ : Fin n ≃ Fin n)
    (x : Fin n → ℝ) :
    vecPermute σ (vecPermute σ.symm x) = x := by
  ext i
  simp [vecPermute]

/-- Euclidean norm of a vector. -/
noncomputable def vecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (vecNorm2Sq x)

/-- Squared Euclidean norm is nonnegative. -/
lemma vecNorm2Sq_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ vecNorm2Sq x := by
  unfold vecNorm2Sq
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- Euclidean norm is nonnegative. -/
lemma vecNorm2_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ vecNorm2 x :=
  Real.sqrt_nonneg _

/-- `||x||₂² = ||x||₂ ^ 2`. -/
lemma vecNorm2_sq {n : ℕ} (x : Fin n → ℝ) :
    vecNorm2 x ^ 2 = vecNorm2Sq x := by
  unfold vecNorm2
  rw [sq, Real.mul_self_sqrt (vecNorm2Sq_nonneg x)]

/-- A single row's squared Euclidean norm is bounded by the whole matrix's
    squared Frobenius norm. -/
theorem vecNorm2Sq_row_le_frobNormSq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    vecNorm2Sq (fun j : Fin n => A i j) ≤ frobNormSq A := by
  unfold vecNorm2Sq frobNormSq
  exact
    Finset.single_le_sum
      (fun r _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A r j)))
      (Finset.mem_univ i)

/-- A single row's squared Euclidean norm is bounded by the square of the
    matrix Frobenius norm. -/
theorem vecNorm2Sq_row_le_frobNorm_sq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    vecNorm2Sq (fun j : Fin n => A i j) ≤ frobNorm A ^ 2 := by
  rw [frobNorm_sq]
  exact vecNorm2Sq_row_le_frobNormSq A i

/-- A single coordinate is bounded by the vector's sum of absolute values. -/
theorem abs_coord_le_sum_abs {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ ∑ j : Fin n, |x j| :=
  Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

/-- The squared Euclidean norm is bounded by the square of the `ℓ₁` norm. -/
theorem vecNorm2Sq_le_sum_abs_sq {n : ℕ} (x : Fin n → ℝ) :
    vecNorm2Sq x ≤ (∑ i : Fin n, |x i|) ^ 2 := by
  let S : ℝ := ∑ i : Fin n, |x i|
  have hterm : ∀ i : Fin n, x i ^ 2 ≤ |x i| * S := by
    intro i
    have hxi : |x i| ≤ S := by
      simpa [S] using abs_coord_le_sum_abs x i
    calc
      x i ^ 2 = |x i| * |x i| := by
        rw [← sq_abs (x i)]
        ring
      _ ≤ |x i| * S :=
        mul_le_mul_of_nonneg_left hxi (abs_nonneg (x i))
  unfold vecNorm2Sq
  calc
    (∑ i : Fin n, x i ^ 2) ≤ ∑ i : Fin n, |x i| * S :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = S ^ 2 := by
      rw [← Finset.sum_mul]
      change S * S = S ^ 2
      ring

/-- A square matrix's Frobenius squared norm is bounded by
    `n * ||A||_∞²`. -/
theorem frobNormSq_le_nat_mul_infNorm_sq {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    frobNormSq A ≤ (n : ℝ) * infNorm A ^ 2 := by
  unfold frobNormSq
  calc
    (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) =
        ∑ i : Fin n, vecNorm2Sq (fun j : Fin n => A i j) := by
      simp [vecNorm2Sq]
    _ ≤ ∑ _i : Fin n, infNorm A ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i _
      have hrow : ∑ j : Fin n, |A i j| ≤ infNorm A :=
        row_sum_le_infNorm A i
      have hrow_nonneg : 0 ≤ ∑ j : Fin n, |A i j| :=
        Finset.sum_nonneg (fun j _ => abs_nonneg (A i j))
      have hinf_nonneg : 0 ≤ infNorm A := infNorm_nonneg A
      calc
        vecNorm2Sq (fun j : Fin n => A i j) ≤
            (∑ j : Fin n, |A i j|) ^ 2 :=
          vecNorm2Sq_le_sum_abs_sq (fun j : Fin n => A i j)
        _ ≤ infNorm A ^ 2 := by
          calc
            (∑ j : Fin n, |A i j|) ^ 2 =
                (∑ j : Fin n, |A i j|) * (∑ j : Fin n, |A i j|) := by
              ring
            _ ≤ infNorm A * infNorm A :=
              mul_le_mul hrow hrow hrow_nonneg hinf_nonneg
            _ = infNorm A ^ 2 := by
              ring
    _ = (n : ℝ) * infNorm A ^ 2 := by
      simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]

/-- A square matrix's Frobenius norm squared is bounded by
    `n * ||A||_∞²`. -/
theorem frobNorm_sq_le_nat_mul_infNorm_sq {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    frobNorm A ^ 2 ≤ (n : ℝ) * infNorm A ^ 2 := by
  rw [frobNorm_sq]
  exact frobNormSq_le_nat_mul_infNorm_sq A

/-- The zero vector has Euclidean norm zero. -/
lemma vecNorm2_zero {n : ℕ} :
    vecNorm2 (fun _i : Fin n => 0) = 0 := by
  unfold vecNorm2 vecNorm2Sq
  simp

/-- A vector has Euclidean norm zero iff all of its entries are zero. -/
lemma vecNorm2_eq_zero_iff {n : ℕ} (x : Fin n → ℝ) :
    vecNorm2 x = 0 ↔ ∀ i, x i = 0 := by
  unfold vecNorm2
  rw [Real.sqrt_eq_zero (vecNorm2Sq_nonneg x)]
  constructor
  · intro h i
    have hterms :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => x i ^ 2)
        (by intro k _; exact sq_nonneg (x k))).mp h
    exact sq_eq_zero_iff.mp (hterms i (Finset.mem_univ i))
  · intro hx
    unfold vecNorm2Sq
    simp [hx]

/-- Taking componentwise absolute values preserves the squared Euclidean norm. -/
lemma vecNorm2Sq_abs {n : ℕ} (x : Fin n → ℝ) :
    vecNorm2Sq (fun i => |x i|) = vecNorm2Sq x := by
  unfold vecNorm2Sq
  apply Finset.sum_congr rfl
  intro i _
  exact sq_abs (x i)

/-- Taking componentwise absolute values preserves the Euclidean norm. -/
lemma vecNorm2_abs {n : ℕ} (x : Fin n → ℝ) :
    vecNorm2 (fun i => |x i|) = vecNorm2 x := by
  unfold vecNorm2
  rw [vecNorm2Sq_abs]

/-- Squared rectangular Frobenius norm of an outer product. -/
theorem frobNormSqRect_outerProduct {m n : ℕ}
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    frobNormSqRect (fun i j => x i * y j) =
      vecNorm2Sq x * vecNorm2Sq y := by
  unfold frobNormSqRect vecNorm2Sq
  simp_rw [show ∀ i : Fin m, ∀ j : Fin n,
      (x i * y j) ^ 2 = x i ^ 2 * y j ^ 2 from fun i j => by ring]
  calc
    (∑ i : Fin m, ∑ j : Fin n, x i ^ 2 * y j ^ 2)
        = ∑ i : Fin m, x i ^ 2 * ∑ j : Fin n, y j ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = (∑ i : Fin m, x i ^ 2) * (∑ j : Fin n, y j ^ 2) := by
            rw [Finset.sum_mul]

/-- Rectangular Frobenius norm of an outer product. -/
theorem frobNormRect_outerProduct {m n : ℕ}
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    frobNormRect (fun i j => x i * y j) =
      vecNorm2 x * vecNorm2 y := by
  unfold frobNormRect vecNorm2
  rw [frobNormSqRect_outerProduct]
  rw [Real.sqrt_mul (vecNorm2Sq_nonneg x)]

/-- The lower-right tail block of a square matrix has no larger squared
    rectangular Frobenius norm than the full matrix. -/
theorem frobNormSqRect_tail_le {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    frobNormSqRect (fun i j : Fin n => A i.succ j.succ) ≤
      frobNormSqRect A := by
  unfold frobNormSqRect
  rw [Fin.sum_univ_succ]
  have hrow0_nonneg : 0 ≤ ∑ j : Fin (n + 1), A 0 j ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg (A 0 j))
  have htail :
      (∑ i : Fin n, ∑ j : Fin n, A i.succ j.succ ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin (n + 1), A i.succ j ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    rw [Fin.sum_univ_succ]
    linarith [sq_nonneg (A i.succ 0)]
  linarith

/-- The lower-right tail block of a square matrix has no larger rectangular
    Frobenius norm than the full matrix. -/
theorem frobNormRect_tail_le {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    frobNormRect (fun i j : Fin n => A i.succ j.succ) ≤
      frobNormRect A := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt (frobNormSqRect_tail_le A)

/-- The initial top-left block of a square matrix has no larger squared
    rectangular Frobenius norm than the full matrix. -/
theorem frobNormSqRect_init_le {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    frobNormSqRect (fun i j : Fin n => A i.castSucc j.castSucc) ≤
      frobNormSqRect A := by
  unfold frobNormSqRect
  rw [Fin.sum_univ_castSucc]
  have htop :
      (∑ i : Fin n, ∑ j : Fin n, A i.castSucc j.castSucc ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin (n + 1), A i.castSucc j ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    rw [Fin.sum_univ_castSucc]
    linarith [sq_nonneg (A i.castSucc (Fin.last n))]
  have hlast_nonneg :
      0 ≤ ∑ j : Fin (n + 1), A (Fin.last n) j ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg (A (Fin.last n) j))
  linarith

/-- The initial top-left block of a square matrix has no larger rectangular
    Frobenius norm than the full matrix. -/
theorem frobNormRect_init_le {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    frobNormRect (fun i j : Fin n => A i.castSucc j.castSucc) ≤
      frobNormRect A := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt (frobNormSqRect_init_le A)

/-- The first-column tail vector has squared Euclidean norm bounded by the
    full squared rectangular Frobenius norm. -/
theorem vecNorm2Sq_firstColumnTail_le_frobNormSqRect {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    vecNorm2Sq (fun i : Fin n => A i.succ 0) ≤ frobNormSqRect A := by
  unfold vecNorm2Sq frobNormSqRect
  rw [Fin.sum_univ_succ]
  have hrow0_nonneg : 0 ≤ ∑ j : Fin (n + 1), A 0 j ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg (A 0 j))
  have htail :
      (∑ i : Fin n, A i.succ 0 ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin (n + 1), A i.succ j ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact
      Finset.single_le_sum
        (fun j _ => sq_nonneg (A i.succ j))
        (Finset.mem_univ 0)
  linarith

/-- The first-column tail vector has Euclidean norm bounded by the full
    rectangular Frobenius norm. -/
theorem vecNorm2_firstColumnTail_le_frobNormRect {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    vecNorm2 (fun i : Fin n => A i.succ 0) ≤ frobNormRect A := by
  unfold vecNorm2 frobNormRect
  exact Real.sqrt_le_sqrt (vecNorm2Sq_firstColumnTail_le_frobNormSqRect A)

/-- The first-row tail vector has squared Euclidean norm bounded by the full
    squared rectangular Frobenius norm. -/
theorem vecNorm2Sq_firstRowTail_le_frobNormSqRect {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    vecNorm2Sq (fun j : Fin n => A 0 j.succ) ≤ frobNormSqRect A := by
  unfold vecNorm2Sq frobNormSqRect
  rw [Fin.sum_univ_succ]
  have htail_rows_nonneg :
      0 ≤ ∑ i : Fin n, ∑ j : Fin (n + 1), A i.succ j ^ 2 :=
    Finset.sum_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i.succ j)))
  have hrow :
      (∑ j : Fin n, A 0 j.succ ^ 2) ≤
        ∑ j : Fin (n + 1), A 0 j ^ 2 := by
    rw [Fin.sum_univ_succ]
    linarith [sq_nonneg (A 0 0)]
  linarith

/-- The first-row tail vector has Euclidean norm bounded by the full
    rectangular Frobenius norm. -/
theorem vecNorm2_firstRowTail_le_frobNormRect {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    vecNorm2 (fun j : Fin n => A 0 j.succ) ≤ frobNormRect A := by
  unfold vecNorm2 frobNormRect
  exact Real.sqrt_le_sqrt (vecNorm2Sq_firstRowTail_le_frobNormSqRect A)

/-- The last-row initial vector has squared Euclidean norm bounded by the full
    squared rectangular Frobenius norm. -/
theorem vecNorm2Sq_lastRowInit_le_frobNormSqRect {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    vecNorm2Sq (fun j : Fin n => A (Fin.last n) j.castSucc) ≤
      frobNormSqRect A := by
  unfold vecNorm2Sq frobNormSqRect
  have hinit :
      (∑ j : Fin n, A (Fin.last n) j.castSucc ^ 2) ≤
        ∑ j : Fin (n + 1), A (Fin.last n) j ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    linarith [sq_nonneg (A (Fin.last n) (Fin.last n))]
  have hrow :
      (∑ j : Fin (n + 1), A (Fin.last n) j ^ 2) ≤
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), A i j ^ 2 :=
    Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))
      (Finset.mem_univ (Fin.last n))
  exact le_trans hinit hrow

/-- The last-row initial vector has Euclidean norm bounded by the full
    rectangular Frobenius norm. -/
theorem vecNorm2_lastRowInit_le_frobNormRect {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    vecNorm2 (fun j : Fin n => A (Fin.last n) j.castSucc) ≤
      frobNormRect A := by
  unfold vecNorm2 frobNormRect
  exact Real.sqrt_le_sqrt (vecNorm2Sq_lastRowInit_le_frobNormSqRect A)

/-- The last-column initial vector has squared Euclidean norm bounded by the
    full squared rectangular Frobenius norm. -/
theorem vecNorm2Sq_lastColumnInit_le_frobNormSqRect {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    vecNorm2Sq (fun i : Fin n => A i.castSucc (Fin.last n)) ≤
      frobNormSqRect A := by
  unfold vecNorm2Sq frobNormSqRect
  have hinit :
      (∑ i : Fin n, A i.castSucc (Fin.last n) ^ 2) ≤
        ∑ i : Fin (n + 1), A i (Fin.last n) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    linarith [sq_nonneg (A (Fin.last n) (Fin.last n))]
  have hcol :
      (∑ i : Fin (n + 1), A i (Fin.last n) ^ 2) ≤
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), A i j ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact
      Finset.single_le_sum
        (fun j _ => sq_nonneg (A i j))
        (Finset.mem_univ (Fin.last n))
  exact le_trans hinit hcol

/-- The last-column initial vector has Euclidean norm bounded by the full
    rectangular Frobenius norm. -/
theorem vecNorm2_lastColumnInit_le_frobNormRect {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    vecNorm2 (fun i : Fin n => A i.castSucc (Fin.last n)) ≤
      frobNormRect A := by
  unfold vecNorm2 frobNormRect
  exact Real.sqrt_le_sqrt (vecNorm2Sq_lastColumnInit_le_frobNormSqRect A)

/-- Exact squared Frobenius block split when the first column below the
    leading entry is zero. -/
theorem frobNormSqRect_block_firstColumnTail_zero {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hcol : ∀ i : Fin n, A i.succ 0 = 0) :
    frobNormSqRect A =
      A 0 0 ^ 2 + vecNorm2Sq (fun j : Fin n => A 0 j.succ) +
        frobNormSqRect (fun i j : Fin n => A i.succ j.succ) := by
  unfold frobNormSqRect vecNorm2Sq
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  have htail :
      (∑ i : Fin n, ∑ j : Fin (n + 1), A i.succ j ^ 2) =
        ∑ i : Fin n, ∑ j : Fin n, A i.succ j.succ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_succ]
    simp [hcol i]
  rw [htail]

/-- Frobenius block triangle estimate when the first column below the leading
    entry is zero. -/
theorem frobNormRect_block_firstColumnTail_zero_le {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hcol : ∀ i : Fin n, A i.succ 0 = 0) :
    frobNormRect A ≤
      |A 0 0| + vecNorm2 (fun j : Fin n => A 0 j.succ) +
        frobNormRect (fun i j : Fin n => A i.succ j.succ) := by
  let a : ℝ := |A 0 0|
  let b : ℝ := vecNorm2 (fun j : Fin n => A 0 j.succ)
  let c : ℝ := frobNormRect (fun i j : Fin n => A i.succ j.succ)
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := vecNorm2_nonneg _
  have hc : 0 ≤ c := frobNormRect_nonneg _
  have hsum_nonneg : 0 ≤ a + b + c := by positivity
  have hsq :
      frobNormSqRect A ≤ (a + b + c) ^ 2 := by
    have hblock := frobNormSqRect_block_firstColumnTail_zero A hcol
    have hb_sq : b ^ 2 = vecNorm2Sq (fun j : Fin n => A 0 j.succ) := by
      dsimp [b]
      exact vecNorm2_sq _
    have hc_sq :
        c ^ 2 = frobNormSqRect (fun i j : Fin n => A i.succ j.succ) := by
      dsimp [c]
      exact frobNormRect_sq _
    have ha_sq : a ^ 2 = A 0 0 ^ 2 := by
      dsimp [a]
      exact sq_abs (A 0 0)
    rw [hblock, ← ha_sq, ← hb_sq, ← hc_sq]
    nlinarith [ha, hb, hc]
  change frobNormRect A ≤ a + b + c
  unfold frobNormRect
  rw [← Real.sqrt_sq hsum_nonneg]
  exact Real.sqrt_le_sqrt hsq

/-- Exact squared Frobenius block split when the last row before the final
    entry is zero. -/
theorem frobNormSqRect_block_lastRowInit_zero {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hrow : ∀ j : Fin n, A (Fin.last n) j.castSucc = 0) :
    frobNormSqRect A =
      frobNormSqRect (fun i j : Fin n => A i.castSucc j.castSucc) +
        vecNorm2Sq (fun i : Fin n => A i.castSucc (Fin.last n)) +
        A (Fin.last n) (Fin.last n) ^ 2 := by
  unfold frobNormSqRect vecNorm2Sq
  rw [Fin.sum_univ_castSucc]
  have htop :
      (∑ i : Fin n, ∑ j : Fin (n + 1), A i.castSucc j ^ 2) =
        (∑ i : Fin n, ∑ j : Fin n, A i.castSucc j.castSucc ^ 2) +
          ∑ i : Fin n, A i.castSucc (Fin.last n) ^ 2 := by
    calc
      (∑ i : Fin n, ∑ j : Fin (n + 1), A i.castSucc j ^ 2)
          = ∑ i : Fin n,
              ((∑ j : Fin n, A i.castSucc j.castSucc ^ 2) +
                A i.castSucc (Fin.last n) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Fin.sum_univ_castSucc]
      _ = (∑ i : Fin n, ∑ j : Fin n, A i.castSucc j.castSucc ^ 2) +
            ∑ i : Fin n, A i.castSucc (Fin.last n) ^ 2 := by
            rw [Finset.sum_add_distrib]
  have hlast :
      (∑ j : Fin (n + 1), A (Fin.last n) j ^ 2) =
        A (Fin.last n) (Fin.last n) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    simp [hrow]
  rw [htop, hlast]

/-- Frobenius block triangle estimate when the last row before the final entry
    is zero. -/
theorem frobNormRect_block_lastRowInit_zero_le {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hrow : ∀ j : Fin n, A (Fin.last n) j.castSucc = 0) :
    frobNormRect A ≤
      frobNormRect (fun i j : Fin n => A i.castSucc j.castSucc) +
        vecNorm2 (fun i : Fin n => A i.castSucc (Fin.last n)) +
        |A (Fin.last n) (Fin.last n)| := by
  let a : ℝ := frobNormRect (fun i j : Fin n => A i.castSucc j.castSucc)
  let b : ℝ := vecNorm2 (fun i : Fin n => A i.castSucc (Fin.last n))
  let c : ℝ := |A (Fin.last n) (Fin.last n)|
  have ha : 0 ≤ a := frobNormRect_nonneg _
  have hb : 0 ≤ b := vecNorm2_nonneg _
  have hc : 0 ≤ c := abs_nonneg _
  have hsum_nonneg : 0 ≤ a + b + c := by positivity
  have hsq : frobNormSqRect A ≤ (a + b + c) ^ 2 := by
    have hblock := frobNormSqRect_block_lastRowInit_zero A hrow
    have ha_sq :
        a ^ 2 =
          frobNormSqRect (fun i j : Fin n => A i.castSucc j.castSucc) := by
      dsimp [a]
      exact frobNormRect_sq _
    have hb_sq :
        b ^ 2 = vecNorm2Sq (fun i : Fin n => A i.castSucc (Fin.last n)) := by
      dsimp [b]
      exact vecNorm2_sq _
    have hc_sq : c ^ 2 = A (Fin.last n) (Fin.last n) ^ 2 := by
      dsimp [c]
      exact sq_abs _
    rw [hblock, ← ha_sq, ← hb_sq, ← hc_sq]
    nlinarith [ha, hb, hc]
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsum_nonneg] at hsqrt
  simpa [frobNormRect, a, b, c] using hsqrt

/-- Rectangular Frobenius squared norm as the sum of squared column norms. -/
theorem frobNormSqRect_eq_sum_vecNorm2Sq_cols {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    frobNormSqRect A = ∑ j : Fin n, vecNorm2Sq (fun i : Fin m => A i j) := by
  unfold frobNormSqRect vecNorm2Sq
  rw [Finset.sum_comm]

/-- Columnwise Euclidean control gives rectangular Frobenius control. -/
theorem frobNormRect_le_of_col_vecNorm2_le {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hcol : ∀ j : Fin n,
      vecNorm2 (fun i : Fin m => A i j) ≤
        η * vecNorm2 (fun i : Fin m => B i j)) :
    frobNormRect A ≤ η * frobNormRect B := by
  have hsqs : frobNormSqRect A ≤ η ^ 2 * frobNormSqRect B := by
    rw [frobNormSqRect_eq_sum_vecNorm2Sq_cols A,
      frobNormSqRect_eq_sum_vecNorm2Sq_cols B]
    calc
      (∑ j : Fin n, vecNorm2Sq (fun i : Fin m => A i j))
          = ∑ j : Fin n, (vecNorm2 (fun i : Fin m => A i j)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro j _
              rw [vecNorm2_sq]
      _ ≤ ∑ j : Fin n,
            (η * vecNorm2 (fun i : Fin m => B i j)) ^ 2 := by
              apply Finset.sum_le_sum
              intro j _
              have hleft_nonneg :
                  0 ≤ vecNorm2 (fun i : Fin m => A i j) :=
                vecNorm2_nonneg _
              have hright_nonneg :
                  0 ≤ η * vecNorm2 (fun i : Fin m => B i j) :=
                mul_nonneg hη (vecNorm2_nonneg _)
              have habs :
                  |vecNorm2 (fun i : Fin m => A i j)| ≤
                    |η * vecNorm2 (fun i : Fin m => B i j)| := by
                rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
                exact hcol j
              exact (sq_le_sq).mpr habs
      _ = ∑ j : Fin n,
            η ^ 2 * (vecNorm2 (fun i : Fin m => B i j)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = η ^ 2 * ∑ j : Fin n,
            (vecNorm2 (fun i : Fin m => B i j)) ^ 2 := by
              rw [Finset.mul_sum]
      _ = η ^ 2 * ∑ j : Fin n,
            vecNorm2Sq (fun i : Fin m => B i j) := by
              congr 1
              apply Finset.sum_congr rfl
              intro j _
              rw [vecNorm2_sq]
  unfold frobNormRect
  calc
    Real.sqrt (frobNormSqRect A)
        ≤ Real.sqrt (η ^ 2 * frobNormSqRect B) :=
          Real.sqrt_le_sqrt hsqs
    _ = η * Real.sqrt (frobNormSqRect B) := by
          rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq_eq_abs,
            abs_of_nonneg hη]

/-- Columnwise Euclidean control gives rectangular Frobenius control even when
    the compared matrices have different row dimensions. -/
theorem frobNormRect_le_of_col_vecNorm2_le_rect {m n p : ℕ}
    (A : Fin m → Fin p → ℝ) (B : Fin n → Fin p → ℝ) {η : ℝ}
    (hη : 0 ≤ η)
    (hcol : ∀ j : Fin p,
      vecNorm2 (fun i : Fin m => A i j) ≤
        η * vecNorm2 (fun i : Fin n => B i j)) :
    frobNormRect A ≤ η * frobNormRect B := by
  have hsqs : frobNormSqRect A ≤ η ^ 2 * frobNormSqRect B := by
    rw [frobNormSqRect_eq_sum_vecNorm2Sq_cols A,
      frobNormSqRect_eq_sum_vecNorm2Sq_cols B]
    calc
      (∑ j : Fin p, vecNorm2Sq (fun i : Fin m => A i j))
          = ∑ j : Fin p, (vecNorm2 (fun i : Fin m => A i j)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro j _
              rw [vecNorm2_sq]
      _ ≤ ∑ j : Fin p,
            (η * vecNorm2 (fun i : Fin n => B i j)) ^ 2 := by
              apply Finset.sum_le_sum
              intro j _
              have hleft_nonneg :
                  0 ≤ vecNorm2 (fun i : Fin m => A i j) :=
                vecNorm2_nonneg _
              have hright_nonneg :
                  0 ≤ η * vecNorm2 (fun i : Fin n => B i j) :=
                mul_nonneg hη (vecNorm2_nonneg _)
              have habs :
                  |vecNorm2 (fun i : Fin m => A i j)| ≤
                    |η * vecNorm2 (fun i : Fin n => B i j)| := by
                rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
                exact hcol j
              exact (sq_le_sq).mpr habs
      _ = ∑ j : Fin p,
            η ^ 2 * (vecNorm2 (fun i : Fin n => B i j)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = η ^ 2 * ∑ j : Fin p,
            (vecNorm2 (fun i : Fin n => B i j)) ^ 2 := by
              rw [Finset.mul_sum]
      _ = η ^ 2 * ∑ j : Fin p,
            vecNorm2Sq (fun i : Fin n => B i j) := by
              congr 1
              apply Finset.sum_congr rfl
              intro j _
              rw [vecNorm2_sq]
  unfold frobNormRect
  calc
    Real.sqrt (frobNormSqRect A)
        ≤ Real.sqrt (η ^ 2 * frobNormSqRect B) :=
          Real.sqrt_le_sqrt hsqs
    _ = η * Real.sqrt (frobNormSqRect B) := by
          rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq_eq_abs,
            abs_of_nonneg hη]

/-- Squared Euclidean norm is homogeneous under scalar multiplication. -/
lemma vecNorm2Sq_smul {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    vecNorm2Sq (fun i => a * x i) = a ^ 2 * vecNorm2Sq x := by
  unfold vecNorm2Sq
  simp_rw [show ∀ i : Fin n, (a * x i) ^ 2 = a ^ 2 * x i ^ 2
    from fun i => by ring]
  rw [Finset.mul_sum]

/-- The quadratic form of the identity matrix is the squared Euclidean norm. -/
theorem quadraticForm_idMatrix_eq_vecNorm2Sq
    {n : ℕ} (y : Fin n → ℝ) :
    (∑ j : Fin n, y j * matMulVec n (idMatrix n) y j) =
      vecNorm2Sq y := by
  have hid : ∀ j : Fin n, matMulVec n (idMatrix n) y j = y j := by
    intro j
    exact congrFun (idMatrix_mulVec n y) j
  calc
    (∑ j : Fin n, y j * matMulVec n (idMatrix n) y j)
        = ∑ j : Fin n, y j * y j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hid j]
    _ = vecNorm2Sq y := by
            unfold vecNorm2Sq
            simp_rw [pow_two]

/-- Adding the identity part of a shifted quadratic form recovers the
    unshifted quadratic form. -/
theorem vecNorm2Sq_add_quadraticForm_sub_id_eq_quadraticForm
    {n : ℕ} (G : Fin n → Fin n → ℝ) (y : Fin n → ℝ) :
    vecNorm2Sq y +
        ∑ j : Fin n, y j *
          matMulVec n (fun j k => G j k - idMatrix n j k) y j =
      ∑ j : Fin n, y j * matMulVec n G y j := by
  have hdiff :
      ∀ j : Fin n,
        matMulVec n (fun j k => G j k - idMatrix n j k) y j =
          matMulVec n G y j - matMulVec n (idMatrix n) y j := by
    intro j
    unfold matMulVec
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hid : ∀ j : Fin n, matMulVec n (idMatrix n) y j = y j := by
    intro j
    exact congrFun (idMatrix_mulVec n y) j
  calc
    vecNorm2Sq y +
        ∑ j : Fin n, y j *
          matMulVec n (fun j k => G j k - idMatrix n j k) y j
        = vecNorm2Sq y +
            ∑ j : Fin n, y j * (matMulVec n G y j - y j) := by
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            rw [hdiff j, hid j]
    _ = ∑ j : Fin n, y j * matMulVec n G y j := by
            unfold vecNorm2Sq
            simp_rw [mul_sub, pow_two]
            rw [Finset.sum_sub_distrib]
            ring

/-- Euclidean norm is homogeneous under scalar multiplication. -/
lemma vecNorm2_smul {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    vecNorm2 (fun i => a * x i) = |a| * vecNorm2 x := by
  unfold vecNorm2
  rw [vecNorm2Sq_smul]
  rw [Real.sqrt_mul (sq_nonneg a)]
  rw [Real.sqrt_sq_eq_abs]

/-- Each coordinate is bounded in magnitude by the Euclidean norm. -/
lemma abs_coord_le_vecNorm2 {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    |x j| ≤ vecNorm2 x := by
  have hterm : x j ^ 2 ≤ vecNorm2Sq x := by
    unfold vecNorm2Sq
    exact Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ j)
  have hsqrt := Real.sqrt_le_sqrt hterm
  simpa [vecNorm2, Real.sqrt_sq_eq_abs] using hsqrt

/-- If every coordinate is bounded by `B`, then the Euclidean norm is bounded
    by `sqrt n * B`.

    This finite-dimensional estimate is used by the Cox--Higham QR route to
    turn an active-tail entrywise row bound into the pivot-row norm bound from
    equation (4.4). -/
lemma vecNorm2_le_sqrt_card_mul_of_abs_le {n : ℕ} (x : Fin n → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hcoord : ∀ i : Fin n, |x i| ≤ B) :
    vecNorm2 x ≤ Real.sqrt (n : ℝ) * B := by
  have hsq :
      vecNorm2Sq x ≤ (n : ℝ) * B ^ 2 := by
    unfold vecNorm2Sq
    calc
      ∑ i : Fin n, x i ^ 2 = ∑ i : Fin n, |x i| ^ 2 := by
        congr 1
        ext i
        rw [sq_abs]
      _ ≤ ∑ _i : Fin n, B ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        nlinarith [abs_nonneg (x i), hcoord i, hB]
      _ = (n : ℝ) * B ^ 2 := by
        simp
  have hsqrt := Real.sqrt_le_sqrt hsq
  have hn : 0 ≤ (n : ℝ) := by positivity
  have htarget :
      Real.sqrt ((n : ℝ) * B ^ 2) = Real.sqrt (n : ℝ) * B := by
    rw [Real.sqrt_mul hn, Real.sqrt_sq_eq_abs, abs_of_nonneg hB]
  exact hsqrt.trans_eq htarget

-- ============================================================
-- Rank-one Frobenius/vector norm bridges
-- ============================================================

/-- Squared Frobenius norm of a rank-one matrix factors into the product of
    the squared vector norms. -/
theorem frobNormSq_rankOne {m n : ℕ}
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    frobNormSq (fun i j => x i * y j) =
      vecNorm2Sq x * vecNorm2Sq y := by
  unfold frobNormSq vecNorm2Sq
  simp_rw [show ∀ i : Fin m, ∀ j : Fin n,
      (x i * y j) ^ 2 = x i ^ 2 * y j ^ 2 from fun i j => by ring]
  calc
    (∑ i : Fin m, ∑ j : Fin n, x i ^ 2 * y j ^ 2)
        = ∑ i : Fin m, x i ^ 2 * ∑ j : Fin n, y j ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = (∑ i : Fin m, x i ^ 2) * (∑ j : Fin n, y j ^ 2) := by
            rw [Finset.sum_mul]

/-- Frobenius norm of a rank-one matrix factors into the product of vector
    Euclidean norms. -/
theorem frobNorm_rankOne {m n : ℕ}
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    frobNorm (fun i j => x i * y j) =
      vecNorm2 x * vecNorm2 y := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNormSq_rankOne]
  unfold vecNorm2
  rw [Real.sqrt_mul (vecNorm2Sq_nonneg x)]

/-- Frobenius norm of a scalar multiple of a rank-one matrix. -/
theorem frobNorm_rankOne_smul {m n : ℕ}
    (a : ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    frobNorm (fun i j => a * (x i * y j)) =
      |a| * vecNorm2 x * vecNorm2 y := by
  rw [← frobNormRect_eq_frobNormFn (fun i j => a * (x i * y j))]
  rw [frobNormRect_smul a (fun i j => x i * y j)]
  rw [frobNormRect_eq_frobNormFn (fun i j => x i * y j)]
  rw [frobNorm_rankOne]
  ring

/-- Specialized rank-one perturbation norm used to convert vector forward
    error into a matrix backward-error witness. -/
theorem frobNorm_rankOne_div_vecNorm2Sq {n : ℕ}
    (e b : Fin n → ℝ) (hb : vecNorm2 b ≠ 0) :
    frobNorm (fun i j => (1 / vecNorm2Sq b) * (e i * b j)) =
      vecNorm2 e / vecNorm2 b := by
  rw [frobNorm_rankOne_smul]
  have hden_nonneg : 0 ≤ vecNorm2Sq b := vecNorm2Sq_nonneg b
  have hden_eq : vecNorm2Sq b = vecNorm2 b ^ 2 := (vecNorm2_sq b).symm
  rw [abs_of_nonneg (one_div_nonneg.mpr hden_nonneg), hden_eq]
  field_simp [hb]

-- ============================================================
-- Finite-type vector-action infrastructure
-- ============================================================

/-- Squared Euclidean norm over an arbitrary finite index type. -/
noncomputable def finiteVecNorm2Sq {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  ∑ i : ι, x i ^ 2

/-- Euclidean norm over an arbitrary finite index type. -/
noncomputable def finiteVecNorm2 {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  Real.sqrt (finiteVecNorm2Sq x)

/-- Generic finite squared Euclidean norm is nonnegative. -/
lemma finiteVecNorm2Sq_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ finiteVecNorm2Sq x := by
  unfold finiteVecNorm2Sq
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- Generic finite Euclidean norm is nonnegative. -/
lemma finiteVecNorm2_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ finiteVecNorm2 x :=
  Real.sqrt_nonneg _

/-- Generic finite Euclidean norm squared is the squared-norm sum. -/
lemma finiteVecNorm2_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    finiteVecNorm2 x ^ 2 = finiteVecNorm2Sq x := by
  unfold finiteVecNorm2
  rw [sq, Real.mul_self_sqrt (finiteVecNorm2Sq_nonneg x)]

/-- The zero vector has zero generic finite Euclidean norm. -/
lemma finiteVecNorm2_zero {ι : Type*} [Fintype ι] :
    finiteVecNorm2 (fun _i : ι => 0) = 0 := by
  unfold finiteVecNorm2 finiteVecNorm2Sq
  simp

/-- A generic finite vector has zero Euclidean norm iff all entries vanish. -/
lemma finiteVecNorm2_eq_zero_iff {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    finiteVecNorm2 x = 0 ↔ ∀ i, x i = 0 := by
  unfold finiteVecNorm2
  rw [Real.sqrt_eq_zero (finiteVecNorm2Sq_nonneg x)]
  constructor
  · intro h i
    have hterms :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset ι))
        (f := fun i : ι => x i ^ 2)
        (by intro k _; exact sq_nonneg (x k))).mp h
    exact sq_eq_zero_iff.mp (hterms i (Finset.mem_univ i))
  · intro hx
    unfold finiteVecNorm2Sq
    simp [hx]

/-- Generic finite squared Euclidean norm is homogeneous under scalar
multiplication. -/
lemma finiteVecNorm2Sq_smul {ι : Type*} [Fintype ι]
    (a : ℝ) (x : ι → ℝ) :
    finiteVecNorm2Sq (fun i => a * x i) = a ^ 2 * finiteVecNorm2Sq x := by
  unfold finiteVecNorm2Sq
  simp_rw [show ∀ i : ι, (a * x i) ^ 2 = a ^ 2 * x i ^ 2
    from fun i => by ring]
  rw [Finset.mul_sum]

/-- Generic finite Euclidean norm is homogeneous under scalar multiplication. -/
lemma finiteVecNorm2_smul {ι : Type*} [Fintype ι]
    (a : ℝ) (x : ι → ℝ) :
    finiteVecNorm2 (fun i => a * x i) = |a| * finiteVecNorm2 x := by
  unfold finiteVecNorm2
  rw [finiteVecNorm2Sq_smul]
  rw [Real.sqrt_mul (sq_nonneg a)]
  rw [Real.sqrt_sq_eq_abs]

/-- Generic finite matrix-vector product. -/
noncomputable def finiteMatVec {ι κ : Type*} [Fintype κ]
    (M : ι → κ → ℝ) (x : κ → ℝ) : ι → ℝ :=
  fun i => ∑ j : κ, M i j * x j

/-- Squared Frobenius norm over arbitrary finite row and column index types. -/
noncomputable def finiteFrobNormSq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : κ, M i j ^ 2

/-- The generic finite squared Frobenius norm specializes to the rectangular
`Fin`-indexed squared Frobenius norm. -/
theorem finiteFrobNormSq_fin {m n : ℕ} (M : Fin m → Fin n → ℝ) :
    finiteFrobNormSq M = frobNormSqRect M := rfl

/-- Negating every entry preserves the generic finite squared Frobenius norm. -/
theorem finiteFrobNormSq_neg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℝ) :
    finiteFrobNormSq (fun i j => -M i j) = finiteFrobNormSq M := by
  unfold finiteFrobNormSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Splitting the column index as a sum type splits the generic finite squared
Frobenius norm into the two block-column squared norms. -/
theorem finiteFrobNormSq_sumColumns
    {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (A : ι → α → ℝ) (B : ι → β → ℝ) :
    finiteFrobNormSq
        (fun i (c : α ⊕ β) =>
          match c with
          | Sum.inl a => A i a
          | Sum.inr b => B i b) =
      finiteFrobNormSq A + finiteFrobNormSq B := by
  unfold finiteFrobNormSq
  calc
    (∑ i : ι,
        ∑ c : α ⊕ β,
          (match c with
          | Sum.inl a => A i a
          | Sum.inr b => B i b) ^ 2)
        =
          ∑ i : ι, ((∑ a : α, A i a ^ 2) + (∑ b : β, B i b ^ 2)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Fintype.sum_sum_type]
    _ = (∑ i : ι, ∑ a : α, A i a ^ 2) +
          (∑ i : ι, ∑ b : β, B i b ^ 2) := by
            rw [Finset.sum_add_distrib]

/-- Right multiplication by a finite column family with orthonormal rows
preserves the squared Frobenius norm of a `Fin`-indexed rectangular matrix.

This is the sum-indexed analogue of `frobNormSqRect_orthogonal_right`; the
column index need only be an arbitrary finite type `κ`, provided the rows of
`Q` satisfy `Q Qᵀ = I`. -/
theorem finiteFrobNormSq_rectRightOrthonormal
    {m n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin m → Fin n → ℝ) (Q : Fin n → κ → ℝ)
    (hQ : ∀ j k, ∑ c : κ, Q j c * Q k c = idMatrix n j k) :
    finiteFrobNormSq (fun i c => ∑ j : Fin n, A i j * Q j c) =
      frobNormSqRect A := by
  unfold finiteFrobNormSq frobNormSqRect
  apply Finset.sum_congr rfl
  intro i _
  have expand : ∀ c : κ,
      (∑ j : Fin n, A i j * Q j c) ^ 2 =
        ∑ j : Fin n, ∑ k : Fin n,
          A i j * A i k * (Q j c * Q k c) := by
    intro c
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [expand]
  have collapse : ∀ j : Fin n,
      ∑ c : κ, ∑ k : Fin n,
          A i j * A i k * (Q j c * Q k c) =
        A i j ^ 2 := by
    intro j
    rw [Finset.sum_comm]
    have factor : ∀ k : Fin n,
        ∑ c : κ, A i j * A i k * (Q j c * Q k c) =
          A i j * A i k * (∑ c : κ, Q j c * Q k c) := by
      intro k
      rw [Finset.mul_sum]
    simp_rw [factor, hQ]
    simp [idMatrix, Finset.sum_ite_eq, Finset.mem_univ]
    ring
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => collapse j)

/-- Generic finite square matrix product. -/
noncomputable def finiteMatMul {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i k => ∑ j : ι, M i j * N j k

/-- Generic finite identity matrix. -/
noncomputable def finiteIdMatrix {ι : Type*} [DecidableEq ι] :
    ι → ι → ℝ :=
  fun i j => if i = j then 1 else 0

/-- Generic finite diagonal matrix with diagonal entries `v`. -/
noncomputable def finiteDiagonal {ι : Type*} [DecidableEq ι]
    (v : ι → ℝ) : ι → ι → ℝ :=
  fun i j => if i = j then v i else 0

/-- Generic finite standard basis vector. -/
noncomputable def finiteBasisVec {ι : Type*} [DecidableEq ι] (i : ι) :
    ι → ℝ :=
  fun j => if j = i then 1 else 0

/-- Generic finite transpose. -/
noncomputable def finiteTranspose {ι κ : Type*} (M : ι → κ → ℝ) :
    κ → ι → ℝ :=
  fun j i => M i j

/-- Transposing a right inverse gives a left inverse of the transposed matrix. -/
theorem isLeftInverse_finiteTranspose_of_isRightInverse {n : ℕ}
    {T T_inv : Fin n → Fin n → ℝ}
    (hInv : IsRightInverse n T T_inv) :
    IsLeftInverse n (finiteTranspose T) (finiteTranspose T_inv) := by
  intro i j
  calc
    ∑ k : Fin n, finiteTranspose T_inv i k * finiteTranspose T k j
        = ∑ k : Fin n, T j k * T_inv k i := by
            apply Finset.sum_congr rfl
            intro k _
            unfold finiteTranspose
            ring
    _ = (if j = i then 1 else 0) := hInv j i
    _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j <;> simp [hij, eq_comm]

/-- Transposing a left inverse gives a right inverse of the transposed matrix. -/
theorem isRightInverse_finiteTranspose_of_isLeftInverse {n : ℕ}
    {T T_inv : Fin n → Fin n → ℝ}
    (hInv : IsLeftInverse n T T_inv) :
    IsRightInverse n (finiteTranspose T) (finiteTranspose T_inv) := by
  intro i j
  calc
    ∑ k : Fin n, finiteTranspose T i k * finiteTranspose T_inv k j
        = ∑ k : Fin n, T_inv j k * T k i := by
            apply Finset.sum_congr rfl
            intro k _
            unfold finiteTranspose
            ring
    _ = (if j = i then 1 else 0) := hInv j i
    _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j <;> simp [hij, eq_comm]

/-- Transposition preserves two-sided inverse witnesses. -/
theorem isInverse_finiteTranspose {n : ℕ}
    {T T_inv : Fin n → Fin n → ℝ}
    (hInv : IsInverse n T T_inv) :
    IsInverse n (finiteTranspose T) (finiteTranspose T_inv) :=
  ⟨isLeftInverse_finiteTranspose_of_isRightInverse hInv.2,
    isRightInverse_finiteTranspose_of_isLeftInverse hInv.1⟩

/-- Generic finite trace. -/
noncomputable def finiteTrace {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) : ℝ :=
  ∑ i : ι, M i i

/-- Trace is additive. -/
theorem finiteTrace_add {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ) :
    finiteTrace (fun i j => M i j + N i j) =
      finiteTrace M + finiteTrace N := by
  unfold finiteTrace
  rw [← Finset.sum_add_distrib]

/-- Trace is homogeneous under scalar multiplication. -/
theorem finiteTrace_smul {ι : Type*} [Fintype ι]
    (a : ℝ) (M : ι → ι → ℝ) :
    finiteTrace (fun i j => a * M i j) = a * finiteTrace M := by
  unfold finiteTrace
  rw [Finset.mul_sum]

/-- Trace commutes with matrix negation. -/
theorem finiteTrace_neg {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) :
    finiteTrace (fun i j => -M i j) = -finiteTrace M := by
  simpa using finiteTrace_smul (-1 : ℝ) M

/-- Trace is subtractive. -/
theorem finiteTrace_sub {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ) :
    finiteTrace (fun i j => M i j - N i j) =
      finiteTrace M - finiteTrace N := by
  have hrewrite :
      (fun i j => M i j - N i j) =
        (fun i j => M i j + (fun i j => -N i j) i j) := by
    ext i j
    ring
  rw [hrewrite, finiteTrace_add, finiteTrace_neg]
  ring

/-- Trace of the generic finite identity matrix. -/
theorem finiteTrace_finiteIdMatrix {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    finiteTrace (finiteIdMatrix : ι → ι → ℝ) = (Fintype.card ι : ℝ) := by
  unfold finiteTrace finiteIdMatrix
  simp [Finset.sum_const, Finset.card_univ]

/-- Trace of a scalar multiple of the generic finite identity matrix. -/
theorem finiteTrace_smul_finiteIdMatrix {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ℝ) :
    finiteTrace (fun i j => a * (finiteIdMatrix : ι → ι → ℝ) i j) =
      a * (Fintype.card ι : ℝ) := by
  rw [finiteTrace_smul, finiteTrace_finiteIdMatrix]

/-- Trace commutes with sums over a finite type. -/
theorem finiteTrace_fintype_sum
    {ι α : Type*} [Fintype ι] [Fintype α]
    (M : α → ι → ι → ℝ) :
    finiteTrace (fun i j => ∑ a : α, M a i j) =
      ∑ a : α, finiteTrace (M a) := by
  classical
  unfold finiteTrace
  rw [Finset.sum_comm]

/-- Trace commutes with weighted sums over a finite type. -/
theorem finiteTrace_fintype_sum_smul
    {ι α : Type*} [Fintype ι] [Fintype α]
    (w : α → ℝ) (M : α → ι → ι → ℝ) :
    finiteTrace (fun i j => ∑ a : α, w a * M a i j) =
      ∑ a : α, w a * finiteTrace (M a) := by
  classical
  rw [finiteTrace_fintype_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [finiteTrace_smul]

/-- Cyclicity of finite trace for two square matrices. -/
theorem finiteTrace_finiteMatMul_comm {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ) :
    finiteTrace (finiteMatMul M N) =
      finiteTrace (finiteMatMul N M) := by
  classical
  unfold finiteTrace finiteMatMul
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Matrix-vector multiplication by a finite matrix product composes the two
    matrix-vector products. -/
theorem finiteMatVec_finiteMatMul {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ) (x : ι → ℝ) :
    finiteMatVec (finiteMatMul M N) x =
      finiteMatVec M (finiteMatVec N x) := by
  classical
  ext i
  unfold finiteMatVec finiteMatMul
  calc
    (∑ k : ι, (∑ j : ι, M i j * N j k) * x k)
        = ∑ k : ι, ∑ j : ι, M i j * (N j k * x k) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = ∑ j : ι, ∑ k : ι, M i j * (N j k * x k) := by
            rw [Finset.sum_comm]
    _ = ∑ j : ι, M i j * ∑ k : ι, N j k * x k := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]

/-- The generic finite identity matrix acts as the identity on vectors. -/
theorem finiteMatVec_finiteIdMatrix {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x : ι → ℝ) :
    finiteMatVec (finiteIdMatrix : ι → ι → ℝ) x = x := by
  ext i
  unfold finiteMatVec finiteIdMatrix
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- Multiplying a finite matrix by a standard basis vector selects a column. -/
theorem finiteMatVec_finiteBasisVec {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : ι → ι → ℝ) (j : ι) :
    finiteMatVec M (finiteBasisVec j) = fun i => M i j := by
  ext i
  unfold finiteMatVec finiteBasisVec
  simp [Finset.mem_univ]

/-- Generic finite matrix-vector multiplication is additive in the vector
argument. -/
theorem finiteMatVec_add {ι κ : Type*} [Fintype κ]
    (M : ι → κ → ℝ) (x y : κ → ℝ) :
    finiteMatVec M (fun j => x j + y j) =
      fun i => finiteMatVec M x i + finiteMatVec M y i := by
  ext i
  unfold finiteMatVec
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Generic finite matrix-vector multiplication is subtractive in the vector
argument. -/
theorem finiteMatVec_sub {ι κ : Type*} [Fintype κ]
    (M : ι → κ → ℝ) (x y : κ → ℝ) :
    finiteMatVec M (fun j => x j - y j) =
      fun i => finiteMatVec M x i - finiteMatVec M y i := by
  ext i
  unfold finiteMatVec
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Generic finite matrix-vector multiplication is bounded by the generic
    squared Frobenius norm. -/
theorem finiteVecNorm2Sq_finiteMatVec_le_finiteFrobNormSq_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℝ) (x : κ → ℝ) :
    finiteVecNorm2Sq (finiteMatVec M x) ≤
      finiteFrobNormSq M * finiteVecNorm2Sq x := by
  unfold finiteVecNorm2Sq finiteMatVec finiteFrobNormSq
  calc
    ∑ i : ι, (∑ j : κ, M i j * x j) ^ 2
        ≤ ∑ i : ι,
            (∑ j : κ, M i j ^ 2) * (∑ j : κ, x j ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.sum_mul_sq_le_sq_mul_sq
            Finset.univ (fun j => M i j) (fun j => x j)
    _ = (∑ i : ι, ∑ j : κ, M i j ^ 2) *
          (∑ j : κ, x j ^ 2) := by
        rw [Finset.sum_mul]

/-- Generic finite vector-action operator-2 predicate. -/
def finiteOpNorm2Le {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (c : ℝ) : Prop :=
  ∀ x : ι → ℝ, finiteVecNorm2 (finiteMatVec M x) ≤ c * finiteVecNorm2 x

/-- A squared Frobenius bound implies the finite vector-action operator-2
    predicate. -/
theorem finiteOpNorm2Le_of_finiteFrobNormSq_le_sq
    {ι : Type*} [Fintype ι] (M : ι → ι → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hF : finiteFrobNormSq M ≤ L ^ 2) :
    finiteOpNorm2Le M L := by
  intro x
  have hvec :=
    finiteVecNorm2Sq_finiteMatVec_le_finiteFrobNormSq_mul M x
  have hx_nonneg : 0 ≤ finiteVecNorm2Sq x := finiteVecNorm2Sq_nonneg x
  have hsq :
      finiteVecNorm2 (finiteMatVec M x) ^ 2 ≤
        (L * finiteVecNorm2 x) ^ 2 := by
    rw [finiteVecNorm2_sq]
    calc
      finiteVecNorm2Sq (finiteMatVec M x)
          ≤ finiteFrobNormSq M * finiteVecNorm2Sq x := hvec
      _ ≤ L ^ 2 * finiteVecNorm2Sq x :=
          mul_le_mul_of_nonneg_right hF hx_nonneg
      _ = (L * finiteVecNorm2 x) ^ 2 := by
          rw [show (L * finiteVecNorm2 x) ^ 2 =
              L ^ 2 * finiteVecNorm2 x ^ 2 from by ring,
            finiteVecNorm2_sq]
  have hleft_nonneg : 0 ≤ finiteVecNorm2 (finiteMatVec M x) :=
    finiteVecNorm2_nonneg (finiteMatVec M x)
  have hright_nonneg : 0 ≤ L * finiteVecNorm2 x :=
    mul_nonneg hL (finiteVecNorm2_nonneg x)
  have habs := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs

/-- Quadratic form `xᵀMx` for a generic finite square matrix. -/
noncomputable def finiteQuadraticForm {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i : ι, x i * finiteMatVec M x i

/-- Positive-semidefinite predicate in quadratic-form form. -/
def finitePSD {ι : Type*} [Fintype ι] (M : ι → ι → ℝ) : Prop :=
  ∀ x : ι → ℝ, 0 ≤ finiteQuadraticForm M x

/-- Loewner-order predicate in quadratic-form form. -/
def finiteLoewnerLe {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ) : Prop :=
  ∀ x : ι → ℝ, finiteQuadraticForm M x ≤ finiteQuadraticForm N x

/-- Reflexivity of the finite Loewner order. -/
theorem finiteLoewnerLe_refl {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) :
    finiteLoewnerLe M M := by
  intro x
  rfl

/-- Transitivity of the finite Loewner order. -/
theorem finiteLoewnerLe_trans {ι : Type*} [Fintype ι]
    {M N K : ι → ι → ℝ}
    (hMN : finiteLoewnerLe M N) (hNK : finiteLoewnerLe N K) :
    finiteLoewnerLe M K := by
  intro x
  exact (hMN x).trans (hNK x)

/-- Positive semidefiniteness is Loewner nonnegativity. -/
theorem finitePSD_iff_zero_loewnerLe {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) :
    finitePSD M ↔ finiteLoewnerLe (fun _ _ => 0) M := by
  constructor
  · intro hM x
    simpa [finiteQuadraticForm, finiteMatVec] using hM x
  · intro hM x
    simpa [finiteQuadraticForm, finiteMatVec] using hM x

/-- Quadratic form of the generic finite identity matrix. -/
theorem finiteQuadraticForm_finiteIdMatrix {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x : ι → ℝ) :
    finiteQuadraticForm (finiteIdMatrix : ι → ι → ℝ) x =
      finiteVecNorm2Sq x := by
  unfold finiteQuadraticForm
  rw [finiteMatVec_finiteIdMatrix]
  unfold finiteVecNorm2Sq
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quadratic form on a standard basis vector reads off a diagonal entry. -/
theorem finiteQuadraticForm_finiteBasisVec {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : ι → ι → ℝ) (i : ι) :
    finiteQuadraticForm M (finiteBasisVec i) = M i i := by
  unfold finiteQuadraticForm
  rw [finiteMatVec_finiteBasisVec]
  unfold finiteBasisVec
  simp [Finset.mem_univ]

/-- Quadratic forms are homogeneous in the matrix argument. -/
theorem finiteQuadraticForm_smul {ι : Type*} [Fintype ι]
    (a : ℝ) (M : ι → ι → ℝ) (x : ι → ℝ) :
    finiteQuadraticForm (fun i j => a * M i j) x =
      a * finiteQuadraticForm M x := by
  unfold finiteQuadraticForm finiteMatVec
  calc
    (∑ i : ι, x i * ∑ j : ι, (a * M i j) * x j)
        = ∑ i : ι, x i * (a * ∑ j : ι, M i j * x j) := by
            apply Finset.sum_congr rfl
            intro i _
            have hsum :
                (∑ j : ι, (a * M i j) * x j) =
                  a * ∑ j : ι, M i j * x j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
            rw [hsum]
    _ = ∑ i : ι, a * (x i * ∑ j : ι, M i j * x j) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = a * ∑ i : ι, x i * ∑ j : ι, M i j * x j := by
            rw [Finset.mul_sum]

/-- Quadratic forms are homogeneous of degree two in the vector argument. -/
theorem finiteQuadraticForm_vec_smul {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (a : ℝ) (x : ι → ℝ) :
    finiteQuadraticForm M (fun i => a * x i) =
      a ^ 2 * finiteQuadraticForm M x := by
  unfold finiteQuadraticForm finiteMatVec
  calc
    (∑ i : ι, (a * x i) * ∑ j : ι, M i j * (a * x j))
        = ∑ i : ι, a ^ 2 * (x i * ∑ j : ι, M i j * x j) := by
            apply Finset.sum_congr rfl
            intro i _
            have hsum :
                (∑ j : ι, M i j * (a * x j)) =
                  a * ∑ j : ι, M i j * x j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
            rw [hsum]
            ring
    _ = a ^ 2 * ∑ i : ι, x i * ∑ j : ι, M i j * x j := by
            rw [Finset.mul_sum]

/-- Quadratic form of a scalar multiple of the identity matrix. -/
theorem finiteQuadraticForm_smul_finiteIdMatrix {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ℝ) (x : ι → ℝ) :
    finiteQuadraticForm (fun i j => a * finiteIdMatrix i j) x =
      a * finiteVecNorm2Sq x := by
  rw [finiteQuadraticForm_smul, finiteQuadraticForm_finiteIdMatrix]

/-- Monotonicity of scalar multiples of the finite identity in Loewner order. -/
theorem finiteLoewnerLe_smul_finiteIdMatrix_mono {ι : Type*}
    [Fintype ι] [DecidableEq ι] {a b : ℝ} (hab : a ≤ b) :
    finiteLoewnerLe
      (fun i j : ι => a * finiteIdMatrix i j)
      (fun i j : ι => b * finiteIdMatrix i j) := by
  intro x
  rw [finiteQuadraticForm_smul_finiteIdMatrix,
    finiteQuadraticForm_smul_finiteIdMatrix]
  exact mul_le_mul_of_nonneg_right hab (finiteVecNorm2Sq_nonneg x)

/-- Quadratic forms are additive in the matrix argument. -/
theorem finiteQuadraticForm_add {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ) (x : ι → ℝ) :
    finiteQuadraticForm (fun i j => M i j + N i j) x =
      finiteQuadraticForm M x + finiteQuadraticForm N x := by
  unfold finiteQuadraticForm finiteMatVec
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hsum :
      (∑ j : ι, (M i j + N i j) * x j) =
        (∑ j : ι, M i j * x j) + (∑ j : ι, N i j * x j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

/-- Quadratic forms commute with matrix negation. -/
theorem finiteQuadraticForm_neg {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (x : ι → ℝ) :
    finiteQuadraticForm (fun i j => -M i j) x =
      -finiteQuadraticForm M x := by
  simpa using finiteQuadraticForm_smul (-1 : ℝ) M x

/-- Quadratic forms are subtractive in the matrix argument. -/
theorem finiteQuadraticForm_sub {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ) (x : ι → ℝ) :
    finiteQuadraticForm (fun i j => M i j - N i j) x =
      finiteQuadraticForm M x - finiteQuadraticForm N x := by
  have hrewrite :
      (fun i j => M i j - N i j) =
        (fun i j => M i j + (fun i j => -N i j) i j) := by
    ext i j
    ring
  rw [hrewrite, finiteQuadraticForm_add, finiteQuadraticForm_neg]
  ring

/-- Difference identity for two quadratic forms with the same matrix:
`q_M(x)-q_M(z) = (x-z)^T M x + z^T M (x-z)`. -/
theorem finiteQuadraticForm_sub_vec_eq_sub_add
    {ι : Type*} [Fintype ι] (M : ι → ι → ℝ) (x z : ι → ℝ) :
    finiteQuadraticForm M x - finiteQuadraticForm M z =
      (∑ i : ι, (x i - z i) * finiteMatVec M x i) +
        ∑ i : ι, z i * finiteMatVec M (fun j => x j - z j) i := by
  rw [finiteMatVec_sub]
  unfold finiteQuadraticForm
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A matrix difference is positive semidefinite exactly when the left matrix
    is below the right matrix in finite Loewner order. -/
theorem finiteLoewnerLe_iff_sub_finitePSD {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ) :
    finiteLoewnerLe M N ↔ finitePSD (fun i j => N i j - M i j) := by
  constructor
  · intro hMN x
    rw [finiteQuadraticForm_sub]
    exact sub_nonneg.mpr (hMN x)
  · intro hdiff x
    have h := hdiff x
    rw [finiteQuadraticForm_sub] at h
    exact sub_nonneg.mp h

/-- Loewner order is closed under matrix addition. -/
theorem finiteLoewnerLe_add {ι : Type*} [Fintype ι]
    {M₁ M₂ N₁ N₂ : ι → ι → ℝ}
    (h₁ : finiteLoewnerLe M₁ N₁) (h₂ : finiteLoewnerLe M₂ N₂) :
    finiteLoewnerLe (fun i j => M₁ i j + M₂ i j)
      (fun i j => N₁ i j + N₂ i j) := by
  intro x
  rw [finiteQuadraticForm_add, finiteQuadraticForm_add]
  exact add_le_add (h₁ x) (h₂ x)

/-- Loewner order is closed under nonnegative scalar multiplication. -/
theorem finiteLoewnerLe_smul_of_nonneg {ι : Type*} [Fintype ι]
    {M N : ι → ι → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hMN : finiteLoewnerLe M N) :
    finiteLoewnerLe (fun i j => a * M i j) (fun i j => a * N i j) := by
  intro x
  rw [finiteQuadraticForm_smul, finiteQuadraticForm_smul]
  exact mul_le_mul_of_nonneg_left (hMN x) ha

/-- Cancel a positive scalar from the matrix side of a scalar-identity Loewner
    upper bound.  In concentration arguments this converts
    `theta • M <= L I` into `M <= (L / theta) I` once `theta > 0`. -/
theorem finiteLoewnerLe_of_smul_left_le_smul_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) {theta L : ℝ} (htheta : 0 < theta)
    (h :
      finiteLoewnerLe (fun i j => theta * M i j)
        (fun i j => L * finiteIdMatrix i j)) :
    finiteLoewnerLe M (fun i j => (L / theta) * finiteIdMatrix i j) := by
  intro x
  have hx := h x
  rw [finiteQuadraticForm_smul, finiteQuadraticForm_smul_finiteIdMatrix] at hx
  rw [finiteQuadraticForm_smul_finiteIdMatrix]
  have htheta_ne : theta ≠ 0 := ne_of_gt htheta
  have hmul :
      theta * finiteQuadraticForm M x ≤
        theta * ((L / theta) * finiteVecNorm2Sq x) := by
    calc
      theta * finiteQuadraticForm M x ≤ L * finiteVecNorm2Sq x := hx
      _ = theta * ((L / theta) * finiteVecNorm2Sq x) := by
          field_simp [htheta_ne]
  exact (mul_le_mul_iff_of_pos_left htheta).mp hmul

/-- Quadratic forms commute with finite matrix sums. -/
theorem finiteQuadraticForm_finset_sum
    {ι α : Type*} [Fintype ι] [DecidableEq α]
    (s : Finset α) (M : α → ι → ι → ℝ) (x : ι → ℝ) :
    finiteQuadraticForm (fun i j => ∑ a ∈ s, M a i j) x =
      ∑ a ∈ s, finiteQuadraticForm (M a) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [finiteQuadraticForm, finiteMatVec]
  | insert a s ha ih =>
      have hmatrix :
          (fun i j => ∑ b ∈ insert a s, M b i j) =
            fun i j => M a i j + (fun i j => ∑ b ∈ s, M b i j) i j := by
        ext i j
        simp [ha]
      rw [hmatrix, finiteQuadraticForm_add, ih]
      simp [ha]

/-- Quadratic forms commute with finite matrix sums with scalar weights. -/
theorem finiteQuadraticForm_finset_sum_smul
    {ι α : Type*} [Fintype ι] [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (M : α → ι → ι → ℝ)
    (x : ι → ℝ) :
    finiteQuadraticForm (fun i j => ∑ a ∈ s, w a * M a i j) x =
      ∑ a ∈ s, w a * finiteQuadraticForm (M a) x := by
  rw [finiteQuadraticForm_finset_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [finiteQuadraticForm_smul]

/-- Quadratic forms commute with sums over a finite type. -/
theorem finiteQuadraticForm_fintype_sum
    {ι α : Type*} [Fintype ι] [Fintype α]
    (M : α → ι → ι → ℝ) (x : ι → ℝ) :
    finiteQuadraticForm (fun i j => ∑ a : α, M a i j) x =
      ∑ a : α, finiteQuadraticForm (M a) x := by
  classical
  simpa using
    finiteQuadraticForm_finset_sum (Finset.univ : Finset α) M x

/-- Quadratic forms commute with weighted sums over a finite type. -/
theorem finiteQuadraticForm_fintype_sum_smul
    {ι α : Type*} [Fintype ι] [Fintype α]
    (w : α → ℝ) (M : α → ι → ι → ℝ) (x : ι → ℝ) :
    finiteQuadraticForm (fun i j => ∑ a : α, w a * M a i j) x =
      ∑ a : α, w a * finiteQuadraticForm (M a) x := by
  classical
  simpa using
    finiteQuadraticForm_finset_sum_smul (Finset.univ : Finset α) w M x

/-- Loewner order is closed under sums over a finite type. -/
theorem finiteLoewnerLe_fintype_sum
    {ι α : Type*} [Fintype ι] [Fintype α]
    {M N : α → ι → ι → ℝ}
    (hMN : ∀ a : α, finiteLoewnerLe (M a) (N a)) :
    finiteLoewnerLe (fun i j => ∑ a : α, M a i j)
      (fun i j => ∑ a : α, N a i j) := by
  intro x
  rw [finiteQuadraticForm_fintype_sum,
    finiteQuadraticForm_fintype_sum]
  exact Finset.sum_le_sum fun a _ => hMN a x

/-- Loewner order is closed under nonnegative weighted finite sums. -/
theorem finiteLoewnerLe_fintype_sum_smul_of_nonneg
    {ι α : Type*} [Fintype ι] [Fintype α]
    (w : α → ℝ) {M N : α → ι → ι → ℝ}
    (hw : ∀ a : α, 0 ≤ w a)
    (hMN : ∀ a : α, finiteLoewnerLe (M a) (N a)) :
    finiteLoewnerLe (fun i j => ∑ a : α, w a * M a i j)
      (fun i j => ∑ a : α, w a * N a i j) := by
  intro x
  rw [finiteQuadraticForm_fintype_sum_smul,
    finiteQuadraticForm_fintype_sum_smul]
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (hMN a x) (hw a)

/-- A finite sum of positive-semidefinite matrices is positive semidefinite. -/
theorem finitePSD_fintype_sum_of_finitePSD
    {ι α : Type*} [Fintype ι] [Fintype α]
    (M : α → ι → ι → ℝ) (hM : ∀ a : α, finitePSD (M a)) :
    finitePSD (fun i j => ∑ a : α, M a i j) := by
  intro x
  rw [finiteQuadraticForm_fintype_sum]
  exact Finset.sum_nonneg fun a _ => hM a x

/-- A nonnegative weighted finite sum of positive-semidefinite matrices is
    positive semidefinite. -/
theorem finitePSD_fintype_sum_smul_of_nonneg
    {ι α : Type*} [Fintype ι] [Fintype α]
    (w : α → ℝ) (M : α → ι → ι → ℝ)
    (hw : ∀ a : α, 0 ≤ w a) (hM : ∀ a : α, finitePSD (M a)) :
    finitePSD (fun i j => ∑ a : α, w a * M a i j) := by
  intro x
  rw [finiteQuadraticForm_fintype_sum_smul]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (hM a x)

/-- Positive-semidefinite finite matrices have nonnegative trace. -/
theorem finiteTrace_nonneg_of_finitePSD {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : ι → ι → ℝ) (hM : finitePSD M) :
    0 ≤ finiteTrace M := by
  unfold finiteTrace
  exact Finset.sum_nonneg fun i _ => by
    simpa [finiteQuadraticForm_finiteBasisVec] using
      hM (finiteBasisVec i)

/-- Finite trace is monotone for the repository-native Loewner order. -/
theorem finiteTrace_mono_of_finiteLoewnerLe {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M N : ι → ι → ℝ}
    (hMN : finiteLoewnerLe M N) :
    finiteTrace M ≤ finiteTrace N := by
  have hdiff : finitePSD (fun i j => N i j - M i j) :=
    (finiteLoewnerLe_iff_sub_finitePSD M N).mp hMN
  have htrace_nonneg :=
    finiteTrace_nonneg_of_finitePSD (fun i j => N i j - M i j) hdiff
  rw [finiteTrace_sub] at htrace_nonneg
  linarith

/-- A scalar-identity Loewner upper bound gives the corresponding trace bound
    with the finite dimension made explicit. -/
theorem finiteTrace_le_of_finiteLoewnerLe_smul_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) {a : ℝ}
    (hM : finiteLoewnerLe M (fun i j => a * finiteIdMatrix i j)) :
    finiteTrace M ≤ a * (Fintype.card ι : ℝ) := by
  have htrace := finiteTrace_mono_of_finiteLoewnerLe hM
  rw [finiteTrace_smul_finiteIdMatrix] at htrace
  exact htrace

/-- Two-sided scalar Loewner bounds imply an absolute quadratic-form bound. -/
theorem abs_finiteQuadraticForm_le_of_loewnerLe_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) {t : ℝ}
    (hupper :
      finiteLoewnerLe M (fun i j => t * finiteIdMatrix i j))
    (hlower :
      finiteLoewnerLe (fun i j => -M i j)
        (fun i j => t * finiteIdMatrix i j))
    (x : ι → ℝ) :
    |finiteQuadraticForm M x| ≤ t * finiteVecNorm2Sq x := by
  have hu := hupper x
  have hl := hlower x
  rw [finiteQuadraticForm_smul_finiteIdMatrix] at hu
  rw [finiteQuadraticForm_neg, finiteQuadraticForm_smul_finiteIdMatrix] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- Generic finite Cauchy--Schwarz for vector inner products. -/
theorem finiteVecInnerProduct_sq_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    (∑ i : ι, x i * y i) ^ 2 ≤
      finiteVecNorm2Sq x * finiteVecNorm2Sq y := by
  unfold finiteVecNorm2Sq
  exact Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset ι) x y

/-- Generic finite Cauchy--Schwarz in norm form. -/
theorem abs_finiteVecInnerProduct_le_finiteVecNorm2_mul
    {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    |∑ i : ι, x i * y i| ≤ finiteVecNorm2 x * finiteVecNorm2 y := by
  have hsq := finiteVecInnerProduct_sq_le x y
  have hprod_nonneg : 0 ≤ finiteVecNorm2 x * finiteVecNorm2 y :=
    mul_nonneg (finiteVecNorm2_nonneg x) (finiteVecNorm2_nonneg y)
  have hrewrite :
      finiteVecNorm2Sq x * finiteVecNorm2Sq y =
        (finiteVecNorm2 x * finiteVecNorm2 y) ^ 2 := by
    rw [show (finiteVecNorm2 x * finiteVecNorm2 y) ^ 2 =
        finiteVecNorm2 x ^ 2 * finiteVecNorm2 y ^ 2 from by ring,
      finiteVecNorm2_sq, finiteVecNorm2_sq]
  rw [hrewrite] at hsq
  have hupper :
      ∑ i : ι, x i * y i ≤ finiteVecNorm2 x * finiteVecNorm2 y := by
    nlinarith [sq_abs (∑ i : ι, x i * y i)]
  have hlower :
      -(finiteVecNorm2 x * finiteVecNorm2 y) ≤
        ∑ i : ι, x i * y i := by
    nlinarith [sq_abs (∑ i : ι, x i * y i)]
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Generic finite Euclidean vector triangle inequality. -/
theorem finiteVecNorm2_add_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    finiteVecNorm2 (fun i => x i + y i) ≤
      finiteVecNorm2 x + finiteVecNorm2 y := by
  have hnn : 0 ≤ finiteVecNorm2 x + finiteVecNorm2 y :=
    add_nonneg (finiteVecNorm2_nonneg x) (finiteVecNorm2_nonneg y)
  rw [← Real.sqrt_sq hnn]
  apply Real.sqrt_le_sqrt
  have hexp : finiteVecNorm2Sq (fun i => x i + y i) =
      finiteVecNorm2Sq x + 2 * (∑ i : ι, x i * y i) +
        finiteVecNorm2Sq y := by
    unfold finiteVecNorm2Sq
    simp_rw [show ∀ i : ι, (x i + y i) ^ 2 =
        x i ^ 2 + 2 * (x i * y i) + y i ^ 2 from fun i => by ring,
      Finset.sum_add_distrib]
    rw [show ∑ i : ι, 2 * (x i * y i) =
        2 * ∑ i : ι, x i * y i from by rw [Finset.mul_sum]]
  rw [hexp, show (finiteVecNorm2 x + finiteVecNorm2 y) ^ 2 =
      finiteVecNorm2 x ^ 2 + 2 * (finiteVecNorm2 x * finiteVecNorm2 y) +
        finiteVecNorm2 y ^ 2 from by ring,
    finiteVecNorm2_sq, finiteVecNorm2_sq]
  have hinner := finiteVecInnerProduct_sq_le x y
  have hinner_le :
      ∑ i : ι, x i * y i ≤ finiteVecNorm2 x * finiteVecNorm2 y := by
    have hprod_nonneg : 0 ≤ finiteVecNorm2 x * finiteVecNorm2 y :=
      mul_nonneg (finiteVecNorm2_nonneg x) (finiteVecNorm2_nonneg y)
    rw [show finiteVecNorm2Sq x * finiteVecNorm2Sq y =
        (finiteVecNorm2 x * finiteVecNorm2 y) ^ 2 from by
      rw [show (finiteVecNorm2 x * finiteVecNorm2 y) ^ 2 =
          finiteVecNorm2 x ^ 2 * finiteVecNorm2 y ^ 2 from by ring,
        finiteVecNorm2_sq, finiteVecNorm2_sq]] at hinner
    have habs := (sq_le_sq).mp hinner
    exact (le_abs_self (∑ i : ι, x i * y i)).trans
      (by simpa [abs_of_nonneg hprod_nonneg] using habs)
  linarith

/-- A generic finite operator-2 bound controls the quadratic form `xᵀMx`. -/
theorem abs_finiteVecInnerProduct_finiteMatVec_le_of_finiteOpNorm2Le
    {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) {c : ℝ} (hM : finiteOpNorm2Le M c)
    (x : ι → ℝ) :
    |∑ i : ι, x i * finiteMatVec M x i| ≤ c * finiteVecNorm2Sq x := by
  calc
    |∑ i : ι, x i * finiteMatVec M x i|
        ≤ finiteVecNorm2 x * finiteVecNorm2 (finiteMatVec M x) :=
          abs_finiteVecInnerProduct_le_finiteVecNorm2_mul x (finiteMatVec M x)
    _ ≤ finiteVecNorm2 x * (c * finiteVecNorm2 x) :=
          mul_le_mul_of_nonneg_left (hM x) (finiteVecNorm2_nonneg x)
    _ = c * finiteVecNorm2Sq x := by
          rw [← finiteVecNorm2_sq]
          ring

/-- A generic finite operator-2 bound controls mixed bilinear forms
`xᵀ M y`. -/
theorem abs_finiteVecInnerProduct_finiteMatVec_two_le_of_finiteOpNorm2Le
    {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) {c : ℝ} (hM : finiteOpNorm2Le M c)
    (x y : ι → ℝ) :
    |∑ i : ι, x i * finiteMatVec M y i| ≤
      c * finiteVecNorm2 x * finiteVecNorm2 y := by
  calc
    |∑ i : ι, x i * finiteMatVec M y i|
        ≤ finiteVecNorm2 x * finiteVecNorm2 (finiteMatVec M y) :=
          abs_finiteVecInnerProduct_le_finiteVecNorm2_mul x (finiteMatVec M y)
    _ ≤ finiteVecNorm2 x * (c * finiteVecNorm2 y) :=
          mul_le_mul_of_nonneg_left (hM y) (finiteVecNorm2_nonneg x)
    _ = c * finiteVecNorm2 x * finiteVecNorm2 y := by ring

/-- Operator-2 control stated directly for the quadratic-form notation. -/
theorem abs_finiteQuadraticForm_le_of_finiteOpNorm2Le
    {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) {c : ℝ} (hM : finiteOpNorm2Le M c)
    (x : ι → ℝ) :
    |finiteQuadraticForm M x| ≤ c * finiteVecNorm2Sq x := by
  simpa [finiteQuadraticForm] using
    abs_finiteVecInnerProduct_finiteMatVec_le_of_finiteOpNorm2Le
      M hM x

/-- One-sided quadratic-form control from a generic finite operator-2 bound. -/
theorem finiteQuadraticForm_le_of_finiteOpNorm2Le
    {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) {c : ℝ} (hM : finiteOpNorm2Le M c)
    (x : ι → ℝ) :
    finiteQuadraticForm M x ≤ c * finiteVecNorm2Sq x := by
  exact (le_abs_self (finiteQuadraticForm M x)).trans
    (abs_finiteQuadraticForm_le_of_finiteOpNorm2Le M hM x)

/-- A vector-action operator-2 bound gives the corresponding one-sided
    scalar-identity Loewner upper bound.  This is the shape used by
    largest-eigenvalue Bernstein hypotheses. -/
theorem finiteLoewnerLe_smul_id_of_finiteOpNorm2Le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) {c : ℝ} (hM : finiteOpNorm2Le M c) :
    finiteLoewnerLe M (fun i j => c * finiteIdMatrix i j) := by
  intro x
  rw [finiteQuadraticForm_smul_finiteIdMatrix]
  exact finiteQuadraticForm_le_of_finiteOpNorm2Le M hM x

/-- A vector-action operator-2 bound also gives the lower Loewner side,
    written as `-M <= c I`. -/
theorem finiteLoewnerLe_neg_smul_id_of_finiteOpNorm2Le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) {c : ℝ} (hM : finiteOpNorm2Le M c) :
    finiteLoewnerLe (fun i j => -M i j)
      (fun i j => c * finiteIdMatrix i j) := by
  intro x
  rw [finiteQuadraticForm_neg, finiteQuadraticForm_smul_finiteIdMatrix]
  exact (neg_le_abs (finiteQuadraticForm M x)).trans
    (abs_finiteQuadraticForm_le_of_finiteOpNorm2Le M hM x)

/-- Generic symmetry predicate for finite real matrices. -/
def IsSymmetricFiniteMatrix {ι : Type*} (M : ι → ι → ℝ) : Prop :=
  ∀ i j, M i j = M j i

/-- The repository-native symmetry predicate is the same symmetry notion as
    mathlib's matrix symmetry predicate.  This bridge is intentionally tiny: it
    lets future spectral/exponential matrix results from mathlib be applied to
    local finite matrices without changing the repository's existing matrix API. -/
theorem IsSymmetricFiniteMatrix.to_matrix_isSymm {ι : Type*}
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    Matrix.IsSymm (M : Matrix ι ι ℝ) := by
  exact Matrix.IsSymm.ext (fun i j => hM j i)

/-- Converse bridge from mathlib's matrix symmetry predicate back to the
    repository-native finite-matrix symmetry predicate. -/
theorem Matrix_isSymm.to_IsSymmetricFiniteMatrix {ι : Type*}
    (M : ι → ι → ℝ) (hM : Matrix.IsSymm (M : Matrix ι ι ℝ)) :
    IsSymmetricFiniteMatrix M := by
  intro i j
  exact Matrix.IsSymm.apply hM j i

/-- The repository-native symmetry predicate also gives mathlib Hermitian
    symmetry for real matrices, which is the entry point for mathlib's spectral
    theorem and eigenvalue API. -/
theorem IsSymmetricFiniteMatrix.to_matrix_isHermitian {ι : Type*}
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    Matrix.IsHermitian (M : Matrix ι ι ℝ) := by
  apply Matrix.IsHermitian.ext
  intro i j
  simpa using (hM i j).symm

/-- Converse bridge from mathlib Hermitian real matrices back to the
    repository-native finite-matrix symmetry predicate. -/
theorem Matrix_isHermitian.to_IsSymmetricFiniteMatrix {ι : Type*}
    (M : ι → ι → ℝ) (hM : Matrix.IsHermitian (M : Matrix ι ι ℝ)) :
    IsSymmetricFiniteMatrix M := by
  intro i j
  simpa using (Matrix.IsHermitian.apply hM i j).symm

/-- The repository nonsingular-inverse table preserves symmetry.  This is an
exact algebra bridge for certificate-style arguments: it says nothing about
whether the matrix is actually nonsingular, but when a separate determinant or
inverse certificate is available, the same `nonsingInv` candidate has the
expected symmetric table. -/
theorem nonsingInv_symmetric_of_symmetric {n : ℕ}
    (T : Fin n → Fin n → ℝ)
    (hT : IsSymmetricFiniteMatrix T) :
    IsSymmetricFiniteMatrix (nonsingInv n T) := by
  intro i j
  let M : Matrix (Fin n) (Fin n) ℝ := T
  have hMT : M.transpose = M := by
    ext a b
    exact hT b a
  calc
    nonsingInv n T i j = (M⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j := by
      rfl
    _ = (M⁻¹ : Matrix (Fin n) (Fin n) ℝ).transpose j i := by
      rfl
    _ = (M.transpose⁻¹ : Matrix (Fin n) (Fin n) ℝ) j i := by
      rw [Matrix.transpose_nonsing_inv]
    _ = (M⁻¹ : Matrix (Fin n) (Fin n) ℝ) j i := by
      rw [hMT]
    _ = nonsingInv n T j i := by
      rfl

/-- Bridge from the repository-native finite quadratic-form PSD predicate to
    mathlib's `Matrix.PosSemidef` predicate.  The local predicate stores only
    quadratic-form nonnegativity, so symmetry is supplied explicitly. -/
theorem finitePSD.to_matrix_posSemidef {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (hMsym : IsSymmetricFiniteMatrix M) (hM : finitePSD M) :
    Matrix.PosSemidef (M : Matrix ι ι ℝ) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa using (hMsym i j).symm
  · intro x
    have h := hM (fun i => x i)
    unfold finiteQuadraticForm finiteMatVec at h
    have hsum :
        (∑ i : ι, x i * ∑ j : ι, M i j * x j) =
          ∑ i : ι, ∑ j : ι, x i * M i j * x j := by
      simp [Finset.mul_sum, mul_assoc]
    simpa [Finsupp.sum_fintype, hsum] using h

/-- Converse bridge from mathlib's `Matrix.PosSemidef` predicate back to the
    repository-native finite quadratic-form PSD predicate. -/
theorem Matrix_posSemidef.to_finitePSD {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (hM : Matrix.PosSemidef (M : Matrix ι ι ℝ)) :
    finitePSD M := by
  intro x
  have h := hM.2 (Finsupp.equivFunOnFinite.symm x)
  unfold finiteQuadraticForm finiteMatVec
  have hsum :
      (∑ i : ι, x i * ∑ j : ι, M i j * x j) =
        ∑ i : ι, ∑ j : ι, x i * M i j * x j := by
    simp [Finset.mul_sum, mul_assoc]
  rw [hsum]
  simpa [Finsupp.sum_fintype] using h

/-- Equivalence between the local finite PSD predicate and mathlib's PSD
    predicate for a locally symmetric real matrix. -/
theorem finitePSD_iff_matrix_posSemidef_of_symmetric {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (hMsym : IsSymmetricFiniteMatrix M) :
    finitePSD M ↔ Matrix.PosSemidef (M : Matrix ι ι ℝ) :=
  ⟨finitePSD.to_matrix_posSemidef M hMsym,
    Matrix_posSemidef.to_finitePSD M⟩

/-- A local finite Loewner bound gives a mathlib positive-semidefinite
    difference matrix, provided both sides are locally symmetric. -/
theorem finiteLoewnerLe.to_matrix_posSemidef_sub {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ)
    (hMsym : IsSymmetricFiniteMatrix M) (hNsym : IsSymmetricFiniteMatrix N)
    (hMN : finiteLoewnerLe M N) :
    Matrix.PosSemidef ((fun i j => N i j - M i j) : Matrix ι ι ℝ) := by
  apply finitePSD.to_matrix_posSemidef
  · intro i j
    change N i j - M i j = N j i - M j i
    rw [hNsym i j, hMsym i j]
  · exact (finiteLoewnerLe_iff_sub_finitePSD M N).mp hMN

/-- Conversely, a mathlib positive-semidefinite difference matrix gives the
    repository-native finite Loewner bound. -/
theorem Matrix_posSemidef_sub.to_finiteLoewnerLe {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ)
    (hMN : Matrix.PosSemidef ((fun i j => N i j - M i j) : Matrix ι ι ℝ)) :
    finiteLoewnerLe M N :=
  (finiteLoewnerLe_iff_sub_finitePSD M N).mpr
    (Matrix_posSemidef.to_finitePSD (fun i j => N i j - M i j) hMN)

/-- Equivalence between the local finite Loewner predicate and mathlib's PSD
    difference predicate for locally symmetric real matrices. -/
theorem finiteLoewnerLe_iff_matrix_posSemidef_sub_of_symmetric
    {ι : Type*} [Fintype ι]
    (M N : ι → ι → ℝ)
    (hMsym : IsSymmetricFiniteMatrix M) (hNsym : IsSymmetricFiniteMatrix N) :
    finiteLoewnerLe M N ↔
      Matrix.PosSemidef ((fun i j => N i j - M i j) : Matrix ι ι ℝ) :=
  ⟨finiteLoewnerLe.to_matrix_posSemidef_sub M N hMsym hNsym,
    Matrix_posSemidef_sub.to_finiteLoewnerLe M N⟩

/-- Moving a matrix-vector product across a finite inner product introduces a
    transpose. -/
theorem finiteVecInnerProduct_finiteMatVec_eq_transpose
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    (∑ i : ι, x i * finiteMatVec M y i) =
      ∑ j : κ, finiteMatVec (finiteTranspose M) x j * y j := by
  classical
  unfold finiteMatVec finiteTranspose
  calc
    (∑ i : ι, x i * ∑ j : κ, M i j * y j)
        = ∑ i : ι, ∑ j : κ, x i * (M i j * y j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ j : κ, ∑ i : ι, x i * (M i j * y j) := by
            rw [Finset.sum_comm]
    _ = ∑ j : κ, (∑ i : ι, M i j * x i) * y j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- A symmetric finite matrix can be moved across an inner product without
    changing the matrix. -/
theorem finiteVecInnerProduct_finiteMatVec_left_eq_right_of_symmetric
    {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (hM : IsSymmetricFiniteMatrix M) (x y : ι → ℝ) :
    (∑ i : ι, x i * finiteMatVec M y i) =
      ∑ i : ι, finiteMatVec M x i * y i := by
  classical
  calc
    (∑ i : ι, x i * finiteMatVec M y i)
        = ∑ j : ι, finiteMatVec (finiteTranspose M) x j * y j :=
            finiteVecInnerProduct_finiteMatVec_eq_transpose M x y
    _ = ∑ j : ι, finiteMatVec M x j * y j := by
            apply Finset.sum_congr rfl
            intro j _
            have hvec :
                finiteMatVec (finiteTranspose M) x j =
                  finiteMatVec M x j := by
              unfold finiteMatVec finiteTranspose
              apply Finset.sum_congr rfl
              intro i _
              rw [hM i j]
            rw [hvec]

/-- The quadratic form of `M * M` for a symmetric finite matrix is the
    squared norm of `Mx`. -/
theorem finiteQuadraticForm_finiteMatMul_self_of_symmetric
    {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (hM : IsSymmetricFiniteMatrix M) (x : ι → ℝ) :
    finiteQuadraticForm (finiteMatMul M M) x =
      finiteVecNorm2Sq (finiteMatVec M x) := by
  unfold finiteQuadraticForm
  rw [finiteMatVec_finiteMatMul]
  rw [finiteVecInnerProduct_finiteMatVec_left_eq_right_of_symmetric
    M hM x (finiteMatVec M x)]
  unfold finiteVecNorm2Sq
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A symmetric idempotent finite matrix is nonexpansive in the Euclidean
norm.  This is the finite-dimensional orthogonal-projector contraction used by
the RandNLA equation-(9) coupling-tail surface. -/
theorem finiteVecNorm2_finiteMatVec_le_of_symmetric_idempotent
    {ι : Type*} [Fintype ι] (P : ι → ι → ℝ)
    (hSym : IsSymmetricFiniteMatrix P)
    (hIdem : ∀ i j, finiteMatMul P P i j = P i j)
    (x : ι → ℝ) :
    finiteVecNorm2 (finiteMatVec P x) ≤ finiteVecNorm2 x := by
  let y : ι → ℝ := finiteMatVec P x
  have hPP : finiteMatMul P P = P := by
    funext i j
    exact hIdem i j
  have hinner :
      finiteVecNorm2Sq y = ∑ i : ι, x i * y i := by
    calc
      finiteVecNorm2Sq y =
          finiteQuadraticForm (finiteMatMul P P) x :=
            (finiteQuadraticForm_finiteMatMul_self_of_symmetric P hSym x).symm
      _ = finiteQuadraticForm P x := by rw [hPP]
      _ = ∑ i : ι, x i * y i := rfl
  have hsq_le :
      finiteVecNorm2 y ^ 2 ≤ finiteVecNorm2 x * finiteVecNorm2 y := by
    calc
      finiteVecNorm2 y ^ 2 = ∑ i : ι, x i * y i := by
        rw [finiteVecNorm2_sq, hinner]
      _ ≤ |∑ i : ι, x i * y i| := le_abs_self _
      _ ≤ finiteVecNorm2 x * finiteVecNorm2 y :=
        abs_finiteVecInnerProduct_le_finiteVecNorm2_mul x y
  by_cases hy : finiteVecNorm2 y = 0
  · rw [hy]
    exact finiteVecNorm2_nonneg x
  · have hypos : 0 < finiteVecNorm2 y :=
      lt_of_le_of_ne (finiteVecNorm2_nonneg y) (Ne.symm hy)
    have hmul :
        finiteVecNorm2 y * finiteVecNorm2 y ≤
          finiteVecNorm2 x * finiteVecNorm2 y := by
      simpa [pow_two] using hsq_le
    exact (mul_le_mul_iff_of_pos_right hypos).mp hmul

/-- Squared-norm form of symmetric-idempotent nonexpansiveness. -/
theorem finiteVecNorm2Sq_finiteMatVec_le_of_symmetric_idempotent
    {ι : Type*} [Fintype ι] (P : ι → ι → ℝ)
    (hSym : IsSymmetricFiniteMatrix P)
    (hIdem : ∀ i j, finiteMatMul P P i j = P i j)
    (x : ι → ℝ) :
    finiteVecNorm2Sq (finiteMatVec P x) ≤ finiteVecNorm2Sq x := by
  have hnorm :=
    finiteVecNorm2_finiteMatVec_le_of_symmetric_idempotent P hSym hIdem x
  have hsquare :
      finiteVecNorm2 (finiteMatVec P x) ^ 2 ≤ finiteVecNorm2 x ^ 2 := by
    nlinarith [finiteVecNorm2_nonneg (finiteMatVec P x),
      finiteVecNorm2_nonneg x]
  simpa [finiteVecNorm2_sq] using hsquare

/-- The square of a symmetric finite matrix is symmetric. -/
theorem finiteMatMul_self_symmetric_of_symmetric
    {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (hM : IsSymmetricFiniteMatrix M) :
    IsSymmetricFiniteMatrix (finiteMatMul M M) := by
  intro i j
  unfold finiteMatMul
  apply Finset.sum_congr rfl
  intro k _
  rw [hM i k, hM k j]
  ring

/-- A finite weighted sum of symmetric matrices is symmetric. -/
theorem IsSymmetricFiniteMatrix.sum_smul
    {α ι : Type*} [Fintype α] [Fintype ι]
    (w : α → ℝ) (M : α → ι → ι → ℝ)
    (hM : ∀ a, IsSymmetricFiniteMatrix (M a)) :
    IsSymmetricFiniteMatrix (fun i j => ∑ a : α, w a * M a i j) := by
  intro i j
  apply Finset.sum_congr rfl
  intro a _
  rw [hM a i j]

/-- The square of a symmetric finite matrix is positive semidefinite. -/
theorem finitePSD_finiteMatMul_self_of_symmetric
    {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (hM : IsSymmetricFiniteMatrix M) :
    finitePSD (finiteMatMul M M) := by
  intro x
  rw [finiteQuadraticForm_finiteMatMul_self_of_symmetric M hM]
  exact finiteVecNorm2Sq_nonneg (finiteMatVec M x)

/-- The square of a symmetric finite matrix has quadratic form bounded by the
    squared Frobenius norm times `||x||₂²`. -/
theorem finiteQuadraticForm_finiteMatMul_self_le_finiteFrobNormSq_mul_of_symmetric
    {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (hM : IsSymmetricFiniteMatrix M) (x : ι → ℝ) :
    finiteQuadraticForm (finiteMatMul M M) x ≤
      finiteFrobNormSq M * finiteVecNorm2Sq x := by
  rw [finiteQuadraticForm_finiteMatMul_self_of_symmetric M hM]
  exact finiteVecNorm2Sq_finiteMatVec_le_finiteFrobNormSq_mul M x

/-- An operator-2 bound on a symmetric finite matrix gives the quadratic
    Loewner bound `M^2 <= L^2 I`.  This is a deterministic building block for
    Bernstein-style bounded-increment and variance-proxy assumptions. -/
theorem finiteMatMul_self_loewnerLe_scalar_id_of_finiteOpNorm2Le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) {L : ℝ}
    (hSym : IsSymmetricFiniteMatrix M)
    (hM : finiteOpNorm2Le M L) (hL : 0 ≤ L) :
    finiteLoewnerLe (finiteMatMul M M)
      (fun i j => L ^ 2 * finiteIdMatrix i j) := by
  intro x
  rw [finiteQuadraticForm_finiteMatMul_self_of_symmetric M hSym x,
    finiteQuadraticForm_smul_finiteIdMatrix]
  have hnorm := hM x
  have hright_nonneg : 0 ≤ L * finiteVecNorm2 x :=
    mul_nonneg hL (finiteVecNorm2_nonneg x)
  have hsquare :
      finiteVecNorm2 (finiteMatVec M x) ^ 2 ≤
        (L * finiteVecNorm2 x) ^ 2 := by
    nlinarith [finiteVecNorm2_nonneg (finiteMatVec M x), hright_nonneg]
  rw [finiteVecNorm2_sq] at hsquare
  have hright :
      (L * finiteVecNorm2 x) ^ 2 = L ^ 2 * finiteVecNorm2Sq x := by
    rw [show (L * finiteVecNorm2 x) ^ 2 =
        L ^ 2 * finiteVecNorm2 x ^ 2 from by ring,
      finiteVecNorm2_sq]
  simpa [hright] using hsquare

/-- An operator-2 bound on a symmetric finite matrix bounds the trace of its
    square by `dimension * L^2`. -/
theorem finiteTrace_finiteMatMul_self_le_card_mul_sq_of_finiteOpNorm2Le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) {L : ℝ}
    (hSym : IsSymmetricFiniteMatrix M)
    (hM : finiteOpNorm2Le M L) (hL : 0 ≤ L) :
    finiteTrace (finiteMatMul M M) ≤
      L ^ 2 * (Fintype.card ι : ℝ) := by
  exact finiteTrace_le_of_finiteLoewnerLe_smul_id
    (finiteMatMul M M)
    (finiteMatMul_self_loewnerLe_scalar_id_of_finiteOpNorm2Le
      M hSym hM hL)

/-- A squared Loewner bound on a symmetric finite matrix gives the vector-action
    operator-2 bound.  This is the deterministic conversion used when a matrix
    concentration theorem is stated as `M^2 <= L^2 I` rather than directly as an
    operator-norm event. -/
theorem finiteOpNorm2Le_of_finiteMatMul_self_loewnerLe_scalar_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) {L : ℝ}
    (hSym : IsSymmetricFiniteMatrix M) (hL : 0 ≤ L)
    (hLoewner :
      finiteLoewnerLe (finiteMatMul M M)
        (fun i j => L ^ 2 * finiteIdMatrix i j)) :
    finiteOpNorm2Le M L := by
  intro x
  have hquad := hLoewner x
  rw [finiteQuadraticForm_finiteMatMul_self_of_symmetric M hSym x,
    finiteQuadraticForm_smul_finiteIdMatrix] at hquad
  have hright :
      (L * finiteVecNorm2 x) ^ 2 = L ^ 2 * finiteVecNorm2Sq x := by
    rw [show (L * finiteVecNorm2 x) ^ 2 =
        L ^ 2 * finiteVecNorm2 x ^ 2 from by ring,
      finiteVecNorm2_sq]
  have hsquare :
      finiteVecNorm2 (finiteMatVec M x) ^ 2 ≤
        (L * finiteVecNorm2 x) ^ 2 := by
    rw [finiteVecNorm2_sq, hright]
    exact hquad
  have hleft_nonneg : 0 ≤ finiteVecNorm2 (finiteMatVec M x) :=
    finiteVecNorm2_nonneg (finiteMatVec M x)
  have hright_nonneg : 0 ≤ L * finiteVecNorm2 x :=
    mul_nonneg hL (finiteVecNorm2_nonneg x)
  have habs := (sq_le_sq).mp hsquare
  simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs

/-- The finite-type norm specializes to the `Fin n` vector norm. -/
lemma finiteVecNorm2Sq_fin {n : ℕ} (x : Fin n → ℝ) :
    finiteVecNorm2Sq x = vecNorm2Sq x := rfl

/-- The finite-type norm specializes to the `Fin n` vector norm. -/
lemma finiteVecNorm2_fin {n : ℕ} (x : Fin n → ℝ) :
    finiteVecNorm2 x = vecNorm2 x := rfl

/-- Left embedding of a vector into a sum-indexed vector. -/
noncomputable def sumInlVec {α β : Type*} (x : α → ℝ) :
    α ⊕ β → ℝ :=
  Sum.elim x (fun _ => 0)

/-- Right embedding of a vector into a sum-indexed vector. -/
noncomputable def sumInrVec {α β : Type*} (y : β → ℝ) :
    α ⊕ β → ℝ :=
  Sum.elim (fun _ => 0) y

/-- Pair a left and right vector into one sum-indexed vector. -/
noncomputable def sumBothVec {α β : Type*} (x : α → ℝ) (y : β → ℝ) :
    α ⊕ β → ℝ :=
  Sum.elim x y

/-- The squared norm of a left sum embedding is the original squared norm. -/
lemma finiteVecNorm2Sq_sumInlVec {α β : Type*} [Fintype α] [Fintype β]
    (x : α → ℝ) :
    finiteVecNorm2Sq (sumInlVec (β := β) x) = finiteVecNorm2Sq x := by
  unfold finiteVecNorm2Sq sumInlVec
  rw [Fintype.sum_sum_type]
  simp

/-- The squared norm of a right sum embedding is the original squared norm. -/
lemma finiteVecNorm2Sq_sumInrVec {α β : Type*} [Fintype α] [Fintype β]
    (y : β → ℝ) :
    finiteVecNorm2Sq (sumInrVec (α := α) y) = finiteVecNorm2Sq y := by
  unfold finiteVecNorm2Sq sumInrVec
  rw [Fintype.sum_sum_type]
  simp

/-- The norm of a left sum embedding is the original norm. -/
lemma finiteVecNorm2_sumInlVec {α β : Type*} [Fintype α] [Fintype β]
    (x : α → ℝ) :
    finiteVecNorm2 (sumInlVec (β := β) x) = finiteVecNorm2 x := by
  unfold finiteVecNorm2
  rw [finiteVecNorm2Sq_sumInlVec]

/-- The norm of a right sum embedding is the original norm. -/
lemma finiteVecNorm2_sumInrVec {α β : Type*} [Fintype α] [Fintype β]
    (y : β → ℝ) :
    finiteVecNorm2 (sumInrVec (α := α) y) = finiteVecNorm2 y := by
  unfold finiteVecNorm2
  rw [finiteVecNorm2Sq_sumInrVec]

/-- The squared norm of a paired sum vector is the sum of squared norms. -/
lemma finiteVecNorm2Sq_sumBothVec {α β : Type*} [Fintype α] [Fintype β]
    (x : α → ℝ) (y : β → ℝ) :
    finiteVecNorm2Sq (sumBothVec x y) =
      finiteVecNorm2Sq x + finiteVecNorm2Sq y := by
  unfold finiteVecNorm2Sq sumBothVec
  rw [Fintype.sum_sum_type]
  simp

/-- Finite Cauchy--Schwarz for the Euclidean vector inner product. -/
theorem vecInnerProduct_sq_le {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, x i * y i) ^ 2 ≤ vecNorm2Sq x * vecNorm2Sq y := by
  unfold vecNorm2Sq
  exact Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin n)) x y

/-- Cauchy--Schwarz in norm form for the Euclidean vector inner product. -/
theorem abs_vecInnerProduct_le_vecNorm2_mul {n : ℕ} (x y : Fin n → ℝ) :
    |∑ i : Fin n, x i * y i| ≤ vecNorm2 x * vecNorm2 y := by
  have hsq := vecInnerProduct_sq_le x y
  have hprod_nonneg : 0 ≤ vecNorm2 x * vecNorm2 y :=
    mul_nonneg (vecNorm2_nonneg x) (vecNorm2_nonneg y)
  have hrewrite :
      vecNorm2Sq x * vecNorm2Sq y = (vecNorm2 x * vecNorm2 y) ^ 2 := by
    rw [show (vecNorm2 x * vecNorm2 y) ^ 2 =
        vecNorm2 x ^ 2 * vecNorm2 y ^ 2 from by ring,
      vecNorm2_sq, vecNorm2_sq]
  rw [hrewrite] at hsq
  have hupper : ∑ i : Fin n, x i * y i ≤ vecNorm2 x * vecNorm2 y := by
    nlinarith [sq_abs (∑ i : Fin n, x i * y i)]
  have hlower : -(vecNorm2 x * vecNorm2 y) ≤
      ∑ i : Fin n, x i * y i := by
    nlinarith [sq_abs (∑ i : Fin n, x i * y i)]
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- A positive Euclidean norm normalizes a vector to unit norm. -/
theorem vecNorm2_inv_smul_self_of_pos {n : ℕ} (x : Fin n → ℝ)
    (hx : 0 < vecNorm2 x) :
    vecNorm2 (fun i => (vecNorm2 x)⁻¹ * x i) = 1 := by
  rw [vecNorm2_smul, abs_of_pos (inv_pos.mpr hx),
    inv_mul_cancel₀ (ne_of_gt hx)]

/-- The normalized vector has inner product equal to the original norm. -/
theorem vecInnerProduct_inv_smul_self_eq_norm {n : ℕ} (x : Fin n → ℝ)
    (hx : 0 < vecNorm2 x) :
    (∑ i : Fin n, ((vecNorm2 x)⁻¹ * x i) * x i) = vecNorm2 x := by
  calc
    (∑ i : Fin n, ((vecNorm2 x)⁻¹ * x i) * x i)
        = (vecNorm2 x)⁻¹ * ∑ i : Fin n, x i ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (vecNorm2 x)⁻¹ * vecNorm2Sq x := rfl
    _ = (vecNorm2 x)⁻¹ * (vecNorm2 x) ^ 2 := by
            rw [← vecNorm2_sq]
    _ = vecNorm2 x := by
            field_simp [ne_of_gt hx]

/-- A unit support vector gives a supporting hyperplane inequality for the
Euclidean norm at `x`.

If `u` is unit length and has inner product `||x||₂` with `x`, then the
decrease in norm from `x` to `y` is bounded by the inner product with
`x - y`. This is the finite-vector norm support fact used in the SRHT
self-bounding proof. -/
theorem vecNorm2_sub_le_inner_unit_diff {n : ℕ}
    (x y u : Fin n → ℝ)
    (hu : vecNorm2 u = 1)
    (hux : (∑ i : Fin n, u i * x i) = vecNorm2 x) :
    vecNorm2 x - vecNorm2 y ≤
      ∑ i : Fin n, u i * (x i - y i) := by
  have hy_support :
      (∑ i : Fin n, u i * y i) ≤ vecNorm2 y := by
    have habs := abs_vecInnerProduct_le_vecNorm2_mul u y
    have hle_abs :
        (∑ i : Fin n, u i * y i) ≤
          |∑ i : Fin n, u i * y i| := le_abs_self _
    have habs' :
        |∑ i : Fin n, u i * y i| ≤ vecNorm2 y := by
      simpa [hu] using habs
    exact hle_abs.trans habs'
  calc
    vecNorm2 x - vecNorm2 y
        ≤ vecNorm2 x - ∑ i : Fin n, u i * y i :=
            sub_le_sub_left hy_support _
    _ = (∑ i : Fin n, u i * x i) -
          ∑ i : Fin n, u i * y i := by rw [hux]
    _ = ∑ i : Fin n, u i * (x i - y i) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring

/-- If each entry of `x` is bounded in absolute value by a nonnegative budget
    vector `b`, then the squared Euclidean norm of `x` is bounded by the squared
    Euclidean norm of `b`. -/
theorem vecNorm2Sq_le_of_abs_le {n : ℕ} (x b : Fin n → ℝ)
    (hxb : ∀ i : Fin n, |x i| ≤ b i) :
    vecNorm2Sq x ≤ vecNorm2Sq b := by
  unfold vecNorm2Sq
  apply Finset.sum_le_sum
  intro i _
  have hsq : |x i| ^ 2 ≤ b i ^ 2 := by
    nlinarith [hxb i, abs_nonneg (x i)]
  simpa [sq_abs] using hsq

/-- Norm monotonicity from an entrywise absolute-value budget. -/
theorem vecNorm2_le_of_abs_le {n : ℕ} (x b : Fin n → ℝ)
    (hxb : ∀ i : Fin n, |x i| ≤ b i) :
    vecNorm2 x ≤ vecNorm2 b := by
  unfold vecNorm2
  exact Real.sqrt_le_sqrt (vecNorm2Sq_le_of_abs_le x b hxb)

/-- Squared Euclidean objective perturbation:
    `||x+e||₂²` differs from `||x||₂²` by at most
    `2||x||₂||e||₂ + ||e||₂²`. -/
theorem abs_vecNorm2Sq_add_sub_le {n : ℕ} (x e : Fin n → ℝ) :
    |vecNorm2Sq (fun i => x i + e i) - vecNorm2Sq x| ≤
      2 * vecNorm2 x * vecNorm2 e + vecNorm2Sq e := by
  have hexp : vecNorm2Sq (fun i => x i + e i) =
      vecNorm2Sq x + 2 * (∑ i : Fin n, x i * e i) + vecNorm2Sq e := by
    unfold vecNorm2Sq
    simp_rw [show ∀ i : Fin n, (x i + e i) ^ 2 =
        x i ^ 2 + 2 * (x i * e i) + e i ^ 2 from fun i => by ring,
      Finset.sum_add_distrib]
    rw [show ∑ i : Fin n, 2 * (x i * e i) =
        2 * ∑ i : Fin n, x i * e i from by rw [Finset.mul_sum]]
  have hinner := abs_vecInnerProduct_le_vecNorm2_mul x e
  have he_nonneg : 0 ≤ vecNorm2Sq e := vecNorm2Sq_nonneg e
  calc
    |vecNorm2Sq (fun i => x i + e i) - vecNorm2Sq x|
        = |2 * (∑ i : Fin n, x i * e i) + vecNorm2Sq e| := by
            rw [hexp]
            congr 1
            ring
    _ ≤ |2 * (∑ i : Fin n, x i * e i)| + |vecNorm2Sq e| := by
            exact abs_add_le _ _
    _ = 2 * |∑ i : Fin n, x i * e i| + vecNorm2Sq e := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
              abs_of_nonneg he_nonneg]
    _ ≤ 2 * vecNorm2 x * vecNorm2 e + vecNorm2Sq e := by
            nlinarith [hinner]

/-- Euclidean vector triangle inequality. -/
theorem vecNorm2_add_le {n : ℕ} (x y : Fin n → ℝ) :
    vecNorm2 (fun i => x i + y i) ≤ vecNorm2 x + vecNorm2 y := by
  have hnn : 0 ≤ vecNorm2 x + vecNorm2 y :=
    add_nonneg (vecNorm2_nonneg x) (vecNorm2_nonneg y)
  rw [← Real.sqrt_sq hnn]
  apply Real.sqrt_le_sqrt
  have hexp : vecNorm2Sq (fun i => x i + y i) =
      vecNorm2Sq x + 2 * (∑ i : Fin n, x i * y i) + vecNorm2Sq y := by
    unfold vecNorm2Sq
    simp_rw [show ∀ i : Fin n, (x i + y i) ^ 2 =
        x i ^ 2 + 2 * (x i * y i) + y i ^ 2 from fun i => by ring,
      Finset.sum_add_distrib]
    rw [show ∑ i : Fin n, 2 * (x i * y i) =
        2 * ∑ i : Fin n, x i * y i from by rw [Finset.mul_sum]]
  rw [hexp, show (vecNorm2 x + vecNorm2 y) ^ 2 =
      vecNorm2 x ^ 2 + 2 * (vecNorm2 x * vecNorm2 y) + vecNorm2 y ^ 2 from by ring,
    vecNorm2_sq, vecNorm2_sq]
  have hinner := vecInnerProduct_sq_le x y
  have hprod_nonneg : 0 ≤ vecNorm2 x * vecNorm2 y :=
    mul_nonneg (vecNorm2_nonneg x) (vecNorm2_nonneg y)
  have hinner_le : ∑ i : Fin n, x i * y i ≤ vecNorm2 x * vecNorm2 y := by
    rw [show vecNorm2Sq x * vecNorm2Sq y =
        (vecNorm2 x * vecNorm2 y) ^ 2 from by
      rw [show (vecNorm2 x * vecNorm2 y) ^ 2 =
          vecNorm2 x ^ 2 * vecNorm2 y ^ 2 from by ring,
        vecNorm2_sq, vecNorm2_sq]] at hinner
    nlinarith [sq_abs (∑ i : Fin n, x i * y i)]
  linarith

/-- Convexity predicate for real-valued functions on repository finite vectors.

This local predicate avoids moving legacy `Fin n -> ℝ` algorithm statements
through Mathlib's bundled Euclidean-space API.  It is the finite-vector
convexity shape needed for the Rademacher convex-Lipschitz route. -/
def FiniteVecConvex {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (θ : ℝ) (x y : Fin n → ℝ), 0 ≤ θ → θ ≤ 1 →
    f (fun i => θ * x i + (1 - θ) * y i) ≤
      θ * f x + (1 - θ) * f y

/-- Lipschitz predicate for repository finite vectors, stated using the local
Euclidean norm wrapper. -/
def FiniteVecLipschitzWith {n : ℕ} (L : ℝ)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ,
    |f x - f y| ≤ L * vecNorm2 (fun i => x i - y i)

/-- Affine map from a unit-cube coordinate representation to a Rademacher-sign
coordinate representation.  The source proof of Tropp's Rademacher tail passes
through Ledoux's product-measure theorem on `[0,1]^n`, so this map records the
factor of two in the constants. -/
def unitCubeToRademacherVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 2 * x i - 1

/-- Pulling a convex finite-vector function back along the affine unit-cube to
Rademacher map and scaling by a nonnegative constant preserves convexity. -/
theorem finiteVecConvex_scaled_unitCubeToRademacher
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} {c : ℝ}
    (hconv : FiniteVecConvex f) (hc : 0 ≤ c) :
    FiniteVecConvex
      (fun x : Fin n → ℝ => c * f (unitCubeToRademacherVec x)) := by
  intro θ x y hθ hθ1
  have haff :
      unitCubeToRademacherVec
          (fun i : Fin n => θ * x i + (1 - θ) * y i) =
        fun i : Fin n =>
          θ * unitCubeToRademacherVec x i +
            (1 - θ) * unitCubeToRademacherVec y i := by
    ext i
    simp [unitCubeToRademacherVec]
    ring
  have hbase :=
    hconv θ (unitCubeToRademacherVec x) (unitCubeToRademacherVec y)
      hθ hθ1
  calc
    c * f
        (unitCubeToRademacherVec
          (fun i : Fin n => θ * x i + (1 - θ) * y i))
        = c * f
            (fun i : Fin n =>
              θ * unitCubeToRademacherVec x i +
                (1 - θ) * unitCubeToRademacherVec y i) := by
            rw [haff]
    _ ≤ c * (θ * f (unitCubeToRademacherVec x) +
          (1 - θ) * f (unitCubeToRademacherVec y)) :=
            mul_le_mul_of_nonneg_left hbase hc
    _ = θ * (c * f (unitCubeToRademacherVec x)) +
          (1 - θ) * (c * f (unitCubeToRademacherVec y)) := by
            ring

/-- Pulling an `L`-Lipschitz finite-vector function back along the affine
unit-cube to Rademacher map and scaling by `(2L)^{-1}` gives a 1-Lipschitz
function.  This is the deterministic constant conversion behind Tropp's
Proposition 2.1: Ledoux's `[0,1]^n` tail with exponent `exp(-t^2/2)` becomes
the Rademacher tail with exponent `exp(-t^2/8)`. -/
theorem finiteVecLipschitzWith_scaled_unitCubeToRademacher
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hL : 0 < L) (hlip : FiniteVecLipschitzWith L f) :
    FiniteVecLipschitzWith 1
      (fun x : Fin n → ℝ =>
        (2 * L)⁻¹ * f (unitCubeToRademacherVec x)) := by
  intro x y
  let c : ℝ := (2 * L)⁻¹
  let N : ℝ := vecNorm2 (fun i : Fin n => x i - y i)
  have hc_nonneg : 0 ≤ c := by
    exact le_of_lt (inv_pos.mpr (mul_pos two_pos hL))
  have hdiff :
      (fun i : Fin n =>
          unitCubeToRademacherVec x i - unitCubeToRademacherVec y i) =
        fun i : Fin n => 2 * (x i - y i) := by
    ext i
    simp [unitCubeToRademacherVec]
    ring
  have hnorm :
      vecNorm2
          (fun i : Fin n =>
            unitCubeToRademacherVec x i - unitCubeToRademacherVec y i) =
        2 * N := by
    rw [hdiff, vecNorm2_smul]
    simp [N]
  have hbase := hlip (unitCubeToRademacherVec x) (unitCubeToRademacherVec y)
  have hbase' :
      |f (unitCubeToRademacherVec x) -
          f (unitCubeToRademacherVec y)| ≤
        L * (2 * N) := by
    simpa [hnorm] using hbase
  have hscaled :
      |c * f (unitCubeToRademacherVec x) -
          c * f (unitCubeToRademacherVec y)| =
        c * |f (unitCubeToRademacherVec x) -
          f (unitCubeToRademacherVec y)| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hc_nonneg]
  have hmain :
      c * |f (unitCubeToRademacherVec x) -
          f (unitCubeToRademacherVec y)| ≤ N := by
    calc
      c * |f (unitCubeToRademacherVec x) -
          f (unitCubeToRademacherVec y)|
          ≤ c * (L * (2 * N)) :=
              mul_le_mul_of_nonneg_left hbase' hc_nonneg
      _ = N := by
            dsimp [c]
            field_simp [ne_of_gt hL]
  change
    |c * f (unitCubeToRademacherVec x) -
      c * f (unitCubeToRademacherVec y)| ≤ (1 : ℝ) * N
  rw [one_mul, hscaled]
  exact hmain

/-- The Euclidean norm of a finite linear map is convex.

This packages the standard proof from homogeneity and the triangle inequality
for the repository's legacy finite-vector representation. -/
theorem vecNorm2_linear_combination_convex {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    FiniteVecConvex
      (fun x : Fin m → ℝ =>
        vecNorm2 (fun j : Fin n => ∑ k : Fin m, A k j * x k)) := by
  intro θ x y hθ hθ1
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  let Ax : Fin n → ℝ := fun j => ∑ k : Fin m, A k j * x k
  let Ay : Fin n → ℝ := fun j => ∑ k : Fin m, A k j * y k
  have hlinear :
      (fun j : Fin n =>
          ∑ k : Fin m, A k j * (θ * x k + (1 - θ) * y k)) =
        fun j : Fin n => θ * Ax j + (1 - θ) * Ay j := by
    ext j
    calc
      (∑ k : Fin m, A k j * (θ * x k + (1 - θ) * y k))
          = ∑ k : Fin m,
              (θ * (A k j * x k) + (1 - θ) * (A k j * y k)) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = (∑ k : Fin m, θ * (A k j * x k)) +
            ∑ k : Fin m, (1 - θ) * (A k j * y k) := by
              rw [Finset.sum_add_distrib]
      _ = θ * Ax j + (1 - θ) * Ay j := by
              rw [Finset.mul_sum, Finset.mul_sum]
  calc
    vecNorm2
        (fun j : Fin n =>
          ∑ k : Fin m, A k j * (θ * x k + (1 - θ) * y k))
        = vecNorm2 (fun j : Fin n => θ * Ax j + (1 - θ) * Ay j) := by
            rw [hlinear]
    _ ≤ vecNorm2 (fun j : Fin n => θ * Ax j) +
          vecNorm2 (fun j : Fin n => (1 - θ) * Ay j) :=
            vecNorm2_add_le (fun j : Fin n => θ * Ax j)
              (fun j : Fin n => (1 - θ) * Ay j)
    _ = θ * vecNorm2 Ax + (1 - θ) * vecNorm2 Ay := by
            rw [vecNorm2_smul, vecNorm2_smul,
              abs_of_nonneg hθ, abs_of_nonneg h1θ]

/-- Euclidean norm is invariant under negation. -/
lemma vecNorm2_neg {n : ℕ} (x : Fin n → ℝ) :
    vecNorm2 (fun i => -x i) = vecNorm2 x := by
  simpa using vecNorm2_smul (-1 : ℝ) x

/-- Reverse triangle inequality for the repository Euclidean norm. -/
theorem abs_vecNorm2_sub_le_vecNorm2_sub {n : ℕ} (x y : Fin n → ℝ) :
    |vecNorm2 x - vecNorm2 y| ≤ vecNorm2 (fun i => x i - y i) := by
  have hxy0 := vecNorm2_add_le (fun i : Fin n => x i - y i) y
  have hxy :
      vecNorm2 x ≤ vecNorm2 (fun i : Fin n => x i - y i) + vecNorm2 y := by
    have hx :
        (fun i : Fin n => (x i - y i) + y i) = x := by
      ext i
      ring
    simpa [hx]
      using hxy0
  have hyx0 := vecNorm2_add_le (fun i : Fin n => y i - x i) x
  have hyx :
      vecNorm2 y ≤ vecNorm2 (fun i : Fin n => x i - y i) + vecNorm2 x := by
    have hy :
        (fun i : Fin n => (y i - x i) + x i) = y := by
      ext i
      ring
    have hneg :
        vecNorm2 (fun i : Fin n => y i - x i) =
          vecNorm2 (fun i : Fin n => x i - y i) := by
      have hfun :
          (fun i : Fin n => y i - x i) =
            fun i : Fin n => -(x i - y i) := by
        ext i
        ring
      rw [hfun, vecNorm2_neg]
    simpa [hy, hneg]
      using hyx0
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Matrix-vector multiplication is bounded by the Frobenius norm:
    `||Mx||₂² ≤ ||M||_F² ||x||₂²`. -/
theorem vecNorm2Sq_matMulVec_le_frobNormSq_mul {n : ℕ}
    (M : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    vecNorm2Sq (matMulVec n M x) ≤ frobNormSq M * vecNorm2Sq x := by
  unfold vecNorm2Sq matMulVec frobNormSq
  calc
    ∑ i : Fin n, (∑ j : Fin n, M i j * x j) ^ 2
        ≤ ∑ i : Fin n,
            (∑ j : Fin n, M i j ^ 2) * (∑ j : Fin n, x j ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.sum_mul_sq_le_sq_mul_sq
            Finset.univ (fun j => M i j) (fun j => x j)
    _ = (∑ i : Fin n, ∑ j : Fin n, M i j ^ 2) *
          (∑ j : Fin n, x j ^ 2) := by
        rw [Finset.sum_mul]

/-- Matrix-vector multiplication is bounded by the Frobenius norm:
    `||Mx||₂ ≤ ||M||_F ||x||₂`. -/
theorem vecNorm2_matMulVec_le_frobNorm_mul {n : ℕ}
    (M : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    vecNorm2 (matMulVec n M x) ≤ frobNorm M * vecNorm2 x := by
  unfold vecNorm2
  rw [frobNorm_eq_sqrt_frobNormSq]
  rw [← Real.sqrt_mul (frobNormSq_nonneg M)]
  exact Real.sqrt_le_sqrt (vecNorm2Sq_matMulVec_le_frobNormSq_mul M x)

/-- Predicate form of an operator 2-norm bound:
    `||Mx||₂ ≤ c ||x||₂` for every vector `x`.

This avoids introducing a separate supremum-valued spectral norm while still
capturing the standard vector-action meaning of `||M||₂ ≤ c`. -/
def opNorm2Le {n : ℕ} (M : Fin n → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, vecNorm2 (matMulVec n M x) ≤ c * vecNorm2 x

/-- An operator-2 bound controls the quadratic form `xᵀMx`. -/
theorem abs_vecInnerProduct_matMulVec_le_of_opNorm2Le {n : ℕ}
    (M : Fin n → Fin n → ℝ) {c : ℝ} (hM : opNorm2Le M c)
    (x : Fin n → ℝ) :
    |∑ i : Fin n, x i * matMulVec n M x i| ≤ c * vecNorm2Sq x := by
  calc
    |∑ i : Fin n, x i * matMulVec n M x i|
        ≤ vecNorm2 x * vecNorm2 (matMulVec n M x) :=
          abs_vecInnerProduct_le_vecNorm2_mul x (matMulVec n M x)
    _ ≤ vecNorm2 x * (c * vecNorm2 x) :=
          mul_le_mul_of_nonneg_left (hM x) (vecNorm2_nonneg x)
    _ = c * vecNorm2Sq x := by
          rw [← vecNorm2_sq]
          ring

/-- A Frobenius-norm bound implies the corresponding operator-2-norm bound. -/
theorem opNorm2Le_of_frobNorm_le {n : ℕ}
    (M : Fin n → Fin n → ℝ) {c : ℝ}
    (hF : frobNorm M ≤ c) :
    opNorm2Le M c := by
  intro x
  calc
    vecNorm2 (matMulVec n M x)
        ≤ frobNorm M * vecNorm2 x :=
          vecNorm2_matMulVec_le_frobNorm_mul M x
    _ ≤ c * vecNorm2 x :=
          mul_le_mul_of_nonneg_right hF (vecNorm2_nonneg x)

/-- The Frobenius norm itself gives an operator-2 bound. -/
theorem opNorm2Le_of_frobNorm_self {n : ℕ}
    (M : Fin n → Fin n → ℝ) :
    opNorm2Le M (frobNorm M) :=
  opNorm2Le_of_frobNorm_le M le_rfl

/-- A two-sided Loewner bound is stable under an additive perturbation whose
Frobenius norm is at most `τ`; the radius increases by `τ`. -/
theorem finiteLoewnerLe_two_sided_add_of_frobNorm_le {n : ℕ}
    (Exact Delta : Fin n → Fin n → ℝ) {ε τ : ℝ}
    (hExactUpper :
      finiteLoewnerLe Exact
        (fun j k : Fin n => ε * finiteIdMatrix j k))
    (hExactLower :
      finiteLoewnerLe (fun j k : Fin n => -Exact j k)
        (fun j k : Fin n => ε * finiteIdMatrix j k))
    (hpert : frobNorm Delta ≤ τ) :
    finiteLoewnerLe
        (fun j k : Fin n => Exact j k + Delta j k)
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n => -(Exact j k + Delta j k))
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
  classical
  have hDeltaOp : opNorm2Le Delta τ :=
    opNorm2Le_of_frobNorm_le Delta hpert
  have hDeltaUpper :
      finiteLoewnerLe Delta
        (fun j k : Fin n => τ * finiteIdMatrix j k) := by
    intro x
    rw [finiteQuadraticForm_smul_finiteIdMatrix]
    have habs :=
      abs_vecInnerProduct_matMulVec_le_of_opNorm2Le Delta hDeltaOp x
    have hquad :
        |finiteQuadraticForm Delta x| ≤ τ * finiteVecNorm2Sq x := by
      simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
        finiteVecNorm2Sq, vecNorm2Sq] using habs
    exact (le_abs_self (finiteQuadraticForm Delta x)).trans hquad
  have hDeltaLower :
      finiteLoewnerLe (fun j k : Fin n => -Delta j k)
        (fun j k : Fin n => τ * finiteIdMatrix j k) := by
    intro x
    rw [finiteQuadraticForm_smul_finiteIdMatrix]
    have hDeltaNegOp :
        opNorm2Le (fun j k : Fin n => -Delta j k) τ := by
      have hneg : frobNorm (fun j k : Fin n => -Delta j k) ≤ τ := by
        simpa [frobNorm_neg] using hpert
      exact opNorm2Le_of_frobNorm_le (fun j k : Fin n => -Delta j k) hneg
    have habs :=
      abs_vecInnerProduct_matMulVec_le_of_opNorm2Le
        (fun j k : Fin n => -Delta j k) hDeltaNegOp x
    have hquad :
        |finiteQuadraticForm (fun j k : Fin n => -Delta j k) x| ≤
          τ * finiteVecNorm2Sq x := by
      simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
        finiteVecNorm2Sq, vecNorm2Sq] using habs
    exact (le_abs_self
      (finiteQuadraticForm (fun j k : Fin n => -Delta j k) x)).trans hquad
  have hUpperAdd := finiteLoewnerLe_add hExactUpper hDeltaUpper
  have hLowerAdd := finiteLoewnerLe_add hExactLower hDeltaLower
  have hRhs :
      finiteLoewnerLe
        (fun j k : Fin n =>
          ε * finiteIdMatrix j k + τ * finiteIdMatrix j k)
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
    intro x
    rw [finiteQuadraticForm_add, finiteQuadraticForm_smul_finiteIdMatrix,
      finiteQuadraticForm_smul_finiteIdMatrix,
      finiteQuadraticForm_smul_finiteIdMatrix]
    ring_nf
    exact le_rfl
  have hUpper :
      finiteLoewnerLe
        (fun j k : Fin n => Exact j k + Delta j k)
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) :=
    finiteLoewnerLe_trans hUpperAdd hRhs
  have hLower :
      finiteLoewnerLe
        (fun j k : Fin n => -(Exact j k + Delta j k))
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
    have hLower' :
        finiteLoewnerLe
          (fun j k : Fin n => -Exact j k + -Delta j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) :=
      finiteLoewnerLe_trans hLowerAdd hRhs
    convert hLower' using 1
    ext j k
    ring
  exact ⟨hUpper, hLower⟩

-- ============================================================
-- Rectangular operator-2 bounds
-- ============================================================

/-- Rectangular matrix-vector product: `(Ax)_i = ∑ⱼ Aᵢⱼ xⱼ`. -/
noncomputable def rectMatMulVec {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin n, A i j * x j

/-- Row permutations commute with rectangular matrix-vector multiplication. -/
theorem rectMatMulVec_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (rectPermuteRows σ A) x =
      vecPermute σ (rectMatMulVec A x) := by
  ext i
  rfl

/-- Column permutations commute with rectangular matrix-vector multiplication,
    provided the coefficient vector is pulled back by the inverse permutation. -/
theorem rectMatMulVec_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (rectPermuteCols π A) x =
      rectMatMulVec A (vecPermute π.symm x) := by
  ext i
  unfold rectMatMulVec rectPermuteCols vecPermute
  exact
    Fintype.sum_equiv π
      (fun j : Fin n => A i (π j) * x j)
      (fun j : Fin n => A i j * x (π.symm j))
      (fun j => by simp)

/-- Rectangular matrix-vector multiplication commutes with scalar
    multiplication of the vector. -/
theorem rectMatMulVec_smul {m n : ℕ} (M : Fin m → Fin n → ℝ)
    (a : ℝ) (x : Fin n → ℝ) :
    rectMatMulVec M (fun j => a * x j) =
      fun i => a * rectMatMulVec M x i := by
  ext i
  unfold rectMatMulVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Rectangular matrix-vector multiplication is additive in the vector. -/
theorem rectMatMulVec_add {m n : ℕ} (M : Fin m → Fin n → ℝ)
    (x y : Fin n → ℝ) :
    rectMatMulVec M (fun j => x j + y j) =
      fun i => rectMatMulVec M x i + rectMatMulVec M y i := by
  ext i
  unfold rectMatMulVec
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Rectangular matrix-vector multiplication is subtractive in the vector. -/
theorem rectMatMulVec_sub {m n : ℕ} (M : Fin m → Fin n → ℝ)
    (x y : Fin n → ℝ) :
    rectMatMulVec M (fun j => x j - y j) =
      fun i => rectMatMulVec M x i - rectMatMulVec M y i := by
  ext i
  unfold rectMatMulVec
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Self-adjoint dilation of a rectangular matrix:
    `[[0, M], [Mᵀ, 0]]`, indexed by a sum type. -/
noncomputable def rectSelfAdjointDilation {m n : ℕ}
    (M : Fin m → Fin n → ℝ) :
    (Fin m ⊕ Fin n) → (Fin m ⊕ Fin n) → ℝ :=
  fun a b =>
    match a, b with
    | Sum.inl i, Sum.inr j => M i j
    | Sum.inr j, Sum.inl i => M i j
    | _, _ => 0

/-- The rectangular self-adjoint dilation is symmetric. -/
theorem rectSelfAdjointDilation_symmetric {m n : ℕ}
    (M : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (rectSelfAdjointDilation M) := by
  intro a b
  cases a <;> cases b <;> rfl

/-- The square of a rectangular self-adjoint dilation is positive
    semidefinite in the finite quadratic-form order. -/
theorem finitePSD_rectSelfAdjointDilation_square {m n : ℕ}
    (M : Fin m → Fin n → ℝ) :
    finitePSD
      (finiteMatMul (rectSelfAdjointDilation M)
        (rectSelfAdjointDilation M)) :=
  finitePSD_finiteMatMul_self_of_symmetric
    (rectSelfAdjointDilation M) (rectSelfAdjointDilation_symmetric M)

/-- An operator-2 bound on a rectangular self-adjoint dilation gives the
    deterministic Loewner bound `D(M)^2 <= L^2 I`. -/
theorem rectSelfAdjointDilation_square_loewnerLe_scalar_id_of_finiteOpNorm2Le
    {m n : ℕ} (M : Fin m → Fin n → ℝ) {L : ℝ}
    (hD : finiteOpNorm2Le (rectSelfAdjointDilation M) L)
    (hL : 0 ≤ L) :
    finiteLoewnerLe
      (finiteMatMul (rectSelfAdjointDilation M)
        (rectSelfAdjointDilation M))
      (fun a b => L ^ 2 * finiteIdMatrix a b) :=
  finiteMatMul_self_loewnerLe_scalar_id_of_finiteOpNorm2Le
    (rectSelfAdjointDilation M) (rectSelfAdjointDilation_symmetric M) hD hL

/-- A squared Loewner bound on a self-adjoint dilation gives the corresponding
    square vector-action operator-2 bound. -/
theorem rectSelfAdjointDilation_opNorm2Le_of_square_loewnerLe_scalar_id
    {m n : ℕ} (M : Fin m → Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L)
    (hSq :
      finiteLoewnerLe
        (finiteMatMul (rectSelfAdjointDilation M)
          (rectSelfAdjointDilation M))
        (fun a b => L ^ 2 * finiteIdMatrix a b)) :
    finiteOpNorm2Le (rectSelfAdjointDilation M) L :=
  finiteOpNorm2Le_of_finiteMatMul_self_loewnerLe_scalar_id
    (rectSelfAdjointDilation M) (rectSelfAdjointDilation_symmetric M) hL hSq

/-- The squared Frobenius norm of the self-adjoint dilation is twice the
    rectangular squared Frobenius norm of the original matrix. -/
theorem finiteFrobNormSq_rectSelfAdjointDilation {m n : ℕ}
    (M : Fin m → Fin n → ℝ) :
    finiteFrobNormSq (rectSelfAdjointDilation M) = 2 * frobNormSqRect M := by
  have hswap : (∑ j : Fin n, ∑ i : Fin m, M i j ^ 2) =
      ∑ i : Fin m, ∑ j : Fin n, M i j ^ 2 := by
    rw [Finset.sum_comm]
  unfold finiteFrobNormSq rectSelfAdjointDilation frobNormSqRect
  rw [Fintype.sum_sum_type]
  simp [Fintype.sum_sum_type]
  rw [hswap]
  ring

/-- Frobenius control of a rectangular matrix gives finite operator control of
    its self-adjoint dilation, with the elementary `sqrt 2` Frobenius factor. -/
theorem finiteOpNorm2Le_rectSelfAdjointDilation_of_frobNormRect_le
    {m n : ℕ} (M : Fin m → Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hF : frobNormRect M ≤ L) :
    finiteOpNorm2Le (rectSelfAdjointDilation M) (Real.sqrt 2 * L) := by
  have hscale_nonneg : 0 ≤ Real.sqrt 2 * L :=
    mul_nonneg (Real.sqrt_nonneg 2) hL
  apply finiteOpNorm2Le_of_finiteFrobNormSq_le_sq
    (rectSelfAdjointDilation M) hscale_nonneg
  have hF_sq : frobNormSqRect M ≤ L ^ 2 := by
    rw [← frobNormRect_sq]
    have habs : |frobNormRect M| ≤ |L| := by
      simpa [abs_of_nonneg (frobNormRect_nonneg M), abs_of_nonneg hL] using hF
    exact (sq_le_sq).mpr habs
  rw [finiteFrobNormSq_rectSelfAdjointDilation]
  calc
    2 * frobNormSqRect M ≤ 2 * L ^ 2 := by
      exact mul_le_mul_of_nonneg_left hF_sq (by norm_num)
    _ = (Real.sqrt 2 * L) ^ 2 := by
      rw [show (Real.sqrt 2 * L) ^ 2 =
          (Real.sqrt 2) ^ 2 * L ^ 2 from by ring,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The trace of the square of the self-adjoint dilation is twice the
    rectangular squared Frobenius norm.  This is the finite-dimensional trace
    identity used by matrix-moment routes to spectral concentration. -/
theorem finiteTrace_finiteMatMul_rectSelfAdjointDilation_self {m n : ℕ}
    (M : Fin m → Fin n → ℝ) :
    finiteTrace
        (finiteMatMul (rectSelfAdjointDilation M)
          (rectSelfAdjointDilation M)) =
      2 * frobNormSqRect M := by
  have hswap : (∑ j : Fin n, ∑ i : Fin m, M i j ^ 2) =
      ∑ i : Fin m, ∑ j : Fin n, M i j ^ 2 := by
    rw [Finset.sum_comm]
  unfold finiteTrace finiteMatMul rectSelfAdjointDilation frobNormSqRect
  rw [Fintype.sum_sum_type]
  simp [Fintype.sum_sum_type]
  simp_rw [← sq]
  rw [hswap]
  ring

/-- Applying the self-adjoint dilation to a right-embedded vector gives the
    left embedding of the rectangular product. -/
theorem finiteMatVec_rectSelfAdjointDilation_sumInr {m n : ℕ}
    (M : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    finiteMatVec (rectSelfAdjointDilation M) (sumInrVec (α := Fin m) x) =
      sumInlVec (β := Fin n) (rectMatMulVec M x) := by
  ext a
  cases a with
  | inl i =>
      unfold finiteMatVec rectSelfAdjointDilation sumInrVec sumInlVec rectMatMulVec
      rw [Fintype.sum_sum_type]
      simp
  | inr j =>
      unfold finiteMatVec rectSelfAdjointDilation sumInrVec sumInlVec rectMatMulVec
      rw [Fintype.sum_sum_type]
      simp

/-- Applying the self-adjoint dilation to a paired vector gives the expected
    left/right rectangular products. -/
theorem finiteMatVec_rectSelfAdjointDilation_sumBothVec {m n : ℕ}
    (M : Fin m → Fin n → ℝ) (y : Fin m → ℝ) (x : Fin n → ℝ) :
    finiteMatVec (rectSelfAdjointDilation M) (sumBothVec y x) =
      sumBothVec (rectMatMulVec M x)
        (fun j : Fin n => ∑ i : Fin m, M i j * y i) := by
  ext a
  cases a with
  | inl i =>
      unfold finiteMatVec rectSelfAdjointDilation sumBothVec rectMatMulVec
      rw [Fintype.sum_sum_type]
      simp
  | inr j =>
      unfold finiteMatVec rectSelfAdjointDilation sumBothVec rectMatMulVec
      rw [Fintype.sum_sum_type]
      simp

/-- Quadratic form of the self-adjoint dilation on a paired vector.

For `z = (y, x)`, the form is `2 * <y, Mx>`.  This is the deterministic
bridge used to convert one-sided dilation Rayleigh/Loewner control into a
rectangular operator bound. -/
theorem finiteQuadraticForm_rectSelfAdjointDilation_sumBothVec {m n : ℕ}
    (M : Fin m → Fin n → ℝ) (y : Fin m → ℝ) (x : Fin n → ℝ) :
    finiteQuadraticForm (rectSelfAdjointDilation M) (sumBothVec y x) =
      2 * ∑ i : Fin m, y i * rectMatMulVec M x i := by
  classical
  have hswap :
      (∑ j : Fin n, x j * ∑ i : Fin m, M i j * y i) =
        ∑ i : Fin m, y i * ∑ j : Fin n, M i j * x j := by
    calc
      (∑ j : Fin n, x j * ∑ i : Fin m, M i j * y i)
          = ∑ j : Fin n, ∑ i : Fin m, x j * (M i j * y i) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
      _ = ∑ i : Fin m, ∑ j : Fin n, x j * (M i j * y i) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin m, y i * ∑ j : Fin n, M i j * x j := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
  unfold finiteQuadraticForm
  rw [finiteMatVec_rectSelfAdjointDilation_sumBothVec]
  unfold sumBothVec
  rw [Fintype.sum_sum_type]
  simp [rectMatMulVec, hswap]
  ring

/-- Matrix-vector multiplication by a rectangular matrix is bounded by the
    rectangular Frobenius norm, squared form. -/
theorem vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_mul {m n : ℕ}
    (M : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    vecNorm2Sq (rectMatMulVec M x) ≤ frobNormSqRect M * vecNorm2Sq x := by
  unfold vecNorm2Sq rectMatMulVec frobNormSqRect
  calc
    ∑ i : Fin m, (∑ j : Fin n, M i j * x j) ^ 2
        ≤ ∑ i : Fin m,
            (∑ j : Fin n, M i j ^ 2) * (∑ j : Fin n, x j ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.sum_mul_sq_le_sq_mul_sq
            Finset.univ (fun j => M i j) (fun j => x j)
    _ = (∑ i : Fin m, ∑ j : Fin n, M i j ^ 2) *
          (∑ j : Fin n, x j ^ 2) := by
        rw [Finset.sum_mul]

/-- Matrix-vector multiplication by a rectangular matrix is bounded by the
    rectangular Frobenius norm. -/
theorem vecNorm2_rectMatMulVec_le_frobNormRect_mul {m n : ℕ}
    (M : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    vecNorm2 (rectMatMulVec M x) ≤ frobNormRect M * vecNorm2 x := by
  unfold vecNorm2 frobNormRect
  rw [← Real.sqrt_mul (frobNormSqRect_nonneg M)]
  exact Real.sqrt_le_sqrt (vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_mul M x)

/-- Triangle inequality for rectangular matrix-vector products:
    `|(Ax)_i| <= ∑_j |A_ij| |x_j|`. -/
theorem abs_rectMatMulVec_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    ∀ i : Fin m,
      |rectMatMulVec A x i| ≤ ∑ j : Fin n, |A i j| * |x j| := by
  intro i
  unfold rectMatMulVec
  calc
    |∑ j : Fin n, A i j * x j|
        ≤ ∑ j : Fin n, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |A i j| * |x j| := by
        apply Finset.sum_congr rfl
        intro j _
        exact abs_mul (A i j) (x j)

/-- If `|A| <= B` entrywise, then `|Ax| <= B |x|` entrywise. -/
theorem rectMatMulVec_abs_entry_le {m n : ℕ}
    {A B : Fin m → Fin n → ℝ} (hAB : ∀ i j, |A i j| ≤ B i j)
    (x : Fin n → ℝ) :
    ∀ i : Fin m,
      |rectMatMulVec A x i| ≤ rectMatMulVec B (fun j => |x j|) i := by
  intro i
  calc
    |rectMatMulVec A x i|
        ≤ ∑ j : Fin n, |A i j| * |x j| :=
          abs_rectMatMulVec_le A x i
    _ ≤ ∑ j : Fin n, B i j * |x j| := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hAB i j) (abs_nonneg (x j))
    _ = rectMatMulVec B (fun j => |x j|) i := rfl

/-- Predicate form of a rectangular operator 2-norm bound:
    `||Mx||₂ ≤ c ||x||₂` for every vector `x`. -/
def rectOpNorm2Le {m n : ℕ} (M : Fin m → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, vecNorm2 (rectMatMulVec M x) ≤ c * vecNorm2 x

/-- Lemma 6.6(b), predicate form: componentwise domination `|A| <= B`
    preserves any rectangular 2-operator upper bound. -/
theorem rectOpNorm2Le_of_abs_entry_le {m n : ℕ}
    {A B : Fin m → Fin n → ℝ} {c : ℝ}
    (hAB : ∀ i j, |A i j| ≤ B i j) (hB : rectOpNorm2Le B c) :
    rectOpNorm2Le A c := by
  intro x
  calc
    vecNorm2 (rectMatMulVec A x)
        ≤ vecNorm2 (rectMatMulVec B (fun j => |x j|)) :=
          vecNorm2_le_of_abs_le (rectMatMulVec A x)
            (rectMatMulVec B (fun j => |x j|))
            (rectMatMulVec_abs_entry_le hAB x)
    _ ≤ c * vecNorm2 (fun j => |x j|) := hB (fun j => |x j|)
    _ = c * vecNorm2 x := by
          rw [vecNorm2_abs]

/-- Lemma 6.6(b), absolute-matrix variant using the local rectangular absolute
    matrix notation. -/
theorem rectOpNorm2Le_of_absMatrixRect_le {m n : ℕ}
    {A B : Fin m → Fin n → ℝ} {c : ℝ}
    (hAB : ∀ i j, absMatrixRect A i j ≤ B i j)
    (hB : rectOpNorm2Le B c) :
    rectOpNorm2Le A c :=
  rectOpNorm2Le_of_abs_entry_le (A := A) (B := B)
    (by simpa [absMatrixRect] using hAB) hB

/-- Lemma 6.6(c), reduction step: if `|A| <= |B|`, then any rectangular
    2-operator upper bound for `|B|` is also a bound for `A`. -/
theorem rectOpNorm2Le_of_abs_entry_le_abs {m n : ℕ}
    {A B : Fin m → Fin n → ℝ} {c : ℝ}
    (hAB : ∀ i j, |A i j| ≤ |B i j|)
    (hBabs : rectOpNorm2Le (absMatrixRect B) c) :
    rectOpNorm2Le A c :=
  rectOpNorm2Le_of_abs_entry_le (A := A) (B := absMatrixRect B)
    (by simpa [absMatrixRect] using hAB) hBabs

/-- Lemma 6.6(d), first inequality in predicate form: every rectangular
    2-operator upper bound for `|A|` is also a bound for `A`. -/
theorem rectOpNorm2Le_of_absMatrixRect_bound {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {c : ℝ}
    (hAbsA : rectOpNorm2Le (absMatrixRect A) c) :
    rectOpNorm2Le A c :=
  rectOpNorm2Le_of_absMatrixRect_le (A := A) (B := absMatrixRect A)
    (by intro i j; exact le_rfl) hAbsA

/-- Monotonicity of rectangular operator-norm upper-bound predicates in the
radius. -/
theorem rectOpNorm2Le_mono {m n : ℕ} {M : Fin m → Fin n → ℝ}
    {c d : ℝ} (hcd : c ≤ d) (hM : rectOpNorm2Le M c) :
    rectOpNorm2Le M d := by
  intro x
  exact le_trans (hM x)
    (mul_le_mul_of_nonneg_right hcd (vecNorm2_nonneg _))

/-- Rectangular operator-2 bounds are preserved by transpose.

The proof is finite-dimensional norm duality: test `Mᵀ y` against its own
normalized direction, move the inner product across the transpose, and apply
the original operator certificate for `M`. -/
theorem rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le {m n : ℕ}
    (M : Fin m → Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hM : rectOpNorm2Le M c) :
    rectOpNorm2Le (finiteTranspose M) c := by
  intro y
  let z : Fin n → ℝ := rectMatMulVec (finiteTranspose M) y
  by_cases hz : vecNorm2 z = 0
  · have hright : 0 ≤ c * vecNorm2 y :=
      mul_nonneg hc (vecNorm2_nonneg y)
    simpa [z, hz] using hright
  · have hzpos : 0 < vecNorm2 z :=
      lt_of_le_of_ne (vecNorm2_nonneg z) (Ne.symm hz)
    let x : Fin n → ℝ := fun j => (vecNorm2 z)⁻¹ * z j
    have hxnorm : vecNorm2 x = 1 :=
      vecNorm2_inv_smul_self_of_pos z hzpos
    have hinner_z : (∑ j : Fin n, x j * z j) = vecNorm2 z :=
      vecInnerProduct_inv_smul_self_eq_norm z hzpos
    have htranspose :
        (∑ j : Fin n, x j * z j) =
          ∑ i : Fin m, rectMatMulVec M x i * y i := by
      calc
        (∑ j : Fin n, x j * z j)
            = ∑ j : Fin n, z j * x j := by
                apply Finset.sum_congr rfl
                intro j _
                ring
        _ = ∑ i : Fin m, y i * rectMatMulVec M x i := by
                simpa [z, rectMatMulVec] using
                  (finiteVecInnerProduct_finiteMatVec_eq_transpose M y x).symm
        _ = ∑ i : Fin m, rectMatMulVec M x i * y i := by
                apply Finset.sum_congr rfl
                intro i _
                ring
    have hinner_eq :
        (∑ i : Fin m, rectMatMulVec M x i * y i) = vecNorm2 z := by
      rw [← htranspose, hinner_z]
    have hcs :
        vecNorm2 z ≤ vecNorm2 (rectMatMulVec M x) * vecNorm2 y := by
      calc
        vecNorm2 z
            = |∑ i : Fin m, rectMatMulVec M x i * y i| := by
                rw [hinner_eq, abs_of_nonneg (vecNorm2_nonneg z)]
        _ ≤ vecNorm2 (rectMatMulVec M x) * vecNorm2 y :=
                abs_vecInnerProduct_le_vecNorm2_mul (rectMatMulVec M x) y
    have hMx_le : vecNorm2 (rectMatMulVec M x) ≤ c := by
      simpa [hxnorm] using hM x
    calc
      vecNorm2 (rectMatMulVec (finiteTranspose M) y)
          = vecNorm2 z := rfl
      _ ≤ vecNorm2 (rectMatMulVec M x) * vecNorm2 y := hcs
      _ ≤ c * vecNorm2 y :=
          mul_le_mul_of_nonneg_right hMx_le (vecNorm2_nonneg y)

/-- A square operator bound on the self-adjoint dilation implies the
    rectangular vector-action operator bound for the original matrix. -/
theorem rectOpNorm2Le_of_selfAdjointDilation {m n : ℕ}
    (M : Fin m → Fin n → ℝ) {c : ℝ}
    (hD : finiteOpNorm2Le (rectSelfAdjointDilation M) c) :
    rectOpNorm2Le M c := by
  intro x
  have h := hD (sumInrVec (α := Fin m) x)
  rw [finiteMatVec_rectSelfAdjointDilation_sumInr,
    finiteVecNorm2_sumInlVec, finiteVecNorm2_sumInrVec,
    finiteVecNorm2_fin, finiteVecNorm2_fin] at h
  exact h

/-- A one-sided scalar-identity Loewner bound on the self-adjoint dilation is
    already enough to bound the rectangular operator action.

This is specific to self-adjoint dilations: testing the Rayleigh bound on
paired vectors `(α Mx, x)` recovers `||Mx||₂ <= L ||x||₂`.  It is the
deterministic adapter needed when a future largest-eigenvalue tail theorem is
stated as `D(M) <= L I`. -/
theorem rectOpNorm2Le_of_selfAdjointDilation_loewnerLe_scalar_id
    {m n : ℕ} (M : Fin m → Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L)
    (hD :
      finiteLoewnerLe
        (rectSelfAdjointDilation M)
        (fun a b => L * finiteIdMatrix a b)) :
    rectOpNorm2Le M L := by
  intro x
  let r : Fin m → ℝ := rectMatMulVec M x
  by_cases hrzero : vecNorm2 r = 0
  · rw [show rectMatMulVec M x = r by rfl, hrzero]
    exact mul_nonneg hL (vecNorm2_nonneg x)
  · have hrpos : 0 < vecNorm2 r :=
      lt_of_le_of_ne (vecNorm2_nonneg r) (Ne.symm hrzero)
    by_cases hxzero : vecNorm2 x = 0
    · have hx_entries : ∀ j, x j = 0 := (vecNorm2_eq_zero_iff x).mp hxzero
      have hr_zero_fun : r = fun _i : Fin m => 0 := by
        ext i
        unfold r rectMatMulVec
        simp [hx_entries]
      have hr_zero : vecNorm2 r = 0 := by
        rw [hr_zero_fun, vecNorm2_zero]
      exact False.elim (hrzero hr_zero)
    · have hxpos : 0 < vecNorm2 x :=
        lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxzero)
      let α : ℝ := vecNorm2 x / vecNorm2 r
      have hα_nonneg : 0 ≤ α := by
        exact div_nonneg (vecNorm2_nonneg x) (le_of_lt hrpos)
      let y : Fin m → ℝ := fun i => α * r i
      let z : Fin m ⊕ Fin n → ℝ := sumBothVec y x
      have hupper := hD z
      rw [finiteQuadraticForm_smul_finiteIdMatrix] at hupper
      have hq :
          finiteQuadraticForm (rectSelfAdjointDilation M) z =
            2 * (α * vecNorm2Sq r) := by
        calc
          finiteQuadraticForm (rectSelfAdjointDilation M) z
              = 2 * ∑ i : Fin m, y i * rectMatMulVec M x i := by
                  simpa [z] using
                    finiteQuadraticForm_rectSelfAdjointDilation_sumBothVec M y x
          _ = 2 * (α * vecNorm2Sq r) := by
                  congr 1
                  unfold y r vecNorm2Sq
                  calc
                    (∑ i : Fin m,
                        α * rectMatMulVec M x i * rectMatMulVec M x i)
                        = ∑ i : Fin m,
                            α * (rectMatMulVec M x i ^ 2) := by
                            apply Finset.sum_congr rfl
                            intro i _
                            ring
                    _ = α * ∑ i : Fin m, rectMatMulVec M x i ^ 2 := by
                            rw [Finset.mul_sum]
      have hzsq :
          finiteVecNorm2Sq z = α ^ 2 * vecNorm2Sq r + vecNorm2Sq x := by
        calc
          finiteVecNorm2Sq z
              = finiteVecNorm2Sq y + finiteVecNorm2Sq x := by
                  simpa [z] using finiteVecNorm2Sq_sumBothVec y x
          _ = α ^ 2 * vecNorm2Sq r + vecNorm2Sq x := by
                  congr 1
                  unfold y r
                  rw [finiteVecNorm2Sq_fin, vecNorm2Sq_smul]
      have hineq :
          2 * (α * vecNorm2Sq r) ≤
            L * (α ^ 2 * vecNorm2Sq r + vecNorm2Sq x) := by
        simpa [hq, hzsq] using hupper
      have hα_eq : α * vecNorm2 r = vecNorm2 x := by
        unfold α
        field_simp [hrzero]
      have hnorm_sq_r : vecNorm2Sq r = vecNorm2 r ^ 2 := by
        rw [← vecNorm2_sq]
      have hnorm_sq_x : vecNorm2Sq x = vecNorm2 x ^ 2 := by
        rw [← vecNorm2_sq]
      have hmain :
          2 * vecNorm2 x * vecNorm2 r ≤
            2 * L * vecNorm2 x ^ 2 := by
        rw [hnorm_sq_r, hnorm_sq_x] at hineq
        have hα_sq :
            α ^ 2 * vecNorm2 r ^ 2 = vecNorm2 x ^ 2 := by
          nlinarith [hα_eq]
        have hleft :
            2 * (α * vecNorm2 r ^ 2) =
              2 * vecNorm2 x * vecNorm2 r := by
          nlinarith [hα_eq]
        rw [hα_sq, hleft] at hineq
        ring_nf at hineq ⊢
        exact hineq
      have hxpos2 : 0 < 2 * vecNorm2 x := mul_pos (by norm_num) hxpos
      have hmul :
          (2 * vecNorm2 x) * vecNorm2 r ≤
            (2 * vecNorm2 x) * (L * vecNorm2 x) := by
        nlinarith [hmain]
      have htarget : vecNorm2 r ≤ L * vecNorm2 x := by
        nlinarith [hmul, hxpos2]
      simpa [r] using htarget

/-- A rectangular operator-2 bound gives a one-sided Loewner bound for the
    self-adjoint dilation.

This is the converse direction needed by rectangular matrix-Bernstein routes:
from `||Mx||₂ ≤ L ||x||₂`, the quadratic form of `D(M)` satisfies
`2⟨y,Mx⟩ ≤ L (||y||₂² + ||x||₂²)`. -/
theorem finiteLoewnerLe_rectSelfAdjointDilation_of_rectOpNorm2Le
    {m n : ℕ} (M : Fin m → Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hM : rectOpNorm2Le M L) :
    finiteLoewnerLe
      (rectSelfAdjointDilation M)
      (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
  classical
  intro z
  let y : Fin m → ℝ := fun i => z (Sum.inl i)
  let x : Fin n → ℝ := fun j => z (Sum.inr j)
  have hz : z = sumBothVec y x := by
    ext a
    cases a <;> rfl
  have hq :
      finiteQuadraticForm (rectSelfAdjointDilation M) z =
        2 * ∑ i : Fin m, y i * rectMatMulVec M x i := by
    rw [hz]
    exact finiteQuadraticForm_rectSelfAdjointDilation_sumBothVec M y x
  have hid :
      finiteQuadraticForm
          (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) z =
        L * (finiteVecNorm2Sq y + finiteVecNorm2Sq x) := by
    rw [finiteQuadraticForm_smul_finiteIdMatrix, hz,
      finiteVecNorm2Sq_sumBothVec]
  have hinner :
      ∑ i : Fin m, y i * rectMatMulVec M x i ≤
        L * (vecNorm2 y * vecNorm2 x) := by
    calc
      ∑ i : Fin m, y i * rectMatMulVec M x i
          ≤ |∑ i : Fin m, y i * rectMatMulVec M x i| := le_abs_self _
      _ ≤ vecNorm2 y * vecNorm2 (rectMatMulVec M x) :=
          abs_vecInnerProduct_le_vecNorm2_mul y (rectMatMulVec M x)
      _ ≤ vecNorm2 y * (L * vecNorm2 x) :=
          mul_le_mul_of_nonneg_left (hM x) (vecNorm2_nonneg y)
      _ = L * (vecNorm2 y * vecNorm2 x) := by ring
  have hmain :
      2 * ∑ i : Fin m, y i * rectMatMulVec M x i ≤
        L * (finiteVecNorm2Sq y + finiteVecNorm2Sq x) := by
    have hy : 0 ≤ vecNorm2 y := vecNorm2_nonneg y
    have hx : 0 ≤ vecNorm2 x := vecNorm2_nonneg x
    have hySq : finiteVecNorm2Sq y = vecNorm2 y ^ 2 := by
      rw [finiteVecNorm2Sq_fin, ← vecNorm2_sq]
    have hxSq : finiteVecNorm2Sq x = vecNorm2 x ^ 2 := by
      rw [finiteVecNorm2Sq_fin, ← vecNorm2_sq]
    nlinarith [hinner, hL, hy, hx, sq_nonneg (vecNorm2 y - vecNorm2 x)]
  simpa [hq, hid] using hmain

/-- The negative self-adjoint dilation satisfies the same one-sided Loewner
    bound as the positive dilation when the rectangular operator norm is
    bounded. -/
theorem finiteLoewnerLe_neg_rectSelfAdjointDilation_of_rectOpNorm2Le
    {m n : ℕ} (M : Fin m → Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hM : rectOpNorm2Le M L) :
    finiteLoewnerLe
      (fun a b : Fin m ⊕ Fin n => -rectSelfAdjointDilation M a b)
      (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
  classical
  intro z
  let y : Fin m → ℝ := fun i => z (Sum.inl i)
  let x : Fin n → ℝ := fun j => z (Sum.inr j)
  have hz : z = sumBothVec y x := by
    ext a
    cases a <;> rfl
  have hq :
      finiteQuadraticForm
          (fun a b : Fin m ⊕ Fin n => -rectSelfAdjointDilation M a b) z =
        -2 * ∑ i : Fin m, y i * rectMatMulVec M x i := by
    calc
      finiteQuadraticForm
          (fun a b : Fin m ⊕ Fin n => -rectSelfAdjointDilation M a b) z
          = -finiteQuadraticForm (rectSelfAdjointDilation M) z := by
              rw [finiteQuadraticForm_neg]
      _ = -(2 * ∑ i : Fin m, y i * rectMatMulVec M x i) := by
              rw [hz, finiteQuadraticForm_rectSelfAdjointDilation_sumBothVec]
      _ = -2 * ∑ i : Fin m, y i * rectMatMulVec M x i := by ring
  have hid :
      finiteQuadraticForm
          (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) z =
        L * (finiteVecNorm2Sq y + finiteVecNorm2Sq x) := by
    rw [finiteQuadraticForm_smul_finiteIdMatrix, hz,
      finiteVecNorm2Sq_sumBothVec]
  have hinner_abs :
      |∑ i : Fin m, y i * rectMatMulVec M x i| ≤
        L * (vecNorm2 y * vecNorm2 x) := by
    calc
      |∑ i : Fin m, y i * rectMatMulVec M x i|
          ≤ vecNorm2 y * vecNorm2 (rectMatMulVec M x) :=
          abs_vecInnerProduct_le_vecNorm2_mul y (rectMatMulVec M x)
      _ ≤ vecNorm2 y * (L * vecNorm2 x) :=
          mul_le_mul_of_nonneg_left (hM x) (vecNorm2_nonneg y)
      _ = L * (vecNorm2 y * vecNorm2 x) := by ring
  have hmain :
      -2 * ∑ i : Fin m, y i * rectMatMulVec M x i ≤
        L * (finiteVecNorm2Sq y + finiteVecNorm2Sq x) := by
    have hy : 0 ≤ vecNorm2 y := vecNorm2_nonneg y
    have hx : 0 ≤ vecNorm2 x := vecNorm2_nonneg x
    have hySq : finiteVecNorm2Sq y = vecNorm2 y ^ 2 := by
      rw [finiteVecNorm2Sq_fin, ← vecNorm2_sq]
    have hxSq : finiteVecNorm2Sq x = vecNorm2 x ^ 2 := by
      rw [finiteVecNorm2Sq_fin, ← vecNorm2_sq]
    have hneg :
        - (∑ i : Fin m, y i * rectMatMulVec M x i) ≤
          |∑ i : Fin m, y i * rectMatMulVec M x i| :=
      neg_le_abs _
    nlinarith [hinner_abs, hneg, hL, hy, hx,
      sq_nonneg (vecNorm2 y - vecNorm2 x), hySq, hxSq]
  simpa [hq, hid] using hmain

/-- A squared Loewner bound on the self-adjoint dilation gives the rectangular
    vector-action operator-2 bound for the original matrix. -/
theorem rectOpNorm2Le_of_selfAdjointDilation_square_loewnerLe_scalar_id
    {m n : ℕ} (M : Fin m → Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L)
    (hSq :
      finiteLoewnerLe
        (finiteMatMul (rectSelfAdjointDilation M)
          (rectSelfAdjointDilation M))
        (fun a b => L ^ 2 * finiteIdMatrix a b)) :
    rectOpNorm2Le M L :=
  rectOpNorm2Le_of_selfAdjointDilation M
    (rectSelfAdjointDilation_opNorm2Le_of_square_loewnerLe_scalar_id
      M hL hSq)

/-- A unit-ball vector-action bound implies the homogeneous rectangular
    operator-2 predicate. -/
theorem rectOpNorm2Le_of_unit_ball_bound {m n : ℕ}
    (M : Fin m → Fin n → ℝ) (c : ℝ)
    (hunit : ∀ x : Fin n → ℝ, vecNorm2 x ≤ 1 →
      vecNorm2 (rectMatMulVec M x) ≤ c) :
    rectOpNorm2Le M c := by
  intro x
  by_cases hxzero : vecNorm2 x = 0
  · have hx_entries : ∀ i, x i = 0 := (vecNorm2_eq_zero_iff x).mp hxzero
    have hMx_zero :
        rectMatMulVec M x = fun _i : Fin m => 0 := by
      ext i
      unfold rectMatMulVec
      simp [hx_entries]
    rw [hMx_zero, vecNorm2_zero, hxzero]
    simp
  · have hxpos : 0 < vecNorm2 x :=
      lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxzero)
    let z : Fin n → ℝ := fun i => (vecNorm2 x)⁻¹ * x i
    have hinvpos : 0 < (vecNorm2 x)⁻¹ := inv_pos.mpr hxpos
    have hz_norm : vecNorm2 z = 1 := by
      unfold z
      rw [vecNorm2_smul, abs_of_pos hinvpos, inv_mul_cancel₀ hxzero]
    have hz_bound : vecNorm2 (rectMatMulVec M z) ≤ c := by
      exact hunit z (by rw [hz_norm])
    have hMz :
        rectMatMulVec M z =
          fun i => (vecNorm2 x)⁻¹ * rectMatMulVec M x i := by
      unfold z
      exact rectMatMulVec_smul M (vecNorm2 x)⁻¹ x
    rw [hMz, vecNorm2_smul, abs_of_pos hinvpos] at hz_bound
    have hdiv :
        vecNorm2 (rectMatMulVec M x) / vecNorm2 x ≤ c := by
      simpa [div_eq_mul_inv, mul_comm] using hz_bound
    exact (div_le_iff₀ hxpos).mp hdiv

/-- A finite family of test vectors covers the unit ball at radius `ρ` if each
    unit-ball vector is within Euclidean distance `ρ` of some test vector. -/
def finiteUnitBallCover {ι κ : Type*} [Fintype κ]
    (net : ι → κ → ℝ) (ρ : ℝ) : Prop :=
  ∀ x : κ → ℝ, finiteVecNorm2 x ≤ 1 →
    ∃ a : ι, finiteVecNorm2 (fun j => x j - net a j) ≤ ρ

/-- A finite quadratic-form test cover plus a coarse operator radius gives a
scalar-identity Loewner upper bound.

If every unit vector is within `ρ` of a tested vector, all tested quadratic forms
are at most `η`, and `M` has coarse operator radius `L`, then every unit
quadratic form is at most `η + L * (2 * ρ + ρ ^ 2)`.  Homogeneity gives the
displayed Loewner statement for all vectors. -/
theorem finiteLoewnerLe_of_finite_unit_ball_cover_quadraticForm
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : κ → κ → ℝ) (net : ι → κ → ℝ) {ρ η L : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hnet : ∀ a : ι, finiteQuadraticForm M (net a) ≤ η)
    (hM : finiteOpNorm2Le M L) (hL : 0 ≤ L) (hρ : 0 ≤ ρ) :
    finiteLoewnerLe M
      (fun i j : κ => (η + L * (2 * ρ + ρ ^ 2)) * finiteIdMatrix i j) := by
  classical
  let C : ℝ := η + L * (2 * ρ + ρ ^ 2)
  have hunit :
      ∀ x : κ → ℝ, finiteVecNorm2 x ≤ 1 →
        finiteQuadraticForm M x ≤ C := by
    intro x hx
    obtain ⟨a, hdist⟩ := hcover x hx
    let z : κ → ℝ := net a
    let d : κ → ℝ := fun j => x j - z j
    have hdist' : finiteVecNorm2 d ≤ ρ := by
      simpa [d, z] using hdist
    have hz_bound : finiteVecNorm2 z ≤ 1 + ρ := by
      have hz_eq : z = fun j => x j + (-1 : ℝ) * d j := by
        ext j
        simp [z, d]
      calc
        finiteVecNorm2 z
            = finiteVecNorm2 (fun j => x j + (-1 : ℝ) * d j) := by
                rw [hz_eq]
        _ ≤ finiteVecNorm2 x + finiteVecNorm2 (fun j => (-1 : ℝ) * d j) :=
                finiteVecNorm2_add_le x (fun j => (-1 : ℝ) * d j)
        _ = finiteVecNorm2 x + finiteVecNorm2 d := by
                rw [finiteVecNorm2_smul]
                norm_num
        _ ≤ 1 + ρ := add_le_add hx hdist'
    have hdiff_eq := finiteQuadraticForm_sub_vec_eq_sub_add M x z
    have hdiff_abs :
        |finiteQuadraticForm M x - finiteQuadraticForm M z| ≤
          L * finiteVecNorm2 d * finiteVecNorm2 x +
            L * finiteVecNorm2 z * finiteVecNorm2 d := by
      rw [hdiff_eq]
      exact (abs_add_le _ _).trans
        (add_le_add
          (abs_finiteVecInnerProduct_finiteMatVec_two_le_of_finiteOpNorm2Le
            M hM d x)
          (abs_finiteVecInnerProduct_finiteMatVec_two_le_of_finiteOpNorm2Le
            M hM z d))
    have hdiff_bound :
        L * finiteVecNorm2 d * finiteVecNorm2 x +
            L * finiteVecNorm2 z * finiteVecNorm2 d ≤
          L * (2 * ρ + ρ ^ 2) := by
      have hdx_nonneg : 0 ≤ finiteVecNorm2 d := finiteVecNorm2_nonneg d
      have hx_nonneg : 0 ≤ finiteVecNorm2 x := finiteVecNorm2_nonneg x
      have hz_nonneg : 0 ≤ finiteVecNorm2 z := finiteVecNorm2_nonneg z
      have hterm₁ : L * finiteVecNorm2 d * finiteVecNorm2 x ≤ L * ρ := by
        have hprod :
            finiteVecNorm2 d * finiteVecNorm2 x ≤ ρ * 1 := by
          exact mul_le_mul hdist' hx hx_nonneg hρ
        have hmul : L * (finiteVecNorm2 d * finiteVecNorm2 x) ≤ L * (ρ * 1) :=
          mul_le_mul_of_nonneg_left hprod hL
        nlinarith
      have hterm₂ :
          L * finiteVecNorm2 z * finiteVecNorm2 d ≤ L * (1 + ρ) * ρ := by
        have honeρ : 0 ≤ 1 + ρ := by nlinarith
        have hprod :
            finiteVecNorm2 z * finiteVecNorm2 d ≤ (1 + ρ) * ρ := by
          exact mul_le_mul hz_bound hdist' hdx_nonneg honeρ
        have hmul :
            L * (finiteVecNorm2 z * finiteVecNorm2 d) ≤
              L * ((1 + ρ) * ρ) :=
          mul_le_mul_of_nonneg_left hprod hL
        nlinarith
      nlinarith
    have hqnet : finiteQuadraticForm M z ≤ η := hnet a
    calc
      finiteQuadraticForm M x
          ≤ finiteQuadraticForm M z +
              |finiteQuadraticForm M x - finiteQuadraticForm M z| := by
              nlinarith [le_abs_self
                (finiteQuadraticForm M x - finiteQuadraticForm M z)]
      _ ≤ η + L * (2 * ρ + ρ ^ 2) := by
              nlinarith [hdiff_abs, hdiff_bound, hqnet]
      _ = C := rfl
  intro x
  rw [finiteQuadraticForm_smul_finiteIdMatrix]
  by_cases hxzero : finiteVecNorm2 x = 0
  · have hx_entries : ∀ i, x i = 0 :=
      (finiteVecNorm2_eq_zero_iff x).mp hxzero
    have hqzero : finiteQuadraticForm M x = 0 := by
      unfold finiteQuadraticForm finiteMatVec
      simp [hx_entries]
    have hsqzero : finiteVecNorm2Sq x = 0 := by
      rw [← finiteVecNorm2_sq, hxzero]
      norm_num
    simp [hqzero, hsqzero]
  · have hxpos : 0 < finiteVecNorm2 x :=
      lt_of_le_of_ne (finiteVecNorm2_nonneg x) (Ne.symm hxzero)
    let y : κ → ℝ := fun i => (finiteVecNorm2 x)⁻¹ * x i
    have hy_norm : finiteVecNorm2 y = 1 := by
      unfold y
      rw [finiteVecNorm2_smul, abs_of_pos (inv_pos.mpr hxpos),
        inv_mul_cancel₀ hxzero]
    have hy_bound : finiteQuadraticForm M y ≤ C :=
      hunit y (by rw [hy_norm])
    have hqscale :
        finiteQuadraticForm M y =
          (finiteVecNorm2 x)⁻¹ ^ 2 * finiteQuadraticForm M x := by
      simpa [y] using
        finiteQuadraticForm_vec_smul M (finiteVecNorm2 x)⁻¹ x
    have hscaled :
        (finiteVecNorm2 x)⁻¹ ^ 2 * finiteQuadraticForm M x ≤ C := by
      simpa [hqscale] using hy_bound
    have hcoeff :
        finiteVecNorm2 x ^ 2 * (finiteVecNorm2 x)⁻¹ ^ 2 = 1 := by
      field_simp [hxzero]
    calc
      finiteQuadraticForm M x
          = finiteVecNorm2 x ^ 2 *
              ((finiteVecNorm2 x)⁻¹ ^ 2 * finiteQuadraticForm M x) := by
              rw [← mul_assoc, hcoeff, one_mul]
      _ ≤ finiteVecNorm2 x ^ 2 * C :=
              mul_le_mul_of_nonneg_left hscaled (sq_nonneg _)
      _ = C * finiteVecNorm2Sq x := by
              rw [← finiteVecNorm2_sq]
              ring

/-- A finite family of test vectors covers the rectangular `Fin n` unit ball at
radius `ρ` if each unit-ball vector is within Euclidean distance `ρ` of some
test vector. -/
def rectUnitBallCover {ι : Type*} {n : ℕ}
    (net : ι → Fin n → ℝ) (ρ : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, vecNorm2 x ≤ 1 →
    ∃ a : ι, vecNorm2 (fun j => x j - net a j) ≤ ρ

/-- A one-dimensional grid covers the real interval `[-1, 1]` at radius `δ`. -/
def realUnitIntervalCover {α : Type*} (grid : α → ℝ) (δ : ℝ) : Prop :=
  ∀ t : ℝ, |t| ≤ 1 → ∃ a : α, |t - grid a| ≤ δ

/-- Coordinatewise product grids give finite covers of the Euclidean unit ball.

This is a constructive reduction for future covering-net arguments: to cover
the `n`-dimensional Euclidean unit ball, it suffices to cover each coordinate
of `[-1,1]` by a one-dimensional grid and pay the Euclidean factor
`sqrt n`. -/
theorem rectUnitBallCover_product_grid {α : Type*} [Fintype α] {n : ℕ}
    (grid : α → ℝ) {δ ρ : ℝ}
    (hgrid : realUnitIntervalCover grid δ)
    (hδ : 0 ≤ δ)
    (hρ : Real.sqrt (n : ℝ) * δ ≤ ρ) :
    rectUnitBallCover
      (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ := by
  intro x hx
  classical
  have hcoord : ∀ j : Fin n, |x j| ≤ 1 := fun j =>
    (abs_coord_le_vecNorm2 x j).trans hx
  have hchoice : ∀ j : Fin n, ∃ a : α, |x j - grid a| ≤ δ :=
    fun j => hgrid (x j) (hcoord j)
  let a : Fin n → α := fun j => Classical.choose (hchoice j)
  refine ⟨a, ?_⟩
  have hentry : ∀ j : Fin n, |x j - grid (a j)| ≤ δ := fun j =>
    Classical.choose_spec (hchoice j)
  have hsq_entry : ∀ j : Fin n, (x j - grid (a j)) ^ 2 ≤ δ ^ 2 := by
    intro j
    exact (sq_le_sq).mpr (by simpa [abs_of_nonneg hδ] using hentry j)
  have hsq :
      vecNorm2Sq (fun j : Fin n => x j - grid (a j)) ≤
        (n : ℝ) * δ ^ 2 := by
    unfold vecNorm2Sq
    calc
      ∑ j : Fin n, (x j - grid (a j)) ^ 2
          ≤ ∑ _j : Fin n, δ ^ 2 := by
              apply Finset.sum_le_sum
              intro j _
              exact hsq_entry j
      _ = (n : ℝ) * δ ^ 2 := by
              simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  calc
    vecNorm2 (fun j : Fin n => x j - grid (a j))
        ≤ Real.sqrt ((n : ℝ) * δ ^ 2) := by
          exact Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (n : ℝ) * δ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs,
            abs_of_nonneg hδ]
    _ ≤ ρ := hρ

/-- A rectangular `Fin n` unit-ball cover is the same cover for the generic
finite-type norm specialized to `Fin n`. -/
theorem finiteUnitBallCover_of_rectUnitBallCover {ι : Type*} {n : ℕ}
    (net : ι → Fin n → ℝ) {ρ : ℝ}
    (hcover : rectUnitBallCover net ρ) :
    finiteUnitBallCover net ρ := by
  intro x hx
  have hx' : vecNorm2 x ≤ 1 := by
    simpa [finiteVecNorm2_fin] using hx
  obtain ⟨a, ha⟩ := hcover x hx'
  refine ⟨a, ?_⟩
  simpa [finiteVecNorm2_fin] using ha

/-- Coordinatewise product grids also give covers for the generic finite-type
unit-ball cover specialized to `Fin n`. -/
theorem finiteUnitBallCover_product_grid {α : Type*} [Fintype α] {n : ℕ}
    (grid : α → ℝ) {δ ρ : ℝ}
    (hgrid : realUnitIntervalCover grid δ)
    (hδ : 0 ≤ δ)
    (hρ : Real.sqrt (n : ℝ) * δ ≤ ρ) :
    finiteUnitBallCover
      (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ :=
  finiteUnitBallCover_of_rectUnitBallCover
    (fun a : Fin n → α => fun j : Fin n => grid (a j))
    (rectUnitBallCover_product_grid grid hgrid hδ hρ)

/-- The index type of an `n`-fold product grid has cardinality `|grid|^n`. -/
theorem fintype_card_product_grid_index (α : Type*) [Fintype α] (n : ℕ) :
    Fintype.card (Fin n → α) = Fintype.card α ^ n := by
  simp

/-- A finite unit-ball cover transfers finitely many vector-action tests and a
    Frobenius residual bound into a rectangular operator-2 bound.

This is deterministic geometry. It does not construct a covering net and does
not prove any probabilistic concentration by itself. -/
theorem rectOpNorm2Le_of_unit_ball_cover {ι : Type*} {m n : ℕ}
    (M : Fin m → Fin n → ℝ) (net : ι → Fin n → ℝ) {ρ η L : ℝ}
    (hcover : rectUnitBallCover net ρ)
    (hnet : ∀ a : ι, vecNorm2 (rectMatMulVec M (net a)) ≤ η)
    (hFrob : frobNormRect M ≤ L) :
    rectOpNorm2Le M (η + L * ρ) := by
  apply rectOpNorm2Le_of_unit_ball_bound
  intro x hx
  obtain ⟨a, hdist⟩ := hcover x hx
  have hL_nonneg : 0 ≤ L := le_trans (frobNormRect_nonneg M) hFrob
  have hsplit :
      rectMatMulVec M x =
        fun i => rectMatMulVec M (net a) i +
          rectMatMulVec M (fun j => x j - net a j) i := by
    ext i
    unfold rectMatMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  calc
    vecNorm2
        (fun i => rectMatMulVec M (net a) i +
          rectMatMulVec M (fun j => x j - net a j) i)
        ≤ vecNorm2 (rectMatMulVec M (net a)) +
            vecNorm2 (rectMatMulVec M (fun j => x j - net a j)) :=
          vecNorm2_add_le _ _
    _ ≤ η + frobNormRect M *
            vecNorm2 (fun j => x j - net a j) := by
          exact add_le_add (hnet a)
            (vecNorm2_rectMatMulVec_le_frobNormRect_mul M
              (fun j => x j - net a j))
    _ ≤ η + L * vecNorm2 (fun j => x j - net a j) := by
          exact add_le_add (le_refl η)
            (mul_le_mul_of_nonneg_right hFrob
              (vecNorm2_nonneg (fun j => x j - net a j)))
    _ ≤ η + L * ρ := by
          exact add_le_add (le_refl η)
            (mul_le_mul_of_nonneg_left hdist hL_nonneg)

/-- A rectangular Frobenius-norm bound implies the corresponding rectangular
    operator-2 bound. -/
theorem rectOpNorm2Le_of_frobNormRect_le {m n : ℕ}
    (M : Fin m → Fin n → ℝ) {c : ℝ}
    (hF : frobNormRect M ≤ c) :
    rectOpNorm2Le M c := by
  intro x
  calc
    vecNorm2 (rectMatMulVec M x)
        ≤ frobNormRect M * vecNorm2 x :=
          vecNorm2_rectMatMulVec_le_frobNormRect_mul M x
    _ ≤ c * vecNorm2 x :=
          mul_le_mul_of_nonneg_right hF (vecNorm2_nonneg x)

/-- Adding a perturbation with Frobenius norm at most `τ` enlarges a rectangular
    operator-2 bound by at most `τ`. -/
theorem rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le {m n : ℕ}
    (M E : Fin m → Fin n → ℝ) {ε τ : ℝ}
    (hM : rectOpNorm2Le M ε)
    (hE : frobNormRect E ≤ τ) :
    rectOpNorm2Le (fun i j => M i j + E i j) (ε + τ) := by
  intro x
  have hsplit :
      rectMatMulVec (fun i j => M i j + E i j) x =
        fun i => rectMatMulVec M x i + rectMatMulVec E x i := by
    ext i
    unfold rectMatMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  calc
    vecNorm2 (fun i => rectMatMulVec M x i + rectMatMulVec E x i)
        ≤ vecNorm2 (rectMatMulVec M x) + vecNorm2 (rectMatMulVec E x) :=
          vecNorm2_add_le _ _
    _ ≤ ε * vecNorm2 x + frobNormRect E * vecNorm2 x := by
          exact add_le_add (hM x) (vecNorm2_rectMatMulVec_le_frobNormRect_mul E x)
    _ ≤ ε * vecNorm2 x + τ * vecNorm2 x := by
          exact add_le_add (le_refl (ε * vecNorm2 x))
            (mul_le_mul_of_nonneg_right hE (vecNorm2_nonneg x))
    _ = (ε + τ) * vecNorm2 x := by ring

-- ============================================================
-- Orthogonal matrices
-- ============================================================

/-- **Orthogonal matrix**: U is orthogonal iff UᵀU = I and UUᵀ = I.
    For finite square real matrices, either condition implies the other,
    but we bundle both for convenience. -/
def IsOrthogonal (n : ℕ) (U : Fin n → Fin n → ℝ) : Prop :=
  IsInverse n U (matTranspose U)

/-- Orthogonal matrices satisfy UᵀU = I (Uᵀ is a left inverse). -/
lemma IsOrthogonal.left_inv {n : ℕ} {U : Fin n → Fin n → ℝ}
    (hU : IsOrthogonal n U) : IsLeftInverse n U (matTranspose U) := hU.1

/-- Orthogonal matrices satisfy UUᵀ = I (Uᵀ is a right inverse). -/
lemma IsOrthogonal.right_inv {n : ℕ} {U : Fin n → Fin n → ℝ}
    (hU : IsOrthogonal n U) : IsRightInverse n U (matTranspose U) := hU.2

/-- For orthogonal U, columns are orthonormal: ∑_k U_ki U_kj = δ_ij. -/
lemma IsOrthogonal.col_orthonormal {n : ℕ} {U : Fin n → Fin n → ℝ}
    (hU : IsOrthogonal n U) (i j : Fin n) :
    ∑ k : Fin n, U k i * U k j = if i = j then 1 else 0 := by
  have := hU.1 i j; unfold matTranspose at this; exact this

/-- Every column of an orthogonal matrix has Euclidean norm one. -/
theorem IsOrthogonal.column_vecNorm2_eq_one {n : ℕ}
    {U : Fin n → Fin n → ℝ} (hU : IsOrthogonal n U) (j : Fin n) :
    vecNorm2 (fun i : Fin n => U i j) = 1 := by
  unfold vecNorm2 vecNorm2Sq
  have hcol : (∑ k : Fin n, U k j * U k j) = 1 := by
    simpa using hU.col_orthonormal j j
  have hsq : (∑ k : Fin n, U k j ^ 2) = 1 := by
    simpa [pow_two] using hcol
  rw [hsq, Real.sqrt_one]

/-- Every column of an orthogonal matrix has Euclidean norm at most one. -/
theorem IsOrthogonal.column_vecNorm2_le_one {n : ℕ}
    {U : Fin n → Fin n → ℝ} (hU : IsOrthogonal n U) (j : Fin n) :
    vecNorm2 (fun i : Fin n => U i j) ≤ 1 := by
  exact le_of_eq (hU.column_vecNorm2_eq_one j)

/-- For orthogonal U, rows are orthonormal: ∑_k U_ik U_jk = δ_ij. -/
lemma IsOrthogonal.row_orthonormal {n : ℕ} {U : Fin n → Fin n → ℝ}
    (hU : IsOrthogonal n U) (i j : Fin n) :
    ∑ k : Fin n, U i k * U j k = if i = j then 1 else 0 := by
  have := hU.2 i j; unfold matTranspose at this; exact this

/-- The identity matrix is orthogonal. -/
theorem IsOrthogonal.id (n : ℕ) : IsOrthogonal n (idMatrix n) := by
  constructor
  · intro i j
    unfold matTranspose idMatrix
    simp [Finset.mem_univ, eq_comm]
  · intro i j
    unfold matTranspose idMatrix
    simp [Finset.mem_univ]

/-- A diagonal matrix with diagonal entries of square one is orthogonal.

This is the deterministic matrix-algebra piece behind randomized sign
preconditioners such as the diagonal sign matrix in an SRHT. -/
theorem IsOrthogonal.diagMatrix_of_sq_eq_one {n : ℕ} (d : Fin n → ℝ)
    (hd : ∀ i : Fin n, d i ^ 2 = 1) :
    IsOrthogonal n (diagMatrix d) := by
  constructor
  · intro i j
    unfold matTranspose diagMatrix
    by_cases hij : i = j
    · subst j
      simpa [pow_two] using hd i
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]
  · intro i j
    unfold matTranspose diagMatrix
    by_cases hij : i = j
    · subst j
      simpa [pow_two] using hd i
    · simp [hij]

/-- The squared Euclidean norm is invariant under multiplication by an
    orthogonal matrix. -/
theorem vecNorm2Sq_orthogonal {n : ℕ}
    (U : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hU : IsOrthogonal n U) :
    vecNorm2Sq (matMulVec n U x) = vecNorm2Sq x := by
  unfold vecNorm2Sq matMulVec
  have expand : ∀ i : Fin n,
      (∑ k : Fin n, U i k * x k) ^ 2 =
        ∑ k : Fin n, ∑ l : Fin n, U i k * U i l * (x k * x l) := by
    intro i
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  have collapse : ∀ k : Fin n,
      ∑ i : Fin n, ∑ l : Fin n, U i k * U i l * (x k * x l) =
        x k ^ 2 := by
    intro k
    rw [Finset.sum_comm]
    have factor : ∀ l : Fin n,
        ∑ i : Fin n, U i k * U i l * (x k * x l) =
          (∑ i : Fin n, U i k * U i l) * (x k * x l) := by
      intro l
      rw [← Finset.sum_mul]
    simp_rw [factor, hU.col_orthonormal]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
    ring
  exact Finset.sum_congr rfl (fun k _ => collapse k)

/-- The Euclidean norm is invariant under multiplication by an orthogonal
    matrix. -/
theorem vecNorm2_orthogonal {n : ℕ}
    (U : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hU : IsOrthogonal n U) :
    vecNorm2 (matMulVec n U x) = vecNorm2 x := by
  unfold vecNorm2
  rw [vecNorm2Sq_orthogonal U x hU]

/-- Left multiplication of a rectangular matrix by a square matrix. -/
def matMulRectLeft {m n : ℕ} (U : Fin m → Fin m → ℝ)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => ∑ k : Fin m, U i k * A k j

/-- General rectangular matrix product. -/
def rectMatMul {m n p : ℕ} (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin p → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- Rectangular products act associatively on vectors. -/
theorem rectMatMulVec_rectMatMul {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (x : Fin p → ℝ) :
    rectMatMulVec (rectMatMul A B) x =
      rectMatMulVec A (rectMatMulVec B x) := by
  ext i
  unfold rectMatMulVec rectMatMul
  calc
    (∑ j : Fin p, (∑ k : Fin n, A i k * B k j) * x j)
        = ∑ j : Fin p, ∑ k : Fin n, (A i k * B k j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ = ∑ k : Fin n, ∑ j : Fin p, (A i k * B k j) * x j := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin n, A i k * ∑ j : Fin p, B k j * x j := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring

/-- A matrix-level left inverse is also a left inverse for the associated
    rectangular matrix-vector action. -/
theorem rectMatMulVec_left_inverse_of_IsLeftInverse
    {n : ℕ} {T T_inv : Fin n → Fin n → ℝ}
    (hInv : IsLeftInverse n T T_inv) :
    ∀ x : Fin n → ℝ, rectMatMulVec T_inv (rectMatMulVec T x) = x := by
  intro x
  ext i
  unfold rectMatMulVec
  calc
    (∑ j : Fin n, T_inv i j * ∑ k : Fin n, T j k * x k)
        = ∑ j : Fin n, ∑ k : Fin n, T_inv i j * (T j k * x k) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ j : Fin n, T_inv i j * (T j k * x k) := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin n, (∑ j : Fin n, T_inv i j * T j k) * x k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = ∑ k : Fin n, (if i = k then (1 : ℝ) else 0) * x k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hInv i k]
    _ = x i := by
            simp

/-- Rectangular operator-2 certificates compose over matrix multiplication. -/
theorem rectOpNorm2Le_rectMatMul {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    {cA cB : ℝ} (hcA : 0 ≤ cA)
    (hA : rectOpNorm2Le A cA) (hB : rectOpNorm2Le B cB) :
    rectOpNorm2Le (rectMatMul A B) (cA * cB) := by
  intro x
  rw [rectMatMulVec_rectMatMul]
  calc
    vecNorm2 (rectMatMulVec A (rectMatMulVec B x))
        ≤ cA * vecNorm2 (rectMatMulVec B x) := hA _
    _ ≤ cA * (cB * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left (hB x) hcA
    _ = (cA * cB) * vecNorm2 x := by ring

/-- Right multiplication of a rectangular matrix by a square matrix. -/
def matMulRectRight {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (V : Fin n → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, A i k * V k j

/-- Rectangular Frobenius submultiplicativity:
    `||AB||_F <= ||A||_F ||B||_F` for compatible rectangular matrices. -/
theorem frobNormRect_rectMatMul_le {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ) :
    frobNormRect (rectMatMul A B) ≤ frobNormRect A * frobNormRect B := by
  have hA : 0 ≤ frobNormRect A := frobNormRect_nonneg A
  apply frobNormRect_le_of_col_vecNorm2_le_rect (rectMatMul A B) B hA
  intro j
  simpa [rectMatMul, rectMatMulVec] using
    (vecNorm2_rectMatMulVec_le_frobNormRect_mul A (fun k : Fin n => B k j))

/-- Entrywise forward-error composition for a computed rectangular product.

The exact product uses `X * Y`; the implementation supplies rounded inputs
`Xhat`, `Yhat`, and a rounded product `Mhat`.  If the row/column contraction
of the left input error is bounded by `alpha`, the row/column contraction of
the right input error is bounded by `beta`, and the final rounded product of
`Xhat` and `Yhat` is within `rho`, then each entry of the exact product is
within `alpha + beta + rho` of `Mhat`. -/
theorem rectMatMul_entry_abs_sub_computed_le_of_component_sums {m n p : ℕ}
    (X Xhat : Fin m → Fin n → ℝ)
    (Y Yhat : Fin n → Fin p → ℝ)
    (Mhat : Fin m → Fin p → ℝ)
    {alpha beta rho : ℝ}
    (hLeft :
      ∀ i k, ∑ j : Fin n, |X i j - Xhat i j| * |Y j k| ≤ alpha)
    (hRight :
      ∀ i k, ∑ j : Fin n, |Xhat i j| * |Y j k - Yhat j k| ≤ beta)
    (hRound :
      ∀ i k, |(∑ j : Fin n, Xhat i j * Yhat j k) - Mhat i k| ≤ rho) :
    ∀ i k,
      |(∑ j : Fin n, X i j * Y j k) - Mhat i k| ≤ alpha + beta + rho := by
  intro i k
  let Aerr : ℝ := ∑ j : Fin n, (X i j - Xhat i j) * Y j k
  let Berr : ℝ := ∑ j : Fin n, Xhat i j * (Y j k - Yhat j k)
  let Rerr : ℝ := (∑ j : Fin n, Xhat i j * Yhat j k) - Mhat i k
  have hsplit :
      (∑ j : Fin n, X i j * Y j k) - Mhat i k = Aerr + Berr + Rerr := by
    unfold Aerr Berr Rerr
    calc
      (∑ j : Fin n, X i j * Y j k) - Mhat i k
          =
            (∑ j : Fin n,
              ((X i j - Xhat i j) * Y j k +
                Xhat i j * (Y j k - Yhat j k) +
                Xhat i j * Yhat j k)) - Mhat i k := by
              congr 1
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ =
            (∑ j : Fin n, (X i j - Xhat i j) * Y j k) +
              (∑ j : Fin n, Xhat i j * (Y j k - Yhat j k)) +
              ((∑ j : Fin n, Xhat i j * Yhat j k) - Mhat i k) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
              ring
  have hA_sum :
      |Aerr| ≤ ∑ j : Fin n, |X i j - Xhat i j| * |Y j k| := by
    unfold Aerr
    calc
      |∑ j : Fin n, (X i j - Xhat i j) * Y j k|
          ≤ ∑ j : Fin n, |(X i j - Xhat i j) * Y j k| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |X i j - Xhat i j| * |Y j k| := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul (X i j - Xhat i j) (Y j k)
  have hB_sum :
      |Berr| ≤ ∑ j : Fin n, |Xhat i j| * |Y j k - Yhat j k| := by
    unfold Berr
    calc
      |∑ j : Fin n, Xhat i j * (Y j k - Yhat j k)|
          ≤ ∑ j : Fin n, |Xhat i j * (Y j k - Yhat j k)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |Xhat i j| * |Y j k - Yhat j k| := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul (Xhat i j) (Y j k - Yhat j k)
  have hA : |Aerr| ≤ alpha := le_trans hA_sum (hLeft i k)
  have hB : |Berr| ≤ beta := le_trans hB_sum (hRight i k)
  have hR : |Rerr| ≤ rho := by
    unfold Rerr
    exact hRound i k
  calc
    |(∑ j : Fin n, X i j * Y j k) - Mhat i k|
        = |Aerr + Berr + Rerr| := by rw [hsplit]
    _ ≤ |Aerr| + |Berr| + |Rerr| := by
        have hAB : |Aerr + Berr| ≤ |Aerr| + |Berr| := abs_add_le Aerr Berr
        have hABC : |Aerr + Berr + Rerr| ≤ |Aerr + Berr| + |Rerr| :=
          abs_add_le (Aerr + Berr) Rerr
        linarith
    _ ≤ alpha + beta + rho := by
        linarith

/-- Left multiplication of a rectangular matrix by the square identity. -/
theorem matMulRectLeft_id {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    matMulRectLeft (idMatrix m) A = A := by
  ext i j
  unfold matMulRectLeft idMatrix
  simp [Finset.mem_univ]

/-- Associativity for a square left factor acting on a rectangular matrix. -/
theorem matMulRectLeft_assoc {m n : ℕ}
    (U V : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ) :
    matMulRectLeft (matMul m U V) A =
      matMulRectLeft U (matMulRectLeft V A) := by
  ext i j
  unfold matMulRectLeft matMul
  calc
    (∑ k : Fin m, (∑ l : Fin m, U i l * V l k) * A k j)
        = ∑ k : Fin m, ∑ l : Fin m, (U i l * V l k) * A k j := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ = ∑ l : Fin m, ∑ k : Fin m, (U i l * V l k) * A k j := by
            rw [Finset.sum_comm]
    _ = ∑ l : Fin m, U i l * ∑ k : Fin m, V l k * A k j := by
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring

/-- Left multiplication is additive in the square left factor. -/
theorem matMulRectLeft_add_left {m n : ℕ}
    (U V : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ) :
    matMulRectLeft (fun i j => U i j + V i j) A =
      fun i j => matMulRectLeft U A i j + matMulRectLeft V A i j := by
  ext i j
  unfold matMulRectLeft
  simp [add_mul, Finset.sum_add_distrib]

/-- Left multiplication is additive in the rectangular right factor. -/
theorem matMulRectLeft_add_right {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A B : Fin m → Fin n → ℝ) :
    matMulRectLeft U (fun i j => A i j + B i j) =
      fun i j => matMulRectLeft U A i j + matMulRectLeft U B i j := by
  ext i j
  unfold matMulRectLeft
  simp [mul_add, Finset.sum_add_distrib]

/-- The squared rectangular Frobenius norm is invariant under left
    multiplication by an orthogonal square matrix.  This is the rectangular
    version of `frobNormSq_orthogonal_left` and is a basic dependency for a
    future rectangular Householder QR stability theorem. -/
theorem frobNormSqRect_orthogonal_left {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hU : IsOrthogonal m U) :
    frobNormSqRect (matMulRectLeft U A) = frobNormSqRect A := by
  unfold frobNormSqRect matMulRectLeft
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have expand : ∀ i : Fin m,
      (∑ k : Fin m, U i k * A k j) ^ 2 =
        ∑ k : Fin m, ∑ l : Fin m,
          U i k * U i l * (A k j * A l j) := by
    intro i
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  have collapse : ∀ k : Fin m,
      ∑ i : Fin m, ∑ l : Fin m,
          U i k * U i l * (A k j * A l j) =
        A k j ^ 2 := by
    intro k
    rw [Finset.sum_comm]
    have factor : ∀ l : Fin m,
        ∑ i : Fin m, U i k * U i l * (A k j * A l j) =
          (∑ i : Fin m, U i k * U i l) * (A k j * A l j) := by
      intro l
      rw [← Finset.sum_mul]
    simp_rw [factor, hU.col_orthonormal]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
    ring
  exact Finset.sum_congr rfl (fun k _ => collapse k)

/-- The rectangular Frobenius norm is invariant under left multiplication by
    an orthogonal square matrix. -/
theorem frobNormRect_orthogonal_left {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hU : IsOrthogonal m U) :
    frobNormRect (matMulRectLeft U A) = frobNormRect A := by
  unfold frobNormRect
  rw [frobNormSqRect_orthogonal_left U A hU]

/-- The squared rectangular Frobenius norm is invariant under right
    multiplication by an orthogonal square matrix. -/
theorem frobNormSqRect_orthogonal_right {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin n → ℝ)
    (hV : IsOrthogonal n V) :
    frobNormSqRect (matMulRectRight A V) = frobNormSqRect A := by
  unfold frobNormSqRect matMulRectRight
  apply Finset.sum_congr rfl
  intro i _
  have expand : ∀ j : Fin n,
      (∑ k : Fin n, A i k * V k j) ^ 2 =
        ∑ k : Fin n, ∑ l : Fin n,
          A i k * A i l * (V k j * V l j) := by
    intro j
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [expand]
  have collapse : ∀ k : Fin n,
      ∑ j : Fin n, ∑ l : Fin n,
          A i k * A i l * (V k j * V l j) =
        A i k ^ 2 := by
    intro k
    rw [Finset.sum_comm]
    have factor : ∀ l : Fin n,
        ∑ j : Fin n, A i k * A i l * (V k j * V l j) =
          A i k * A i l * (∑ j : Fin n, V k j * V l j) := by
      intro l
      rw [Finset.mul_sum]
    simp_rw [factor, hV.row_orthonormal]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
    ring
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => collapse k)

/-- The rectangular Frobenius norm is invariant under right multiplication by
    an orthogonal square matrix. -/
theorem frobNormRect_orthogonal_right {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin n → ℝ)
    (hV : IsOrthogonal n V) :
    frobNormRect (matMulRectRight A V) = frobNormRect A := by
  unfold frobNormRect
  rw [frobNormSqRect_orthogonal_right A V hV]

/-- Rectangular Frobenius submultiplicativity for a square factor on the left. -/
theorem frobNormRect_matMulRectLeft_le {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ) :
    frobNormRect (matMulRectLeft U A) ≤ frobNorm U * frobNormRect A := by
  rw [frobNormRect_eq_frobNormFn, frobNormRect_eq_frobNormFn]
  unfold matMulRectLeft
  simpa [Matrix.mul_apply, Matrix.of_apply] using
    (Matrix.frobenius_norm_mul (Matrix.of U : Matrix (Fin m) (Fin m) ℝ)
      (Matrix.of A : Matrix (Fin m) (Fin n) ℝ))

/-- Rectangular Frobenius submultiplicativity for a square factor on the right. -/
theorem frobNormRect_matMulRectRight_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin n → ℝ) :
    frobNormRect (matMulRectRight A V) ≤ frobNormRect A * frobNorm V := by
  rw [frobNormRect_eq_frobNormFn, frobNormRect_eq_frobNormFn]
  unfold matMulRectRight
  simpa [Matrix.mul_apply, Matrix.of_apply] using
    (Matrix.frobenius_norm_mul (Matrix.of A : Matrix (Fin m) (Fin n) ℝ)
      (Matrix.of V : Matrix (Fin n) (Fin n) ℝ))

/-- Squared Frobenius bound for left multiplication by a square matrix followed
by a rectangular factor whose transpose action has an operator-2 certificate:
`||Sigma M||_F^2 <= eps^2 ||Sigma||_F^2`.

The hypothesis is deliberately stated on `finiteTranspose M`.  This is the
right-acting certificate needed by row-wise Frobenius summation; proving that it
is equivalent to an ordinary spectral-norm certificate for `M` is a separate
transpose-operator-norm foundation. -/
theorem frobNormSqRect_matMulRectLeft_le_sq_mul_of_transpose_rectOpNorm2Le
    {q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (M : Fin q → Fin r → ℝ)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hM : rectOpNorm2Le (finiteTranspose M) eps) :
    frobNormSqRect (matMulRectLeft Sigma M) ≤
      eps ^ 2 * frobNormSq Sigma := by
  unfold frobNormSqRect frobNormSq
  calc
    (∑ a : Fin q, ∑ b : Fin r, matMulRectLeft Sigma M a b ^ 2)
        ≤ ∑ a : Fin q, eps ^ 2 * ∑ c : Fin q, Sigma a c ^ 2 := by
          apply Finset.sum_le_sum
          intro a _
          have hrow_eq :
              (fun b : Fin r => matMulRectLeft Sigma M a b) =
                rectMatMulVec (finiteTranspose M)
                  (fun c : Fin q => Sigma a c) := by
            ext b
            unfold matMulRectLeft rectMatMulVec finiteTranspose
            apply Finset.sum_congr rfl
            intro c _
            ring
          have hnorm :
              vecNorm2 (fun b : Fin r => matMulRectLeft Sigma M a b) ≤
                eps * vecNorm2 (fun c : Fin q => Sigma a c) := by
            simpa [hrow_eq] using hM (fun c : Fin q => Sigma a c)
          have hright_nonneg :
              0 ≤ eps * vecNorm2 (fun c : Fin q => Sigma a c) :=
            mul_nonneg heps (vecNorm2_nonneg _)
          have hsquare :
              vecNorm2 (fun b : Fin r => matMulRectLeft Sigma M a b) ^ 2 ≤
                (eps * vecNorm2 (fun c : Fin q => Sigma a c)) ^ 2 := by
            nlinarith [vecNorm2_nonneg
              (fun b : Fin r => matMulRectLeft Sigma M a b), hright_nonneg]
          have hright :
              (eps * vecNorm2 (fun c : Fin q => Sigma a c)) ^ 2 =
                eps ^ 2 * vecNorm2Sq (fun c : Fin q => Sigma a c) := by
            rw [show (eps * vecNorm2 (fun c : Fin q => Sigma a c)) ^ 2 =
                eps ^ 2 * vecNorm2 (fun c : Fin q => Sigma a c) ^ 2 by ring,
              vecNorm2_sq]
          simpa [vecNorm2_sq, vecNorm2Sq, hright] using hsquare
    _ = eps ^ 2 * ∑ a : Fin q, ∑ c : Fin q, Sigma a c ^ 2 := by
          rw [Finset.mul_sum]

/-- Norm form of the transpose-action spectral certificate:
`||Sigma M||_F <= eps ||Sigma||_F`. -/
theorem frobNormRect_matMulRectLeft_le_of_transpose_rectOpNorm2Le
    {q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (M : Fin q → Fin r → ℝ)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hM : rectOpNorm2Le (finiteTranspose M) eps) :
    frobNormRect (matMulRectLeft Sigma M) ≤ eps * frobNorm Sigma := by
  have hsq :
      frobNormSqRect (matMulRectLeft Sigma M) ≤
        (eps * frobNorm Sigma) ^ 2 := by
    calc
      frobNormSqRect (matMulRectLeft Sigma M)
          ≤ eps ^ 2 * frobNormSq Sigma :=
            frobNormSqRect_matMulRectLeft_le_sq_mul_of_transpose_rectOpNorm2Le
              Sigma M heps hM
      _ = (eps * frobNorm Sigma) ^ 2 := by
          rw [show (eps * frobNorm Sigma) ^ 2 =
              eps ^ 2 * frobNorm Sigma ^ 2 by ring, frobNorm_sq]
  have hsqrt := Real.sqrt_le_sqrt hsq
  have hright_nonneg : 0 ≤ eps * frobNorm Sigma :=
    mul_nonneg heps (frobNorm_nonneg Sigma)
  simpa [frobNormRect, Real.sqrt_sq_eq_abs, abs_of_nonneg hright_nonneg]
    using hsqrt

/-- Frobenius norm is invariant under left multiplication by orthogonal matrix:
    ‖UA‖²_F = ‖A‖²_F.

    Proof: ‖UA‖²_F = tr((UA)ᵀUA) = tr(AᵀUᵀUA) = tr(AᵀA) = ‖A‖²_F.
    We prove this directly by expanding sums and using orthogonality. -/
theorem frobNormSq_orthogonal_left {n : ℕ} (U A : Fin n → Fin n → ℝ)
    (hU : IsOrthogonal n U) :
    frobNormSq (matMul n U A) = frobNormSq A := by
  unfold frobNormSq matMul
  -- ∑_i ∑_j (∑_k U_ik A_kj)² = ∑_i ∑_j A_ij²
  -- Strategy: swap to ∑_j ∑_i on LHS, then for fixed j show
  -- ∑_i (∑_k U_ik A_kj)² = ∑_k A_kj² via column orthogonality.
  conv_lhs => rw [Finset.sum_comm]
  -- LHS is now ∑_j ∑_i (∑_k U_ik A_kj)², RHS is still ∑_i ∑_j A_ij²
  conv_rhs => rw [Finset.sum_comm]
  -- RHS is now ∑_j ∑_i A_ij²
  apply Finset.sum_congr rfl; intro j _
  -- Goal: ∑_i (∑_k U_ik A_kj)² = ∑_i A_ij²
  -- For fixed j, expand and use column orthogonality of U.
  have expand : ∀ i : Fin n,
      (∑ k : Fin n, U i k * A k j) ^ 2 =
      ∑ k : Fin n, ∑ l : Fin n, U i k * U i l * (A k j * A l j) := by
    intro i; rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _; ring
  simp_rw [expand]
  -- Goal: ∑_i ∑_k ∑_l U_ik U_il (A_kj A_lj) = ∑_i A_ij²
  -- Swap to ∑_k ∑_i ∑_l, then ∑_k ∑_l ∑_i
  rw [Finset.sum_comm]
  -- Goal: ∑_k ∑_i ∑_l U_ik U_il (A_kj A_lj) = ∑_i A_ij²
  -- For fixed k, collapse using orthogonality
  have collapse : ∀ k : Fin n,
      ∑ i : Fin n, ∑ l : Fin n, U i k * U i l * (A k j * A l j) = A k j ^ 2 := by
    intro k; rw [Finset.sum_comm]
    -- ∑_l ∑_i U_ik U_il (A_kj A_lj) = A_kj²
    -- Factor: ∑_i U_ik U_il (A_kj A_lj) = (∑_i U_ik U_il)(A_kj A_lj)
    have factor : ∀ l : Fin n,
        ∑ i : Fin n, U i k * U i l * (A k j * A l j) =
        (∑ i : Fin n, U i k * U i l) * (A k j * A l j) := by
      intro l; rw [← Finset.sum_mul]
    simp_rw [factor, hU.col_orthonormal]
    simp [Finset.sum_ite_eq, Finset.mem_univ]; ring
  exact Finset.sum_congr rfl (fun k _ => collapse k)

/-- Frobenius norm is invariant under right multiplication by orthogonal matrix:
    ‖AV‖²_F = ‖A‖²_F. -/
theorem frobNormSq_orthogonal_right {n : ℕ} (A V : Fin n → Fin n → ℝ)
    (hV : IsOrthogonal n V) :
    frobNormSq (matMul n A V) = frobNormSq A := by
  unfold frobNormSq matMul
  -- For fixed i: ∑_j (∑_k A_ik V_kj)² = ∑_k A_ik² (by row orthogonality of V)
  apply Finset.sum_congr rfl; intro i _
  have expand : ∀ j : Fin n,
      (∑ k : Fin n, A i k * V k j) ^ 2 =
      ∑ k : Fin n, ∑ l : Fin n, A i k * A i l * (V k j * V l j) := by
    intro j; rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _; ring
  simp_rw [expand]
  have collapse : ∀ k : Fin n,
      ∑ j : Fin n, ∑ l : Fin n, A i k * A i l * (V k j * V l j) = A i k ^ 2 := by
    intro k
    rw [Finset.sum_comm]
    have factor : ∀ l : Fin n,
        ∑ j : Fin n, A i k * A i l * (V k j * V l j) =
        A i k * A i l * (∑ j : Fin n, V k j * V l j) := by
      intro l; rw [Finset.mul_sum]
    simp_rw [factor, hV.row_orthonormal]
    simp [Finset.sum_ite_eq, Finset.mem_univ]; ring
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => collapse k)

/-- ‖UA‖_F = ‖A‖_F when U is orthogonal. -/
theorem frobNorm_orthogonal_left {n : ℕ} (U A : Fin n → Fin n → ℝ)
    (hU : IsOrthogonal n U) :
    frobNorm (matMul n U A) = frobNorm A := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNorm_eq_sqrt_frobNormSq,
    frobNormSq_orthogonal_left U A hU]

/-- ‖AV‖_F = ‖A‖_F when V is orthogonal. -/
theorem frobNorm_orthogonal_right {n : ℕ} (A V : Fin n → Fin n → ℝ)
    (hV : IsOrthogonal n V) :
    frobNorm (matMul n A V) = frobNorm A := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNorm_eq_sqrt_frobNormSq,
    frobNormSq_orthogonal_right A V hV]

/-- Transpose of orthogonal matrix is orthogonal.

    Since (Uᵀ)ᵀ = U, we have (Uᵀ)ᵀUᵀ = UUᵀ = I and Uᵀ(Uᵀ)ᵀ = UᵀU = I. -/
theorem IsOrthogonal.transpose {n : ℕ} {U : Fin n → Fin n → ℝ}
    (hU : IsOrthogonal n U) : IsOrthogonal n (matTranspose U) :=
  -- matTranspose (matTranspose U) = U definitionally at each entry,
  -- so IsLeftInverse for Uᵀ is IsRightInverse for U and vice versa.
  ⟨hU.right_inv, hU.left_inv⟩

/-- An orthogonal matrix has operator 2-norm at most one. -/
theorem IsOrthogonal.opNorm2Le_one {n : ℕ} {U : Fin n → Fin n → ℝ}
    (hU : IsOrthogonal n U) : opNorm2Le U 1 := by
  intro x
  calc
    vecNorm2 (matMulVec n U x) = vecNorm2 x :=
      vecNorm2_orthogonal U x hU
    _ ≤ 1 * vecNorm2 x := by simp

/-- The transpose/inverse of an orthogonal matrix also has operator 2-norm at
most one.  This is the symmetric-eigenbasis conditioning bridge used by the
inverse-iteration route. -/
theorem IsOrthogonal.transpose_opNorm2Le_one {n : ℕ}
    {U : Fin n → Fin n → ℝ} (hU : IsOrthogonal n U) :
    opNorm2Le (matTranspose U) 1 :=
  hU.transpose.opNorm2Le_one

/-- Product of orthogonal matrices is orthogonal.

    Proof: (UV)ᵀ(UV) = VᵀUᵀUV = VᵀV = I and
    (UV)(UV)ᵀ = UVVᵀUᵀ = UUᵀ = I, both by expanding sums and
    using column/row orthonormality of U and V. -/
theorem IsOrthogonal.mul {n : ℕ} {U V : Fin n → Fin n → ℝ}
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    IsOrthogonal n (matMul n U V) := by
  constructor
  · -- Left inverse: (UV)ᵀ(UV) = I
    intro i j
    have h1 : ∀ k : Fin n,
        matTranspose (matMul n U V) i k = ∑ l : Fin n, U k l * V l i := by
      intro k; rfl
    have h2 : ∀ k : Fin n,
        matMul n U V k j = ∑ m : Fin n, U k m * V m j := by
      intro k; rfl
    simp_rw [h1, h2]
    -- Goal: ∑_k (∑_l U_{kl} V_{li}) * (∑_m U_{km} V_{mj}) = δ_{ij}
    -- Step 1: distribute to triple sum ∑_k ∑_l ∑_m
    conv_lhs => arg 2; ext k; rw [Finset.sum_mul]
    conv_lhs => arg 2; ext k; arg 2; ext l; rw [Finset.mul_sum]
    -- Step 2: swap to ∑_l ∑_m ∑_k
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
    -- Step 3: factor out V terms and use column orthonormality of U
    conv_lhs =>
      arg 2; ext l; arg 2; ext m; arg 2; ext k
      rw [show U k l * V l i * (U k m * V m j) =
          V l i * V m j * (U k l * U k m) by ring]
    simp_rw [← Finset.mul_sum, hU.col_orthonormal]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
    exact hV.col_orthonormal i j
  · -- Right inverse: (UV)(UV)ᵀ = I
    intro i j
    have h1 : ∀ k : Fin n,
        matMul n U V i k = ∑ l : Fin n, U i l * V l k := by
      intro k; rfl
    have h2 : ∀ k : Fin n,
        matTranspose (matMul n U V) k j = ∑ m : Fin n, U j m * V m k := by
      intro k; rfl
    simp_rw [h1, h2]
    conv_lhs => arg 2; ext k; rw [Finset.sum_mul]
    conv_lhs => arg 2; ext k; arg 2; ext l; rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext l; arg 2; ext m; arg 2; ext k
      rw [show U i l * V l k * (U j m * V m k) =
          U i l * U j m * (V l k * V m k) by ring]
    simp_rw [← Finset.mul_sum, hV.row_orthonormal]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
    exact hU.row_orthonormal i j

-- ============================================================
-- Infinity norm bounds for Neumann series
-- ============================================================

/-- **Infinity norm bound**: `‖M‖∞ ≤ c`.

    Earlier versions used the equivalent row-wise predicate
    `∀ i, ∑ j, |M i j| ≤ c`. With total `infNorm`, the norm inequality is the
    cleaner public statement; `row_sum_le_of_infNormBound` recovers the row-wise
    form needed inside Neumann-series proofs. -/
def infNormBound (n : ℕ) (M : Fin n → Fin n → ℝ) (c : ℝ) : Prop :=
  infNorm M ≤ c

/-- A row-wise proof gives an ∞-norm bound. -/
lemma infNormBound_of_row_sum_le {n : ℕ} (A : Fin n → Fin n → ℝ) {c : ℝ}
    (hrows : ∀ i : Fin n, ∑ j : Fin n, |A i j| ≤ c) (hc : 0 ≤ c) :
    infNormBound n A c := by
  exact infNorm_le_of_row_sum_le A hrows hc

/-- An ∞-norm bound implies every row sum is bounded. -/
lemma row_sum_le_of_infNormBound {n : ℕ} {A : Fin n → Fin n → ℝ} {c : ℝ}
    (hbound : infNormBound n A c) (i : Fin n) :
    ∑ j : Fin n, |A i j| ≤ c :=
  le_trans (row_sum_le_infNorm A i) hbound

-- ============================================================
-- Nonneg matrix power entry bounds
-- ============================================================

/-- Nonneg matrix has nonneg entries in all powers. -/
theorem matPow_nonneg (n : ℕ) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (k : ℕ) :
    ∀ i j, 0 ≤ matPow n M k i j := by
  induction k with
  | zero => intro i j; unfold matPow idMatrix; split <;> linarith
  | succ k ih =>
    intro i j; unfold matPow matMul
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (hM i l) (ih l j))

/-- **Row sum bound for M^k** when M ≥ 0 and ‖M‖∞ ≤ c.

    If M ≥ 0 and ∑_j M_{ij} ≤ c for all i, then ∑_j (M^k)_{ij} ≤ c^k. -/
theorem matPow_infNorm_bound (n : ℕ) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (c : ℝ) (hc : 0 ≤ c)
    (hbound : infNormBound n M c) (k : ℕ) :
    infNormBound n (matPow n M k) (c ^ k) := by
  induction k with
  | zero =>
    apply infNormBound_of_row_sum_le
    · intro i; simp only [matPow, pow_zero]
      unfold idMatrix
      have : ∀ j : Fin n, |if i = j then (1 : ℝ) else 0| = if i = j then 1 else 0 := by
        intro j; split <;> simp
      simp_rw [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]; linarith
    · norm_num
  | succ k ih =>
    apply infNormBound_of_row_sum_le
    · intro i; simp only [matPow_succ, pow_succ']
      unfold matMul
      -- ∑_j |∑_l M_{il} M^k_{lj}| ≤ ∑_j ∑_l M_{il} · M^k_{lj}  (all nonneg)
      -- = ∑_l M_{il} · (∑_j M^k_{lj}) ≤ ∑_l M_{il} · c^k ≤ c · c^k
      calc ∑ j : Fin n, |∑ l : Fin n, M i l * matPow n M k l j|
          = ∑ j : Fin n, ∑ l : Fin n, M i l * matPow n M k l j := by
            congr 1; ext j; rw [abs_of_nonneg]
            exact Finset.sum_nonneg (fun l _ => mul_nonneg (hM i l) (matPow_nonneg n M hM k l j))
        _ = ∑ l : Fin n, M i l * ∑ j : Fin n, matPow n M k l j := by
            rw [Finset.sum_comm]; congr 1; ext l; rw [Finset.mul_sum]
        _ ≤ ∑ l : Fin n, M i l * c ^ k := by
            apply Finset.sum_le_sum; intro l _
            apply mul_le_mul_of_nonneg_left _ (hM i l)
            calc ∑ j : Fin n, matPow n M k l j
                = ∑ j : Fin n, |matPow n M k l j| := by
                  congr 1; ext j; rw [abs_of_nonneg (matPow_nonneg n M hM k l j)]
              _ ≤ c ^ k := row_sum_le_of_infNormBound ih l
        _ = c ^ k * ∑ l : Fin n, M i l := by rw [Finset.mul_sum]; congr 1; ext l; ring
        _ ≤ c ^ k * c := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc k)
            calc ∑ l : Fin n, M i l = ∑ l : Fin n, |M i l| := by
                  congr 1; ext l; rw [abs_of_nonneg (hM i l)]
              _ ≤ c := row_sum_le_of_infNormBound hbound i
        _ = c * c ^ k := by ring
    · exact pow_nonneg hc (k + 1)

-- ============================================================
-- ∞-norm submultiplicativity (general, no nonneg requirement)
-- ============================================================

/-- **∞-norm submultiplicativity**: ‖AB‖∞ ≤ ‖A‖∞ · ‖B‖∞.
    Unlike `matPow_infNorm_bound`, this requires no nonnegativity hypothesis. -/
theorem infNorm_matMul_le {n : ℕ} (_hn : 0 < n)
    (A B : Fin n → Fin n → ℝ) :
    infNorm (matMul n A B) ≤ infNorm A * infNorm B := by
  unfold infNorm matMul
  simpa [Matrix.mul_apply] using
    (Matrix.linfty_opNorm_mul (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
      (Matrix.of B : Matrix (Fin n) (Fin n) ℝ))

/-- **‖M^k‖∞ ≤ ‖M‖∞^k** for any matrix (no nonneg requirement).
    Generalizes `matPow_infNorm_bound` by removing the M ≥ 0 hypothesis. -/
theorem infNorm_matPow_le {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (k : ℕ) :
    infNorm (matPow n M k) ≤ infNorm M ^ k := by
  induction k with
  | zero =>
    simp only [matPow, pow_zero]
    apply infNorm_le_of_row_sum_le
    · intro i
      unfold idMatrix
      have : ∀ j : Fin n, |if i = j then (1 : ℝ) else 0| = if i = j then 1 else 0 := by
        intro j; split <;> simp
      simp_rw [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]; linarith
    · norm_num
  | succ k ih =>
    have hnn := infNorm_nonneg M
    calc infNorm (matPow n M (k + 1))
        = infNorm (matMul n M (matPow n M k)) := by rw [matPow_succ]
      _ ≤ infNorm M * infNorm (matPow n M k) := infNorm_matMul_le hn M _
      _ ≤ infNorm M * infNorm M ^ k :=
          mul_le_mul_of_nonneg_left ih hnn
      _ = infNorm M ^ (k + 1) := by ring

-- ============================================================
-- Matrix-vector product: associativity and triangle inequality
-- ============================================================

/-- Matrix-vector product associativity: ((AB)v)_i = (A(Bv))_i. -/
theorem matMulVec_matMul (n : ℕ) (A B : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    ∀ i, matMulVec n (matMul n A B) v i = matMulVec n A (matMulVec n B v) i := by
  intro i; unfold matMulVec matMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext k; congr 1; ext j; ring

/-- The identity matrix acts as the identity on vectors. -/
theorem matMulVec_id (n : ℕ) (v : Fin n → ℝ) :
    matMulVec n (idMatrix n) v = v := by
  ext i
  simpa [matMulVec] using congrFun (idMatrix_mulVec n v) i

/-- Matrix-vector multiplication is additive in the matrix argument. -/
theorem matMulVec_add_left (n : ℕ)
    (A B : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    matMulVec n (fun i j => A i j + B i j) v =
      fun i => matMulVec n A v i + matMulVec n B v i := by
  ext i
  unfold matMulVec
  simp [add_mul, Finset.sum_add_distrib]

/-- Matrix-vector multiplication is additive in the vector argument. -/
theorem matMulVec_add_right (n : ℕ)
    (A : Fin n → Fin n → ℝ) (v w : Fin n → ℝ) :
    matMulVec n A (fun i => v i + w i) =
      fun i => matMulVec n A v i + matMulVec n A w i := by
  ext i
  unfold matMulVec
  simp [mul_add, Finset.sum_add_distrib]

/-- Triangle inequality for matrix-vector product:
    |Ax|_i ≤ ∑_j |A_{ij}| · |x_j|. -/
theorem abs_matMulVec_le (n : ℕ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    ∀ i : Fin n, |matMulVec n A x i| ≤ ∑ j : Fin n, |A i j| * |x j| := by
  intro i
  unfold matMulVec
  calc |∑ j : Fin n, A i j * x j|
      ≤ ∑ j : Fin n, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |A i j| * |x j| := by
        congr 1; ext j; exact abs_mul (A i j) (x j)

/-- **‖Av‖∞ ≤ ‖A‖∞ · ‖v‖∞**: submultiplicativity for matrix-vector product. -/
theorem infNormVec_matMulVec_le {n : ℕ} (_hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    infNormVec (matMulVec n A v) ≤ infNorm A * infNormVec v := by
  unfold infNormVec infNorm matMulVec
  simpa [Matrix.mulVec] using
    (Matrix.linfty_opNorm_mulVec (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) v)

/-- Infinity norm of |A| equals infinity norm of A. -/
theorem infNorm_absMatrix {n : ℕ} (_hn : 0 < n) (A : Fin n → Fin n → ℝ) :
    infNorm (absMatrix n A) = infNorm A := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      calc ∑ j : Fin n, |absMatrix n A i j|
          = ∑ j : Fin n, |A i j| := by
            unfold absMatrix
            congr 1; ext j; exact abs_abs (A i j)
        _ ≤ infNorm A := row_sum_le_infNorm A i
    · exact infNorm_nonneg A
  · apply infNorm_le_of_row_sum_le
    · intro i
      calc ∑ j : Fin n, |A i j|
          = ∑ j : Fin n, |absMatrix n A i j| := by
            unfold absMatrix
            congr 1; ext j; exact (abs_abs (A i j)).symm
        _ ≤ infNorm (absMatrix n A) := row_sum_le_infNorm (absMatrix n A) i
    · exact infNorm_nonneg (absMatrix n A)

/-- Infinity norm of |v| equals infinity norm of v. -/
theorem infNormVec_absVec {n : ℕ} (_hn : 0 < n) (v : Fin n → ℝ) :
    infNormVec (absVec n v) = infNormVec v := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      unfold absVec
      rw [abs_abs]
      exact abs_le_infNormVec v i
    · exact infNormVec_nonneg v
  · apply infNormVec_le_of_abs_le
    · intro i
      have h := abs_le_infNormVec (absVec n v) i
      unfold absVec at h
      rwa [abs_abs] at h
    · exact infNormVec_nonneg (absVec n v)

-- ============================================================
-- Neumann partial sum: nonneg entries when M ≥ 0
-- ============================================================

/-- **S_N has nonneg entries** when M ≥ 0. -/
theorem neumannSum_nonneg (n : ℕ) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (N : ℕ) :
    ∀ i j, 0 ≤ neumannSum n M N i j := by
  induction N with
  | zero => intro i j; unfold neumannSum idMatrix; split <;> linarith
  | succ N ih =>
    intro i j; unfold neumannSum
    exact add_nonneg (ih i j) (matPow_nonneg n M hM (N + 1) i j)

-- ============================================================
-- Monotonicity: S_N ≤ S_{N+1} entrywise when M ≥ 0
-- ============================================================

/-- **S_N ≤ S_{N+1} entrywise** when M ≥ 0. -/
theorem neumannSum_mono (n : ℕ) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (N : ℕ) :
    ∀ i j, neumannSum n M N i j ≤ neumannSum n M (N + 1) i j := by
  intro i j; simp [neumannSum_succ]; linarith [matPow_nonneg n M hM (N + 1) i j]

-- ============================================================
-- Row sum bound for Neumann partial sums
-- ============================================================

/-- **Row sum bound for S_N**: if ‖M‖∞ ≤ c < 1 and M ≥ 0,
    then ∑_j (S_N)_{ij} ≤ (1 − c^{N+1}) / (1 − c). -/
theorem neumannSum_rowSum_bound (n : ℕ) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (c : ℝ) (hc_nn : 0 ≤ c) (hc_lt : c < 1)
    (hbound : infNormBound n M c) (N : ℕ) :
    ∀ i, ∑ j : Fin n, neumannSum n M N i j ≤ (1 - c ^ (N + 1)) / (1 - c) := by
  induction N with
  | zero =>
    intro i
    simp [neumannSum, idMatrix, Finset.sum_ite_eq, Finset.mem_univ]
    have hne : (1 : ℝ) - c ≠ 0 := by linarith
    rw [div_self hne]
  | succ N ih =>
    intro i
    simp only [neumannSum_succ]
    simp_rw [Finset.sum_add_distrib]
    -- ∑(S_N)_{ij} + ∑(M^{N+1})_{ij} ≤ (1 - c^{N+1})/(1-c) + c^{N+1}
    have h1 := ih i
    have h2 : ∑ j : Fin n, matPow n M (N + 1) i j ≤ c ^ (N + 1) := by
      calc ∑ j, matPow n M (N + 1) i j
          = ∑ j, |matPow n M (N + 1) i j| := by
            congr 1; ext j; rw [abs_of_nonneg (matPow_nonneg n M hM (N + 1) i j)]
        _ ≤ c ^ (N + 1) :=
          row_sum_le_of_infNormBound (matPow_infNorm_bound n M hM c hc_nn hbound (N + 1)) i
    have hc1 : (0 : ℝ) < 1 - c := by linarith
    calc ∑ j, neumannSum n M N i j + ∑ j, matPow n M (N + 1) i j
        ≤ (1 - c ^ (N + 1)) / (1 - c) + c ^ (N + 1) := add_le_add h1 h2
      _ = (1 - c ^ (N + 2)) / (1 - c) := by field_simp; ring

-- ============================================================
-- Row sum bound: 1/(1−c) universal bound
-- ============================================================

/-- **Universal row sum bound**: S_N row sums ≤ 1/(1−c) for all N. -/
theorem neumannSum_rowSum_le_inv (n : ℕ) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (c : ℝ) (hc_nn : 0 ≤ c) (hc_lt : c < 1)
    (hbound : infNormBound n M c) (N : ℕ) :
    ∀ i, ∑ j : Fin n, neumannSum n M N i j ≤ 1 / (1 - c) := by
  intro i
  have h := neumannSum_rowSum_bound n M hM c hc_nn hc_lt hbound N i
  have hc1 : (0 : ℝ) < 1 - c := by linarith
  calc ∑ j, neumannSum n M N i j
      ≤ (1 - c ^ (N + 1)) / (1 - c) := h
    _ ≤ 1 / (1 - c) := by
        apply div_le_div_of_nonneg_right _ (by linarith : 0 < 1 - c).le
        linarith [pow_nonneg hc_nn (N + 1)]

-- ============================================================
-- Constructive Neumann inverse: (I − M)⁻¹ exists when M ≥ 0, ‖M‖∞ < 1
-- ============================================================

/-- **Neumann series left inverse**: (I − M) · S_N = I − M^{N+1},
    so as N → ∞, S_N → (I − M)⁻¹.

    For finite-dimensional matrices, we can take N large enough that M^{N+1}
    is "negligible", but in practice we work with the telescoping identity
    directly. The key result is that S_N is a left approximate inverse with
    error M^{N+1}, which can be bounded by c^{N+1}. -/
theorem neumann_left_approx_inv (n : ℕ) (M : Fin n → Fin n → ℝ) (N : ℕ) :
    ∀ i j, ∑ k : Fin n, (matSub_id n M i k) * (neumannSum n M N k j) =
      idMatrix n i j - matPow n M (N + 1) i j := by
  intro i j
  have := congr_fun (congr_fun (neumann_telescope n M N) i) j
  unfold matMul at this; exact this

/-- **Neumann series right inverse**: S_N · (I − M) = I − M^{N+1}. -/
theorem neumann_right_approx_inv (n : ℕ) (M : Fin n → Fin n → ℝ) (N : ℕ) :
    ∀ i j, ∑ k : Fin n, (neumannSum n M N i k) * (matSub_id n M k j) =
      idMatrix n i j - matPow n M (N + 1) i j := by
  intro i j
  have := congr_fun (congr_fun (neumann_telescope_right n M N) i) j
  unfold matMul at this; exact this

-- ============================================================
-- Resolution property: (I − M)w = v implies |w| ≤ S_N|v| + M^{N+1}|w|
-- ============================================================

/-- **Resolution with remainder**: if (I − M)w = v and M ≥ 0 with ‖M‖∞ ≤ c,
    then S_N · v = w − M^{N+1} · w, so |w_i| ≤ (S_N|v|)_i + (M^{N+1}|w|)_i. -/
theorem neumann_resolution_approx (n : ℕ) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j)
    (v w : Fin n → ℝ) (N : ℕ)
    (hsolve : ∀ i, w i - ∑ j : Fin n, M i j * w j = v i) :
    ∀ i, |w i| ≤ ∑ j : Fin n, neumannSum n M N i j * |v j| +
      ∑ j : Fin n, matPow n M (N + 1) i j * |w j| := by
  intro i
  -- From S_N · (I−M) = I − M^{N+1}, we get S_N · v = w − M^{N+1} · w
  -- So w = S_N · v + M^{N+1} · w
  -- We need: ∑_k S_N(i,k) * v(k) = w(i) - ∑_k M^{N+1}(i,k) * w(k)
  have hSNv : ∑ k : Fin n, neumannSum n M N i k * v k =
      w i - ∑ k : Fin n, matPow n M (N + 1) i k * w k := by
    -- Strategy: v(k) = ∑_j (I-M)(k,j) * w(j), so S_N·v = S_N·(I-M)·w = (I-M^{N+1})·w
    -- Step 1: rewrite v in terms of (I-M)w
    have hv : ∀ k, v k = ∑ j : Fin n, matSub_id n M k j * w j := by
      intro k; unfold matSub_id idMatrix
      simp_rw [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ite_true]
      linarith [hsolve k]
    -- Step 2: ∑_k S_N(i,k) * v(k) = ∑_k S_N(i,k) * ∑_j (I-M)(k,j) * w(j)
    conv_lhs => arg 2; ext k; rw [hv k]
    -- Step 3: swap sums to get ∑_j (∑_k S_N(i,k)*(I-M)(k,j)) * w(j)
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    -- Step 4: use telescope: ∑_k S_N(i,k)*(I-M)(k,j) = I(i,j) - M^{N+1}(i,j)
    have htel := neumann_right_approx_inv n M N
    simp_rw [show ∀ k j : Fin n, neumannSum n M N i k * (matSub_id n M k j * w j) =
      (neumannSum n M N i k * matSub_id n M k j) * w j from fun k j => by ring]
    simp_rw [← Finset.sum_mul]
    simp_rw [htel i]
    -- Now: ∑_j (I(i,j) - M^{N+1}(i,j)) * w(j) = w(i) - ∑_j M^{N+1}(i,j) * w(j)
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    congr 1
    unfold idMatrix; simp [Finset.sum_ite_eq, Finset.mem_univ]
  -- So w(i) = (S_N · v)(i) + (M^{N+1} · w)(i)
  have hw_eq : w i = ∑ k, neumannSum n M N i k * v k +
      ∑ k, matPow n M (N + 1) i k * w k := by linarith [hSNv]
  rw [hw_eq]
  calc |∑ k, neumannSum n M N i k * v k + ∑ k, matPow n M (N + 1) i k * w k|
      ≤ |∑ k, neumannSum n M N i k * v k| + |∑ k, matPow n M (N + 1) i k * w k| :=
        abs_add_le _ _
    _ ≤ ∑ k, |neumannSum n M N i k * v k| + ∑ k, |matPow n M (N + 1) i k * w k| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ k, |neumannSum n M N i k| * |v k| + ∑ k, |matPow n M (N + 1) i k| * |w k| := by
        congr 1 <;> (congr 1; ext k; exact abs_mul _ _)
    _ = ∑ k, neumannSum n M N i k * |v k| + ∑ k, matPow n M (N + 1) i k * |w k| := by
        congr 1
        · congr 1; ext k; rw [abs_of_nonneg (neumannSum_nonneg n M hM N i k)]
        · congr 1; ext k; rw [abs_of_nonneg (matPow_nonneg n M hM (N + 1) i k)]

-- ============================================================
-- Key theorem: inf-norm resolution for (I − M)w = v
-- ============================================================

/-- **Exact Neumann resolution** (finite-dimensional, inf-norm form).

    If M ≥ 0 with ‖M‖∞ ≤ c < 1, and (I − M)w = v, then:
      |w_i| ≤ (1/(1 − c)) · ∑_j |v_j|

    Proof by the standard max-norm argument:
    1. Let W = max_i |w_i|.
    2. From (I−M)w = v: |w_i| ≤ |v_i| + c·W for all i.
    3. Taking max: W ≤ max|v| + c·W, so W ≤ max|v|/(1−c).
    4. Since max|v| ≤ ∑|v|: W ≤ ∑|v|/(1−c).

    This is the normwise bound used in iterative refinement (Higham §11). -/
theorem neumann_exact_scalar_resolution (n : ℕ) (hn : 0 < n)
    (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (c : ℝ) (_hc_nn : 0 ≤ c) (hc_lt : c < 1)
    (hbound : infNormBound n M c)
    (v w : Fin n → ℝ)
    (hsolve : ∀ i, w i - ∑ j : Fin n, M i j * w j = v i) :
    ∀ i, |w i| ≤ (1 / (1 - c)) * ∑ j : Fin n, |v j| := by
  have hc1 : (0 : ℝ) < 1 - c := by linarith
  -- Step 1: from (I-M)w = v, get |w_i| ≤ |v_i| + ∑_j M_{ij} |w_j|
  have habs : ∀ i : Fin n, |w i| ≤ |v i| + ∑ j : Fin n, M i j * |w j| := by
    intro i
    have hwi : w i = v i + ∑ j, M i j * w j := by linarith [(hsolve i).symm]
    rw [hwi]
    calc |v i + ∑ j, M i j * w j|
        ≤ |v i| + |∑ j, M i j * w j| := abs_add_le _ _
      _ ≤ |v i| + ∑ j, |M i j * w j| := by
          linarith [Finset.abs_sum_le_sum_abs (fun j => M i j * w j) Finset.univ]
      _ = |v i| + ∑ j, |M i j| * |w j| := by
          congr 1; congr 1; ext j; exact abs_mul _ _
      _ = |v i| + ∑ j, M i j * |w j| := by
          congr 1; congr 1; ext j; rw [abs_of_nonneg (hM i j)]
  -- Step 2: define W = sup' |w| and V = ∑|v|
  let hne : Finset.univ.Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  let W := Finset.sup' Finset.univ hne (fun i => |w i|)
  let V := ∑ j : Fin n, |v j|
  -- Step 3: |w_i| ≤ W for all i
  have hW_ge : ∀ i : Fin n, |w i| ≤ W :=
    fun i => Finset.le_sup' (fun i => |w i|) (Finset.mem_univ i)
  -- W ≥ 0
  have hW_nn : (0 : ℝ) ≤ W := le_trans (abs_nonneg _) (hW_ge ⟨0, hn⟩)
  -- Step 4: |w_i| ≤ |v_i| + c * W
  have hW_bound : ∀ i : Fin n, |w i| ≤ |v i| + c * W := by
    intro i
    have h1 := habs i
    have h2 : ∑ j, M i j * |w j| ≤ c * W := by
      have hMW : ∑ j : Fin n, M i j * |w j| ≤ ∑ j : Fin n, M i j * W :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hW_ge j) (hM i j))
      have hMW_eq : ∑ j : Fin n, M i j * W = W * ∑ j : Fin n, M i j := by
        simp_rw [mul_comm (M i _) W]; exact (Finset.mul_sum Finset.univ (fun j => M i j) W).symm
      have hrow : ∑ j : Fin n, M i j ≤ c := by
        calc ∑ j, M i j = ∑ j, |M i j| := by
              congr 1; ext j; rw [abs_of_nonneg (hM i j)]
          _ ≤ c := row_sum_le_of_infNormBound hbound i
      calc ∑ j, M i j * |w j| ≤ ∑ j, M i j * W := hMW
        _ = W * ∑ j, M i j := hMW_eq
        _ ≤ W * c := mul_le_mul_of_nonneg_left hrow hW_nn
        _ = c * W := mul_comm W c
    linarith
  -- Step 5: W ≤ V + c * W
  have hV_max_le : ∀ i : Fin n, |v i| ≤ V :=
    fun i => Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
  have hW_le_V : W ≤ V + c * W := by
    apply Finset.sup'_le
    intro i _
    calc |w i| ≤ |v i| + c * W := hW_bound i
      _ ≤ V + c * W := by linarith [hV_max_le i]
  -- Step 6: (1 - c) * W ≤ V, so W ≤ V / (1 - c) = (1/(1-c)) * V
  have hW_final : W ≤ (1 / (1 - c)) * V := by
    have h1c_W : (1 - c) * W ≤ V := by nlinarith
    have hcancel : 1 / (1 - c) * (1 - c) = 1 := by field_simp
    have hinv_nn : (0 : ℝ) ≤ 1 / (1 - c) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1c_W hinv_nn]
  -- Step 7: |w_i| ≤ W ≤ (1/(1-c)) ∑|v|
  intro i
  exact le_trans (hW_ge i) hW_final

end LeanFpAnalysis.FP
