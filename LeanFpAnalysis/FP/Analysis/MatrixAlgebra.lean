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

/-- ‖A‖²_F = ‖A‖_F². -/
lemma frobNorm_sq {m n : ℕ} (A : RMatFn m n) :
    frobNorm A ^ 2 = frobNormSq A := by
  rw [frobNorm_eq_sqrt_frobNormSq]
  rw [sq, Real.mul_self_sqrt (frobNormSq_nonneg A)]

/-- Frobenius norm monotonicity from entrywise absolute-value domination. -/
theorem frobNorm_le_of_entry_abs_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (h : ∀ i j, |A i j| ≤ B i j) :
    frobNorm A ≤ frobNorm B := by
  unfold frobNorm
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

/-- For orthogonal U, rows are orthonormal: ∑_k U_ik U_jk = δ_ij. -/
lemma IsOrthogonal.row_orthonormal {n : ℕ} {U : Fin n → Fin n → ℝ}
    (hU : IsOrthogonal n U) (i j : Fin n) :
    ∑ k : Fin n, U i k * U j k = if i = j then 1 else 0 := by
  have := hU.2 i j; unfold matTranspose at this; exact this

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
