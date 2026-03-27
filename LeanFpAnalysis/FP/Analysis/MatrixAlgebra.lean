-- Analysis/MatrixAlgebra.lean
--
-- Matrix algebra infrastructure: matrix multiplication, matrix power,
-- Neumann series, and constructive (I − M)⁻¹ for nonneg M with ‖M‖∞ < 1.
--
-- This provides the matrix inverse theory needed for iterative refinement
-- (Higham §11) and forward error analysis (§8.2).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace LeanFpAnalysis.FP

open scoped BigOperators

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
-- Infinity norm for matrices
-- ============================================================

/-- **Infinity norm** of a matrix: max row sum of absolute values.
    We define this as a hypothesis-based predicate rather than computing it,
    since the max over Fin n is well-defined but awkward to work with. -/
def infNormBound (n : ℕ) (M : Fin n → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ i : Fin n, ∑ j : Fin n, |M i j| ≤ c

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
    intro i; simp only [matPow, pow_zero]
    unfold idMatrix infNormBound at *
    have : ∀ j : Fin n, |if i = j then (1 : ℝ) else 0| = if i = j then 1 else 0 := by
      intro j; split <;> simp
    simp_rw [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]; linarith
  | succ k ih =>
    intro i; simp only [matPow_succ, pow_succ']
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
          have := ih l
          calc ∑ j : Fin n, matPow n M k l j
              = ∑ j : Fin n, |matPow n M k l j| := by
                congr 1; ext j; rw [abs_of_nonneg (matPow_nonneg n M hM k l j)]
            _ ≤ c ^ k := ih l
      _ = c ^ k * ∑ l : Fin n, M i l := by rw [Finset.mul_sum]; congr 1; ext l; ring
      _ ≤ c ^ k * c := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc k)
          calc ∑ l : Fin n, M i l = ∑ l : Fin n, |M i l| := by
                congr 1; ext l; rw [abs_of_nonneg (hM i l)]
            _ ≤ c := hbound i
      _ = c * c ^ k := by ring

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
        _ ≤ c ^ (N + 1) := matPow_infNorm_bound n M hM c hc_nn hbound (N + 1) i
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
          _ ≤ c := hbound i
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
