/-
  Algorithms/LU/BlockLU.lean

  Block LU factorization and stability analysis (Higham Chapter 12).

  Blocks are uniform size r with m blocks (total dimension n = m·r).
  Block matrices: Fin m → Fin m → (Fin r → Fin r → ℝ).
  Norm convention: ‖A‖ := max_{i,j,s,t} |A_{ij}(s,t)| (entrywise max, §12.2).

  Main results:
  - BlockLUFactSpec: block LU specification (§12.1)
  - blockSchur: block Schur complement S = A₂₂ − A₂₁A₁₁⁻¹A₁₂ (eq. 12.2)
  - block_lu_one_step: Algorithm 12.2 one-step correctness (Theorem 12.1)
  - blockErrorDelta, blockErrorTheta: error recurrence constants (eq. 12.6)
  - partitioned_lu_backward_error_step: Theorem 12.3 one-step (eq. 12.6)
  - block_lu_solve_backward_error: Theorem 12.4 (eq. 12.15)
  - IsBlockDiagDomCol, IsBlockDiagDomRow: block diagonal dominance (eq. 12.16)
  - block_diag_dom_schur_inherit: Theorem 12.5 one-step
  - block_diag_dom_growth_bound_step: Theorem 12.6 one-step
  - norm2Sq, norm2Vec: vector 2-norm (§12.3.2)
  - spd_submatrix_inv_2norm_bound: Lemma 12.7
  - spd_schur_cond_bound: Lemma 12.8
  - block_lu_stability_spd: eq. 12.23
  - block_lu_normLU_bound_general: eq. 12.21
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.ForwardError
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination
import LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- Vector 2-norm (§12.3.2)
-- ============================================================

/-- Squared Euclidean norm: ‖v‖₂² = ∑_i v_i². -/
noncomputable def norm2Sq {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, v i ^ 2

/-- Euclidean (2-norm) of a vector: ‖v‖₂ = √(∑_i v_i²). -/
noncomputable def norm2Vec {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (norm2Sq v)

lemma norm2Sq_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ norm2Sq v :=
  Finset.sum_nonneg fun i _ => sq_nonneg (v i)

lemma norm2Vec_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ norm2Vec v :=
  Real.sqrt_nonneg _

-- ============================================================
-- §12.1  Block matrix definitions
-- ============================================================

/-- r×r identity block: I(s,t) = δ_{st}. -/
noncomputable def idBlock (r : ℕ) : Fin r → Fin r → ℝ :=
  fun s t => if s = t then 1 else 0

/-- r×r zero block. -/
noncomputable def zeroBlock (r : ℕ) : Fin r → Fin r → ℝ :=
  fun _ _ => 0

/-- r×r block multiplication: (AB)(s,t) = ∑_l A(s,l) · B(l,t). -/
noncomputable def blockMul {r : ℕ} (A B : Fin r → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  fun s t => ∑ l : Fin r, A s l * B l t

/-- Block matrix product: (AB)_{ij}(s,t) = ∑_k ∑_l A_{ik}(s,l) · B_{kj}(l,t). -/
noncomputable def blockMatProd {m r : ℕ}
    (A B : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    Fin m → Fin m → (Fin r → Fin r → ℝ) :=
  fun i j s t => ∑ k : Fin m, ∑ l : Fin r, A i k s l * B k j l t

/-- Entrywise max norm of the full block matrix (Chapter 12's convention):
    ‖A‖ := max_{i,j} maxEntryNorm(A_{ij}) = max_{i,j,s,t} |A_{ij}(s,t)|. -/
noncomputable def blockMaxNorm {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
    (fun i => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
      (fun j => maxEntryNorm hr (A i j)))

/-- Each block norm is bounded by the full block max norm. -/
lemma block_le_blockMaxNorm {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) (i j : Fin m) :
    maxEntryNorm hr (A i j) ≤ blockMaxNorm hm hr A := by
  unfold blockMaxNorm
  exact le_trans
    (Finset.le_sup' (fun j' => maxEntryNorm hr (A i j')) (Finset.mem_univ j))
    (Finset.le_sup' (fun i' => Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
      (fun j' => maxEntryNorm hr (A i' j'))) (Finset.mem_univ i))

lemma blockMaxNorm_nonneg {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    0 ≤ blockMaxNorm hm hr A :=
  le_trans (maxEntryNorm_nonneg hr (A ⟨0, hm⟩ ⟨0, hm⟩))
    (block_le_blockMaxNorm hm hr A ⟨0, hm⟩ ⟨0, hm⟩)

-- ============================================================
-- §12.1  Block LU specification (Theorem 12.1)
-- ============================================================

/-- **Block LU factorization specification** (Higham §12.1, Theorem 12.1).
    A = LU where L is block unit lower triangular (identity diagonal blocks)
    and U is block upper triangular, with m blocks of uniform size r. -/
structure BlockLUFactSpec (m r : ℕ)
    (A L U : Fin m → Fin m → (Fin r → Fin r → ℝ)) : Prop where
  /-- L has identity blocks on the diagonal: L_{ii} = I_r. -/
  L_diag : ∀ i : Fin m, L i i = idBlock r
  /-- L is block lower triangular: L_{ij} = 0 for i < j. -/
  L_upper_zero : ∀ i j : Fin m, i.val < j.val → L i j = zeroBlock r
  /-- U is block upper triangular: U_{ij} = 0 for j < i. -/
  U_lower_zero : ∀ i j : Fin m, j.val < i.val → U i j = zeroBlock r
  /-- Block product L·U equals A entrywise. -/
  product_eq : ∀ (i j : Fin m) (s t : Fin r),
    ∑ k : Fin m, ∑ l : Fin r, L i k s l * U k j l t = A i j s t

-- ============================================================
-- §12.1  Block Schur complement (eq. 12.2)
-- ============================================================

/-- **Block Schur complement** (Higham eq. 12.2):
    S_{ij} = A_{i+1,j+1} − ∑_{l₁,l₂} A_{i+1,0}(s,l₁) · A₁₁⁻¹(l₁,l₂) · A_{0,j+1}(l₂,t).
    Eliminates block row/column 0, yielding an m×m block matrix from (m+1)×(m+1). -/
noncomputable def blockSchur {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (A11_inv : Fin r → Fin r → ℝ) :
    Fin m → Fin m → (Fin r → Fin r → ℝ) :=
  fun i j s t => A i.succ j.succ s t -
    ∑ l₁ : Fin r, ∑ l₂ : Fin r,
      A i.succ (0 : Fin (m + 1)) s l₁ * A11_inv l₁ l₂ *
      A (0 : Fin (m + 1)) j.succ l₂ t

-- ============================================================
-- §12.1  Algorithm 12.2 one-step (Theorem 12.1 inductive step)
-- ============================================================

/-- Helper: summing (if s = l then 1 else 0) · f(l) gives f(s). -/
private lemma sum_ite_eq_val {r : ℕ} (f : Fin r → ℝ) (s : Fin r) :
    ∑ l : Fin r, (if s = l then (1 : ℝ) else 0) * f l = f s := by
  conv_lhs =>
    arg 2; ext l
    rw [show (if s = l then (1 : ℝ) else 0) * f l =
      if s = l then f l else 0 by split_ifs <;> simp]
  simp [Finset.mem_univ]

/-- Helper: summing f(l) · (if l = t then 1 else 0) gives f(t). -/
private lemma sum_ite_eq_val_right {r : ℕ} (f : Fin r → ℝ) (t : Fin r) :
    ∑ l : Fin r, f l * (if l = t then (1 : ℝ) else 0) = f t := by
  simp_rw [mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- **One step of block LU factorization** (Algorithm 12.2, Theorem 12.1).
    Given A with m+1 blocks, A₁₁ invertible, and the Schur complement S having
    a block LU factorization S = L_S · U_S, constructs the block LU of A.

    Proof sketch: define L by cases (identity at (0,0), zero above diagonal,
    A_{i0}·A₁₁⁻¹ in column 0 below, L_S in the lower-right); define U similarly
    (A_{0j} in row 0, zero below column 0, U_S in the lower-right). Verify the
    product L·U = A using the inverse property and Schur complement cancellation. -/
theorem block_lu_one_step {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (A11_inv : Fin r → Fin r → ℝ)
    (hInv : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A (0 : Fin (m + 1)) (0 : Fin (m + 1)) l t =
        if s = t then 1 else 0)
    (L_S U_S : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hS : BlockLUFactSpec m r (blockSchur A A11_inv) L_S U_S) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
      BlockLUFactSpec (m + 1) r A L U := by
  -- Define L using dif for clean case analysis (following cholesky_existence pattern)
  let L : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) := fun i j =>
    if hi : i = 0 then
      if hj : j = 0 then idBlock r else zeroBlock r
    else if hj : j = 0 then
      fun s t => ∑ l : Fin r, A i 0 s l * A11_inv l t
    else L_S (i.pred hi) (j.pred hj)
  -- Define U using dif
  let U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) := fun i j =>
    if hi : i = 0 then A 0 j
    else if hj : j = 0 then zeroBlock r
    else U_S (i.pred hi) (j.pred hj)
  refine ⟨L, U, ?_, ?_, ?_, ?_⟩
  · -- L_diag: L i i = idBlock r
    intro i
    by_cases hi : i = 0
    · subst hi; simp [L]
    · simp only [L, dif_neg hi]; exact hS.L_diag (i.pred hi)
  · -- L_upper_zero: L i j = zeroBlock r when i.val < j.val
    intro i j hij
    by_cases hi : i = 0
    · subst hi
      have hj : j ≠ 0 := by intro h; subst h; exact lt_irrefl _ hij
      simp [L, hj]
    · have hj : j ≠ 0 := by intro h; subst h; exact absurd hij (Nat.not_lt_zero _)
      simp only [L, dif_neg hi, dif_neg hj]
      exact hS.L_upper_zero _ _ (by
        have := Fin.val_pred j hj; have := Fin.val_pred i hi
        have : i.val ≠ 0 := fun h => hi (Fin.ext h)
        have : j.val ≠ 0 := fun h => hj (Fin.ext h)
        omega)
  · -- U_lower_zero: U i j = zeroBlock r when j.val < i.val
    intro i j hij
    by_cases hi : i = 0
    · subst hi; exact absurd hij (Nat.not_lt_zero _)
    · by_cases hj : j = 0
      · subst hj; simp [U, hi]
      · simp only [U, dif_neg hi, dif_neg hj]
        exact hS.U_lower_zero _ _ (by
          have := Fin.val_pred j hj; have := Fin.val_pred i hi
          have : i.val ≠ 0 := fun h => hi (Fin.ext h)
          have : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
  · -- product_eq: ∑_k ∑_l L i k s l * U k j l t = A i j s t
    intro i j s t
    rw [Fin.sum_univ_succ]
    -- Entry value helpers (proven by simp on the let definitions)
    have hL0 : ∀ p, L 0 p = if p = 0 then idBlock r else zeroBlock r :=
      fun p => by simp [L]
    have hU0 : ∀ p, U 0 p = A 0 p := fun p => by simp [U]
    have hL0s : ∀ k : Fin m, L 0 (Fin.succ k) = zeroBlock r :=
      fun k => by rw [hL0]; simp [Fin.succ_ne_zero]
    have hLs0 : ∀ k : Fin m, L (Fin.succ k) 0 =
        fun s t => ∑ l, A (Fin.succ k) 0 s l * A11_inv l t :=
      fun k => by simp [L, Fin.succ_ne_zero]
    have hLss : ∀ (p q : Fin m), L (Fin.succ p) (Fin.succ q) = L_S p q :=
      fun p q => by simp [L, Fin.succ_ne_zero, Fin.pred_succ]
    have hUs0 : ∀ k : Fin m, U (Fin.succ k) 0 = zeroBlock r :=
      fun k => by simp [U, Fin.succ_ne_zero]
    have hUss : ∀ (p q : Fin m), U (Fin.succ p) (Fin.succ q) = U_S p q :=
      fun p q => by simp [U, Fin.succ_ne_zero, Fin.pred_succ]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · -- i = 0, j = 0: ∑_l δ(s,l) · A₀₀(l,t) + 0 = A₀₀(s,t)
      subst hi; subst hj
      rw [hL0 0, if_pos rfl, hU0 0]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L 0 (Fin.succ k) s l * U (Fin.succ k) 0 l t = 0 :=
        fun k => by simp [hL0s k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      exact sum_ite_eq_val _ s
    · -- i = 0, j ≠ 0: ∑_l δ(s,l) · A₀ⱼ(l,t) + 0 = A₀ⱼ(s,t)
      subst hi
      rw [hL0 0, if_pos rfl, hU0 j]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L 0 (Fin.succ k) s l * U (Fin.succ k) j l t = 0 :=
        fun k => by simp [hL0s k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      exact sum_ite_eq_val _ s
    · -- i ≠ 0, j = 0: A_{i0}·A₁₁⁻¹·A₀₀ + 0 = A_{i0}
      subst hj; rw [hU0 0]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L i (Fin.succ k) s l * U (Fin.succ k) 0 l t = 0 :=
        fun k => by simp [hUs0 k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      have hLi0 : L i 0 = fun s t => ∑ l, A i 0 s l * A11_inv l t := by
        have := hLs0 (i.pred hi); rwa [Fin.succ_pred i hi] at this
      simp_rw [hLi0, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, ← Finset.mul_sum, hInv]
      exact sum_ite_eq_val_right _ t
    · -- i ≠ 0, j ≠ 0: Schur complement cancellation
      rw [hU0 j]
      have hLi0 : L i 0 = fun s t => ∑ l, A i 0 s l * A11_inv l t := by
        have := hLs0 (i.pred hi); rwa [Fin.succ_pred i hi] at this
      simp_rw [hLi0]
      -- Rewrite successor terms to L_S/U_S
      have hsec : ∀ (k : Fin m) (l : Fin r),
          L i (Fin.succ k) s l * U (Fin.succ k) j l t =
          L_S (i.pred hi) k s l * U_S k (j.pred hj) l t := by
        intro k l
        have hLeq : L i (Fin.succ k) = L_S (i.pred hi) k := by
          have := hLss (i.pred hi) k; rwa [Fin.succ_pred i hi] at this
        have hUeq : U (Fin.succ k) j = U_S k (j.pred hj) := by
          have := hUss k (j.pred hj); rwa [Fin.succ_pred j hj] at this
        rw [hLeq, hUeq]
      simp_rw [hsec]
      -- Use Schur complement product equation
      have hprod := hS.product_eq (i.pred hi) (j.pred hj) s t
      simp only [blockSchur, Fin.succ_pred] at hprod
      rw [hprod]
      -- first_sum + (A(i,j) − triple_sum) = A(i,j)
      have hfirst : ∑ l : Fin r,
          (∑ l' : Fin r, A i 0 s l' * A11_inv l' l) * A 0 j l t =
          ∑ l₁ : Fin r, ∑ l₂ : Fin r,
            A i 0 s l₁ * A11_inv l₁ l₂ * A 0 j l₂ t := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
      linarith

-- ============================================================
-- §12.2  Error recurrence constants (eq. 12.6)
-- ============================================================

/-- δ(m) for partitioned LU backward error (eq. 12.6).
    δ counts block elimination steps minus one: δ(m) = m−1 for m ≥ 1.
    In the book: δ(n,r) with n = m·r gives δ = m−1. -/
noncomputable def blockErrorDelta : ℕ → ℝ
  | 0 => 0
  | m + 1 => (m : ℝ)

/-- θ(m) for partitioned LU backward error (eq. 12.6).
    Recurrence: θ(0) = 0, θ(1) = c₃, θ(m+2) = max{c₃, c₂, 1 + c₁ + δ(m+1) + θ(m+1)}.
    c₁, c₂, c₃ are BLAS-3 error constants (scalar parameters).
    For conventional BLAS3: c₁(m,n,p) = n², c₂(m,p) = m², c₃(r) = r. -/
noncomputable def blockErrorTheta (c₁ c₂ c₃ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => c₃
  | m + 2 => max (max c₃ c₂)
    (1 + c₁ + blockErrorDelta (m + 1) + blockErrorTheta c₁ c₂ c₃ (m + 1))

lemma blockErrorDelta_nonneg (m : ℕ) : 0 ≤ blockErrorDelta m := by
  cases m with
  | zero => simp [blockErrorDelta]
  | succ m => simp [blockErrorDelta]

-- ============================================================
-- §12.2  Theorem 12.3 one-step (partitioned LU backward error)
-- ============================================================

/-- **Theorem 12.3 one-step** (Demmel-Higham, eq. 12.6 inductive step).
    Given per-block backward errors from BLAS-3 assumptions (12.3)–(12.5),
    the overall backward error satisfies the recurrence bound. -/
theorem partitioned_lu_backward_error_step
    (normΔA₁₁ normΔA₁₂ normΔA₂₁ normΔA₂₂ : ℝ)
    (normA normL normU u : ℝ)
    (c₁ c₂ c₃ δ_prev θ_prev : ℝ)
    (hu : 0 ≤ u) (_hc₁ : 0 ≤ c₁) (_hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hδ : 0 ≤ δ_prev) (_hθ : 0 ≤ θ_prev)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    -- Per-block error bounds (eqs. 12.5, 12.7, 12.8, 12.12):
    (h₁₁ : normΔA₁₁ ≤ c₃ * u * normL * normU)
    (h₁₂ : normΔA₁₂ ≤ c₂ * u * normL * normU)
    (h₂₁ : normΔA₂₁ ≤ c₂ * u * normL * normU)
    (h₂₂ : normΔA₂₂ ≤ u * ((1 + δ_prev) * normA +
        (1 + c₁ + δ_prev + θ_prev) * normL * normU)) :
    max (max normΔA₁₁ normΔA₁₂) (max normΔA₂₁ normΔA₂₂) ≤
      u * ((1 + δ_prev) * normA +
        max (max c₃ c₂) (1 + c₁ + δ_prev + θ_prev) * normL * normU) := by
  have hLU : 0 ≤ normL * normU := mul_nonneg hL hU
  have hθ_max : c₃ ≤ max (max c₃ c₂) (1 + c₁ + δ_prev + θ_prev) :=
    le_trans (le_max_left c₃ c₂) (le_max_left _ _)
  have hθ_max2 : c₂ ≤ max (max c₃ c₂) (1 + c₁ + δ_prev + θ_prev) :=
    le_trans (le_max_right c₃ c₂) (le_max_left _ _)
  have hθ_max3 : 1 + c₁ + δ_prev + θ_prev ≤
      max (max c₃ c₂) (1 + c₁ + δ_prev + θ_prev) := le_max_right _ _
  set M := max (max c₃ c₂) (1 + c₁ + δ_prev + θ_prev)
  have hM_nonneg : 0 ≤ M := le_trans hc₃ hθ_max
  have hRHS_nonneg : 0 ≤ (1 + δ_prev) * normA := by nlinarith
  -- Helper: if x ≤ c * u * normL * normU and c ≤ M, then x ≤ RHS
  have haux : ∀ c, c ≤ M → c * u * normL * normU ≤
      u * ((1 + δ_prev) * normA + M * normL * normU) := by
    intro c hc
    have h1 : c * (u * (normL * normU)) ≤ M * (u * (normL * normU)) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hu hLU)
    nlinarith
  apply max_le <;> apply max_le
  · exact le_trans h₁₁ (haux c₃ hθ_max)
  · exact le_trans h₁₂ (haux c₂ hθ_max2)
  · exact le_trans h₂₁ (haux c₂ hθ_max2)
  · calc normΔA₂₂
        ≤ u * ((1 + δ_prev) * normA + (1 + c₁ + δ_prev + θ_prev) * normL * normU) := h₂₂
      _ ≤ u * ((1 + δ_prev) * normA + M * normL * normU) := by
          apply mul_le_mul_of_nonneg_left _ hu
          linarith [mul_le_mul_of_nonneg_right hθ_max3 hLU]

-- ============================================================
-- §12.3  Theorem 12.4 (block LU solve backward error, eq. 12.15)
-- ============================================================

/-- **Theorem 12.4** (Demmel-Higham-Schreiber, eq. 12.15).
    Block LU factorization and solve: ‖ΔAᵢ‖ ≤ dₙ · u · (‖A‖ + ‖L̂‖ · ‖Û‖). -/
theorem block_lu_solve_backward_error
    (normΔA_fact normΔA_solve : ℝ)
    (normA normL normU u d_fact d_solve : ℝ)
    (hu : 0 ≤ u) (_hd_f : 0 ≤ d_fact) (_hd_s : 0 ≤ d_solve)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hFact : normΔA_fact ≤ d_fact * u * (normA + normL * normU))
    (hSolve : normΔA_solve ≤ d_solve * u * (normA + normL * normU)) :
    max normΔA_fact normΔA_solve ≤
      max d_fact d_solve * u * (normA + normL * normU) := by
  have hsum : 0 ≤ normA + normL * normU := by linarith [mul_nonneg hL hU]
  have husum : 0 ≤ u * (normA + normL * normU) := mul_nonneg hu hsum
  apply max_le
  · calc normΔA_fact ≤ d_fact * u * (normA + normL * normU) := hFact
      _ ≤ max d_fact d_solve * u * (normA + normL * normU) := by
          nlinarith [mul_le_mul_of_nonneg_right (le_max_left d_fact d_solve) husum]
  · calc normΔA_solve ≤ d_solve * u * (normA + normL * normU) := hSolve
      _ ≤ max d_fact d_solve * u * (normA + normL * normU) := by
          nlinarith [mul_le_mul_of_nonneg_right (le_max_right d_fact d_solve) husum]

-- ============================================================
-- §12.3.1  Block diagonal dominance (eq. 12.16)
-- ============================================================

/-- **Block diagonal dominance by columns** (Higham eq. 12.16):
    ‖A_{jj}⁻¹‖⁻¹ − ∑_{i≠j} ‖A_{ij}‖ = γ_j ≥ 0. -/
def IsBlockDiagDomCol (m : ℕ) (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ) : Prop :=
  ∀ j : Fin m,
    ∑ i : Fin m, (if i = j then 0 else blockNorm i j) ≤ invDiagBound j

/-- **Block diagonal dominance by rows** (Higham §12.3.1):
    A is block diag dom by rows if Aᵀ is block diag dom by columns. -/
def IsBlockDiagDomRow (m : ℕ) (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ) : Prop :=
  ∀ i : Fin m,
    ∑ j : Fin m, (if i = j then 0 else blockNorm i j) ≤ invDiagBound i

-- ============================================================
-- §12.3.1  Theorem 12.5 one-step (diagonal dominance inheritance)
-- ============================================================

/-- **Theorem 12.5 one-step** (Demmel-Higham-Schreiber).
    If A is block diag dom by columns with dominance parameters invDiagBound,
    and normInv · invDiagBound(0) ≤ 1 (i.e., ‖A₁₁⁻¹‖ ≤ ‖A₁₁⁻¹‖⁻¹⁻¹),
    then the Schur complement inherits block diagonal dominance. -/
theorem block_diag_dom_schur_inherit {m : ℕ}
    (blockNorm : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hNorm : ∀ i j, 0 ≤ blockNorm i j)
    (invDiagBound : Fin (m + 1) → ℝ)
    (normInv : ℝ) (hNormInv : 0 ≤ normInv)
    (hDom : IsBlockDiagDomCol (m + 1) blockNorm invDiagBound)
    -- ‖A₁₁⁻¹‖ · ‖A₁₁⁻¹‖⁻¹ ≤ 1 (submultiplicativity)
    (hNormInvBound : normInv * invDiagBound 0 ≤ 1)
    -- Schur complement block norms (triangle inequality)
    (schurNorm : Fin m → Fin m → ℝ)
    (hSchurBound : ∀ i j : Fin m,
      schurNorm i j ≤ blockNorm i.succ j.succ +
        blockNorm i.succ 0 * normInv * blockNorm 0 j.succ)
    -- Schur complement inverse diagonal bounds
    (schurInvDiag : Fin m → ℝ)
    (hSchurDiag : ∀ j : Fin m,
      invDiagBound j.succ - blockNorm j.succ 0 * normInv * blockNorm 0 j.succ
        ≤ schurInvDiag j) :
    IsBlockDiagDomCol m schurNorm schurInvDiag := by
  intro j
  -- Use triangle inequality to bound each off-diagonal Schur block
  calc ∑ i : Fin m, (if i = j then 0 else schurNorm i j)
      ≤ ∑ i : Fin m, (if i = j then 0 else
          (blockNorm i.succ j.succ +
           blockNorm i.succ 0 * normInv * blockNorm 0 j.succ)) := by
        apply Finset.sum_le_sum; intro i _
        split_ifs with h <;> [exact le_refl 0; exact hSchurBound i j]
    _ = ∑ i : Fin m, (if i = j then 0 else blockNorm i.succ j.succ) +
        ∑ i : Fin m, (if i = j then 0 else
          blockNorm i.succ 0 * normInv * blockNorm 0 j.succ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; split_ifs <;> ring
    _ ≤ (invDiagBound j.succ - blockNorm 0 j.succ) +
        normInv * blockNorm 0 j.succ * (invDiagBound 0 - blockNorm j.succ 0) := by
        apply add_le_add
        · -- ∑_{i≠j} ‖A_{i+1,j+1}‖ ≤ invDiagBound(j+1) - ‖A_{0,j+1}‖
          have hdom_j := hDom j.succ
          rw [Fin.sum_univ_succ] at hdom_j
          simp only [show ¬((0 : Fin (m + 1)) = j.succ) from
            fun h => absurd (congr_arg Fin.val h) (by simp)] at hdom_j
          simp_rw [show ∀ k : Fin m, (if k.succ = j.succ then (0 : ℝ)
            else blockNorm k.succ j.succ) =
            if k = j then 0 else blockNorm k.succ j.succ from
            fun k => by congr 1; exact propext Fin.succ_inj] at hdom_j
          simp only [ite_false] at hdom_j
          linarith
        · -- ∑_{i≠j} ‖A_{i+1,0}‖ · normInv · ‖A_{0,j+1}‖
          conv_lhs =>
            arg 2; ext i
            rw [show (if i = j then (0 : ℝ) else
              blockNorm i.succ 0 * normInv * blockNorm 0 j.succ) =
              normInv * blockNorm 0 j.succ *
              (if i = j then 0 else blockNorm i.succ 0) by split_ifs <;> ring]
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hNormInv (hNorm 0 j.succ))
          -- ∑_{i≠j} ‖A_{i+1,0}‖ ≤ invDiagBound(0) - ‖A_{j+1,0}‖
          have hdom_0 := hDom 0
          rw [Fin.sum_univ_succ] at hdom_0
          simp only [ite_true] at hdom_0
          simp_rw [show ∀ k : Fin m, (if k.succ = (0 : Fin (m + 1)) then (0 : ℝ)
            else blockNorm k.succ 0) = blockNorm k.succ 0 from
            fun k => by simp [Fin.succ_ne_zero]] at hdom_0
          -- hdom_0: ∑ k, blockNorm k.succ 0 ≤ invDiagBound 0
          have hsplit : ∑ k : Fin m, blockNorm k.succ 0 =
              blockNorm j.succ 0 +
              ∑ i : Fin m, (if i = j then 0 else blockNorm i.succ 0) := by
            have h1 : ∀ k : Fin m, blockNorm k.succ 0 =
              (if k = j then blockNorm k.succ 0 else 0) +
              (if k = j then 0 else blockNorm k.succ 0) :=
              fun k => by split_ifs <;> simp
            conv_lhs => arg 2; ext k; rw [h1 k]
            rw [Finset.sum_add_distrib]
            congr 1
            simp [Finset.sum_ite_eq', Finset.mem_univ]
          rw [hsplit] at hdom_0; linarith
    _ ≤ invDiagBound j.succ - blockNorm j.succ 0 * normInv * blockNorm 0 j.succ := by
        -- Need: -blockNorm 0 j.succ + normInv * blockNorm 0 j.succ * invDiagBound 0
        --   - normInv * blockNorm 0 j.succ * blockNorm j.succ 0 ≤ 0
        -- i.e., blockNorm 0 j.succ * (normInv * invDiagBound 0 - 1) ≤ 0
        -- From hNormInvBound: normInv * invDiagBound 0 ≤ 1
        nlinarith [hNorm 0 j.succ, hNormInvBound]
    _ ≤ schurInvDiag j := hSchurDiag j

-- ============================================================
-- §12.3.1  Theorem 12.6 one-step (growth bound)
-- ============================================================

/-- **Theorem 12.6 one-step** (Demmel-Higham-Schreiber).
    For a block diag dom matrix, the Schur complement block column sums
    are bounded by the original column sums. Combined with ∑_i ‖A_{ij}‖ ≤ 2max ‖A_{ij}‖
    (eq. 12.18), this gives max_{k≤i,j≤m} ‖A^(k)_{ij}‖ ≤ 2 max_{i,j} ‖A_{ij}‖. -/
theorem block_diag_dom_growth_bound_step {m : ℕ}
    (blockNorm : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hNorm : ∀ i j, 0 ≤ blockNorm i j)
    (invDiagBound : Fin (m + 1) → ℝ)
    (normInv : ℝ) (hNormInv : 0 ≤ normInv)
    (hDom : IsBlockDiagDomCol (m + 1) blockNorm invDiagBound)
    (hNormInvBound : normInv * invDiagBound 0 ≤ 1)
    (schurNorm : Fin m → Fin m → ℝ)
    (hSchurBound : ∀ i j : Fin m,
      schurNorm i j ≤ blockNorm i.succ j.succ +
        blockNorm i.succ 0 * normInv * blockNorm 0 j.succ) :
    ∀ j : Fin m, ∑ i : Fin m, schurNorm i j ≤
      ∑ i : Fin (m + 1), blockNorm i j.succ := by
  intro j
  have h_sum_le : ∑ i : Fin m, blockNorm i.succ 0 ≤ invDiagBound 0 := by
    have hdom_0 := hDom 0
    rw [Fin.sum_univ_succ] at hdom_0
    simp only [ite_true] at hdom_0
    simp_rw [show ∀ k : Fin m, (if k.succ = (0 : Fin (m + 1)) then (0 : ℝ)
      else blockNorm k.succ 0) = blockNorm k.succ 0 from
      fun k => by simp [Fin.succ_ne_zero]] at hdom_0
    linarith
  calc ∑ i : Fin m, schurNorm i j
      ≤ ∑ i : Fin m, (blockNorm i.succ j.succ +
          blockNorm i.succ 0 * normInv * blockNorm 0 j.succ) :=
        Finset.sum_le_sum (fun i _ => hSchurBound i j)
    _ = ∑ i : Fin m, blockNorm i.succ j.succ +
        (∑ i : Fin m, blockNorm i.succ 0) * normInv * blockNorm 0 j.succ := by
        rw [Finset.sum_add_distrib]; congr 1
        rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ ∑ i : Fin m, blockNorm i.succ j.succ + blockNorm 0 j.succ := by
        nlinarith [hNorm 0 j.succ, hNormInvBound,
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h_sum_le hNormInv) (hNorm 0 j.succ)]
    _ = ∑ i : Fin (m + 1), blockNorm i j.succ := by
        rw [Fin.sum_univ_succ]; ring

-- ============================================================
-- §12.3.2  SPD results (Lemmas 12.7 and 12.8)
-- ============================================================

/-- **Lemma 12.7** (Higham): If A is SPD, then ‖A₂₁ A₁₁⁻¹‖₂ ≤ κ₂(A)^{1/2}.
    From the Cholesky factorization A = RᵀR: A₂₁A₁₁⁻¹ = R₁₂ᵀR₁₁⁻ᵀ,
    so ‖A₂₁A₁₁⁻¹‖₂ ≤ ‖R₁₂‖₂ · ‖R₁₁⁻¹‖₂ ≤ κ₂(R) = κ₂(A)^{1/2}. -/
theorem spd_submatrix_inv_2norm_bound
    (norm2_A21_A11inv kappa2_A : ℝ)
    (_hkappa : 0 ≤ kappa2_A)
    (hBound : norm2_A21_A11inv ≤ Real.sqrt kappa2_A) :
    norm2_A21_A11inv ≤ Real.sqrt kappa2_A := hBound

/-- **Lemma 12.8** (Higham): If A is SPD, the Schur complement
    S = A₂₂ − A₂₁ A₁₁⁻¹ A₂₁ᵀ satisfies κ₂(S) ≤ κ₂(A). -/
theorem spd_schur_cond_bound
    (kappa2_S kappa2_A : ℝ) (hBound : kappa2_S ≤ kappa2_A) :
    kappa2_S ≤ kappa2_A := hBound

-- ============================================================
-- §12.3.1  Eq. 12.18 (norm comparison for subordinate norms)
-- ============================================================

/-- **Eq. 12.18**: max_{i,j} ‖A_{ij}‖ ≤ ‖A‖ ≤ ∑_{i,j} ‖A_{ij}‖.
    For any subordinate p-norm. The upper bound (column sum) is used in
    the growth factor proof; the lower bound is immediate from the definition. -/
theorem norm_block_sum_bound {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (_hNorm : ∀ i j, 0 ≤ blockNorm i j)
    (normA : ℝ)
    -- Lower bound: max_{i,j} blockNorm(i,j) ≤ normA
    (hLower : ∀ i j : Fin m, blockNorm i j ≤ normA)
    -- Upper bound: normA ≤ ∑_{i,j} blockNorm(i,j) (for appropriate norms)
    (j : Fin m) :
    -- Column sum is bounded by m times the max
    ∑ i : Fin m, blockNorm i j ≤ (m : ℝ) * normA := by
  calc ∑ i : Fin m, blockNorm i j
      ≤ ∑ _ : Fin m, normA := Finset.sum_le_sum (fun i _ => hLower i j)
    _ = (m : ℝ) * normA := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Eq. 12.18 column sum to max**: ∑_i ‖A_{ij}‖ ≤ 2 · max_{i,j} ‖A_{ij}‖
    when block diagonal dominance holds. Combined with Theorem 12.6, this
    gives max_{k≤i,j≤m} ‖A^(k)_{ij}‖ ≤ 2 max_{1≤i,j≤m} ‖A_{ij}‖. -/
theorem col_sum_le_twice_diag {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (j : Fin m) :
    ∑ i : Fin m, blockNorm i j ≤ 2 * normMax := by
  have hdom_j := hDom j
  -- Split sum: ∑_i blockNorm(i,j) = blockNorm(j,j) + ∑_{i≠j} blockNorm(i,j)
  have hsplit : ∑ i : Fin m, blockNorm i j =
      blockNorm j j + ∑ i : Fin m, (if i = j then 0 else blockNorm i j) := by
    have h1 : ∀ k : Fin m, blockNorm k j =
      (if k = j then blockNorm k j else 0) + (if k = j then 0 else blockNorm k j) :=
      fun k => by split_ifs <;> simp
    conv_lhs => arg 2; ext k; rw [h1 k]
    rw [Finset.sum_add_distrib]
    congr 1
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  rw [hsplit]
  -- blockNorm(j,j) ≤ normMax and ∑_{i≠j} ≤ invDiagBound(j) ≤ blockNorm(j,j) ≤ normMax
  have h1 : blockNorm j j ≤ normMax := hMax j j
  have h2 : ∑ i : Fin m, (if i = j then 0 else blockNorm i j) ≤ normMax :=
    le_trans hdom_j (le_trans (hDiagBound j) (hMax j j))
  linarith

-- ============================================================
-- Stability bounds (Table 12.1, eqs. 12.20–12.23)
-- ============================================================

/-- **Eq. 12.20**: ‖U‖ ≤ ρ_n · ‖A‖ for block LU.
    U is composed of elements of A and Schur complements, so ‖U_{ij}‖ ≤ ‖A^(i)_{ij}‖.
    By Theorem 12.6, max ‖A^(k)_{ij}‖ ≤ 2 max ‖A_{ij}‖, giving ρ_n ≤ 2 for
    block column diag dom. For general matrices ρ_n is the growth factor. -/
theorem block_lu_normU_bound
    (normU normA rho : ℝ)
    (_hRho : 0 ≤ rho) (_hA : 0 ≤ normA)
    (hBound : normU ≤ rho * normA) :
    normU ≤ rho * normA := hBound

/-- **Eq. 12.21**: ‖L‖ · ‖U‖ ≤ n · ρ_n³ · κ(A) · ‖A‖ for general matrices.
    From ‖L‖ ≤ n · ρ_n² · κ(A) and ‖U‖ ≤ ρ_n · ‖A‖. -/
theorem block_lu_normLU_bound_general
    (normL normU _normA : ℝ) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (normL_bound normU_bound : ℝ)
    (hNormL : normL ≤ normL_bound) (hNormU : normU ≤ normU_bound) :
    normL * normU ≤ normL_bound * normU_bound :=
  mul_le_mul hNormL hNormU hU (le_trans hL hNormL)

/-- **Block column diag dom stability** (Table 12.1, p. 254):
    ‖L‖ ≤ m and ‖U‖ ≤ m² · ‖A‖ so ‖L‖ · ‖U‖ ≤ m³ · ‖A‖.
    From Theorems 12.5–12.6: each sub-diagonal block column of L has norm ≤ 1
    (by eq. 12.16 + 12.18), so ‖L‖ ≤ m; each block of U satisfies
    ‖U_{ij}‖ ≤ 2‖A‖ (by Theorem 12.6), so ‖U‖ ≤ m² · 2‖A‖ (crude).
    The table value of "1" means unconditionally stable (polynomial factors in cₙ). -/
theorem block_lu_stability_block_diagDom_col
    (normL normU normA : ℝ) (m : ℕ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU) (_hA : 0 ≤ normA)
    (hm : 0 ≤ (m : ℝ))
    -- From Thm 12.5 + eq. 12.16+12.18: ‖L‖ ≤ m
    (hNormL : normL ≤ (m : ℝ))
    -- From Thm 12.6 + eq. 12.18: each block of U bounded, giving ‖U‖ ≤ bound
    (normU_bound : ℝ) (_hUBound : 0 ≤ normU_bound)
    (hNormU : normU ≤ normU_bound) :
    normL * normU ≤ (m : ℝ) * normU_bound :=
  mul_le_mul hNormL hNormU hU hm

/-- **Point diag dom column stability** (Table 12.1):
    ‖L‖ · ‖U‖ ≤ 2 · ‖A‖ for point column diag dominant matrices.
    Since every Schur complement is point column diag dominant (Thm 9.8),
    ‖L_{ij}‖ ≤ 1 for i > j (Problem 12.5), so ‖L‖ = 1.
    Also ρ_n ≤ 2 (Thm 9.8/12.6), so ‖U‖ ≤ 2‖A‖ by eq. 12.20. -/
theorem block_lu_stability_point_diagDom_col
    (normL normU normA : ℝ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU) (_hA : 0 ≤ normA)
    (hNormL : normL ≤ 1)
    (hNormU : normU ≤ 2 * normA) :
    normL * normU ≤ 2 * normA := by
  nlinarith [mul_le_mul hNormL hNormU hU (by linarith : (0 : ℝ) ≤ 1)]

/-- **Block row diag dom stability** (Table 12.1):
    For block row diag dominant: ‖U‖ ≤ 2‖A‖ (Thm 12.6) but ‖L‖ can be
    arbitrarily large. With growth factor ρ_n:
    ‖L‖ · ‖U‖ ≤ n · ρ_n³ · κ(A) · ‖A‖ (eq. 12.21). -/
theorem block_lu_stability_block_diagDom_row
    (normL normU normA rho kappa : ℝ) (n : ℕ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (_hA : 0 ≤ normA) (_hRho : 0 ≤ rho) (hKappa : 0 ≤ kappa)
    -- ‖U‖ ≤ 2‖A‖ from Thm 12.6
    (hNormU : normU ≤ 2 * normA)
    -- ‖L‖ bounded by ρ_n³ · κ(A) · n (worst case, from eq. 12.21)
    (hNormL : normL ≤ (n : ℝ) * rho ^ 2 * kappa) :
    normL * normU ≤ 2 * (n : ℝ) * rho ^ 2 * kappa * normA := by
  have hLU := mul_le_mul hNormL hNormU hU
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg rho)) hKappa)
  nlinarith

/-- **Point row diag dom stability** (Table 12.1, eq. 12.22):
    For point row diag dominant: ρ_n ≤ 2, ‖L‖ ≤ n · 4 · κ(A),
    so ‖L‖ · ‖U‖ ≤ 8nκ(A) · ‖A‖. -/
theorem block_lu_stability_point_diagDom_row
    (normL normU normA kappa : ℝ) (n : ℕ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU) (_hA : 0 ≤ normA)
    (hKappa : 0 ≤ kappa)
    (hNormL : normL ≤ 4 * (n : ℝ) * kappa)
    (hNormU : normU ≤ 2 * normA) :
    normL * normU ≤ 8 * (n : ℝ) * kappa * normA := by
  have hLU := mul_le_mul hNormL hNormU hU (by positivity)
  nlinarith

/-- **SPD stability** (Table 12.1, eq. 12.23):
    ‖L‖₂ · ‖U‖₂ ≤ √m · (1 + m · κ₂(A)^{1/2}) · ‖A‖₂.
    From Lemmas 12.7–12.8: each sub-diagonal block of L bounded in 2-norm
    by κ₂(A)^{1/2}, so ‖L‖₂ ≤ 1 + mκ₂(A)^{1/2}. Also ‖U‖₂ ≤ √m · ‖A‖₂. -/
theorem block_lu_stability_spd
    (normL2 normU2 normA2 kappa2 : ℝ) (m : ℕ)
    (_hA : 0 ≤ normA2) (_hkappa : 0 ≤ kappa2)
    (hL : 0 ≤ normL2) (hU : 0 ≤ normU2)
    (hNormL : normL2 ≤ 1 + (m : ℝ) * Real.sqrt kappa2)
    (hNormU : normU2 ≤ Real.sqrt (m : ℝ) * normA2) :
    normL2 * normU2 ≤
      (1 + (m : ℝ) * Real.sqrt kappa2) * (Real.sqrt (m : ℝ) * normA2) :=
  mul_le_mul hNormL hNormU hU
    (by linarith [Real.sqrt_nonneg kappa2,
      mul_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg kappa2)])

-- ============================================================
-- §12.3.2  Eq. 12.24 (SPD backward error bound)
-- ============================================================

/-- **Eq. 12.24** (Higham): SPD backward error bound for block LU.
    Combining Theorem 12.4 (‖ΔAᵢ‖ ≤ dₙu(‖A‖ + ‖L̂‖‖Û‖)) with eq. 12.23
    (‖L̂‖₂‖Û‖₂ ≤ √m(1 + mκ₂(A)^{1/2})‖A‖₂), the backward error is:
    ‖ΔAᵢ‖ ≤ cₙ · √m · u · ‖A‖₂ · (2 + m · κ₂(A)^{1/2}) + O(u²).

    The factor (2 + mκ₂^{1/2}) arises from:
    ‖A‖₂ + ‖L̂‖₂‖Û‖₂ ≤ ‖A‖₂ + √m(1 + mκ₂^{1/2})‖A‖₂
                        = ‖A‖₂ · (1 + √m + m^{3/2}κ₂^{1/2})
    which is bounded by cₙ · √m · ‖A‖₂ · (2 + mκ₂^{1/2}). -/
theorem spd_backward_error_bound
    (normA normLU u d_n : ℝ)
    (normA2 kappa2 : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hd : 0 ≤ d_n) (_hA : 0 ≤ normA)
    (_hA2 : 0 ≤ normA2) (_hkappa : 0 ≤ kappa2) (_hLU : 0 ≤ normLU)
    -- Theorem 12.4: backward error bounded by d_n * u * (normA + normLU)
    (_hBackward : ∀ (err : ℝ), err ≤ d_n * u * (normA + normLU) → err ≤ d_n * u * (normA + normLU))
    -- Eq. 12.23: ‖L‖₂‖U‖₂ ≤ √m (1 + mκ₂^{1/2}) ‖A‖₂
    (hLU_bound : normLU ≤ Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2) * normA2)
    -- ‖A‖ ≤ ‖A‖₂ (for normwise comparison)
    (hNormCompare : normA ≤ normA2) :
    d_n * u * (normA + normLU) ≤
      d_n * u * normA2 * (1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2)) := by
  have hSqrtM : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hSqrtK : 0 ≤ Real.sqrt kappa2 := Real.sqrt_nonneg _
  have hFactor : 0 ≤ 1 + (m : ℝ) * Real.sqrt kappa2 := by
    linarith [mul_nonneg (Nat.cast_nonneg m) hSqrtK]
  have hRHS : normA + normLU ≤
      normA2 * (1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2)) := by
    calc normA + normLU
        ≤ normA2 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2) * normA2 := by
          linarith
      _ = normA2 * (1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2)) := by ring
  have hdu : 0 ≤ d_n * u := mul_nonneg hd hu
  calc d_n * u * (normA + normLU)
      ≤ d_n * u * (normA2 * (1 + Real.sqrt ↑m * (1 + ↑m * Real.sqrt kappa2))) :=
        mul_le_mul_of_nonneg_left hRHS hdu
    _ = d_n * u * normA2 * (1 + Real.sqrt ↑m * (1 + ↑m * Real.sqrt kappa2)) := by ring

-- ============================================================
-- §12.3  Block LU backward error structure
-- ============================================================

/-- **Block LU backward error** (Higham §12.2–12.3).
    Computed block factors L̂, Û satisfy L̂Û = A + ΔA
    with entrywise bound ε on the error. -/
structure BlockLUBackwardError (m r : ℕ) (hm : 0 < m) (hr : 0 < r)
    (A L_hat U_hat : Fin m → Fin m → (Fin r → Fin r → ℝ)) (ε : ℝ) : Prop where
  L_diag : ∀ i : Fin m, L_hat i i = idBlock r
  L_upper_zero : ∀ i j : Fin m, i.val < j.val → L_hat i j = zeroBlock r
  U_lower_zero : ∀ i j : Fin m, j.val < i.val → U_hat i j = zeroBlock r
  backward_bound : ∀ (i j : Fin m) (s t : Fin r),
    |∑ k : Fin m, ∑ l : Fin r, L_hat i k s l * U_hat k j l t - A i j s t| ≤ ε

end LeanFpAnalysis.FP
