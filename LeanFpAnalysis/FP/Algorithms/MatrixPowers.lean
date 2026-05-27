-- Algorithms/MatrixPowers.lean
--
-- Higham Chapter 17: Error analysis of matrix powers.
--
-- Covers §17.2 (finite precision bounds for computed A^m via repeated
-- matrix-vector products) and the similarity-based convergence engine
-- underlying Theorem 17.1 (Higham–Knight).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Analysis.Rounding
namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §17.2  Backward error model for computed matrix powers
-- ============================================================

/-- Model for computing A^m v by repeated matrix-vector multiplication.

    At each step the computed vector satisfies
      v_{k+1} = (A + ΔA_k) · v_k,   |ΔA_k| ≤ c · |A|  componentwise
    corresponding to Higham eq (17.10)–(17.11).

    The constant c is `gamma fp n` when each step is a standard matVec
    of an n-column matrix (from `matVec_backward_error`). -/
structure ComputedMatPowVec (n : ℕ) (A : Fin n → Fin n → ℝ)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) : Prop where
  step : ∀ k, ∃ ΔA : Fin n → Fin n → ℝ,
    (∀ i j, |ΔA i j| ≤ c * |A i j|) ∧
    (∀ i, v (k + 1) i = ∑ j : Fin n, (A i j + ΔA i j) * v k j)

-- ============================================================
-- One-step componentwise bound
-- ============================================================

/-- **One-step componentwise bound**: if v_{k+1} = (A+ΔA)v_k with
    |ΔA_{ij}| ≤ c·|A_{ij}|, then
    |v_{k+1,i}| ≤ (1+c) · ∑_j |A_{ij}| · |v_{k,j}|. -/
theorem one_step_matpow_bound (n : ℕ) (A ΔA : Fin n → Fin n → ℝ)
    (v : Fin n → ℝ) (c : ℝ)
    (hΔ : ∀ i j, |ΔA i j| ≤ c * |A i j|)
    (w : Fin n → ℝ) (hw : ∀ i, w i = ∑ j : Fin n, (A i j + ΔA i j) * v j) :
    ∀ i, |w i| ≤ (1 + c) * ∑ j : Fin n, |A i j| * |v j| := by
  intro i
  rw [hw i]
  calc |∑ j : Fin n, (A i j + ΔA i j) * v j|
      ≤ ∑ j : Fin n, |(A i j + ΔA i j) * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |A i j + ΔA i j| * |v j| := by
        congr 1; ext j; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, (|A i j| + c * |A i j|) * |v j| := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        calc |A i j + ΔA i j|
            ≤ |A i j| + |ΔA i j| := abs_add_le _ _
          _ ≤ |A i j| + c * |A i j| := by linarith [hΔ i j]
    _ = (1 + c) * ∑ j : Fin n, |A i j| * |v j| := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

-- ============================================================
-- §17.2  Componentwise forward bound (consequence of 17.10–17.11)
-- ============================================================

/-- **Componentwise bound for computed matrix powers** (§17.2).

    If v_{k+1} = (A+ΔA_k)v_k with |ΔA_k| ≤ c|A|, then
      |v_m i| ≤ (1+c)^m · (|A|^m |v_0|)_i
    componentwise, where |A|^m denotes the mth power of the entrywise
    absolute value matrix. -/
theorem matPow_componentwise_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c) (m : ℕ) :
    ∀ i, |v m i| ≤ (1 + c) ^ m *
      matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i := by
  induction m with
  | zero =>
    intro i
    simp only [pow_zero, one_mul, matPow]
    unfold matMulVec absVec idMatrix
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, le_refl]
  | succ m ih =>
    intro i
    obtain ⟨ΔA, hΔ, hstep⟩ := hComp.step m
    have h1 := one_step_matpow_bound n A ΔA (v m) c hΔ (v (m + 1)) hstep i
    calc |v (m + 1) i|
        ≤ (1 + c) * ∑ j : Fin n, |A i j| * |v m j| := h1
      _ ≤ (1 + c) * ∑ j : Fin n, |A i j| *
          ((1 + c) ^ m * matMulVec n (matPow n (absMatrix n A) m)
            (absVec n (v 0)) j) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left (ih j) (abs_nonneg _)
      _ = (1 + c) ^ (m + 1) * ∑ j : Fin n, |A i j| *
          matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) j := by
          simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
          set w := matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) j; ring
      _ = (1 + c) ^ (m + 1) *
          matMulVec n (matPow n (absMatrix n A) (m + 1)) (absVec n (v 0)) i := by
          congr 1
          show ∑ j, |A i j| * matMulVec n (matPow n (absMatrix n A) m)
              (absVec n (v 0)) j =
            matMulVec n (matMul n (absMatrix n A) (matPow n (absMatrix n A) m))
              (absVec n (v 0)) i
          unfold matMulVec matMul absMatrix
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro j _; ring

-- ============================================================
-- §17.2  Normwise forward bound
-- ============================================================

/-- **Normwise bound for computed matrix powers** (§17.2).

    ‖v_m‖∞ ≤ ((1+c) · ‖A‖∞)^m · ‖v_0‖∞. -/
theorem matPow_normwise_bound (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c) (m : ℕ) :
    infNormVec (v m) ≤ ((1 + c) * infNorm A) ^ m * infNormVec (v 0) := by
  apply infNormVec_le_of_abs_le
  · intro i
    have hcw := matPow_componentwise_bound n A v c hc hComp m i
    -- Pointwise bound on the matMulVec term
    have hmv : matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i ≤
        infNorm A ^ m * infNormVec (v 0) := by
      calc matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i
          ≤ |matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i| :=
            le_abs_self _
        _ ≤ infNormVec (matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0))) :=
            abs_le_infNormVec _ i
        _ ≤ infNorm (matPow n (absMatrix n A) m) * infNormVec (absVec n (v 0)) :=
            infNormVec_matMulVec_le hn _ _
        _ ≤ infNorm A ^ m * infNormVec (absVec n (v 0)) := by
            apply mul_le_mul_of_nonneg_right _ (infNormVec_nonneg _)
            calc infNorm (matPow n (absMatrix n A) m)
                ≤ infNorm (absMatrix n A) ^ m := infNorm_matPow_le hn _ _
              _ = infNorm A ^ m := by rw [infNorm_absMatrix hn]
        _ = infNorm A ^ m * infNormVec (v 0) := by
            rw [infNormVec_absVec hn]
    calc |v m i|
        ≤ (1 + c) ^ m * matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i := hcw
      _ ≤ (1 + c) ^ m * (infNorm A ^ m * infNormVec (v 0)) :=
          mul_le_mul_of_nonneg_left hmv (pow_nonneg (by linarith) m)
      _ = ((1 + c) * infNorm A) ^ m * infNormVec (v 0) := by
          rw [← mul_assoc, ← mul_pow]
  · exact mul_nonneg
      (pow_nonneg (mul_nonneg (by linarith) (infNorm_nonneg A)) m)
      (infNormVec_nonneg _)

-- ============================================================
-- §17.2  Sufficient convergence condition (normwise, eq 17.12)
-- ============================================================

/-- **Sufficient condition for convergence of computed matrix powers**
    (normwise version of eq 17.12).

    If q := (1+c)·‖A‖∞ ≤ some q₀ < 1, then ‖v_m‖∞ ≤ q₀^m · ‖v_0‖∞.

    The book states (17.12) as ρ(|A|) < 1/(1+γ_n), which is sharper
    since ρ(|A|) ≤ ‖A‖∞. -/
theorem matPow_convergence_bound (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (q : ℝ) (hq : (1 + c) * infNorm A ≤ q) (m : ℕ) :
    infNormVec (v m) ≤ q ^ m * infNormVec (v 0) := by
  calc infNormVec (v m)
      ≤ ((1 + c) * infNorm A) ^ m * infNormVec (v 0) :=
        matPow_normwise_bound n hn A v c hc hComp m
    _ ≤ q ^ m * infNormVec (v 0) := by
        apply mul_le_mul_of_nonneg_right _ (infNormVec_nonneg _)
        exact pow_le_pow_left₀
          (mul_nonneg (by linarith) (infNorm_nonneg A)) hq m

-- ============================================================
-- §17.2  Matrix-level componentwise bound (column by column)
-- ============================================================

/-- **Matrix-level componentwise bound**: if each column of fl(A^m) is
    computed by repeated matVec starting from e_j (so B_0 = I), then
    |fl(A^m)_{ij}| ≤ (1+c)^m · (|A|^m)_{ij}. -/
theorem matPow_matrix_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (B : ℕ → (Fin n → Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hInit : B 0 = idMatrix n)
    (hCol : ∀ j : Fin n, ComputedMatPowVec n A (fun k => fun i => B k i j) c)
    (m : ℕ) :
    ∀ i j, |B m i j| ≤ (1 + c) ^ m * matPow n (absMatrix n A) m i j := by
  intro i j
  have hcw := matPow_componentwise_bound n A
    (fun k => fun i' => B k i' j) c hc (hCol j) m i
  calc |B m i j|
      ≤ (1 + c) ^ m * matMulVec n (matPow n (absMatrix n A) m)
          (absVec n (fun i' => B 0 i' j)) i := hcw
    _ = (1 + c) ^ m * ∑ l : Fin n,
          matPow n (absMatrix n A) m i l * |B 0 l j| := by
        unfold matMulVec absVec; ring_nf
    _ = (1 + c) ^ m * matPow n (absMatrix n A) m i j := by
        congr 1
        have hid : ∀ l : Fin n, |B 0 l j| = if l = j then 1 else 0 := by
          intro l; rw [hInit]; unfold idMatrix; split <;> simp
        simp_rw [hid, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]

-- ============================================================
-- §17.2  Nonneg matrix specialization
-- ============================================================

/-- **Nonneg matrix simplification**: when A ≥ 0, |A| = A so the
    componentwise bound simplifies to |v_m i| ≤ (1+c)^m · (A^m |v_0|)_i. -/
theorem matPow_nonneg_componentwise_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c) (m : ℕ) :
    ∀ i, |v m i| ≤ (1 + c) ^ m *
      matMulVec n (matPow n A m) (absVec n (v 0)) i := by
  have habs : absMatrix n A = A := by
    ext i j; unfold absMatrix; exact abs_of_nonneg (hA i j)
  intro i
  have hcw := matPow_componentwise_bound n A v c hc hComp m i
  rwa [habs] at hcw

-- ============================================================
-- §17.2  Similarity-based convergence engine (eq 17.14)
-- ============================================================

/-- **Similarity-based convergence criterion** (eq 17.14 in Theorem 17.1 proof).

    If there exists a nonsingular S such that for all perturbations ΔA_k,
      ‖S⁻¹(A+ΔA_k)S‖∞ ≤ q < 1,
    then ‖S⁻¹ v_m‖∞ ≤ q^m · ‖S⁻¹ v_0‖∞.

    This is the reusable engine underlying Theorem 17.1. The Jordan form
    is only used to CONSTRUCT the right S; this engine works for any S. -/
theorem similarity_product_bound (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (S S_inv : Fin n → Fin n → ℝ)
    (hSr : IsRightInverse n S S_inv)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ)
    (hComp : ComputedMatPowVec n A v c)
    (q : ℝ) (hq : 0 ≤ q)
    (hBound : ∀ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ c * |A i j|) →
      infNorm (matMul n S_inv (matMul n (fun i j => A i j + ΔA i j) S)) ≤ q) :
    ∀ m, infNormVec (matMulVec n S_inv (v m)) ≤
      q ^ m * infNormVec (matMulVec n S_inv (v 0)) := by
  intro m; induction m with
  | zero => simp [pow_zero, one_mul]
  | succ m ih =>
    obtain ⟨ΔA, hΔ, hstep⟩ := hComp.step m
    have hBk := hBound ΔA hΔ
    let B := fun i j => A i j + ΔA i j
    have hSS : matMul n S S_inv = idMatrix n := by ext a b; exact hSr a b
    -- Establish v_{m+1} = B v_m
    have hBv : ∀ k, v (m + 1) k = matMulVec n B (v m) k := by
      intro k; exact hstep k
    -- Key algebraic identity: (S⁻¹BS) · S⁻¹ = S⁻¹B
    have h_eq : matMul n (matMul n S_inv (matMul n B S)) S_inv =
        matMul n S_inv B := by
      rw [matMul_assoc, matMul_assoc, hSS, matMul_id_right]
    -- Key: S⁻¹ v_{m+1} = (S⁻¹ B S)(S⁻¹ v_m)
    have key : ∀ i, matMulVec n S_inv (v (m + 1)) i =
        matMulVec n (matMul n S_inv (matMul n B S))
          (matMulVec n S_inv (v m)) i := by
      intro i
      -- S⁻¹ v_{m+1} = S⁻¹ (B v_m)
      have h1 : matMulVec n S_inv (v (m + 1)) i =
          matMulVec n S_inv (matMulVec n B (v m)) i := by
        unfold matMulVec; congr 1; ext k; congr 1; exact hBv k
      -- S⁻¹ (B v_m) = (S⁻¹ B) v_m
      have h2 : matMulVec n S_inv (matMulVec n B (v m)) i =
          matMulVec n (matMul n S_inv B) (v m) i :=
        (matMulVec_matMul n S_inv B (v m) i).symm
      -- (S⁻¹ B) v_m = ((S⁻¹BS)S⁻¹) v_m
      have h3 : matMulVec n (matMul n S_inv B) (v m) i =
          matMulVec n (matMul n (matMul n S_inv (matMul n B S)) S_inv) (v m) i := by
        rw [h_eq]
      -- ((S⁻¹BS)S⁻¹) v_m = (S⁻¹BS)(S⁻¹ v_m)
      have h4 : matMulVec n (matMul n (matMul n S_inv (matMul n B S)) S_inv) (v m) i =
          matMulVec n (matMul n S_inv (matMul n B S)) (matMulVec n S_inv (v m)) i :=
        matMulVec_matMul n (matMul n S_inv (matMul n B S)) S_inv (v m) i
      exact h1.trans (h2.trans (h3.trans h4))
    -- ‖S⁻¹ v_{m+1}‖ ≤ ‖S⁻¹BS‖ · ‖S⁻¹ v_m‖ ≤ q · ‖S⁻¹ v_m‖
    have h1 : infNormVec (matMulVec n S_inv (v (m + 1))) ≤
        q * infNormVec (matMulVec n S_inv (v m)) := by
      calc infNormVec (matMulVec n S_inv (v (m + 1)))
          = infNormVec (matMulVec n (matMul n S_inv (matMul n B S))
              (matMulVec n S_inv (v m))) := by
            exact congrArg infNormVec (funext key)
        _ ≤ infNorm (matMul n S_inv (matMul n B S)) *
            infNormVec (matMulVec n S_inv (v m)) :=
            infNormVec_matMulVec_le hn _ _
        _ ≤ q * infNormVec (matMulVec n S_inv (v m)) :=
            mul_le_mul_of_nonneg_right hBk (infNormVec_nonneg _)
    calc infNormVec (matMulVec n S_inv (v (m + 1)))
        ≤ q * infNormVec (matMulVec n S_inv (v m)) := h1
      _ ≤ q * (q ^ m * infNormVec (matMulVec n S_inv (v 0))) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (m + 1) * infNormVec (matMulVec n S_inv (v 0)) := by ring

-- ============================================================
-- §17.2  Corollary: normwise bound via similarity
-- ============================================================

/-- **Normwise bound via similarity**: ‖v_m‖∞ ≤ κ∞(S) · q^m · ‖v_0‖∞.

    Since v = S(S⁻¹v), we have ‖v‖ ≤ ‖S‖·‖S⁻¹v‖.
    Combined with the similarity product bound and ‖S⁻¹v_0‖ ≤ ‖S⁻¹‖·‖v_0‖. -/
theorem similarity_normwise_bound (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (S S_inv : Fin n → Fin n → ℝ)
    (hSr : IsRightInverse n S S_inv)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ)
    (hComp : ComputedMatPowVec n A v c)
    (q : ℝ) (hq : 0 ≤ q)
    (hBound : ∀ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ c * |A i j|) →
      infNorm (matMul n S_inv (matMul n (fun i j => A i j + ΔA i j) S)) ≤ q)
    (m : ℕ) :
    infNormVec (v m) ≤
      infNorm S * infNorm S_inv * q ^ m * infNormVec (v 0) := by
  have hSS : matMul n S S_inv = idMatrix n := by ext a b; exact hSr a b
  -- Step 1: w = S(S⁻¹w) so ‖w‖ ≤ ‖S‖·‖S⁻¹w‖
  have hv_eq : ∀ (w : Fin n → ℝ) (i : Fin n),
      w i = matMulVec n S (matMulVec n S_inv w) i := by
    intro w i
    have h1 := (matMulVec_matMul n S S_inv w i).symm
    rw [h1, hSS]; unfold matMulVec idMatrix; simp [Finset.mem_univ]
  have h_norm_le : ∀ (w : Fin n → ℝ),
      infNormVec w ≤ infNorm S * infNormVec (matMulVec n S_inv w) := by
    intro w
    apply infNormVec_le_of_abs_le
    · intro i
      rw [hv_eq w i]
      calc |matMulVec n S (matMulVec n S_inv w) i|
          ≤ ∑ j, |S i j| * |matMulVec n S_inv w j| := abs_matMulVec_le n S _ i
        _ ≤ ∑ j : Fin n, |S i j| * infNormVec (matMulVec n S_inv w) := by
            apply Finset.sum_le_sum; intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact abs_le_infNormVec (matMulVec n S_inv w) j
        _ = (∑ j : Fin n, |S i j|) * infNormVec (matMulVec n S_inv w) :=
            (Finset.sum_mul ..).symm
        _ ≤ infNorm S * infNormVec (matMulVec n S_inv w) :=
            mul_le_mul_of_nonneg_right (row_sum_le_infNorm S i)
              (infNormVec_nonneg _)
    · exact mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _)
  -- Step 2: combine
  have h2 := similarity_product_bound n hn A S S_inv hSr v c hComp q hq hBound m
  have h3 : infNormVec (matMulVec n S_inv (v 0)) ≤
      infNorm S_inv * infNormVec (v 0) :=
    infNormVec_matMulVec_le hn S_inv (v 0)
  calc infNormVec (v m)
      ≤ infNorm S * infNormVec (matMulVec n S_inv (v m)) := h_norm_le (v m)
    _ ≤ infNorm S * (q ^ m * infNormVec (matMulVec n S_inv (v 0))) :=
        mul_le_mul_of_nonneg_left h2 (infNorm_nonneg S)
    _ ≤ infNorm S * (q ^ m * (infNorm S_inv * infNormVec (v 0))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h3 (pow_nonneg hq m))
          (infNorm_nonneg S)
    _ = infNorm S * infNorm S_inv * q ^ m * infNormVec (v 0) := by ring

-- ============================================================
-- Theorem 17.1: JordanFormSpec and convergence condition
-- ============================================================

/-- Axiomatized Jordan form data for a matrix A.

    Captures the essential properties needed from A = XJX⁻¹:
    - X is the similarity matrix with inverse X_inv
    - spectral_radius ρ(A) < 1 (convergent matrix)
    - max_block_size t = max_i n_i (largest Jordan block)

    The key derived property `similarity_absorbs` axiomatizes the full
    Jordan block scaling construction (Higham pp. 354–355): given the
    Higham–Knight condition 4t·η·κ∞(X)·‖A‖∞ < (1-ρ)^t, there exists
    a similarity S = XP(ε) (constructed over ℂ via Jordan form scaling
    with D(δ) = diag(1,δ,...,δ^{n_i-1})) that absorbs all perturbations
    ΔA with |ΔA| ≤ η|A|.  The construction requires:
    1. Jordan Normal Form (needs algebraically closed field ℂ),
    2. δ-scaling of Jordan blocks to control ‖S⁻¹(A+ΔA)S‖∞,
    3. The inequality (1+1/t)^t < e < 4 for the 4t factor.

    Note: κ∞(S) ≤ (1−ρ−ε)^{1−t} · κ∞(X) from eq (17.15), which is
    generally ≥ κ∞(X) when t > 1.  We do not constrain κ∞(S) here;
    the convergence constant C in Theorem 17.1 is κ∞(S), not κ∞(X). -/
structure JordanFormSpec (n : ℕ) (hn : 0 < n)
    (A X X_inv : Fin n → Fin n → ℝ) where
  inv_right : IsRightInverse n X X_inv
  spectral_radius : ℝ
  hr_nonneg : 0 ≤ spectral_radius
  hr_lt_one : spectral_radius < 1
  max_block_size : ℕ
  ht_pos : 0 < max_block_size
  /-- The Higham–Knight condition guarantees existence of a similarity
      absorbing all valid perturbations. -/
  similarity_absorbs :
    ∀ (η : ℝ), 0 ≤ η →
    4 * max_block_size * η * (infNorm X * infNorm X_inv) *
      infNorm A < (1 - spectral_radius) ^ max_block_size →
    ∃ S S_inv : Fin n → Fin n → ℝ,
    ∃ q : ℝ,
      IsRightInverse n S S_inv ∧
      0 ≤ q ∧ q < 1 ∧
      (∀ ΔA : Fin n → Fin n → ℝ,
        (∀ i j, |ΔA i j| ≤ η * |A i j|) →
        infNorm (matMul n S_inv
          (matMul n (fun i j => A i j + ΔA i j) S)) ≤ q)

/-- **Theorem 17.1** (Higham–Knight): sufficient condition for convergence
    of computed matrix powers.

    Let A ∈ ℝ^{n×n} with ρ(A) < 1 and Jordan form data (X, X⁻¹, ρ, t).
    A sufficient condition for fl(A^m) → 0 is

      4t · c · κ∞(X) · ‖A‖∞ < (1 − ρ(A))^t       (eq 17.13)

    where t = max_i n_i (largest Jordan block), c is the per-step backward
    error bound, and κ∞(X) = ‖X‖∞ · ‖X⁻¹‖∞.

    The conclusion gives geometric convergence: ∃ C q with q < 1 and
    ‖v_m‖∞ ≤ C · q^m · ‖v_0‖∞.  The constant C = κ∞(S) where S = XP(ε)
    is the scaled similarity from the proof (eq 17.15); in general
    κ∞(S) ≥ κ∞(X) when t > 1.

    Proof: obtain similarity S from JordanFormSpec.similarity_absorbs,
    then apply the similarity-based convergence engine. -/
theorem higham_knight_17_1 (n : ℕ) (hn : 0 < n)
    (A X X_inv : Fin n → Fin n → ℝ)
    (hJ : JordanFormSpec n hn A X X_inv)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * hJ.max_block_size * c *
      (infNorm X * infNorm X_inv) * infNorm A <
      (1 - hJ.spectral_radius) ^ hJ.max_block_size) :
    ∃ (C q : ℝ), 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ m, infNormVec (v m) ≤
        C * q ^ m * infNormVec (v 0) := by
  obtain ⟨S, S_inv, q, hSr, hq0, hq1, hAbsorb⟩ :=
    hJ.similarity_absorbs c hc hCond
  exact ⟨infNorm S * infNorm S_inv, q,
    mul_nonneg (infNorm_nonneg S) (infNorm_nonneg S_inv),
    hq0, hq1, fun m =>
    similarity_normwise_bound n hn A S S_inv hSr v c hComp q hq0 hAbsorb m⟩

end LeanFpAnalysis.FP
