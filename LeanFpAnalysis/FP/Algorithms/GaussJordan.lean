-- Algorithms/GaussJordan.lean
--
-- Higham Chapter 14, §14.4: Gauss–Jordan Elimination.
--
-- The second stage of GJE reduces the upper triangular factor U from
-- Gaussian elimination to diagonal form via matrices N_k.
-- This file proves the algebraic composition from explicitly supplied
-- second-stage contracts to the overall GJE residual and forward-error
-- bounds.  The local recurrence/second-stage bounds are exposed as abstract
-- interfaces rather than derived here from a concrete GJE loop.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.ForwardError
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination

namespace LeanFpAnalysis.FP

open Finset BigOperators

-- ══════════════════════════════════════════════════════════════════════
-- §14.4  GJE second-stage cumulative error constant
-- ══════════════════════════════════════════════════════════════════════

/-- **GJE second-stage cumulative error constant** (Higham §14.4).

    The accumulation of n−1 elimination steps, each introducing error γ₃
    with (1+γ₃) amplification per subsequent step, gives the cumulative
    bound (n−1)γ₃(1+γ₃)^{n−2}. -/
noncomputable def gje_c₃ (fp : FPModel) (n : ℕ) : ℝ :=
  ((n : ℝ) - 1) * gamma fp 3 * (1 + gamma fp 3) ^ (n - 2)

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.1  GJE Second Stage: Specification
-- ══════════════════════════════════════════════════════════════════════

/-- **GJE second-stage Nₖ matrix specification**.

    The second stage of GJE applies matrices N₂, N₃, …, Nₙ to reduce
    the upper triangular factor U to diagonal form.
    Each Nₖ has the form Nₖ = I − nₖeₖᵀ where nₖ has zeros
    in positions k through n (i.e., the entries below the diagonal). -/
structure GJEStage2Spec (n : ℕ) (U : Fin n → Fin n → ℝ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) : Prop where
  /-- Each N̂ₖ has the Nₖ-structure: N̂ₖ = I − n̂ₖeₖᵀ. -/
  N_form : ∀ k : Fin n, ∀ i j : Fin n,
    N_hat k i j = (if i = j then 1 else 0) -
      (if j = k then N_hat k i k else 0)
  /-- The diagonal of N̂ₖ at position k is 1 (since (Nₖ)ₖₖ = 1 − nₖₖ and
      nₖₖ = 0 for the second stage). -/
  diag_one : ∀ k : Fin n, N_hat k k k = 1
  /-- Entries at or below k in column k are zero (nₖᵢ = 0 for i ≥ k). -/
  lower_zero : ∀ k : Fin n, ∀ i : Fin n,
    i.val ≥ k.val → i ≠ k → N_hat k i k = 0

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.2  Error Recurrences (eqs. 14.25–14.26)
-- ══════════════════════════════════════════════════════════════════════

/-- **Abstract Eq. 14.25a interface**: matrix recurrence error bound for
    the GJE second stage.

    At each step k, the computed upper triangular factor satisfies:
      Û_{k+1} = N̂ₖÛₖ + Δₖ  with  |Δₖ| ≤ γ₃|N̂ₖ||Ûₖ|.

    The γ₃ constant arises because each element of N̂ₖÛₖ involves
    at most 3 arithmetic operations (multiply, add, subtract).  The hypothesis
    `hComp` supplies that local rounded-computation analysis. -/
theorem gje_stage2_matrix_recurrence (n : ℕ) (fp : FPModel)
    (U_k N_k U_next : Fin n → Fin n → ℝ)
    (_hn : gammaValid fp 3)
    -- N̂ₖÛₖ is computed with rounding errors bounded by γ₃
    (hComp : ∀ i j : Fin n,
      |U_next i j - ∑ l : Fin n, N_k i l * U_k l j| ≤
      gamma fp 3 * ∑ l : Fin n, |N_k i l| * |U_k l j|) :
    ∀ i j : Fin n,
      |U_next i j - ∑ l : Fin n, N_k i l * U_k l j| ≤
      gamma fp 3 * ∑ l : Fin n, |N_k i l| * |U_k l j| :=
  hComp

/-- **Abstract Eq. 14.26 interface**: RHS recurrence error bound for the
    GJE second stage.

    The computed right-hand side satisfies:
      x̂_{k+1} = N̂ₖx̂ₖ + fₖ  with  |fₖ| ≤ γ₃|N̂ₖ||x̂ₖ|.

    Same γ₃ constant as the matrix recurrence.  The hypothesis `hComp`
    supplies the local rounded-computation analysis. -/
theorem gje_stage2_rhs_recurrence (n : ℕ) (fp : FPModel)
    (x_k : Fin n → ℝ) (N_k : Fin n → Fin n → ℝ)
    (x_next : Fin n → ℝ)
    (_hn : gammaValid fp 3)
    (hComp : ∀ i : Fin n,
      |x_next i - ∑ l : Fin n, N_k i l * x_k l| ≤
      gamma fp 3 * ∑ l : Fin n, |N_k i l| * |x_k l|) :
    ∀ i : Fin n,
      |x_next i - ∑ l : Fin n, N_k i l * x_k l| ≤
      gamma fp 3 * ∑ l : Fin n, |N_k i l| * |x_k l| :=
  hComp

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.3  Cumulative Product (eqs. 14.27–14.28)
-- ══════════════════════════════════════════════════════════════════════

/-- **Cumulative product of N̂ matrices** for the GJE second stage.

    gje_cumulative_product n N̂ start finish = N̂_{finish-1} · ⋯ · N̂_{start},
    or I if finish ≤ start.

    This represents the product of N̂ₖ matrices applied in the second stage
    of Gauss–Jordan elimination. -/
noncomputable def gje_cumulative_product (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ)
    (start finish_ : ℕ) : Fin n → Fin n → ℝ :=
  if finish_ ≤ start then fun i j => if i = j then 1 else 0
  else if h : finish_ - 1 < n then
    let prev := gje_cumulative_product n N_hat start (finish_ - 1)
    fun i j => ∑ k : Fin n, N_hat ⟨finish_ - 1, h⟩ i k * prev k j
  else fun i j => if i = j then 1 else 0
termination_by finish_ - start

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.4  Forward Error (eq. 14.29)
-- ══════════════════════════════════════════════════════════════════════

/-- **Abstract Eq. 14.29 interface**: forward error bound for the GJE
    second stage.

    The componentwise forward error for the second stage satisfies:
      |x − x̂| ≤ (n−1)γ₃(1+γ₃)^{n−2} · |X̂| · (|U||x| + |y|)

    where X̂ = |N̂ₙ|···|N̂₂| is the absolute cumulative product of N̂ matrices
    and y is the first-stage output.  The hypothesis `hErr` supplies the
    second-stage accumulation proof. -/
theorem gje_stage2_forward_error_bound (n : ℕ) (fp : FPModel)
    (U : Fin n → Fin n → ℝ) (y x x_hat : Fin n → ℝ)
    (X_abs : Fin n → Fin n → ℝ)
    (_hn3 : gammaValid fp 3)
    -- U is upper triangular with nonzero diagonal
    (_hU_diag : ∀ i : Fin n, U i i ≠ 0)
    -- x is the exact solution of Ux = y
    (_hExact : ∀ i : Fin n, ∑ j : Fin n, U i j * x j = y i)
    -- x̂ is the GJE-computed solution with total second-stage error
    (hErr : ∀ i : Fin n,
      |x i - x_hat i| ≤
      gje_c₃ fp n *
        ∑ j : Fin n, |X_abs i j| * (∑ k : Fin n, |U j k| * |x k| + |y j|)) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      gje_c₃ fp n *
        ∑ j : Fin n, |X_abs i j| * (∑ k : Fin n, |U j k| * |x k| + |y j|) :=
  hErr

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.5  Backward Error (eq. 14.30)
-- ══════════════════════════════════════════════════════════════════════

/-- **Abstract Eq. 14.30 interface**: GJE second-stage backward error.

    The computed solution x̂ of Ux = y satisfies:
      (U + ΔU)x̂ = y + Δy
    with componentwise bounds (eqs. 14.30b–c):
      |ΔU| ≤ (n−1)γ₃(1+γ₃)^{n−2} · |X̂| · |U|
      |Δy| ≤ (n−1)γ₃(1+γ₃)^{n−2} · |X̂| · |y|

    where X̂ = |N̂ₙ|···|N̂₂| is the absolute cumulative product.  The
    existential hypothesis `hBackward` supplies the second-stage backward
    analysis used by the overall GJE theorem below. -/
theorem gje_stage2_backward_error (n : ℕ) (fp : FPModel)
    (U : Fin n → Fin n → ℝ) (y x_hat : Fin n → ℝ)
    (X_abs : Fin n → Fin n → ℝ)
    (_hn : gammaValid fp 3)
    (_hU_diag : ∀ i : Fin n, U i i ≠ 0)
    -- Backward error hypothesis: there exist ΔU, Δy such that
    -- (U + ΔU)x̂ = y + Δy with the stated bounds
    (hBackward : ∃ (ΔU : Fin n → Fin n → ℝ) (Δy : Fin n → ℝ),
      (∀ i : Fin n, ∑ j : Fin n, (U i j + ΔU i j) * x_hat j = y i + Δy i) ∧
      (∀ i j : Fin n, |ΔU i j| ≤
        gje_c₃ fp n * ∑ k : Fin n, |X_abs i k| * |U k j|) ∧
      (∀ i : Fin n, |Δy i| ≤
        gje_c₃ fp n * ∑ j : Fin n, |X_abs i j| * |y j|)) :
    ∃ (ΔU : Fin n → Fin n → ℝ) (Δy : Fin n → ℝ),
      (∀ i : Fin n, ∑ j : Fin n, (U i j + ΔU i j) * x_hat j = y i + Δy i) ∧
      (∀ i j : Fin n, |ΔU i j| ≤
        gje_c₃ fp n * ∑ k : Fin n, |X_abs i k| * |U k j|) ∧
      (∀ i : Fin n, |Δy i| ≤
        gje_c₃ fp n * ∑ j : Fin n, |X_abs i j| * |y j|) :=
  hBackward

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.6  Theorem 14.5: Overall GJE Error (eqs. 14.31–14.32)
-- ══════════════════════════════════════════════════════════════════════

/-- **Theorem 14.5, eq. 14.31**: Overall GJE residual bound.

    Combining the first-stage error (GE: A + ΔA = L̂Û with |ΔA| ≤ γₙ|L̂||Û|)
    with the second-stage backward error (eq. 14.30), the residual satisfies:
      |b − Ax̂| ≤ γₙ|L̂||Û||x̂| + c₃|L̂||X̂|(|Û||x̂| + |y|)

    where X̂ = |N̂ₙ|···|N̂₂| and c₃ = (n−1)γ₃(1+γ₃)^{n−2}.

    The proof decomposes b − Ax̂ = L̂(ΔU·x̂ − Δy) + (L̂Û − A)x̂
    using the first-stage equation L̂ŷ = b and the second-stage
    backward error (Û + ΔU)x̂ = ŷ + Δy. -/
theorem gje_overall_residual (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (X_abs : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (_hn : gammaValid fp n)
    (_hn3 : gammaValid fp 3)
    -- First-stage equation: L̂ŷ = b
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    -- Second-stage backward error: (Û + ΔU)x̂ = ŷ + Δy with bounds
    (ΔU : Fin n → Fin n → ℝ) (Δy : Fin n → ℝ)
    (hStage2_eq : ∀ i : Fin n,
      ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y i + Δy i)
    (hΔU_bound : ∀ i j : Fin n, |ΔU i j| ≤
      gje_c₃ fp n * ∑ k : Fin n, |X_abs i k| * |U_hat k j|)
    (hΔy_bound : ∀ i : Fin n, |Δy i| ≤
      gje_c₃ fp n * ∑ j : Fin n, |X_abs i j| * |y j|) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      -- First-stage contribution: |ΔA·x̂| ≤ γₙ|L̂||Û||x̂|
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
      -- Second-stage U-error: |L̂ΔU·x̂| via |X̂||Û|
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| +
      -- Second-stage y-error: |L̂Δy| via |X̂||y|
      gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |X_abs k j| * |y j|) := by
  intro i
  let T1 := gamma fp n * ∑ j : Fin n,
    (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j|
  let T2 := gje_c₃ fp n * ∑ j : Fin n,
    (∑ k₁ : Fin n, |L_hat i k₁| *
      (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
  let T3 := gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
    (∑ j : Fin n, |X_abs k j| * |y j|)
  -- From stage 2: y − Ûx̂ = ΔU·x̂ − Δy
  have hLUx : ∀ k : Fin n,
      y k - ∑ j : Fin n, U_hat k j * x_hat j =
      ∑ j : Fin n, ΔU k j * x_hat j - Δy k := by
    intro k
    have h := hStage2_eq k
    have : ∑ j : Fin n, (U_hat k j + ΔU k j) * x_hat j =
        ∑ j : Fin n, U_hat k j * x_hat j + ∑ j : Fin n, ΔU k j * x_hat j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    linarith
  have hLUerr := hLU.backward_bound
  -- Bound 1: |(L̂Û − A)x̂| ≤ T1
  have hB1 : |∑ j : Fin n, (∑ k : Fin n, L_hat i k * U_hat k j - A i j) *
      x_hat j| ≤ T1 := by
    calc _ ≤ ∑ j, |(∑ k, L_hat i k * U_hat k j - A i j) * x_hat j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |∑ k, L_hat i k * U_hat k j - A i j| * |x_hat j| := by
          apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
      _ ≤ ∑ j, (gamma fp n * ∑ k, |L_hat i k| * |U_hat k j|) * |x_hat j| := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_right (hLUerr i j) (abs_nonneg _)
      _ = T1 := by
          show _ = gamma fp n * _; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
  -- Bound 2: |L̂(ΔU·x̂ − Δy)| ≤ T2 + T3
  have hB2 : |∑ k : Fin n, L_hat i k *
      (∑ j : Fin n, ΔU k j * x_hat j - Δy k)| ≤ T2 + T3 := by
    calc _ ≤ ∑ k, |L_hat i k| * |∑ j, ΔU k j * x_hat j - Δy k| := by
          calc _ ≤ ∑ k, |L_hat i k * (∑ j, ΔU k j * x_hat j - Δy k)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k, |L_hat i k| * (∑ j, |ΔU k j| * |x_hat j| + |Δy k|) := by
          apply Finset.sum_le_sum; intro k _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc _ = |∑ j, ΔU k j * x_hat j + (-Δy k)| := by
                rw [sub_eq_add_neg]
            _ ≤ |∑ j, ΔU k j * x_hat j| + |(-Δy k)| := abs_add_le _ _
            _ = |∑ j, ΔU k j * x_hat j| + |Δy k| := by rw [abs_neg]
            _ ≤ (∑ j, |ΔU k j| * |x_hat j|) + |Δy k| := by
                linarith [show |∑ j, ΔU k j * x_hat j| ≤
                  ∑ j, |ΔU k j * x_hat j| from Finset.abs_sum_le_sum_abs _ _,
                  show ∑ j : Fin n, |ΔU k j * x_hat j| =
                    ∑ j, |ΔU k j| * |x_hat j| from
                    Finset.sum_congr rfl (fun j _ => abs_mul _ _)]
      _ ≤ ∑ k, |L_hat i k| *
          (∑ j, ((gje_c₃ fp n * ∑ k₂, |X_abs k k₂| * |U_hat k₂ j|) *
            |x_hat j|) + gje_c₃ fp n * ∑ j, |X_abs k j| * |y j|) := by
          apply Finset.sum_le_sum; intro k _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply add_le_add
          · apply Finset.sum_le_sum; intro j _
            exact mul_le_mul_of_nonneg_right (hΔU_bound k j) (abs_nonneg _)
          · exact hΔy_bound k
      _ = T2 + T3 := by
          -- Factor gje_c₃ from inner j-sum
          have h1 : ∀ k : Fin n,
              ∑ j : Fin n, (gje_c₃ fp n *
                ∑ k₂ : Fin n, |X_abs k k₂| * |U_hat k₂ j|) * |x_hat j| =
              gje_c₃ fp n *
                ∑ j : Fin n, (∑ k₂ : Fin n, |X_abs k k₂| * |U_hat k₂ j|) *
                  |x_hat j| := by
            intro k; rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j _; ring
          simp_rw [h1]
          -- Factor gje_c₃ out of each summand
          have h2 : ∀ k : Fin n,
              |L_hat i k| * (gje_c₃ fp n *
                ∑ j, (∑ k₂, |X_abs k k₂| * |U_hat k₂ j|) * |x_hat j| +
                gje_c₃ fp n * ∑ j, |X_abs k j| * |y j|) =
              gje_c₃ fp n * (|L_hat i k| *
                ∑ j, (∑ k₂, |X_abs k k₂| * |U_hat k₂ j|) * |x_hat j|) +
              gje_c₃ fp n * (|L_hat i k| * ∑ j, |X_abs k j| * |y j|) :=
            fun _ => by ring
          simp_rw [h2, Finset.sum_add_distrib, ← Finset.mul_sum]
          -- T2 needs Fubini; T3 matches directly
          congr 1
          · congr 1
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _
            simp_rw [show ∀ k : Fin n,
                |L_hat i k| * ((∑ k₂, |X_abs k k₂| * |U_hat k₂ j|) * |x_hat j|) =
                (|L_hat i k| * (∑ k₂, |X_abs k k₂| * |U_hat k₂ j|)) * |x_hat j|
              from fun _ => by ring]
            rw [← Finset.sum_mul]; congr 1
            simp_rw [Finset.mul_sum]
  -- Combine: |b − Ax̂| = |L̂(ΔU·x̂ − Δy) + (L̂Û − A)x̂| ≤ T1 + T2 + T3
  -- Algebraic decomposition
  suffices h : b i - ∑ j, A i j * x_hat j =
      ∑ k, L_hat i k * (∑ j, ΔU k j * x_hat j - Δy k) +
      ∑ j, (∑ k, L_hat i k * U_hat k j - A i j) * x_hat j by
    rw [h]
    have htri := abs_add_le
      (∑ k, L_hat i k * (∑ j, ΔU k j * x_hat j - Δy k))
      (∑ j, (∑ k, L_hat i k * U_hat k j - A i j) * x_hat j)
    linarith
  -- Prove the decomposition
  have hb : b i = ∑ k : Fin n, L_hat i k * y k := (hy i).symm
  have hyk : ∀ k : Fin n, L_hat i k * y k =
      L_hat i k * (∑ j : Fin n, U_hat k j * x_hat j) +
      L_hat i k * (∑ j : Fin n, ΔU k j * x_hat j - Δy k) := by
    intro k; rw [← mul_add]; congr 1; linarith [hLUx k]
  rw [hb]; simp_rw [hyk]; rw [Finset.sum_add_distrib]
  -- Fubini on ∑_k L̂_{ik} · ∑_j Û_{kj}x̂_j
  have hFubini : ∑ k : Fin n, L_hat i k * (∑ j : Fin n, U_hat k j * x_hat j) =
      ∑ j : Fin n, (∑ k : Fin n, L_hat i k * U_hat k j) * x_hat j := by
    simp_rw [Finset.mul_sum, ← mul_assoc]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_mul]
  linarith [show ∑ j : Fin n, (∑ k : Fin n, L_hat i k * U_hat k j) * x_hat j -
      ∑ j : Fin n, A i j * x_hat j =
      ∑ j : Fin n, (∑ k : Fin n, L_hat i k * U_hat k j - A i j) * x_hat j from by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring]

/-- **Theorem 14.5, eq. 14.32**: Overall GJE forward error.

    The forward error satisfies:
      |x − x̂| ≤ |A⁻¹| · |b − Ax̂|.

    Combined with the residual bound (eq. 14.31), this gives:
      |x − x̂| ≤ |A⁻¹| · (γₙ|L̂||Û||x̂| + c₃|L̂||X̂|(|Û||x̂| + |y|)). -/
theorem gje_overall_forward_error (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (X_abs : Fin n → Fin n → ℝ)
    (_hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (_hn : gammaValid fp n)
    (_hn3 : gammaValid fp 3)
    -- Exact solution
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    -- Residual bound from gje_overall_residual
    (hResidual : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |X_abs k j| * |y j|)) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ k|)) * |x_hat k| +
        gje_c₃ fp n * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n, |X_abs l k| * |y k|)) := by
  intro i
  -- x − x̂ = A⁻¹(b − Ax̂) since Ax = b
  have hDiff : x i - x_hat i =
      ∑ j : Fin n, A_inv i j *
        (b j - ∑ k : Fin n, A j k * x_hat k) := by
    have hRHS_expand : ∑ j : Fin n, A_inv i j *
        (b j - ∑ k : Fin n, A j k * x_hat k) =
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x k) -
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x_hat k) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [hExact j]; ring
    rw [hRHS_expand]
    -- ∑_j A⁻¹(i,j) · ∑_k A(j,k) · x(k) = x(i) using hAinv
    have hFirst : ∑ j : Fin n, A_inv i j *
        (∑ k : Fin n, A j k * x k) = x i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hSecond : ∑ j : Fin n, A_inv i j *
        (∑ k : Fin n, A j k * x_hat k) = x_hat i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    linarith
  rw [hDiff]
  -- |∑ A⁻¹ · r| ≤ ∑ |A⁻¹| · |r| ≤ ∑ |A⁻¹| · (bound)
  calc |∑ j : Fin n, A_inv i j *
        (b j - ∑ k : Fin n, A j k * x_hat k)|
      ≤ ∑ j : Fin n, |A_inv i j| *
        |b j - ∑ k : Fin n, A j k * x_hat k| := by
        calc _ ≤ ∑ j, |A_inv i j * (b j - ∑ k, A j k * x_hat k)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = _ := by apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        (gje_c₃ fp n) * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ k|)) * |x_hat k| +
        (gje_c₃ fp n) * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n, |X_abs l k| * |y k|)) := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (hResidual j) (abs_nonneg _)

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.7  Corollary 14.6: SPD Specialization
-- ══════════════════════════════════════════════════════════════════════

/-- **Abstract Corollary 14.6 interface** (Higham p. 277): GJE for SPD matrices.

    For SPD A with Cholesky factorization A + ΔA = R̂ᵀR̂, the GJE
    residual simplifies because L̂ = R̂ᵀ, Û = R̂, and the cumulative
    product X̂ = |N̂ₙ···N̂₂| is bounded by |R̂⁻¹|.

    The componentwise residual specializes to:
      |b − Ax̂| ≤ γₙ|R̂ᵀ||R̂||x̂| + c₃|R̂ᵀ||R̂⁻¹|(|R̂||x̂| + |y|)

    which gives the normwise bound (Higham eq. 14.33):
      ‖b − Ax̂‖ / (‖A‖ · ‖x̂‖) ≤ 8n³u κ(A)^{1/2} + O(u²).

    The specialized residual is supplied as `hResidual`; the general
    composition theorem `gje_overall_residual` above is fully proved from its
    stated first- and second-stage hypotheses. -/
theorem gje_spd_residual (n : ℕ) (fp : FPModel)
    (A R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (_hSPD : IsSymPosDef n A)
    (_hn : gammaValid fp n)
    (_hn3 : gammaValid fp 3)
    -- Cholesky: A + ΔA = R̂ᵀR̂ (L̂ = R̂ᵀ, Û = R̂)
    (_hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    -- The overall residual bound specializing Theorem 14.5
    -- with L̂ = R̂ᵀ, Û = R̂, X_abs = |R̂⁻¹|
    (hResidual : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |R_hat k₁ i| *
          (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |R_hat k i| *
        (∑ j : Fin n, |R_inv k j| * |y j|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |R_hat k₁ i| *
          (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |R_hat k i| *
        (∑ j : Fin n, |R_inv k j| * |y j|) :=
  hResidual

end LeanFpAnalysis.FP
