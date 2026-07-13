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

/-- Higham, 2nd ed., Chapter 14, Theorem 14.5 support:
    specialize the generic `gamma` first-order split to the `gamma_3`
    correction term used by the GJE second-stage constant. -/
theorem gamma_three_sub_linear_eq_quadratic_remainder
    (fp : FPModel) (h3 : gammaValid fp 3) :
    gamma fp 3 - 3 * fp.u =
      (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) := by
  rw [gamma_eq_linear_plus_quadratic_remainder fp 3 h3]
  ring

/-- Higham, 2nd ed., Chapter 14, Theorem 14.5 support:
    exact scalar split of the GJE cumulative coefficient into the displayed
    first-order term `3 (n - 1) u` plus explicit higher-order factors. -/
theorem gje_c3_eq_linear_plus_explicit_remainder
    (fp : FPModel) (n : ℕ) :
    gje_c₃ fp n =
      3 * ((n : ℝ) - 1) * fp.u +
        ((n : ℝ) - 1) *
          ((gamma fp 3 - 3 * fp.u) * (1 + gamma fp 3) ^ (n - 2) +
            3 * fp.u * ((1 + gamma fp 3) ^ (n - 2) - 1)) := by
  unfold gje_c₃
  ring

/-- Higham, 2nd ed., Chapter 14, Theorem 14.5 support:
    the preceding split with the `gamma_3 - 3u` term expanded using the
    standard quadratic-and-higher `gamma` remainder. -/
theorem gje_c3_eq_linear_plus_quadratic_remainder
    (fp : FPModel) (n : ℕ) (h3 : gammaValid fp 3) :
    gje_c₃ fp n =
      3 * ((n : ℝ) - 1) * fp.u +
        ((n : ℝ) - 1) *
          (((((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u)) *
              (1 + gamma fp 3) ^ (n - 2) +
            3 * fp.u * ((1 + gamma fp 3) ^ (n - 2) - 1)) := by
  rw [gje_c3_eq_linear_plus_explicit_remainder,
    gamma_three_sub_linear_eq_quadratic_remainder fp h3]

/-- Explicit higher-order term in the Chapter 14 first-order split of
    the GJE cumulative coefficient. -/
noncomputable def gje_c3_quadratic_remainder (fp : FPModel) (n : ℕ) : ℝ :=
  ((n : ℝ) - 1) *
    (((((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u)) *
        (1 + gamma fp 3) ^ (n - 2) +
      3 * fp.u * ((1 + gamma fp 3) ^ (n - 2) - 1))

/-- Named form of the `gje_c₃` first-order split, using
    `gje_c3_quadratic_remainder` for the higher-order contribution. -/
theorem gje_c3_eq_linear_plus_quadratic_remainder_term
    (fp : FPModel) (n : ℕ) (h3 : gammaValid fp 3) :
    gje_c₃ fp n =
      3 * ((n : ℝ) - 1) * fp.u + gje_c3_quadratic_remainder fp n := by
  simpa [gje_c3_quadratic_remainder] using
    gje_c3_eq_linear_plus_quadratic_remainder fp n h3

/-- Elementary scalar growth bound used to connect the exact constant
    product envelope `(1 + c)^steps - 1` to Higham's `c₃`-style coefficient. -/
theorem gje_one_add_pow_sub_one_le_nat_mul_pred {c : ℝ} (hc : 0 ≤ c) :
    ∀ steps : ℕ,
      (1 + c) ^ steps - 1 ≤ (steps : ℝ) * c * (1 + c) ^ (steps - 1) := by
  intro steps
  induction steps with
  | zero =>
      simp
  | succ k ih =>
      cases k with
      | zero =>
          ring_nf
          exact le_rfl
      | succ m =>
          have hbase_nonneg : 0 ≤ 1 + c := by linarith
          have hbase_one : (1 : ℝ) ≤ 1 + c := by linarith
          have hpow_ge_one : (1 : ℝ) ≤ (1 + c) ^ (m + 1) :=
            one_le_pow₀ hbase_one
          have hmul := mul_le_mul_of_nonneg_right ih hbase_nonneg
          have hc_le : c ≤ c * (1 + c) ^ (m + 1) := by
            calc
              c = c * 1 := by ring
              _ ≤ c * (1 + c) ^ (m + 1) :=
                mul_le_mul_of_nonneg_left hpow_ge_one hc
          calc
            (1 + c) ^ (Nat.succ (Nat.succ m)) - 1 =
                (1 + c) ^ (m + 1) * (1 + c) - 1 := by
              rw [show Nat.succ (Nat.succ m) = (m + 1) + 1 by omega, pow_succ]
            _ = ((1 + c) ^ (m + 1) - 1) * (1 + c) + c := by
              ring
            _ ≤ ((m + 1 : ℕ) : ℝ) * c * (1 + c) ^ ((m + 1) - 1) *
                  (1 + c) + c := by
              exact add_le_add hmul (le_refl c)
            _ = ((m + 1 : ℕ) : ℝ) * c * ((1 + c) ^ m * (1 + c)) + c := by
              rw [show (m + 1 : ℕ) - 1 = m by omega]
              ring
            _ = ((m + 1 : ℕ) : ℝ) * c * (1 + c) ^ (m + 1) + c := by
              rw [pow_succ]
            _ ≤ ((m + 1 : ℕ) : ℝ) * c * (1 + c) ^ (m + 1) +
                  c * (1 + c) ^ (m + 1) := by
              exact add_le_add (le_refl _) hc_le
            _ = ((Nat.succ (Nat.succ m) : ℕ) : ℝ) * c *
                  (1 + c) ^ (Nat.succ (Nat.succ m) - 1) := by
              rw [show Nat.succ (Nat.succ m) - 1 = m + 1 by omega]
              norm_num [Nat.cast_add, Nat.cast_one]
              ring

/-- Chapter 14 scalar bridge: the constant GJE product envelope with
    `eta = gamma fp 3` is bounded by the file's `gje_c₃ fp n` coefficient. -/
theorem gje_one_add_gamma_three_pow_sub_one_le_c3 (fp : FPModel) (n : ℕ)
    (hn : 1 ≤ n) (hvalid : gammaValid fp 3) :
    (1 + gamma fp 3) ^ (n - 1) - 1 ≤ gje_c₃ fp n := by
  have hgamma : 0 ≤ gamma fp 3 := gamma_nonneg fp hvalid
  have h := gje_one_add_pow_sub_one_le_nat_mul_pred hgamma (n - 1)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hexp : (n - 1) - 1 = n - 2 := by omega
  simpa [gje_c₃, hcast, hexp] using h

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

/-- Equation (14.27) base case for the GJE cumulative product:
    an empty stage range is the identity. -/
theorem gje_cumulative_product_base (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) {start finish_ : ℕ}
    (hfinish : finish_ ≤ start) :
    gje_cumulative_product n N_hat start finish_ = idMatrix n := by
  conv_lhs => unfold gje_cumulative_product
  ext i j
  simp [hfinish, idMatrix]

/-- Equation (14.27) step case for the GJE cumulative product:
    when the stage index `finish - 1` is valid, the product is obtained by
    multiplying that stage on the left of the previous cumulative product. -/
theorem gje_cumulative_product_step (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) {start finish_ : ℕ}
    (hstep : start < finish_) (hidx : finish_ - 1 < n) :
    gje_cumulative_product n N_hat start finish_ =
      matMul n (N_hat ⟨finish_ - 1, hidx⟩)
        (gje_cumulative_product n N_hat start (finish_ - 1)) := by
  conv_lhs => unfold gje_cumulative_product
  ext i j
  simp [not_le_of_gt hstep, hidx, matMul]

/-- Out-of-range guard for the cumulative product: if the requested stage
    `finish - 1` is not a valid `Fin n` index, the definition returns the
    identity.  This keeps the total function honest outside the source range. -/
theorem gje_cumulative_product_oob (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) {start finish_ : ℕ}
    (hstep : start < finish_) (hidx : ¬ finish_ - 1 < n) :
    gje_cumulative_product n N_hat start finish_ = idMatrix n := by
  conv_lhs => unfold gje_cumulative_product
  ext i j
  simp [not_le_of_gt hstep, hidx, idMatrix]

/-- Entrywise nonnegative stage matrices have entrywise nonnegative GJE
    cumulative products.  This is the basic monotonicity fact needed before
    turning (14.27)--(14.28) into componentwise absolute-value bounds. -/
theorem gje_cumulative_product_nonneg (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ)
    (hN : ∀ k i j : Fin n, 0 ≤ N_hat k i j) :
    ∀ start finish_ : ℕ, ∀ i j : Fin n,
      0 ≤ gje_cumulative_product n N_hat start finish_ i j := by
  intro start finish_
  induction finish_ using Nat.strong_induction_on generalizing start with
  | h finish_ ih =>
      intro i j
      by_cases hfinish : finish_ ≤ start
      · rw [gje_cumulative_product_base n N_hat hfinish]
        simp [idMatrix]
        split <;> norm_num
      · by_cases hidx : finish_ - 1 < n
        · have hstep : start < finish_ := lt_of_not_ge hfinish
          have hfinish_ne : finish_ ≠ 0 :=
            Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le start) hstep)
          rw [gje_cumulative_product_step n N_hat hstep hidx]
          simp [matMul]
          exact Finset.sum_nonneg fun k _ =>
            mul_nonneg (hN ⟨finish_ - 1, hidx⟩ i k)
              (ih (finish_ - 1) (Nat.sub_one_lt hfinish_ne) start k j)
        · have hstep : start < finish_ := lt_of_not_ge hfinish
          rw [gje_cumulative_product_oob n N_hat hstep hidx]
          simp [idMatrix]
          split <;> norm_num

/-- The absolute-value stage matrices used in the GJE error bounds have
    nonnegative cumulative products. -/
theorem gje_cumulative_product_abs_nonneg (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) :
    ∀ start finish_ : ℕ, ∀ i j : Fin n,
      0 ≤ gje_cumulative_product n
        (fun k i j => |N_hat k i j|) start finish_ i j :=
  gje_cumulative_product_nonneg n
    (fun k i j => |N_hat k i j|)
    (fun _ _ _ => abs_nonneg _)

/-- The GJE cumulative product over a valid `steps`-long range is the generic
    matrix sequence product of the same stages in reverse order.  This bridge
    lets the generic product-perturbation lemmas in `MatrixAlgebra` feed the
    source-shaped GJE cumulative product used in (14.27)--(14.30). -/
theorem gje_cumulative_product_eq_matSeqProd_rev (n : Nat)
    (N_hat : Fin n -> Fin n -> Fin n -> Real)
    (start steps : Nat)
    (hidx : forall r : Fin steps, start + (steps - 1 - r.val) < n) :
    gje_cumulative_product n N_hat start (start + steps) =
      matSeqProd n steps (fun r : Fin steps =>
        let k : Fin n := Fin.mk (start + (steps - 1 - r.val)) (hidx r);
        N_hat k) := by
  induction steps with
  | zero =>
      rw [Nat.add_zero]
      rw [gje_cumulative_product_base n N_hat (le_refl start)]
      simp [matSeqProd]
  | succ m ih =>
      have htop : start + m < n := by
        simpa using hidx 0
      have hstep : start < start + (m + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos m)
      have hfinish_idx : start + (m + 1) - 1 < n := by
        simpa [Nat.add_assoc] using htop
      have hprev_idx : forall r : Fin m, start + (m - 1 - r.val) < n := by
        intro r
        have hr := hidx r.succ
        have heq : m - (r.val + 1) = m - 1 - r.val := by
          rw [Nat.sub_sub, Nat.add_comm]
        simpa [Nat.succ_eq_add_one, heq] using hr
      have hfin : (Fin.mk (start + (m + 1) - 1) hfinish_idx : Fin n) =
          Fin.mk (start + m) htop := by
        apply Fin.ext
        simp
      have hcp_prev :
          gje_cumulative_product n N_hat start (start + (m + 1) - 1) =
            gje_cumulative_product n N_hat start (start + m) := by
        simp
      rw [gje_cumulative_product_step n N_hat hstep hfinish_idx]
      rw [hfin, hcp_prev]
      rw [ih hprev_idx]
      simp [matSeqProd, Nat.sub_sub, Nat.add_comm]

/-- Componentwise perturbation bound for GJE cumulative products, obtained by
    transporting the generic `matSeqProd_componentwise_perturbation_bound`
    through `gje_cumulative_product_eq_matSeqProd_rev`. -/
theorem gje_cumulative_product_componentwise_perturbation_bound (n : Nat)
    (N_hat DeltaN : Fin n -> Fin n -> Fin n -> Real)
    (start steps : Nat) (delta : Fin steps -> Real)
    (hidx : forall r : Fin steps, start + (steps - 1 - r.val) < n)
    (hdelta : forall r : Fin steps, 0 <= delta r)
    (hDelta : forall r : Fin steps, forall i j : Fin n,
      |DeltaN (Fin.mk (start + (steps - 1 - r.val)) (hidx r)) i j| <=
        delta r * |N_hat (Fin.mk (start + (steps - 1 - r.val)) (hidx r)) i j|)
    (i j : Fin n) :
    |gje_cumulative_product n (fun k i j => N_hat k i j + DeltaN k i j)
        start (start + steps) i j -
      gje_cumulative_product n N_hat start (start + steps) i j| <=
      ((scalarSeqProd steps fun r => 1 + delta r) - 1) *
        gje_cumulative_product n (fun k i j => |N_hat k i j|)
          start (start + steps) i j := by
  let X : Fin steps -> Fin n -> Fin n -> Real := fun r =>
    N_hat (Fin.mk (start + (steps - 1 - r.val)) (hidx r))
  let DX : Fin steps -> Fin n -> Fin n -> Real := fun r =>
    DeltaN (Fin.mk (start + (steps - 1 - r.val)) (hidx r))
  have hDelta' : forall r : Fin steps, forall i j : Fin n,
      |DX r i j| <= delta r * |X r i j| := by
    intro r i j
    simpa [X, DX] using hDelta r i j
  have hbound :=
    matSeqProd_componentwise_perturbation_bound n steps X DX delta
      hdelta hDelta' i j
  have hpert := gje_cumulative_product_eq_matSeqProd_rev n
    (fun k i j => N_hat k i j + DeltaN k i j) start steps hidx
  have hbase := gje_cumulative_product_eq_matSeqProd_rev n N_hat start steps hidx
  have habs := gje_cumulative_product_eq_matSeqProd_rev n
    (fun k i j => |N_hat k i j|) start steps hidx
  rw [hpert, hbase, habs]
  simpa [X, DX, absMatrix] using hbound

/-- Constant per-stage scalar product for the GJE product-error envelope. -/
theorem gje_scalarSeqProd_const (steps : Nat) (eta : Real) :
    scalarSeqProd steps (fun _ : Fin steps => 1 + eta) =
      (1 + eta) ^ steps := by
  induction steps with
  | zero =>
      simp [scalarSeqProd]
  | succ m ih =>
      simp [scalarSeqProd, ih, pow_succ, mul_comm]

/-- Constant-error specialization of
    `gje_cumulative_product_componentwise_perturbation_bound`, with the
    scalar envelope in the source-shaped form `(1 + eta)^steps - 1`. -/
theorem gje_cumulative_product_componentwise_perturbation_bound_const (n : Nat)
    (N_hat DeltaN : Fin n -> Fin n -> Fin n -> Real)
    (start steps : Nat) (eta : Real)
    (hidx : forall r : Fin steps, start + (steps - 1 - r.val) < n)
    (heta : 0 <= eta)
    (hDelta : forall r : Fin steps, forall i j : Fin n,
      |DeltaN (Fin.mk (start + (steps - 1 - r.val)) (hidx r)) i j| <=
        eta * |N_hat (Fin.mk (start + (steps - 1 - r.val)) (hidx r)) i j|)
    (i j : Fin n) :
    |gje_cumulative_product n (fun k i j => N_hat k i j + DeltaN k i j)
        start (start + steps) i j -
      gje_cumulative_product n N_hat start (start + steps) i j| <=
      ((1 + eta) ^ steps - 1) *
        gje_cumulative_product n (fun k i j => |N_hat k i j|)
          start (start + steps) i j := by
  have h := gje_cumulative_product_componentwise_perturbation_bound n
    N_hat DeltaN start steps (fun _ : Fin steps => eta) hidx
    (fun _ => heta) hDelta i j
  simpa [gje_scalarSeqProd_const] using h

/-- Source-shaped constant-error GJE product perturbation bound with the
    accumulated scalar envelope absorbed into `gje_c₃ fp n`. -/
theorem gje_cumulative_product_componentwise_perturbation_bound_gamma_c3
    (n : Nat) (fp : FPModel)
    (N_hat DeltaN : Fin n -> Fin n -> Fin n -> Real)
    (start : Nat)
    (hn : 1 <= n) (hvalid : gammaValid fp 3)
    (hidx : forall r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : forall r : Fin (n - 1), forall i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| <=
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (i j : Fin n) :
    |gje_cumulative_product n (fun k i j => N_hat k i j + DeltaN k i j)
        start (start + (n - 1)) i j -
      gje_cumulative_product n N_hat start (start + (n - 1)) i j| <=
      gje_c₃ fp n *
        gje_cumulative_product n (fun k i j => |N_hat k i j|)
          start (start + (n - 1)) i j := by
  have hconst :=
    gje_cumulative_product_componentwise_perturbation_bound_const n
      N_hat DeltaN start (n - 1) (gamma fp 3) hidx
      (gamma_nonneg fp hvalid) hDelta i j
  have hscalar := gje_one_add_gamma_three_pow_sub_one_le_c3 fp n hn hvalid
  have hprod_nonneg :
      0 <= gje_cumulative_product n (fun k i j => |N_hat k i j|)
        start (start + (n - 1)) i j :=
    gje_cumulative_product_abs_nonneg n N_hat start (start + (n - 1)) i j
  exact le_trans hconst (mul_le_mul_of_nonneg_right hscalar hprod_nonneg)

/-- Vector-applied form of the Chapter 14 GJE cumulative-product perturbation
    bound.  This is the matrix-vector bridge needed by the right-hand-side
    accumulation in the route to equation (14.29): the existing entrywise
    product perturbation theorem is pushed through multiplication by a fixed
    right-hand side. -/
theorem gje_cumulative_product_matMulVec_componentwise_perturbation_bound_gamma_c3
    (n : Nat) (fp : FPModel)
    (N_hat DeltaN : Fin n -> Fin n -> Fin n -> Real)
    (start : Nat) (rhs : Fin n -> Real)
    (hn : 1 <= n) (hvalid : gammaValid fp 3)
    (hidx : forall r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : forall r : Fin (n - 1), forall i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| <=
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (i : Fin n) :
    |matMulVec n
        (gje_cumulative_product n (fun k a b => N_hat k a b + DeltaN k a b)
          start (start + (n - 1))) rhs i -
      matMulVec n
        (gje_cumulative_product n N_hat start (start + (n - 1))) rhs i| <=
      gje_c₃ fp n *
        ∑ j : Fin n,
          gje_cumulative_product n (fun k a b => |N_hat k a b|)
            start (start + (n - 1)) i j * |rhs j| := by
  let Pδ : Fin n -> Fin n -> Real :=
    gje_cumulative_product n (fun k a b => N_hat k a b + DeltaN k a b)
      start (start + (n - 1))
  let P : Fin n -> Fin n -> Real :=
    gje_cumulative_product n N_hat start (start + (n - 1))
  let Pabs : Fin n -> Fin n -> Real :=
    gje_cumulative_product n (fun k a b => |N_hat k a b|)
      start (start + (n - 1))
  have hentry : forall j : Fin n,
      |Pδ i j - P i j| <= gje_c₃ fp n * Pabs i j := by
    intro j
    simpa [Pδ, P, Pabs] using
      gje_cumulative_product_componentwise_perturbation_bound_gamma_c3
        n fp N_hat DeltaN start hn hvalid hidx hDelta i j
  change |matMulVec n Pδ rhs i - matMulVec n P rhs i| <=
    gje_c₃ fp n * ∑ j : Fin n, Pabs i j * |rhs j|
  change |(∑ j : Fin n, Pδ i j * rhs j) -
      (∑ j : Fin n, P i j * rhs j)| <=
    gje_c₃ fp n * ∑ j : Fin n, Pabs i j * |rhs j|
  have hdiff :
      (∑ j : Fin n, Pδ i j * rhs j) -
          (∑ j : Fin n, P i j * rhs j) =
        ∑ j : Fin n, (Pδ i j - P i j) * rhs j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdiff]
  calc
    |∑ j : Fin n, (Pδ i j - P i j) * rhs j|
        <= ∑ j : Fin n, |(Pδ i j - P i j) * rhs j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |Pδ i j - P i j| * |rhs j| := by
          apply Finset.sum_congr rfl
          intro j _
          exact abs_mul _ _
    _ <= ∑ j : Fin n, (gje_c₃ fp n * Pabs i j) * |rhs j| := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hentry j) (abs_nonneg _)
    _ = gje_c₃ fp n * ∑ j : Fin n, Pabs i j * |rhs j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- Matrix-applied form of the Chapter 14 GJE cumulative-product perturbation
    bound.  This is the fixed-right-matrix bridge needed by the matrix side of
    equation (14.30): the entrywise product perturbation theorem is pushed
    through multiplication by the current upper-triangular factor. -/
theorem gje_cumulative_product_matMul_componentwise_perturbation_bound_gamma_c3
    (n : Nat) (fp : FPModel)
    (N_hat DeltaN : Fin n -> Fin n -> Fin n -> Real)
    (start : Nat) (rhs : Fin n -> Fin n -> Real)
    (hn : 1 <= n) (hvalid : gammaValid fp 3)
    (hidx : forall r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : forall r : Fin (n - 1), forall i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| <=
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (i j : Fin n) :
    |matMul n
        (gje_cumulative_product n (fun k a b => N_hat k a b + DeltaN k a b)
          start (start + (n - 1))) rhs i j -
      matMul n
        (gje_cumulative_product n N_hat start (start + (n - 1))) rhs i j| <=
      gje_c₃ fp n *
        ∑ k : Fin n,
          gje_cumulative_product n (fun s a b => |N_hat s a b|)
            start (start + (n - 1)) i k * |rhs k j| := by
  let Pdelta : Fin n -> Fin n -> Real :=
    gje_cumulative_product n (fun k a b => N_hat k a b + DeltaN k a b)
      start (start + (n - 1))
  let P : Fin n -> Fin n -> Real :=
    gje_cumulative_product n N_hat start (start + (n - 1))
  let Pabs : Fin n -> Fin n -> Real :=
    gje_cumulative_product n (fun k a b => |N_hat k a b|)
      start (start + (n - 1))
  have hentry : forall k : Fin n,
      |Pdelta i k - P i k| <= gje_c₃ fp n * Pabs i k := by
    intro k
    simpa [Pdelta, P, Pabs] using
      gje_cumulative_product_componentwise_perturbation_bound_gamma_c3
        n fp N_hat DeltaN start hn hvalid hidx hDelta i k
  change |matMul n Pdelta rhs i j - matMul n P rhs i j| <=
    gje_c₃ fp n * ∑ k : Fin n, Pabs i k * |rhs k j|
  change |(∑ k : Fin n, Pdelta i k * rhs k j) -
      (∑ k : Fin n, P i k * rhs k j)| <=
    gje_c₃ fp n * ∑ k : Fin n, Pabs i k * |rhs k j|
  have hdiff :
      (∑ k : Fin n, Pdelta i k * rhs k j) -
          (∑ k : Fin n, P i k * rhs k j) =
        ∑ k : Fin n, (Pdelta i k - P i k) * rhs k j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hdiff]
  calc
    |∑ k : Fin n, (Pdelta i k - P i k) * rhs k j|
        <= ∑ k : Fin n, |(Pdelta i k - P i k) * rhs k j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |Pdelta i k - P i k| * |rhs k j| := by
          apply Finset.sum_congr rfl
          intro k _
          exact abs_mul _ _
    _ <= ∑ k : Fin n, (gje_c₃ fp n * Pabs i k) * |rhs k j| := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_right (hentry k) (abs_nonneg _)
    _ = gje_c₃ fp n * ∑ k : Fin n, Pabs i k * |rhs k j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring

/-- Equation (14.27) accumulation algebra for the GJE second-stage matrix
    recurrence.  If the exact stage matrices obey
    `U_{start+t+1} = N_{start+t} U_{start+t}` for `steps` valid stages, then
    the last stage is the cumulative product times the initial stage. -/
theorem gje_cumulative_product_matrix_accumulation (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ)
    (U_stage : ℕ → Fin n → Fin n → ℝ)
    (start steps : ℕ)
    (hidx : ∀ t : ℕ, t < steps → start + t < n)
    (hrec : ∀ t : ℕ, (ht : t < steps) →
      U_stage (start + (t + 1)) =
        matMul n (N_hat ⟨start + t, hidx t ht⟩) (U_stage (start + t))) :
    U_stage (start + steps) =
      matMul n (gje_cumulative_product n N_hat start (start + steps))
        (U_stage start) := by
  induction steps with
  | zero =>
      simp
      rw [gje_cumulative_product_base n N_hat (le_refl start), matMul_id_left]
  | succ steps ih =>
      have hidx_prev : ∀ t : ℕ, t < steps → start + t < n := by
        intro t ht
        exact hidx t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have hrec_prev : ∀ t : ℕ, (ht : t < steps) →
          U_stage (start + (t + 1)) =
            matMul n (N_hat ⟨start + t, hidx_prev t ht⟩)
              (U_stage (start + t)) := by
        intro t ht
        simpa [hidx_prev] using hrec t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have ih' := ih hidx_prev hrec_prev
      have hstage := hrec steps (Nat.lt_succ_self steps)
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfinish_eq : start + (steps + 1) - 1 = start + steps := by
        simp
      have hfinish_idx : start + (steps + 1) - 1 < n := by
        simpa [hfinish_eq] using hidx steps (Nat.lt_succ_self steps)
      have hfin : (⟨start + (steps + 1) - 1, hfinish_idx⟩ : Fin n) =
          ⟨start + steps, hidx steps (Nat.lt_succ_self steps)⟩ := by
        apply Fin.ext
        simp
      have hcp_prev :
          gje_cumulative_product n N_hat start (start + (steps + 1) - 1) =
            gje_cumulative_product n N_hat start (start + steps) := by
        rw [hfinish_eq]
      have hcp := gje_cumulative_product_step n N_hat hstep hfinish_idx
      rw [hstage, ih', hcp, hfin, hcp_prev, matMul_assoc]

/-- Equation (14.28) accumulation algebra for the GJE second-stage right-hand
    side recurrence.  If the exact stage vectors obey
    `x_{start+t+1} = N_{start+t} x_{start+t}` for `steps` valid stages, then
    the last vector is the cumulative product applied to the initial vector. -/
theorem gje_cumulative_product_rhs_accumulation (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ)
    (x_stage : ℕ → Fin n → ℝ)
    (start steps : ℕ)
    (hidx : ∀ t : ℕ, t < steps → start + t < n)
    (hrec : ∀ t : ℕ, (ht : t < steps) →
      x_stage (start + (t + 1)) =
        matMulVec n (N_hat ⟨start + t, hidx t ht⟩) (x_stage (start + t))) :
    x_stage (start + steps) =
      matMulVec n (gje_cumulative_product n N_hat start (start + steps))
        (x_stage start) := by
  induction steps with
  | zero =>
      simp
      rw [gje_cumulative_product_base n N_hat (le_refl start), matMulVec_id]
  | succ steps ih =>
      have hidx_prev : ∀ t : ℕ, t < steps → start + t < n := by
        intro t ht
        exact hidx t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have hrec_prev : ∀ t : ℕ, (ht : t < steps) →
          x_stage (start + (t + 1)) =
            matMulVec n (N_hat ⟨start + t, hidx_prev t ht⟩)
              (x_stage (start + t)) := by
        intro t ht
        simpa [hidx_prev] using hrec t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have ih' := ih hidx_prev hrec_prev
      have hstage := hrec steps (Nat.lt_succ_self steps)
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfinish_eq : start + (steps + 1) - 1 = start + steps := by
        simp
      have hfinish_idx : start + (steps + 1) - 1 < n := by
        simpa [hfinish_eq] using hidx steps (Nat.lt_succ_self steps)
      have hfin : (⟨start + (steps + 1) - 1, hfinish_idx⟩ : Fin n) =
          ⟨start + steps, hidx steps (Nat.lt_succ_self steps)⟩ := by
        apply Fin.ext
        simp
      have hcp_prev :
          gje_cumulative_product n N_hat start (start + (steps + 1) - 1) =
            gje_cumulative_product n N_hat start (start + steps) := by
        rw [hfinish_eq]
      have hcp := gje_cumulative_product_step n N_hat hstep hfinish_idx
      rw [hstage, ih', hcp, hfin, hcp_prev]
      ext i
      exact (matMulVec_matMul n
        (N_hat ⟨start + steps, hidx steps (Nat.lt_succ_self steps)⟩)
        (gje_cumulative_product n N_hat start (start + steps))
        (x_stage start) i).symm

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

/-- **Equation 14.30, cumulative-product certificate route.**

    This source-facing wrapper removes the final componentwise bound
    hypotheses from `gje_stage2_backward_error`: once the per-stage
    perturbations of the GJE second-stage matrices are bounded by `γ₃`, the
    cumulative-product matrix and right-hand-side perturbation bridges provide
    the componentwise bounds (14.30b)--(14.30c).  The exact backward equation
    (14.30a) remains an explicit recurrence-instantiation hypothesis. -/
theorem gje_stage2_backward_error_of_cumulative_product_certificates
    (n : ℕ) (fp : FPModel)
    (U : Fin n → Fin n → ℝ) (y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hn : 1 ≤ n) (hvalid : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1))) U i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∃ (DeltaU : Fin n → Fin n → ℝ) (Deltay : Fin n → ℝ),
      (∀ i : Fin n, ∑ j : Fin n, (U i j + DeltaU i j) * x_hat j =
        y i + Deltay i) ∧
      (∀ i j : Fin n, |DeltaU i j| ≤
        gje_c₃ fp n * ∑ k : Fin n,
          |gje_cumulative_product n (fun s a b => |N_hat s a b|)
            start (start + (n - 1)) i k| * |U k j|) ∧
      (∀ i : Fin n, |Deltay i| ≤
        gje_c₃ fp n * ∑ j : Fin n,
          |gje_cumulative_product n (fun s a b => |N_hat s a b|)
            start (start + (n - 1)) i j| * |y j|) := by
  let Pdelta : Fin n → Fin n → ℝ :=
    gje_cumulative_product n
      (fun k a b => N_hat k a b + DeltaN k a b)
      start (start + (n - 1))
  let P : Fin n → Fin n → ℝ :=
    gje_cumulative_product n N_hat start (start + (n - 1))
  let Pabs : Fin n → Fin n → ℝ :=
    gje_cumulative_product n (fun s a b => |N_hat s a b|)
      start (start + (n - 1))
  let DeltaU : Fin n → Fin n → ℝ := fun i j =>
    matMul n Pdelta U i j - matMul n P U i j
  let Deltay : Fin n → ℝ := fun i =>
    matMulVec n Pdelta y i - matMulVec n P y i
  refine ⟨DeltaU, Deltay, ?_, ?_, ?_⟩
  · intro i
    simpa [DeltaU, Deltay, Pdelta, P] using hBackwardEq i
  · intro i j
    change |DeltaU i j| ≤
      gje_c₃ fp n * ∑ k : Fin n, |Pabs i k| * |U k j|
    have hPabs_nonneg : ∀ a b : Fin n, 0 ≤ Pabs a b := by
      intro a b
      simpa [Pabs] using
        gje_cumulative_product_abs_nonneg n N_hat start (start + (n - 1)) a b
    have hBridge : |DeltaU i j| ≤
        gje_c₃ fp n * ∑ k : Fin n, Pabs i k * |U k j| := by
      simpa [DeltaU, Pdelta, P, Pabs] using
        gje_cumulative_product_matMul_componentwise_perturbation_bound_gamma_c3
          n fp N_hat DeltaN start U hn hvalid hidx hDelta i j
    have hsum :
        (∑ k : Fin n, Pabs i k * |U k j|) =
          ∑ k : Fin n, |Pabs i k| * |U k j| := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_of_nonneg (hPabs_nonneg i k)]
    simpa [hsum] using hBridge
  · intro i
    change |Deltay i| ≤
      gje_c₃ fp n * ∑ j : Fin n, |Pabs i j| * |y j|
    have hPabs_nonneg : ∀ a b : Fin n, 0 ≤ Pabs a b := by
      intro a b
      simpa [Pabs] using
        gje_cumulative_product_abs_nonneg n N_hat start (start + (n - 1)) a b
    have hBridge : |Deltay i| ≤
        gje_c₃ fp n * ∑ j : Fin n, Pabs i j * |y j| := by
      simpa [Deltay, Pdelta, P, Pabs] using
        gje_cumulative_product_matMulVec_componentwise_perturbation_bound_gamma_c3
          n fp N_hat DeltaN start y hn hvalid hidx hDelta i
    have hsum :
        (∑ j : Fin n, Pabs i j * |y j|) =
          ∑ j : Fin n, |Pabs i j| * |y j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_of_nonneg (hPabs_nonneg i j)]
    simpa [hsum] using hBridge

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

/-- **Theorem 14.5, eq. 14.31 certificate route**:
    the cumulative-product second-stage certificates from (14.30) imply the
    overall GJE residual bound, leaving only the exact rounded-recurrence
    backward equation as an explicit source-instantiation hypothesis. -/
theorem gje_overall_residual_of_cumulative_product_certificates
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) k₁ k₂| *
              |U_hat k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n,
          |gje_cumulative_product n (fun s a b => |N_hat s a b|)
            start (start + (n - 1)) k j| * |y j|) := by
  let X_abs : Fin n → Fin n → ℝ :=
    gje_cumulative_product n (fun s a b => |N_hat s a b|)
      start (start + (n - 1))
  obtain ⟨DeltaU, Deltay, hStage2_eq, hDeltaU, hDeltay⟩ :=
    gje_stage2_backward_error_of_cumulative_product_certificates
      n fp U_hat y x_hat N_hat DeltaN start hnpos hn3 hidx hDelta hBackwardEq
  simpa [X_abs] using
    gje_overall_residual n fp A L_hat U_hat b y x_hat X_abs
      hLU hn hn3 hy DeltaU Deltay hStage2_eq hDeltaU hDeltay

/-- **Theorem 14.5 scalar-split residual route**:
    the cumulative-product residual certificate route with the `gje_c₃`
    coefficient expanded into its first-order `3(n-1)u` part plus the
    explicit higher-order remainder. -/
theorem gje_overall_residual_of_cumulative_product_certificates_c3_split
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
      (3 * ((n : ℝ) - 1) * fp.u + gje_c3_quadratic_remainder fp n) *
        ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) k₁ k₂| *
              |U_hat k₂ j|)) * |x_hat j| +
      (3 * ((n : ℝ) - 1) * fp.u + gje_c3_quadratic_remainder fp n) *
        ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) k j| * |y j|) := by
  have h :=
    gje_overall_residual_of_cumulative_product_certificates
      n fp A L_hat U_hat b y x_hat N_hat DeltaN start
      hLU hn hnpos hn3 hidx hDelta hy hBackwardEq
  simpa [gje_c3_eq_linear_plus_quadratic_remainder_term fp n hn3] using h

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

/-- **Theorem 14.5, eqs. 14.31--14.32 certificate route**:
    the cumulative-product second-stage certificates imply the overall GJE
    forward error bound after composing the residual certificate route with
    the exact inverse transfer `|x - x_hat| <= |A_inv| |b - A x_hat|`.

    The exact rounded-recurrence backward equation from (14.30a) remains an
    explicit source-instantiation hypothesis. -/
theorem gje_overall_forward_error_of_cumulative_product_certificates
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) k₁ k₂| *
              |U_hat k₂ k|)) * |x_hat k| +
        gje_c₃ fp n * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) l k| * |y k|)) := by
  let X_abs : Fin n → Fin n → ℝ :=
    gje_cumulative_product n (fun s a b => |N_hat s a b|)
      start (start + (n - 1))
  have hResidual :
      ∀ i : Fin n,
        |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        gamma fp n * ∑ j : Fin n,
          (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
        gje_c₃ fp n * ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| +
        gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n, |X_abs k j| * |y j|) := by
    simpa [X_abs] using
      gje_overall_residual_of_cumulative_product_certificates
        n fp A L_hat U_hat b y x_hat N_hat DeltaN start
        hLU hn hnpos hn3 hidx hDelta hy hBackwardEq
  simpa [X_abs] using
    gje_overall_forward_error n fp A A_inv L_hat U_hat b y x x_hat X_abs
      hLU hAinv hn hn3 hExact hResidual

/-- **Theorem 14.5 scalar-split forward-error route**:
    the cumulative-product forward-error certificate route with the `gje_c₃`
    coefficient expanded into its first-order `3(n-1)u` part plus the
    explicit higher-order remainder. -/
theorem gje_overall_forward_error_of_cumulative_product_certificates_c3_split
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        (3 * ((n : ℝ) - 1) * fp.u + gje_c3_quadratic_remainder fp n) *
          ∑ k : Fin n,
            (∑ k₁ : Fin n, |L_hat j k₁| *
              (∑ k₂ : Fin n,
                |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                  start (start + (n - 1)) k₁ k₂| *
                |U_hat k₂ k|)) * |x_hat k| +
        (3 * ((n : ℝ) - 1) * fp.u + gje_c3_quadratic_remainder fp n) *
          ∑ l : Fin n, |L_hat j l| *
            (∑ k : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) l k| * |y k|)) := by
  have h :=
    gje_overall_forward_error_of_cumulative_product_certificates
      n fp A A_inv L_hat U_hat b y x x_hat N_hat DeltaN start
      hLU hAinv hn hnpos hn3 hidx hDelta hy hExact hBackwardEq
  simpa [gje_c3_eq_linear_plus_quadratic_remainder_term fp n hn3] using h

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
