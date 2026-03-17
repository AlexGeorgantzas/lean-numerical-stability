-- Rounding.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Model

namespace LeanFpAnalysis.FP

/-!
# Accumulated Rounding Error Bound (γ)

Following Higham, "Accuracy and Stability of Numerical Algorithms", §3.1.

For a sequence of n elementary floating-point operations each introducing
a relative error at most u (the unit roundoff), the worst-case accumulated
relative error is bounded by γ(n), defined below.

The definition is valid only under the side condition `n * u < 1`,
which ensures the denominator is positive and the bound is finite.
This condition is always satisfied in practice for reasonable n,
since u is of order 2⁻⁵³ for IEEE double precision.
-/

-- ============================================================
-- §3.1  The γ function
-- ============================================================

/-- `gamma fp n` is Higham's γₙ = (n * u) / (1 - n * u).

    It bounds the relative error accumulated after n rounding operations,
    each satisfying the standard model fl(x op y) = (x op y)(1 + δ), |δ| ≤ u.

    Precondition for meaningful use: `n * fp.u < 1`.
    See `gammaValid` for the explicit guard and `prod_error_bound` for the
    central lemma that justifies this bound. -/
noncomputable def gamma (fp : FPModel) (n : ℕ) : ℝ :=
  (n * fp.u) / (1 - n * fp.u)

/-- Well-definedness guard for `gamma`.
    The denominator `1 - n * u` is positive iff `n * u < 1`.
    All lemmas that use `gamma` in a meaningful bound require this hypothesis.
    In practice this holds for any realistic algorithm depth, since
    u ≈ 2⁻⁵³ in double precision. -/
def gammaValid (fp : FPModel) (n : ℕ) : Prop :=
  (n : ℝ) * fp.u < 1

-- ============================================================
-- §3.1  Product lemma
-- ============================================================

open scoped BigOperators

/-- **Product rounding error lemma** (Higham §3.1, Lemma 3.1).

    Given n rounding errors δ_i with |δ_i| ≤ u, their product satisfies
      ∏ᵢ (1 + δᵢ) = 1 + θ
    for some θ with |θ| ≤ γ(n).

    This is the foundational lemma for all forward error analysis:
    any composition of n rounded operations accumulates a relative
    error bounded by γ(n), regardless of the signs of the individual δᵢ.-/

lemma prod_error_bound (fp : FPModel) (n : ℕ) (δ : Fin n → ℝ)
    (hδ : ∀ i, |δ i| ≤ fp.u)
    (hn : gammaValid fp n) :
    ∃ θ : ℝ, |θ| ≤ gamma fp n ∧
      ∏ i : Fin n, (1 + δ i) = 1 + θ := by
  induction n with
  | zero => exact ⟨0, by simp [gamma], by simp⟩
  | succ n ih =>
    -- Predecessor validity: n*u < (n+1)*u < 1
    have hnu : (n : ℝ) * fp.u < 1 := by
      have h := hn; unfold gammaValid at h; push_cast at h
      have : (↑n + 1) * fp.u = ↑n * fp.u + fp.u := by ring
      linarith [fp.u_nonneg]
    have hn_pred : gammaValid fp n := hnu
    -- Apply IH to the first n components
    obtain ⟨θ', hθ', hprod⟩ :=
      ih (fun i => δ i.castSucc) (fun i => hδ i.castSucc) hn_pred
    -- The new error: θ' from prefix + δₙ from last op + cross term
    refine ⟨θ' + δ (Fin.last n) + θ' * δ (Fin.last n), ?_, ?_⟩
    · have hδn   : |δ (Fin.last n)| ≤ fp.u := hδ (Fin.last n)
      have hγn   : 0 ≤ gamma fp n :=
        div_nonneg (mul_nonneg (by exact_mod_cast n.zero_le) fp.u_nonneg) (by linarith)
      have hn1u  : ((n : ℝ) + 1) * fp.u < 1 := by
        have h := hn; unfold gammaValid at h; push_cast at h; exact h
      have hd_pos  : (0 : ℝ) < 1 - ↑n * fp.u       := by linarith
      have hd1_pos : (0 : ℝ) < 1 - (↑n + 1) * fp.u := by linarith
      -- Product bound: |θ' * δₙ| ≤ γ(n) * u
      have hmul : |θ'| * |δ (Fin.last n)| ≤ gamma fp n * fp.u :=
        mul_le_mul hθ' hδn (abs_nonneg _) hγn
      have hcmul : |θ' * δ (Fin.last n)| ≤ gamma fp n * fp.u := abs_mul θ' _ ▸ hmul
      -- Triangle inequality via abs_le (avoids case split on sign)
      have h_tri : |θ' + δ (Fin.last n) + θ' * δ (Fin.last n)|
          ≤ gamma fp n + fp.u + gamma fp n * fp.u := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le θ', neg_abs_le (δ (Fin.last n)),
                    neg_abs_le (θ' * δ (Fin.last n))]
        · linarith [le_abs_self θ', le_abs_self (δ (Fin.last n)),
                    le_abs_self (θ' * δ (Fin.last n))]
      -- Algebraic identity: γ(n) + u + γ(n)·u = (n+1)·u / (1 - n·u)
      have h_id : gamma fp n + fp.u + gamma fp n * fp.u =
          (↑n + 1) * fp.u / (1 - ↑n * fp.u) := by
        unfold gamma; field_simp [hd_pos.ne']; ring
      -- Monotonicity: (n+1)·u / (1 - n·u) ≤ γ(n+1) since denominator shrinks
      -- Proof: show γ(n+1) - (n+1)u/(1-nu) = (n+1)u² / ((1-nu)(1-(n+1)u)) ≥ 0
      have h_le : (↑n + 1) * fp.u / (1 - ↑n * fp.u) ≤ gamma fp (n + 1) := by
        unfold gamma; push_cast
        have h0n : (0 : ℝ) ≤ ↑n := by exact_mod_cast n.zero_le
        have ha : (0 : ℝ) ≤ (↑n + 1) * fp.u := by
          have : (↑n + 1) * fp.u = ↑n * fp.u + fp.u := by ring
          linarith [mul_nonneg h0n fp.u_nonneg, fp.u_nonneg]
        rw [← sub_nonneg]
        have key : (↑n + 1) * fp.u / (1 - (↑n + 1) * fp.u) -
                   (↑n + 1) * fp.u / (1 - ↑n * fp.u) =
                   (↑n + 1) * fp.u * fp.u /
                   ((1 - ↑n * fp.u) * (1 - (↑n + 1) * fp.u)) := by
          field_simp [hd_pos.ne', hd1_pos.ne']; ring
        rw [key]
        exact div_nonneg (mul_nonneg ha fp.u_nonneg) (le_of_lt (mul_pos hd_pos hd1_pos))
      linarith
    · -- ∏ᵢ<n+1 (1+δᵢ) = (∏ᵢ<n (1+δᵢ.castSucc)) * (1+δₙ) = (1+θ') * (1+δₙ)
      rw [Fin.prod_univ_castSucc, hprod]; ring

-- ============================================================
-- §3.4  Lemma 3.3 — γ arithmetic rules
-- ============================================================

/- **γ multiplication rule** (Higham §3.4, Lemma 3.3 part 1).

    If |θⱼ| ≤ γ(j) and |θₖ| ≤ γ(k), then (1+θⱼ)(1+θₖ) = 1+θ
    for some θ with |θ| ≤ γ(j+k).

    Proof sketch: expand (1+θⱼ)(1+θₖ) = 1 + (θⱼ + θₖ + θⱼθₖ) and bound
      |θⱼ + θₖ + θⱼθₖ| ≤ γ(j) + γ(k) + γ(j)·γ(k) = γ(j+k)
    using the inequality γ(j) + γ(k) + γ(j)·γ(k) ≤ γ(j+k), proved via
    γ(j+k) − (γ(j)+γ(k)+γ(j)γ(k)) = j·k·u² / ((1−j·u)(1−k·u)(1−(j+k)·u)) ≥ 0. -/

lemma gamma_mul (fp : FPModel) (j k : ℕ) (θj θk : ℝ)
    (hj  : |θj| ≤ gamma fp j)
    (hk  : |θk| ≤ gamma fp k)
    (hval : gammaValid fp (j + k)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (j + k) ∧ (1 + θj) * (1 + θk) = 1 + θ := by
  refine ⟨θj + θk + θj * θk, ?_, by ring⟩
  -- Sub-step 1: positivity facts
  have hval' : (↑j + ↑k) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; exact h
  have hju : (↑j : ℝ) * fp.u < 1 := by
    linarith [mul_nonneg (by exact_mod_cast k.zero_le : (0:ℝ) ≤ ↑k) fp.u_nonneg]
  have hku : (↑k : ℝ) * fp.u < 1 := by
    linarith [mul_nonneg (by exact_mod_cast j.zero_le : (0:ℝ) ≤ ↑j) fp.u_nonneg]
  have hdj  : (0 : ℝ) < 1 - ↑j * fp.u       := by linarith
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u       := by linarith
  have hdjk : (0 : ℝ) < 1 - (↑j + ↑k) * fp.u := by linarith
  have hγj : 0 ≤ gamma fp j :=
    div_nonneg (mul_nonneg (by exact_mod_cast j.zero_le) fp.u_nonneg) (by linarith)
  have hγk : 0 ≤ gamma fp k :=
    div_nonneg (mul_nonneg (by exact_mod_cast k.zero_le) fp.u_nonneg) (by linarith)
  -- Sub-step 2: cross term bound
  have hmul : |θj * θk| ≤ gamma fp j * gamma fp k :=
    abs_mul θj θk ▸ mul_le_mul hj hk (abs_nonneg _) hγj
  -- Sub-step 3: triangle inequality
  have h_tri : |θj + θk + θj * θk| ≤ gamma fp j + gamma fp k + gamma fp j * gamma fp k := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le θj, neg_abs_le θk, neg_abs_le (θj * θk)]
    · linarith [le_abs_self θj, le_abs_self θk, le_abs_self (θj * θk)]
  -- Sub-step 4: γ(j) + γ(k) + γ(j)·γ(k) ≤ γ(j+k)
  have h_gamma_ineq : gamma fp j + gamma fp k + gamma fp j * gamma fp k ≤ gamma fp (j + k) := by
    unfold gamma; push_cast
    rw [← sub_nonneg]
    have key : (↑j + ↑k) * fp.u / (1 - (↑j + ↑k) * fp.u) -
               (↑j * fp.u / (1 - ↑j * fp.u) + ↑k * fp.u / (1 - ↑k * fp.u) +
                ↑j * fp.u / (1 - ↑j * fp.u) * (↑k * fp.u / (1 - ↑k * fp.u))) =
               ↑j * ↑k * fp.u ^ 2 /
               ((1 - ↑j * fp.u) * (1 - ↑k * fp.u) * (1 - (↑j + ↑k) * fp.u)) := by
      field_simp [hdj.ne', hdk.ne', hdjk.ne']; ring
    rw [key]
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by exact_mod_cast j.zero_le) (by exact_mod_cast k.zero_le))
                       (sq_nonneg fp.u)
    · exact le_of_lt (mul_pos (mul_pos hdj hdk) hdjk)
  linarith

/-- **γ reciprocal rule** (Higham §3.4, Lemma 3.3 part 2).

    If |θₖ| ≤ γ(k) and 1 + θₖ > 0, then 1/(1+θₖ) = 1+θ
    for some θ with |θ| ≤ γ(2k).

    Proof sketch:
      |1/(1+θₖ) - 1| = |θₖ/(1+θₖ)| ≤ γ(k)/(1-γ(k)) = ku/(1-2ku) ≤ γ(2k). -/
lemma gamma_inv (fp : FPModel) (k : ℕ) (θk : ℝ)
    (hk   : |θk| ≤ gamma fp k)
    (hpos : (0 : ℝ) < 1 + θk)
    (hval : gammaValid fp (2 * k)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (2 * k) ∧ 1 / (1 + θk) = 1 + θ := by
  sorry

/-- **γ division rule** (Higham §3.4, Lemma 3.3 part 3).

    If |θⱼ| ≤ γ(j) and |θₖ| ≤ γ(k) and 1+θₖ > 0, then (1+θⱼ)/(1+θₖ) = 1+θ
    for some θ with |θ| ≤ γ(j + 2k).

    Proof sketch: apply `gamma_inv` to denominator (cost: 2k), then
      `gamma_mul` with the numerator (cost: j), total j+2k. -/
lemma gamma_div (fp : FPModel) (j k : ℕ) (θj θk : ℝ)
    (hj   : |θj| ≤ gamma fp j)
    (hk   : |θk| ≤ gamma fp k)
    (hpos : (0 : ℝ) < 1 + θk)
    (hval : gammaValid fp (j + 2 * k)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (j + 2 * k) ∧ (1 + θj) / (1 + θk) = 1 + θ := by
  sorry

end LeanFpAnalysis.FP
