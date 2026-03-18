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
-- §3.1  Basic properties of gamma and gammaValid
-- ============================================================

/-- `gammaValid` is monotone: if n operations are valid, so are k ≤ n. -/
lemma gammaValid_mono (fp : FPModel) {k n : ℕ} (h : k ≤ n) (hn : gammaValid fp n) :
    gammaValid fp k := by
  unfold gammaValid at hn ⊢
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast h
  linarith [mul_le_mul_of_nonneg_right hkn fp.u_nonneg]

/-- `gamma` is nonneg whenever `gammaValid` holds. -/
lemma gamma_nonneg (fp : FPModel) {n : ℕ} (hn : gammaValid fp n) : 0 ≤ gamma fp n :=
  div_nonneg (mul_nonneg (by exact_mod_cast n.zero_le) fp.u_nonneg)
             (by unfold gammaValid at hn; linarith)

/-- `gamma` is monotone in n.

    Proof: write n = k + m, then γ(k) ≤ γ(k) + γ(m) + γ(k)·γ(m) ≤ γ(k+m) = γ(n). -/
lemma gamma_mono (fp : FPModel) {k n : ℕ} (h : k ≤ n) (hn : gammaValid fp n) :
    gamma fp k ≤ gamma fp n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hval' : (↑k + ↑m) * fp.u < 1 := by
    have h := hn; unfold gammaValid at h; push_cast at h; exact h
  have hku  : (↑k : ℝ) * fp.u < 1 :=
    by linarith [mul_nonneg (by exact_mod_cast m.zero_le : (0:ℝ) ≤ ↑m) fp.u_nonneg]
  have hmu  : (↑m : ℝ) * fp.u < 1 :=
    by linarith [mul_nonneg (by exact_mod_cast k.zero_le : (0:ℝ) ≤ ↑k) fp.u_nonneg]
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u        := by linarith
  have hdm  : (0 : ℝ) < 1 - ↑m * fp.u        := by linarith
  have hdkm : (0 : ℝ) < 1 - (↑k + ↑m) * fp.u := by linarith
  have hγk  : 0 ≤ gamma fp k :=
    div_nonneg (mul_nonneg (by exact_mod_cast k.zero_le) fp.u_nonneg) (by linarith)
  have hγm  : 0 ≤ gamma fp m :=
    div_nonneg (mul_nonneg (by exact_mod_cast m.zero_le) fp.u_nonneg) (by linarith)
  -- γ(k) + γ(m) + γ(k)·γ(m) ≤ γ(k+m)  (same identity as in gamma_mul)
  have h_ineq : gamma fp k + gamma fp m + gamma fp k * gamma fp m ≤ gamma fp (k + m) := by
    unfold gamma; push_cast; rw [← sub_nonneg]
    have key : (↑k + ↑m) * fp.u / (1 - (↑k + ↑m) * fp.u) -
               (↑k * fp.u / (1 - ↑k * fp.u) + ↑m * fp.u / (1 - ↑m * fp.u) +
                ↑k * fp.u / (1 - ↑k * fp.u) * (↑m * fp.u / (1 - ↑m * fp.u))) =
               ↑k * ↑m * fp.u ^ 2 /
               ((1 - ↑k * fp.u) * (1 - ↑m * fp.u) * (1 - (↑k + ↑m) * fp.u)) := by
      field_simp [hdk.ne', hdm.ne', hdkm.ne']; ring
    rw [key]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by exact_mod_cast k.zero_le) (by exact_mod_cast m.zero_le))
                  (sq_nonneg fp.u))
      (le_of_lt (mul_pos (mul_pos hdk hdm) hdkm))
  linarith [mul_nonneg hγk hγm]

/-- The unit roundoff is bounded by γ(k) for any k ≥ 1.

    Proof: u ≤ k·u ≤ k·u/(1−k·u) = γ(k),
    since k ≥ 1 gives u ≤ k·u, and 1−k·u ≤ 1 gives k·u ≤ k·u/(1−k·u). -/
lemma u_le_gamma (fp : FPModel) {k : ℕ} (hk : 0 < k) (hval : gammaValid fp k) :
    fp.u ≤ gamma fp k := by
  unfold gamma
  have hku  : (↑k : ℝ) * fp.u < 1 := hval
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u := by linarith
  have hk1  : (1 : ℝ) ≤ ↑k := by exact_mod_cast hk
  -- fp.u ≤ k * fp.u  (since k ≥ 1)
  have h1 : fp.u ≤ ↑k * fp.u := le_mul_of_one_le_left fp.u_nonneg hk1
  -- k * fp.u ≤ k * fp.u / (1 - k * fp.u)  (since 1 - k * fp.u ≤ 1)
  have h2 : ↑k * fp.u ≤ ↑k * fp.u / (1 - ↑k * fp.u) := by
    by_contra hc
    push_neg at hc
    have hmul := mul_lt_mul_of_pos_right hc hdk
    have hcancel : ↑k * fp.u / (1 - ↑k * fp.u) * (1 - ↑k * fp.u) = ↑k * fp.u := by
      field_simp [hdk.ne']
    rw [hcancel] at hmul
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ ↑k) fp.u_nonneg) fp.u_nonneg]
  linarith

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

    Proof sketch: witness θ = −θₖ/(1+θₖ). Bound via
      |θ| = |θₖ|/(1+θₖ) ≤ γ(k)/(1+θₖ) ≤ γ(2k),
    using the identity γ(2k)·(1−γ(k)) = 2·γ(k) and 1−γ(k) ≤ 1+θₖ. -/
lemma gamma_inv (fp : FPModel) (k : ℕ) (θk : ℝ)
    (hk   : |θk| ≤ gamma fp k)
    (hpos : (0 : ℝ) < 1 + θk)
    (hval : gammaValid fp (2 * k)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (2 * k) ∧ 1 / (1 + θk) = 1 + θ := by
  refine ⟨-θk / (1 + θk), ?_, by field_simp [hpos.ne']; ring⟩
  -- Setup facts from hval
  have h2ku : 2 * (↑k : ℝ) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; linarith
  have hku  : (↑k : ℝ) * fp.u < 1 := by linarith
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u     := by linarith
  have hd2k : (0 : ℝ) < 1 - 2 * ↑k * fp.u := by linarith
  have hγk  : 0 ≤ gamma fp k :=
    div_nonneg (mul_nonneg (by exact_mod_cast k.zero_le) fp.u_nonneg) (by linarith)
  have hγk_lt1 : gamma fp k < 1 := by
    unfold gamma; rw [div_lt_one hdk]; linarith
  have hγ2k : 0 ≤ gamma fp (2 * k) := by
    unfold gamma
    apply div_nonneg
    · exact mul_nonneg (by exact_mod_cast (2 * k).zero_le) fp.u_nonneg
    · have h := hval; unfold gammaValid at h; linarith
  have htk_lb : -gamma fp k ≤ θk := by linarith [neg_abs_le θk]
  -- Rewrite to multiplicative form
  have h_abs : |-θk / (1 + θk)| = |θk| / (1 + θk) := by
    rw [abs_div, abs_neg, abs_of_pos hpos]
  rw [h_abs]
  -- Key algebraic identity: γ(2k) · (1 − γ(k)) = 2 · γ(k)
  have h_id : gamma fp (2 * k) * (1 - gamma fp k) = 2 * gamma fp k := by
    unfold gamma; push_cast
    field_simp [hdk.ne', hd2k.ne']; ring
  have h_bound : |θk| ≤ gamma fp (2 * k) * (1 + θk) := by
    calc |θk|
        ≤ gamma fp k                           := hk
      _ ≤ 2 * gamma fp k                      := by linarith
      _ = gamma fp (2 * k) * (1 - gamma fp k) := h_id.symm
      _ ≤ gamma fp (2 * k) * (1 + θk)        :=
            mul_le_mul_of_nonneg_left (by linarith) hγ2k
  -- |θk| / (1 + θk) ≤ γ(2k): by contradiction, multiplying out
  have hcancel : |θk| / (1 + θk) * (1 + θk) = |θk| := by field_simp [hpos.ne']
  by_contra h
  push_neg at h
  have hmul := mul_lt_mul_of_pos_right h hpos
  rw [hcancel] at hmul
  linarith

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
  -- Step 1: extract gammaValid fp (2 * k) from hval
  have hval2k : gammaValid fp (2 * k) := by
    unfold gammaValid at hval ⊢; push_cast at hval ⊢
    linarith [mul_nonneg (by exact_mod_cast j.zero_le : (0:ℝ) ≤ ↑j) fp.u_nonneg]
  -- Step 2: apply gamma_inv — cost 2k on denominator
  obtain ⟨θ', hθ', hinv⟩ := gamma_inv fp k θk hk hpos hval2k
  -- Step 3: apply gamma_mul — cost j + 2k on numerator × inv
  obtain ⟨θ'', hθ'', hmul⟩ := gamma_mul fp j (2 * k) θj θ' hj hθ' hval
  refine ⟨θ'', hθ'', ?_⟩
  have : (1 + θj) / (1 + θk) = (1 + θj) * (1 / (1 + θk)) := by ring
  rw [this, hinv, hmul]

-- ============================================================
-- §3.4  Additional Lemma 3.3 rules (standalone)
-- ============================================================

/-- **Lemma 3.3 rule 6** (standalone): γ(j) + γ(k) + γ(j)·γ(k) ≤ γ(j+k).

    This algebraic identity underlies both `gamma_mul` and `gamma_mono`.
    Proof: γ(j+k) − (γ(j)+γ(k)+γ(j)γ(k)) = j·k·u² / ((1−ju)(1−ku)(1−(j+k)u)) ≥ 0. -/
lemma gamma_sum_le (fp : FPModel) (j k : ℕ) (hval : gammaValid fp (j + k)) :
    gamma fp j + gamma fp k + gamma fp j * gamma fp k ≤ gamma fp (j + k) := by
  have hval' : (↑j + ↑k) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; exact h
  have hju : (↑j : ℝ) * fp.u < 1 :=
    by linarith [mul_nonneg (by exact_mod_cast k.zero_le : (0:ℝ) ≤ ↑k) fp.u_nonneg]
  have hku : (↑k : ℝ) * fp.u < 1 :=
    by linarith [mul_nonneg (by exact_mod_cast j.zero_le : (0:ℝ) ≤ ↑j) fp.u_nonneg]
  have hdj  : (0 : ℝ) < 1 - ↑j * fp.u        := by linarith
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u        := by linarith
  have hdjk : (0 : ℝ) < 1 - (↑j + ↑k) * fp.u := by linarith
  unfold gamma; push_cast; rw [← sub_nonneg]
  have key : (↑j + ↑k) * fp.u / (1 - (↑j + ↑k) * fp.u) -
             (↑j * fp.u / (1 - ↑j * fp.u) + ↑k * fp.u / (1 - ↑k * fp.u) +
              ↑j * fp.u / (1 - ↑j * fp.u) * (↑k * fp.u / (1 - ↑k * fp.u))) =
             ↑j * ↑k * fp.u ^ 2 /
             ((1 - ↑j * fp.u) * (1 - ↑k * fp.u) * (1 - (↑j + ↑k) * fp.u)) := by
    field_simp [hdj.ne', hdk.ne', hdjk.ne']; ring
  rw [key]
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by exact_mod_cast j.zero_le) (by exact_mod_cast k.zero_le))
                (sq_nonneg fp.u))
    (le_of_lt (mul_pos (mul_pos hdj hdk) hdjk))

/-- **Lemma 3.3 rule 5**: γ(k) + u ≤ γ(k+1).

    Proof: γ(k+1) − (γ(k)+u) = u²·(2k+1−k(k+1)u) / ((1−ku)(1−(k+1)u)) ≥ 0,
    since k(k+1)u < k ≤ 2k+1 from gammaValid fp (k+1). -/
lemma gamma_add_u_le (fp : FPModel) (k : ℕ) (hval : gammaValid fp (k + 1)) :
    gamma fp k + fp.u ≤ gamma fp (k + 1) := by
  have hku  : (↑k : ℝ) * fp.u < 1 := gammaValid_mono fp (Nat.le_succ k) hval
  have hk1u : ((↑k : ℝ) + 1) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; exact h
  have hdk  : (0 : ℝ) < 1 - ↑k * fp.u        := by linarith
  have hdk1 : (0 : ℝ) < 1 - (↑k + 1) * fp.u  := by linarith
  unfold gamma; push_cast; rw [← sub_nonneg]
  have key : (↑k + 1) * fp.u / (1 - (↑k + 1) * fp.u) -
             (↑k * fp.u / (1 - ↑k * fp.u) + fp.u) =
             fp.u ^ 2 * (2 * ↑k + 1 - ↑k * (↑k + 1) * fp.u) /
             ((1 - ↑k * fp.u) * (1 - (↑k + 1) * fp.u)) := by
    field_simp [hdk.ne', hdk1.ne']; ring
  rw [key]
  apply div_nonneg
  · apply mul_nonneg (sq_nonneg fp.u)
    have hk0 : (0 : ℝ) ≤ ↑k := by exact_mod_cast k.zero_le
    have : ↑k * ((↑k + 1) * fp.u) ≤ ↑k * 1 :=
      mul_le_mul_of_nonneg_left (le_of_lt hk1u) hk0
    linarith
  · exact le_of_lt (mul_pos hdk hdk1)

/-- **Lemma 3.3 rule 4**: i·γ(k) ≤ γ(i·k) for i ≥ 1.

    Proof: i·(ku/(1−ku)) = iku/(1−ku) ≤ iku/(1−iku),
    since i ≥ 1 gives iku ≥ ku, hence 1−iku ≤ 1−ku (smaller denominator).
    Algebraically: γ(ik) − i·γ(k) = i(i−1)(ku)² / ((1−iku)(1−ku)) ≥ 0. -/
lemma gamma_nsmul_le (fp : FPModel) (i k : ℕ) (hi : 1 ≤ i)
    (hval : gammaValid fp (i * k)) :
    (i : ℝ) * gamma fp k ≤ gamma fp (i * k) := by
  have hiku : (↑i * ↑k) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; linarith
  have hi1 : (1 : ℝ) ≤ ↑i := by exact_mod_cast hi
  have hk0 : (0 : ℝ) ≤ ↑k := by exact_mod_cast k.zero_le
  have hku : (↑k : ℝ) * fp.u < 1 := by
    nlinarith [mul_nonneg hk0 fp.u_nonneg]
  have hdiku : (0 : ℝ) < 1 - ↑i * ↑k * fp.u := by linarith
  have hdku  : (0 : ℝ) < 1 - ↑k * fp.u       := by linarith
  unfold gamma; push_cast; rw [← sub_nonneg]
  have key : ↑i * ↑k * fp.u / (1 - ↑i * ↑k * fp.u) -
             ↑i * (↑k * fp.u / (1 - ↑k * fp.u)) =
             ↑i * (↑i - 1) * (↑k * fp.u) ^ 2 /
             ((1 - ↑i * ↑k * fp.u) * (1 - ↑k * fp.u)) := by
    field_simp [hdiku.ne', hdku.ne']; ring
  rw [key]
  apply div_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (by exact_mod_cast Nat.zero_le i) (by linarith)
    · exact sq_nonneg _
  · exact le_of_lt (mul_pos hdiku hdku)

/-- **Helper**: γ(k) < 1 whenever gammaValid fp (2k).

    Proof: gammaValid fp (2k) gives 2ku < 1, so ku < 1/2,
    hence ku/(1−ku) < 1 iff ku < 1−ku iff 2ku < 1. -/
lemma gamma_lt_one (fp : FPModel) (k : ℕ) (hval : gammaValid fp (2 * k)) :
    gamma fp k < 1 := by
  have hku : (↑k : ℝ) * fp.u < 1 :=
    gammaValid_mono fp (by omega) hval
  have h2ku : 2 * (↑k : ℝ) * fp.u < 1 := by
    have h := hval; unfold gammaValid at h; push_cast at h; linarith
  have hdk : (0 : ℝ) < 1 - ↑k * fp.u := by linarith
  unfold gamma
  rw [div_lt_one hdk]
  linarith

/-- **Lemma 3.3 rule 3**: γ(j)·γ(k) ≤ γ(min j k).

    WLOG j ≤ k (min = j).  Then γ(k) < 1 (from gammaValid fp (2k)),
    so γ(j)·γ(k) ≤ γ(j)·1 = γ(j).

    Precondition: gammaValid fp (2·k) (the larger index) ensures γ(k) < 1. -/
lemma gamma_prod_le (fp : FPModel) (j k : ℕ) (hjk : j ≤ k)
    (hval2k : gammaValid fp (2 * k)) :
    gamma fp j * gamma fp k ≤ gamma fp j := by
  have hval_j : gammaValid fp j :=
    gammaValid_mono fp (le_trans hjk (by omega)) hval2k
  have hγj    : 0 ≤ gamma fp j   := gamma_nonneg fp hval_j
  have hγk_lt : gamma fp k < 1   := gamma_lt_one fp k hval2k
  calc gamma fp j * gamma fp k
      ≤ gamma fp j * 1 := mul_le_mul_of_nonneg_left (le_of_lt hγk_lt) hγj
    _ = gamma fp j     := mul_one _

end LeanFpAnalysis.FP
