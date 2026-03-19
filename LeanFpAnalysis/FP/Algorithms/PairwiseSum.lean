-- Algorithms/PairwiseSum.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-!
# Pairwise Summation (Higham §4.2, equation 4.6)

For `n = 2^r` inputs, pairwise (cascade/fan-in) summation halves the array
recursively and adds the two sub-sums:

```
S₄ = (x₀ + x₁) + (x₂ + x₃)
S₈ = ((x₀+x₁)+(x₂+x₃)) + ((x₄+x₅)+(x₆+x₇))
```

Each element takes part in exactly `r = log₂ n` additions, giving the error
bound  `|Ê - S| ≤ γ(r) * Σ|xᵢ|`  (Higham (4.6)).
-/

-- ============================================================
-- Index-bound helpers for the two halves of Fin (2^(r+1))
-- ============================================================

private lemma left_lt (r : ℕ) (i : Fin (2 ^ r)) : i.val < 2 ^ (r + 1) := by
  have := i.isLt; simp [pow_succ]; omega

private lemma right_lt (r : ℕ) (i : Fin (2 ^ r)) : i.val + 2 ^ r < 2 ^ (r + 1) := by
  have := i.isLt; simp [pow_succ]; omega

-- ============================================================
-- Sum-splitting lemma: Fin (2^(r+1)) = left half + right half
-- ============================================================

/-- Split a sum over `Fin (2^(r+1))` into left and right halves. -/
private lemma sum_split {M : Type*} [AddCommMonoid M] (r : ℕ)
    (v : Fin (2 ^ (r + 1)) → M) :
    ∑ i : Fin (2 ^ (r + 1)), v i =
    ∑ i : Fin (2 ^ r), v ⟨i.val, left_lt r i⟩ +
    ∑ i : Fin (2 ^ r), v ⟨i.val + 2 ^ r, right_lt r i⟩ := by
  -- Step 1: reindex over Fin (2^r + 2^r) via finCongr
  have h : (2 : ℕ) ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
  have lhs_eq : ∑ i : Fin (2 ^ (r + 1)), v i =
      ∑ i : Fin (2 ^ r + 2 ^ r), v ⟨i.val, h.symm ▸ i.isLt⟩ :=
    Fintype.sum_equiv (finCongr h) _ _ fun i => by
      -- finCongr h i has the same val as i, so the Fin elements are equal by proof irrel
      rfl
  -- Step 2: split Fin (2^r + 2^r) using Fin.sum_univ_add
  rw [lhs_eq, Fin.sum_univ_add]
  -- congr 1 closes the castAdd goal by definitional equality (val = i.val);
  -- the only remaining goal is the natAdd side (val = 2^r + i.val, need add_comm)
  congr 1
  apply Finset.sum_congr rfl; intro i _
  congr 1; apply Fin.ext; simp

-- ============================================================
-- Definition
-- ============================================================

/-- Floating-point pairwise summation of `2^r` values.

    - `r = 0`: single element, no addition.
    - `r + 1`: recursively sum left half and right half, then `fl_add`. -/
noncomputable def fl_pairwiseSum (fp : FPModel) :
    (r : ℕ) → (Fin (2 ^ r) → ℝ) → ℝ
  | 0,     v => v ⟨0, by norm_num⟩
  | r + 1, v => fp.fl_add
      (fl_pairwiseSum fp r (fun i => v ⟨i.val, left_lt r i⟩))
      (fl_pairwiseSum fp r (fun i => v ⟨i.val + 2 ^ r, right_lt r i⟩))

-- ============================================================
-- Backward error
-- ============================================================

/-- **Pairwise summation backward error** (Higham §4.2).

    For `n = 2^r` inputs, pairwise summation satisfies:
      `fl_pairwiseSum fp r v = ∑ i, v i * (1 + η i)`
    where each `|η i| ≤ γ(r)`.

    Each element takes part in exactly `r` additions; the backward error
    factor per element is therefore γ(r), not γ(n-1) as in recursive summation.

    Proof sketch: induction on `r`.
    - Base: no addition, so η ≡ 0 and γ(0) = 0.
    - Step: IH gives left and right halves each with error ≤ γ(r).
      The final `fl_add` introduces δ with |δ| ≤ u ≤ γ(1).
      `gamma_mul` combines each per-element γ(r) error with δ into γ(r+1). -/
theorem pairwiseSum_backward_error (fp : FPModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hr : gammaValid fp r) :
    ∃ η : Fin (2 ^ r) → ℝ,
      (∀ i, |η i| ≤ gamma fp r) ∧
      fl_pairwiseSum fp r v = ∑ i : Fin (2 ^ r), v i * (1 + η i) := by
  induction r with
  | zero =>
    refine ⟨fun _ => 0, fun _ => by simp [gamma], ?_⟩
    simp [fl_pairwiseSum]
  | succ r ih =>
    -- gammaValid for subproblems
    have hr' : gammaValid fp r := gammaValid_mono fp (Nat.le_succ r) hr
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hr
    -- IH on left and right halves
    obtain ⟨ηL, hηL, hL⟩ := ih (fun i => v ⟨i.val, left_lt r i⟩) hr'
    obtain ⟨ηR, hηR, hR⟩ := ih (fun i => v ⟨i.val + 2 ^ r, right_lt r i⟩) hr'
    -- rounding error from the top-level fl_add
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (fl_pairwiseSum fp r (fun i => v ⟨i.val, left_lt r i⟩))
        (fl_pairwiseSum fp r (fun i => v ⟨i.val + 2 ^ r, right_lt r i⟩))
    have hδ_1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos h1valid)
    -- per-element combined errors
    -- left half i : Fin (2^r)  → ηL i + δ + ηL i * δ,  bounded by γ(r+1)
    -- right half i : Fin (2^r) → ηR i + δ + ηR i * δ,  bounded by γ(r+1)
    -- extend to η : Fin (2^(r+1)) → ℝ by splitting on index
    let η : Fin (2 ^ (r + 1)) → ℝ := fun i =>
      if h : i.val < 2 ^ r then
        ηL ⟨i.val, h⟩ + δ + ηL ⟨i.val, h⟩ * δ
      else
        ηR ⟨i.val - 2 ^ r,
          (by have := i.isLt; simp [pow_succ] at this; omega)⟩ + δ +
        ηR ⟨i.val - 2 ^ r,
          (by have := i.isLt; simp [pow_succ] at this; omega)⟩ * δ
    refine ⟨η, ?_, ?_⟩
    · -- bound: ∀ i, |η i| ≤ γ(r+1)
      intro i
      simp only [η]
      split_ifs with h
      · -- left: combine ηL ⟨i.val, h⟩ with δ via gamma_mul
        obtain ⟨e, he, heq⟩ := gamma_mul fp r 1 (ηL ⟨i.val, h⟩) δ (hηL ⟨i.val, h⟩) hδ_1 hr
        have hval : e = ηL ⟨i.val, h⟩ + δ + ηL ⟨i.val, h⟩ * δ := by linarith [heq, (by ring : (1 + ηL ⟨i.val, h⟩) * (1 + δ) = 1 + (ηL ⟨i.val, h⟩ + δ + ηL ⟨i.val, h⟩ * δ))]
        rw [← hval]; exact he
      · -- right: combine ηR ⟨…⟩ with δ via gamma_mul
        push_neg at h
        set j : Fin (2 ^ r) := ⟨i.val - 2 ^ r, by have := i.isLt; simp [pow_succ] at this; omega⟩
        obtain ⟨e, he, heq⟩ := gamma_mul fp r 1 (ηR j) δ (hηR j) hδ_1 hr
        have hval : e = ηR j + δ + ηR j * δ := by linarith [heq, (by ring : (1 + ηR j) * (1 + δ) = 1 + (ηR j + δ + ηR j * δ))]
        rw [← hval]; exact he
    · -- sum equality: fl_pairwiseSum (r+1) v = ∑ v i * (1 + η i)
      show fp.fl_add
          (fl_pairwiseSum fp r fun i => v ⟨i.val, left_lt r i⟩)
          (fl_pairwiseSum fp r fun i => v ⟨i.val + 2 ^ r, right_lt r i⟩) =
          ∑ i : Fin (2 ^ (r + 1)), v i * (1 + η i)
      rw [hfl, hL, hR]
      -- split RHS into left + right halves, then distribute (1+δ) on LHS
      conv_rhs => rw [sum_split r (fun i => v i * (1 + η i))]
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      · -- left half: ∑ v ⟨i.val,_⟩ * (1+ηL i) * (1+δ) = ∑ v ⟨i.val,_⟩ * (1 + η ⟨i.val,_⟩)
        apply Finset.sum_congr rfl; intro i _
        have hη_i : η ⟨i.val, left_lt r i⟩ = ηL i + δ + ηL i * δ := by
          change dite (i.val < 2 ^ r)
            (fun h => ηL ⟨i.val, h⟩ + δ + ηL ⟨i.val, h⟩ * δ)
            (fun _ => ηR ⟨i.val - 2 ^ r, _⟩ + δ + ηR ⟨i.val - 2 ^ r, _⟩ * δ) = _
          rw [dif_pos i.isLt]
        rw [hη_i]; ring
      · -- right half: ∑ v ⟨i.val+2^r,_⟩ * (1+ηR i) * (1+δ) = ∑ v ⟨i.val+2^r,_⟩ * (1 + η ⟨i.val+2^r,_⟩)
        apply Finset.sum_congr rfl; intro i _
        have hη_i : η ⟨i.val + 2 ^ r, right_lt r i⟩ = ηR i + δ + ηR i * δ := by
          change dite (i.val + 2 ^ r < 2 ^ r)
            (fun h => ηL ⟨i.val + 2 ^ r, h⟩ + δ + ηL ⟨i.val + 2 ^ r, h⟩ * δ)
            (fun _ => ηR ⟨i.val + 2 ^ r - 2 ^ r, _⟩ + δ + ηR ⟨i.val + 2 ^ r - 2 ^ r, _⟩ * δ) = _
          rw [dif_neg (by omega : ¬ (i.val + 2 ^ r < 2 ^ r))]
          have hj : (⟨i.val + 2 ^ r - 2 ^ r,
              (by have := i.isLt; simp at this; omega : i.val + 2 ^ r - 2 ^ r < 2 ^ r)⟩
              : Fin (2 ^ r)) = i := Fin.ext (Nat.add_sub_cancel_right i.val (2 ^ r))
          rw [hj]
        rw [hη_i]; ring

-- ============================================================
-- Forward error bound
-- ============================================================

/-- **Pairwise summation forward error bound** (Higham §4.2, equation 4.6).

    For `n = 2^r` inputs:
      `|fl_pairwiseSum fp r v - ∑ i, v i| ≤ γ(r) * ∑ i, |v i|`

    Since the exponent is `r = log₂ n` rather than `n - 1`, this is a
    significantly tighter bound than recursive summation for large `n`. -/
theorem pairwiseSum_forward_error_bound (fp : FPModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hr : gammaValid fp r) :
    |fl_pairwiseSum fp r v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp r * ∑ i : Fin (2 ^ r), |v i| := by
  obtain ⟨η, hη, hfold⟩ := pairwiseSum_backward_error fp r v hr
  have herr : fl_pairwiseSum fp r v - ∑ i : Fin (2 ^ r), v i =
      ∑ i : Fin (2 ^ r), v i * η i := by
    rw [hfold, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [herr]
  calc |∑ i : Fin (2 ^ r), v i * η i|
      ≤ ∑ i : Fin (2 ^ r), |v i * η i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (2 ^ r), |v i| * |η i| := by
          apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
    _ ≤ ∑ i : Fin (2 ^ r), |v i| * gamma fp r :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hη i) (abs_nonneg _)
    _ = gamma fp r * ∑ i : Fin (2 ^ r), |v i| := by
          rw [← Finset.sum_mul, mul_comm]

end LeanFpAnalysis.FP
