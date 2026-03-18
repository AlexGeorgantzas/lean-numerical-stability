-- Summation.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-- **Summation rounding error lemma** (Higham §3.1).

    For a sequence of values v : Fin n → ℝ, sequential floating-point
    summation (left-to-right, starting from 0) produces a result equal to
    a perturbation of the exact sum:

      fl_sum fp n v = ∑ i, v i * (1 + θ i)

    where each |θ i| ≤ gamma fp n.

    Intuition: the term v 0 passes through all n additions and accumulates
    up to n rounding errors; term v i passes through (n - i) additions.
    The worst case over all terms is γ(n), giving a uniform bound.

    Precondition: gammaValid fp n ensures the denominator of γ is positive.

    Proof sketch: induction on n, peeling the last addition via
    `Fin.foldl_succ_last`.  For each prior term, one new rounding error δ
    combines with the IH witness θ' i via `gamma_mul`: the new error
    θ' i + δ + θ' i · δ satisfies |·| ≤ γ(n+1).  The new term v(last n)
    picks up only δ, which is bounded by u ≤ γ(1) ≤ γ(n+1). -/

lemma fl_sum_error (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ gamma fp n) ∧
      Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0 =
        ∑ i : Fin n, v i * (1 + θ i) := by
  induction n with
  | zero =>
    exact ⟨fun i => i.elim0, fun i => i.elim0, by simp⟩
  | succ n ih =>
    have hn_pred : gammaValid fp n := gammaValid_mono fp (Nat.le_succ n) hn
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
    -- Apply IH to v ∘ Fin.castSucc
    obtain ⟨θ', hθ', hfold_n⟩ := ih (fun i => v i.castSucc) hn_pred
    -- Peel the last addition off the fold
    have hfold_last : Fin.foldl (n + 1) (fun acc i => fp.fl_add acc (v i)) 0 =
        fp.fl_add (Fin.foldl n (fun acc i => fp.fl_add acc (v i.castSucc)) 0) (v (Fin.last n)) :=
      Fin.foldl_succ_last _ _
    -- Extract the rounding error δ for the last fl_add
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (Fin.foldl n (fun acc i => fp.fl_add acc (v i.castSucc)) 0) (v (Fin.last n))
    -- Rewrite the fold to its expanded form
    rw [hfold_last, hfl, hfold_n]
    -- Construct θ : Fin (n+1) → ℝ
    refine ⟨Fin.lastCases δ (fun i => θ' i + δ + θ' i * δ), ?_, ?_⟩
    · -- Bound: ∀ i, |θ i| ≤ γ(n+1)
      intro i
      refine Fin.lastCases ?_ ?_ i
      · -- i = Fin.last n: |δ| ≤ u ≤ γ(1) ≤ γ(n+1)
        simp only [Fin.lastCases_last]
        have h1n : gamma fp 1 ≤ gamma fp (n + 1) := gamma_mono fp (by omega) hn
        linarith [u_le_gamma fp one_pos h1valid]
      · -- i = j.castSucc: |θ' j + δ + θ' j * δ| ≤ γ(n+1)
        intro j
        simp only [Fin.lastCases_castSucc]
        have hδ_1 : |δ| ≤ gamma fp 1 :=
          le_trans hδ (u_le_gamma fp one_pos h1valid)
        obtain ⟨θ_j, hθ_j, heq⟩ := gamma_mul fp n 1 (θ' j) δ (hθ' j) hδ_1 hn
        have hval : θ_j = θ' j + δ + θ' j * δ := by
          have hring : (1 + θ' j) * (1 + δ) = 1 + (θ' j + δ + θ' j * δ) := by ring
          linarith [hring, heq]
        rw [← hval]; exact hθ_j
    · -- Sum equality: (∑ θ'·terms + last) * (1+δ) = ∑(n+1) θ·terms
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      rw [add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- **Summation rounding error with initial accumulator** (Higham §3.1 generalized).

    For a sequence v : Fin n → ℝ and an initial value s ∈ ℝ, sequential
    floating-point summation starting from s satisfies:

      foldl n (fl_add · (v ·)) s = s * (1 + Θ) + ∑ i, v i * (1 + θ i)

    where |Θ| ≤ γ(n) and each |θ i| ≤ γ(n).

    This generalizes `fl_sum_error` (which has s = 0) and is the key ingredient
    for the tight Higham dot-product bound, where the initial accumulator is
    fl_mul (x 0) (y 0) rather than 0.

    Proof sketch: induction on n, peeling the last addition via
    `Fin.foldl_succ_last`.  The new error δ combines with Θ' (and each θ' i)
    via `gamma_mul` to stay within γ(n+1). -/
lemma fl_sum_error_init (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) (s : ℝ)
    (hn : gammaValid fp n) :
    ∃ (Θ : ℝ) (θ : Fin n → ℝ),
      |Θ| ≤ gamma fp n ∧ (∀ i, |θ i| ≤ gamma fp n) ∧
      Fin.foldl n (fun acc i => fp.fl_add acc (v i)) s =
        s * (1 + Θ) + ∑ i : Fin n, v i * (1 + θ i) := by
  induction n with
  | zero =>
    exact ⟨0, fun i => i.elim0, by simp [gamma], fun i => i.elim0, by simp⟩
  | succ n ih =>
    have hn_pred : gammaValid fp n := gammaValid_mono fp (Nat.le_succ n) hn
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
    -- Apply IH to v ∘ Fin.castSucc with the same initial accumulator s
    obtain ⟨Θ', θ', hΘ', hθ', hfold_n⟩ := ih (fun i => v i.castSucc) hn_pred
    -- Peel the last addition off the fold
    have hfold_last : Fin.foldl (n + 1) (fun acc i => fp.fl_add acc (v i)) s =
        fp.fl_add (Fin.foldl n (fun acc i => fp.fl_add acc (v i.castSucc)) s)
          (v (Fin.last n)) :=
      Fin.foldl_succ_last _ _
    -- Extract the rounding error δ for the last fl_add
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (Fin.foldl n (fun acc i => fp.fl_add acc (v i.castSucc)) s) (v (Fin.last n))
    -- Rewrite the fold to its expanded form
    rw [hfold_last, hfl, hfold_n]
    -- Construct witnesses: Θ = Θ' + δ + Θ'·δ,  θ = lastCases δ (θ' j + δ + θ' j·δ)
    refine ⟨Θ' + δ + Θ' * δ, Fin.lastCases δ (fun i => θ' i + δ + θ' i * δ), ?_, ?_, ?_⟩
    · -- |Θ' + δ + Θ' * δ| ≤ γ(n+1)
      have hδ_1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos h1valid)
      obtain ⟨η, hη, heq⟩ := gamma_mul fp n 1 Θ' δ hΘ' hδ_1 hn
      have hval : η = Θ' + δ + Θ' * δ := by
        have hring : (1 + Θ') * (1 + δ) = 1 + (Θ' + δ + Θ' * δ) := by ring
        linarith [hring, heq]
      rw [← hval]; exact hη
    · -- ∀ i, |θ i| ≤ γ(n+1)
      intro i
      refine Fin.lastCases ?_ ?_ i
      · -- i = Fin.last n: |δ| ≤ u ≤ γ(1) ≤ γ(n+1)
        simp only [Fin.lastCases_last]
        have h1n : gamma fp 1 ≤ gamma fp (n + 1) := gamma_mono fp (by omega) hn
        linarith [u_le_gamma fp one_pos h1valid]
      · -- i = j.castSucc: |θ' j + δ + θ' j * δ| ≤ γ(n+1)
        intro j
        simp only [Fin.lastCases_castSucc]
        have hδ_1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos h1valid)
        obtain ⟨θ_j, hθ_j, heq⟩ := gamma_mul fp n 1 (θ' j) δ (hθ' j) hδ_1 hn
        have hval : θ_j = θ' j + δ + θ' j * δ := by
          have hring : (1 + θ' j) * (1 + δ) = 1 + (θ' j + δ + θ' j * δ) := by ring
          linarith [hring, heq]
        rw [← hval]; exact hθ_j
    · -- Sum equality: s*(1+Θ')*(1+δ) + (∑ terms)*(1+δ) + last*(1+δ) = s*(1+Θ) + ∑(n+1) terms
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      have hsum_rw : ∑ i : Fin n, v i.castSucc * (1 + (θ' i + δ + θ' i * δ)) =
                     (∑ i : Fin n, v i.castSucc * (1 + θ' i)) * (1 + δ) := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      rw [hsum_rw]
      ring

end LeanFpAnalysis.FP
