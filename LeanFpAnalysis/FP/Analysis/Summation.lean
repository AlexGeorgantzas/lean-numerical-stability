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

end LeanFpAnalysis.FP
