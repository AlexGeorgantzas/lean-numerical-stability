-- Algorithms/DotProduct.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Error
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.Summation

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-- Floating-point dot product of two n-dimensional vectors.

    Models Higham's sequential accumulation (Algorithm 3.1):
      ŝ₁    = fl_mul (x 0) (y 0)
      ŝᵢ₊₁ = fl_add ŝᵢ (fl_mul (x i) (y i)),  i = 1, …, n-1

    Starting from the first rounded product (rather than 0) avoids the
    spurious extra rounding error that would arise from fl_add(0, fl_mul …),
    allowing the tight γₙ bound of Higham §3.5. -/
noncomputable def fl_dotProduct (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0      => 0
  | n' + 1 =>
      Fin.foldl n' (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

/-- **Dot product rounding error bound** (Higham §3.5, tight bound).

    The computed floating-point dot product satisfies:
      |fl_dotProduct fp x y - ∑ i, x i * y i| ≤ γ(n) * ∑ i, |x i| * |y i|

    Proof sketch:
      1. For n = 0 the result is trivial.
      2. For n = n'+1, extract mul rounding errors: fl_mul (x i) (y i) = x i * y i * (1 + δ i)
         with |δ i| ≤ u ≤ γ(1).
      3. Apply fl_sum_error_init to the n' accumulated additions starting from
         fl_mul (x 0) (y 0) with initial-accumulator error Θ and per-term errors θ i,
         all bounded by γ(n').
      4. Combine each pair (δ i, Θ or θ i) via gamma_mul to get a single error η i
         with |η i| ≤ γ(n'+1) = γ(n).
      5. Total error is ∑ x i * y i * η i; apply triangle inequality to get the bound. -/
theorem dotProduct_error_bound (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ)
    (hn : gammaValid fp n) :
    |fl_dotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      gamma fp n * ∑ i : Fin n, |x i| * |y i| := by
  cases n with
  | zero => simp [fl_dotProduct]
  | succ n' =>
    -- gammaValid helpers
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
    have hn' : gammaValid fp n' := gammaValid_mono fp (Nat.le_succ n') hn
    -- mul rounding errors for all n'+1 terms
    let δ : Fin (n' + 1) → ℝ := fun i => Classical.choose (fp.model_mul (x i) (y i))
    have hδ : ∀ i, |δ i| ≤ fp.u ∧ fp.fl_mul (x i) (y i) = x i * y i * (1 + δ i) :=
      fun i => Classical.choose_spec (fp.model_mul (x i) (y i))
    have hδ_1 : ∀ i, |δ i| ≤ gamma fp 1 :=
      fun i => le_trans (hδ i).1 (u_le_gamma fp one_pos h1valid)
    -- apply fl_sum_error_init to the n' additions starting from fl_mul (x 0) (y 0)
    obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ :=
      fl_sum_error_init fp n' (fun i => fp.fl_mul (x i.succ) (y i.succ))
        (fp.fl_mul (x 0) (y 0)) hn'
    -- expand fl_dotProduct
    have hdot : fl_dotProduct fp (n' + 1) x y =
        x 0 * y 0 * (1 + δ 0) * (1 + Θ) +
        ∑ i : Fin n', x i.succ * y i.succ * (1 + δ i.succ) * (1 + θ i) := by
      show Fin.foldl n' (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
          (fp.fl_mul (x 0) (y 0)) = _
      rw [hfold, (hδ 0).2]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      rw [(hδ i.succ).2]
    -- combined errors: η₀ for term 0, ηs i for term i.succ
    let η₀ : ℝ := δ 0 + Θ + δ 0 * Θ
    let ηs : Fin n' → ℝ := fun i => δ i.succ + θ i + δ i.succ * θ i
    -- |η₀| ≤ γ(n'+1)
    have hη₀ : |η₀| ≤ gamma fp (n' + 1) := by
      obtain ⟨η, hη, heq⟩ := gamma_mul fp n' 1 Θ (δ 0) hΘ (hδ_1 0) hn
      have hval : η = η₀ := by
        have hring : (1 + Θ) * (1 + δ 0) = 1 + η₀ := by simp only [η₀]; ring
        linarith [heq, hring]
      rw [← hval]; exact hη
    -- |ηs i| ≤ γ(n'+1) for each i
    have hηs : ∀ i, |ηs i| ≤ gamma fp (n' + 1) := fun i => by
      obtain ⟨η, hη, heq⟩ := gamma_mul fp n' 1 (θ i) (δ i.succ) (hθ i) (hδ_1 i.succ) hn
      have hval : η = ηs i := by
        have hring : (1 + θ i) * (1 + δ i.succ) = 1 + ηs i := by simp only [ηs]; ring
        linarith [heq, hring]
      rw [← hval]; exact hη
    -- the total error equals x 0 * y 0 * η₀ + ∑ x i.succ * y i.succ * ηs i
    have herr : fl_dotProduct fp (n' + 1) x y - ∑ i : Fin (n' + 1), x i * y i =
        x 0 * y 0 * η₀ + ∑ i : Fin n', x i.succ * y i.succ * ηs i := by
      rw [hdot, Fin.sum_univ_succ]
      have hzero : x 0 * y 0 * (1 + δ 0) * (1 + Θ) - x 0 * y 0 = x 0 * y 0 * η₀ := by
        simp only [η₀]; ring
      have hsucc : ∑ i : Fin n', x i.succ * y i.succ * (1 + δ i.succ) * (1 + θ i) -
                   ∑ i : Fin n', x i.succ * y i.succ =
                   ∑ i : Fin n', x i.succ * y i.succ * ηs i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro i _
        show x i.succ * y i.succ * (1 + δ i.succ) * (1 + θ i) - x i.succ * y i.succ =
             x i.succ * y i.succ * ηs i
        simp only [ηs]; ring
      linarith [hzero, hsucc]
    rw [herr]
    calc |x 0 * y 0 * η₀ + ∑ i : Fin n', x i.succ * y i.succ * ηs i|
        ≤ |x 0 * y 0 * η₀| + |∑ i : Fin n', x i.succ * y i.succ * ηs i| := by
              rw [abs_le]; constructor <;>
              linarith [le_abs_self (x 0 * y 0 * η₀),
                        le_abs_self (∑ i : Fin n', x i.succ * y i.succ * ηs i),
                        neg_abs_le (x 0 * y 0 * η₀),
                        neg_abs_le (∑ i : Fin n', x i.succ * y i.succ * ηs i)]
      _ ≤ |x 0 * y 0 * η₀| + ∑ i : Fin n', |x i.succ * y i.succ * ηs i| :=
              add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
      _ = |x 0| * |y 0| * |η₀| + ∑ i : Fin n', |x i.succ| * |y i.succ| * |ηs i| := by
              simp only [abs_mul]
      _ ≤ |x 0| * |y 0| * gamma fp (n' + 1) +
          ∑ i : Fin n', |x i.succ| * |y i.succ| * gamma fp (n' + 1) :=
              add_le_add
                (mul_le_mul_of_nonneg_left hη₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
                (Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_left (hηs i) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      _ = gamma fp (n' + 1) * ∑ i : Fin (n' + 1), |x i| * |y i| := by
              rw [Fin.sum_univ_succ, ← Finset.sum_mul]; ring

end LeanFpAnalysis.FP
