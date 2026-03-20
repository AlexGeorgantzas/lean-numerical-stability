-- Algorithms/RecursiveSum.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.Summation

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-- Floating-point recursive summation of `n` values.

    Computes `fl_add(... fl_add(fl_add(0, v 0), v 1) ..., v (n-1))`,
    left-to-right starting from the accumulator 0.

    This formalises the standard loop from Higham §4.1:
    ```
    s = 0
    for i = 1:n
      s = s + xᵢ
    end
    ``` -/
noncomputable def fl_recursiveSum (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0

/-- **Recursive summation backward error** (Higham §4.2, eq. 4.4).

    The computed recursive sum satisfies:
      `fl_recursiveSum fp n v = ∑ i, v i * (1 + θ i)`
    where each `|θ i| ≤ γ(n - 1)`.

    Backward result: the computed sum is the *exact* sum of perturbed
    inputs `vᵢ * (1 + θᵢ)`.  The bound γ(n-1) is tight: no number xᵢ
    participates in more than n - 1 additions (Higham §4.2).  The first
    step `fl_add 0 (v 0) = v 0` is exact by `fl_add_zero`, leaving only
    n - 1 rounding steps; this is captured via `fl_sum_error_tight`. -/
theorem recursiveSum_backward_error (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : gammaValid fp (n - 1)) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ gamma fp (n - 1)) ∧
      fl_recursiveSum fp n v = ∑ i : Fin n, v i * (1 + θ i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨Fin.elim0, fun i => i.elim0, by simp [fl_recursiveSum]⟩
  · exact fl_sum_error_tight fp n hpos v hn

/-- **Exact error decomposition** (Higham §4.2, eq. 4.2 — per-input form).

    Given backward error witnesses `θ` certifying
      `fl_recursiveSum fp n v = ∑ i, v i * (1 + θ i)`,
    the absolute error decomposes as:
      `fl_recursiveSum fp n v - ∑ i, v i = ∑ i, v i * θ i`

    This is the per-input counterpart of Higham's eq. (4.2), which writes the
    error as a sum of local contributions `δᵢ T̂ᵢ`.  It is the stepping stone
    from the backward error representation to the forward bound (4.4). -/
lemma recursiveSum_error_decomp (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (θ : Fin n → ℝ)
    (hfl : fl_recursiveSum fp n v = ∑ i : Fin n, v i * (1 + θ i)) :
    fl_recursiveSum fp n v - ∑ i : Fin n, v i = ∑ i : Fin n, v i * θ i := by
  rw [hfl, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

/-- **Recursive summation forward error bound** (Higham §4.2, equation 4.4).

    The absolute error of recursive summation satisfies:
      `|fl_recursiveSum fp n v - ∑ i, v i| ≤ γ(n - 1) * ∑ i, |v i|`

    This matches Higham's eq. (4.4) exactly: the constant is n - 1, not n,
    because the initial `fl_add 0 (v 0)` is exact (see `recursiveSum_backward_error`).

    Proof: from the backward form `∑ vᵢ(1+θᵢ)`, apply `recursiveSum_error_decomp`
    to get the error equals `∑ vᵢθᵢ`; triangle inequality + `|θᵢ| ≤ γ(n-1)` close. -/
theorem recursiveSum_forward_error_bound (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : gammaValid fp (n - 1)) :
    |fl_recursiveSum fp n v - ∑ i : Fin n, v i| ≤
      gamma fp (n - 1) * ∑ i : Fin n, |v i| := by
  obtain ⟨θ, hθ, hfold⟩ := recursiveSum_backward_error fp n v hn
  rw [recursiveSum_error_decomp fp n v θ hfold]
  calc |∑ i : Fin n, v i * θ i|
      ≤ ∑ i : Fin n, |v i * θ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |v i| * |θ i| := by
          apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
    _ ≤ ∑ i : Fin n, |v i| * gamma fp (n - 1) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hθ i) (abs_nonneg _)
    _ = gamma fp (n - 1) * ∑ i : Fin n, |v i| := by
          rw [← Finset.sum_mul, mul_comm]

-- ============================================================
-- Running error bound (Higham §4.2, equation 4.3)
-- ============================================================

/-- The sequence of pre-rounding pairwise sums during recursive summation.
    At step `i`, this is `fl_recursiveSum fp i.val (v ∘ castSucc...) + v i`,
    i.e., the exact sum of the accumulated result and the new element,
    before rounding. This matches the `ŝₖ` quantities in Higham eq. (4.3). -/
noncomputable def fl_partialSums (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fl_recursiveSum fp i.val (fun j => v ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) + v i

/-- **Recursive summation running error bound** (Higham §4.2, equation 4.3).

    The absolute error is bounded by `u` times the sum of absolute values of
    the pre-rounding pairwise sums at each step:
      `|fl_recursiveSum fp n v − ∑ i, v i| ≤ u * ∑ i, |fl_partialSums fp v i|`

    Here `fl_partialSums fp v i` is the exact sum `Ŝᵢ + vᵢ` just before
    rounding at step `i`, corresponding to Higham (4.3).

    Proof sketch: induction on n, peeling the last step.  At each step the
    error splits as `E_{n+1} = E_n + δ * (Ŝₙ + vₙ)` where `|δ| ≤ u` and
    `Ŝₙ + vₙ = fl_partialSums fp v (Fin.last n)`. -/
theorem recursiveSum_running_error_bound (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    |fl_recursiveSum fp n v - ∑ i : Fin n, v i| ≤
      fp.u * ∑ i : Fin n, |fl_partialSums fp v i| := by
  induction n with
  | zero => simp [fl_recursiveSum, fl_partialSums]
  | succ n ih =>
    -- Peel the last fold step
    have hfold : fl_recursiveSum fp (n + 1) v =
        fp.fl_add (fl_recursiveSum fp n (fun i => v i.castSucc)) (v (Fin.last n)) :=
      Fin.foldl_succ_last _ _
    -- Extract rounding error δ from the last fl_add
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (fl_recursiveSum fp n (fun i => v i.castSucc)) (v (Fin.last n))
    -- Abbreviations
    set Sn := fl_recursiveSum fp n (fun i => v i.castSucc)
    set vn := v (Fin.last n)
    -- Helper: two fl_recursiveSum calls with pointwise-equal functions are equal
    have reindex : ∀ (m : ℕ) (w₁ w₂ : Fin m → ℝ),
        (∀ j : Fin m, w₁ j = w₂ j) →
        fl_recursiveSum fp m w₁ = fl_recursiveSum fp m w₂ :=
      fun m w₁ w₂ h => by congr 1; funext j; exact h j
    -- The last pre-rounding pairwise sum equals Sn + vn
    have hlast : fl_partialSums fp v (Fin.last n) = Sn + vn := by
      unfold fl_partialSums
      -- (Fin.last n).val = n, and the fn arg equals (fun i => v i.castSucc)
      have hfn : fl_recursiveSum fp (Fin.last n).val
                   (fun j => v ⟨j.val, Nat.lt_trans j.isLt (Fin.last n).isLt⟩) = Sn :=
        reindex n _ _ (fun j => by congr 1)
      have hvn : v (Fin.last n) = vn := rfl
      rw [hfn, hvn]
    -- Compatibility: fl_partialSums fp v i.castSucc = fl_partialSums fp (v ∘ castSucc) i
    have hcompat : ∀ i : Fin n,
        fl_partialSums fp v i.castSucc = fl_partialSums fp (fun j => v j.castSucc) i := by
      intro i
      unfold fl_partialSums
      -- The recursive sum arguments are pointwise equal
      have hfn : fl_recursiveSum fp (Fin.castSucc i).val
                   (fun j => v ⟨j.val, Nat.lt_trans j.isLt (Fin.castSucc i).isLt⟩) =
                 fl_recursiveSum fp i.val
                   (fun j => (fun k : Fin n => v k.castSucc) ⟨j.val,
                     Nat.lt_trans j.isLt i.isLt⟩) := by
        simp only [Fin.val_castSucc]
        apply reindex
        intro j
        congr 1
      have hvn : v (Fin.castSucc i) = (fun k : Fin n => v k.castSucc) i := rfl
      rw [hfn, hvn]
    -- Error decomposition: E_{n+1} = E_n + δ * (Sn + vn)
    have herr : fl_recursiveSum fp (n + 1) v - ∑ i : Fin (n + 1), v i =
        (Sn - ∑ i : Fin n, v i.castSucc) + δ * (Sn + vn) := by
      rw [hfold, hfl, Fin.sum_univ_castSucc]; ring
    -- IH specialised to (v ∘ castSucc)
    have ih' := ih (fun i => v i.castSucc)
    -- Split the sum of partial sums
    have hpsum : ∑ i : Fin (n + 1), |fl_partialSums fp v i| =
        ∑ i : Fin n, |fl_partialSums fp (fun j => v j.castSucc) i| +
        |fl_partialSums fp v (Fin.last n)| := by
      rw [Fin.sum_univ_castSucc]
      congr 1
    -- Triangle inequality (using abs_le + linarith instead of unavailable abs_add)
    have htri : |(Sn - ∑ i : Fin n, v i.castSucc) + δ * (Sn + vn)| ≤
        |Sn - ∑ i : Fin n, v i.castSucc| + |δ * (Sn + vn)| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Sn - ∑ i : Fin n, v i.castSucc),
                  neg_abs_le (δ * (Sn + vn))]
      · linarith [le_abs_self (Sn - ∑ i : Fin n, v i.castSucc),
                  le_abs_self (δ * (Sn + vn))]
    -- Bound |δ * (Sn + vn)| ≤ fp.u * |fl_partialSums fp v (Fin.last n)|
    have hbound_last : |δ * (Sn + vn)| ≤ fp.u * |fl_partialSums fp v (Fin.last n)| := by
      rw [hlast, abs_mul]
      exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
    rw [herr, hpsum]
    calc |(Sn - ∑ i : Fin n, v i.castSucc) + δ * (Sn + vn)|
        ≤ |Sn - ∑ i : Fin n, v i.castSucc| + |δ * (Sn + vn)| := htri
      _ ≤ fp.u * ∑ i : Fin n, |fl_partialSums fp (fun j => v j.castSucc) i| +
            fp.u * |fl_partialSums fp v (Fin.last n)| := by linarith [ih', hbound_last]
      _ = fp.u * (∑ i : Fin n, |fl_partialSums fp (fun j => v j.castSucc) i| +
            |fl_partialSums fp v (Fin.last n)|) := by ring

end LeanFpAnalysis.FP
