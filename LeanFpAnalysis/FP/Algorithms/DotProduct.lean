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

    Models the standard sequential accumulation:
      acc₀     = 0
      accᵢ₊₁  = fl_add accᵢ (fl_mul (x i) (y i))

    Each step introduces up to two rounding errors (one from fl_mul,
    one from fl_add), giving 2n total rounding operations for an
    n-dimensional dot product. -/
noncomputable def fl_dotProduct (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0

/-- **Dot product rounding error bound** (Higham §3.5).

    The computed floating-point dot product satisfies:
      |fl_dotProduct fp x y - ∑ i, x i * y i| ≤ γ(2n) * ∑ i, |x i| * |y i|

    Proof sketch:
      1. Apply model_mul to each fl_mul (x i) (y i): each rounded product
         equals x i * y i * (1 + δ i) for some |δ i| ≤ u.
      2. Apply fl_sum_error to the accumulated additions, yielding
         fl_dotProduct = ∑ i, fl_mul(x i)(y i) * (1 + θ i) for some
         |θ i| ≤ γ(n).
      3. Substitute: fl_dotProduct = ∑ i, x i * y i * (1 + δ i)(1 + θ i).
         Setting η i = δ i + θ i + δ i * θ i gives (1 + δ i)(1 + θ i) = 1 + η i.
      4. Bound |η i| ≤ γ(n+1) ≤ γ(2n) via gamma_mul fp 1 n with
         |δ i| ≤ u ≤ γ(1) and |θ i| ≤ γ(n).  (n ≥ 1 follows from i : Fin n.)
      5. fl_dotProduct - ∑ x y = ∑ x i * y i * η i; apply triangle inequality
         and Σ |x i||y i||η i| ≤ γ(2n) * Σ |x i||y i|. -/
theorem dotProduct_error_bound (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ)
    (hn : gammaValid fp (2 * n)) :
    |fl_dotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      gamma fp (2 * n) * ∑ i : Fin n, |x i| * |y i| := by
  -- gammaValid for n (n ≤ 2n)
  have hn_n : gammaValid fp n := gammaValid_mono fp (by omega) hn
  -- Step 1: extract mul rounding errors δ i via classical choice
  let δ : Fin n → ℝ := fun i => Classical.choose (fp.model_mul (x i) (y i))
  have hδ_spec : ∀ i, |δ i| ≤ fp.u ∧ fp.fl_mul (x i) (y i) = x i * y i * (1 + δ i) :=
    fun i => Classical.choose_spec (fp.model_mul (x i) (y i))
  -- Step 2: apply fl_sum_error to the rounded products
  obtain ⟨θ, hθ, hfold⟩ :=
    fl_sum_error fp n (fun i => fp.fl_mul (x i) (y i)) hn_n
  -- Step 3: expand fl_dotProduct as ∑ x i * y i * (1 + δ i) * (1 + θ i)
  have hdot : fl_dotProduct fp n x y =
      ∑ i : Fin n, x i * y i * (1 + δ i) * (1 + θ i) := by
    unfold fl_dotProduct
    rw [hfold]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hδ_spec i).2]
  -- Step 4: combined error η i = δ i + θ i + δ i * θ i
  let η : Fin n → ℝ := fun i => δ i + θ i + δ i * θ i
  have hη_bound : ∀ i, |η i| ≤ gamma fp (2 * n) := by
    intro i
    -- n ≥ 1 since i : Fin n is inhabited
    have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hn1 : gammaValid fp (n + 1) := gammaValid_mono fp (by omega) hn
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn1
    have hδ1 : |δ i| ≤ gamma fp 1 :=
      le_trans (hδ_spec i).1 (u_le_gamma fp one_pos h1valid)
    obtain ⟨η_val, hη_val, heq⟩ := gamma_mul fp n 1 (θ i) (δ i) (hθ i) hδ1 hn1
    have hval : η_val = η i := by
      have hring : (1 + θ i) * (1 + δ i) = 1 + η i := by ring
      linarith [heq, hring]
    calc |η i| = |η_val| := by rw [hval]
      _ ≤ gamma fp (n + 1) := hη_val
      _ ≤ gamma fp (2 * n) := gamma_mono fp (by omega) hn
  -- Step 5: the error equals ∑ x i * y i * η i
  have herr : fl_dotProduct fp n x y - ∑ i : Fin n, x i * y i =
      ∑ i : Fin n, x i * y i * η i := by
    rw [hdot, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- Step 6: triangle inequality and constant bound
  rw [herr]
  have hγ2n : 0 ≤ gamma fp (2 * n) := gamma_nonneg fp hn
  calc |∑ i : Fin n, x i * y i * η i|
      ≤ ∑ i : Fin n, |x i * y i * η i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |x i| * |y i| * |η i| := by
          apply Finset.sum_congr rfl; intro i _
          rw [abs_mul, abs_mul]
    _ ≤ ∑ i : Fin n, |x i| * |y i| * gamma fp (2 * n) := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_left (hη_bound i)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = gamma fp (2 * n) * ∑ i : Fin n, |x i| * |y i| := by
          rw [← Finset.sum_mul, mul_comm]

end LeanFpAnalysis.FP
