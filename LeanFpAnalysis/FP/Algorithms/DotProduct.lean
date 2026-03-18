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
         fl_mul (x 0) (y 0), giving fl_dotProduct = fl_mul(x 0)(y 0) * (1+Θ) + ∑ i≥1 fl_mul(x i)(y i) * (1+θ i)
         with |Θ|, |θ i| ≤ γ(n').
      4. Substitute fl_mul expressions: each term becomes x i * y i * (1+δ i) * (1+ηᵢ)
         where ηᵢ is either Θ or θ i.  Combine via gamma_mul: |(1+δ i)(1+ηᵢ)-1| ≤ γ(n).
      5. The total error ∑ x i * y i * combined_i satisfies the bound via the
         triangle inequality and γ(n) * ∑ |x i||y i|. -/
theorem dotProduct_error_bound (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ)
    (hn : gammaValid fp n) :
    |fl_dotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      gamma fp n * ∑ i : Fin n, |x i| * |y i| := by
  sorry

end LeanFpAnalysis.FP
