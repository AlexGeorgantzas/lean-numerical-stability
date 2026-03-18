-- Algorithms/MatVec.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Error
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.Summation
import LeanFpAnalysis.FP.Analysis.Stability
import LeanFpAnalysis.FP.Algorithms.DotProduct

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-- Floating-point matrix-vector product ŷ = fl(Ax).

    Each output component ŷᵢ is computed as the floating-point inner product
    of the ith row of A with x (Higham §3.5, "sdot" / inner product form):
      ŷᵢ = fl_dotProduct fp n (A i) x

    This is the row-by-row accumulation matching Algorithm 3.1 applied m times. -/
noncomputable def fl_matVec (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => fl_dotProduct fp n (A i) x

/-- **Matrix-vector componentwise backward error** (Higham §3.5, equation 3.10).

    The computed matrix-vector product satisfies:
      ŷ = (A + ΔA)x,   |ΔA| ≤ γ(n)|A|  (componentwise)

    Formally: there exists ΔA : Fin m → Fin n → ℝ such that
      ∀ i j, |ΔA i j| ≤ γ(n) * |A i j|
      ∀ i, fl_matVec fp m n A x i = ∑ j, (A i j + ΔA i j) * x j

    Proof sketch: apply `dotProduct_backward_stable_x` to each row independently.
    The witness ΔA is constructed row-by-row via Classical.choose. -/
theorem matVec_backward_error (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n * |A i j|) ∧
      ∀ i, fl_matVec fp m n A x i = ∑ j : Fin n, (A i j + ΔA i j) * x j := by
  -- Extract per-row witnesses via Classical.choose
  let Δrow : Fin m → Fin n → ℝ :=
    fun i => Classical.choose (dotProduct_backward_stable_x fp n (A i) x hn)
  have hrow : ∀ i, (∀ j, |Δrow i j| ≤ gamma fp n * |A i j|) ∧
      fl_dotProduct fp n (A i) x = ∑ j : Fin n, (A i j + Δrow i j) * x j :=
    fun i => Classical.choose_spec (dotProduct_backward_stable_x fp n (A i) x hn)
  exact ⟨Δrow, fun i j => (hrow i).1 j, fun i => (hrow i).2⟩

/-- **Matrix-vector forward error bound** (Higham §3.5, equation 3.11).

    The componentwise forward error satisfies:
      |y - ŷ| ≤ γ(n)|A||x|  (componentwise)

    Formally: for each output component i,
      |fl_matVec fp m n A x i - ∑ j, A i j * x j| ≤ γ(n) * ∑ j, |A i j| * |x j|

    Proof sketch: apply `dotProduct_error_bound` to each row. -/
theorem matVec_error_bound (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ i : Fin m,
      |fl_matVec fp m n A x i - ∑ j : Fin n, A i j * x j| ≤
        gamma fp n * ∑ j : Fin n, |A i j| * |x j| :=
  fun i => dotProduct_error_bound fp n (A i) x hn

/-- **Matrix-vector row-wise backward stability** (Higham §3.5).

    Each row of `fl_matVec` is computed by `fl_dotProduct`, which is relatively
    componentwise backward stable with bound γ(n).  This theorem makes that
    explicit: the per-row inner product algorithm satisfies
    `isRelComponentwiseBackwardStable` with the row of A as the perturbed input.

    The global backward error for the full matrix (3.10) is captured by
    `matVec_backward_error`, which constructs a perturbation ΔA row-by-row. -/
theorem matVec_row_isRelBackwardStable (fp : FPModel) (n : ℕ)
    (hn : gammaValid fp n) :
    isRelComponentwiseBackwardStable n
      (fun a x => ∑ j : Fin n, a j * x j)
      (fun a x => fl_dotProduct fp n a x)
      (gamma fp n) :=
  dotProduct_isRelBackwardStable fp n hn

end LeanFpAnalysis.FP
