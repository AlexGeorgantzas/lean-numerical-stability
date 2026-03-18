-- Algorithms/MatMul.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.MatVec

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-- Floating-point matrix-matrix product Ĉ = fl(AB).

    Computed column by column: each column j of Ĉ is the floating-point
    matrix-vector product of A with the jth column of B (Higham §3.5):
      Ĉ(:,j) = fl_matVec fp A B(:,j)

    This matches the "jik" and "jki" loop orderings Higham describes, which
    both compute C a column at a time and commit the same rounding errors as
    the standard triple-loop ordering. -/
noncomputable def fl_matMul (fp : FPModel) (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => fl_matVec fp m n A (fun k => B k j) i

/-- **Matrix-matrix forward error bound** (Higham §3.5, equation 3.12).

    The componentwise forward error satisfies:
      |C - Ĉ| ≤ γ(n)|A||B|  (componentwise)

    Formally: for each entry (i, j),
      |fl_matMul fp A B i j - ∑ k, A i k * B k j| ≤ γ(n) * ∑ k, |A i k| * |B k j|

    Proof: `fl_matMul fp A B i j` is by definition `fl_matVec fp A (B(:,j)) i`,
    so `matVec_error_bound` applies directly. -/
theorem matMul_error_bound (fp : FPModel) (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hn : gammaValid fp n) :
    ∀ i : Fin m, ∀ j : Fin p,
      |fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j| ≤
        gamma fp n * ∑ k : Fin n, |A i k| * |B k j| :=
  fun i j => matVec_error_bound fp m n A (fun k => B k j) hn i

/-- **Matrix-matrix columnwise backward error** (Higham §3.5).

    Each computed column of Ĉ is the exact result for a slightly perturbed A:
      ∀ j, ∃ ΔAⱼ, (∀ i k, |ΔAⱼ i k| ≤ γ(n) * |A i k|) ∧
                   ∀ i, Ĉ i j = ∑ k, (A i k + ΔAⱼ i k) * B k j

    **Important**: the perturbation ΔAⱼ depends on j — each column has its
    own backward error matrix.  There is no single ΔA that simultaneously
    explains all columns (Higham §3.5 explicitly notes this: "The same cannot
    be said for Ĉ as a whole").

    Proof: apply `matVec_backward_error` to each column independently. -/
theorem matMul_backward_error_col (fp : FPModel) (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hn : gammaValid fp n) :
    ∀ j : Fin p, ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i k, |ΔA i k| ≤ gamma fp n * |A i k|) ∧
      ∀ i, fl_matMul fp m n p A B i j = ∑ k : Fin n, (A i k + ΔA i k) * B k j :=
  fun j => matVec_backward_error fp m n A (fun k => B k j) hn

end LeanFpAnalysis.FP
