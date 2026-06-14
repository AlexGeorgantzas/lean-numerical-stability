-- Algorithms/MatMulBackwardError.lean
--
-- Higham Chapter 3, Problem 3.6.

import Mathlib.Tactic.Linarith
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-!
# Matrix-Multiplication Backward-Error Definitions

Higham Chapter 3, Problem 3.6 studies componentwise backward errors for
matrix multiplication and asks for the residual lower bound

`omega >= max_ij (sqrt (1 + |r_ij| / g_ij) - 1)`,

where `R = C - A*B` and `G = |A|*|B|` in the relative componentwise case.
The theorem below proves the pointwise form: every feasible relative
backward-error radius `epsilon` is at least the displayed lower bound.

The file also exposes a mixed backward/forward feasibility predicate, which is
the natural general-rank replacement when exact factor perturbations alone
need not exist.
-/

/-- Residual matrix `R = C - A*B` for a rectangular product. -/
noncomputable def matMulResidual (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (C : Fin m → Fin p → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => C i j - ∑ k : Fin n, A i k * B k j

/-- Relative componentwise product majorant `G = |A| |B|`. -/
noncomputable def matMulRelativeMajorant (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ) :
    Fin m → Fin p → ℝ :=
  fun i j => ∑ k : Fin n, |A i k| * |B k j|

/-- Feasibility of a relative componentwise backward error for matrix
multiplication:

`C = (A + DeltaA)(B + DeltaB)`, with
`|DeltaA| <= epsilon |A|` and `|DeltaB| <= epsilon |B|`.

This is the source lower-bound setting specialized to the relative
componentwise majorants. -/
def matMulRelativeBackwardFeasible (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (C : Fin m → Fin p → ℝ) (epsilon : ℝ) : Prop :=
  ∃ ΔA : Fin m → Fin n → ℝ, ∃ ΔB : Fin n → Fin p → ℝ,
    (∀ i k, |ΔA i k| ≤ epsilon * |A i k|) ∧
    (∀ k j, |ΔB k j| ≤ epsilon * |B k j|) ∧
    ∀ i j, C i j = ∑ k : Fin n, (A i k + ΔA i k) * (B k j + ΔB k j)

/-- Mixed backward/forward feasibility for matrix multiplication.

For general rank-deficient inputs, exact representation only as
`(A + DeltaA)(B + DeltaB)` can be ill-posed or impossible.  This predicate
allows a forward residual `DeltaC` as well:

`C + DeltaC = (A + DeltaA)(B + DeltaB)`,

with componentwise budgets for `DeltaA`, `DeltaB`, and `DeltaC`. -/
def matMulMixedBackwardForwardFeasible (m n p : ℕ)
    (A E : Fin m → Fin n → ℝ) (B F : Fin n → Fin p → ℝ)
    (C H : Fin m → Fin p → ℝ) (epsilon : ℝ) : Prop :=
  ∃ ΔA : Fin m → Fin n → ℝ, ∃ ΔB : Fin n → Fin p → ℝ,
    ∃ ΔC : Fin m → Fin p → ℝ,
      (∀ i k, |ΔA i k| ≤ epsilon * E i k) ∧
      (∀ k j, |ΔB k j| ≤ epsilon * F k j) ∧
      (∀ i j, |ΔC i j| ≤ epsilon * H i j) ∧
      ∀ i j,
        C i j + ΔC i j =
          ∑ k : Fin n, (A i k + ΔA i k) * (B k j + ΔB k j)

/-- **Problem 3.6 residual majorant.**

Every feasible relative componentwise backward-error radius `epsilon`
satisfies

`|R_ij| <= ((1 + epsilon)^2 - 1) G_ij`,

where `R = C - A*B` and `G = |A|*|B|`. -/
theorem matMulRelativeBackwardFeasible_residual_entry_le (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (C : Fin m → Fin p → ℝ) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hfeas : matMulRelativeBackwardFeasible m n p A B C epsilon) :
    ∀ i j,
      |matMulResidual m n p A B C i j| ≤
        ((1 + epsilon) ^ 2 - 1) *
          matMulRelativeMajorant m n p A B i j := by
  rcases hfeas with ⟨ΔA, ΔB, hΔA, hΔB, hC⟩
  intro i j
  have hcoef_nonneg : 0 ≤ 2 * epsilon + epsilon ^ 2 := by
    nlinarith [hepsilon, sq_nonneg epsilon]
  have hcoef_eq : ((1 + epsilon) ^ 2 - 1) = 2 * epsilon + epsilon ^ 2 := by
    ring
  have hres_sum :
      matMulResidual m n p A B C i j =
        ∑ k : Fin n,
          (A i k * ΔB k j + ΔA i k * B k j + ΔA i k * ΔB k j) := by
    simp [matMulResidual, hC i j]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hterm :
      ∀ k : Fin n,
        |A i k * ΔB k j + ΔA i k * B k j + ΔA i k * ΔB k j| ≤
          (2 * epsilon + epsilon ^ 2) * (|A i k| * |B k j|) := by
    intro k
    have hAabs : 0 ≤ |A i k| := abs_nonneg _
    have hBabs : 0 ≤ |B k j| := abs_nonneg _
    have hDA_nonneg : 0 ≤ epsilon * |A i k| := mul_nonneg hepsilon hAabs
    have hDB_nonneg : 0 ≤ epsilon * |B k j| := mul_nonneg hepsilon hBabs
    calc
      |A i k * ΔB k j + ΔA i k * B k j + ΔA i k * ΔB k j|
          ≤ |A i k * ΔB k j| + |ΔA i k * B k j| + |ΔA i k * ΔB k j| := by
            calc
              |A i k * ΔB k j + ΔA i k * B k j + ΔA i k * ΔB k j|
                  ≤ |A i k * ΔB k j + ΔA i k * B k j| +
                      |ΔA i k * ΔB k j| := abs_add_le _ _
              _ ≤ |A i k * ΔB k j| + |ΔA i k * B k j| +
                      |ΔA i k * ΔB k j| := by
                    nlinarith [abs_add_le (A i k * ΔB k j) (ΔA i k * B k j)]
      _ = |A i k| * |ΔB k j| + |ΔA i k| * |B k j| +
            |ΔA i k| * |ΔB k j| := by
            rw [abs_mul, abs_mul, abs_mul]
      _ ≤ |A i k| * (epsilon * |B k j|) +
            (epsilon * |A i k|) * |B k j| +
            (epsilon * |A i k|) * (epsilon * |B k j|) := by
            exact add_le_add
              (add_le_add
                (mul_le_mul_of_nonneg_left (hΔB k j) hAabs)
                (mul_le_mul_of_nonneg_right (hΔA i k) hBabs))
              (mul_le_mul (hΔA i k) (hΔB k j) (abs_nonneg _) hDA_nonneg)
      _ = (2 * epsilon + epsilon ^ 2) * (|A i k| * |B k j|) := by
            ring
  calc
    |matMulResidual m n p A B C i j|
        = |∑ k : Fin n,
            (A i k * ΔB k j + ΔA i k * B k j + ΔA i k * ΔB k j)| := by
            rw [hres_sum]
    _ ≤ ∑ k : Fin n,
          |A i k * ΔB k j + ΔA i k * B k j + ΔA i k * ΔB k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n,
          (2 * epsilon + epsilon ^ 2) * (|A i k| * |B k j|) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ =
        (2 * epsilon + epsilon ^ 2) *
          matMulRelativeMajorant m n p A B i j := by
        simp [matMulRelativeMajorant, Finset.mul_sum]
    _ =
        ((1 + epsilon) ^ 2 - 1) *
          matMulRelativeMajorant m n p A B i j := by
        rw [hcoef_eq]

/-- **Problem 3.6 square-root lower bound, pointwise form.**

If a relative componentwise backward-error radius `epsilon` is feasible and
the source majorant entry `g_ij` is positive, then

`sqrt (1 + |r_ij| / g_ij) - 1 <= epsilon`.

Taking the maximum over all entries gives the displayed lower bound for the
minimal feasible radius `omega`. -/
theorem matMulRelativeBackwardFeasible_sqrt_lower_bound_entry (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (C : Fin m → Fin p → ℝ) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hfeas : matMulRelativeBackwardFeasible m n p A B C epsilon)
    (i : Fin m) (j : Fin p)
    (hg : 0 < matMulRelativeMajorant m n p A B i j) :
    Real.sqrt
          (1 + |matMulResidual m n p A B C i j| /
            matMulRelativeMajorant m n p A B i j) -
        1 ≤
      epsilon := by
  let g := matMulRelativeMajorant m n p A B i j
  let r := matMulResidual m n p A B C i j
  have hentry :=
    matMulRelativeBackwardFeasible_residual_entry_le m n p A B C hepsilon hfeas i j
  have hratio :
      |r| / g ≤ ((1 + epsilon) ^ 2 - 1) := by
    have hg_nonneg : 0 ≤ g := le_of_lt hg
    exact (div_le_iff₀ hg).mpr (by simpa [r, g, mul_comm] using hentry)
  have hone_ratio :
      1 + |r| / g ≤ (1 + epsilon) ^ 2 := by
    nlinarith
  have hleft_nonneg : 0 ≤ 1 + |r| / g := by
    have hratio_nonneg : 0 ≤ |r| / g := div_nonneg (abs_nonneg _) (le_of_lt hg)
    nlinarith
  have hsqrt :
      Real.sqrt (1 + |r| / g) ≤ 1 + epsilon := by
    have hsquare :=
      Real.sqrt_le_sqrt hone_ratio
    have hone_epsilon_nonneg : 0 ≤ 1 + epsilon := by
      nlinarith
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hone_epsilon_nonneg] using hsquare
  nlinarith

end LeanFpAnalysis.FP
