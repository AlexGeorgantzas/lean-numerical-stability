import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# HighamBench shared setting

This file is deliberately independent of the evaluated library.  It contains
only the small amount of notation needed to state the three P01 tasks in both
benchmark conditions.
-/

namespace HighamBench

open scoped BigOperators

/-- The part of the usual floating-point model needed for ordinary summation. -/
structure StandardAddModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add :
    ∀ x y : ℝ, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)

/-- The weaker addition rule used when the arithmetic has no guard digit. -/
structure NoGuardAddModel where
  u : ℝ
  u_pos : 0 < u
  fl_add : ℝ → ℝ → ℝ
  model_add :
    ∀ x y : ℝ, ∃ α β : ℝ,
      |α| ≤ u ∧
      |β| ≤ u ∧
      fl_add x y = x * (1 + α) + y * (1 + β)

/-- Higham's accumulated-error number `γₙ = n*u/(1-n*u)`. -/
noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

/-- The denominator in `gamma u n` is positive. -/
def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

/-- Embed an index into the left half of a vector of length `2^(r+1)`. -/
def leftIndex (r : ℕ) (i : Fin (2 ^ r)) : Fin (2 ^ (r + 1)) :=
  ⟨i.val, by
    have hi := i.isLt
    simp [pow_succ]
    omega⟩

/-- Embed an index into the right half of a vector of length `2^(r+1)`. -/
def rightIndex (r : ℕ) (i : Fin (2 ^ r)) : Fin (2 ^ (r + 1)) :=
  ⟨i.val + 2 ^ r, by
    have hi := i.isLt
    simp [pow_succ]
    omega⟩

/-- Balanced pairwise summation of exactly `2^r` inputs. -/
noncomputable def pairwiseSum (flAdd : ℝ → ℝ → ℝ) :
    (r : ℕ) → (Fin (2 ^ r) → ℝ) → ℝ
  | 0, v => v ⟨0, by norm_num⟩
  | r + 1, v =>
      flAdd
        (pairwiseSum flAdd r (fun i => v (leftIndex r i)))
        (pairwiseSum flAdd r (fun i => v (rightIndex r i)))

/-- Left-to-right recursive summation, with a one-element sum kept exact. -/
noncomputable def recursiveSum (flAdd : ℝ → ℝ → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then
        v ⟨0, by omega⟩
      else
        flAdd
          (recursiveSum flAdd n (fun i => v i.castSucc))
          (v (Fin.last n))

/-- The right side of Higham (1993), equation (5.3), without the leading `u`.

For inputs `x₁, ..., xₙ`, this is

`(|Ŝ₁| + |x₂|) + ... + (|Ŝₙ₋₁| + |xₙ|)`,

where `Ŝₖ` is the computed recursive sum of the first `k` inputs. The
recursive definition follows the same last-step split as `recursiveSum`. -/
noncomputable def noGuardRecursiveRunningBudget (fp : NoGuardAddModel) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      if n = 0 then
        0
      else
        noGuardRecursiveRunningBudget fp n (fun i => v i.castSucc) +
          |recursiveSum fp.fl_add n (fun i => v i.castSucc)| +
          |v (Fin.last n)|

end HighamBench
