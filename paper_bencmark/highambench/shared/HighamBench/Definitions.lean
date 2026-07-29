import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# HighamBench shared setting

This file is deliberately independent of the evaluated library.  It contains
only the small amount of notation needed to state the P01 and P02 tasks in
both benchmark conditions.
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

/-! ## Ogita--Rump--Oishi error-free transformations

The P02 tasks use only the mathematical contracts of `TwoSum` and
`TwoProduct` that the paper establishes before analyzing `VecSum`, `Sum2`, and
`DotK`.  Keeping those contracts abstract avoids building IEEE-754 machinery
into the fixed statements and gives conditions N and L the same small model.
-/

/-- A standard rounded-addition model equipped with an error-free `TwoSum`.

The first component is the rounded sum.  The two components add to the exact
real sum, and the low component obeys the residual estimate used in Lemma 4.2
of Ogita--Rump--Oishi (2005). -/
structure ErrorFreeAddModel extends StandardAddModel where
  twoSum : ℝ → ℝ → ℝ × ℝ
  twoSum_high :
    ∀ a b : ℝ, (twoSum a b).1 = fl_add a b
  twoSum_exact :
    ∀ a b : ℝ, (twoSum a b).1 + (twoSum a b).2 = a + b
  twoSum_low_le :
    ∀ a b : ℝ, |(twoSum a b).2| ≤ u * |(twoSum a b).1|

/-- Main value after `k` successive `TwoSum` operations, starting with the
first entry of a nonempty vector. -/
noncomputable def twoSumPrefix (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) : ℝ :=
  Fin.foldl k
    (fun s i =>
      (fp.twoSum s
        (v ⟨i.val + 1,
          Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩)).1)
    (v ⟨0, Nat.succ_pos n⟩)

/-- The low component emitted at step `i+1` of the `VecSum` cascade. -/
noncomputable def twoSumCorrection (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  (fp.twoSum
    (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
    (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).2

/-- Algorithm 4.3 (`VecSum`): the `n` emitted low components followed by the
final high component.  The input and output both have length `n+1`. -/
noncomputable def vecSum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases
    (twoSumPrefix fp v n (Nat.le_refl n))
    (twoSumCorrection fp v)

/-- Apply `VecSum` exactly `k` times. -/
noncomputable def iteratedVecSum (fp : ErrorFreeAddModel) {n : ℕ}
    (k : ℕ) (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  match k with
  | 0 => v
  | k + 1 => vecSum fp (iteratedVecSum fp k v)

/-- Algorithm 4.8 (`SumK`): apply `VecSum` `K-1` times and recursively sum the
result in working precision. -/
noncomputable def sumK (fp : ErrorFreeAddModel) {n : ℕ}
    (K : ℕ) (v : Fin (n + 1) → ℝ) : ℝ :=
  recursiveSum fp.fl_add (n + 1) (iteratedVecSum fp (K - 1) v)

/-- Algorithm 4.4 (`Sum2`), the `K = 2` instance of `SumK`. -/
noncomputable def sum2 (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) : ℝ :=
  sumK fp 2 v

/-- The no-multiplication-underflow contract used for the P02 `DotK` task.

The two product components add exactly to `a*b`, and the low component is at
most unit roundoff times the exact product.  This is the minimal part of
Theorem 3.4 needed for the transformed-vector absolute-mass estimate. -/
structure ErrorFreeDotModel extends ErrorFreeAddModel where
  twoProduct : ℝ → ℝ → ℝ × ℝ
  twoProduct_exact :
    ∀ a b : ℝ, (twoProduct a b).1 + (twoProduct a b).2 = a * b
  twoProduct_low_le_exact :
    ∀ a b : ℝ, |(twoProduct a b).2| ≤ u * |a * b|

/-- Exact real dot product of two nonempty vectors. -/
noncomputable def exactDot {n : ℕ} (x y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), x i * y i

/-- Componentwise absolute mass `|x|ᵀ|y|` of a dot product. -/
noncomputable def dotMagnitude {n : ℕ} (x y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), |x i| * |y i|

/-- The length-`2*(n+1)` vector passed to `SumK` in Algorithm 5.10.

Its first half contains the low parts from `TwoProduct`; its second half is
`VecSum` applied to the product high parts, hence contains the addition lows
and the final high component. -/
noncomputable def dotKTransform (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) : Fin ((2 * n + 1) + 1) → ℝ :=
  fun j =>
    Fin.addCases
      (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).2)
      (vecSum fp.toErrorFreeAddModel
        (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1))
      (Fin.cast (by omega) j)

/-- Algorithm 5.10 (`DotK`): transform the products and call `SumK` with
precision parameter `K-1`. -/
noncomputable def dotK (fp : ErrorFreeDotModel) {n : ℕ}
    (K : ℕ) (x y : Fin (n + 1) → ℝ) : ℝ :=
  sumK fp.toErrorFreeAddModel (K - 1) (dotKTransform fp x y)

end HighamBench
