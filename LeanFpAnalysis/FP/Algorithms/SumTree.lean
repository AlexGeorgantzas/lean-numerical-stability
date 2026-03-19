-- Algorithms/SumTree.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-!
# Summation Trees — Algorithm 4.1 (Higham §4.2)

A `SumTree n` is a binary tree whose `n` leaves are the summands and
whose internal nodes each perform one `fl_add`.  Any summation method
expressible as `n − 1` pairwise additions is an instance.

The key parameter is `depth`: the maximum number of additions any
single summand participates in.  The backward error per summand is
`γ(depth)`.  Specialisations:

- Chain tree (right-skewed): depth `n − 1` → recursive summation bound γ(n−1).
- Balanced tree: depth `r` for `n = 2ʳ` → pairwise summation bound γ(r).

This is the abstract framework behind Higham equations (4.2)–(4.6).
-/

-- ============================================================
-- Type
-- ============================================================

/-- A binary summation tree for `n` summands (Algorithm 4.1, Higham §4.2).
    `leaf` is a single summand; `node l r` computes `fl_add(sum_l, sum_r)`.
    A tree with `n` leaves performs exactly `n − 1` additions. -/
inductive SumTree : ℕ → Type where
  | leaf : SumTree 1
  | node : SumTree m → SumTree n → SumTree (m + n)

namespace SumTree

-- ============================================================
-- Structural properties
-- ============================================================

/-- Depth = max additions any single summand participates in. -/
def depth : SumTree n → ℕ
  | .leaf    => 0
  | .node l r => max l.depth r.depth + 1

/-- Number of additions performed (= number of internal nodes). -/
def numAdds : SumTree n → ℕ
  | .leaf    => 0
  | .node l r => l.numAdds + r.numAdds + 1

/-- Every `SumTree n` has `n ≥ 1`. -/
lemma n_pos : ∀ (_ : SumTree n), 0 < n := by
  intro t; induction t with
  | leaf => norm_num
  | node _ _ ihl ihr => omega

/-- A `SumTree n` performs exactly `n − 1` additions. -/
lemma numAdds_eq (t : SumTree n) : t.numAdds + 1 = n := by
  induction t with
  | leaf => simp [numAdds]
  | node l r ihl ihr => simp only [numAdds]; omega

/-- The depth of a `SumTree n` is at most `n − 1`. -/
lemma depth_le (t : SumTree n) : t.depth ≤ n - 1 := by
  induction t with
  | leaf => simp [depth]
  | node l r ihl ihr =>
    simp only [depth]
    have hl := n_pos l; have hr := n_pos r
    omega

-- ============================================================
-- Transport helpers
-- ============================================================

/-- Depth is invariant under index transport. -/
lemma depth_cast {m n : ℕ} (h : m = n) (t : SumTree m) :
    (h ▸ t).depth = t.depth := by
  subst h; rfl

-- ============================================================
-- Floating-point evaluation
-- ============================================================

/-- Evaluate a `SumTree` using floating-point arithmetic.
    Leaves map to vector entries; internal nodes call `fp.fl_add`. -/
noncomputable def eval (fp : FPModel) : SumTree n → (Fin n → ℝ) → ℝ
  | .leaf,     v => v ⟨0, by norm_num⟩
  | .node l r, v => fp.fl_add
      (eval fp l (fun i => v (Fin.castAdd _ i)))
      (eval fp r (fun i => v (Fin.natAdd _ i)))

/-- `eval` is invariant under index transport. -/
lemma eval_cast {m n : ℕ} (h : m = n) (fp : FPModel) (t : SumTree m) (v : Fin n → ℝ) :
    (h ▸ t).eval fp v = t.eval fp (fun i => v ⟨i.val, h ▸ i.isLt⟩) := by
  subst h; rfl

-- ============================================================
-- Backward error theorem (Algorithm 4.1, Higham §4.2)
-- ============================================================

/-- **Summation tree backward error** (Higham §4.2, equations 4.1–4.4).

    For any `SumTree n` with depth `d`, the computed sum satisfies:
      `t.eval fp v = ∑ i, v i * (1 + η i)`
    where each `|η i| ≤ γ(d)`.

    Specialises to eq. (4.4) for chain trees (d = n−1) and eq. (4.6)
    for balanced trees (d = r = log₂n).

    Proof: structural induction.  Leaf is exact; at each `node` the two IH
    witnesses are combined with the top-level rounding error `δ` via
    `gamma_mul`, giving per-summand error `ηL + δ + ηL·δ` bounded by
    `γ(l.depth + 1) ≤ γ(depth (node l r))`. -/
theorem backward_error (fp : FPModel) {n : ℕ} (t : SumTree n) :
    ∀ (_ : gammaValid fp t.depth) (v : Fin n → ℝ), ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp t.depth) ∧
      t.eval fp v = ∑ i : Fin n, v i * (1 + η i) := by
  induction t with
  | leaf =>
    intro ht v
    refine ⟨fun _ => 0, fun _ => ?_, by simp [eval]⟩
    simp only [abs_zero]; exact gamma_nonneg fp ht
  | node l r ihl ihr =>
    rename_i m k
    intro ht v
    simp only [depth] at ht
    -- gammaValid for subtrees
    have hml : l.depth ≤ max l.depth r.depth + 1 :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
    have hmr : r.depth ≤ max l.depth r.depth + 1 :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
    have ht_l  : gammaValid fp l.depth := gammaValid_mono fp hml ht
    have ht_r  : gammaValid fp r.depth := gammaValid_mono fp hmr ht
    have ht_1  : gammaValid fp 1       :=
      gammaValid_mono fp (Nat.succ_le_succ (Nat.zero_le _)) ht
    have ht_l1 : gammaValid fp (l.depth + 1) :=
      gammaValid_mono fp (Nat.add_le_add_right (Nat.le_max_left _ _) 1) ht
    have ht_r1 : gammaValid fp (r.depth + 1) :=
      gammaValid_mono fp (Nat.add_le_add_right (Nat.le_max_right _ _) 1) ht
    -- IH on left and right subtrees
    obtain ⟨ηL, hηL, hL⟩ := ihl ht_l (fun i => v (Fin.castAdd k i))
    obtain ⟨ηR, hηR, hR⟩ := ihr ht_r (fun i => v (Fin.natAdd m i))
    -- Rounding error from the top-level fl_add
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (l.eval fp (fun i => v (Fin.castAdd k i)))
        (r.eval fp (fun i => v (Fin.natAdd m i)))
    have hδ_1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos ht_1)
    -- Witness: per-element combined error using Fin.addCases
    refine ⟨Fin.addCases (fun i => ηL i + δ + ηL i * δ) (fun i => ηR i + δ + ηR i * δ),
            ?_, ?_⟩
    · -- Bound: ∀ i, |η i| ≤ γ(max l.depth r.depth + 1)
      intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [Fin.addCases_left]
        obtain ⟨e, he, heq⟩ := gamma_mul fp l.depth 1 (ηL j) δ (hηL j) hδ_1 ht_l1
        have hval : e = ηL j + δ + ηL j * δ := by
          linarith [heq, (by ring : (1 + ηL j) * (1 + δ) = 1 + (ηL j + δ + ηL j * δ))]
        rw [← hval]
        exact le_trans he (gamma_mono fp (Nat.add_le_add_right (Nat.le_max_left _ _) 1) ht)
      · intro j
        simp only [Fin.addCases_right]
        obtain ⟨e, he, heq⟩ := gamma_mul fp r.depth 1 (ηR j) δ (hηR j) hδ_1 ht_r1
        have hval : e = ηR j + δ + ηR j * δ := by
          linarith [heq, (by ring : (1 + ηR j) * (1 + δ) = 1 + (ηR j + δ + ηR j * δ))]
        rw [← hval]
        exact le_trans he (gamma_mono fp (Nat.add_le_add_right (Nat.le_max_right _ _) 1) ht)
    · -- Sum equality
      show fp.fl_add (l.eval fp fun i => v (Fin.castAdd k i))
                     (r.eval fp fun i => v (Fin.natAdd m i)) =
           ∑ i : Fin (m + k), v i * (1 + Fin.addCases (fun i => ηL i + δ + ηL i * δ)
                                                        (fun i => ηR i + δ + ηR i * δ) i)
      rw [hfl, hL, hR]
      conv_rhs => rw [Fin.sum_univ_add]
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl; intro i _
        simp only [Fin.addCases_left]; ring
      · apply Finset.sum_congr rfl; intro i _
        simp only [Fin.addCases_right]; ring

-- ============================================================
-- Forward error bound
-- ============================================================

/-- **Summation tree forward error bound** (Higham §4.2, eqs. 4.4 and 4.6).

    For any `SumTree n` with depth `d`:
      `|t.eval fp v − ∑ i, v i| ≤ γ(d) * ∑ i, |v i|`

    This is eq. (4.4) for chain trees and eq. (4.6) for balanced trees. -/
theorem forward_error (fp : FPModel) {n : ℕ} (t : SumTree n)
    (ht : gammaValid fp t.depth) (v : Fin n → ℝ) :
    |t.eval fp v - ∑ i : Fin n, v i| ≤ gamma fp t.depth * ∑ i : Fin n, |v i| := by
  obtain ⟨η, hη, hfold⟩ := backward_error fp t ht v
  have herr : t.eval fp v - ∑ i : Fin n, v i = ∑ i : Fin n, v i * η i := by
    rw [hfold, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [herr]
  calc |∑ i : Fin n, v i * η i|
      ≤ ∑ i : Fin n, |v i * η i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |v i| * |η i| := by
          apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
    _ ≤ ∑ i : Fin n, |v i| * gamma fp t.depth :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hη i) (abs_nonneg _)
    _ = gamma fp t.depth * ∑ i : Fin n, |v i| := by
          rw [← Finset.sum_mul, mul_comm]

-- ============================================================
-- Chain tree (recursive summation, depth n−1)
-- ============================================================

-- Private structural-recursion helper: `chainTree' n : SumTree (n + 1)`.
-- Uses bare constructor names (no `SumTree.` prefix) to avoid dot-notation ambiguity.
private def chainTree' : ∀ n : ℕ, SumTree (n + 1)
  | 0     => leaf
  | n + 1 => node (chainTree' n) leaf

private lemma chainTree'_depth : ∀ n : ℕ, (chainTree' n).depth = n
  | 0     => rfl
  | n + 1 => by
      simp only [chainTree', depth, chainTree'_depth n]
      omega

/-- Right-skewed chain tree: `(⋯((v₀ + v₁) + v₂)⋯ + vₙ₋₁)`.
    Depth = `n − 1` — the worst case.  This is the tree underlying
    recursive summation. -/
def chainTree (n : ℕ) (h : 0 < n) : SumTree n :=
  Nat.sub_add_cancel h ▸ chainTree' (n - 1)

/-- The chain tree has depth `n − 1`. -/
lemma chainTree_depth (n : ℕ) (h : 0 < n) : (chainTree n h).depth = n - 1 := by
  unfold chainTree
  rw [depth_cast, chainTree'_depth]

/-- **Chain tree backward error** (Higham §4.2, eq. 4.4 backward form).

    The chain tree for `n` summands has depth `n − 1`, giving the tight
    backward error bound γ(n−1) per summand. -/
theorem chainTree_backward_error (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (h : gammaValid fp (n - 1)) (v : Fin n → ℝ) :
    ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp (n - 1)) ∧
      (chainTree n hn).eval fp v = ∑ i : Fin n, v i * (1 + η i) := by
  have hd : (chainTree n hn).depth = n - 1 := chainTree_depth n hn
  have hd' : gammaValid fp (chainTree n hn).depth := by rw [hd]; exact h
  obtain ⟨η, hη, heq⟩ := backward_error fp (chainTree n hn) hd' v
  rw [hd] at hη
  exact ⟨η, hη, heq⟩

/-- **Chain tree forward error bound** (Higham §4.2, eq. 4.4). -/
theorem chainTree_forward_error (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (h : gammaValid fp (n - 1)) (v : Fin n → ℝ) :
    |(chainTree n hn).eval fp v - ∑ i : Fin n, v i| ≤
      gamma fp (n - 1) * ∑ i : Fin n, |v i| := by
  have hd : (chainTree n hn).depth = n - 1 := chainTree_depth n hn
  have hd' : gammaValid fp (chainTree n hn).depth := by rw [hd]; exact h
  have hfe := forward_error fp (chainTree n hn) hd' v
  rw [hd] at hfe
  exact hfe

-- ============================================================
-- Balanced tree (pairwise summation, depth r)
-- ============================================================

/-- Perfectly balanced binary tree for `2^r` summands.
    Depth = `r = log₂n`.  This is the tree underlying pairwise summation. -/
def balancedTree : ∀ (r : ℕ), SumTree (2 ^ r)
  | 0     => .leaf
  | r + 1 => (show 2 ^ r + 2 ^ r = 2 ^ (r + 1) from by ring) ▸
               .node (balancedTree r) (balancedTree r)

/-- The balanced tree has depth `r`. -/
lemma balancedTree_depth : ∀ r, (balancedTree r).depth = r := by
  intro r; induction r with
  | zero => simp [balancedTree, depth]
  | succ r ih =>
    simp only [balancedTree]
    rw [depth_cast]
    simp only [depth, ih]
    omega

/-- **Balanced tree backward error** (Higham §4.2, eq. 4.6 backward form).

    The balanced tree for `2^r` summands has depth `r`, giving the tight
    backward error bound `γ(r)` per summand (much smaller than `γ(n−1)`). -/
theorem balancedTree_backward_error (fp : FPModel) (r : ℕ)
    (h : gammaValid fp r) (v : Fin (2 ^ r) → ℝ) :
    ∃ η : Fin (2 ^ r) → ℝ,
      (∀ i, |η i| ≤ gamma fp r) ∧
      (balancedTree r).eval fp v = ∑ i : Fin (2 ^ r), v i * (1 + η i) := by
  have hd : (balancedTree r).depth = r := balancedTree_depth r
  have hd' : gammaValid fp (balancedTree r).depth := by rw [hd]; exact h
  obtain ⟨η, hη, heq⟩ := backward_error fp (balancedTree r) hd' v
  rw [hd] at hη
  exact ⟨η, hη, heq⟩

/-- **Balanced tree forward error bound** (Higham §4.2, eq. 4.6). -/
theorem balancedTree_forward_error (fp : FPModel) (r : ℕ)
    (h : gammaValid fp r) (v : Fin (2 ^ r) → ℝ) :
    |(balancedTree r).eval fp v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp r * ∑ i : Fin (2 ^ r), |v i| := by
  have hd : (balancedTree r).depth = r := balancedTree_depth r
  have hd' : gammaValid fp (balancedTree r).depth := by rw [hd]; exact h
  have hfe := forward_error fp (balancedTree r) hd' v
  rw [hd] at hfe
  exact hfe

end SumTree

end LeanFpAnalysis.FP
