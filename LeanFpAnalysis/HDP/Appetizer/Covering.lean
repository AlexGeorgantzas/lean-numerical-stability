import LeanFpAnalysis.HDP.Geometry.Convex
import LeanFpAnalysis.HDP.Combinatorics.Binomial
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Vector.Basic

/-!
# Covering Polytopes by Empirical Averages

This file formalizes the covering consequence of approximate Caratheodory from
Vershynin's HDP appetizer.
-/

open scoped BigOperators

namespace LeanFpAnalysis.HDP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Centers obtained by averaging `k` vertices, with repetition allowed. -/
noncomputable def empiricalCenters (V : Finset E) (k : ℕ) : Set E :=
  Set.range fun f : Fin k → V => empiricalAverage fun j : Fin k => (f j : E)

lemma mem_empiricalCenters_iff {V : Finset E} {k : ℕ} {c : E} :
    c ∈ empiricalCenters V k ↔
      ∃ f : Fin k → V, empiricalAverage (fun j : Fin k => (f j : E)) = c := by
  rfl

lemma empiricalCenters_ncard_le (V : Finset E) (k : ℕ) :
    (empiricalCenters V k).ncard ≤ V.card ^ k := by
  classical
  calc
    (empiricalCenters V k).ncard ≤ Nat.card (Fin k → V) := by
      let F : (Fin k → V) → E := fun f => empiricalAverage fun j : Fin k => (f j : E)
      have hle : (Set.range F).ncard ≤ (Set.univ : Set (Fin k → V)).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le (s := (Set.univ : Set (Fin k → V))) (f := F)
      simpa [empiricalCenters, F] using hle
    _ = Fintype.card (Fin k → V) := Nat.card_eq_fintype_card
    _ = V.card ^ k := by
      rw [Fintype.card_pi_const, Fintype.card_coe]

omit [InnerProductSpace ℝ E] in
lemma list_ofFn_subtype_sum {V : Finset E} :
    ∀ {k : ℕ} (f : Fin k → V),
      (List.ofFn f).unattach.sum = ∑ x, (f x : E)
  | 0, _ => by simp
  | k + 1, f => by
      rw [List.ofFn_succ]
      rw [Fin.sum_univ_succ]
      simp [list_ofFn_subtype_sum (fun i : Fin k => f i.succ)]

/-- Average of an unordered `k`-tuple of vertices. -/
noncomputable def symAverage {V : Finset E} {k : ℕ} (s : Sym V k) : E :=
  ((k : ℝ)⁻¹) • ((s : Multiset V).map (fun v : V => (v : E))).sum

lemma symAverage_ofFn {V : Finset E} {k : ℕ} (f : Fin k → V) :
    symAverage ((List.Vector.ofFn f : List.Vector V k) : Sym V k) =
      empiricalAverage (fun j : Fin k => (f j : E)) := by
  unfold symAverage empiricalAverage
  congr 1
  change (List.Vector.toList (List.Vector.ofFn f)).unattach.sum = ∑ x, ↑(f x)
  rw [List.Vector.toList_ofFn]
  exact list_ofFn_subtype_sum f

/-- Centers obtained by averaging unordered `k`-tuples of vertices.  This removes
the ordering overcount from `empiricalCenters`. -/
noncomputable def unorderedEmpiricalCenters (V : Finset E) (k : ℕ) : Set E :=
  Set.range fun s : Sym V k => symAverage s

lemma unorderedEmpiricalCenters_ncard_le_choose (V : Finset E) (k : ℕ) :
    (unorderedEmpiricalCenters V k).ncard ≤ (V.card + k - 1).choose k := by
  classical
  calc
    (unorderedEmpiricalCenters V k).ncard ≤ Nat.card (Sym V k) := by
      let F : Sym V k → E := fun s => symAverage s
      have hle : (Set.range F).ncard ≤ (Set.univ : Set (Sym V k)).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le (s := (Set.univ : Set (Sym V k))) (f := F)
      simpa [unorderedEmpiricalCenters, F] using hle
    _ = Fintype.card (Sym V k) := Nat.card_eq_fintype_card
    _ = (V.card + k - 1).choose k := by
      rw [Sym.card_sym_eq_choose, Fintype.card_coe]

theorem convexHull_covered_by_empiricalCenters {V : Finset E} {D ε : ℝ} {k : ℕ}
    (hD : 0 ≤ D) (hk : 0 < k)
    (hdiam : PairwiseNormBound (V : Set E) D)
    (hε : D / Real.sqrt (k : ℝ) ≤ ε) :
    ∀ x ∈ convexHull ℝ (V : Set E),
      ∃ c ∈ empiricalCenters V k, ‖x - c‖ ≤ ε := by
  classical
  intro x hx
  rcases approximate_caratheodory (E := E) (T := (V : Set E)) (D := D)
      hD hdiam hx hk with ⟨pts, hpts, hdist⟩
  let f : Fin k → V := fun j => ⟨pts j, hpts j⟩
  refine ⟨empiricalAverage (fun j : Fin k => (f j : E)), ?_, ?_⟩
  · exact ⟨f, rfl⟩
  · exact hdist.trans hε

theorem convexHull_covered_by_unorderedEmpiricalCenters {V : Finset E} {D ε : ℝ} {k : ℕ}
    (hD : 0 ≤ D) (hk : 0 < k)
    (hdiam : PairwiseNormBound (V : Set E) D)
    (hε : D / Real.sqrt (k : ℝ) ≤ ε) :
    ∀ x ∈ convexHull ℝ (V : Set E),
      ∃ c ∈ unorderedEmpiricalCenters V k, ‖x - c‖ ≤ ε := by
  classical
  intro x hx
  rcases approximate_caratheodory (E := E) (T := (V : Set E)) (D := D)
      hD hdiam hx hk with ⟨pts, hpts, hdist⟩
  let f : Fin k → V := fun j => ⟨pts j, hpts j⟩
  refine ⟨symAverage ((List.Vector.ofFn f : List.Vector V k) : Sym V k), ?_, ?_⟩
  · exact ⟨((List.Vector.ofFn f : List.Vector V k) : Sym V k), rfl⟩
  · rw [symAverage_ofFn f]
    exact hdist.trans hε

/-- HDP Corollary 0.0.4 in a parameterized form. If `k` is chosen so that
`1 / sqrt(k) ≤ ε`, then the convex hull of `N` vertices and diameter at most
`1` is covered by at most `N^k` Euclidean balls of radius `ε`. -/
theorem covering_polytopes_by_balls_param {V : Finset E} {ε : ℝ} {k : ℕ}
    (hk : 0 < k) (hdiam : PairwiseNormBound (V : Set E) 1)
    (hε : 1 / Real.sqrt (k : ℝ) ≤ ε) :
    (∀ x ∈ convexHull ℝ (V : Set E),
      ∃ c ∈ empiricalCenters V k, ‖x - c‖ ≤ ε) ∧
    (empiricalCenters V k).ncard ≤ V.card ^ k := by
  refine ⟨?_, empiricalCenters_ncard_le V k⟩
  exact convexHull_covered_by_empiricalCenters (E := E) (V := V)
    (D := 1) (ε := ε) (k := k) (by norm_num) hk hdiam hε

lemma one_div_sqrt_natCeil_one_div_sq_le {ε : ℝ} (hε : 0 < ε) :
    1 / Real.sqrt ((⌈(1 / ε ^ 2 : ℝ)⌉₊ : ℝ)) ≤ ε := by
  let k : ℕ := ⌈(1 / ε ^ 2 : ℝ)⌉₊
  have hceil : (1 / ε ^ 2 : ℝ) ≤ (k : ℝ) := by exact Nat.le_ceil _
  have hsq : (1 / ε) ^ 2 ≤ (k : ℝ) := by
    convert hceil using 1
    field_simp [ne_of_gt hε]
  have hk_pos : 0 < (k : ℝ) := by
    have hpos : (0 : ℝ) < 1 / ε ^ 2 := by positivity
    exact lt_of_lt_of_le hpos hceil
  have hsqrt_ge : 1 / ε ≤ Real.sqrt (k : ℝ) := by
    have hs := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hε)] at hs
  have hsqrt_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos_of_pos hk_pos
  have hmul : 1 ≤ ε * Real.sqrt (k : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt_ge (le_of_lt hε)
    field_simp [ne_of_gt hε] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  rw [div_le_iff₀ hsqrt_pos]
  simpa [k, mul_comm] using hmul

/-- HDP Corollary 0.0.4 with `k = ceil(1 / ε^2)`: a polytope with `N`
vertices and diameter at most `1` is covered by at most `N^ceil(1/ε^2)`
balls of radius `ε`. -/
theorem covering_polytopes_by_balls {V : Finset E} {ε : ℝ}
    (hε : 0 < ε) (hdiam : PairwiseNormBound (V : Set E) 1) :
    (∀ x ∈ convexHull ℝ (V : Set E),
      ∃ c ∈ empiricalCenters V ⌈(1 / ε ^ 2 : ℝ)⌉₊, ‖x - c‖ ≤ ε) ∧
    (empiricalCenters V ⌈(1 / ε ^ 2 : ℝ)⌉₊).ncard ≤
      V.card ^ ⌈(1 / ε ^ 2 : ℝ)⌉₊ := by
  have hk : 0 < ⌈(1 / ε ^ 2 : ℝ)⌉₊ := by positivity
  exact covering_polytopes_by_balls_param (E := E) (V := V) (ε := ε)
    (k := ⌈(1 / ε ^ 2 : ℝ)⌉₊) hk hdiam
    (one_div_sqrt_natCeil_one_div_sq_le hε)

/-- HDP Exercise 0.0.6 in parameterized form. Using unordered empirical
averages improves the count from ordered `N^k` choices to the stars-and-bars
quantity `choose (N+k-1) k`. -/
theorem improved_covering_polytopes_by_balls_param {V : Finset E} {ε : ℝ} {k : ℕ}
    (hk : 0 < k) (hdiam : PairwiseNormBound (V : Set E) 1)
    (hε : 1 / Real.sqrt (k : ℝ) ≤ ε) :
    (∀ x ∈ convexHull ℝ (V : Set E),
      ∃ c ∈ unorderedEmpiricalCenters V k, ‖x - c‖ ≤ ε) ∧
    (unorderedEmpiricalCenters V k).ncard ≤ (V.card + k - 1).choose k := by
  refine ⟨?_, unorderedEmpiricalCenters_ncard_le_choose V k⟩
  exact convexHull_covered_by_unorderedEmpiricalCenters (E := E) (V := V)
    (D := 1) (ε := ε) (k := k) (by norm_num) hk hdiam hε

/-- HDP Exercise 0.0.6 with the explicit absolute constant `C = e`.
The number of radius-`ε` balls is bounded by
`(e + e ε^2 N)^ceil(1/ε^2)`. -/
theorem improved_covering_polytopes_by_balls {V : Finset E} {ε : ℝ}
    (hε : 0 < ε) (hdiam : PairwiseNormBound (V : Set E) 1) :
    (∀ x ∈ convexHull ℝ (V : Set E),
      ∃ c ∈ unorderedEmpiricalCenters V ⌈(1 / ε ^ 2 : ℝ)⌉₊, ‖x - c‖ ≤ ε) ∧
    ((unorderedEmpiricalCenters V ⌈(1 / ε ^ 2 : ℝ)⌉₊).ncard : ℝ) ≤
      (Real.exp 1 + Real.exp 1 * ε ^ 2 * (V.card : ℝ)) ^
        ⌈(1 / ε ^ 2 : ℝ)⌉₊ := by
  let k : ℕ := ⌈(1 / ε ^ 2 : ℝ)⌉₊
  have hk : 0 < k := by
    dsimp [k]
    positivity
  have hcover := convexHull_covered_by_unorderedEmpiricalCenters (E := E) (V := V)
    (D := 1) (ε := ε) (k := k) (by norm_num) hk hdiam
    (one_div_sqrt_natCeil_one_div_sq_le hε)
  refine ⟨hcover, ?_⟩
  have hcard_nat := unorderedEmpiricalCenters_ncard_le_choose V k
  have hcard_real :
      ((unorderedEmpiricalCenters V k).ncard : ℝ) ≤ ((V.card + k - 1).choose k : ℝ) := by
    exact_mod_cast hcard_nat
  have hchoose_mono :
      ((V.card + k - 1).choose k : ℝ) ≤ ((V.card + k).choose k : ℝ) := by
    exact_mod_cast Nat.choose_le_choose k (by omega : V.card + k - 1 ≤ V.card + k)
  have hchoose_exp :
      ((V.card + k).choose k : ℝ) ≤
        (Real.exp 1 * ((V.card + k : ℕ) : ℝ) / (k : ℝ)) ^ k :=
    choose_le_exp_mul_div (V.card + k) k hk
  have hceil : (1 / ε ^ 2 : ℝ) ≤ (k : ℝ) := by
    dsimp [k]
    exact Nat.le_ceil _
  have hbase :
      Real.exp 1 * ((V.card + k : ℕ) : ℝ) / (k : ℝ) ≤
        Real.exp 1 + Real.exp 1 * ε ^ 2 * (V.card : ℝ) :=
    eps_card_base_bound (N := V.card) (k := k) hε hceil
  have hpow :
      (Real.exp 1 * ((V.card + k : ℕ) : ℝ) / (k : ℝ)) ^ k ≤
        (Real.exp 1 + Real.exp 1 * ε ^ 2 * (V.card : ℝ)) ^ k := by
    exact pow_le_pow_left₀ (by positivity) hbase k
  simpa [k] using hcard_real.trans (hchoose_mono.trans (hchoose_exp.trans hpow))

end LeanFpAnalysis.HDP
