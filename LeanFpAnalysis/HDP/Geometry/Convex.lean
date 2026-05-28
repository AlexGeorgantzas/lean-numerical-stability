import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

/-!
# Convex Geometry Tools for HDP

This file contains reusable convex-combination facts used in Vershynin's
High-Dimensional Probability appetizer and later covering arguments.
-/

open scoped BigOperators
open Finset

namespace LeanFpAnalysis.HDP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A set has pairwise norm diameter at most `D`. This is the pointwise form of
`diam(T) ≤ D`, and is often more convenient than `Metric.diam` in constructive
covering proofs. -/
def PairwiseNormBound (T : Set E) (D : ℝ) : Prop :=
  ∀ ⦃s⦄, s ∈ T → ∀ ⦃t⦄, t ∈ T → ‖s - t‖ ≤ D

omit [InnerProductSpace ℝ E] in
/-- The pointwise diameter bound implies the standard mathlib diameter bound. -/
lemma diam_le_of_pairwiseNormBound {T : Set E} {D : ℝ}
    (hD : 0 ≤ D) (hdiam : PairwiseNormBound T D) :
    Metric.diam T ≤ D := by
  refine Metric.diam_le_of_forall_dist_le hD ?_
  intro s hs t ht
  simpa [dist_eq_norm] using hdiam hs ht

omit [InnerProductSpace ℝ E] in
/-- Bridge from mathlib's bounded real diameter API to `PairwiseNormBound`.
The boundedness hypothesis is needed because `Metric.diam` is defined via
`ENNReal.toReal`, which is `0` on infinite extended diameter. -/
lemma pairwiseNormBound_of_diam_le {T : Set E} {D : ℝ}
    (hbounded : Bornology.IsBounded T) (hdiam : Metric.diam T ≤ D) :
    PairwiseNormBound T D := by
  intro s hs t ht
  rw [← dist_eq_norm]
  exact (Metric.dist_le_diam_of_mem hbounded hs ht).trans hdiam

/-- Equal-weight average of `k` points. -/
noncomputable def empiricalAverage {k : ℕ} (x : Fin k → E) : E :=
  ((k : ℝ)⁻¹) • ∑ j : Fin k, x j

section FiniteConvex

variable {ι : Type*} [Fintype ι]

lemma exists_pos_weight {w : ι → ℝ} (hw₁ : ∑ i, w i = 1) :
    ∃ i, 0 < w i := by
  classical
  by_contra h
  push_neg at h
  have h_nonpos : ∑ i, w i ≤ 0 := by
    exact Finset.sum_nonpos fun i _ => h i
  linarith

lemma exists_inner_nonpos_of_weighted_sum_zero {w : ι → ℝ} {u : ι → E} (s : E)
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1)
    (hu : ∑ i, w i • u i = 0) :
    ∃ i, inner ℝ s (u i) ≤ 0 := by
  classical
  by_contra h
  push_neg at h
  have hpos_weight : ∃ i, 0 < w i := exists_pos_weight hw₁
  have hsum_pos : 0 < ∑ i, w i * inner ℝ s (u i) := by
    refine Finset.sum_pos' (fun i _ => ?_) ?_
    · exact mul_nonneg (hw₀ i) (le_of_lt (h i))
    · rcases hpos_weight with ⟨i, hwi⟩
      exact ⟨i, Finset.mem_univ i, mul_pos hwi (h i)⟩
  have hsum_zero : ∑ i, w i * inner ℝ s (u i) = 0 := by
    calc
      ∑ i, w i * inner ℝ s (u i)
          = inner ℝ s (∑ i, w i • u i) := by
              simp [inner_sum, real_inner_smul_right]
      _ = 0 := by simp [hu]
  linarith

lemma weighted_deviation_sum_zero {w : ι → ℝ} {z : ι → E} {x : E}
    (hw₁ : ∑ i, w i = 1) (hx : ∑ i, w i • z i = x) :
    ∑ i, w i • (z i - x) = 0 := by
  classical
  calc
    ∑ i, w i • (z i - x)
        = (∑ i, w i • z i) - (∑ i, w i) • x := by
            simp [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
    _ = 0 := by simp [hx, hw₁]

lemma convex_combo_dist_le_pairwise {T : Set E} {D : ℝ} {w : ι → ℝ} {z : ι → E} {x : E}
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1)
    (hz : ∀ i, z i ∈ T) (hx : ∑ i, w i • z i = x)
    (hdiam : PairwiseNormBound T D) (i : ι) :
    ‖z i - x‖ ≤ D := by
  classical
  have hrepr : z i - x = ∑ j, w j • (z i - z j) := by
    calc
      z i - x = (∑ j, w j) • z i - ∑ j, w j • z j := by
        simp [hw₁, hx]
      _ = ∑ j, (w j • z i - w j • z j) := by
        rw [Finset.sum_sub_distrib]
        simp [Finset.sum_smul]
      _ = ∑ j, w j • (z i - z j) := by
        simp [smul_sub]
  calc
    ‖z i - x‖ = ‖∑ j, w j • (z i - z j)‖ := by rw [hrepr]
    _ ≤ ∑ j, ‖w j • (z i - z j)‖ := by
      simpa using norm_sum_le Finset.univ (fun j => w j • (z i - z j))
    _ = ∑ j, w j * ‖z i - z j‖ := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw₀ j)]
    _ ≤ ∑ j, w j * D := by
      refine Finset.sum_le_sum ?_
      intro j _
      exact mul_le_mul_of_nonneg_left (hdiam (hz i) (hz j)) (hw₀ j)
    _ = D := by
      rw [← Finset.sum_mul]
      simp [hw₁]

lemma maurey_sum_deviation_sq {T : Set E} {D : ℝ} (hD : 0 ≤ D)
    {w : ι → ℝ} {z : ι → E} {x : E}
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1)
    (hz : ∀ i, z i ∈ T) (hx : ∑ i, w i • z i = x)
    (hdiam : PairwiseNormBound T D) :
    ∀ k : ℕ, ∃ idx : Fin k → ι,
      ‖∑ j : Fin k, (z (idx j) - x)‖ ^ 2 ≤ (k : ℝ) * D ^ 2 := by
  classical
  intro k
  induction k with
  | zero =>
      refine ⟨fun j => Fin.elim0 j, ?_⟩
      simp
  | succ k ih =>
      rcases ih with ⟨idx, hidx⟩
      let s : E := ∑ j : Fin k, (z (idx j) - x)
      have hdev_zero : ∑ i, w i • (z i - x) = 0 :=
        weighted_deviation_sum_zero hw₁ hx
      rcases exists_inner_nonpos_of_weighted_sum_zero s hw₀ hw₁ hdev_zero with ⟨i, hi⟩
      let idx' : Fin (k + 1) → ι := @Fin.snoc k (fun _ => ι) idx i
      refine ⟨idx', ?_⟩
      have hsum :
          ∑ j : Fin (k + 1), (z (idx' j) - x) = s + (z i - x) := by
        rw [Fin.sum_univ_castSucc]
        simp [idx', s, Fin.snoc_castSucc, Fin.snoc_last]
      have hu : ‖z i - x‖ ≤ D :=
        convex_combo_dist_le_pairwise hw₀ hw₁ hz hx hdiam i
      have hu_sq : ‖z i - x‖ ^ 2 ≤ D ^ 2 := by
        nlinarith [norm_nonneg (z i - x), hD, hu]
      have hinner : 2 * inner ℝ s (z i - x) ≤ 0 := by
        nlinarith
      calc
        ‖∑ j : Fin (k + 1), (z (idx' j) - x)‖ ^ 2
            = ‖s + (z i - x)‖ ^ 2 := by rw [hsum]
        _ = ‖s‖ ^ 2 + 2 * inner ℝ s (z i - x) + ‖z i - x‖ ^ 2 := by
          rw [norm_add_sq_real]
        _ ≤ (k : ℝ) * D ^ 2 + 0 + D ^ 2 := by
          nlinarith
        _ = (k + 1 : ℕ) * D ^ 2 := by
          norm_num
          ring

lemma norm_sum_deviation_le {T : Set E} {D : ℝ} (hD : 0 ≤ D)
    {w : ι → ℝ} {z : ι → E} {x : E}
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1)
    (hz : ∀ i, z i ∈ T) (hx : ∑ i, w i • z i = x)
    (hdiam : PairwiseNormBound T D) {k : ℕ} (hk : 0 < k) :
    ∃ idx : Fin k → ι,
      ‖∑ j : Fin k, (z (idx j) - x)‖ ≤ Real.sqrt (k : ℝ) * D := by
  classical
  rcases maurey_sum_deviation_sq hD hw₀ hw₁ hz hx hdiam k with ⟨idx, hidx⟩
  refine ⟨idx, ?_⟩
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hprod_nonneg : 0 ≤ (k : ℝ) * D ^ 2 := mul_nonneg hk_nonneg (sq_nonneg D)
  calc
    ‖∑ j : Fin k, (z (idx j) - x)‖
        = Real.sqrt (‖∑ j : Fin k, (z (idx j) - x)‖ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt ((k : ℝ) * D ^ 2) := Real.sqrt_le_sqrt hidx
    _ = Real.sqrt (k : ℝ) * D := by
      rw [Real.sqrt_mul hk_nonneg, Real.sqrt_sq_eq_abs, abs_of_nonneg hD]

lemma empirical_error_eq_smul_sum_deviation {k : ℕ} (hk : 0 < k) (x : E) (pts : Fin k → E) :
    x - empiricalAverage pts = -((k : ℝ)⁻¹ • ∑ j : Fin k, (pts j - x)) := by
  classical
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  unfold empiricalAverage
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ k x]
  calc
    x - (k : ℝ)⁻¹ • ∑ j : Fin k, pts j
        = (k : ℝ)⁻¹ • ((k : ℝ) • x) - (k : ℝ)⁻¹ • ∑ j : Fin k, pts j := by
          simp [smul_smul, inv_mul_cancel₀ hk_ne]
    _ = -((k : ℝ)⁻¹ • ((∑ j : Fin k, pts j) - (k : ℝ) • x)) := by
      module

theorem approximate_caratheodory_fintype {T : Set E} {D : ℝ} (hD : 0 ≤ D)
    {w : ι → ℝ} {z : ι → E} {x : E}
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1)
    (hz : ∀ i, z i ∈ T) (hx : ∑ i, w i • z i = x)
    (hdiam : PairwiseNormBound T D) {k : ℕ} (hk : 0 < k) :
    ∃ pts : Fin k → E,
      (∀ j, pts j ∈ T) ∧ ‖x - empiricalAverage pts‖ ≤ D / Real.sqrt (k : ℝ) := by
  classical
  rcases norm_sum_deviation_le hD hw₀ hw₁ hz hx hdiam hk with ⟨idx, hidx⟩
  refine ⟨fun j => z (idx j), fun j => hz (idx j), ?_⟩
  have hsqrt_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos_of_pos (by exact_mod_cast hk)
  have hk_pos_real : 0 < (k : ℝ) := by exact_mod_cast hk
  have herr :
      ‖x - empiricalAverage (fun j : Fin k => z (idx j))‖
        = (k : ℝ)⁻¹ * ‖∑ j : Fin k, (z (idx j) - x)‖ := by
    rw [empirical_error_eq_smul_sum_deviation hk]
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk_pos_real)]
  calc
    ‖x - empiricalAverage (fun j : Fin k => z (idx j))‖
        = (k : ℝ)⁻¹ * ‖∑ j : Fin k, (z (idx j) - x)‖ := herr
    _ ≤ (k : ℝ)⁻¹ * (Real.sqrt (k : ℝ) * D) := by
      exact mul_le_mul_of_nonneg_left hidx (le_of_lt (inv_pos.mpr hk_pos_real))
    _ = D / Real.sqrt (k : ℝ) := by
      field_simp [hk_pos_real.ne', hsqrt_pos.ne']
      rw [Real.sq_sqrt (le_of_lt hk_pos_real)]

end FiniteConvex

theorem approximate_caratheodory {T : Set E} {D : ℝ} (hD : 0 ≤ D)
    (hdiam : PairwiseNormBound T D) {x : E} (hx : x ∈ convexHull ℝ T)
    {k : ℕ} (hk : 0 < k) :
    ∃ pts : Fin k → E,
      (∀ j, pts j ∈ T) ∧ ‖x - empiricalAverage pts‖ ≤ D / Real.sqrt (k : ℝ) := by
  classical
  rcases (mem_convexHull_iff_exists_fintype.mp hx) with
    ⟨ι, _inst, w, z, hw₀, hw₁, hz, hxsum⟩
  exact approximate_caratheodory_fintype (E := E) (T := T) hD hw₀ hw₁ hz hxsum hdiam hk

/-- Vershynin, HDP Theorem 0.0.2, normalized to diameter at most `1`. -/
theorem approximate_caratheodory_unit {T : Set E}
    (hdiam : PairwiseNormBound T 1) {x : E} (hx : x ∈ convexHull ℝ T)
    {k : ℕ} (hk : 0 < k) :
    ∃ pts : Fin k → E,
      (∀ j, pts j ∈ T) ∧ ‖x - empiricalAverage pts‖ ≤ 1 / Real.sqrt (k : ℝ) := by
  simpa using approximate_caratheodory (E := E) (T := T) (D := 1) (by norm_num) hdiam hx hk

end LeanFpAnalysis.HDP
