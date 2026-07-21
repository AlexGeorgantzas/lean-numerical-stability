-- Algorithms/StationaryIterationSeries.lean
--
-- Higham Chapter 17 "Stationary Iterative Methods", §17.2-§17.3: the literal
-- infinite-series surfaces behind eqs (17.8)/(17.11)-(17.17) and (17.20).
--
-- The finite theorems in `StationaryIteration.lean` are all phrased against
-- the finite-horizon certificate `PartialSumBound` (the partial sums of the
-- series in eq (17.12)) and the supremum envelope `residualSigmaSup` (the
-- finite partial norms of the sigma series before eq (17.20)).  This file
-- supplies the genuine `tsum` objects:
--
--   * geometric summability of `‖G^k‖∞` under a norm certificate
--     `‖G‖∞ ≤ q < 1`, and under a genuine `spectralRadius` certificate via
--     Gelfand's formula;
--   * the literal entrywise series `Σ'_k Σ_l |G^k|_{il} |M^{-1}|_{lj}` of
--     eq (17.12), the attained constant `c(A)` as an `sInf`, and the bridge
--     that turns the literal infinite statement into every finite
--     `PartialSumBound` certificate simultaneously (hence uniform-in-m
--     versions of the forward bounds (17.13)-(17.17));
--   * the literal entrywise `tsum` sigma matrix of §17.3 (paragraph before
--     eq (17.20)) and its equality with the supremum envelope
--     `residualSigmaSup`.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Monotone
import NumStability.Algorithms.StationaryIteration
import NumStability.Algorithms.MatrixPowersSpectral

namespace NumStability

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

-- ============================================================
-- §17.2  A. Summability foundations for the series in (17.8)/(17.12)
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.8): the norms `‖G^k‖∞` of the iteration-matrix powers appearing in
    the infinite error series are summable under the norm certificate
    `‖G‖∞ ≤ q < 1`.  Scope: this is the standard geometric-majorant argument
    `‖G^k‖∞ ≤ ‖G‖∞^k ≤ q^k`; it does not use the weaker spectral condition
    (for that see `summable_infNorm_matPow_of_spectralRadius`). -/
theorem summable_infNorm_matPow (n : ℕ) (hn : 0 < n)
    (G : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hG : infNorm G ≤ q) :
    Summable (fun k => infNorm (matPow n G k)) :=
  Summable.of_nonneg_of_le (fun _ => infNorm_nonneg _)
    (fun k => (infNorm_matPow_le hn G k).trans
      (pow_le_pow_left₀ (infNorm_nonneg G) hG k))
    (summable_geometric_of_lt_one hq0 hq1)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eqs (17.8)/(17.12): the summed norms of the iteration-matrix powers are
    bounded by the geometric series value `(1 - q)⁻¹` under the norm
    certificate `‖G‖∞ ≤ q < 1`. -/
theorem tsum_infNorm_matPow_le (n : ℕ) (hn : 0 < n)
    (G : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hG : infNorm G ≤ q) :
    ∑' k : ℕ, infNorm (matPow n G k) ≤ (1 - q)⁻¹ :=
  calc ∑' k : ℕ, infNorm (matPow n G k)
      ≤ ∑' k : ℕ, q ^ k :=
        Summable.tsum_le_tsum
          (fun k => (infNorm_matPow_le hn G k).trans
            (pow_le_pow_left₀ (infNorm_nonneg G) hG k))
          (summable_infNorm_matPow n hn G q hq0 hq1 hG)
          (summable_geometric_of_lt_one hq0 hq1)
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1

/-- Geometric majorant for the entrywise terms of the series in Higham,
    Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): each term `Σ_l |G^k|_{il} |M^{-1}|_{lj}` is bounded by
    `q^k · ‖M^{-1}‖₁`.  Scope note on the choice of majorant: every entry
    `|M^{-1}|_{lj}` is dominated by the `j`-th column sum, hence by the
    matrix 1-norm `‖M^{-1}‖₁` (the maximum column sum); this single uniform
    constant keeps all subsequent summability comparisons one-dimensional. -/
theorem matPow_entry_mul_sum_le_geometric (n : ℕ) (hn : 0 < n)
    (G M_inv : Fin n → Fin n → ℝ)
    (q : ℝ) (hG : infNorm G ≤ q) (i j : Fin n) (k : ℕ) :
    ∑ l : Fin n, |matPow n G k i l| * |M_inv l j| ≤ q ^ k * oneNorm M_inv := by
  have hcol : ∀ l : Fin n, |M_inv l j| ≤ oneNorm M_inv := fun l =>
    le_trans
      (Finset.single_le_sum (fun p _ => abs_nonneg (M_inv p j)) (Finset.mem_univ l))
      (col_sum_le_oneNorm M_inv j)
  calc ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|
      ≤ ∑ l : Fin n, |matPow n G k i l| * oneNorm M_inv := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul_of_nonneg_left (hcol l) (abs_nonneg _)
    _ = (∑ l : Fin n, |matPow n G k i l|) * oneNorm M_inv := by
        rw [Finset.sum_mul]
    _ ≤ infNorm (matPow n G k) * oneNorm M_inv :=
        mul_le_mul_of_nonneg_right (row_sum_le_infNorm _ i) (oneNorm_nonneg _)
    _ ≤ q ^ k * oneNorm M_inv :=
        mul_le_mul_of_nonneg_right
          ((infNorm_matPow_le hn G k).trans
            (pow_le_pow_left₀ (infNorm_nonneg G) hG k))
          (oneNorm_nonneg _)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): entrywise summability of the series
    `Σ_k Σ_l |G^k|_{il} |M^{-1}|_{lj}` under the norm certificate
    `‖G‖∞ ≤ q < 1`, by comparison with the geometric majorant
    `q^k · ‖M^{-1}‖₁` from `matPow_entry_mul_sum_le_geometric`. -/
theorem summable_matPow_entry_mul (n : ℕ) (hn : 0 < n)
    (G M_inv : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hG : infNorm G ≤ q) (i j : Fin n) :
    Summable (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|) :=
  Summable.of_nonneg_of_le
    (fun _ => Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (fun k => matPow_entry_mul_sum_le_geometric n hn G M_inv q hG i j k)
    ((summable_geometric_of_lt_one hq0 hq1).mul_right (oneNorm M_inv))

/-- Norm of the complexified `k`-th power of an arbitrary real matrix equals
    the repository infinity norm of the real power.  Bridge lemma for the
    Gelfand extraction below (generalizing `norm_absMatrixComplexified_pow`
    from the entrywise-absolute case to arbitrary real matrices). -/
theorem norm_complexified_pow (n : ℕ) (B : Fin n → Fin n → ℝ) (k : ℕ) :
    ‖((Matrix.of B).map Complex.ofReal) ^ k‖ = infNorm (matPow n B k) := by
  rw [← map_ofReal_pow, linfty_opNorm_map_ofReal, infNorm_eq_linfty_opNorm,
    matPow_eq_matrix_pow]

/-- **Gelfand extraction for an arbitrary real matrix** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.2, discussion around
    eq (17.9): convergence of the powers `G^k` is governed by the spectral
    radius `ρ(G) < 1`): if the genuine Mathlib `spectralRadius` of the
    complexified matrix is at most `ρ` and `ρ < r`, then eventually
    `‖B^k‖∞ ≤ r^k`.  This generalizes
    `eventually_matPow_abs_le_of_spectralRadius_le` from `|A|` to an
    arbitrary real matrix `B`; the Gelfand argument is unchanged. -/
theorem eventually_matPow_le_of_spectralRadius_le (n : ℕ)
    (B : Fin n → Fin n → ℝ) (ρ r : ℝ) (hρ0 : 0 ≤ ρ) (hρr : ρ < r)
    (hspec : spectralRadius ℂ ((Matrix.of B).map Complex.ofReal) ≤
      ENNReal.ofReal ρ) :
    ∀ᶠ k in Filter.atTop, infNorm (matPow n B k) ≤ r ^ k := by
  haveI hfd : FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.finiteDimensional
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.complete ℂ _
  have hr0 : 0 < r := lt_of_le_of_lt hρ0 hρr
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius
    ((Matrix.of B).map Complex.ofReal)
  have hlt : spectralRadius ℂ ((Matrix.of B).map Complex.ofReal) <
      ENNReal.ofReal r :=
    lt_of_le_of_lt hspec (ENNReal.ofReal_lt_ofReal_iff hr0 |>.mpr hρr)
  have hev : ∀ᶠ (k : ℕ) in Filter.atTop,
      ENNReal.ofReal (‖((Matrix.of B).map Complex.ofReal) ^ k‖ ^ (1 / (k:ℝ))) <
        ENNReal.ofReal r :=
    hgel.eventually_lt_const hlt
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with k hk hk1
  have hklt : ‖((Matrix.of B).map Complex.ofReal) ^ k‖ ^ (1 / (k:ℝ)) < r :=
    (ENNReal.ofReal_lt_ofReal_iff hr0).mp hk
  have hknorm0 : (0:ℝ) ≤ ‖((Matrix.of B).map Complex.ofReal) ^ k‖ :=
    norm_nonneg _
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
  -- Undo the 1/k root: x = (x^(1/k))^k for x ≥ 0, k ≠ 0.
  have hroot : ‖((Matrix.of B).map Complex.ofReal) ^ k‖ =
      (‖((Matrix.of B).map Complex.ofReal) ^ k‖ ^ (1 / (k:ℝ))) ^ (k:ℕ) := by
    rw [← Real.rpow_natCast
      (‖((Matrix.of B).map Complex.ofReal) ^ k‖ ^ (1 / (k:ℝ))) k,
      ← Real.rpow_mul hknorm0]
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hkR), Real.rpow_one]
  have hle : ‖((Matrix.of B).map Complex.ofReal) ^ k‖ ≤ r ^ k := by
    rw [hroot]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hknorm0 _) (le_of_lt hklt) k
  rw [norm_complexified_pow] at hle
  exact hle

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eqs (17.8)/(17.9): summability of `‖G^k‖∞` from the genuine spectral
    certificate `spectralRadius(G) ≤ ρ < 1` (Mathlib `spectralRadius` of the
    complexified matrix), via Gelfand's formula.  The series is split at the
    eventual index provided by `eventually_matPow_le_of_spectralRadius_le`
    with `r := (ρ + 1)/2` strictly between `ρ` and `1`.  Scope: unlike
    `summable_infNorm_matPow` this needs no norm certificate `‖G‖∞ < 1`. -/
theorem summable_infNorm_matPow_of_spectralRadius (n : ℕ)
    (B : Fin n → Fin n → ℝ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hspec : spectralRadius ℂ ((Matrix.of B).map Complex.ofReal) ≤
      ENNReal.ofReal ρ) :
    Summable (fun k => infNorm (matPow n B k)) := by
  set r := (ρ + 1) / 2 with hr
  have hρr : ρ < r := by rw [hr]; linarith
  have hr0 : 0 ≤ r := le_of_lt (lt_of_le_of_lt hρ0 hρr)
  have hr1 : r < 1 := by rw [hr]; linarith
  have hev := eventually_matPow_le_of_spectralRadius_le n B ρ r hρ0 hρr hspec
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  have hshift : Summable (fun k => infNorm (matPow n B (k + K))) := by
    refine Summable.of_nonneg_of_le (fun _ => infNorm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (r ^ K))
    calc infNorm (matPow n B (k + K))
        ≤ r ^ (k + K) := hK (k + K) (Nat.le_add_left K k)
      _ = r ^ K * r ^ k := by rw [pow_add]; ring
  exact (summable_nat_add_iff
    (f := fun k => infNorm (matPow n B k)) K).mp hshift

/-- Higham, Problem 17.1, in the exact form consumed by (17.8), (17.11),
    and (17.29): if the spectral radius of `B` is strictly below one, then
    every entry of the matrix series `∑ |B^k|` and the scalar series
    `∑ ‖B^k‖∞` are summable.  The first conjunct is the finite-dimensional
    meaning of convergence of the entrywise-absolute matrix series; the
    second uses the repository's matrix infinity norm. -/
theorem higham17_problem17_1 (n : ℕ)
    (B : Fin n → Fin n → ℝ)
    (hspec : spectralRadius ℂ ((Matrix.of B).map Complex.ofReal) < 1) :
    (∀ i j : Fin n, Summable (fun k => |matPow n B k i j|)) ∧
      Summable (fun k => infNorm (matPow n B k)) := by
  obtain ⟨r, _hr0', hrspec, hr1'⟩ := ENNReal.lt_iff_exists_real_btwn.mp hspec
  have hr0 : 0 < r := by
    by_contra h
    push_neg at h
    rw [ENNReal.ofReal_of_nonpos h] at hrspec
    exact (not_lt_bot hrspec).elim
  have hr1 : r < 1 := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp] at hr1'
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mp hr1'
  have hnorm : Summable (fun k => infNorm (matPow n B k)) :=
    summable_infNorm_matPow_of_spectralRadius n B r hr0.le hr1
      (le_of_lt hrspec)
  refine ⟨?_, hnorm⟩
  intro i j
  exact Summable.of_nonneg_of_le
    (fun _ => abs_nonneg _)
    (fun k =>
      le_trans
        (Finset.single_le_sum
          (fun l _ => abs_nonneg (matPow n B k i l))
          (Finset.mem_univ j))
        (row_sum_le_infNorm (matPow n B k) i))
    hnorm

-- ============================================================
-- §17.2  B. The literal c(A) series surface of eq (17.12)
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): the literal entry of the infinite series
    `Σ_{k=0}^∞ |G^k M^{-1}|` at position `(i,j)`, in the componentwise form
    `Σ'_k Σ_l |G^k|_{il} |M^{-1}|_{lj}` used throughout the finite layer.
    Scope: like every real `tsum`, this evaluates to `0` when the series is
    not summable; the summability certificates above make it meaningful. -/
noncomputable def stationarySeriesEntry (n : ℕ) (G M_inv : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  ∑' k : ℕ, ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|

/-- The literal (17.12) series entries are nonnegative. -/
theorem stationarySeriesEntry_nonneg (n : ℕ) (G M_inv : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    0 ≤ stationarySeriesEntry n G M_inv i j :=
  tsum_nonneg fun _ =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): the literal series entry is bounded by
    `(1 - q)⁻¹ · ‖M^{-1}‖₁` under the norm certificate `‖G‖∞ ≤ q < 1`. -/
theorem stationarySeriesEntry_le (n : ℕ) (hn : 0 < n)
    (G M_inv : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hG : infNorm G ≤ q) (i j : Fin n) :
    stationarySeriesEntry n G M_inv i j ≤ (1 - q)⁻¹ * oneNorm M_inv :=
  calc stationarySeriesEntry n G M_inv i j
      ≤ ∑' k : ℕ, q ^ k * oneNorm M_inv :=
        Summable.tsum_le_tsum
          (fun k => matPow_entry_mul_sum_le_geometric n hn G M_inv q hG i j k)
          (summable_matPow_entry_mul n hn G M_inv q hq0 hq1 hG i j)
          ((summable_geometric_of_lt_one hq0 hq1).mul_right (oneNorm M_inv))
    _ = (1 - q)⁻¹ * oneNorm M_inv := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]

/-- **The bridge from the literal (17.12) statement to every finite
    certificate** (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §17.2, eq (17.12)): if the infinite series entries satisfy
    `Σ'_k Σ_l |G^k|_{il} |M^{-1}|_{lj} ≤ cA · |A^{-1}|_{ij}` and the
    entrywise series are summable, then the finite `PartialSumBound`
    certificate consumed by every finite forward theorem holds for ALL
    horizons `m` simultaneously. -/
theorem partialSumBound_of_stationarySeriesEntry_le (n : ℕ)
    (G M_inv A_inv : Fin n → Fin n → ℝ) (cA : ℝ)
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hle : ∀ i j, stationarySeriesEntry n G M_inv i j ≤ cA * |A_inv i j|)
    (m : ℕ) :
    PartialSumBound n G M_inv A_inv cA m := by
  intro i j
  calc ∑ k ∈ Finset.range (m + 1),
        ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|
      ≤ stationarySeriesEntry n G M_inv i j :=
        Summable.sum_le_tsum (Finset.range (m + 1))
          (fun _ _ => Finset.sum_nonneg fun _ _ =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (hsum i j)
    _ ≤ cA * |A_inv i j| := hle i j

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): the set of admissible constants `c` for the literal
    componentwise series bound `Σ_{k=0}^∞ |G^k M^{-1}| ≤ c · |A^{-1}|`. -/
def CAValues (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ) : Set ℝ :=
  {c | 0 ≤ c ∧ ∀ i j, stationarySeriesEntry n G M_inv i j ≤ c * |A_inv i j|}

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): the literal constant `c(A)` — the least admissible constant
    in the componentwise series bound, as an infimum.  Scope: `sInf` of an
    empty set is `0` in ℝ; the membership theorem `cALiteral_mem` carries the
    honest nonemptiness hypothesis. -/
noncomputable def cALiteral (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ) : ℝ :=
  sInf (CAValues n G M_inv A_inv)

/-- The admissible-constant set of eq (17.12) is closed: it is the
    intersection of `[0, ∞)` with finitely many closed half-line
    conditions, one per matrix entry. -/
theorem isClosed_CAValues (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ) :
    IsClosed (CAValues n G M_inv A_inv) := by
  have hrepr : CAValues n G M_inv A_inv =
      Set.Ici (0:ℝ) ∩ ⋂ i : Fin n, ⋂ j : Fin n,
        {c : ℝ | stationarySeriesEntry n G M_inv i j ≤ c * |A_inv i j|} := by
    ext c
    simp only [CAValues, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici,
      Set.mem_iInter]
  rw [hrepr]
  exact IsClosed.inter isClosed_Ici
    (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (continuous_mul_const _))

/-- **The literal `c(A)` of eq (17.12) is attained** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.2, eq (17.12)): the
    infimum of the admissible constants is itself admissible, because the
    admissible set is closed, bounded below by `0`, and (by hypothesis)
    nonempty.  Scope note: nonemptiness is a genuine hypothesis — it can
    fail when some `|A^{-1}|_{ij} = 0` while the corresponding series entry
    is positive; the source implicitly assumes a finite `c(A)` exists.  A
    sufficient condition is provided by
    `CAValues_nonempty_of_entry_lower_bound`. -/
theorem cALiteral_mem (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ)
    (hne : (CAValues n G M_inv A_inv).Nonempty) :
    cALiteral n G M_inv A_inv ∈ CAValues n G M_inv A_inv :=
  (isClosed_CAValues n G M_inv A_inv).csInf_mem hne ⟨0, fun _ hc => hc.1⟩

/-- The attained literal `c(A)` is nonnegative. -/
theorem cALiteral_nonneg (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ)
    (hne : (CAValues n G M_inv A_inv).Nonempty) :
    0 ≤ cALiteral n G M_inv A_inv :=
  (cALiteral_mem n G M_inv A_inv hne).1

/-- Sufficient condition for the admissible set of eq (17.12) to be
    nonempty (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §17.2, eq (17.12)): a norm certificate `‖G‖∞ ≤ q < 1` together
    with a uniform positive lower bound `δ ≤ |A^{-1}|_{ij}` on all entries.
    The witness is `c := (1 - q)⁻¹ · ‖M^{-1}‖₁ / δ`.  Scope: the entrywise
    positivity of `|A^{-1}|` is a strong (but honest) hypothesis; without
    some such majorization the set can be empty. -/
theorem CAValues_nonempty_of_entry_lower_bound (n : ℕ) (hn : 0 < n)
    (G M_inv A_inv : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hG : infNorm G ≤ q)
    (δ : ℝ) (hδ : 0 < δ) (hA : ∀ i j, δ ≤ |A_inv i j|) :
    (CAValues n G M_inv A_inv).Nonempty := by
  have hq' : (0:ℝ) < 1 - q := by linarith
  have hc0 : 0 ≤ (1 - q)⁻¹ * oneNorm M_inv / δ :=
    div_nonneg (mul_nonneg (inv_nonneg.mpr (le_of_lt hq')) (oneNorm_nonneg _))
      (le_of_lt hδ)
  refine ⟨(1 - q)⁻¹ * oneNorm M_inv / δ, hc0, fun i j => ?_⟩
  calc stationarySeriesEntry n G M_inv i j
      ≤ (1 - q)⁻¹ * oneNorm M_inv :=
        stationarySeriesEntry_le n hn G M_inv q hq0 hq1 hG i j
    _ = (1 - q)⁻¹ * oneNorm M_inv / δ * δ := by
        field_simp
    _ ≤ (1 - q)⁻¹ * oneNorm M_inv / δ * |A_inv i j| :=
        mul_le_mul_of_nonneg_left (hA i j) hc0

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.12): the attained literal constant `c(A)` supplies the finite
    `PartialSumBound` certificate at EVERY horizon `m` simultaneously — the
    literal infinite statement of (17.12) specialised back to the finite
    layer. -/
theorem partialSumBound_cALiteral (n : ℕ)
    (G M_inv A_inv : Fin n → Fin n → ℝ)
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hne : (CAValues n G M_inv A_inv).Nonempty) (m : ℕ) :
    PartialSumBound n G M_inv A_inv (cALiteral n G M_inv A_inv) m :=
  partialSumBound_of_stationarySeriesEntry_le n G M_inv A_inv _ hsum
    (cALiteral_mem n G M_inv A_inv hne).2 m

-- ============================================================
-- §17.2  B'. Uniform-in-m forward bounds with the literal c(A)
--        (eqs 17.13-17.17)
-- ============================================================

/-- **Literal uniform-in-m norm-form forward bound** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.2, eqs (17.13)-(17.15)):
    the finite norm-form forward bound holds with the SINGLE literal
    constant `c(A) = cALiteral` for ALL horizons `m` simultaneously, exactly
    as printed — the constant no longer depends on the horizon of the
    certificate.  Obtained by instantiating the finite theorem with
    `partialSumBound_cALiteral`. -/
theorem literal_norm_form_forward_bound (n : ℕ)
    (G M_inv A_inv M N : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (cn_u θ_x : ℝ) (hcn : 0 ≤ cn_u) (hθ : 0 ≤ θ_x)
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hne : (CAValues n G M_inv A_inv).Nonempty) (m : ℕ) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M N x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cALiteral n G M_inv A_inv *
          infNormVec (mainForwardBoundVector n A_inv M N x) :=
  finite_norm_form_forward_bound n G M_inv A_inv M N e₀ x cn_u θ_x
    (cALiteral n G M_inv A_inv) hcn (cALiteral_nonneg n G M_inv A_inv hne)
    hθ m (partialSumBound_cALiteral n G M_inv A_inv hsum hne m)

/-- **Literal uniform-in-m Jacobi forward bound** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.2, eq (17.16)): the
    Jacobi specialization `|M| + |N| = |A|` of the norm-form forward bound
    with the literal constant `c(A)`, valid for all horizons `m`
    simultaneously. -/
theorem literal_norm_form_jacobi_forward_bound (n : ℕ)
    (A G M_inv A_inv M N : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (cn_u θ_x : ℝ) (hcn : 0 ≤ cn_u) (hθ : 0 ≤ θ_x)
    (hM : ∀ i j, M i j = if i = j then A i i else 0)
    (hN : ∀ i j, N i j = M i j - A i j)
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hne : (CAValues n G M_inv A_inv).Nonempty) (m : ℕ) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M N x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cALiteral n G M_inv A_inv *
          infNormVec (jacobiForwardBoundVector n A_inv A x) :=
  finite_norm_form_jacobi_forward_bound n A G M_inv A_inv M N e₀ x cn_u θ_x
    (cALiteral n G M_inv A_inv) hcn (cALiteral_nonneg n G M_inv A_inv hne)
    hθ hM hN m (partialSumBound_cALiteral n G M_inv A_inv hsum hne m)

/-- **Literal uniform-in-m SOR forward bound** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.2, eq (17.17)): the SOR
    specialization with multiplier `f(ω) = (1 + |1 - ω|)/ω` of the norm-form
    forward bound with the literal constant `c(A)`, valid for all horizons
    `m` simultaneously. -/
theorem literal_norm_form_sor_forward_bound (n : ℕ)
    (A G M_inv A_inv D L U M_sor N_sor : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (ω cn_u θ_x : ℝ) (hω_pos : 0 < ω) (hcn : 0 ≤ cn_u) (hθ : 0 ≤ θ_x)
    (hDecomp : ∀ i j, A i j = D i j + L i j + U i j)
    (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, j.val ≥ i.val → L i j = 0)
    (hU : ∀ i j, j.val ≤ i.val → U i j = 0)
    (hM : ∀ i j, M_sor i j = (1 / ω) * (D i j + ω * L i j))
    (hN : ∀ i j, N_sor i j = (1 / ω) * ((1 - ω) * D i j - ω * U i j))
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hne : (CAValues n G M_inv A_inv).Nonempty) (m : ℕ) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M_sor N_sor x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cALiteral n G M_inv A_inv *
          (sorForwardFactor ω *
            infNormVec (jacobiForwardBoundVector n A_inv A x)) :=
  finite_norm_form_sor_forward_bound n A G M_inv A_inv D L U M_sor N_sor e₀ x
    ω cn_u θ_x (cALiteral n G M_inv A_inv) hω_pos hcn
    (cALiteral_nonneg n G M_inv A_inv hne) hθ hDecomp hD hL hU hM hN m
    (partialSumBound_cALiteral n G M_inv A_inv hsum hne m)

/-- **Literal uniform-in-m Gauss-Seidel forward bound** (Higham, Accuracy
    and Stability of Numerical Algorithms, 2nd ed., §17.2.2, following
    eq (17.17): Gauss-Seidel is SOR with `ω = 1`, so `f(1) = 1`): the
    Gauss-Seidel specialization of the norm-form forward bound with the
    literal constant `c(A)`, valid for all horizons `m` simultaneously. -/
theorem literal_norm_form_gaussSeidel_forward_bound (n : ℕ)
    (A G M_inv A_inv D L U M_gs N_gs : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (cn_u θ_x : ℝ) (hcn : 0 ≤ cn_u) (hθ : 0 ≤ θ_x)
    (hDecomp : ∀ i j, A i j = D i j + L i j + U i j)
    (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, j.val ≥ i.val → L i j = 0)
    (hU : ∀ i j, j.val ≤ i.val → U i j = 0)
    (hM : ∀ i j, M_gs i j = D i j + L i j)
    (hN : ∀ i j, N_gs i j = -U i j)
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hne : (CAValues n G M_inv A_inv).Nonempty) (m : ℕ) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M_gs N_gs x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cALiteral n G M_inv A_inv *
          infNormVec (jacobiForwardBoundVector n A_inv A x) :=
  finite_norm_form_gaussSeidel_forward_bound n A G M_inv A_inv D L U M_gs N_gs
    e₀ x cn_u θ_x (cALiteral n G M_inv A_inv) hcn
    (cALiteral_nonneg n G M_inv A_inv hne) hθ hDecomp hD hL hU hM hN m
    (partialSumBound_cALiteral n G M_inv A_inv hsum hne m)

-- ============================================================
-- §17.3  C. The literal (17.20) entrywise tsum sigma model
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.3,
    paragraph before eq (17.20): the literal `(i,j)` entry of the infinite
    sigma series `Σ_{k=0}^∞ |H^k (I - H)|`.  Scope: like every real `tsum`
    this evaluates to `0` when not summable; `summable_residualSigmaEntry`
    certifies summability under `‖H‖∞ ≤ q < 1`. -/
noncomputable def residualSigmaEntry (n : ℕ) (H : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  ∑' k : ℕ, |matMul n (matPow n H k) (matSub_id n H) i j|

/-- The literal (17.20) sigma entries are nonnegative. -/
theorem residualSigmaEntry_nonneg (n : ℕ) (H : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    0 ≤ residualSigmaEntry n H i j :=
  tsum_nonneg fun _ => abs_nonneg _

/-- Geometric majorant for the terms of the sigma series in Higham,
    Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.3,
    eq (17.20): each entry satisfies
    `||H^k (I - H)|_{ij}| ≤ q^k · ‖I - H‖∞` (single entry ≤ row sum ≤
    matrix norm, then submultiplicativity and the power bound). -/
theorem residual_entry_abs_le_geometric (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (q : ℝ) (hH : infNorm H ≤ q)
    (i j : Fin n) (k : ℕ) :
    |matMul n (matPow n H k) (matSub_id n H) i j| ≤
      q ^ k * infNorm (matSub_id n H) :=
  calc |matMul n (matPow n H k) (matSub_id n H) i j|
      ≤ ∑ l : Fin n, |matMul n (matPow n H k) (matSub_id n H) i l| :=
        Finset.single_le_sum
          (f := fun l => |matMul n (matPow n H k) (matSub_id n H) i l|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ infNorm (matMul n (matPow n H k) (matSub_id n H)) :=
        row_sum_le_infNorm _ i
    _ ≤ infNorm (matPow n H k) * infNorm (matSub_id n H) :=
        infNorm_matMul_le hn _ _
    _ ≤ q ^ k * infNorm (matSub_id n H) :=
        mul_le_mul_of_nonneg_right
          ((infNorm_matPow_le hn H k).trans
            (pow_le_pow_left₀ (infNorm_nonneg H) hH k))
          (infNorm_nonneg _)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.3,
    eq (17.20): entrywise summability of the sigma series
    `Σ_k ||H^k (I - H)|_{ij}|` under the norm certificate `‖H‖∞ ≤ q < 1`,
    by comparison with the geometric majorant `q^k · ‖I - H‖∞`. -/
theorem summable_residualSigmaEntry (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) (i j : Fin n) :
    Summable (fun k => |matMul n (matPow n H k) (matSub_id n H) i j|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun k => residual_entry_abs_le_geometric n hn H q hH i j k)
    ((summable_geometric_of_lt_one hq0 hq1).mul_right (infNorm (matSub_id n H)))

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.3,
    paragraph before eq (17.20): the literal entrywise `tsum` sigma matrix
    `Σ_{k=0}^∞ |H^k (I - H)|`. -/
noncomputable def residualSigmaMatrix (n : ℕ) (H : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => residualSigmaEntry n H i j

/-- The finite partial sigma matrices are entrywise nonnegative. -/
theorem finiteResidualSigmaMatrix_nonneg (n : ℕ) (H : Fin n → Fin n → ℝ)
    (m : ℕ) (i j : Fin n) :
    0 ≤ finiteResidualSigmaMatrix n H m i j :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Each finite partial sigma matrix is entrywise dominated by the literal
    `tsum` sigma matrix (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.3, eq (17.20)): partial sums of a summable
    nonnegative series are below its `tsum`. -/
theorem finiteResidualSigmaMatrix_le_residualSigmaMatrix (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q)
    (m : ℕ) (i j : Fin n) :
    finiteResidualSigmaMatrix n H m i j ≤ residualSigmaMatrix n H i j :=
  Summable.sum_le_tsum (Finset.range (m + 1)) (fun _ _ => abs_nonneg _)
    (summable_residualSigmaEntry n hn H q hq0 hq1 hH i j)

/-- Every finite partial sigma norm is dominated by the norm of the literal
    `tsum` sigma matrix (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.3, eq (17.20)): row sums are monotone under
    the entrywise domination of nonnegative matrices. -/
theorem finiteResidualSigma_le_infNorm_residualSigmaMatrix (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) (m : ℕ) :
    finiteResidualSigma n H m ≤ infNorm (residualSigmaMatrix n H) := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |finiteResidualSigmaMatrix n H m i j|
        = ∑ j : Fin n, finiteResidualSigmaMatrix n H m i j :=
          Finset.sum_congr rfl fun j _ =>
            abs_of_nonneg (finiteResidualSigmaMatrix_nonneg n H m i j)
      _ ≤ ∑ j : Fin n, residualSigmaMatrix n H i j :=
          Finset.sum_le_sum fun j _ =>
            finiteResidualSigmaMatrix_le_residualSigmaMatrix
              n hn H q hq0 hq1 hH m i j
      _ = ∑ j : Fin n, |residualSigmaMatrix n H i j| :=
          Finset.sum_congr rfl fun j _ =>
            (abs_of_nonneg (residualSigmaEntry_nonneg n H i j)).symm
      _ ≤ infNorm (residualSigmaMatrix n H) :=
          row_sum_le_infNorm _ i
  · exact infNorm_nonneg _

/-- The candidate finite partial sigma norms are bounded above under the
    norm certificate `‖H‖∞ ≤ q < 1` — the `bddAbove` input that makes the
    supremum envelope `residualSigmaSup` meaningful. -/
theorem bddAbove_residualSigmaValues (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    BddAbove (ResidualSigmaValues n H) := by
  refine ⟨infNorm (residualSigmaMatrix n H), fun y hy => ?_⟩
  rcases hy with ⟨m, rfl⟩
  exact finiteResidualSigma_le_infNorm_residualSigmaMatrix n hn H q hq0 hq1 hH m

/-- One half of the (17.20) equality: the supremum envelope is dominated by
    the norm of the literal `tsum` sigma matrix (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.3, eq (17.20)). -/
theorem residualSigmaSup_le_infNorm_residualSigmaMatrix (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    residualSigmaSup n H ≤ infNorm (residualSigmaMatrix n H) :=
  residualSigmaSup_le_of_finiteResidualSigma_le n H _
    (fun m => finiteResidualSigma_le_infNorm_residualSigmaMatrix
      n hn H q hq0 hq1 hH m)

/-- Other half of the (17.20) equality: the norm of the literal `tsum` sigma
    matrix is dominated by the supremum envelope (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.3, eq (17.20)).  Route:
    each row sum of the `tsum` matrix is a `tsum` of finite row sums (the
    finite-sum/`tsum` exchange), whose partial sums are row sums of the
    finite partial sigma matrices, hence below the supremum envelope. -/
theorem infNorm_residualSigmaMatrix_le_residualSigmaSup (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    infNorm (residualSigmaMatrix n H) ≤ residualSigmaSup n H := by
  have hbdd : BddAbove (ResidualSigmaValues n H) :=
    bddAbove_residualSigmaValues n hn H q hq0 hq1 hH
  have hsup0 : 0 ≤ residualSigmaSup n H :=
    le_trans (infNorm_nonneg (finiteResidualSigmaMatrix n H 0))
      (le_csSup hbdd ⟨0, rfl⟩)
  apply infNorm_le_of_row_sum_le
  · intro i
    have habs : ∑ j : Fin n, |residualSigmaMatrix n H i j| =
        ∑ j : Fin n, residualSigmaEntry n H i j :=
      Finset.sum_congr rfl fun j _ =>
        abs_of_nonneg (residualSigmaEntry_nonneg n H i j)
    rw [habs]
    have hexch : ∑ j : Fin n, residualSigmaEntry n H i j =
        ∑' k : ℕ, ∑ j : Fin n,
          |matMul n (matPow n H k) (matSub_id n H) i j| := by
      unfold residualSigmaEntry
      exact (Summable.tsum_finsetSum
        (fun j _ => summable_residualSigmaEntry n hn H q hq0 hq1 hH i j)).symm
    rw [hexch]
    apply Real.tsum_le_of_sum_range_le
    · intro k
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · intro mtot
      cases mtot with
      | zero => simpa using hsup0
      | succ m =>
        have hcomm : ∑ k ∈ Finset.range (m + 1), ∑ j : Fin n,
            |matMul n (matPow n H k) (matSub_id n H) i j| =
            ∑ j : Fin n, finiteResidualSigmaMatrix n H m i j := by
          unfold finiteResidualSigmaMatrix
          exact Finset.sum_comm
        rw [hcomm]
        calc ∑ j : Fin n, finiteResidualSigmaMatrix n H m i j
            = ∑ j : Fin n, |finiteResidualSigmaMatrix n H m i j| :=
              Finset.sum_congr rfl fun j _ =>
                (abs_of_nonneg (finiteResidualSigmaMatrix_nonneg n H m i j)).symm
          _ ≤ finiteResidualSigma n H m :=
              row_sum_le_infNorm (finiteResidualSigmaMatrix n H m) i
          _ ≤ residualSigmaSup n H := le_csSup hbdd ⟨m, rfl⟩
  · exact hsup0

/-- **The literal (17.20) sigma equality** (Higham, Accuracy and Stability
    of Numerical Algorithms, 2nd ed., §17.3, eq (17.20)): the infinity norm
    of the literal entrywise `tsum` matrix series `Σ_{k=0}^∞ |H^k (I - H)|`
    EQUALS the supremum envelope `residualSigmaSup` of the finite partial
    sigma norms, under the norm certificate `‖H‖∞ ≤ q < 1`.  This closes
    the gap between the `tsum` sigma model and the `sSup`-based finite
    model used by the residual bounds of §17.3. -/
theorem infNorm_residualSigmaMatrix_eq_residualSigmaSup (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    infNorm (residualSigmaMatrix n H) = residualSigmaSup n H :=
  le_antisymm
    (infNorm_residualSigmaMatrix_le_residualSigmaSup n hn H q hq0 hq1 hH)
    (residualSigmaSup_le_infNorm_residualSigmaMatrix n hn H q hq0 hq1 hH)

-- ============================================================
-- Bridges to the `residualSigmaTsum` surface of StationaryIteration.lean
-- ============================================================

/-- The two independently developed literal sigma objects coincide: this
    module's `residualSigmaMatrix` and `StationaryIteration.lean`'s
    `residualSigmaTsumMatrix` are the same entrywise `tsum`, so the scalar
    `residualSigmaTsum` is definitionally the ∞-norm of
    `residualSigmaMatrix`. -/
theorem residualSigmaTsum_eq_infNorm_residualSigmaMatrix (n : ℕ)
    (H : Fin n → Fin n → ℝ) :
    residualSigmaTsum n H = infNorm (residualSigmaMatrix n H) := rfl

/-- **Eq (17.20), literal `tsum` sigma equals the supremum envelope**
    (Higham 2nd ed., §17.3): under a norm certificate `‖H‖∞ ≤ q < 1`, the
    scalar `residualSigmaTsum` coincides with the supremum of the finite
    partial norms `residualSigmaSup`. -/
theorem residualSigmaTsum_eq_residualSigmaSup (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    residualSigmaTsum n H = residualSigmaSup n H := by
  rw [residualSigmaTsum_eq_infNorm_residualSigmaMatrix]
  exact infNorm_residualSigmaMatrix_eq_residualSigmaSup n hn H q hq0 hq1 hH

/-- **Eq (17.20), q-certificate bridge for the literal diagonalizable sigma
    bound on the `tsum` object**
    (Higham 2nd ed., §17.3): with real diagonalization data `X⁻¹HX = J`
    (`|J i i| < 1`) and a norm certificate `‖H‖∞ ≤ q < 1`, the literal
    series sigma satisfies
    `residualSigmaTsum ≤ κ∞(X) · diagonalResidualRatioMax`.  Composes the
    envelope equality with the finite-partial diagonalization bound from
    `StationaryIteration.lean`. -/
theorem residualSigmaTsum_le_diagonalizable_max_bound_of_infNorm_bound
    (n : ℕ) (hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    residualSigmaTsum n H ≤
      (infNorm X * infNorm X_inv) * diagonalResidualRatioMax n J hn := by
  rw [residualSigmaTsum_eq_residualSigmaSup n hn H q hq0 hq1 hH]
  exact residualSigmaSup_le_diagonalizable_max_bound n hn H X X_inv J
    hXr hXl hsim hdiag hLam

end NumStability
