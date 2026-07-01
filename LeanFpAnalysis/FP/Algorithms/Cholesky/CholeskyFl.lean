-- Algorithms/Cholesky/CholeskyFl.lean
--
-- Concrete floating-point Cholesky foundations (Higham §10.1, 2nd ed.,
-- Algorithm 10.2 / Theorem 10.3, pp. 197-199).
--
-- Algorithm 10.2 computes, for each entry of the upper factor,
--   off-diagonal:  r̂_ij = fl((a_ij − ∑_{k<i} r̂_ki r̂_kj) / r̂_ii)
--   diagonal:      r̂_jj = fl(√(a_jj − ∑_{k<j} r̂_kj²))
-- This file proves the per-entry rounding specifications of these two scalar
-- steps over the standard model, generically in the previously computed
-- entries.  They are the local facts from which the Theorem 10.3 backward
-- error certificate (`CholeskyBackwardError`) is assembled by recursion.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.SubtractionFold
import LeanFpAnalysis.FP.Analysis.Summation
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyDemmel

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-- **Cholesky partial-pivot fold** (Higham §10.1, Algorithm 10.2).

    The sequentially rounded evaluation of `c − ∑_k x k * y k`:
    the common inner expression of both Cholesky entry recurrences, with
    `c` an entry of `A` and `x`, `y` previously computed factor columns. -/
noncomputable def fl_cholSubFold (fp : FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (c : ℝ) : ℝ :=
  Fin.foldl m (fun acc k => fp.fl_sub acc (fp.fl_mul (x k) (y k))) c

/-- **Cholesky partial-pivot fold error** (Higham §10.1, Algorithm 10.2 inner
    expression; standard-model expansion in the style of §8.1, Lemma 8.4).

    The rounded fold equals `c (1 + Θ) − ∑ x k y k (1 + θ k)` with
    `|Θ| ≤ γ_m` and `|θ k| ≤ γ_{m+1}`: each product term absorbs its
    multiplication rounding plus the suffix of subtraction roundings. -/
theorem fl_cholSubFold_error (fp : FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (c : ℝ) (hm1 : gammaValid fp (m + 1)) :
    ∃ (Θ : ℝ) (θ : Fin m → ℝ),
      |Θ| ≤ gamma fp m ∧ (∀ k, |θ k| ≤ gamma fp (m + 1)) ∧
      fl_cholSubFold fp m x y c =
        c * (1 + Θ) - ∑ k : Fin m, x k * y k * (1 + θ k) := by
  have hm : gammaValid fp m := gammaValid_mono fp (Nat.le_succ m) hm1
  have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hm1
  have h1m : gammaValid fp (1 + m) := by rw [Nat.add_comm]; exact hm1
  obtain ⟨Θ, θsub, hΘ, hθsub, hfold⟩ :=
    fl_sub_sum_error_init fp m (fun k => fp.fl_mul (x k) (y k)) c hm
  have hcomb : ∀ k : Fin m, ∃ η : ℝ, |η| ≤ gamma fp (1 + m) ∧
      fp.fl_mul (x k) (y k) * (1 + θsub k) = x k * y k * (1 + η) := by
    intro k
    obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x k) (y k)
    have hδ1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos h1valid)
    obtain ⟨η, hη, heq⟩ := gamma_mul fp 1 m δ (θsub k) hδ1 (hθsub k) h1m
    exact ⟨η, hη, by rw [hmul, mul_assoc, heq]⟩
  choose η hη hηeq using hcomb
  refine ⟨Θ, η, hΘ, ?_, ?_⟩
  · intro k
    have := hη k
    rwa [Nat.add_comm] at this
  · unfold fl_cholSubFold
    rw [hfold]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hηeq k

/-- **Cholesky off-diagonal entry specification** (Higham §10.1,
    Algorithm 10.2 / Theorem 10.3 off-diagonal step).

    The computed entry `r̂ = fl((c − ∑ x k y k)/d)` satisfies
    `d r̂ = (c (1 + Θ) − ∑ x k y k (1 + θ k)) (1 + ρ)` with `|Θ| ≤ γ_m`,
    `|θ k| ≤ γ_{m+1}`, `|ρ| ≤ u`: the entry of `A` is recovered by the
    computed inner product up to the per-operation rounding factors that
    Theorem 10.3 compresses into the `γ_{n+1}` certificate. -/
theorem fl_chol_offdiag_step_error (fp : FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (c d : ℝ) (hd : d ≠ 0)
    (hm1 : gammaValid fp (m + 1)) :
    ∃ (Θ : ℝ) (θ : Fin m → ℝ) (ρ : ℝ),
      |Θ| ≤ gamma fp m ∧ (∀ k, |θ k| ≤ gamma fp (m + 1)) ∧ |ρ| ≤ fp.u ∧
      d * fp.fl_div (fl_cholSubFold fp m x y c) d =
        (c * (1 + Θ) - ∑ k : Fin m, x k * y k * (1 + θ k)) * (1 + ρ) := by
  obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ := fl_cholSubFold_error fp m x y c hm1
  obtain ⟨ρ, hρ, hdiv⟩ := fp.model_div (fl_cholSubFold fp m x y c) d hd
  refine ⟨Θ, θ, ρ, hΘ, hθ, hρ, ?_⟩
  rw [hdiv, ← hfold]
  field_simp

/-- **Cholesky diagonal entry specification** (Higham §10.1,
    Algorithm 10.2 / Theorem 10.3 diagonal step).

    When the rounded partial pivot is nonnegative (the success case governed
    by Theorem 10.7), the computed diagonal entry `r̂ = fl(√(c − ∑ x k²))`
    satisfies `r̂² = (c (1 + Θ) − ∑ x k² (1 + θ k)) (1 + η)` with
    `|Θ| ≤ γ_m`, `|θ k| ≤ γ_{m+1}`, `|η| ≤ 2u + u²`. -/
theorem fl_chol_diag_step_error (fp : FPModel) (m : ℕ)
    (x : Fin m → ℝ) (c : ℝ)
    (hs : 0 ≤ fl_cholSubFold fp m x x c)
    (hm1 : gammaValid fp (m + 1)) :
    ∃ (Θ : ℝ) (θ : Fin m → ℝ) (η : ℝ),
      |Θ| ≤ gamma fp m ∧ (∀ k, |θ k| ≤ gamma fp (m + 1)) ∧
      |η| ≤ 2 * fp.u + fp.u ^ 2 ∧
      (fp.fl_sqrt (fl_cholSubFold fp m x x c)) ^ 2 =
        (c * (1 + Θ) - ∑ k : Fin m, x k * x k * (1 + θ k)) * (1 + η) := by
  obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ := fl_cholSubFold_error fp m x x c hm1
  obtain ⟨η, hη, hsq⟩ := fl_sqrt_sq_backward_error fp _ hs
  exact ⟨Θ, θ, η, hΘ, hθ, hη, by rw [hsq, hfold]⟩

set_option linter.unusedVariables false in
/-- **Algorithm 10.2** (Higham §10.1), entry recursion over `ℕ` indices.

    Column-major evaluation of the upper Cholesky factor:
    `r̂_ij = fl((a_ij − ∑_{k<i} r̂_ki r̂_kj) / r̂_ii)` for `i < j` and
    `r̂_jj = fl(√(a_jj − ∑_{k<j} r̂_kj²))`, with junk value `0` below the
    diagonal and outside the matrix range.  Recursion is well-founded in the
    lexicographic order on (column, row). -/
noncomputable def fl_cholEntry (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : ℕ → ℕ → ℝ
  | i, j =>
    if h : i < n ∧ j < n then
      if hij : i < j then
        fp.fl_div
          (fl_cholSubFold fp i
            (fun k => fl_cholEntry fp n A k.val i)
            (fun k => fl_cholEntry fp n A k.val j)
            (A ⟨i, h.1⟩ ⟨j, h.2⟩))
          (fl_cholEntry fp n A i i)
      else if hji : i = j then
        fp.fl_sqrt
          (fl_cholSubFold fp i
            (fun k => fl_cholEntry fp n A k.val i)
            (fun k => fl_cholEntry fp n A k.val i)
            (A ⟨i, h.1⟩ ⟨i, h.1⟩))
      else 0
    else 0
  termination_by i j => (j, i)
  decreasing_by
  all_goals
    first
      | exact Prod.Lex.left _ _ hij
      | exact Prod.Lex.right _ k.isLt
      | (subst hji; exact Prod.Lex.right _ k.isLt)

/-- **Algorithm 10.2** (Higham §10.1): the computed floating-point Cholesky
    factor `R̂` as a `Fin n` matrix. -/
noncomputable def fl_cholesky (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => fl_cholEntry fp n A i.val j.val

/-- The computed factor is upper triangular: entries strictly below the
    diagonal are the algorithm's junk value `0`. -/
theorem fl_cholesky_strict_lower (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (i j : Fin n) (h : j.val < i.val) :
    fl_cholesky fp n A i j = 0 := by
  unfold fl_cholesky
  rw [fl_cholEntry.eq_1]
  have h1 : ¬ i.val < j.val := by omega
  have h2 : ¬ i.val = j.val := by omega
  simp [i.isLt, j.isLt, h1, h2]

/-- **Algorithm 10.2 off-diagonal recurrence, matrix form**:
    `R̂ i j = fl((A i j − ∑_{k<i} R̂ k i · R̂ k j) / R̂ i i)` for `i < j`. -/
theorem fl_cholesky_offdiag_eq (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (i j : Fin n) (hij : i.val < j.val) :
    fl_cholesky fp n A i j =
      fp.fl_div
        (fl_cholSubFold fp i.val
          (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ i)
          (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ j)
          (A i j))
        (fl_cholesky fp n A i i) := by
  show fl_cholEntry fp n A i.val j.val = _
  rw [fl_cholEntry.eq_1]
  rw [dif_pos (⟨i.isLt, j.isLt⟩ : i.val < n ∧ j.val < n), dif_pos hij]
  rfl

/-- **Algorithm 10.2 diagonal recurrence, matrix form**:
    `R̂ j j = fl(√(A j j − ∑_{k<j} (R̂ k j)²))`. -/
theorem fl_cholesky_diag_eq (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (j : Fin n) :
    fl_cholesky fp n A j j =
      fp.fl_sqrt
        (fl_cholSubFold fp j.val
          (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩ j)
          (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩ j)
          (A j j)) := by
  show fl_cholEntry fp n A j.val j.val = _
  rw [fl_cholEntry.eq_1]
  rw [dif_pos (⟨j.isLt, j.isLt⟩ : j.val < n ∧ j.val < n),
      dif_neg (lt_irrefl j.val), dif_pos rfl]
  rfl

/-- **Factor-level subtraction-fold expansion** (Higham §3.1/§3.4 bookkeeping
    for Algorithm 10.2, uncompressed form).

    Unlike `fl_sub_sum_error_init`, which compresses rounding factors into
    `γ` witnesses, this exposes the actual local subtraction factors:
    the initial accumulator passes through every subtraction, while term `k`
    passes through only the suffix of subtractions from its insertion step.
    This uncompressed form is required for the sharp `γ_{n+1}` constant of
    Theorem 10.3: the factors shared between the accumulator product and each
    term's suffix product cancel when the recurrence is solved for `A i j`. -/
theorem fl_sub_fold_local_factors (fp : FPModel) (m : ℕ)
    (t : Fin m → ℝ) (c : ℝ) :
    ∃ δ : Fin m → ℝ, (∀ s, |δ s| ≤ fp.u) ∧
      Fin.foldl m (fun acc k => fp.fl_sub acc (t k)) c =
        c * ∏ s : Fin m, (1 + δ s) -
          ∑ k : Fin m, t k * sumSuffixErrorProduct m δ k := by
  induction m with
  | zero =>
      exact ⟨fun s => s.elim0, fun s => s.elim0, by simp⟩
  | succ m ih =>
      obtain ⟨δ', hδ', hfold⟩ := ih (fun k => t k.castSucc)
      obtain ⟨δl, hδl, hsub⟩ := fp.model_sub
        (Fin.foldl m (fun acc k => fp.fl_sub acc (t k.castSucc)) c)
        (t (Fin.last m))
      refine ⟨(Fin.snoc δ' δl : Fin (m + 1) → ℝ), ?_, ?_⟩
      · intro s
        refine Fin.lastCases ?_ ?_ s
        · rw [Fin.snoc_last]; exact hδl
        · intro s; rw [Fin.snoc_castSucc]; exact hδ' s
      · have hsuffix_cast : ∀ k : Fin m,
            sumSuffixErrorProduct (m + 1) (Fin.snoc δ' δl) k.castSucc =
              sumSuffixErrorProduct m δ' k * (1 + δl) := by
          intro k
          rw [sumSuffixErrorProduct_eq_prod_if, sumSuffixErrorProduct_eq_prod_if,
              Fin.prod_univ_castSucc]
          congr 1
          · apply Finset.prod_congr rfl
            intro j _
            simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last, Nat.le_of_lt k.isLt]
        have hsuffix_last :
            sumSuffixErrorProduct (m + 1) (Fin.snoc δ' δl) (Fin.last m) =
              1 + δl := by
          rw [sumSuffixErrorProduct_eq_prod_if, Fin.prod_univ_castSucc]
          have h1 : ∀ j : Fin m,
              (if (Fin.last m).val ≤ (j.castSucc).val
                then 1 + (Fin.snoc δ' δl : Fin (m + 1) → ℝ) j.castSucc
                else 1) = 1 := by
            intro j
            rw [if_neg]
            simp only [Fin.val_last, Fin.val_castSucc]
            exact Nat.not_le.mpr j.isLt
          rw [Finset.prod_congr rfl (fun j _ => h1 j)]
          simp [Fin.snoc_last]
        rw [Fin.foldl_succ_last, hsub, hfold,
            Fin.prod_univ_castSucc, Fin.sum_univ_castSucc, hsuffix_last]
        simp only [hsuffix_cast, Fin.snoc_castSucc, Fin.snoc_last]
        have hsum : ∑ k : Fin m,
              t k.castSucc * (sumSuffixErrorProduct m δ' k * (1 + δl)) =
            (∑ k : Fin m, t k.castSucc * sumSuffixErrorProduct m δ' k) *
              (1 + δl) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [hsum]
        ring

-- ============================================================
-- §10.1  Sharp solve forms for the Algorithm 10.2 recurrences
--        (Higham Theorem 10.3 per-entry equations, Stewart counters)
-- ============================================================

private lemma one_add_pos_of_abs_le_u {fp : FPModel} {δ : ℝ}
    (h : |δ| ≤ fp.u) (hu : fp.u < 1) : (0 : ℝ) < 1 + δ := by
  have := abs_le.mp h
  linarith [this.1]

private lemma u_lt_one_of_gammaValid_succ {fp : FPModel} {m : ℕ}
    (hm1 : gammaValid fp (m + 1)) : fp.u < 1 := by
  unfold gammaValid at hm1
  push_cast at hm1
  nlinarith [mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ)) fp.u_nonneg]

private lemma counter_one (fp : FPModel) {δ : ℝ} (hδ : |δ| ≤ fp.u) :
    relErrorCounter fp 1 (1 + δ) :=
  ⟨fun _ => δ, fun _ => false, fun _ => hδ, by simp⟩

private lemma counter_plain_prod (fp : FPModel) (m : ℕ) (δ : Fin m → ℝ)
    (hδ : ∀ s, |δ s| ≤ fp.u) :
    relErrorCounter fp m (∏ s : Fin m, (1 + δ s)) :=
  ⟨δ, fun _ => false, hδ, by simp⟩

/-- Prefix product of subtraction factors strictly before insertion step `k`.
    Complements `sumSuffixErrorProduct`: their product is the full factor
    product, which is the cancellation behind the sharp Theorem 10.3
    constant. -/
private lemma suffix_mul_prefix_eq_prod (m : ℕ) (δ : Fin m → ℝ) (k : Fin m) :
    sumSuffixErrorProduct m δ k *
      (∏ j : Fin m, if j.val < k.val then 1 + δ j else 1) =
    ∏ s : Fin m, (1 + δ s) := by
  rw [sumSuffixErrorProduct_eq_prod_if, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rcases Nat.lt_or_ge j.val k.val with h | h
  · rw [if_neg (Nat.not_le.mpr h), if_pos h, one_mul]
  · rw [if_pos h, if_neg (Nat.not_lt.mpr h), mul_one]

/-- The Cholesky per-term local factor `(1 + μ)/(prefix product)` is a
    Stewart counter of `m + 1` factors, hence within `γ_{m+1}` of `1`. -/
private lemma chol_term_factor_bound (fp : FPModel) (m : ℕ)
    (δ : Fin m → ℝ) (μk : ℝ) (k : Fin m)
    (hδ : ∀ s, |δ s| ≤ fp.u) (hμ : |μk| ≤ fp.u)
    (hm1 : gammaValid fp (m + 1)) :
    |(1 + μk) / (∏ j : Fin m, if j.val < k.val then 1 + δ j else 1) - 1| ≤
      gamma fp (m + 1) := by
  have hu : fp.u < 1 := u_lt_one_of_gammaValid_succ hm1
  have hQcnt : relErrorCounter fp m
      (∏ j : Fin m, if j.val < k.val then 1 + δ j else 1) := by
    refine ⟨fun j => if j.val < k.val then δ j else 0, fun _ => false, ?_, ?_⟩
    · intro j
      by_cases h : j.val < k.val
      · simpa [h] using hδ j
      · simpa [h] using fp.u_nonneg
    · simp only [Bool.false_eq_true, if_false]
      apply Finset.prod_congr rfl
      intro j _
      by_cases h : j.val < k.val <;> simp [h]
  have hcnt : relErrorCounter fp (1 + m)
      ((1 + μk) * (1 / ∏ j : Fin m, if j.val < k.val then 1 + δ j else 1)) :=
    relErrorCounter_mul fp 1 m _ _ (counter_one fp hμ)
      (relErrorCounter_inv fp m _ hQcnt hu)
  rw [Nat.add_comm 1 m] at hcnt
  have := relErrorCounter_abs_sub_one_le_gamma fp (m + 1) _ hcnt hm1
  rwa [mul_one_div] at this

/-- **Algorithm 10.2 off-diagonal solve form** (Higham §10.1, Theorem 10.3
    off-diagonal equation, sharp constants).

    The computed entry `r̂ = fl((c − ∑ x k y k)/d)` satisfies
    `d r̂ φ₀ = c − ∑ x k y k φ k` where every local factor is within
    `γ_{m+1}` of `1`.  The sharp constant comes from the factor-level fold
    expansion: each term's suffix factors cancel against the accumulator
    product, leaving at most `m + 1` signed factors per term. -/
theorem fl_chol_offdiag_solve_form (fp : FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (c d : ℝ) (hd : d ≠ 0)
    (hm1 : gammaValid fp (m + 1)) :
    ∃ (φ₀ : ℝ) (φ : Fin m → ℝ),
      |φ₀ - 1| ≤ gamma fp (m + 1) ∧
      (∀ k, |φ k - 1| ≤ gamma fp (m + 1)) ∧
      d * fp.fl_div (fl_cholSubFold fp m x y c) d * φ₀ =
        c - ∑ k : Fin m, x k * y k * φ k := by
  have hu : fp.u < 1 := u_lt_one_of_gammaValid_succ hm1
  obtain ⟨δ, hδ, hfold⟩ := fl_sub_fold_local_factors fp m
    (fun k => fp.fl_mul (x k) (y k)) c
  choose μ hμ hμeq using fun k : Fin m => fp.model_mul (x k) (y k)
  obtain ⟨ρ, hρ, hdiv⟩ := fp.model_div (fl_cholSubFold fp m x y c) d hd
  have hfac : ∀ s : Fin m, (0:ℝ) < 1 + δ s :=
    fun s => one_add_pos_of_abs_le_u (hδ s) hu
  have hρpos : (0:ℝ) < 1 + ρ := one_add_pos_of_abs_le_u hρ hu
  have hP : (0:ℝ) < ∏ s : Fin m, (1 + δ s) :=
    Finset.prod_pos fun s _ => hfac s
  have hQ : ∀ k : Fin m,
      (0:ℝ) < ∏ j : Fin m, (if j.val < k.val then 1 + δ j else 1) := by
    intro k
    apply Finset.prod_pos
    intro j _
    by_cases h : j.val < k.val <;> simp [h, hfac j]
  -- φ₀ bound
  have hφ₀cnt : relErrorCounter fp (m + 1)
      (1 / ((∏ s : Fin m, (1 + δ s)) * (1 + ρ))) :=
    relErrorCounter_inv fp (m + 1) _
      (relErrorCounter_mul fp m 1 _ _
        (counter_plain_prod fp m δ hδ) (counter_one fp hρ)) hu
  have hφ₀ : |1 / ((∏ s : Fin m, (1 + δ s)) * (1 + ρ)) - 1| ≤
      gamma fp (m + 1) :=
    relErrorCounter_abs_sub_one_le_gamma fp (m + 1) _ hφ₀cnt hm1
  refine ⟨1 / ((∏ s : Fin m, (1 + δ s)) * (1 + ρ)),
    fun k => (1 + μ k) /
      (∏ j : Fin m, if j.val < k.val then 1 + δ j else 1),
    hφ₀, fun k => chol_term_factor_bound fp m δ (μ k) k hδ (hμ k) hm1, ?_⟩
  have hfold' : fl_cholSubFold fp m x y c =
      c * ∏ s : Fin m, (1 + δ s) -
        ∑ k : Fin m, x k * y k * (1 + μ k) * sumSuffixErrorProduct m δ k := by
    have h0 : fl_cholSubFold fp m x y c =
        c * ∏ s : Fin m, (1 + δ s) -
          ∑ k : Fin m, fp.fl_mul (x k) (y k) * sumSuffixErrorProduct m δ k :=
      hfold
    rw [h0]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hμeq k]
  rw [hdiv]
  have hLHS : d * (fl_cholSubFold fp m x y c / d * (1 + ρ)) *
      (1 / ((∏ s : Fin m, (1 + δ s)) * (1 + ρ))) =
      fl_cholSubFold fp m x y c / (∏ s : Fin m, (1 + δ s)) := by
    field_simp
  rw [hLHS, hfold', sub_div]
  congr 1
  · field_simp
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    have hSP := suffix_mul_prefix_eq_prod m δ k
    show x k * y k * (1 + μ k) * sumSuffixErrorProduct m δ k /
        (∏ s : Fin m, (1 + δ s)) =
      x k * y k *
        ((1 + μ k) / ∏ j : Fin m, if j.val < k.val then 1 + δ j else 1)
    rw [← mul_div_assoc, div_eq_div_iff hP.ne' (hQ k).ne']
    linear_combination (x k * y k * (1 + μ k)) * hSP

/-- **Algorithm 10.2 diagonal solve form** (Higham §10.1, Theorem 10.3
    diagonal equation, sharp constants).

    When the rounded partial pivot is nonnegative, the computed diagonal
    entry `r̂ = fl(√(c − ∑ x k²))` satisfies `r̂² φ₀ = c − ∑ x k² φ k` with
    `|φ₀ − 1| ≤ γ_{m+2}` (the two square-root factors join the accumulator
    product) and `|φ k − 1| ≤ γ_{m+1}`. -/
theorem fl_chol_diag_solve_form (fp : FPModel) (m : ℕ)
    (x : Fin m → ℝ) (c : ℝ)
    (hs : 0 ≤ fl_cholSubFold fp m x x c)
    (hm2 : gammaValid fp (m + 2)) :
    ∃ (φ₀ : ℝ) (φ : Fin m → ℝ),
      |φ₀ - 1| ≤ gamma fp (m + 2) ∧
      (∀ k, |φ k - 1| ≤ gamma fp (m + 1)) ∧
      (fp.fl_sqrt (fl_cholSubFold fp m x x c)) ^ 2 * φ₀ =
        c - ∑ k : Fin m, x k * x k * φ k := by
  have hm1 : gammaValid fp (m + 1) :=
    gammaValid_mono fp (by omega) hm2
  have hu : fp.u < 1 := u_lt_one_of_gammaValid_succ hm1
  obtain ⟨δ, hδ, hfold⟩ := fl_sub_fold_local_factors fp m
    (fun k => fp.fl_mul (x k) (x k)) c
  choose μ hμ hμeq using fun k : Fin m => fp.model_mul (x k) (x k)
  obtain ⟨σ, hσ, hsqrt⟩ := fp.model_sqrt (fl_cholSubFold fp m x x c) hs
  have hfac : ∀ s : Fin m, (0:ℝ) < 1 + δ s :=
    fun s => one_add_pos_of_abs_le_u (hδ s) hu
  have hσpos : (0:ℝ) < 1 + σ := one_add_pos_of_abs_le_u hσ hu
  have hP : (0:ℝ) < ∏ s : Fin m, (1 + δ s) :=
    Finset.prod_pos fun s _ => hfac s
  have hQ : ∀ k : Fin m,
      (0:ℝ) < ∏ j : Fin m, (if j.val < k.val then 1 + δ j else 1) := by
    intro k
    apply Finset.prod_pos
    intro j _
    by_cases h : j.val < k.val <;> simp [h, hfac j]
  -- φ₀ bound: m subtraction factors plus two square-root factors
  have hφ₀cnt : relErrorCounter fp (m + 2)
      (1 / ((∏ s : Fin m, (1 + δ s)) * (1 + σ) * (1 + σ))) :=
    relErrorCounter_inv fp (m + 2) _
      (relErrorCounter_mul fp (m + 1) 1 _ _
        (relErrorCounter_mul fp m 1 _ _
          (counter_plain_prod fp m δ hδ) (counter_one fp hσ))
        (counter_one fp hσ)) hu
  have hφ₀ : |1 / ((∏ s : Fin m, (1 + δ s)) * (1 + σ) * (1 + σ)) - 1| ≤
      gamma fp (m + 2) :=
    relErrorCounter_abs_sub_one_le_gamma fp (m + 2) _ hφ₀cnt hm2
  refine ⟨1 / ((∏ s : Fin m, (1 + δ s)) * (1 + σ) * (1 + σ)),
    fun k => (1 + μ k) /
      (∏ j : Fin m, if j.val < k.val then 1 + δ j else 1),
    hφ₀, fun k => chol_term_factor_bound fp m δ (μ k) k hδ (hμ k) hm1, ?_⟩
  have hfold' : fl_cholSubFold fp m x x c =
      c * ∏ s : Fin m, (1 + δ s) -
        ∑ k : Fin m, x k * x k * (1 + μ k) * sumSuffixErrorProduct m δ k := by
    have h0 : fl_cholSubFold fp m x x c =
        c * ∏ s : Fin m, (1 + δ s) -
          ∑ k : Fin m, fp.fl_mul (x k) (x k) * sumSuffixErrorProduct m δ k :=
      hfold
    rw [h0]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hμeq k]
  have hsq : (fp.fl_sqrt (fl_cholSubFold fp m x x c)) ^ 2 =
      fl_cholSubFold fp m x x c * (1 + σ) ^ 2 := by
    rw [hsqrt, mul_pow, Real.sq_sqrt hs]
  rw [hsq]
  have hLHS : fl_cholSubFold fp m x x c * (1 + σ) ^ 2 *
      (1 / ((∏ s : Fin m, (1 + δ s)) * (1 + σ) * (1 + σ))) =
      fl_cholSubFold fp m x x c / (∏ s : Fin m, (1 + δ s)) := by
    field_simp
  rw [hLHS, hfold', sub_div]
  congr 1
  · field_simp
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    have hSP := suffix_mul_prefix_eq_prod m δ k
    show x k * x k * (1 + μ k) * sumSuffixErrorProduct m δ k /
        (∏ s : Fin m, (1 + δ s)) =
      x k * x k *
        ((1 + μ k) / ∏ j : Fin m, if j.val < k.val then 1 + δ j else 1)
    rw [← mul_div_assoc, div_eq_div_iff hP.ne' (hQ k).ne']
    linear_combination (x k * x k * (1 + μ k)) * hSP

end LeanFpAnalysis.FP
