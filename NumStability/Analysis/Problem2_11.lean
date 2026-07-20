-- Analysis/Problem2_11.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.11.

import Mathlib.Data.Nat.Factorial.Basic
import NumStability.Analysis.LeadingDigitDistribution

namespace NumStability

open scoped BigOperators

noncomputable section

/-!
# Higham Chapter 2, Problem 2.11

Problem 2.11 is an empirical leading-significant-digit investigation.  It asks
the reader to examine five data sources: powers `2^n` and `3^n`, factorials,
random symmetric-matrix eigenvalues, physical constants, and newspaper numbers.

This file records the formal finite-sample object used by those investigations.
Given a classifier that assigns each positive sample value a decimal leading
digit, the induced histogram is a probability distribution on the digits
`1, ..., 9`.  The externally gathered data sources remain empirical inputs.
-/

/-- The five source families named by Problem 2.11. -/
inductive problem2_11EmpiricalSource where
  | powersOfTwo
  | powersOfThree
  | factorials
  | randomSymmetricEigenvalues
  | physicalConstants
  | newspaperNumbers
  deriving DecidableEq, Repr

theorem problem2_11EmpiricalSource_exhaustive
    (s : problem2_11EmpiricalSource) :
    s = problem2_11EmpiricalSource.powersOfTwo ∨
      s = problem2_11EmpiricalSource.powersOfThree ∨
      s = problem2_11EmpiricalSource.factorials ∨
      s = problem2_11EmpiricalSource.randomSymmetricEigenvalues ∨
      s = problem2_11EmpiricalSource.physicalConstants ∨
      s = problem2_11EmpiricalSource.newspaperNumbers := by
  cases s <;> simp

/-- Decimal leading-digit relation: digit `d.val + 1` is the leading digit of
`x` if some decimal scaling places `|x|` in that digit's decade cell. -/
def problem2_11_decimalLeadingDigit (x : ℝ) (d : Fin 9) : Prop :=
  ∃ e : ℤ,
    ((d.val + 1 : ℕ) : ℝ) * (10 : ℝ) ^ e ≤ |x| ∧
      |x| < ((d.val + 2 : ℕ) : ℝ) * (10 : ℝ) ^ e

theorem problem2_11_decimalLeadingDigit_digit_between (d : Fin 9) :
    1 ≤ d.val + 1 ∧ d.val + 1 ≤ 9 := by
  constructor
  · exact Nat.succ_pos d.val
  · exact d.isLt

theorem problem2_11_decimalLeadingDigit_abs_pos
    {x : ℝ} {d : Fin 9}
    (h : problem2_11_decimalLeadingDigit x d) :
    0 < |x| := by
  rcases h with ⟨e, hlow, _hhigh⟩
  have hpow_pos : 0 < (10 : ℝ) ^ e := zpow_pos (by norm_num) e
  have hdigit_pos : (0 : ℝ) < ((d.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos d.val
  exact lt_of_lt_of_le (mul_pos hdigit_pos hpow_pos) hlow

theorem problem2_11_decimalLeadingDigit_normalized_bin
    {x : ℝ} {d : Fin 9}
    (h : problem2_11_decimalLeadingDigit x d) :
    ∃ e : ℤ,
      ((d.val + 1 : ℕ) : ℝ) ≤ |x| / (10 : ℝ) ^ e ∧
        |x| / (10 : ℝ) ^ e < ((d.val + 2 : ℕ) : ℝ) := by
  rcases h with ⟨e, hlow, hhigh⟩
  refine ⟨e, ?_, ?_⟩
  · rw [le_div_iff₀ (zpow_pos (by norm_num : (0 : ℝ) < 10) e)]
    exact hlow
  · rw [div_lt_iff₀ (zpow_pos (by norm_num : (0 : ℝ) < 10) e)]
    exact hhigh

/-- Formal version of the Problem 2.11 programming note: after division by the
witnessed power of `10`, a sample with a decimal leading digit lies in
`[1,10)`. -/
theorem problem2_11_decimalLeadingDigit_exists_scaled_mem_one_ten
    {x : ℝ} {d : Fin 9}
    (h : problem2_11_decimalLeadingDigit x d) :
    ∃ e : ℤ,
      1 ≤ |x| / (10 : ℝ) ^ e ∧ |x| / (10 : ℝ) ^ e < 10 := by
  rcases problem2_11_decimalLeadingDigit_normalized_bin h with
    ⟨e, hlow, hhigh⟩
  refine ⟨e, ?_, ?_⟩
  · exact le_trans (by norm_num : (1 : ℝ) ≤ ((d.val + 1 : ℕ) : ℝ)) hlow
  · exact lt_of_lt_of_le hhigh
      (by
        have hd : d.val + 1 ≤ 9 := d.isLt
        have hd' : d.val + 2 ≤ 10 := Nat.succ_le_succ hd
        exact_mod_cast hd')

/-- Source item 1: powers `k^n`, `n = 0:1000`, represented by `Fin 1001`. -/
def problem2_11_powerSample (k : ℕ) : Fin 1001 → ℝ :=
  fun n => (k ^ n.val : ℕ)

theorem problem2_11_powerSample_card :
    Fintype.card (Fin 1001) = 1001 := by
  simp

theorem problem2_11_powerSample_index_le_1000 (n : Fin 1001) :
    n.val ≤ 1000 :=
  Nat.le_of_lt_succ n.isLt

theorem problem2_11_powerSample_first (k : ℕ) :
    problem2_11_powerSample k ⟨0, by norm_num⟩ = 1 := by
  simp [problem2_11_powerSample]

theorem problem2_11_powerSample_last (k : ℕ) :
    problem2_11_powerSample k ⟨1000, by norm_num⟩ =
      ((k ^ 1000 : ℕ) : ℝ) := by
  simp [problem2_11_powerSample]

theorem problem2_11_powerSample_two_last :
    problem2_11_powerSample 2 ⟨1000, by norm_num⟩ =
      ((2 ^ 1000 : ℕ) : ℝ) :=
  problem2_11_powerSample_last 2

theorem problem2_11_powerSample_three_last :
    problem2_11_powerSample 3 ⟨1000, by norm_num⟩ =
      ((3 ^ 1000 : ℕ) : ℝ) :=
  problem2_11_powerSample_last 3

theorem problem2_11_powerSample_pos {k : ℕ} (hk : 0 < k)
    (n : Fin 1001) :
    0 < problem2_11_powerSample k n := by
  dsimp [problem2_11_powerSample]
  have hnat : 0 < k ^ n.val := Nat.pow_pos hk
  exact_mod_cast hnat

theorem problem2_11_powerSample_two_pos (n : Fin 1001) :
    0 < problem2_11_powerSample 2 n :=
  problem2_11_powerSample_pos (by norm_num) n

theorem problem2_11_powerSample_three_pos (n : Fin 1001) :
    0 < problem2_11_powerSample 3 n :=
  problem2_11_powerSample_pos (by norm_num) n

/-- Source item 2: factorials `n!`, `n = 1:1000`, represented by `Fin 1000`
with value `(i+1)!`. -/
def problem2_11_factorialSample : Fin 1000 → ℝ :=
  fun n => (Nat.factorial (n.val + 1) : ℕ)

theorem problem2_11_factorialSample_card :
    Fintype.card (Fin 1000) = 1000 := by
  simp

theorem problem2_11_factorialSample_index_between (n : Fin 1000) :
    1 ≤ n.val + 1 ∧ n.val + 1 ≤ 1000 :=
  ⟨Nat.succ_pos n.val, Nat.succ_le_of_lt n.isLt⟩

theorem problem2_11_factorialSample_first :
    problem2_11_factorialSample ⟨0, by norm_num⟩ = 1 := by
  simp [problem2_11_factorialSample]

theorem problem2_11_factorialSample_last :
    problem2_11_factorialSample ⟨999, by norm_num⟩ =
      ((Nat.factorial 1000 : ℕ) : ℝ) := by
  change ((Nat.factorial (999 + 1) : ℕ) : ℝ) =
    ((Nat.factorial 1000 : ℕ) : ℝ)
  rw [show 999 + 1 = 1000 by norm_num]

theorem problem2_11_factorialSample_pos (n : Fin 1000) :
    0 < problem2_11_factorialSample n := by
  dsimp [problem2_11_factorialSample]
  have hnat : 0 < Nat.factorial (n.val + 1) := Nat.factorial_pos _
  exact_mod_cast hnat

/-- Count of sample points classified as a given decimal leading digit. -/
def problem2_11_digitCount {sampleSize : ℕ}
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) : ℕ :=
  ((Finset.univ : Finset (Fin sampleSize)).filter
    (fun i => digitOf i = d)).card

theorem problem2_11_digitCount_le_sampleSize {sampleSize : ℕ}
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) :
    problem2_11_digitCount digitOf d ≤ sampleSize := by
  classical
  have hle :
      ((Finset.univ : Finset (Fin sampleSize)).filter
        (fun i => digitOf i = d)).card ≤
        (Finset.univ : Finset (Fin sampleSize)).card :=
    Finset.card_filter_le _ _
  simpa [problem2_11_digitCount] using hle

/-- Empirical frequency of a decimal leading digit in a nonempty finite sample. -/
def problem2_11_digitFrequency {sampleSize : ℕ} (_hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) : ℝ :=
  (problem2_11_digitCount digitOf d : ℝ) / (sampleSize : ℝ)

theorem problem2_11_digitFrequency_nonneg {sampleSize : ℕ}
    (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) :
    0 ≤ problem2_11_digitFrequency hsize digitOf d := by
  exact div_nonneg (Nat.cast_nonneg _)
    (le_of_lt (Nat.cast_pos.mpr hsize : (0 : ℝ) < sampleSize))

theorem problem2_11_digitFrequency_le_one {sampleSize : ℕ}
    (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) :
    problem2_11_digitFrequency hsize digitOf d ≤ 1 := by
  have hden_pos : (0 : ℝ) < sampleSize := Nat.cast_pos.mpr hsize
  rw [problem2_11_digitFrequency, div_le_one hden_pos]
  exact_mod_cast problem2_11_digitCount_le_sampleSize digitOf d

theorem problem2_11_sum_digitCount_eq_sampleSize {sampleSize : ℕ}
    (digitOf : Fin sampleSize → Fin 9) :
    (∑ d : Fin 9, problem2_11_digitCount digitOf d) = sampleSize := by
  classical
  have hfiber :
      (Finset.univ : Finset (Fin sampleSize)).card =
        ∑ d ∈ (Finset.univ : Finset (Fin 9)),
          ((Finset.univ : Finset (Fin sampleSize)).filter
            (fun i => digitOf i = d)).card :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin sampleSize)))
      (t := (Finset.univ : Finset (Fin 9)))
      (f := digitOf)
      (by intro i hi; simp)
  simpa [problem2_11_digitCount] using hfiber.symm

theorem problem2_11_sum_digitFrequency_eq_one {sampleSize : ℕ}
    (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) :
    (∑ d : Fin 9, problem2_11_digitFrequency hsize digitOf d) = 1 := by
  classical
  have hcount := problem2_11_sum_digitCount_eq_sampleSize digitOf
  have hsize_ne : (sampleSize : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsize)
  calc
    (∑ d : Fin 9, problem2_11_digitFrequency hsize digitOf d)
        = (∑ d : Fin 9, (problem2_11_digitCount digitOf d : ℝ)) /
            (sampleSize : ℝ) := by
            simp [problem2_11_digitFrequency, div_eq_mul_inv, Finset.sum_mul]
    _ = (sampleSize : ℝ) / (sampleSize : ℝ) := by
            rw [← Nat.cast_sum, hcount]
    _ = 1 := by
            exact div_self hsize_ne

/-- The finite empirical digit distribution induced by any nonempty classified
sample. -/
def problem2_11_empiricalDigitProbability {sampleSize : ℕ}
    (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) : FiniteProbability (Fin 9) where
  prob d := problem2_11_digitFrequency hsize digitOf d
  prob_nonneg d := problem2_11_digitFrequency_nonneg hsize digitOf d
  prob_sum := problem2_11_sum_digitFrequency_eq_one hsize digitOf

theorem problem2_11_empiricalDigitProbability_prob_eq_frequency
    {sampleSize : ℕ} (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) :
    (problem2_11_empiricalDigitProbability hsize digitOf).prob d =
      problem2_11_digitFrequency hsize digitOf d :=
  rfl

theorem problem2_11_empiricalDigitProbability_prob_le_one
    {sampleSize : ℕ} (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) :
    (problem2_11_empiricalDigitProbability hsize digitOf).prob d ≤ 1 := by
  simpa [problem2_11_empiricalDigitProbability_prob_eq_frequency]
    using problem2_11_digitFrequency_le_one hsize digitOf d

end

end NumStability
