import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-!
# Binomial Coefficient Bounds

Reusable binomial estimates for Vershynin's HDP appetizer.  The main
statements formalize Exercise 0.0.5 and the stars-and-bars estimates
used in Exercise 0.0.6.
-/

open Finset

namespace LeanFpAnalysis.HDP

lemma binomial_weighted_sum (n : ℕ) (a : ℝ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ k) = (1 + a) ^ n := by
  simpa [mul_comm, mul_left_comm, mul_assoc, add_comm] using (add_pow a 1 n).symm

lemma one_add_pow_le_exp_nat_mul (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (1 + a) ^ n ≤ Real.exp ((n : ℝ) * a) := by
  have hbase : 1 + a ≤ Real.exp a := by
    simpa [add_comm] using Real.add_one_le_exp a
  have hnonneg : 0 ≤ 1 + a := by linarith
  calc
    (1 + a) ^ n ≤ (Real.exp a) ^ n := by
      exact pow_le_pow_left₀ hnonneg hbase n
    _ = Real.exp ((n : ℝ) * a) := by
      exact (Real.exp_nat_mul a n).symm

lemma binomial_lower_term {n m i : ℕ} (hm0 : 0 < m) (hmn : m ≤ n)
    (hi : i ∈ Finset.range m) :
    (n : ℝ) / (m : ℝ) * ((i + 1 : ℕ) : ℝ) ≤
      ((n + 1 - m + i : ℕ) : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hi_le : (i + 1 : ℕ) ≤ m := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
  have hcast :
      ((n + 1 - m + i : ℕ) : ℝ) = (n : ℝ) + 1 - (m : ℝ) + (i : ℝ) := by
    have hrew : n + 1 - m + i = n + 1 + i - m := by omega
    rw [hrew]
    rw [Nat.cast_sub (by omega : m ≤ n + 1 + i)]
    norm_num [Nat.cast_add]
    ring
  rw [hcast]
  field_simp [hmpos.ne']
  have hrle : (((i + 1 : ℕ) : ℝ) ≤ (m : ℝ)) := by exact_mod_cast hi_le
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  norm_num at hrle ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hrle) (sub_nonneg.mpr hmnR)]

/-- Lower bound in HDP Exercise 0.0.5:
`(n / m)^m ≤ (n choose m)`, for `1 ≤ m ≤ n`. -/
theorem choose_lower_bound (n m : ℕ) (hm0 : 0 < m) (hmn : m ≤ n) :
    ((n : ℝ) / (m : ℝ)) ^ m ≤ (n.choose m : ℝ) := by
  have hprod :
      (∏ i ∈ Finset.range m, ((n : ℝ) / (m : ℝ) * ((i + 1 : ℕ) : ℝ))) ≤
        ∏ i ∈ Finset.range m, ((n + 1 - m + i : ℕ) : ℝ) := by
    refine Finset.prod_le_prod ?nonneg ?le
    · intro i hi
      positivity
    · intro i hi
      exact binomial_lower_term hm0 hmn hi
  have hleft :
      (∏ i ∈ Finset.range m, ((n : ℝ) / (m : ℝ) * ((i + 1 : ℕ) : ℝ))) =
        ((n : ℝ) / (m : ℝ)) ^ m * (Nat.factorial m : ℝ) := by
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_const]
    have hfacprod : (∏ i ∈ Finset.range m, (((i + 1 : ℕ) : ℝ))) =
        (Nat.factorial m : ℝ) := by
      exact_mod_cast (Finset.prod_range_add_one_eq_factorial m)
    rw [hfacprod]
    simp
  have hright :
      (∏ i ∈ Finset.range m, ((n + 1 - m + i : ℕ) : ℝ)) =
        ((n + 1 - m).ascFactorial m : ℝ) := by
    rw [Nat.ascFactorial_eq_prod_range]
    norm_cast
  have hchoose_prod :
      ((n + 1 - m).ascFactorial m : ℝ) = (Nat.factorial m : ℝ) * (n.choose m : ℝ) := by
    have hnat := Nat.ascFactorial_eq_factorial_mul_choose' (n + 1 - m) m
    have harg : n + 1 - m + m - 1 = n := by omega
    rw [harg] at hnat
    exact_mod_cast hnat
  have hfact_pos : 0 < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rw [hleft, hright, hchoose_prod] at hprod
  rw [mul_comm (Nat.factorial m : ℝ) (n.choose m : ℝ)] at hprod
  exact (mul_le_mul_iff_left₀ hfact_pos).mp hprod

lemma choose_le_sum_range_choose (n m : ℕ) :
    (n.choose m : ℝ) ≤ ∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ) := by
  exact Finset.single_le_sum (s := Finset.range (m + 1))
    (f := fun k => (n.choose k : ℝ)) (fun k _ => by positivity)
    (Finset.mem_range.mpr (Nat.lt_succ_self m))

/-- Upper bound in HDP Exercise 0.0.5:
`sum_{k=0}^m (n choose k) ≤ (e n / m)^m`, for `1 ≤ m ≤ n`. -/
theorem sum_range_choose_le_exp_mul_div (n m : ℕ) (hm0 : 0 < m) (hmn : m ≤ n) :
    (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ)) ≤
      (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m := by
  let a : ℝ := (m : ℝ) / (n : ℝ)
  have hn0 : 0 < n := lt_of_lt_of_le hm0 hmn
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn0
  have ha0 : 0 ≤ a := by positivity
  have hapos : 0 < a := by positivity
  have ha1 : a ≤ 1 := by
    rw [div_le_one hnpos]
    exact_mod_cast hmn
  have hweighted :
      a ^ m * (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ)) ≤
        ∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ) * a ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpow : a ^ m ≤ a ^ k := pow_le_pow_of_le_one ha0 ha1 hkm
    calc
      a ^ m * (n.choose k : ℝ) ≤ a ^ k * (n.choose k : ℝ) := by
        exact mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (n.choose k : ℝ) * a ^ k := by ring
  have hpartial :
      (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ) * a ^ k) ≤
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ k := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro x hx
        exact Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hmn)))
      (by intro k hk _; positivity)
  have hfull :
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ k) ≤ (Real.exp 1) ^ m := by
    calc
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ k) = (1 + a) ^ n :=
        binomial_weighted_sum n a
      _ ≤ Real.exp ((n : ℝ) * a) := one_add_pow_le_exp_nat_mul n ha0
      _ = (Real.exp 1) ^ m := by
        have hna : (n : ℝ) * a = (m : ℝ) := by
          dsimp [a]
          field_simp [hnpos.ne']
        rw [hna]
        simp
  have hmain : a ^ m * (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ)) ≤
      (Real.exp 1) ^ m :=
    hweighted.trans (hpartial.trans hfull)
  have hapow : 0 < a ^ m := by positivity
  rw [← le_div_iff₀' hapow] at hmain
  calc
    (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ)) ≤ (Real.exp 1) ^ m / a ^ m := hmain
    _ = (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m := by
      rw [← div_pow]
      congr 1
      dsimp [a]
      field_simp [hmpos.ne', hnpos.ne']

/-- HDP Exercise 0.0.5, packaged as the chain of binomial inequalities
`(n/m)^m ≤ choose n m ≤ sum_{k≤m} choose n k ≤ (e n/m)^m`. -/
theorem exercise_0_0_5_binomial_chain (n m : ℕ) (hm0 : 0 < m) (hmn : m ≤ n) :
    ((n : ℝ) / (m : ℝ)) ^ m ≤ (n.choose m : ℝ) ∧
    (n.choose m : ℝ) ≤ ∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ) ∧
    (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ)) ≤
      (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m := by
  exact ⟨choose_lower_bound n m hm0 hmn,
    choose_le_sum_range_choose n m,
    sum_range_choose_le_exp_mul_div n m hm0 hmn⟩

lemma one_le_sqrt_two_pi_mul_nat {k : ℕ} (hk : 0 < k) :
    (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
  rw [Real.one_le_sqrt]
  have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith

lemma pow_div_exp_le_factorial {k : ℕ} (hk : 0 < k) :
    ((k : ℝ) / Real.exp 1) ^ k ≤ (Nat.factorial k : ℝ) := by
  have hst := Stirling.le_factorial_stirling k
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) :=
    one_le_sqrt_two_pi_mul_nat hk
  have hbase_nonneg : 0 ≤ ((k : ℝ) / Real.exp 1) ^ k := by positivity
  have hmul : ((k : ℝ) / Real.exp 1) ^ k ≤
      Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k := by
    simpa using mul_le_mul_of_nonneg_right hsqrt hbase_nonneg
  exact hmul.trans hst

/-- Single binomial coefficient version of Exercise 0.0.5:
`(n choose k) ≤ (e n / k)^k`, for `k > 0`. -/
theorem choose_le_exp_mul_div (n k : ℕ) (hk : 0 < k) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  have hchoose : (n.choose k : ℝ) ≤ ((n : ℝ) ^ k) / (Nat.factorial k : ℝ) :=
    Nat.choose_le_pow_div (α := ℝ) k n
  have hfac : ((k : ℝ) / Real.exp 1) ^ k ≤ (Nat.factorial k : ℝ) :=
    pow_div_exp_le_factorial hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbasepos : 0 < ((k : ℝ) / Real.exp 1) ^ k := by positivity
  have hdiv : ((n : ℝ) ^ k) / (Nat.factorial k : ℝ) ≤
      ((n : ℝ) ^ k) / (((k : ℝ) / Real.exp 1) ^ k) := by
    exact div_le_div_of_nonneg_left (by positivity) hbasepos hfac
  calc
    (n.choose k : ℝ) ≤ ((n : ℝ) ^ k) / (Nat.factorial k : ℝ) := hchoose
    _ ≤ ((n : ℝ) ^ k) / (((k : ℝ) / Real.exp 1) ^ k) := hdiv
    _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
      rw [div_pow, div_pow, mul_pow]
      field_simp [hkpos.ne', Real.exp_ne_zero]

lemma eps_card_base_bound {ε : ℝ} {N k : ℕ} (hε : 0 < ε)
    (hceil : (1 / ε ^ 2 : ℝ) ≤ (k : ℝ)) :
    Real.exp 1 * ((N + k : ℕ) : ℝ) / (k : ℝ) ≤
      Real.exp 1 + Real.exp 1 * ε ^ 2 * (N : ℝ) := by
  have hkpos_real : 0 < (k : ℝ) := by
    have hpos : (0 : ℝ) < 1 / ε ^ 2 := by positivity
    exact lt_of_lt_of_le hpos hceil
  have hmul : (1 : ℝ) ≤ (k : ℝ) * ε ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hceil (sq_nonneg ε)
    field_simp [ne_of_gt hε] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hone_div : (1 : ℝ) / (k : ℝ) ≤ ε ^ 2 := by
    rw [div_le_iff₀ hkpos_real]
    simpa [mul_comm] using hmul
  have hN : (N : ℝ) / (k : ℝ) ≤ ε ^ 2 * (N : ℝ) := by
    calc
      (N : ℝ) / (k : ℝ) = (N : ℝ) * (1 / (k : ℝ)) := by ring
      _ ≤ (N : ℝ) * ε ^ 2 := by
        exact mul_le_mul_of_nonneg_left hone_div (by positivity)
      _ = ε ^ 2 * (N : ℝ) := by ring
  calc
    Real.exp 1 * ((N + k : ℕ) : ℝ) / (k : ℝ)
        = Real.exp 1 * (1 + (N : ℝ) / (k : ℝ)) := by
            field_simp [hkpos_real.ne']
            norm_num [Nat.cast_add, add_comm]
    _ ≤ Real.exp 1 * (1 + ε ^ 2 * (N : ℝ)) := by
            have hsum : 1 + (N : ℝ) / (k : ℝ) ≤ 1 + ε ^ 2 * (N : ℝ) := by
              linarith
            exact mul_le_mul_of_nonneg_left hsum (le_of_lt (Real.exp_pos 1))
    _ = Real.exp 1 + Real.exp 1 * ε ^ 2 * (N : ℝ) := by ring

end LeanFpAnalysis.HDP
